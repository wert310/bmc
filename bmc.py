#!/usr/bin/env python3

import abc
import argparse
import collections
import itertools
import random
import string
import z3


def get_vars(exp):
    if z3.is_var(exp): return set([exp])
    s = set()
    for c in exp.children():
        s = s.union(get_vars(c))
    return s

def get_uninterpreted_calls(exp):
    if z3.is_app_of(exp, z3.Z3_OP_UNINTERPRETED):
        if exp.num_args() == 0: return set() # Consts are 0 args uninterpreted calls :/
        return set([exp])
    s = set()
    for c in exp.children():
        s = s.union(get_uninterpreted_calls(c))
    return s

def random_string(length=12):
    return ''.join(random.choice(string.ascii_lowercase + string.digits) for _ in range(length))


class BMC(abc.ABC):

    @abc.abstractmethod
    def query(self, query):
        raise NotImplementedError

    @abc.abstractmethod
    def get_answer(self):
        raise NotImplementedError

    @staticmethod
    def split_rule(r):
        r = r.body() if z3.is_quantifier(r) else r
        head, tail = r, z3.BoolVal(True)
        if z3.is_implies(r):
            head, tail = r.arg(1), r.arg(0)
        return head, tail



class LinearBMC(BMC):

    def __init__(self, rules, solver=None, verbose=False, simplify=False):
        self.solver = solver if solver else z3.Solver()
        self.rules = rules
        self.verbose = verbose
        self.simplify = simplify
        self.__sat_res = None
        z3.set_param(verbose="1" if verbose else "0")

    def _assert(self, what):
        if self.simplify:
            what = z3.simplify(what)
        self.solver.add(what)

    def _log(self, *what):
        if self.verbose: print(*what)

    @staticmethod
    def _mk_rule(pred, level, rule_idx):
        return z3.Const(f"rule:{pred.decl().name()}#{level}_{rule_idx}", z3.BoolSort())

    @staticmethod
    def _mk_vars(pred, exp, level, rule_idx):
        return [ (v, z3.Const(f"var:{pred.decl().name()}#{level}_{rule_idx}_{i}", v.sort()))
                 for i, v in enumerate(get_vars(exp)) ]

    @staticmethod
    def _mk_args(pred, level):
        return [ (pred.arg(i),
                  z3.Const(f"arg:{pred.decl().name()}#{level}_{i}", pred.decl().domain(i)))
                 for i in range(pred.num_args()) ]

    @staticmethod
    def _mk_pred(pred, level):
        name = pred if isinstance(pred, str) else pred.decl().name()
        return  z3.Const(f"{name}#{level}", z3.BoolSort())


    def _compile(self, level):
        rule_names = collections.defaultdict(lambda: [])

        for r_idx, r in enumerate(self.rules):
            head, tail = BMC.split_rule(r)
            assert z3.is_app_of(head, z3.Z3_OP_UNINTERPRETED)

            level_rule_i = LinearBMC._mk_rule(head, level, r_idx)
            rule_names[head.decl().name()].append(level_rule_i)

            if level == 0 and len(get_uninterpreted_calls(tail)) > 0:
                self._assert(z3.Not(level_rule_i))
                continue

            # Substitute vars
            rule_vars = self._mk_vars(head, r, level, r_idx)
            rule_body = z3.substitute(tail, rule_vars)
            rule_head = z3.substitute(head, rule_vars)

            # Substitute args and make equalities
            conjs = []
            rule_args = LinearBMC._mk_args(rule_head, level)
            conjs.extend( [ exp == arg_sym for exp, arg_sym in rule_args ] )
            rule_body = z3.substitute(rule_body, rule_args)

            # Substitute calls
            for c in get_uninterpreted_calls(rule_body):
                args = [ exp == sym for exp,sym in self._mk_args(c, level-1) ]
                pred = LinearBMC._mk_pred(c, level-1)
                rule_body = z3.substitute(rule_body, [(c, z3.And(z3.And(*args), pred))])

            self._assert(z3.Implies(level_rule_i, z3.And(z3.And(*conjs), rule_body)))

        for k,v in rule_names.items():
            level_pred = self._mk_pred(k, level)
            self._assert(z3.Implies(level_pred, z3.Or(*v)))

    def _check(self, query, level):
        q = self._mk_pred(query, level)
        args = [ sym for _, sym in self._mk_args(query, level) ]
        self._log('Check:', q, args)
        return self.solver.check(q), args

    def query(self, query):
        self._log(f"Query: {query}")
        for i in itertools.count():
            self._log(f"level: {i}")
            self._compile(level=i)
            res, args = self._check(query, level=i)
            if res == z3.sat:
                self.__sat_res = res, args
                return res
            if res == z3.unknown:
                return res

    def get_answer(self):
        assert self.__sat_res
        _, args = self.__sat_res
        m = self.solver.model()
        return [ (arg, m[arg]) for arg in args ]


class NonlinearBMC(BMC):

    def __init__(self, rules, solver=None, verbose=False, simplify=False):
        self.solver = solver if solver else z3.Solver()
        self.rules = rules
        self.verbose = verbose
        self.simplify = simplify
        z3.set_param(verbose="1" if verbose else "0")
        self.solver.set(':core.minimize', True)
        self.reachability_literals = {}
        self.calls = {}
        self.paths = {}

    def _assert(self, what):
        if self.simplify:
            what = z3.simplify(what)
        self.solver.add(what)

    def _log(self, *what):
        if self.verbose: print(*what)


    def mk_reachability_literal(self, call, path):
        assert z3.is_app_of(call, z3.Z3_OP_UNINTERPRETED)
        assert not get_vars(call)

        if (l := self.reachability_literals.get(call, None)) is not None:
            return l
        l = z3.Const(f'rl:{call.decl().name()}#{path}', z3.BoolSort())
        self.reachability_literals[call] = l
        self.calls[l] = call
        self.paths[l] = path
        return l


    @staticmethod
    def _mk_vars(pred, exp, path):
        return [ (v, z3.Const(f"var:{pred.decl().name()}#{path}_{i}", v.sort()))
                 for i, v in enumerate(get_vars(exp)) ]

    def query(self, query):

        rule_groups = collections.defaultdict(lambda: [])
        for r in self.rules:
            head, _ = BMC.split_rule(r)
            rule_groups[head.decl().name()].append(r)

        vs = self._mk_vars(query, query, 'query')
        query = z3.substitute(query, vs)
        q_lit = self.mk_reachability_literal(query, 'query')
        literals = set([ q_lit ])
        for iter_n in itertools.count():
            assumptions = [ q_lit ] + [ z3.Not(l) for l in literals ]
            print(f'Check-sat with:', assumptions)
            res = self.solver.check(assumptions)
            if res == z3.sat or res == z3.unknown:
                self.__sat_res = res, vs
                return res
            core = self.solver.unsat_core()
            if len(core) <= 1:
                return z3.unsat

            print(f"Core #{iter_n}:", core)

            # One unrolling step for everything
            for c_lit in core:
                if z3.is_not(c_lit):
                    c_path = c_lit.arg(0).decl().name().split("#")[1]
                    pt_level = c_path.split('_')
                    if len(pt_level) == 1:
                        lit = c_lit
                        break
            else:
                while (lit := random.choice(core)).decl().name() == q_lit.decl().name(): pass

            assert z3.is_not(lit)
            lit = lit.arg(0)
            literals.remove(lit)
            rl_call = self.calls[lit]
            rl_path = self.paths[lit]
            print("Expanding:", rl_call)
            args = LinearBMC._mk_args(rl_call, rl_path)
            r_conjs = [ exp == arg for exp, arg in args ]

            # Store unrolling depth in the path (FIXME: move into a method)
            rl_path_parts = rl_path.split('_')
            if len(rl_path_parts) == 1:
                rl_path_rec = f'{rl_path}_1'
            else:
                rnd, lvl = rl_path_parts
                rl_path_rec = f'{rnd}_{int(lvl)+1}'

            rules = []
            for r_idx, r in enumerate(rule_groups[rl_call.decl().name()]):
                head, tail = BMC.split_rule(r)
                assert z3.is_app_of(head, z3.Z3_OP_UNINTERPRETED)

                level_rule_i = LinearBMC._mk_rule(head, rl_path, r_idx)
                rules.append(level_rule_i)

                # substitute vars
                rule_vars = self._mk_vars(head, r, f'{rl_path}_{r_idx}')
                rule_body = z3.substitute(tail, rule_vars)
                rule_head = z3.substitute(head, rule_vars)

                # Substitute args and make equalities
                conjs = []
                rule_args = LinearBMC._mk_args(rule_head, rl_path)
                conjs.extend( [ exp == arg_sym for exp, arg_sym in rule_args ] )
                rule_body = z3.substitute(rule_body, rule_args)

                for c in get_uninterpreted_calls(rule_body):
                    rl_path_c = rl_path_rec
                    if rl_call.decl().name() != c.decl().name():
                        rl_path_c = random_string(12)
                    args = [ exp == sym for exp,sym in LinearBMC._mk_args(c, rl_path_c) ]
                    pred = self.mk_reachability_literal(c, rl_path_c)
                    literals.add(pred)
                    rule_body = z3.substitute(rule_body, [(c, z3.And(z3.And(*args), pred))])

                self._assert(z3.Implies(level_rule_i, z3.And(z3.And(*conjs), rule_body)))

            self._assert(z3.Implies(lit, z3.And(z3.And(*r_conjs), z3.Or(*rules))))

    def get_answer(self):
        assert self.__sat_res
        _, args = self.__sat_res
        m = self.solver.model()
        return [ (arg, m[arg]) for _, arg in args ]


if __name__ == '__main__':

    parser = argparse.ArgumentParser(description='BMC')
    parser.add_argument('filename', type=str, help='smtlib file')
    parser.add_argument('-v', '--verbose', action='store_true', help='Be verbose')
    args = parser.parse_args()

    fp = z3.Fixedpoint()
    queries = fp.parse_file(args.filename)
    rules = fp.get_rules()

    solver = LinearBMC
    for r in rules:
        _, tail = BMC.split_rule(r)
        if len(get_uninterpreted_calls(tail)) > 1:
            solver = NonlinearBMC
            break
    print(f'Solver: {solver.__name__}')

    for q in queries:
        bmc = solver(rules, verbose=args.verbose)
        res = bmc.query(q)
        if res == z3.sat:
            ans = bmc.get_answer()
            print(q.decl().name())
            print('\n'.join(f'{arg} := {val}' for arg, val in ans))
