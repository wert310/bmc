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

    def log(self, *what):
        if self.verbose: print(*what)

    @staticmethod
    def mk_rule(pred, level, rule_idx):
        return z3.Const(f"rule:{pred.decl().name()}#{level}_{rule_idx}", z3.BoolSort())

    @staticmethod
    def mk_vars(pred, exp, level, rule_idx):
        return [ (v, z3.Const(f"var:{pred.decl().name()}#{level}_{rule_idx}_{i}", v.sort()))
                 for i, v in enumerate(get_vars(exp)) ]

    @staticmethod
    def mk_args(pred, level):
        return [ (pred.arg(i),
                  z3.Const(f"arg:{pred.decl().name()}#{level}_{i}", pred.decl().domain(i)))
                 for i in range(pred.num_args()) ]

    @staticmethod
    def mk_pred(pred, level):
        name = pred if isinstance(pred, str) else pred.decl().name()
        return  z3.Const(f"{name}#{level}", z3.BoolSort())

    def compile(self, level):
        rule_names = collections.defaultdict(lambda: [])

        for r_idx, r in enumerate(self.rules):
            head, tail = BMC.split_rule(r)
            assert z3.is_app_of(head, z3.Z3_OP_UNINTERPRETED)

            level_rule_i = self.mk_rule(head, level, r_idx)
            rule_names[head.decl().name()].append(level_rule_i)

            if level == 0 and len(get_uninterpreted_calls(tail)) > 0:
                self._assert(z3.Not(level_rule_i))
                continue

            # Substitute vars
            rule_vars = self.mk_vars(head, r, level, r_idx)
            rule_body = z3.substitute(tail, rule_vars)
            rule_head = z3.substitute(head, rule_vars)

            # Substitute args and make equalities
            conjs = []
            rule_args = self.mk_args(rule_head, level)
            conjs.extend( [ exp == arg_sym for exp, arg_sym in rule_args ] )
            rule_body = z3.substitute(rule_body, rule_args)

            # Substitute calls
            for c in get_uninterpreted_calls(rule_body):
                args = [ exp == sym for exp,sym in self.mk_args(c, level-1) ]
                pred = self.mk_pred(c, level-1)
                rule_body = z3.substitute(rule_body, [(c, z3.And(z3.And(*args), pred))])

            self._assert(z3.Implies(level_rule_i, z3.And(z3.And(*conjs), rule_body)))

        for k,v in rule_names.items():
            level_pred = self.mk_pred(k, level)
            self._assert(z3.Implies(level_pred, z3.Or(*v)))

    def check(self, query, level):
        q = self.mk_pred(query, level)
        args = [ sym for _, sym in self.mk_args(query, level) ]
        self.log('Check:', q, args)
        return self.solver.check(q), args

    def query(self, query):
        self.log(f"Query: {query}")
        for i in itertools.count():
            self.log(f"level: {i}")
            self.compile(level=i)
            res, args = self.check(query, level=i)
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
        self.reachability_literals = {} # rl -> call
        self.calls = {} # call -> rl, path

        self.rule_groups = collections.defaultdict(lambda: [])
        for r in self.rules:
            head, _ = BMC.split_rule(r)
            self.rule_groups[head.decl().name()].append(r)

    def _assert(self, what):
        if self.simplify:
            what = z3.simplify(what)
        self.solver.add(what)

    def log(self, *what):
        if self.verbose: print(*what)

    @staticmethod
    def mk_vars(pred, exp, path):
        return [ (v, z3.Const(f"var:{pred.decl().name()}#{path}_{i}", v.sort()))
                 for i, v in enumerate(get_vars(exp)) ]


    def mk_reachability_literal(self, call, path):
        assert z3.is_app_of(call, z3.Z3_OP_UNINTERPRETED)
        assert not get_vars(call)

        if (l := self.reachability_literals.get(call, None)) is not None:
            return l
        l = z3.Const(f'rl:{call.decl().name()}#{path}', z3.BoolSort())
        self.reachability_literals[call] = l
        self.calls[l] = (call, path)
        return l

    def select_literals(self, core, query_lit):
        lits_to_unroll = []
        # One unrolling step for everything
        for c_lit in core:
            if z3.is_not(c_lit):
                if self.get_rl_unrolling_level(c_lit.arg(0)) == 0:
                    lits_to_unroll.append(c_lit)
        # If everything has already been unrolled at least once
        # choose a random literal
        if not lits_to_unroll:
            while (lit := random.choice(core)).decl().name() == query_lit.decl().name(): pass
            lits_to_unroll.append(lit)
        return lits_to_unroll

    def get_rl_unrolling_level(self, lit):
        # Get the unrolling level from the path
        c_path = lit.decl().name().split("#")[1]
        pt_level = c_path.split('_')
        if len(pt_level) == 1:
            return 0
        return int(pt_level[1])

    def mk_rec_call_path(self, rl_path):
        # Store unrolling depth in the path
        rl_path_parts = rl_path.split('_')
        if len(rl_path_parts) == 1:
            return f'{rl_path}_1'
        rnd, lvl = rl_path_parts
        return f'{rnd}_{int(lvl)+1}'

    def expand_literal(self, lit):
        new_calls = set()
        rl_call, rl_path = self.calls[lit]
        self.log("Expanding:", rl_call)
        args = LinearBMC.mk_args(rl_call, rl_path)
        r_conjs = [ exp == arg for exp, arg in args ]
        rl_path_rec = self.mk_rec_call_path(rl_path)

        rules = []
        for r_idx, r in enumerate(self.rule_groups[rl_call.decl().name()]):
            head, tail = BMC.split_rule(r)
            assert z3.is_app_of(head, z3.Z3_OP_UNINTERPRETED)

            level_rule_i = LinearBMC.mk_rule(head, rl_path, r_idx)
            rules.append(level_rule_i)

            # substitute vars
            rule_vars = self.mk_vars(head, r, f'{rl_path}_{r_idx}')
            rule_body = z3.substitute(tail, rule_vars)
            rule_head = z3.substitute(head, rule_vars)

            # Substitute args and make equalities
            conjs = []
            rule_args = LinearBMC.mk_args(rule_head, rl_path)
            conjs.extend( [ exp == arg_sym for exp, arg_sym in rule_args ] )
            rule_body = z3.substitute(rule_body, rule_args)

            rec_call = False
            for c in get_uninterpreted_calls(rule_body):
                if c.decl().name() not in self.rule_groups:
                    continue # skip uninterpreted functions that are not predicates
                rl_path_c = random_string(12)
                if rl_call.decl().name() == c.decl().name() and not rec_call:
                    # reuse the path only for the frst recursive call
                    rec_call = True
                    rl_path_c = rl_path_rec
                args = [ exp == sym for exp,sym in LinearBMC.mk_args(c, rl_path_c) ]
                pred = self.mk_reachability_literal(c, rl_path_c)
                new_calls.add(pred)
                rule_body = z3.substitute(rule_body, [(c, z3.And(z3.And(*args), pred))])

            self._assert(z3.Implies(level_rule_i, z3.And(z3.And(*conjs), rule_body)))

        self._assert(z3.Implies(lit, z3.And(z3.And(*r_conjs), z3.Or(*rules))))

        return new_calls

    def query(self, query):

        vs = self.mk_vars(query, query, 'query')
        query = z3.substitute(query, vs)
        q_lit = self.mk_reachability_literal(query, 'query')
        literals = set([ q_lit ]) # tracks reachability literals of calls

        for iter_n in itertools.count():
            assumptions = [ q_lit ] + [ z3.Not(l) for l in literals ]
            self.log(f'Check-sat with:', assumptions)
            res = self.solver.check(assumptions)
            if res == z3.sat or res == z3.unknown:
                self.__sat_res = res, vs
                return res
            core = self.solver.unsat_core()
            if len(core) <= 1:
                return z3.unsat

            self.log(f"Core #{iter_n}:", core)
            selected = self.select_literals(core, q_lit)
            for lit in selected:
                assert z3.is_not(lit)
                lit = lit.arg(0)
                literals.remove(lit)
                new_calls = self.expand_literal(lit)
                literals = literals.union(new_calls)

    def get_answer(self):
        assert self.__sat_res
        # TODO: return hyper-res answer
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
