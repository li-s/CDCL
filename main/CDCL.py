import logging
import operator
import random
import time
from collections import deque

from main import logger
from main import parser

TRUE = 1
FALSE = 0
UNDEFINED = -1


class CDCLSolver:

    def __init__(self, filepath, PBV_heuristic="DLIS"):
        logger.init_logger()
        logging.info("---------Initializing CDCL Solver---------")
        self.filepath = filepath
        self.clauses = parser.read_file_and_parse(filepath)
        self.atomic_prop = self.get_ap(self.clauses)
        self.learnt_clauses = set()
        self.assignments = {i: UNDEFINED for i in self.atomic_prop}

        self.level = 0
        self.implication_graph = dict((v, Node(v, UNDEFINED)) for v in self.atomic_prop)
        self.branching_var = set()
        self.guess_trail = {}  # keep track of guesses
        self.propagation_trail = {}  # dict - level:int -> literals:set, keep track of unit propagations
        self.num_PBV_invocations = 0  # number of pick branching var invocations
        self.PBV_heuristic = PBV_heuristic

    def solve(self):
        while not self.all_variable_assigned():
            logging.info(f"Current decision level = {self.level}")
            conflict = self.unit_propagation()
            if conflict:
                backtrack_level, learnt_clause = self.conflict_analysis(conflict)
                if backtrack_level < 0:
                    return "UNSAT"
                else:
                    logging.info(f"Adding clause {learnt_clause}")
                    self.learnt_clauses.add(learnt_clause)
                    self.backtrack(backtrack_level)
            elif self.all_variable_assigned():
                break
            else:
                x, v = self.pick_branching_var()
                logging.info(f"Pick {x} = {v}")
                self.level += 1
                self.assignments[x] = v
                self.branching_var.add(x)
                self.guess_trail[self.level] = x
                self.propagation_trail[self.level] = deque()
                self.update_graph(x)
        return self.assignments

    def unit_propagation(self):
        while True:
            # A list of clauses that we will propagate in this iteration
            clauses_to_propagate = []
            for clause in self.clauses.union(self.learnt_clauses):
                clause_value = self.clause_value(clause)
                # logging.debug(f"Check clause {clause}")
                # Check if conflict is found, return the clause that caused the conflict
                if clause_value == FALSE:
                    logging.debug(f"Found conflict at {clause}")
                    return clause
                if clause_value == UNDEFINED:
                    # logging.debug(f"Found undefined clause: {clause}")
                    is_unit_clause, unit_literal = self.is_unit_clause(clause)
                    if is_unit_clause and (unit_literal, clause) not in clauses_to_propagate:
                        clauses_to_propagate.append((unit_literal, clause))

            # If nothing to propagate, return None to signal no conflict
            if not clauses_to_propagate:
                return None

            for unit_literal, clause in reversed(clauses_to_propagate):
                # Assign value so that the literal is true
                logging.debug(f"Unit propagation: {unit_literal} in {clause}")
                if unit_literal > 0:
                    self.assignments[abs(unit_literal)] = TRUE
                else:
                    self.assignments[abs(unit_literal)] = FALSE
                self.update_graph(abs(unit_literal), clause)
                # Add propagation trail if level > 0, we don't care if unit prop happened in level 0
                if self.level > 0:
                    self.propagation_trail[self.level].append(unit_literal)

    def all_variable_assigned(self):
        """Returns true if all variables have assignment"""
        all_assigned = all(var in self.assignments for var in self.atomic_prop)
        none_unassigned = not any(var for var in self.atomic_prop if self.assignments[var] == UNDEFINED)
        return all_assigned and none_unassigned

    def pick_branching_var(self):
        """Pick a variable to branch"""
        self.num_PBV_invocations += 1
        if self.PBV_heuristic == "DLIS":
            variables = {}
            unassigned = list(self.all_unassigned_vars())
            for clause in self.clauses.union(self.learnt_clauses):
                for prop in clause:
                    if abs(prop) not in unassigned:
                        continue
                    if prop in variables:
                        variables[prop] += 1
                    else:
                        variables[prop] = 1
            variable = max(variables.items(), key=operator.itemgetter(1))[0]
            assign = TRUE if variable > 0 else FALSE
            return abs(variable), assign
        elif self.PBV_heuristic == "Random":
            return random.choice(list(self.all_unassigned_vars())), random.sample([TRUE, FALSE], 1)[0]
        elif self.PBV_heuristic == "Ordered":
            return list(self.all_unassigned_vars())[0], TRUE
        elif self.PBV_heuristic == "2Clause":
            variables = {}
            unassigned = list(self.all_unassigned_vars())
            for clause in filter(lambda x: self.check_two_clause(x), self.clauses.union(self.learnt_clauses)):
                for prop in clause:
                    if abs(prop) not in unassigned:
                        continue
                    if prop in variables:
                        variables[prop] += 1
                    else:
                        variables[prop] = 1
            variable = random.choice(max(variables.items(), key=operator.itemgetter(1))) if len(variables) != 0 \
                else random.choice(list(self.all_unassigned_vars()))
            assign = TRUE if variable > 0 else FALSE
            return abs(variable), assign

    def conflict_analysis(self, conflict_clause):
        """Perform conflict analysis and return the level to back jump to"""
        """
        Analyze the most recent conflict and learn a new clause from the conflict.
        - Find the cut in the implication graph that led to the conflict
        - Derive a new clause which is the negation of the assignments that led to the conflict

        Returns a decision level to be backtracked to.
        :param conf_cls: (set of int) the clause that introduces the conflict
        :return: ({int} level to backtrack to, {set(int)} clause learnt)
        """
        logging.info(f"Performing conflict analysis on clause {conflict_clause} at {self.level}")
        logging.info('conflict clause: %s', conflict_clause)

        if self.level == 0:
            return -1, None

        assign_history = [self.guess_trail[self.level]] + list(self.propagation_trail[self.level])
        logging.info('assign history for level %s: %s', self.level, assign_history)

        pool_lits = conflict_clause
        done_lits = set()
        curr_level_lits = set()
        prev_level_lits = set()

        while True:
            logging.info('-------')
            logging.info('pool lits: %s', pool_lits)
            for lit in pool_lits:
                if self.implication_graph[abs(lit)].level == self.level:
                    curr_level_lits.add(lit)
                else:
                    prev_level_lits.add(lit)

            logging.info('curr level lits: %s', curr_level_lits)
            logging.info('prev level lits: %s', prev_level_lits)
            if len(curr_level_lits) == 1:
                break

            last_assigned, others = self.next_recent_assigned(curr_level_lits, assign_history)
            logging.info('last assigned: %s, others: %s', last_assigned, others)

            done_lits.add(abs(last_assigned))
            curr_level_lits = set(others)

            pool_clause = self.implication_graph[abs(last_assigned)].clause
            pool_lits = [
                l for l in pool_clause if abs(l) not in done_lits
            ] if pool_clause is not None else []

            logging.info('done lits: %s', done_lits)

        learnt = frozenset([l for l in curr_level_lits.union(prev_level_lits)])
        if prev_level_lits:
            level = max([self.implication_graph[abs(x)].level for x in prev_level_lits])
        else:
            level = self.level - 1

        return level, learnt

    def find_dependencies(self, clause, level):
        """Find dependency of a variable"""
        dependencies = []
        if -self.guess_trail.get(level, -1) in clause:
            dependencies.append(self.guess_trail[level])
        for literal in self.propagation_trail.get(level, []):
            if -literal in clause:
                dependencies.append(literal)
        logging.debug(f"Found {len(dependencies)} dependencies for {clause}: {dependencies} at level {level}")
        return dependencies

    def backtrack(self, backtrack_level):
        """
        Non-chronologically backtrack ("back jump") to the appropriate decision level,
        where the first-assigned variable involved in the conflict was assigned
        """
        logging.debug('backtracking to %s', backtrack_level)
        # Update implication graph
        for var, node in self.implication_graph.items():
            if node.level <= backtrack_level:
                # If keep node, remove all children with decision level higher than backtrack level
                node.children = list(filter(lambda child: child.level <= backtrack_level, node.children))
            else:
                # Else remove node entirely
                node.value = UNDEFINED
                node.level = -1
                node.parents = []
                node.children = []
                node.clause = None
                self.assignments[node.variable] = UNDEFINED

        # Remove branching variable list according to implication graph
        # print("Before " + str(self.branching_var))
        # print(self.assignments)
        self.branching_var = set([
            var for var in self.atomic_prop
            if (self.assignments[var] != UNDEFINED
                and len(self.implication_graph[var].parents) == 0)
        ])
        # print(self.branching_var)

        levels = list(self.propagation_trail.keys())
        for k in levels:
            if k <= backtrack_level:
                continue
            del self.guess_trail[k]
            del self.propagation_trail[k]

        self.level = backtrack_level
        logging.info('after backtracking, graph:\n%s', self.implication_graph)

    def update_graph(self, var, clause=None):
        """Update the implication graph for a variable, insert propagation clause if needed"""
        node = self.implication_graph[var]
        node.value = self.assignments[var]
        node.level = self.level
        node.clause = clause

        # update reason for propagation (parents) if needed
        if clause:
            for v in [abs(lit) for lit in clause if abs(lit) != var]:
                node.parents.append(self.implication_graph[v])
                self.implication_graph[v].children.append(node)
            logging.info('Updated node %s with parents: %s', var, node.parents)

    @staticmethod
    def resolution(c1, c2, prop=None):
        """Resolution, optionally make use of the literal supplied"""
        # If no resolving proposition is supplied, find one
        if not prop:
            for literal in c1:
                if -literal in c2:
                    prop = abs(literal)
                    break
        # If no proposition found, resolution cannot be performed
        if not prop:
            return None
        resolvent = set([c for c in c1 if c != prop and c != -prop] + [c for c in c2 if c != prop and c != -prop])
        return resolvent

    @staticmethod
    def get_ap(formula):
        """Find atomic proposition in formula"""
        ap = set()
        for clause in formula:
            for prop in clause:
                ap.add(abs(prop))
        return ap

    def is_value_sat_in_formula(self, prop, value):
        backup = self.assignments[prop]
        self.assignments[prop] = value
        result = self.formula_value(self.clauses)
        self.assignments[prop] = backup
        return result

    def formula_value(self, cnf):
        """Check if a cnf formula is SAT based on current assignments"""
        has_undefined = False
        for clause in cnf:
            clause_val = self.clause_value(clause)
            if clause_val == UNDEFINED:
                has_undefined = True
            elif clause_val == FALSE:
                return FALSE
        return UNDEFINED if has_undefined else TRUE

    def clause_value(self, clause):
        """Check if a clause is SAT based on current assignments"""
        has_undefined = False
        for literal in clause:
            lit_val = self.literal_value(literal)
            if lit_val == UNDEFINED:
                has_undefined = True
            elif lit_val == TRUE:
                return TRUE
        return UNDEFINED if has_undefined else FALSE

    def literal_value(self, literal):
        """Check if a literal is SAT based on current assignments"""
        value = self.assignments[abs(literal)]
        if value == UNDEFINED:
            return UNDEFINED
        if literal < 0:
            return TRUE if value == FALSE else FALSE
        else:
            return TRUE if value == TRUE else FALSE

    def get_all_unit_clauses(self):
        """Get all unit clauses"""
        unit_clauses = []
        for clause in self.clauses:
            clause_value, unit_literal = self.is_unit_clause(clause)
            if clause_value:
                unit_clauses.append(clause)
        return unit_clauses

    def is_unit_clause(self, clause):
        """Check if a clause is a unit clause (all false except one undefined)"""
        unit_literal = None
        for literal in clause:
            if self.literal_value(literal) == TRUE:
                return False, None
            elif self.literal_value(literal) == UNDEFINED:
                if unit_literal:
                    return False, None
                unit_literal = literal
        return True, unit_literal

    def complete_assignment(self):
        """Check if we have a complete assignment so we can stop"""
        for assignment in self.assignments.values():
            if assignment == UNDEFINED:
                return False
        return True

    def next_recent_assigned(self, clause, assign_history):
        """
        According to the assign history, separate the latest assigned variable
        with the rest in `clause`
        :param clause: {set of int} the clause to separate
        :return: ({int} variable, [int] other variables in clause)
        """
        for v in reversed(assign_history):
            if v in clause or -v in clause:
                return v, [x for x in clause if abs(x) != abs(v)]

    def all_unassigned_vars(self):
        return filter(
            lambda v: v in self.assignments and self.assignments[v] == UNDEFINED, self.atomic_prop)

    def check_two_clause(self, clause):
        num_unassigned = sum([1 for lit in clause if self.assignments[abs(lit)] == UNDEFINED])
        return num_unassigned == 2

    def checkSAT(self):
        return self.formula_value(self.clauses)


class Node:

    def __init__(self, variable, value):
        self.variable = variable
        self.value = value
        self.level = -1
        self.parents = []
        self.children = []
        self.clause = None      # The clause that caused unit prop

    def all_parents(self):
        ans = set(self.parents)
        for parent in self.parents:
            for p in parent.all_parents():
                ans.add(p)
        return list(ans)

    def __str__(self):
        sign = '+' if self.value == TRUE else '-' if self.value == FALSE else '?'
        return "[{}{}:L{}, {}p, {}c, {}]".format(
            sign, self.variable, self.level, len(self.parents), len(self.children), self.clause)

    def __repr__(self):
        return str(self)


if __name__ == "__main__":
    num_tries = 1
    t1 = time.time()
    for i in range(num_tries):
        solver = CDCLSolver("../data/game.cnf", "2Clause")
        print("Answer: ", solver.solve())
        print("Verify: ", solver.checkSAT())
    t2 = time.time()
    print("Time: ", (t2 - t1) / num_tries)

