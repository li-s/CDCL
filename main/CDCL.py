import logging
import math
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

    def __init__(self, filepath, PBV_heuristic="DLIS", restart=True):
        logger.init_logger()
        logging.info("---------Initializing CDCL Solver---------")
        self.filepath = filepath
        self.clauses = parser.read_file_and_parse(filepath)
        self.atomic_prop = self.get_ap(self.clauses)
        self.learnt_clauses = set()
        self.assignments = {lit: UNDEFINED for lit in self.atomic_prop}

        self.level = 0
        self.implication_graph = dict((v, Node(v, UNDEFINED)) for v in self.atomic_prop)
        self.branching_var = set()
        self.guess_trail = {}  # keep track of guesses
        self.propagation_trail = {}  # dict - level:int -> literals:set, keep track of unit propagations
        self.num_PBV_invocations = 0  # number of pick branching var invocations
        self.PBV_heuristic = PBV_heuristic
        self.vsid_activity = {lit: 0 for lit in self.atomic_prop} # Weight for VSID
        self.vsid_decay = 0.3

        self.restart = restart
        self.restart_counter = 0
        self.restart_factor = 1.1
        self.restart_threshold = 100

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
                    # Update weights for VSID
                    self.update_vsid_activity(learnt_clause)
                    self.backtrack(backtrack_level)
            elif self.all_variable_assigned():
                break
            else:
                if self.restart:
                    # Perform restart if threshold is reached
                    self.restart_counter += 1
                    if self.restart_counter == self.restart_threshold:
                        self.assignments = {lit: UNDEFINED for lit in self.atomic_prop}
                        self.branching_var = set()
                        self.guess_trail = {}
                        self.propagation_trail = {}
                        self.implication_graph = dict((v, Node(v, UNDEFINED)) for v in self.atomic_prop)
                        self.vsid_activity = {lit: 0 for lit in self.atomic_prop}
                        self.level = 0
                        self.restart_threshold *= 1.1
                        continue

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
        """Perform unit propagation and return conflict if conflict is found"""
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

        if self.PBV_heuristic == "surprise_me":
            self.PBV_heuristic = random.choice(["DLIS", "Lishuo", "Random", "VSID", "MOM", "JW"])
            return self.pick_branching_var()

        if self.PBV_heuristic == "DLIS":
            variables = self.count_unassigned_literals(self.clauses.union(self.learnt_clauses))
            variable = max(variables.items(), key=operator.itemgetter(1))[0]
            assign = TRUE if variable > 0 else FALSE
            return abs(variable), assign

        if self.PBV_heuristic == "Lishuo":

            # def count_var(v):
            #     print(v)
            #     if isinstance(v, int):
            #         return v
            #     total = 0
            #     for item in v:
            #         total += count_var(item)
            #     return total

            variables = {}
            variables2 = {}
            unassigned = list(self.all_unassigned_vars())
            two_clause = set()
            for clause in self.clauses.union(self.learnt_clauses):
                if self.check_two_clause(clause):
                    two_clause.add(clause)
                for lit in clause:
                    if abs(lit) not in unassigned:
                        continue
                    if lit in variables:
                        variables[lit] += 1
                        variables2[lit] += 1
                    else:
                        variables[lit] = 1
                        variables2[lit] = 1

            # two_clause = set(filter(lambda x: self.check_two_clause(x), self.clauses.union(self.learnt_clauses)))
            for clause in two_clause:
                unassigned_lits = self.get_unassigned_literals_in_clause(clause)
                if abs(unassigned_lits[0]) in unassigned and -unassigned_lits[0] in variables2 and unassigned_lits[1] in variables:
                    variables2[-unassigned_lits[0]] += variables[unassigned_lits[1]]
                if abs(unassigned_lits[1]) in unassigned and -unassigned_lits[1] in variables2 and unassigned_lits[0] in variables:
                    variables2[-unassigned_lits[1]] += variables[unassigned_lits[0]]

            variable = max(variables2.items(), key=operator.itemgetter(1))[0]
            assign = TRUE if variable > 0 else FALSE
            return abs(variable), assign

        if self.PBV_heuristic == "RDLIS":
            variables = self.count_unassigned_literals(self.clauses.union(self.learnt_clauses))
            # Randomly choose if there are more than 1 maximum value
            max_val = max(variables.items(), key=operator.itemgetter(1))[1]
            variable = random.choice(list(filter(lambda elem: elem[1] == max_val, variables.items())))[0]
            assign = TRUE if variable > 0 else FALSE
            return abs(variable), assign

        if self.PBV_heuristic == "DLCS":
            variables = self.count_unassigned_literals(self.clauses.union(self.learnt_clauses))
            variables2 = self.count_unassigned_literals(self.clauses.union(self.learnt_clauses), False)
            variable = max(variables2.items(), key=operator.itemgetter(1))[0]
            assign = TRUE if variables.get(variable, 0) > variables.get(-variable, 0) else FALSE
            return variable, assign

        if self.PBV_heuristic == "RDLCS":
            variables = self.count_unassigned_literals(self.clauses.union(self.learnt_clauses))
            variables2 = self.count_unassigned_literals(self.clauses.union(self.learnt_clauses), False)
            max_val = max(variables2.items(), key=operator.itemgetter(1))[1]
            variable = random.choice(list(filter(lambda elem: elem[1] == max_val, variables2.items())))[0]
            assign = TRUE if variables.get(variable, 0) > variables.get(-variable, 0) else FALSE
            return variable, assign

        if self.PBV_heuristic == "Random":
            return random.choice(list(self.all_unassigned_vars())), random.choice([TRUE, FALSE])

        if self.PBV_heuristic == "Ordered":
            return list(self.all_unassigned_vars())[0], random.choice([TRUE, FALSE])

        if self.PBV_heuristic == "2-Clause":
            variables = self.count_unassigned_literals(
                list(filter(lambda x: self.check_two_clause(x), self.clauses.union(self.learnt_clauses))), False)
            if len(variables) != 0:
                max_val = max(variables.items(), key=operator.itemgetter(1))[1]
                variable = random.choice(list(filter(lambda elem: elem[1] == max_val, variables.items())))[0]
            else:
                variable = random.choice(list(self.all_unassigned_vars()))
            assign = TRUE if variable > 0 else FALSE
            return abs(variable), assign

        if self.PBV_heuristic == "JW":
            variables = {}
            unassigned = list(self.all_unassigned_vars())
            for clause in self.clauses.union(self.learnt_clauses):
                for lit in clause:
                    if abs(lit) not in unassigned:
                        continue
                    if lit in variables:
                        variables[lit] += math.pow(2, -len(clause))
                    else:
                        variables[lit] = math.pow(2, -len(clause))
            variable = max(variables.items(), key=operator.itemgetter(1))[0]
            assign = TRUE if variable > 0 else FALSE
            return abs(variable), assign

        if self.PBV_heuristic == "MOM":
            variables = self.count_unassigned_literals(self.get_unresolved_smallest_clauses())
            variable = max(variables.items(), key=operator.itemgetter(1))[0]
            assign = TRUE if variable > 0 else FALSE
            return abs(variable), assign

        if self.PBV_heuristic == "VSID":
            unassigned = list(self.all_unassigned_vars())
            variable = 0
            for lit in unassigned:
                if variable == 0 or self.vsid_activity[variable] < self.vsid_activity[lit]:
                    variable = lit
            assign = TRUE if variable > 0 else FALSE
            return variable, assign

    def conflict_analysis(self, conflict_clause):
        """Perform conflict analysis and return the level to back jump to and learnt clause"""
        logging.info(f"Performing conflict analysis on clause {conflict_clause} at {self.level}")

        # If conflict is found at level 0, UNSAT
        if self.level == 0:
            return -1, None

        assign_history = [self.guess_trail[self.level]] + list(self.propagation_trail[self.level])
        logging.info(f"assign history for level {self.level} = {assign_history}")

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
        self.branching_var = set(filter(lambda v: self.assignments[v] != UNDEFINED, self.branching_var))

        # Remove guess trail and propagation trail
        for k in list(self.propagation_trail.keys()):
            if k > backtrack_level:
                del self.guess_trail[k]
                del self.propagation_trail[k]

        self.level = backtrack_level
        logging.info('after backtracking, graph:\n%s', self.implication_graph)

    def update_graph(self, var, clause=None):
        """Update the implication graph for a variable, update literals in implication clause if needed"""
        node = self.implication_graph[var]
        node.value = self.assignments[var]
        node.level = self.level
        node.clause = clause

        # update reason for propagation (parent-child links in implication graph) if needed
        if clause:
            for v in [abs(lit) for lit in clause if abs(lit) != var]:
                node.parents.append(self.implication_graph[v])
                self.implication_graph[v].children.append(node)
            logging.info(f'Updated node {var} with parents: {node.parents}')

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
        """Test if a value is SAT in a formula"""
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
                # Already satisfied
                return False, None
            elif self.literal_value(literal) == UNDEFINED:
                # Check if this is the only undefined literal
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
        """Get all unassigned variables from all atomic propositions"""
        return filter(lambda v: v in self.assignments and self.assignments[v] == UNDEFINED, self.atomic_prop)

    def check_two_clause(self, clause):
        """Check if a clause is a 2-clause"""
        num_unassigned = sum([1 for lit in clause if self.assignments[abs(lit)] == UNDEFINED])
        return num_unassigned == 2

    def checkSAT(self):
        """Verify that the current assignment is satisfiable (value is 1)"""
        return self.formula_value(self.clauses)

    def count_unassigned_literals(self, clauses, polarity=True):
        """Count the unassigned literals in all clauses"""
        variables = {}
        unassigned = list(self.all_unassigned_vars())
        for clause in clauses:
            for lit in clause:
                if abs(lit) not in unassigned:
                    continue
                if lit in variables:
                    if polarity:
                        variables[lit] += 1
                    else:
                        variables[abs(lit)] += 1
                else:
                    if polarity:
                        variables[lit] = 1
                    else:
                        variables[abs(lit)] = 1
        return variables

    def get_unresolved_smallest_clauses(self):
        """Get unresolved smallest clause"""
        smallest_clause_size = -1
        for clause in self.clauses.union(self.learnt_clauses):
            if self.clause_value(clause) != UNDEFINED:
                continue
            if smallest_clause_size == -1 or smallest_clause_size > len(clause):
                smallest_clause_size = len(clause)

        # If all clauses are satisfied, just return all clauses
        if smallest_clause_size == -1:
            return self.clauses

        # Else return a list of k-clauses with the least k
        smallest_clauses = set()
        for clause in self.clauses.union(self.learnt_clauses):
            if self.clause_value(clause) != UNDEFINED:
                continue
            if len(clause) == smallest_clause_size:
                smallest_clauses.add(clause)

        return smallest_clauses

    def update_vsid_activity(self, learnt_clause):
        """Update VSID counter"""
        if self.PBV_heuristic != "VSID":
            pass

        # Increment activity and apply decay
        for lit in learnt_clause:
            self.vsid_activity[abs(lit)] += 1
        for lit in self.atomic_prop:
            self.vsid_activity[abs(lit)] *= self.vsid_decay

    def get_unassigned_literals_in_clause(self, clause):
        lits = []
        for lit in clause:
            if self.literal_value(lit) == UNDEFINED:
                lits.append(lit)
        return lits


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
    total_time = 0
    for i in range(num_tries):
        t1 = time.time()
        # solver = CDCLSolver("../data/test/uf150-645/uf150-01.cnf", "Lishuo")
        solver = CDCLSolver("../data/test/uf100-430/uf100-04.cnf", "Lishuo")
        ans = solver.solve()
        t2 = time.time()
        total_time += t2 - t1
        print("Answer: ", ans)
        print("Verify: ", solver.checkSAT())
        print("Branching: ", solver.num_PBV_invocations)
        print("Heuristic: ", solver.PBV_heuristic)
    print("Time: ", total_time / num_tries)

