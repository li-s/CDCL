import logging
from main import logger
from main import parser


TRUE = 1
FALSE = 0
UNDEFINED = -1


class CDCLSolver:

    def __init__(self, filepath):
        logger.init_logger()
        logging.info("---------Initializing CDCL Solver---------")
        self.filepath = filepath
        self.clauses = parser.read_file_and_parse(filepath)
        self.atomic_prop = self.get_ap(self.clauses)
        self.assignments = {i: UNDEFINED for i in self.atomic_prop}
        self.level = 0
        self.guess_trail = {}
        self.propagation_trail = {}    # dict - level:int -> literals:set
        self.reason = {}               # dict - literal:int -> clause:set

    def solve(self):
        if self.unit_propagation():
            return "UNSAT"
        while not self.all_variable_assigned():
            logging.info(f"Current decision level = {self.level}")
            x, v = self.pick_branching_var()
            logging.info(f"Pick {x} = {v}")
            self.level += 1
            self.assignments[x] = v
            self.guess_trail[self.level] = x
            self.reason[x] = (-1)
            self.propagation_trail[self.level] = []
            conflict = self.unit_propagation()
            if conflict:
                backtrack_level, learn_clause = self.conflict_analysis(conflict)
                if backtrack_level < 0:
                    return "UNSAT"
                else:
                    logging.info(f"Adding clause {learn_clause}")
                    self.clauses.add(frozenset(learn_clause))
                    self.backtrack(backtrack_level)
        return self.assignments

    def unit_propagation(self):
        while True:
            # A list of clauses that we will propagate in this iteration
            clauses_to_propagate = []
            for clause in self.clauses:
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
                # Add propagation trail if level > 0, we don't care if unit prop happened in level 0
                if self.level > 0:
                    self.propagation_trail[self.level].append(unit_literal)
                    self.reason[abs(unit_literal)] = clause

    def all_variable_assigned(self):
        """Returns true if all variables have assignment"""
        for assignment in self.assignments.values():
            if assignment == UNDEFINED:
                return False
        return True

    def pick_branching_var(self):
        """Pick a variable to branch, the first unassigned variable that does not make any clause UNSAT"""
        for variable, assignment in self.assignments.items():
            if assignment == UNDEFINED:
                if self.is_value_sat_in_formula(variable, TRUE):
                    return variable, TRUE
                if self.is_value_sat_in_formula(variable, FALSE):
                    return variable, FALSE
        return None, UNDEFINED

    def conflict_analysis(self, conflict_clause):
        """Perform conflict analysis and return the level to back jump to"""
        logging.info(f"Performing conflict analysis on clause {conflict_clause} at {self.level}")
        if self.level == 0:
            return -1, None
        c = conflict_clause
        while True:
            dependent_vars = self.find_dependencies(c, self.level)
            # If there's only 1 dependent vars then we are done and ready to back jump
            if len(dependent_vars) == 1:
                # If unit clause, go back to level 0
                if len(c) == 1:
                    return 0, c
                bj_level = self.level - 1
                # Check which level to back jump to
                while bj_level >= 0:
                    if len(self.find_dependencies(c, bj_level)) == 1:
                        break
                    bj_level -= 1
                return bj_level, c
            # Update c by resolving c with a dependency's cause
            dependent_var = dependent_vars[-1]
            c = self.resolution(c, self.reason[abs(dependent_var)], dependent_var)

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
        logging.info(f"Backtracking to decision level {backtrack_level}")
        logging.info(f"Reason: {self.reason}")
        for i in range(backtrack_level + 1, self.level + 1):
            logging.info(f"Popping decision level {i}")
            # Unassign guess trail
            self.assignments[abs(self.guess_trail[i])] = UNDEFINED
            del self.reason[abs(self.guess_trail[i])]
            # Unassign propagation trail
            for prop in self.propagation_trail[i]:
                self.assignments[abs(prop)] = UNDEFINED
                self.reason.pop(abs(prop), None)
            # Delete reason, guess trail, propagation trail
            del self.guess_trail[i]
            del self.propagation_trail[i]
        self.level = backtrack_level

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
        assignment = self.assignments[abs(literal)]
        if assignment == UNDEFINED:
            return UNDEFINED
        if literal < 0:
            return TRUE if assignment == FALSE else FALSE
        else:
            return TRUE if assignment == TRUE else FALSE

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


if __name__ == "__main__":
    solver = CDCLSolver("../data/base_case.txt")
    print("Answer ", solver.solve())
