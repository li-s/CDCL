from queue import Queue

TRUE = 1
FALSE = -1
UNDEFINED = 0


class Literal:
    """Literal class"""

    def __init__(self, variable, index):
        self.variable = variable
        self.index = index

    def negation(self):
        """Immutable negation operation"""
        return Literal(-self.variable, self.index)

    def sign(self):
        return self.variable > 0


class VarOrder:
    ref_to_assigns = {}
    ref_to_activity = {}

    def newVar(self):
        pass

    def update(self, x):
        pass

    def updateAll(self):
        pass

    def undo(self, x):
        pass

    def select(self):
        pass






class Solver:

    def __init__(self):
        # Constraints database
        self.constraints = []
        self.learnts = []
        self.clause_increment = 0.0
        self.clause_decay = 0.0

        # Variable order
        self.activity = []
        self.variable_increment = 0.0
        self.variable_decay = 0.0
        self.var_order = None

        # Propagation
        self.watches = {}
        self.undos = {}
        self.propQ = Queue()

        # Assignments
        self.assigns = {}
        self.trail = []
        self.trail_lim = []
        self.reason = {}
        self.level = {}
        self.root_level = 0

    def nVars(self):
        return len(self.assigns)

    def nAssigns(self):
        return len(self.assigns)

    def nConstraints(self):
        return len(self.constraints)

    def nLearnts(self):
        return len(self.learnts)

    def value(self, x):
        return self.assigns[x]

    def value(self, lit):
        return -self.assigns[lit.variable] if lit.sign() else self.assigns[lit.variable]

    def decisionLevel(self):
        return len(self.trail_lim)


