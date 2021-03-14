import copy
from main import parser
from main.helper import debug_print


def DPLL(file_name):
    debug_print("---- DPLL initiated ----")
    num_variables, clauses = parser.read_file_and_parse(file_name)
    a = ap_phi(clauses)
    sat, assignments = DPLL_helper(clauses, {}, 1, [])

    # Add extra propositions that doesn't matter
    if sat == "SAT":
        for i in a:
            if not (-i in assignments or i in assignments):
                assignments.append(i)
        return assignments
    return sat


def DPLL_helper(phi, dec_list, level, mapping):
    debug_print("DPLL helper called with " + str(phi))
    proplist, phi = unit_prop(phi, [])

    # Add proplist into mapping
    mapping_copy = copy.deepcopy(mapping)
    mapping_copy += proplist

    if not phi:
        return "SAT", mapping_copy
    if [] in phi:
        return "UNSAT", []

    dec_list[level] = proplist
    p = ap_phi(phi)[0]

    phi_l = copy.deepcopy(phi)
    phi_l.append([p])

    phi_not_l = copy.deepcopy(phi)
    phi_not_l.append([-p])

    check_l, correct_mapping = DPLL_helper(phi_l, dec_list, level + 1, mapping_copy)
    if check_l == "SAT":
        return "SAT", correct_mapping
    return DPLL_helper(phi_not_l, dec_list, level + 1, mapping_copy)


def find_unit(phi):
    """Returns true if a unit clause exists in phi, and return its index and clause, else return -1, None"""
    for clause in phi:
        if len(clause) == 1:
            return clause
    return None


def unit_prop(phi, proplist):
    """Perform unit propagation on phi"""
    debug_print("---- Performing unit prop on " + str(phi) + " with proplist " + str(proplist) + " ----")
    new_phi = phi
    unit_clause = ["aaa"]
    while unit_clause:
        if new_phi == {}:
            break
        unit_clause = find_unit(new_phi)
        if unit_clause:
            new_phi = find_up(new_phi, unit_clause[0])
            proplist.append(unit_clause[0])
            debug_print("Found unit clause: " + str(unit_clause) + "  Updated phi to: " + str(new_phi))
    return proplist, new_phi


def find_up(phi, p):
    """Find U_p of phi"""
    phi_copy = copy.deepcopy(phi)
    for clause in phi:
        if p in clause:
            phi_copy.remove(clause)
        elif -p in clause:
            phi_copy.remove(clause)
            new_clause = clause
            new_clause.remove(-p)
            phi_copy.append(new_clause)
    return phi_copy


def ap_phi(phi):
    ap = []
    for clause in phi:
        for prop in clause:
            if abs(prop) not in ap:
                ap.append(abs(prop))
    return ap


if __name__ == "__main__":
    print(DPLL("../data/base_case.txt"))
