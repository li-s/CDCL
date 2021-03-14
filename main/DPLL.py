import copy
from main import parser
from main.helper import debug_print


def DPLL(file_name):
    debug_print("---- DPLL initiated ----")
    num_variables, clauses = parser.read_file_and_parse(file_name)
    return DPLL_helper(clauses, {}, 1, {})


def DPLL_helper(phi, dec_list, level, mapping):
    debug_print("DPLL helper called with " + str(phi))
    proplist, phi = unit_prop(phi, [])
    if [] in phi.values():
        return "UNSAT", []
    if not phi:
        return "SAT", []

    dec_list[level] = proplist
    # Select the first atomic proposition in phi
    p = ap_phi(phi)[0]

    largest_clause_index = list(phi)[len(phi)-1]
    print(largest_clause_index)
    phi_l = copy.deepcopy(phi)
    phi_l[largest_clause_index+1] = [p]

    phi_not_l = copy.deepcopy(phi)
    phi_not_l[largest_clause_index+1] = [-p]

    l_mapping = copy.deepcopy(mapping)
    l_mapping.append(p)

    l_not_mapping = copy.deepcopy(mapping)
    l_not_mapping.append(-p)

    check_l, correct_mapping = DPLL_helper(phi_l, dec_list, level + 1, l_mapping)
    if check_l == "SAT":
        return "SAT", correct_mapping
    return DPLL_helper(phi_not_l, dec_list, level + 1, l_not_mapping)


def find_unit(phi):
    """Returns true if a unit clause exists in phi, and return its index and clause, else return -1, None"""
    for index, clause in phi.items():
        if len(clause) == 1:
            return index, clause
    return -1, None


def unit_prop(phi, proplist):
    """Perform unit propagation on phi"""
    debug_print("---- Performing unit prop on " + str(phi) + " with proplist " + str(proplist) + " ----")
    new_phi = phi
    uc_index = 0
    while uc_index != -1:
        if new_phi == {}:
            break
        uc_index, uc_clause = find_unit(new_phi)
        if uc_index != -1:
            new_phi = find_up(new_phi, uc_clause[0])
            proplist.append(uc_clause)
            if uc_index != -1:
                debug_print("Found unit clause: " + str(uc_clause) + "  Updated phi to: " + str(new_phi))
    return proplist, new_phi


def find_up(phi, p):
    """Find U_p of phi"""
    phi_copy = copy.deepcopy(phi)
    for index, clause in phi.items():
        if p in clause:
            phi_copy.pop(index)
        elif -p in clause:
            phi_copy[index].remove(-p)
    return phi_copy


def ap_phi(phi):
    ap = []
    for index, clause in phi.items():
        for prop in clause:
            if abs(prop) not in ap:
                ap.append(abs(prop))
    return ap


if __name__ == "__main__":
    phi_test = {1: [1, -2], 2: [2222, 132112, -1], 3: [2], 4: [-1]}
    print(DPLL_helper(phi_test, {}, 1, []))
