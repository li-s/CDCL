import copy

import parser

def DPLL(file_name):
    num_variables, clauses =  parser.read_file_and_parse(file_name)
    return DPLL_helper(clauses, [], 1)


def DPLL_helper(phi, dec_list, level, correct_mapping):
    proplist, phi = unit_prop(phi)
    if not phi:
        return "UNSAT", []
    if [] in phi:
        return "SAT", correct_mapping

    dec_list[level] = proplist
    p = ap_phi(phi)[0]

    phi_l = copy.deepcopy(phi)
    phi_l[len(phi) + 1 + 1] = p

    phi_not_l = copy.deepcopy(phi)
    phi_not_l[len(phi) + 1 + 1] = - p

    if DPLL_helper(phi_l, dec_list, level + 1) == "SAT", correct:
        return "SAT"
    return DPLL_helper(phi_not_l, dec_list, level + 1)

def ap_phi(phi):
    ap = []
    for index, clause in phi.items():
        for prop in clause:
            if abs(prop) not in ap:
                ap.append(abs(prop))
    return ap

if __name__ == "__main__":
    a = ap_phi({1: [-3], 2: [3, -1]})
    print(a)