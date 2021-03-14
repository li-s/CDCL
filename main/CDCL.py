import copy

from main import parser_dict

def CDCL(file_name):
    num_variables, clauses =  parser_dict.read_file_and_parse(file_name)

    a = ap_phi(clauses)
    sat, assignments = CDCL_helper({0: clauses}, {0 : None}, 1, {0 : None})

    # print(f"assignments {assignments}")
    correct_assignments = []
    for index, assignments in assignments.items():
        if index != 0:
            correct_assignments += assignments
    # Add extra propositions that doesn't matter
    if sat == "SAT":
        for i in a:
            if not (-i in correct_assignments or i in assignments):
                correct_assignments.append(i)
        return correct_assignments
    return sat


def CDCL_helper(clauses_level, decicion_level, level, mapping):
    mapping_copy = copy.deepcopy(mapping)

    decicion_level_copy = copy.deepcopy(decicion_level)
    clauses_level_l = copy.deepcopy(clauses_level)
    clauses_level_not_l = copy.deepcopy(clauses_level)

    clauses_used = []

    prop_list, phi = unit_prop(clauses_level[level - 1])
    # Add proplist into mapping

    mapping_copy[level] = prop_list

    if phi == {}:
        return "SAT", mapping_copy
    if level == 1 and [] in phi.values():
        return "UNSAT", []

    if level != 1 and [] in phi.values():
        # print(f"clauses_level {clauses_level}\ndecision_level {decicion_level}\nprop_list {prop_list}\nphi {phi}")
        affected_clauses = find_clauses(prop_list, clauses_level[level - 1])
        # print(affected_clauses)
        all_props = find_props(affected_clauses, clauses_level[0])
        # print(all_props)

        all_decisions, highest_level = find_decisions(all_props, decicion_level_copy)
        # print(f"all decisions {all_decisions}, level {highest_level}")
        new_clauses_level = {}
        for index, clause in clauses_level.items():
            if index < highest_level:
                new_clauses_level[index] = clause

        current_clause = new_clauses_level[highest_level - 1]
        current_clause[list(current_clause.keys())[-1] + 1] = all_decisions

        new_decision_level = {}
        for index, decision in decicion_level.items():
            if index < highest_level:
                new_decision_level[index] = decision

        new_mapping_level = {}
        for index, map in mapping.items():
            if index < highest_level:
                new_mapping_level[index] = map

        # print(f"new clauses {new_clauses_level}\nnew decision {new_decision_level}\nmap {new_mapping_level}")

        return CDCL_helper(new_clauses_level, new_decision_level, highest_level, new_mapping_level)

    '''
    1. find clauses that are used to get current prop list
    2. find all prop in the clauses (in level 0)
    2.5 find all props in decision level that help us get all the props in the clauses 
    2.7 repeat 1-2.5
    3. find all same props in decision_level
    4. jump up to the highest decision_level with the clause + 1
    5. jump up to the highest clauses_level with the clause + 1
    6. add in all the props into new clause
    '''



    p = ap_phi(phi)[0]
    decicion_level_copy[level] = (p, prop_list)

    phi_l = copy.deepcopy(phi)
    phi_l[list(phi.keys())[-1] + 1] = [p]
    clauses_level_l[level] = phi_l

    phi_not_l = copy.deepcopy(phi)
    phi_not_l[list(phi.keys())[-1] + 1] = [-p]
    clauses_level_not_l[level] = phi_not_l

    check_l, correct_mapping = CDCL_helper(clauses_level_l, decicion_level_copy, level + 1, mapping_copy)
    if check_l == "SAT":
        return "SAT", correct_mapping
    return CDCL_helper(clauses_level_not_l, decicion_level_copy, level + 1, mapping_copy)

def unit_prop(phi):
    prop_list = []
    index, prop = find_unit(phi)
    while index >= 0:
        prop_list.append(prop)
        phi = update_phi(phi, prop)
        index, prop = find_unit(phi)
    return prop_list, phi


def find_unit(phi):
    '''
    Returns true if a unit clause exists in phi, and return its index and clause, else return -1, None
    '''
    for index, clause in phi.items():
        if len(clause) == 1:
            return index, clause[0]
    return -1, None

def update_phi(phi, prop):
    '''
    removes all clauses in phi with prop, and updates those with (not prop)
    '''
    phi_copy = copy.deepcopy(phi)
    for index, clause in phi.items():
        if prop in clause:
            phi_copy.pop(index)
        elif -prop in clause:
            phi_copy[index].remove(-prop)
            if len(clause) == 1:
                phi_copy[index] = []
    return phi_copy

def ap_phi(phi):
    ap = []
    for item, clause in phi.items():
        for prop in clause:
            if abs(prop) not in ap:
                ap.append(abs(prop))
    return ap

def ap_clause(phi):
    ap = []
    for clause in phi:
        for prop in clause:
            if abs(prop) not in ap:
                ap.append(abs(prop))
    return ap

def find_clauses(prop_list, clauses):
    clause_list = []
    for index, clause in clauses.items():
        for p in prop_list:
            if p in clause or -p in clause:
                clause_list.append(index)

    return list(set(clause_list))

def find_props(affected_clauses, clauses):
    affected_props = []
    for i in affected_clauses:
        if i in clauses.keys():
            affected_props += clauses[i]
    affected_props = [abs(i) for i in affected_props]

    return find_props_helper(list(set(affected_props)), clauses)

def find_props_helper(props, clauses):
    end = True
    while not end:
        for index, clause in clauses.items():
            if not all(elem in props for elem in clause):
                props += clause
                end = False
    return props

def find_decisions(all_props, decision_level):
    all_decisions = []
    highest_level = 1000000
    for level, choices in decision_level.items():
        if level != 0:
            if abs(choices[0]) in all_props:
                if level < highest_level:
                    highest_level = level
                all_decisions.append(choices[0])
    return all_decisions, level

if __name__ == "__main__":
    print(CDCL("../data/16v18c"))