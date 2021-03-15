import copy

from main import parser_dict

def CDCL(file_name):
    num_variables, clauses =  parser_dict.read_file_and_parse(file_name)

    atomic_props = ap_phi(clauses)
    sat, assignments = CDCL_helper({0: clauses}, {0 : None}, 1, {0 : None})

    # print(f"assignments {assignments}")
    # Convert dictionary to list
    correct_assignments = []
    for index, assignments in assignments.items():
        if index != 0:
            correct_assignments += assignments

    # Add extra propositions that can either be true or false
    if sat == "SAT":
        for i in atomic_props:
            if not (-i in correct_assignments or i in assignments):
                correct_assignments.append(i)
        return correct_assignments
    return sat


def CDCL_helper(clauses_level, decicion_level, level, mapping):
    '''
    Main function for CDCL
    Inputs:
    clauses_level: the clausesss we are working with at each level (e.g {0 : all clauses, 1 : reduced clauses, 2 : ...})
    decision_level: the decisions we have made and the prop_list resulted from the decision at each level ({0 : None, 1 : (prop, [])})
    level: the current level we are operating on
    mapping: the mappings which we have guessed thus far for each level ({0 : None, 1 : [prp list]})

    outputs:
    If the formula in clauses_level is satisfying: "SAT", mappings dict
    Otherwise if unsat: "Unsat", []
    '''
    # Make copies of each dictionary as we want to keep immutability
    mapping_copy = copy.deepcopy(mapping)
    decicion_level_copy = copy.deepcopy(decicion_level)
    clauses_level_l = copy.deepcopy(clauses_level)
    clauses_level_not_l = copy.deepcopy(clauses_level)

    # Find the list of propositions at the current level, and the reduced formula
    prop_list, phi = unit_prop(clauses_level[level - 1])
    # Add proplist into mapping
    mapping_copy[level] = prop_list

    # If our fomula is empty, we have a satisfying assignment
    if phi == {}:
        return "SAT", mapping_copy
    # If our fomula contains box, but we are on the first level, we know our formula is unsat
    if level == 1 and [] in phi.values():
        return "UNSAT", []
    # If our fomula contains box, and we are not on first level, perform the CDCL step
    if level != 1 and [] in phi.values():
        '''
        Idea:
        1. find clauses that are used to get current prop list
        2. find all prop in the clauses (in level 0)
        2.5 find all props in decision level that help us get all the props in the clauses 
        2.7 repeat 1-2.5
        3. find all same props in decision_level
        4. jump up to the highest decision_level with the clause + 1
        5. jump up to the highest clauses_level with the clause + 1
        6. add in all the props into new clause
        '''
        # print(f"clauses_level {clauses_level}\ndecision_level {decicion_level}\nprop_list {prop_list}\nphi {phi}")
        # Find the index of all clauses that have been reduced to the proplist at the current level.
        affected_clauses = find_clauses(prop_list, clauses_level[level - 1])
        # print(affected_clauses)
        # Find all props of these clauses from the original formula, and props of any formula containing these props
        all_props = find_props(affected_clauses, clauses_level[0])
        # print(all_props)

        # Find all of the decisions that have resulted in a proplist containing those props we have found,
        # and the level closest to the root which has the decision
        all_decisions, highest_level = find_decisions(all_props, decicion_level_copy)
        # print(f"all decisions {all_decisions}, level {highest_level}")
        
        # Remove all the clauses after the level in clauses_level
        new_clauses_level = {}
        for index, clause in clauses_level.items():
            if index < highest_level:
                new_clauses_level[index] = clause
        current_clause = new_clauses_level[highest_level - 1]
        current_clause[list(current_clause.keys())[-1] + 1] = all_decisions

        # Remove all decisions after the level in decision_level
        new_decision_level = {}
        for index, decision in decicion_level.items():
            if index < highest_level:
                new_decision_level[index] = decision

        # Remove all mapping after the level in mapping_level
        new_mapping_level = {}
        for index, map in mapping.items():
            if index < highest_level:
                new_mapping_level[index] = map

        # print(f"new clauses {new_clauses_level}\nnew decision {new_decision_level}\nmap {new_mapping_level}")

        # Call CDCL with our new clauses, decisions and mapping, along with our new highest level
        return CDCL_helper(new_clauses_level, new_decision_level, highest_level, new_mapping_level)

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
    '''
    Finds all atomic propositions in formula
    '''
    ap = []
    for item, clause in phi.items():
        for prop in clause:
            if abs(prop) not in ap:
                ap.append(abs(prop))
    return ap

def find_clauses(prop_list, clauses):
    '''
    Finds all clauses that contains propositions in the prop_list
    '''
    clause_list = []
    for index, clause in clauses.items():
        for p in prop_list:
            if p in clause or -p in clause:
                clause_list.append(index)

    return list(set(clause_list))

def find_props(affected_clauses, clauses):
    '''
    Finds all propositions contained in the clause indicated by affected_clauses
    Input:
    affected_clauses: List of clauses by their index number
    clauses: formla
    '''
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
    '''
    Finds all the decisions that have resulted in the prositions in prop_list, and 
    the level of the decision closest to the first level
    '''
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