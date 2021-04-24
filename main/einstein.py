import re
import time
from CDCL import CDCLSolver


categories = {
"colour" : ["red", "green", "white", "yellow", "blue"],
"nationality" : ["Brit", "Swede", "Dane", "Norwegian", "German"],
"beverage" : ["tea", "coffee", "milk", "beer", "water"],
"cigar" : ["Pall Mall", "Dunhill", "Blends", "Bluemasters", "Prince"],
"pet" : ["dogs", "birds", "cats", "horse", "fish"]
}


def generate_fol():
    fol = {}
    for key in categories:
        for i in range(len(categories[key])):
            for j in range(1, 6):
                fol[len(fol) + 1] = f"{key}({j}, {categories[key][i]})"

    return fol


def generate_cnf(fol):
    houses = initialize_houses(fol)
    constrains = initialize_constrains(fol)
    hints = generate_hints()

    all_constrains = houses + constrains + hints

    output = ""
    output += "c\nc SAT instance of Einstein's Puzzle\nc\n"
    output += f"p cnf {len(fol)} {len(all_constrains)}\n"
    for constrain in all_constrains:
        for num in constrain:
            output += f"{num} "
        output += "0\n"

    return output


def generate_hints():
    hints = []
    # birt live in red:
    for i in range(1, 6):
        hints.append((-(i + 25), i))
        hints.append((i + 25, -i))

    # swede dog:
    for i in range(1, 6):
        hints.append((-(i + 30), (i + 100)))
        hints.append(((i + 30), -(i + 100)))

    # Dane tea:
    for i in range(1, 6):
        hints.append((-(i + 35), (i + 50)))
        hints.append(((i + 35), -(i + 50)))
    # Green left of white
    for i in range(1, 5):
        hints.append((-(i + 5), (i + 11)))
        hints.append(((i + 5), -(i + 11)))

    # green drink coffee
    for i in range(1, 6):
        hints.append((-(i + 5), (i + 55)))
        hints.append(((i + 5), -(i + 55)))

    # Pall mall bird
    for i in range(1, 6):
        hints.append((-(i + 75), (i + 105)))
        hints.append(((i + 75), -(i + 105)))

    # yellow house Dunhill
    for i in range(1, 6):
        hints.append((-(i + 15), (i + 80)))
        hints.append(((i + 15), -(i + 80)))

    # center milk
    hints.append((63,))

    # norwegian first
    hints.append((41,))

    # blends nex to cats
    hints.append((-86, 112))
    hints.append((-87, 111, 113))
    hints.append((-88, 112, 114))
    hints.append((-89, 113, 115))
    hints.append((-90, 114))

    # hosre next to dunhill
    hints.append((-116, 82))
    hints.append((-117, 81, 83))
    hints.append((-118, 82, 84))
    hints.append((-119, 83, 85))
    hints.append((-120, 84))

    # bluemasters drink beer
    for i in range(1, 6):
        hints.append((-(i + 90), (i + 65)))
        hints.append(((i + 90), -(i + 65)))

    # German prince
    for i in range(1, 6):
        hints.append((-(i + 45), (i + 95)))
        hints.append(((i + 45), -(i + 95)))

    # Norwegian next to blue
    hints.append((-41, 22))
    hints.append((-42, 21, 23))
    hints.append((-43, 22, 24))
    hints.append((-44, 23, 25))
    hints.append((-45, 24))

    # Blends next to water
    hints.append((-86, 72))
    hints.append((-87, 71, 73))
    hints.append((-88, 72, 74))
    hints.append((-89, 73, 75))
    hints.append((-90, 74))

    return hints


def initialize_houses(fol):
    counter = 0
    houses = []
    house = []
    for key in fol:
        if int(abs(key - 1) / 5) == counter:
            house.append(key)
        else:
            houses.append(tuple(house))
            house = []
            house.append(key)
            counter += 1
    houses.append(tuple(house))

    return houses


def initialize_constrains(fol):
    counter = 0
    constrains = []
    for key in fol:
        if int(abs(key - 1) / 25) == counter:
            for i in range(key + 1, (counter + 1) * 25 + 1):
                if int(abs(i - 1) / 5) == int(abs(key - 1) / 5):
                    constrains.append((-key, -i))
                if i % 5 == key % 5:
                    constrains.append((-key, -i))
        else:
            counter += 1
            for i in range(key + 1, (counter + 1) * 25 + 1):
                if int(abs(i - 1) / 5) == int(abs(key - 1) / 5):
                    constrains.append((-key, -i))
                if i % 5 == key % 5:
                    constrains.append((-key, -i))

    return constrains


def convert_mapping_to_ans(mapping):
    ans = []

    fol = generate_fol()
    for i in fol:
        if mapping[i] == 1:
            expr = re.search('\(([^)]+)', fol[i]).group(1).split(', ')
            expr[0] = int(expr[0])
            ans.append(expr)

    ans = sorted(ans)

    string = ""
    for i in range(1, 6):
        curr = [str(i), "0", "0", "0", "0", "0"]
        for j in ans:
            if j[0] == i:
                for index, cat in enumerate(categories):
                    if j[1] in categories[cat]:
                        curr[index + 1] = j[1]

        string += " ".join(curr) + "\n"
    return string

if __name__ == "__main__":
    with open('../data/einstein.cnf', 'w') as f:
        f.write(generate_cnf(generate_fol()))
        f.close()
    t1 = time.time()
    solver = CDCLSolver("../data/einstein.cnf")
    ans = solver.solve()
    t2 = time.time()
    print(t2 - t1)
    print(solver.num_PBV_invocations)
    print(convert_mapping_to_ans(ans))
