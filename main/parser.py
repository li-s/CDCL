import re
import logging
from main import logger


def read_file_and_parse(file_name):
    """Read file and return CNF clauses"""
    logger.init_logger()
    f = open(file_name, "r")
    p_line = f.readline().strip()
    while p_line[0] == 'c':
        p_line = f.readline().strip()
    p_line_split = [i for i in re.compile("\\s+").split(p_line)]
    num_variables = int(p_line_split[2])
    num_clauses = int(p_line_split[3])
    logging.info(f"[Parser] Num variables: {num_variables}")
    logging.info(f"[Parser] Num clauses: {num_clauses}")

    cnf = set()
    for i in range(num_clauses):
        next_line = f.readline().strip()
        clause = frozenset([int(i) for i in re.compile("\\s+").split(next_line) if i != "0"])
        cnf.add(clause)

    return cnf, num_variables
