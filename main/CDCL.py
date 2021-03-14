import parser

def CDCL(file_name):
    num_variables, clauses =  parser.read_file_and_parse(file_name)
    