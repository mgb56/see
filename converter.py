"""
Turns parsed statements into programs in the guarded-command language
Program in the guarded command language is output as a list of commands, 
all of which are either simple (assert, assume, or havoc) or a list of the form ['BRANCH', command1, command2]
We also build a new aexp structure REPL, where ["REPL", e, v_old, v_new] denotes the aexp e with all instances of v_old replaced by v_new (i.e. e[v_new/v_old])
"""
import copy

import program_parser


TRUE = ['=', ['INT', 0], ['INT', 0]]
FALSE = ['=', ['INT', 0], ['INT', 1]]

def replace(B, var, fresh_var):
    
    """
    Replace all occurences of var with fresh var in B
    """
    if B == var:
        return fresh_var
    elif not isinstance(B, list):
        return B
    elif B[0] in ['exists', 'forall'] and var in B[1]:
        return B
    else:
        return[replace(n, var, fresh_var) for n in B]


assert replace(['a', 'b', 'c', 'd'], 'b', 'e') == ['a', 'e', 'c', 'd']
assert replace(['a', ['b', 'c'], ['c', ['b', 'b', ['b']]], 'd'], 'b', 'e') == ['a', ['e', 'c'], ['c', ['e', 'e', ['e']]], 'd']


def vars_in_statement(stmt):
    """
    Returns a set of all variables modified in the statement
    """
    vars_so_far = set()
    if stmt[0] == 'ASSIGN':
        vars_so_far.update({stmt[1]})  # pylint: disable=undefined-variable
    elif stmt[0] == 'DUALASSIGN':
        vars_so_far.update({stmt[1]})  # pylint: disable=undefined-variable
        vars_so_far.update({stmt[2]})  # pylint: disable=undefined-variable
    elif stmt[0] == 'ARRASSIGN':
        vars_so_far.update({stmt[1]})  # pylint: disable=undefined-variable
    else:
        for i in range (1, len(stmt)):
            if isinstance(stmt[i], list):
                vars_so_far.update(vars_in_statement(stmt[i]))  # pylint: disable=undefined-variable
    return vars_so_far


class FreshVarGenerator:
    def __init__(self, verbose=False):
        self.verbose = verbose
        self.i = 1000
    
    def next(self):
        si = str(self.i)
        for j in range(0, 10):
            si = si.replace(str(j), "abcdefghij"[j])
        si = "VAR_SYS_" + si
        if self.verbose:
            print(si)
        self.i += 1
        return si

    

def parsed_stmt_to_GC(parsed_stmt, fvg):
    """
    Parses a statement recursively. We must share the same fresh_var_generator throughout the program \
    (or have a randomized one) to avoid overlap
    TODO: Implement array stuff
    """
    translated = None
    if parsed_stmt[0] == 'SKIP':
        translated = [['ASSUME', TRUE]]
    elif parsed_stmt[0] == 'ASSIGN':
        fv = fvg.next()
        translated = [['ASSUME', ["=", ["VAR", fv], ["VAR", parsed_stmt[1]]]],
                  ['HAVOC', ["VAR", parsed_stmt[1]]],
                  ['ASSUME', ["=", ["VAR", parsed_stmt[1]], replace(parsed_stmt[2], parsed_stmt[1], fv)]]]
    
    elif parsed_stmt[0] == 'DUALASSIGN':  # Just do two separate assigns with temp variables
        fv1 = fvg.next()
        fv2 = fvg.next()
        translated = parsed_stmt_to_GC(['ASSIGN', fv1, parsed_stmt[3]], fvg) +\
            parsed_stmt_to_GC(['ASSIGN', fv2, parsed_stmt[4]], fvg) +\
            parsed_stmt_to_GC(['ASSIGN', parsed_stmt[1], ["VAR", fv1]], fvg) +\
            parsed_stmt_to_GC(['ASSIGN', parsed_stmt[2], ["VAR", fv2]], fvg)
    elif parsed_stmt[0] == 'ARRASSIGN':
        fv = 'ARR' + fvg.next()[3:]
        translated = [['ASSUME', ["=", ["ARR", fv], ["ARR", parsed_stmt[1]]]],
                  ['HAVOC', ["ARR", parsed_stmt[1]]],
                  ['ASSUME', ["=", ["ARR", parsed_stmt[1]], ["STORE", fv, parsed_stmt[2], parsed_stmt[3]]]]]

    elif parsed_stmt[0] == 'IF':
         translated = [['BRANCH', [['ASSUME', parsed_stmt[1]]] + parsed_stmt_to_GC(parsed_stmt[2], fvg), [['ASSUME', ['!', parsed_stmt[1]]]] + ([['SKIP']] if len(parsed_stmt) == 3 else parsed_stmt_to_GC(parsed_stmt[3], fvg))]]

    elif parsed_stmt[0] == 'WHILE':
        assertions = parsed_stmt[2:-1]
        modified_variables = vars_in_statement(parsed_stmt[-1])
        translated = [['ASSERT', a[1]] for a in assertions]
        translated += [['HAVOC', [v[:3], v]] for v in modified_variables]
        translated += [['ASSUME', a[1]] for a in assertions]
        translated += [['BRANCH', [['ASSUME', parsed_stmt[1]]] + parsed_stmt_to_GC(parsed_stmt[-1], fvg) + [['ASSERT', a[1]] for a in assertions] + [['ASSUME', FALSE]],
                                 [['ASSUME', ['!', parsed_stmt[1]]]]]]
    elif parsed_stmt[0] == 'CONCAT':
        # print(parsed_stmt)
        translated = parsed_stmt_to_GC(parsed_stmt[1], fvg) + parsed_stmt_to_GC(parsed_stmt[2], fvg)
    elif parsed_stmt[0] == 'PROGRAM':
        translated = [['ASSUME', pre[1]] for pre in parsed_stmt[2]] + parsed_stmt_to_GC(parsed_stmt[3], fvg) #+  [['ASSERT', post[1]] for post in parsed_stmt[3]]
    #print(translated)
    elif parsed_stmt[0] == 'ASSERT':
        translated = parsed_stmt[1]
    return translated

fvg = FreshVarGenerator()




with open(r"find_see.imp") as myFile:
    test_program = myFile.read()

_, parsed_stmt = program_parser.parse_statement(test_program)


print(parsed_stmt_to_GC(parsed_stmt, fvg))













