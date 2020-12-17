import string
import re

DEBUG = False


"""
Contains all functions to parse the language into component expressions in tree form as delineated by lang.txt
Note: each level of the tree is a list. The first element is a string containing the operation (i.e. "%", "if", "ifelse")
and the subsequent elements are the parsed representations of the arguments in the same order as given by the spec
(i.e. for an if statement, it would be ["if", PARSED_BEXP_LIST, PARSED_BLOCK])
Note that there are a few special types: 
"VAR" (designating a variable reference) 
"INT" (designating an explicit integer)
"CONCAT" (designates two STMTs which are joined)
"ARR" (designates an array name and the aexp indexing into it, in the context of an AEXP
TODO: Variable name replacement in pre/post conditions?
      Pre/post conditions.
      Separate array and variable namespaces
"""

def prune_whitespace(s, max_consec=0):
    """
    Turns all whitespace into spaces and reduces length of whitespace sequences to max_consec >= 0
    Probably a clever way to regex this, but this is easier, and we only do O(1) passes per program anyway.
    """
    s = re.sub("\s+", ''.join([' '] * max_consec), s)    # pylint: disable=anomalous-backslash-in-string
    return s

# assert(prune_whitespace("     \ta      b   c     d\n  e  ")) == "abcde"
# assert(prune_whitespace("     \ta      b   c     d\n  e  ", 1)) == " a b c d e "
# assert(prune_whitespace("     \ta      b   c     d\n  e  ", 2)) == "  a  b  c  d  e  "
# assert(prune_whitespace("some\n \twords", 1)) == "some words"



def back_scan_for_phrases_outside_parens(scan_str, phrase_list):
    """
    Returns the indices of the first character of, and the first character after, the last occurence of any 
    phrase in phrase_list as (idx, idx) or None if none exists
    """
    phrase_list = sorted(phrase_list, key=len)[::-1]  # Get longest first to prevent things like recognizing "<" in "<="
    phrase_max_length = len(phrase_list[0])
    scan_len = len(scan_str)
    par_ct = 0
    for i in range (scan_len-1, -1, -1):
        if scan_str[i] in ")]}":
            par_ct += 1
        elif scan_str[i] in "([{":
            par_ct -= 1
            if par_ct < 0:
                raise NotImplementedError
        elif par_ct == 0:
            possible_phrase = scan_str[max(i-phrase_max_length+1, 0):i+1]  # Shortest string guaranteed to contain all phrases starting at that point.
            # We go left in order to not match proper suffixes (have to go same direction as scan)
            for p in phrase_list:
                if possible_phrase.endswith(p):
                    return (i+1-len(p), i+1)

    return None



# assert back_scan_for_phrases_outside_parens("%0000", ["%"]) == (0, 1)
# assert back_scan_for_phrases_outside_parens("0000%", ["%"]) == (4, 5)
# assert back_scan_for_phrases_outside_parens("000%%00", ["%"]) == (4, 5)
# assert back_scan_for_phrases_outside_parens("000", ["%"]) is None
# assert back_scan_for_phrases_outside_parens("0(%)((%)%)00", ["%"]) is None
# assert back_scan_for_phrases_outside_parens("0(%)%(%)0", ["%"]) == (4, 5)
# assert back_scan_for_phrases_outside_parens("00<=0", ["%"]) is None
# assert back_scan_for_phrases_outside_parens("00<=0", ["<", "<="]) == (2, 4)
# assert back_scan_for_phrases_outside_parens("00<=0", ["=", "<="]) == (2, 4)

def parse_aexp(in_str, assignments=None, should_sub=False):
    # if DEBUG:
        # print(in_str)
    
    """
    Note: naive top-down parsing like this is O(n^2), but bottom-up is harder to implement, and we shouldn't see massive aexps
    """
    in_str = prune_whitespace(in_str)
    
    if in_str == "":
        raise NotImplementedError

    for char_list in [["+", "-"], ["*", "/", "%"]]:  # Do lowest-to-highest precedence scan
        break_idxs = back_scan_for_phrases_outside_parens(in_str, char_list)
        if break_idxs is not None:
            aexp1, op, aexp2 = in_str[:break_idxs[0]], in_str[break_idxs[0]:break_idxs[1]], in_str[break_idxs[1]:]
            if aexp2 == '':
                raise NotImplementedError
            if aexp1 == '':
                if op == '-':  # Support negation
                    aexp1 = '0'
                else:
                    raise NotImplementedError
            return [op, parse_aexp(aexp1), parse_aexp(aexp2)]
    if in_str[0] == "(" and in_str[-1] == ")":
        return parse_aexp(in_str[1:-1])
    if in_str[0] in '0123456789':
        return(["INT", int(in_str)])
    fb, lb = in_str.find('['), in_str.rfind(']')
    if fb != -1 and lb != -1:  # Given brackets for a list index, process it as that
        return ["ARR", "ARR_"+in_str[:fb], parse_aexp(in_str[fb+1:lb])]
    for c in ["()+-*/%<>=![]"]:
        assert c not in in_str

    if should_sub and in_str in assignments:
            return assignments[in_str]

    return(["VAR", in_str])


# assert parse_aexp("x+2*3%4") == ['+', ['VAR', 'VAR_x'], ['%', ['*', ['INT', 2], ['INT', 3]], ['INT', 4]]]
# assert parse_aexp("(5+6)*(4+2)%((7+8)/(5+6))") == ['%', ['*', ['+', ['INT', 5], ['INT', 6]], ['+', ['INT', 4], ['INT', 2]]], ['/', ['+', ['INT', 7], ['INT', 8]], ['+', ['INT', 5], ['INT', 6]]]]
# assert parse_aexp("arr[x+2*3%4]") == ["ARR", "ARR_arr", parse_aexp("x+2*3%4")]

def parse_comp(in_str):
    # if DEBUG:
        # print(in_str)
    
    in_str = prune_whitespace(in_str)
    break_idxs = back_scan_for_phrases_outside_parens(in_str, ["=", "!=", "<=", ">=", "<", ">"])
    if break_idxs is None:
        raise NotImplementedError

    aexp1, op, aexp2 = in_str[:break_idxs[0]], in_str[break_idxs[0]:break_idxs[1]], in_str[break_idxs[1]:]
    return [op, parse_aexp(aexp1), parse_aexp(aexp2)]

# assert parse_comp("x>=5") == ['>=', ['VAR', 'VAR_x'], ['INT', 5]]
# assert parse_comp("x<=5") == ['<=', ['VAR', 'VAR_x'], ['INT', 5]]
# assert parse_comp("x!=5") == ['!=', ['VAR', 'VAR_x'], ['INT', 5]]
# assert parse_comp("x=5") == ['=', ['VAR', 'VAR_x'], ['INT', 5]]



def parse_bexp(in_str):

    # print(in_str)   
    in_str = prune_whitespace(in_str, 1)
    while in_str.startswith(" "):
        in_str = in_str[1:]
    while in_str.endswith(" "):
        in_str = in_str[:-1]
    
    for quant in ['forall', 'exists']:
        if in_str.startswith(quant + ' '):
            end_vars = in_str.find(",")
            start_vars = len(quant) + 1
            quant_vars = [v for v in in_str[start_vars:end_vars].split()]
            return [quant, quant_vars, parse_bexp(in_str[end_vars+1:])]

    for char_list in [["==>"], ["||"], ["&&"]]:
        last_checked = len(in_str)
        while last_checked != 0:
            break_idxs = back_scan_for_phrases_outside_parens(in_str[:last_checked], char_list)
            if break_idxs is not None: 
                if back_scan_for_phrases_outside_parens(in_str[:break_idxs[0]], ['forall', 'exists']) is None:  # Do not yet process things still bound by a quantifier
                    bexp1, op, bexp2 = in_str[:break_idxs[0]], in_str[break_idxs[0]:break_idxs[1]], in_str[break_idxs[1]:]
                    return [op, parse_bexp(bexp1), parse_bexp(bexp2)]
                else:
                    last_checked = break_idxs[0]
            else:
                last_checked = 0
    
    if in_str[0] == "!":
        return ["!", parse_bexp(in_str[1:])]
    if in_str[0] == "(" and in_str[-1] == ")":
        return parse_bexp(in_str[1:-1])
    return parse_comp(in_str)

# assert parse_bexp("x>2 && y<4 || z=6") == ['||', ['&&', ['>', ['VAR', 'VAR_x'], ['INT', 2]], ['<', ['VAR', 'VAR_y'], ['INT', 4]]], ['=', ['VAR', 'VAR_z'], ['INT', 6]]]
# assert parse_bexp("x>2||y<4&&z=6") == ['||', ['>', ['VAR', 'VAR_x'], ['INT', 2]], ['&&', ['<', ['VAR', 'VAR_y'], ['INT', 4]], ['=', ['VAR', 'VAR_z'], ['INT', 6]]]]
# assert parse_bexp("(x>2||x<2)&&!(y>2||y<2)") == ['&&', ['||', ['>', ['VAR', 'VAR_x'], ['INT', 2]], ['<', ['VAR', 'VAR_x'], ['INT', 2]]], ['!', ['||', ['>', ['VAR', 'VAR_y'], ['INT', 2]], ['<', ['VAR', 'VAR_y'], ['INT', 2]]]]]
# assert parse_bexp("  forall i  j k, j>i && exists l, k<=l || k>l") == ['forall', ['VAR_i', 'VAR_j', 'VAR_k'], ['&&', ['>', ['VAR', 'VAR_j'], ['VAR', 'VAR_i']], ['exists', ['VAR_l'], ['||', ['<=', ['VAR', 'VAR_k'], ['VAR', 'VAR_l']], ['>', ['VAR', 'VAR_k'], ['VAR', 'VAR_l']]]]]]
# assert parse_bexp(" !( exists c b, c*c*b == n && c>1 && b>= 1 && c<pa) || pa * pa * (n / (pa * pa)) = n") == ['||', ['!', ['exists', ['VAR_c', 'VAR_b'], ['&&', ['&&', ['&&', ['=', ['*', ['*', ['VAR', 'VAR_c'], ['VAR', 'VAR_c']], ['VAR', 'VAR_b=']], ['VAR', 'VAR_n']], ['>', ['VAR', 'VAR_c'], ['INT', 1]]], ['>=', ['VAR', 'VAR_b'], ['INT', 1]]], ['<', ['VAR', 'VAR_c'], ['VAR', 'VAR_pa']]]]], ['=', ['*', ['*', ['VAR', 'VAR_pa'], ['VAR', 'VAR_pa']], ['/', ['VAR', 'VAR_n'], ['*', ['VAR', 'VAR_pa'], ['VAR', 'VAR_pa']]]], ['VAR', 'VAR_n']]]

def parse_assn(in_str):
    # if DEBUG:
        # print(in_str)
    
    """
    Represent assertions as [condition type, ASSN].
    """
    in_str = prune_whitespace(in_str, 1)
    while in_str.startswith(" "):
        in_str = in_str[1:]

    if in_str.startswith("pre"):
        return ["pre", parse_bexp(in_str[len("pre"):])]

    return parse_bexp(in_str)

# assert parse_assn("pre 2<=n") == ['pre', ['<=', ['INT', 2], ['VAR', 'VAR_n']]]
# assert parse_assn("inv forall i, (0<=i&&i<n)==>a[i]!=x") == \
# ['inv', ['forall', ['VAR_i'], ['==>', ['&&', ['<=', ['INT', 0], ['VAR', 'VAR_i']], ['<', ['VAR', 'VAR_i'], ['VAR', 'VAR_n']]], ['!=', ['ARR', "ARR_a", parse_aexp("i")], ['VAR', 'VAR_x']]]]]
# assert parse_assn("post forall i j, 0 <= i && i <= j && j < n ==> a[i] <= a[j]") == \
# ['post', ['forall', ['VAR_i', 'VAR_j'], ['==>', ['&&', ['&&', ['<=', ['INT', 0], ['VAR', 'VAR_i']], ['<=', ['VAR', 'VAR_i'], ['VAR', 'VAR_j']]], ['<', ['VAR', 'VAR_j'], ['VAR', 'VAR_n']]], ['<=', ['ARR', 'ARR_a', ['VAR', 'VAR_i']], ['ARR', 'ARR_a', ['VAR', 'VAR_j']]]]]]


def parse_statement_recursive(in_str):
    # if DEBUG:
    #   print(in_str)
    
    """
    Here we treat blocks as statements, and have a rule for splitting statements, as recursing is cleaner this way.
    Note that concatenation of up to 2 is supported; further will 
    """
    in_str = prune_whitespace(in_str, max_consec=1)
    # print("printing pruned in_str")
    # print(in_str)
    # print()
    while in_str[-1] == " ":
        in_str = in_str[:-1]
    while in_str[0] == " ":
        in_str = in_str[1:]
    in_str = " " + in_str + " "
    start_this_stmt = None  # Holds the end of the starting term of the statement, if it is loopy
    end_last_stmt = None
    stmt_type = None
    else_idx = None
    then_idx = None
    inv_idxs = []
    pre_post_idxs = []
    do_idx = None
    is_idx = None
    if in_str.endswith(" end "):  # We know that this block starts with the last while/if at depth zero. Then we can search backward for that
        loop_depth = 0
        idx = len(in_str) - 1
        while idx >= 0:
            current_search_str = in_str[idx:idx+10]
            # print("current_search_str is:", current_search_str)
            # print()
            if current_search_str.startswith(" end "):
                loop_depth += 1
            elif current_search_str.startswith(" if "):
                loop_depth -= 1 
                if loop_depth == 0:
                    stmt_type = 'if'
                    start_this_stmt = idx+4
                    end_last_stmt = idx
                    break
            elif current_search_str.startswith(" while "):
                loop_depth -= 1
                if loop_depth == 0:
                    stmt_type = 'while'
                    start_this_stmt = idx+7
                    end_last_stmt = idx
                    break
            elif current_search_str.startswith(" program "):
                loop_depth -= 1
                if loop_depth == 0:
                    stmt_type = 'program'
                    start_this_stmt = idx+9
                    end_last_stmt = idx
                    break
            # Intermediate loop components which will be nice to have later
            elif current_search_str.startswith(" else "):
                if loop_depth == 1:
                    else_idx = idx
            elif current_search_str.startswith(" then "):
                if loop_depth == 1:
                    then_idx = idx
            elif current_search_str.startswith(" inv "):
                if loop_depth == 1:
                    inv_idxs += [idx]
            elif current_search_str.startswith(" pre "):
                if loop_depth == 1:
                    pre_post_idxs += [idx]
            elif current_search_str.startswith(" post "):
                if loop_depth == 1:
                    pre_post_idxs += [idx]
            elif current_search_str.startswith(" do "):
                if loop_depth == 1:
                    do_idx = idx
            elif current_search_str.startswith(" is "):
                if loop_depth == 1:
                    is_idx = idx
            
            idx -= 1
    elif in_str.endswith("; "):  # No nesting here, so easy.
        start_this_stmt = back_scan_for_phrases_outside_parens(in_str[:-2], [" end ", ";"])
        if start_this_stmt is None:
            end_last_stmt = start_this_stmt = 0
        else:
            end_last_stmt = start_this_stmt = start_this_stmt[1]
        stmt_type = ";"

    # print("stmt_type is:", stmt_type)
    # print()

    # print("start_this_stmt is:", start_this_stmt)
    # print("end_last_stmt:", end_last_stmt)
    # print()

    if start_this_stmt == 0:
        prev_stmt = None
    else:
        prev_stmt = in_str[:end_last_stmt] + " "

    # print("prev_stmt is:", prev_stmt)
    # print()


    if stmt_type is None:
        raise NotImplementedError
    elif stmt_type == "if":
        ret = ["IF"]
        ret += [parse_bexp(in_str[start_this_stmt:then_idx])]
        if else_idx is not None:
            ret += [parse_statement_recursive(in_str[then_idx + 6:else_idx])]
            ret += [parse_statement_recursive(in_str[else_idx + 6:-4])]
        else:
            ret += [parse_statement_recursive(in_str[then_idx + 6:-4])]

    elif stmt_type == "while":
        inv_idxs = sorted(inv_idxs)
        ret = ["WHILE"]
        if inv_idxs == []:
            ret += [parse_bexp(in_str[start_this_stmt:do_idx])]
        else:
            ret += [parse_bexp(in_str[start_this_stmt:inv_idxs[0]])]
            for i in range (0, len(inv_idxs)-1):
                ret += [parse_assn(in_str[inv_idxs[i]:inv_idxs[i+1]])]  # As we parse assertions as containing their tag (here, inv)
            ret += [parse_assn(in_str[inv_idxs[-1]:do_idx])]
        ret += [parse_statement_recursive(in_str[do_idx+4:-4])]

    elif stmt_type == "program":
        # print("pre_post_idxs is:", pre_post_idxs)
        pre_post_idxs = sorted(pre_post_idxs)
        pre_post_stmts = [parse_assn(s) for s in [in_str[pre_post_idxs[x]:pre_post_idxs[x+1]] for x in range(len(pre_post_idxs)-1)] + [in_str[pre_post_idxs[-1]:is_idx]]]
        # print("pre_post_stmts:", pre_post_stmts)
        pre_stmts = [x for x in pre_post_stmts if x[0] == "pre"]
        # print("pre_stmts:", pre_stmts)
        post_stmts = [x for x in pre_post_stmts if x[0] == "post"]
        # print("about to parse:", in_str[is_idx + 4: -4])
        # print()
        ret = ["PROGRAM", pre_stmts, parse_statement_recursive(in_str[is_idx + 4: -4])]
        # ret = ["PROGRAM", pre_stmts, parse_statement_recursive(in_str[is_idx + 4: -4]), post_stmts]



    else:
        current_stmt = in_str[start_this_stmt:]
        # print("current_stmt:", current_stmt)
        # Otherwise, is a semicolon statement

        # must be an assert
        if not back_scan_for_phrases_outside_parens(current_stmt, [":="]):
            ret = ["ASSERT", parse_assn(current_stmt[7:-2])]

        else:
            equal_pos = back_scan_for_phrases_outside_parens(current_stmt, [":="])[0]
            if '[' in current_stmt[:equal_pos]:  # If we are assigning into a list
                fb = current_stmt.find('[')
                lb = -1
                depth = 0
                for i in range(0, len(current_stmt)):
                    if current_stmt[i] == '[':
                        depth += 1
                    elif current_stmt[i] == ']':
                        depth -= 1
                        if depth == 0:
                            lb = i
                            break
                ret = ["ARRASSIGN", "ARR_"+prune_whitespace(current_stmt[:fb]), parse_aexp(current_stmt[fb+1:lb]), parse_aexp(current_stmt[equal_pos+2:-2])]
            elif back_scan_for_phrases_outside_parens(current_stmt, [","]) is not None:
                first_comma_idx = back_scan_for_phrases_outside_parens(current_stmt[:equal_pos], [","])[0]
                second_comma_idx = back_scan_for_phrases_outside_parens(current_stmt, [","])[0]
                ret = ["DUALASSIGN", prune_whitespace(current_stmt[:first_comma_idx]),  "VAR_"+prune_whitespace(current_stmt[first_comma_idx+1:equal_pos]),
                        parse_aexp(current_stmt[equal_pos+2:second_comma_idx]),  parse_aexp(current_stmt[second_comma_idx+1:-2])]
            else:
                ret = ["ASSIGN", prune_whitespace(current_stmt[:equal_pos]), parse_aexp(current_stmt[equal_pos+2:-2])]

    if prev_stmt is None or prev_stmt.isspace():
        return ret
    else:
        return ["CONCAT", parse_statement_recursive(prev_stmt), ret]


['find', [['VAR', 'VAR_N'], ['ARR', 'ARR_a']], [['pre', ['<=', ['INT', 0], ['VAR', 'VAR_N']]], ['pre', ['<=', ['VAR', 'VAR_N'], ['INT', 10]]]],\
 ['CONCAT', ['CONCAT', ['CONCAT', ['ASSIGN', 'VAR_n', ['INT', 0]], ['WHILE', ['&&', ['<', ['VAR', 'VAR_n'], ['VAR', 'VAR_N']],\
  ['!=', ['ARR', 'ARR_a', ['VAR', 'VAR_n']], ['VAR', 'VAR_x']]], ['CONCAT', ['ASSIGN', 'VAR_n', ['+', ['VAR', 'VAR_n'], ['INT', 1]]],\
   ['ASSERT', ['=', ['VAR', 'VAR_x'], ['INT', 1]]]]]], ['ASSERT', ['!', ['||', ['=', ['ARR', 'ARR_a', ['VAR', 'VAR_n']], ['VAR', 'VAR_x']],\
    ['forall', ['VAR_i'], ['==>', ['&&', ['<=', ['INT', 0], ['VAR', 'VAR_i']], ['<', ['VAR', 'VAR_i'], ['VAR', 'VAR_N']]],\
     ['!=', ['ARR', 'ARR_a', ['VAR', 'VAR_i']], ['VAR', 'VAR_x']]]]]]]], ['ASSERT', ['=', ['ARR', 'ARR_a', ['INT', 0]], ['VAR', 'VAR_i']]]]]


def parse_statement(in_str):
    in_str_tmp = prune_whitespace(in_str, max_consec=1)
    start_idx = in_str_tmp.find("(")
    end_idx = in_str_tmp.find(")")

    in_str_vars = in_str_tmp[start_idx+1:end_idx].split()

    var_list = [['ARR', 'ARR_' + s[:-2]] if s.endswith("[]") else ['VAR', 'VAR_' + s] for s in in_str_vars]

    parsed_stmt = parse_statement_recursive(in_str)
    parsed_stmt.insert(1, var_list)

    name = in_str_tmp[in_str_tmp.find("program ") + 8:start_idx]

    parsed_stmt[0] = name

    return parsed_stmt


# with open(r"find.imp") as myFile:
#     test_program = myFile.read()


# print(parse_statement(test_program))







