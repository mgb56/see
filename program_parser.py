import string
import re


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
    s = re.sub("\s+", ''.join([' '] * max_consec), s)  
    return s

assert(prune_whitespace("     \ta      b   c     d\n  e  ")) == "abcde"
assert(prune_whitespace("     \ta      b   c     d\n  e  ", 1)) == " a b c d e "
assert(prune_whitespace("     \ta      b   c     d\n  e  ", 2)) == "  a  b  c  d  e  "
assert(prune_whitespace("some\n \twords", 1)) == "some words"



def back_scan_for_phrases_outside_parens(scan_str, phrase_list):
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


assert back_scan_for_phrases_outside_parens("%0000", ["%"]) == (0, 1)
assert back_scan_for_phrases_outside_parens("0000%", ["%"]) == (4, 5)
assert back_scan_for_phrases_outside_parens("000%%00", ["%"]) == (4, 5)
assert back_scan_for_phrases_outside_parens("000", ["%"]) is None
assert back_scan_for_phrases_outside_parens("0(%)((%)%)00", ["%"]) is None
assert back_scan_for_phrases_outside_parens("0(%)%(%)0", ["%"]) == (4, 5)
assert back_scan_for_phrases_outside_parens("00<=0", ["%"]) is None
assert back_scan_for_phrases_outside_parens("00<=0", ["<", "<="]) == (2, 4)
assert back_scan_for_phrases_outside_parens("00<=0", ["=", "<="]) == (2, 4)

def parse_aexp(in_str, assignments=None, should_sub=False):
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
            return [op, parse_aexp(aexp1, assignments, should_sub), parse_aexp(aexp2, assignments, should_sub)]
    if in_str[0] == "(" and in_str[-1] == ")":
        return parse_aexp(in_str[1:-1], assignments, should_sub)
    if in_str[0] in '0123456789':
        return(["INT", int(in_str)])
    fb, lb = in_str.find('['), in_str.rfind(']')
    if fb != -1 and lb != -1:  # Given brackets for a list index, process it as that
        return ["ARR", "ARR_"+in_str[:fb], parse_aexp(in_str[fb+1:lb], assignments, should_sub)]
    for c in ["()+-*/%<>=![]"]:
        assert c not in in_str

    if should_sub and in_str in assignments:
        return assignments[in_str]

    return(["VAR", in_str])

assert parse_aexp("x+2*3%4") == ['+', ['VAR', 'x'], ['%', ['*', ['INT', 2], ['INT', 3]], ['INT', 4]]]
assert parse_aexp("(5+6)*(4+2)%((7+8)/(5+6))") == ['%', ['*', ['+', ['INT', 5], ['INT', 6]], ['+', ['INT', 4], ['INT', 2]]], ['/', ['+', ['INT', 7], ['INT', 8]], ['+', ['INT', 5], ['INT', 6]]]]
assert parse_aexp("arr[x+2*3%4]") == ["ARR", "ARR_arr", parse_aexp("x+2*3%4")]


def parse_comp(in_str, assignments=None, should_sub=False):    
    in_str = prune_whitespace(in_str)
    break_idxs = back_scan_for_phrases_outside_parens(in_str, ["=", "!=", "<=", ">=", "<", ">"])
    if break_idxs is None:
        raise NotImplementedError

    aexp1, op, aexp2 = in_str[:break_idxs[0]], in_str[break_idxs[0]:break_idxs[1]], in_str[break_idxs[1]:]
    return [op, parse_aexp(aexp1, assignments, should_sub), parse_aexp(aexp2, assignments, should_sub)]

assert parse_comp("x>=5") == ['>=', ['VAR', 'x'], ['INT', 5]]
assert parse_comp("x<=5") == ['<=', ['VAR', 'x'], ['INT', 5]]
assert parse_comp("x!=5") == ['!=', ['VAR', 'x'], ['INT', 5]]
assert parse_comp("x=5") == ['=', ['VAR', 'x'], ['INT', 5]]


def parse_bexp(in_str, assignments=None, should_sub=False):
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
            return [quant, quant_vars, parse_bexp(in_str[end_vars+1:], assignments, should_sub)]

    for char_list in [["==>"], ["||"], ["&&"]]:
        last_checked = len(in_str)
        while last_checked != 0:
            break_idxs = back_scan_for_phrases_outside_parens(in_str[:last_checked], char_list)
            if break_idxs is not None: 
                if back_scan_for_phrases_outside_parens(in_str[:break_idxs[0]], ['forall', 'exists']) is None:  # Do not yet process things still bound by a quantifier
                    bexp1, op, bexp2 = in_str[:break_idxs[0]], in_str[break_idxs[0]:break_idxs[1]], in_str[break_idxs[1]:]
                    return [op, parse_bexp(bexp1, assignments, should_sub), parse_bexp(bexp2, assignments, should_sub)]
                else:
                    last_checked = break_idxs[0]
            else:
                last_checked = 0
    
    if in_str[0] == "!":
        return ["!", parse_bexp(in_str[1:], assignments, should_sub)]
    if in_str[0] == "(" and in_str[-1] == ")":
        return parse_bexp(in_str[1:-1], assignments, should_sub)


    return parse_comp(in_str, assignments, should_sub)

assert parse_bexp("x>2 && y<4 || z=6") == ['||', ['&&', ['>', ['VAR', 'x'], ['INT', 2]], ['<', ['VAR', 'y'], ['INT', 4]]], ['=', ['VAR', 'z'], ['INT', 6]]]
assert parse_bexp("x>2||y<4&&z=6") == ['||', ['>', ['VAR', 'x'], ['INT', 2]], ['&&', ['<', ['VAR', 'y'], ['INT', 4]], ['=', ['VAR', 'z'], ['INT', 6]]]]
assert parse_bexp("(x>2||x<2)&&!(y>2||y<2)") == ['&&', ['||', ['>', ['VAR', 'x'], ['INT', 2]], ['<', ['VAR', 'x'], ['INT', 2]]], ['!', ['||', ['>', ['VAR', 'y'], ['INT', 2]], ['<', ['VAR', 'y'], ['INT', 2]]]]]
assert parse_bexp("  forall i  j k, j>i && exists l, k<=l || k>l") == ['forall', ['i', 'j', 'k'], ['&&', ['>', ['VAR', 'j'], ['VAR', 'i']], ['exists', ['l'], ['||', ['<=', ['VAR', 'k'], ['VAR', 'l']], ['>', ['VAR', 'k'], ['VAR', 'l']]]]]]
assert parse_bexp(" !( exists c b, c*c*b == n && c>1 && b>= 1 && c<pa) || pa * pa * (n / (pa * pa)) = n") == ['||', ['!', ['exists', ['c', 'b'], ['&&', ['&&', ['&&', ['=', ['*', ['*', ['VAR', 'c'], ['VAR', 'c']], ['VAR', 'b=']], ['VAR', 'n']], ['>', ['VAR', 'c'], ['INT', 1]]], ['>=', ['VAR', 'b'], ['INT', 1]]], ['<', ['VAR', 'c'], ['VAR', 'pa']]]]], ['=', ['*', ['*', ['VAR', 'pa'], ['VAR', 'pa']], ['/', ['VAR', 'n'], ['*', ['VAR', 'pa'], ['VAR', 'pa']]]], ['VAR', 'n']]]


def parse_assn(in_str):    
    """
    Represent assertions as [condition type, ASSN].
    """
    in_str = prune_whitespace(in_str, 1)
    while in_str.startswith(" "):
        in_str = in_str[1:]

    if in_str.startswith("pre"):
        return ["pre", parse_bexp(in_str[len("pre"):])]

    return parse_bexp(in_str)

