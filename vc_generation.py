"""
Backpropagates program written in guarded-command languange to compute the weakest precondition.
"""

import converter, program_parser
from converter import replace




def backprop_gc(gc, B, fvg):
    if not gc:
        return B

    if gc[-1][0] == 'SKIP':
        return backprop_gc(gc[:-1], B, fvg)

    elif gc[-1][0] == 'BRANCH':
        return backprop_gc(gc[:-1], ['&&', backprop_gc(gc[-1][1], B, fvg), backprop_gc(gc[-1][2], B, fvg)], fvg)

    elif gc[-1][0] == 'ASSERT':
        return backprop_gc(gc[:-1], ['&&', gc[-1][1], B], fvg)

    elif gc[-1][0] == 'ASSUME':
        return backprop_gc(gc[:-1], ['==>', gc[-1][1], B], fvg)

    elif gc[-1][0] == 'HAVOC':
        # replace all occurences of var with fresh var in B
        next_var = fvg.next()
        next_var = gc[-1][1][1] + next_var[3:]
        #print(gc[-1][1][1], next_var)
        return backprop_gc(gc[:-1], replace(B, gc[-1][1][1], next_var), fvg)
    else:
        raise NotImplementedError