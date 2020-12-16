from z3 import *

x = Int('x')
y = Int('y')

s = Solver()

s.add(x <= 10, x >= 0)

s.add(Not(x == 11))

print(s.check())

m = s.model()
print(m)
