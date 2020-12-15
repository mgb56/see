from z3 import *

x = Int('x')
y = 11

s = Solver()

s.add(y + x < 10)

print(s.check())

m = s.model()
print(m)
