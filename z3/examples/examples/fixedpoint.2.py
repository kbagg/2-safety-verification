<<<<<<< HEAD

=======
from z3 import *
>>>>>>> 2ca60cd8aa1a3263a3db6d0ebc19aebab1e7bbad
fp = Fixedpoint()

a, b, c = Bools('a b c')

fp.register_relation(a.decl(), b.decl(), c.decl())
fp.rule(a,b)
fp.rule(b,c)
fp.fact(c)
<<<<<<< HEAD
fp.set(generate_explanations=True, engine='datalog')
=======
fp.set(engine='datalog', generate_explanations=True)
>>>>>>> 2ca60cd8aa1a3263a3db6d0ebc19aebab1e7bbad
print fp.query(a)
print fp.get_answer()

