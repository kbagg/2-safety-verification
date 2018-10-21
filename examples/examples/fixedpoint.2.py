from z3 import *
fp = Fixedpoint()

a, b, c = Bools('a b c')

fp.register_relation(a.decl(), b.decl(), c.decl())
fp.rule(a,b)
fp.rule(b,c)
fp.fact(c)
fp.set(engine='datalog', generate_explanations=True)
print fp.query(a)
print fp.get_answer()

