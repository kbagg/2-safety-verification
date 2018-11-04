from z3 import *

# find a way to encode relations as well in addition to functions.
fun = Function('fun', IntSort(), IntSort(), BoolSort())
err = Bool('err')
# for model M
fp1 = Fixedpoint()

fp1.register_relation(fun)
fp1.register_relation(err.decl())

x, i = z3.Ints('x i')
l = [x, i]
fp1.declare_var(*l) # Important to have variables in traces, to see diff, print ans without it.

fp1.rule(fun(x, i), [x == 1, i == 0])
fp1.rule(fun(x + 2, i + 1), fun(x, i))

fp1.rule(err, [fun(x, i), i >= x]) # find a way to encode error relation/function-------------found!!!

# Query for all other variables and calculate the count, i.e number of steps take in M that will be used to solve model M'
fp1.query(And(fun(x, i), x==9))
ans = fp1.get_answer()

count = ans.arg(0).children()[-1] # assuming count is the last varibale int he list of variables
print(ans.arg(0).children()[-1]) # The value of the last variable count, i.e. i in this case

count = len(ans.children())-1 # length of trace - 1
print(len(ans.children())-1) # number of states - 1 = number of steps taken. (Will use this in case over approximation is used as indicated by sir)
print(fp1.help())
# for model M'
fp2 = Fixedpoint()

fp2.register_relation(fun)
fp2.register_relation(err.decl())

a, j = z3.Ints('a, j')
fp2.declare_var(a,j)

fp2.rule(fun(a, j), [a == 1, j == 0])
fp2.rule(fun(a + 2, j + 1), fun(a, j))
fp2.rule(err, [fun(a, j), j >= a])

found = fp2.query(And(fun(a, j), a==9, j==count))
if found:
	print("Yayy, it worked!")