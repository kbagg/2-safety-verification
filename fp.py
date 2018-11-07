# Changes made by me are put between ------ comments
# ----------------------
<<<<<<< HEAD
import z3
# ----------------------

tr = Relation('transition', IntSort(), IntSort())
err = Relation('error')

# model M
fp1 = Fixedpoint()
fp1.set(generate_explanations=True, engine='pdr')

fp1.register_relation(tr)

x, y = z3.Ints('x, y')

fp1.rule(tr(x, y), [x = 0, y > 1])
fp1.rule(tr(x + 1, y + x), tr(x,y))
fp1.rule(error, [tr(x, y), x >= y])

# model M' (M_d)
fp2 = Fixedpoint()
fp2.set(generate_explanations=True, engine='pdr')

fp2.register_relation(tr)

a, b = z3.Ints('a, b')

fp2.rule(tr(a, b), [a = 0, b > 1])
fp2.rule(tr(a + 1, b + a), tr(a, b))
fp2.rule(error, [tr(a, b), a >= b])
=======
from z3 import *
# ----------------------

tr = Function('transition', IntSort(), IntSort(), IntSort(), BoolSort())

# model M
fp1 = Fixedpoint()
fp1.set(engine='pdr')
fp1.register_relation(tr)
x, y , i = z3.Ints('x, y, i')
list1 = [x, y, i]  										# List of variables of first model

fp1.rule(tr(x, y, i), [x == 0, y > 1, i == 0])
fp1.rule(tr(x + 1, y + x, i + 1), tr(x, y, i))
# fp1.rule(And(False), [tr(x, y, i), x >= y]) 			# False has to be added as And(False) to work in z3

# model M' (M_d)
fp2 = Fixedpoint()
fp2.set(engine='pdr')

fp2.register_relation(tr)

a, b, j = z3.Ints('a, b, j')
list1 = [a, b, j]  										# List of variables of second (copy) model

fp2.rule(tr(a, b, j), [a == 0, b > 1, j == 0])
fp2.rule(tr(a + 1, b + a, j + 1), tr(a, b, j))
# fp2.rule(And(False), [tr(a, b, j), a >= b])			# Make the "bad" one work

# Think of a way that if we are given M and M' without i, j, i.e. the count, can we modify the models to introduce the count.
>>>>>>> 2ca60cd8aa1a3263a3db6d0ebc19aebab1e7bbad

# Self composition of M and M'
# -------------------------------------------------------
# Don't think model for Msc needs to be a fixed-point. It just has to solve normal SMT queries.
# -------------------------------------------------------
# trace = Relation('transition', IntSort(), IntSort(), IntSort(), IntSort())

# fp3 = Fixedpoint()
# fp3.set(generate_explanations=True, engine='pdr')

# fp3.register_relation(tr)

# X, Y, A, B = Ints('X, Y, A, B')

# fp3.rule(trace(X, Y, A, B), [X = 0, Y > 1, A = 0, B > 1])
# fp3.rule(trace(X + 1, Y + X, A + 1, B + A), trace(X, Y, A, B))
# fp3.rule(error, [trace(X, Y, A, B), X >= Y, A >= B])

# ----------------------------------------------

# This must use PDR Fixed point to check if Var1 is reachable in M. Here, Var1 is a list of integer values
<<<<<<< HEAD
def Check_Reachability_M(Var1):
    pass

# This must implement BMC in M' and return a tuple. Here, Var2 is a list of integer values and L is the number of steps taken from initial state of M' to Var2
def Check_Reachability_M_(Var2, L):
=======
def check_reachability_m(Var1):
    pass

 #    state = fp1.query(Var1)

 #    lastAnd = fp1.arg(0).children()[-1]
 #    i = 0
 #    trace = lastAnd.children()[1]
    
 #    while trace.num_args() > 0:
	# 	i = i + 1
	# 	trace = trace.children()[-1]

	# return i
q = Function('query')
fp1.register_relation(q)
fp1.rule(q, [tr(x, y, i)])


def get_length(ans):
	count = 0
	last _and = ans.arg(0).children()[-1]
    trace = last_and.children()[1]
    while trace.num_args() > 0:
		count = count + 1
		trace = trace.children()[-1]
	return count

# This must implement BMC in M' and return a tuple. Here, Var2 is a list of integer values and L is the number of steps taken from initial state of M' to Var2
def check_reachability_m_(Var2, L):

>>>>>>> 2ca60cd8aa1a3263a3db6d0ebc19aebab1e7bbad
    pass

Msc = z3.Solver()
# Assuming Var1 and Var2 are lists of variables of M and M'. For ex. Var1 = [x, y]
Var = Var1 + Var2
# Var_ is defined arbitrarily
Var_ = [z3.Int('l%d' % j) for j in range(len(Var))]

# This function must return true when there is a transition from Var to Var_
<<<<<<< HEAD
def Tr(Var, Var_):
=======
def tr(Var, Var_):
>>>>>>> 2ca60cd8aa1a3263a3db6d0ebc19aebab1e7bbad
    pass

# This has the assumption that Var is symmetric
# LowVar1 is a boolean array storing whether Var1[i] is low security variable or not. This must be assigned at the beginning of the program.
<<<<<<< HEAD
def Good(Var):
=======
def good(Var):
>>>>>>> 2ca60cd8aa1a3263a3db6d0ebc19aebab1e7bbad
    good = True
    for i, l in enumerate(Var):
        good = z3.And(good, z3.Implies(LowVar1(l), l == Var[i+len(Var)/2]))

# This should return a clause for representing if a state is a bad state
<<<<<<< HEAD
def Bad(Var):
=======
def bad(Var):
>>>>>>> 2ca60cd8aa1a3263a3db6d0ebc19aebab1e7bbad
    return z3.Not(Good(Var))
    
# Var and Var_ are 2 copies of the same set of variables for Msc representing 2 states of Msc
Msc.add(z3.Exists(Var + Var_), z3.And(Tr(Var, Var_), Bad(Var_)))

while True:
    if Msc.check() == z3.sat():
        # Extracting the exact value of Var which satisfied the query
        Var_Result = extract_model(Msc.model())

        # Checking if the counter-example is real
<<<<<<< HEAD
        Lm = Check_Reachability_M(Var_Result[len(Var)/2]) 
        result = Check_Reachability_M_(Var_Result[len(Var)/2:], Lm)
=======
        Lm = check_reachability_m(Var_Result[len(Var)/2]) 
        result = check_reachability_m_(Var_Result[len(Var)/2:], Lm)
>>>>>>> 2ca60cd8aa1a3263a3db6d0ebc19aebab1e7bbad

        if result == true:
            # We have a valid counter-example
            print "MODEL NOT SECURE"
            break
        else:
            # Add the suitable condition so that Var is not repeated
            Msc.add(Var != Var_Result)
    else:
        print "MODEL SECURE"

# ----------------------------------------------
