from z3 import *

# Transition function declaration
trans = Function('transition', IntSort(), IntSort(), IntSort(), BoolSort())
err = Bool('error')

# Variables for the original models
x1, x2 , i = z3.Ints('x1 x2 i')
var_list = [x1, x2, i]

# Original model M
fp_orig = Fixedpoint()
fp_orig.declare_var(*var_list)
fp_orig.register_relation(trans)
fp_orig.register_relation(err.decl())

fp_orig.rule(trans(x1, x2, i), [x1 == 0, x2 > 1, i == 0])
fp_orig.rule(trans(x1 + 1, x2 + x1, i + 1), tr(x1, x2, i))
fp_orig.rule(err, [trans(x1, x2, i), x1 >= x2])

def copy_model(solver, old_vars):
	new_vars = ['%s_c' % string for string in old_vars]
	new_vars = [z3.Int(string) for string in old_vars]
	replace = [(old_vars[i], new_vars[i]) for i in range(len(old_vars))]

	# Replace rules, all variables replaced, functions remain same.
	new_rules = [substitute(*([rule]+replace)) for rule in solver.get_rules()]
	return new_rules, new_vars

# create duplicate/copy model M'
new_rules, new_vars = copy_model(fp_orig, var_list)
fp_copy = Fixedpoint()
fp_copy.declare_var(*new_vars)
fp_copy.register_relation(trans)
fp_copy.register_relation(err.decl())
for rule in new_rules:
	fp_copy.rule(rule)

# Self Composition of M and M', solved using SMT queries...........
# I wonder how to convert it to nomarl queries, hence keeping count = 1.
fp_sc = Fixedpoint()
vars_sc = var_list + new_vars
fp_sc.declare_var(*vars_sc)
# How to declare the new relations and all????
#---------------------------------------STUCK------------------------------------