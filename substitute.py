from z3 import *

fun = Function('fun', IntSort(), IntSort(), BoolSort())
err = Bool('err')
fp1 = Fixedpoint()

fp1.register_relation(fun)
fp1.register_relation(err.decl())

x, i = z3.Ints('x i')

# list of variables of original model, assuming count is last one
list1 = [x, i] 
fp1.rule(fun(x, i), [x == 1, i == 0])
fp1.rule(fun(x + 2, i + 1), fun(x, i))
fp1.rule(err, [fun(x, i), i >= x])

# list2 = ['x_%d' % j for j in range(len(list1))]
list2 = ['%s_m' % s for s in list1]
list2 = [z3.Int(s) for s in list2]
print(list2)

# rules to be replaced
replace = [(list1[i], list2[i]) for i in range(len(list1))]
print(replace)

# replaced rules, all variables replaced, functionas remain same.
new_model = [substitute(*([rule]+replace)) for rule in fp1.get_rules()]
print('Original model', fp1.get_rules())
print('Copy model', new_model)