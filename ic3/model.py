from pyzz import *

N = netlist() # construct a netlist

def bit_vec(n):
    bits = [ 0 for i in xrange(32) ]
    for i in xrange(32):
        bits[31-i] = n%2
        n = n/2
    return bits

def create_int(v=0):
    v_bitvec = bit_vec(v)
    res = []
    for i in xrange(32):
        res.append( N.add_Flop( init=v_bitvec[i] ) )
    return res

def bool_vec_from_bit_vec(y):

    b = [ 0 for i in xrange(32) ]
    
    for i, bit in enumerate(y):
        if bit == 0:
            b[i] = ~N.get_True()
        else:
            b[i] = N.get_True()

    return b

def equals(x, y):

    res = N.get_True()
    a = x
    b = y
    
    if isinstance(y[0], int):
        # if y is a bit-vector
        b = bool_vec_from_bit_vec(y)

    for i in xrange(32):
        res = res & a[i].equals(b[i])

    return res

def add(x, y):

    res = [ 0 for i in xrange(32) ]
    carry = ~N.get_True()
    a = x
    b = y

    if isinstance(y[0], int):
        # if y is a bit-vector
        b = bool_vec_from_bit_vec(y)
                
    for i in xrange(32):

        res[31-i] = a[31-i] ^ b[31-i] ^ carry
        carry = ( a[31-i] & b[31-i] ) | ( (x[31-i] | b[31-i] ) & carry ) 

    return res

def greater_than(x, y):

    if len(x) == 1:
        return x[0] & ~y[0]
    
    a = x[0]
    b = y[0]
    
    if isinstance(y[0], int):
        if y[0] == 0:
            b = ~N.get_True()
        else:
            b = N.get_True()

    return ( a & ~b ) | ( a.equals(b) & greater_than( x[1:], y[1:] ) )

# creating variables
x = create_int()
y = create_int(1)

x_plus_one = add( x, bit_vec(1) )
x_plus_y = add( x, y )

# setting next state function
for i in xrange(32):
    x[i][0] = x_plus_one[i]
    y[i][0] = x_plus_y[i]

N.add_property( greater_than( x, y ) )

N.write_aiger('test1.aig')
