-------------------------------- MODULE Bits --------------------------------
LOCAL INSTANCE Integers

RECURSIVE And(_,_,_,_)
LOCAL And(x,y,n,m) == LET exp == 2^n
IN IF m = 0
THEN 0
ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2)
+ And(x,y,n+1,m \div 2)

x & y == And(x, y, 0, x)

=============================================================================
