def bin(s):
    return str(s) if s<=1 else bin(s>>1) + str(s&1)

#add, sub, mul, div, or, and, lsh, rsh, neg, mod, xor and arsh.
class Tnum :
    def __init__(self, v, m):
        self.v = v
        self.m = m

    def __or__(self,x):
        return(Tnum(self.v | x.v,(self.v | x.m) & (self.m | x.v)))
    
    def __and__(self,x):
        return(Tnum(self.v & x.v,(self.v & x.m) | (self.m & x.v)))

    def __str__(self):
        return(bin(self.v) + ' ; ' + bin(self.m))

def Hand(pc) : return pc + 1
def Hor(pc) : return pc + 1
def Add(pc) : return pc + 1
def Jump (pc , k) : return pc + k

class LInst :
    def __init__(self, l : list):
        self.l = l
    
class Progr :
    def __init__(self, len, linst : LInst, lfun):
        self.len = len
        self.linst = linst
        self.lfun = lfun

    def __str__(self):
        return(str(self.len) + ' ; ' + str(self.linst) + ' ; ' + str(self.lfun))

a = Progr


def member(x,t):
    return((x&(~t.m))==t.v)

def well_formed(t):
    return(t.m & t.v == 0)

t1 = Tnum(0b0000110,0b0110000)
t2 = Tnum(0b0100010,0b0000101)
t3 = t1.__or__(t2)
t4 = t1.__and__(t2)
#print(t4)
#print (1|2)
#print(t3, t4)
#print(0b000011 & 0b000100)
#print(member(0b000011,t1))
#print(member(0b000010,t1))
#print(well_formed(t1))
def tnum_add(t1, t2):
    sv = t1.v + t2.v
    sm = t1.m + t2.m
    S = sv + sm
    q = S ^ sv
    h = q | t1.m | t2.m
    R= Tnum(sv & ~h, h)
    return R

#print(tnum_add(t1,t1))
class Interval :
    def __init__(self, a, b):
        self.a = a
        self.b = b
    
    def __add__(self,x):
        if type(x)==Interval :
            return(Interval(self.a + x.a,self.b + x.b))
        if type(x)==int :
            return(Interval(self.a + x,self.b + x))
    
    def __sub__(self,x):
        if type(x)==Interval :
            return(Interval(self.a - x.b,self.b - x.a))
        if type(x)==int :
            return(Interval(self.a - x,self.b - x))

    def __mul__(self,x):
        if type(x)==Interval :
            return(Interval(self.a * x.a,self.b * x.b))
        if type(x)==int :
            return(Interval(self.a*x,self.b*x))

    def __str__(self):
        return('['+str(self.a) + ',' + str(self.b)+']')

i1 = Interval(2,5)
i2 = Interval(4,8)
i3 = i1 + i2
i4 = i2 - i1
i5 = i1*i2

def plus_grand_div_impair(n):
    m=0
    for i in range(int(n)):
        if (2*i+1)<=n:
            if n%(2*i+1)==0:
                m = (2*i+1)
    return m

def Collatz_Conway(n):
    u = n
    l = [u]
    while u != 1 and len(l)<100 :
        if u%2 == 0 :
            u = plus_grand_div_impair(u)
        else :
            u = int((3*u+1)/2)
        l.append(u)
    return l



#print(i1,i3,i4,i5)
#print(i1*2)


