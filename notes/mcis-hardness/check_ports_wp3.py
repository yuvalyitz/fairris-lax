# check_ports_wp3.py -- brute-force test of the WP3 Lean statements (RN, rankN, compN, mateN, unmatchedN, occGraphN)
# on token streams ns = [vars, T, U] ++ flatten [(var,sign)], transcribed literally from McisHard/Defs.lean.
import itertools
from collections import Counter
from check_ports import F

def getD(ns,i): return ns[i] if i<len(ns) else 0
def SlotsN(ns): return 2*getD(ns,1)+3*getD(ns,2)
def litV(ns,o): return getD(ns,3+2*o)
def litS(ns,o): return getD(ns,4+2*o)
def compN(ns,o,o2): return litV(ns,o)==litV(ns,o2) and litS(ns,o)!=litS(ns,o2)
def clSz(ns,o): return 2 if o<2*getD(ns,1) else 3
def clIx(ns,o): return o%2 if o<2*getD(ns,1) else (o-2*getD(ns,1))%3
def clId(ns,o): return o//2 if o<2*getD(ns,1) else getD(ns,1)+(o-2*getD(ns,1))//3
def mateN(ns,o,j): return o-clIx(ns,o)+(clIx(ns,o)+j+1)%clSz(ns,o)
def rankN(ns,o): return sum(1 for x in range(o) if litV(ns,x)==litV(ns,o) and litS(ns,x)==litS(ns,o))
def RN(ns,o,j,o2,j2):
    S=SlotsN(ns)
    return o<S and o2<S and ((j<2 and j2<2 and j+j2+2==clSz(ns,o) and o2==mateN(ns,o,j) and not compN(ns,o,o2)) or
      (2<=j<4 and 2<=j2<4 and compN(ns,o,o2) and rankN(ns,o2)==j-2 and rankN(ns,o)==j2-2))
def coCount(ns,o): return sum(1 for x in range(SlotsN(ns)) if litV(ns,x)==litV(ns,o) and litS(ns,x)!=litS(ns,o))
def unmatchedN(ns,o,j): return j==4 or (j<2 and (clSz(ns,o)<=j+1 or compN(ns,o,mateN(ns,o,j)))) or (2<=j<4 and coCount(ns,o)<=j-2)

cnt=Counter()
for (T,U,nv) in [(1,0,1),(1,0,2),(2,0,2),(2,0,3),(0,1,1),(0,1,2),(0,2,2),(1,1,2),(1,1,3)]:
    S=2*T+3*U
    for lits in itertools.product([(v,b) for v in range(nv) for b in (0,1)],repeat=S):
        if Counter(lits).most_common(1)[0][1]>2: continue     # CondN: rank<=1
        ns=[nv,T,U]+[x for l in lits for x in l]
        f=F(T,U,list(lits)); cnt["formulas"]+=1
        for o in range(S):
            for j in range(5):
                pr=f.partner(o,j)
                rs=[(o2,j2) for o2 in range(S) for j2 in range(5) if RN(ns,o,j,o2,j2)]
                assert len(rs)<=1                                   # func
                assert (rs[0] if rs else None)==pr, (ns,o,j,rs,pr)   # agrees with the Python partner
                assert (not rs)==unmatchedN(ns,o,j)                 # unmatched_iff
                for (o2,j2) in rs:
                    assert o2!=o and RN(ns,o2,j2,o,j)               # ne, symm
                    pass
        for o in range(S):
            for o2 in range(S):
                if o==o2: continue
                lhs=(clId(ns,o)==clId(ns,o2) or compN(ns,o,o2))
                rhs=any(RN(ns,o,j,o2,j2) for j in range(5) for j2 in range(5))
                assert lhs==rhs, (ns,o,o2)                          # posGraph_RN
                # simple: two ports of o into the same o2 coincide
                js={j for j in range(5) for j2 in range(5) if RN(ns,o,j,o2,j2)}
                assert len(js)<=1
        # rank_initial
        for v in range(nv):
            for s in (0,1):
                L=[o for o in range(S) if (litV(ns,o),litS(ns,o))==(v,s)]
                for q in range(4):
                    assert (any(rankN(ns,o)==q for o in L))==(q<len(L))
print(dict(cnt),"all WP3 statements hold")
