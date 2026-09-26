# check_bit.py -- the machine's case tree for the adjacency bit (WP6) against the oracle of check_ports.py.
# Mirrors Defs.lean (RN, unmatchedN, coCountN, mateN, clSz, clIx, clId, gadAdj, adjF, kOf, nOf) and Machine/PredMath.lean (treeP, adjM).
import random, itertools
from collections import Counter
from check_ports import F, NONADJ

def mk(f):                       # the stream ns of a formula: [n, T, U, (var,sign)*]
    return [0, f.T, f.U] + [x for l in f.lits for x in l]

def slots(ns): return 2*ns[1]+3*ns[2]
def litV(ns,o): return ns[3+2*o]
def litS(ns,o): return ns[4+2*o]
def comp(ns,o,p): return litV(ns,o)==litV(ns,p) and litS(ns,o)!=litS(ns,p)
def clSz(ns,o): return 2 if o<2*ns[1] else 3
def clIx(ns,o): return o%2 if o<2*ns[1] else (o-2*ns[1])%3
def clId(ns,o): return o//2 if o<2*ns[1] else ns[1]+(o-2*ns[1])//3
def mate(ns,o,j): return o-clIx(ns,o)+(clIx(ns,o)+j+1)%clSz(ns,o)
def rank(ns,o): return sum(1 for x in range(o) if litV(ns,x)==litV(ns,o) and litS(ns,x)==litS(ns,o))
def coCount(ns,o): return sum(1 for x in range(slots(ns)) if litV(ns,x)==litV(ns,o) and litS(ns,x)!=litS(ns,o))
def RN(ns,o,j,o2,j2):
    S=slots(ns)
    if not (o<S and o2<S): return False
    if j<2 and j2<2 and j+j2+2==clSz(ns,o) and o2==mate(ns,o,j) and not comp(ns,o,o2): return True
    return 2<=j<4 and 2<=j2<4 and comp(ns,o,o2) and rank(ns,o2)==j-2 and rank(ns,o)==j2-2
def unmatched(ns,o,j):
    return j==4 or (j<2 and (clSz(ns,o)<=j+1 or comp(ns,o,mate(ns,o,j)))) or (2<=j<4 and coCount(ns,o)<=j-2)
def PEP(ns,o,p): return o!=p and (clId(ns,o)==clId(ns,p) or comp(ns,o,p))
def gad(t,t2):
    if not (t<7 and t2<7): return False
    c=7*t+t2
    return c not in (0,1,2,7,8,14,16,24,25,31,32,40,41,47,48)
def treeP(ns,u,v):
    o,r,p,r2=u//36,u%36,v//36,v%36
    if r==0:
        if r2==0: return PEP(ns,o,p)
        return o==p and (r2-1)%7==0 and unmatched(ns,o,(r2-1)//7)
    if r2==0: return o==p and (r-1)%7==0 and unmatched(ns,p,(r-1)//7)
    q,t,q2,t2=(r-1)//7,(r-1)%7,(r2-1)//7,(r2-1)%7
    return (o==p and q==q2 and gad(t,t2)) or (t==0 and t2==0 and RN(ns,o,q,p,q2))
def adjM(ns,w,w2):
    S=slots(ns); Nn=4 if S==0 else 36*S
    return w//Nn!=w2//Nn and (w%Nn==w2%Nn or (S!=0 and treeP(ns,w%Nn,w2%Nn)))
def gadref(t,t2): return t<7 and t2<7 and t!=t2 and (min(t,t2),max(t,t2)) not in NONADJ and (t,t2) not in NONADJ
if __name__=="__main__":
    assert all(gad(t,t2)==gadref(t,t2) for t in range(9) for t2 in range(9))
    rng=random.Random(11); n=0
    for _ in range(300):
        nv=rng.choice([1,2,2,3,3,4]); T=rng.randint(0,3); U=rng.randint(0,2)
        if T+U==0: continue
        lits=[(rng.randrange(nv),rng.randrange(2)) for _ in range(2*T+3*U)]
        if not all(c<=2 for c in Counter(lits).values()): continue
        f=F(T,U,lits); ns=mk(f); S=f.S
        if S>6: continue
        Nn=36*S
        for u in range(Nn):
            for v in range(Nn):
                assert treeP(ns,u,v)==f.adjp(u,v),(ns,u,v)
        # H at two classes: adjM = the oracle of check_ports
        K=f.p+10*S
        for w in random.Random(3).sample(range(K*Nn),min(200,K*Nn)):
            for w2 in random.Random(4).sample(range(K*Nn),50):
                ref=(w//Nn!=w2//Nn) and (w%Nn==w2%Nn or f.adjp(w%Nn,w2%Nn))
                assert adjM(ns,w,w2)==ref
        n+=1
    # S = 0: two classes of a graph on 4 vertices, no edges but the diagonal
    ns=[0,0,0]
    for w in range(8):
        for w2 in range(8): assert adjM(ns,w,w2)==(w//4!=w2//4 and w%4==w2%4)
    print("ok",n)
