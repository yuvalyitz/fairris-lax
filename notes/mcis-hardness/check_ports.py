# check_ports.py  --  verification of the uniform port construction (r = 5, 36 vertices per position)
# (from the architect's report; requires numpy, scipy, networkx)
import itertools, random
from collections import Counter
import numpy as np, networkx as nx
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

NONADJ = {(0,1),(0,2),(3,4),(5,6)}            # gadget X = K7 minus these; vertex 0 = a
def Xadj(t,s):
    return t!=s and (min(t,s),max(t,s)) not in NONADJ

class F:                                       # a [2,3]-formula: T two-clauses then U three-clauses; lits[o]=(var,sign)
    def __init__(s,T,U,lits): s.T,s.U,s.lits,s.S,s.p = T,U,lits,2*T+3*U,T+U
    def cl(s,o):                               # (clause id, size, index in clause, base)
        if o < 2*s.T: return (o//2,2,o%2,2*(o//2))
        q=o-2*s.T; return (s.T+q//3,3,q%3,2*s.T+3*(q//3))
    def comp(s,o,o2): return s.lits[o][0]==s.lits[o2][0] and s.lits[o][1]!=s.lits[o2][1]
    def rank(s,o): return sum(1 for x in range(o) if s.lits[x]==s.lits[o])
    def partner(s,o,j):                        # the port relation R
        c,sz,t,base=s.cl(o)
        if j in (0,1):
            if j+1<sz:
                m=base+(t+j+1)%sz
                if not s.comp(o,m): return (m,sz-2-j)
            return None
        if j in (2,3):
            for o2 in range(s.S):
                if s.comp(o,o2) and s.rank(o2)==j-2: return (o2,2+s.rank(o))
        return None
    def PE(s,o,o2): return o!=o2 and (s.cl(o)[0]==s.cl(o2)[0] or s.comp(o,o2))
    def adjp(s,u,v):                           # adjacency of G on 36*S vertices
        o,r=divmod(u,36); o2,r2=divmod(v,36)
        if r==0 and r2==0: return s.PE(o,o2)
        if r==0:
            j2,t2=divmod(r2-1,7); return o==o2 and t2==0 and s.partner(o,j2) is None
        if r2==0:
            j,t=divmod(r-1,7); return o==o2 and t==0 and s.partner(o2,j) is None
        j,t=divmod(r-1,7); j2,t2=divmod(r2-1,7)
        return (o==o2 and j==j2 and Xadj(t,t2)) or (t==0 and t2==0 and s.partner(o,j)==(o2,j2))

def brute_alpha(n,adj):
    best=0
    def rec(c,size):
        nonlocal best
        if size+len(c)<=best: return
        if not c: best=max(best,size); return
        v=c[0]; rec([x for x in c[1:] if x not in adj[v]],size+1); rec(c[1:],size)
    rec(list(range(n)),0); return best
def milp_alpha(n,edges):
    G=nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    cl=list(nx.find_cliques(G)); A=lil_matrix((len(cl),n))
    for i,c in enumerate(cl):
        for v in c: A[i,v]=1
    r=milp(c=-np.ones(n),constraints=LinearConstraint(A.tocsr(),-np.inf,np.ones(len(cl))),integrality=np.ones(n),bounds=Bounds(0,1))
    return int(round(-r.fun))
def sat(f,nv):
    return any(all(any(a[f.lits[o][0]]==f.lits[o][1] for o in range(f.S) if f.cl(o)[0]==c) for c in range(f.p))
               for a in itertools.product([0,1],repeat=nv))

if __name__ == "__main__":
    # 1. random formulas (many degenerate): G symmetric, 5-regular, alpha(G)=alpha(G0)+10S (S<=4), R an involution
    rng=random.Random(7); st=Counter()
    for _ in range(400):
        nv=rng.choice([1,2,2,3,3,4]); T=rng.randint(0,3); U=rng.randint(0,2)
        if T+U==0: continue
        lits=[(rng.randrange(nv),rng.randrange(2)) for _ in range(2*T+3*U)]
        if not all(c<=2 for c in Counter(lits).values()): continue
        f=F(T,U,lits); S=f.S
        if S>7: continue
        n=36*S; adj=[set() for _ in range(n)]
        for u in range(n):
            for v in range(n):
                a=f.adjp(u,v); assert a==f.adjp(v,u)
                if a: assert u!=v; adj[u].add(v)
        assert all(len(x)==5 for x in adj)
        for o in range(S):
            for j in range(5):
                pr=f.partner(o,j)
                if pr: assert f.partner(*pr)==(o,j) and pr[0]!=o
        g0=[set(o2 for o2 in range(S) if f.PE(o,o2)) for o in range(S)]; a0=brute_alpha(S,g0)
        if S<=4: assert milp_alpha(n,[(u,v) for u in range(n) for v in adj[u] if u<v])==a0+10*S; st["alpha-shift"]+=1
        assert a0<=f.p and ((a0>=f.p)==sat(f,nv)); st["ok"]+=1
    print("random:",dict(st))
    # 2. exhaustive small formulas: satisfiable <=> alpha(occurrence graph) >= p
    cnt=Counter()
    for (T,U,nv) in [(1,0,1),(1,0,2),(2,0,1),(2,0,2),(3,0,1),(3,0,2),(0,1,1),(0,1,2),(0,2,1),(0,2,2),(1,1,1),(1,1,2),(2,1,1),(2,1,2),(1,2,1),(0,2,3),(3,0,3),(2,0,3),(1,1,3)]:
        S=2*T+3*U
        for lits in itertools.product([(v,b) for v in range(nv) for b in (0,1)],repeat=S):
            if not all(c<=2 for c in Counter(lits).values()): continue
            f=F(T,U,list(lits)); g0=[set(o2 for o2 in range(S) if f.PE(o,o2)) for o in range(S)]
            a0=brute_alpha(S,g0); sv=sat(f,nv); assert a0<=f.p and ((a0>=f.p)==sv); cnt["sat" if sv else "unsat"]+=1
    print("exhaustive:",dict(cnt))
    # 3. the copy instance H for S=2, p=1: k=21 classes, n=72: regular of degree 6(k-1), even edge count 3 n k (k-1)
    f=F(1,0,[(0,1),(1,1)]); n=72; k=21
    adj=[set(v for v in range(n) if f.adjp(u,v)) for u in range(n)]
    Hadj=lambda w,w2: divmod(w,n)[0]!=divmod(w2,n)[0] and (w%n==w2%n or (w2%n) in adj[w%n])
    V=k*n
    print("H degrees",set(sum(1 for w2 in range(V) if Hadj(w,w2)) for w in range(0,V,37)),"expected",6*(k-1))
    E=sum(1 for w in range(V) for w2 in range(w+1,V) if Hadj(w,w2)); print("edges",E,E%2==0,3*n*k*(k-1))
