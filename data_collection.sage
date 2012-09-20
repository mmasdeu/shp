
def mostRefs(n = 30):
    d = {}
    for obj in gc.get_objects():
        if type(obj) is types.InstanceType:
            cls = obj.__class__
        else:
            cls = type(obj)
        d[cls] = d.get(cls,0)+1
    counts = [(x[1],x[0]) for x in d.items()]
    counts = sorted(counts)[-n:]
    return reversed(counts)

def printCounts(counts = None, file = None):
    if counts is None: counts = mostRefs()
    if file is None: file = sys.stdout
    for c, obj in counts:
        file.write("%s %s\n" %(c,obj))

############
# Other curves
##########
candidates = []
for N in range(11,200,1):
    ff = ZZ(N).factor()
    if len(ff) == 1: continue
    try:
        E = EllipticCurve(str(N))
    except ValueError:
        continue
    for p,r in ff:
        if r > 1:
            continue
        M = ZZ(N/p)
        V = [q for q,s in M.factor() if s == 1 and q != 2]
        if len(V) > 1 or any([E.ap(q) == -1 for q in V]):
            candidates.append((N,p,len(ff)))
            if any([s == 2 for q,s in M.factor()]):
                print N,p

###################
## Generic
############
crlabel = '35a1'
p= 7
prec = 80
discbound = 200
save_data = False

###
E = EllipticCurve(crlabel)
N=E.conductor()
M=ZZ(N/p)
QQp = Qp(p,prec)
fname = 'ModSym_%s_%s_%s.sobj'%(crlabel,p,prec)

set_verbose(1)

if not os.path.isfile(fname):
    phi0 = ps_modsym_from_elliptic_curve(E).plus_part()
    phi0 = gcd([val.moments[0] for val in phi0.values()]) * phi0
    Phi = phi0.lift(p,M = prec,algorithm = 'stevens',eigensymbol = True)
    save(Phi,fname)

Phi = load(fname)

print fields_up_to(p,M,discbound)

data_collect = {}
failed_discs = []
for disc,_,_ in fields_up_to(p,M,discbound):
    if data_collect.has_key(disc):
        continue
    try:
        idx = failed_discs.index(disc)
        continue
    except ValueError:
        pass
    val = stark_heegner_points(Phi,E,disc,QQp,working_prec = 2*prec)
    data_collect[disc] = (val[1],val[2])
    print 'Done with discriminant %s !!'%disc
    if save_data == True:
        save(data_collect,'data_%s_%s.sobj'%(crlabel,p))

#### Tests for reciprocity
P,Jlist,emblist = val
F.<r> = QuadraticField(145)
r= F.gen()
w = F.ring_of_integers().ring_generators()[0]
H.<b> = F.hilbert_class_field()
EH = E.change_ring(H)
EF = E.change_ring(F)
Pts = [[],[],[],[]]
for kk in range(4):
    xx,yy = getcoords(E,Jlist[kk],prec)
    for ii,jj in product(range(4),repeat = 2):
        xg1 = p**(xx.valuation())*algdep(Qp(p,95)(ZZ(xx._ntl_rep()[0])),4).roots(H)[ii][0]
        xg2 = p**(xx.valuation())*algdep(Qp(p,95)(ZZ(xx._ntl_rep()[1])),4).roots(H)[jj][0]
        try:
            Pts[kk].append(EH.lift_x(xg1 + w*xg2))
            Pts[kk].append(EH.lift_x(xg1 + (w.trace()-w)*xg2))
        except:
            pass

for sgnvec in product([1,-1],repeat = 3):
    for vec in product(range(8),repeat = 3):
        P = Pts[0][0]+sgnvec[0]*Pts[1][vec[0]]+sgnvec[1]*Pts[2][vec[1]]+sgnvec[2]*Pts[3][vec[2]]
        if P[2] == 0:
            continue
        try:
            Q0 = F(P[0])
            Q1 = F(P[1])
            Q = EF([Q0,Q1])
            if Q.order()  > 100:
                print sgnvec,vec
        except:
            pass

### Some tests for 14A1
crlabel = '14a1'
p= 7
prec = 90
discbound = 200
save_data = False

###
E = EllipticCurve(crlabel)
N=E.conductor()
#assert E.ap(p) == 1
M=ZZ(N/p)
QQp = Qp(p,prec)
fname = 'ModSym_%s_%s_%s.sobj'%(crlabel,p,prec)
E = EllipticCurve(crlabel)
N=E.conductor()
#assert E.ap(p) == 1
M=ZZ(N/p)
QQp = Qp(p,prec)
fname = 'ModSym_%s_%s_%s.sobj'%(crlabel,p,prec)

set_verbose(1)

if not os.path.isfile(fname):
    phi0 = ps_modsym_from_elliptic_curve(E).plus_part()
    phi0 /= gcd([val.moments[0] for val in phi0.values()])
    Phi = phi0.lift(p,M = prec,algorithm = 'stevens',eigensymbol = True)
    save(Phi,fname)

Phi = load(fname)

D = 17
F.<r>  = QuadraticField(D)
r = F.gen()
EF = E.change_ring(F)

v0 = F.hom([Qp(p,prec).extension(F.gen().minpoly(),names = 'g').gen()])
Cp = v0.codomain()
ECp = E.change_ring(Cp)
W = find_optimal_embeddings(F)[0]
tau, gtau,sign,limits = find_tau0_and_gtau(v0,M,W)
J = indef_integral(Phi,tau,gtau,limits = limits)**sign
xg = 593/576
P = EF.lift_x(xg)

Jlog = J.log()

qE = E.tate_curve(p).parameter(prec = 100)
qlog = qE.log(branch = 0)

for phi in E.isogeny_class(return_maps = True)[2][0]:
    if phi == 0:
        continue
    Q = phi(P)
    nQ = Q
    while True:
        xQ = Cp(nQ[0])
        yQ = Cp(nQ[1])
        if xQ.valuation() <0:
            break
        nQ += Q
    Jgood = period_from_coords(p,phi.codomain(),[xQ,yQ],prec = 100)
    Jglog = Jgood.log()
    # Real parts
    JglogR = p**(Jglog.valuation())* Qp(p,100)(ZZ(Jglog._ntl_rep()[0]))
    JlogR = p**(Jlog.valuation())* Qp(p,100)(ZZ(Jlog._ntl_rep()[0]))
    qlogR = qlog
    print gp.lindep([JglogR,JlogR,qlogR])

    # Imag parts
    JglogI = p**(Jglog.valuation())* Qp(p,90)(ZZ(Jglog._ntl_rep()[1]))
    JlogI = p**(Jlog.valuation())* Qp(p,90)(ZZ(Jlog._ntl_rep()[1]))
    print gp.lindep([JglogI,JlogI])

###################
## Curve 33A1.
############
crlabel = '33a1'
p=11
prec = 80

E = EllipticCurve(crlabel)
N=E.conductor()
assert E.ap(p) == 1
M=ZZ(N/p)
QQp = Qp(p,prec)
fname = 'ModSym_%s_%s_%s.sobj'%(crlabel,p,prec)

set_verbose(1)

if not os.path.isfile(fname):
    Phi0 = ps_modsym_from_elliptic_curve(E).plus_part().lift(p,M = prec,algorithm = 'stevens',eigensymbol = True)
    scale_factor =  gcd([val.moment(0).rational_reconstruction() for val in Phi0.values()])
    Phi = 1/scale_factor * Phi0
    save(Phi,fname%(crlabel,p,prec))

Phi = load('ModSym_%s_%s_%s.sobj'%(crlabel,p,prec))

print fields_up_to(p,M,200)

data_collect = {}
failed_discs = []

for disc,_,_ in [(145,0,0)]: #fields_up_to(p,M,200):
    if data_collect.has_key(disc):
        continue
    try:
        signal.alarm(max_time)
        val = stark_heegner_points(Phi,E,disc,QQp,working_prec=500)
        data_collect[disc] = (val[1],val[2])
        print 'Done with discriminant %s !!'%disc
        save(data_collect,'data_%s_%s.sobj'%(crlabel,p))
    except RuntimeError:
        print 'Was taking too long (disc = %s)...'%disc
        failed_discs.append(disc)


###########################
# Try the minus points: does not seem to work this easy...
################
E = EllipticCurve('33a1')
N=E.conductor()
p=11
assert E.ap(p) == 1
M=ZZ(N/p)
#print 'aq =', E.ap(M)
prec = 80
QQp = Qp(p,prec)

# set_verbose(1)
# Phi0 = ps_modsym_from_elliptic_curve(E).minus_part().lift(p,M = prec,algorithm = 'stevens',eigensymbol = True)
# scale_factor =  gcd([val.moment(0).rational_reconstruction() for val in Phi0.values()])
# Phi = 1/scale_factor * Phi0
# set_verbose(0)
# save(Phi,'ModSym_33a1_11_80_minus.sobj')

Phi = load('ModSym_33a1_11_80_minus.sobj')

print fields_up_to(p,M,200)

data_collect = {}

for disc,_,_ in fields_up_to(p,M,200):
    if data_collect.has_key(disc):
        continue
    val = stark_heegner_points(Phi,E,disc,QQp)
    data_collect[disc] = (val[1],val[2])
    print 'Done with discriminant %s !!'%disc
    #save(data_collect,'data_33a1_11.sobj')

########################
### Curve 51A1
############
E = EllipticCurve('51a1')

N=E.conductor()
p=3
assert E.ap(p) == 1
M=ZZ(N/p)
#print 'aq =', E.ap(M)
prec = 200
QQp = Qp(p,prec)

# set_verbose(1)
# Phi0 = ps_modsym_from_elliptic_curve(E).plus_part().lift(p,M = prec,algorithm = 'stevens',eigensymbol = True)
# scale_factor =  gcd([val.moment(0).rational_reconstruction() for val in Phi0.values()])
# Phi = 1/scale_factor * Phi0
# set_verbose(0)
# save(Phi,'ModSym_51a1_3_200.sobj')

Phi = load('ModSym_51a1_3_200.sobj')

print fields_up_to(p,M,200)

data_collect = {}

for disc,_,_ in fields_up_to(p,M,200):
    if data_collect.has_key(disc):
        continue
    val = stark_heegner_points(Phi,E,disc,QQp)
    data_collect[disc] = (val[1],val[2])
    print 'Done with discriminant %s !!'%disc
    save(data_collect,'data_51a1_3.sobj')

##########
E = EllipticCurve('15a1')

N=E.conductor()
p=5
assert E.ap(p) == 1
M=ZZ(N/p)
#print 'aq =', E.ap(M)
prec = 80
QQp = Qp(p,prec)

# set_verbose(1)
# Phi0 = ps_modsym_from_elliptic_curve(E).plus_part().lift(p,M = prec,algorithm = 'stevens',eigensymbol = True)
# scale_factor =  gcd([val.moment(0).rational_reconstruction() for val in Phi0.values()])
# Phi = 1/scale_factor * Phi0
# set_verbose(0)
# save(Phi,'ModSym_15a1_5_80.sobj')

Phi = load('ModSym_15a1_5_80.sobj')

print fields_up_to(p,M,200)

data_collect = {}

for disc,_,_ in fields_up_to(p,M,200):
    if data_collect.has_key(disc):
        continue
    val = stark_heegner_points(Phi,E,disc,QQp)
    data_collect[disc] = (val[1],val[2])
    print 'Done with discriminant %s !!'%disc
    save(data_collect,'data_15a1_5.sobj')

############
##########
E = EllipticCurve('21a1')
N=E.conductor()
p=3
assert E.ap(p) == 1
M=ZZ(N/p)
#print 'aq =', E.ap(M)
prec = 80
QQp = Qp(p,prec)

# set_verbose(1)
# Phi0 = ps_modsym_from_elliptic_curve(E).plus_part().lift(p,M = prec,algorithm = 'stevens',eigensymbol = True)
# scale_factor =  gcd([val.moment(0).rational_reconstruction() for val in Phi0.values()])
# Phi = 1/scale_factor * Phi0
# set_verbose(0)
# save(Phi,'ModSym_21a1_3_80.sobj')

Phi = load('ModSym_21a1_3_80.sobj')

print fields_up_to(p,M,200)

data_collect = {}

for disc,_,_ in fields_up_to(p,M,200):
    if data_collect.has_key(disc):
        continue
    val = stark_heegner_points(Phi,E,disc,QQp)
    data_collect[disc] = (val[1],val[2])
    print 'Done with discriminant %s !!'%disc
    save(data_collect,'data_21a1_3.sobj')
