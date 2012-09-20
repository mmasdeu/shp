########################
# Finding candidate curves
########################
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

###############################
## Generic code to collect data
###############################
crlabel = '35a1'
p= 7
prec = 100
discbound = 200
save_data = False

#### Do not edit below ########

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
else:
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
