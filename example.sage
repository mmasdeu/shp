##########################
## A commented example
##########################

E = EllipticCurve('35a1') # Create the elliptic curve
p = 7 # Prime dividing the conductor
prec = 100
disc = 41

### No need to modify below

crlabel = E.cremona_label() # Cremona label for the curve
N=E.conductor()
M=ZZ(N/p)
QQp = Qp(p,prec)

# Make sure that there is some Atkin-Lehner with eigenvalue 1
V = [q for q,s in M.factor() if s == 1 and q != 2]
assert len(V) > 1 or any([E.ap(q) == -1 for q in V])

fname = 'ModSym_%s_%s_%s.sobj'%(crlabel,p,prec) # Name of the file containing the moments

# If the moments are pre-calculated, will load them. Otherwise, calculate and
# save them to disk.
if not os.path.isfile(fname):
    print 'Computing the moments...'
    phi0 = ps_modsym_from_elliptic_curve(E).plus_part()
    phi0 = gcd([val.moments[0] for val in phi0.values()]) * phi0
    verb_level = get_verbose()
    set_verbose(1)
    Phi = phi0.lift(p,M = prec,algorithm = 'stevens',eigensymbol = True)
    set_verbose(verb_level)
    save(Phi,fname)
else:
    Phi = load(fname)

# Find the points
P,Jlist, emblist = stark_heegner_points(Phi,E,disc,QQp,working_prec = 2*prec)

# The variable P contains the point on the elliptic curve, if it could be found.
print 'The point has order: %s'%P.order()
