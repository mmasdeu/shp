from sage.modular.pollack_stevens.fund_domain import M2Z
from itertools import starmap,izip,product,chain
from operator import mul,itemgetter
from sage.modular.pollack_stevens.space import ps_modsym_from_elliptic_curve
from functools import wraps
import os.path
import gc,errno,signal,os,types

########################################################################################
# First some auxiliary functions
########################################################################################
def fields_up_to(p,M,bound):
    good = []
    for disc in range(2,bound):
        if fundamental_discriminant(disc) != disc:
            continue
        D = ZZ(disc/4) if disc%4 == 0 else ZZ(disc)
        assert D.is_squarefree()
        if kronecker_symbol(disc,p) == -1:
            if all([kronecker_symbol(disc,ff[0]) == 1 for ff in ZZ(M).factor()]):
                if True:# QuadraticField(D,names='r').narrow_class_group().order() == 1:
                    good.append((disc,QuadraticField(D,names='r').class_group().order(),QuadraticField(D,names='r').narrow_class_group().order()))
    return good

def find_containing_affinoid(p,z,level = 1):
    r"""
    Returns the vertex corresponding to the affinoid in 
    the `p`-adic upper half plane that a given (unramified!) point reduces to.

    INPUT:

      - ``z`` - an element of an unramified extension of `\QQ_p` that is not contained
        in `\QQ_p`.

    OUTPUT:

      A 2x2 integer matrix representing the affinoid.

        sage: K.<a> = Qq(5^2,20)
        sage: find_containing_affinoid(5,a)
        [1 0]
        [0 1]
        sage: z = 5*a+3
        sage: v = find_containing_affinoid(5,z).inverse(); v
        [ 1/5 -3/5]
        [   0    1]

    Note that the translate of ``z`` belongs to the standard affinoid. That is,
    it is a `p`-adic unit and its reduction modulo `p` is not in `\FF_p`::

        sage: a,b,c,d = v.list()
        sage: gz = (a*z+b)/(c*z+d); gz
        a + O(5^19)
        sage: gz.valuation() == 0
        True
    """
    #Assume z belongs to some extension of QQp.
    if(z.valuation(p)<0):
        return M2Z([0,1,p*level,0])*find_containing_affinoid(p,1/(p*z))
    a=0
    pn=1
    val=z.valuation(p)
    L=[0]*val+z.unit_part().list()
    for n in range(len(L)):
        if L[n] != 0:
            if len(L[n]) > 1:
                break
            if len(L[n]) > 0:
                a += pn*L[n][0]
        pn*=p
    return M2Z([pn,a,0,1])

def find_center(p,level,t1,t2):
    r"""
    This function computes the center between two points in Cp
    """
    old_dir = M2Z([1,0,0,1])
    E0inf = [M2Z([0,-1,level,0])]
    E0Zp = [M2Z([p,a,0,1]) for a in range(p)]
    while True:
        new_dirs = [old_dir * e0 for e0 in E0Zp]
        same_ball = False
        new_dir = None
        for g in new_dirs:
            a,b,c,d = (g**(-1)).list()
            # Check whether t1 and t2 are in the open given by g
            if all([(a*t + b).valuation() >= (c*t + d).valuation() for t in [t1,t2]]):
                new_dir = g
                break
        if new_dir is None:
            return old_dir
        else:
            old_dir = new_dir

def is_in_Gamma_1(mat,N,p):
    if N != 1:
        a,b,c,d=mat.list()
        if not all([QQ(x).is_S_integral([p]) for x in [a,b,c,d]]):
            return False
        if Zmod(N)(a) != 1 or Zmod(N)(c) % N != 0:
            return False
    if mat.det() != 1:
        return False
    return True


#########################################################################################################################
# now the new functions that we need...they follow pretty close the article we're writting
#########################################################################################################################
def factorize_matrix(m,M):
    a,b,c,d = m.list()
    if QQ(a).denominator() != 1:
        return [m]
    aabs = ZZ(a).abs()
    Zm = Zmod(M)
    for alpha0 in xrange(1,aabs,M):
        for alpha in [alpha0,-alpha0]:
            delta0 = (Zm(alpha)**(-1)).lift()
            for delta in xrange(delta0-10*M,delta0+10*M,M):
                if alpha*delta == 1:
                    continue
                gamma0 = ZZ( (alpha*delta -1) / M)
                c1vec = divisors(gamma0)
                for c1 in c1vec:
                    ulentry = (a*delta-b*c1*M).abs()
                    if ulentry < aabs:
                        gamma = c1*M
                        beta = ZZ(gamma0/c1)
                        r1 = Matrix(QQ,2,2,[alpha,beta,gamma,delta])
                        r2 = m*r1.adjoint()
                        assert r1.determinant() == 1
                        V1 = factorize_matrix(r1,M)
                        V2 = factorize_matrix(r2,M)
                        return V2 + V1
    return [m]

#given a matrix M=[a,b,c,d] we run over all lambda in O until we find some satisfying that the class of c mod a+lambda*c is represented by a unit; observe that we are not requiring that a+lambda*c is a prime, nor that the units generate all the quotient ring: if the class of c (mod a+lambda*c) can be represented by a unit, that's fine
#Rmk: maybe here's room for improvement: the loop is pretty pedestrian, and moreover it's not clear at all that we're running over the best lambda'a possible...but apparently it works so far...
#adapted
def find_lambda(M,p,n_results = 1):
    a,b,c,d=M.list()
    if c == 0:
        return [(0,a)]
    valc = c.valuation(p)
    vala = a.valuation(p)
    ap = ZZ(p**(-vala)*a)
    cp = ZZ(p**(-valc)*c)

    lmbd0 = ZZ(QQ(-ap/cp).round())
    lambda_set = sorted([(ZZ(lmbd0 + delta),ZZ(ap+(lmbd0 + delta)*cp)) for delta in range(-20,+20)],key = lambda x:x[1].abs())
    res = []
    for lmd,aplc in lambda_set:
        res.extend([(lmd*p**(vala-valc),unit*p**(valc)) for unit in is_represented_by_unit(aplc,cp,p)])
        if len(res) >= n_results:
            return res[:n_results]
    if len(res) == 0:
        verbose('Lambda not found')
        raise RuntimeError,'Lambda not found'
    return res[:n_results]

#we want to know if the class of c mod a is represented by a unit in F
#returns the unit representing c mod a if it is, and returns False otherwise
#adapted
def is_represented_by_unit(a,c,p):
    #we can forget about powers of p, because they are units; then we can work with integers
    vala = 0
    valc = 0
    while a % p == 0:
        vala += 1
        a = ZZ(a/p)
    while c % p == 0:
        valc += 1
        c = ZZ(c/p)
    aa = a.abs()
    # verbose('is_rep_by_unit aa=%s, cc=%s'%(aa,cc_mod_aa))
    G = Zmod(aa)
    cc = G(c)
    Gp = G(p)
    res = []
    sizeG = G.unit_group_order()
    expn = G.unit_group_exponent()
    # verbose('Group of order=%s'%sizeG)
    try:
        n0 = discrete_log(cc,Gp,sizeG,operation = '*')
        n0 = n0 % expn
        if n0 > expn/2:
            n0 -= expn
        res.append( p**ZZ(n0 + valc) )
    except (ValueError,RuntimeError): pass
    try:
        n0 = discrete_log(cc,-Gp,sizeG,operation = '*')
        n0 = n0 % expn
        if n0 > expn/2:
            n0 -= expn
        res.append( (-1)**n0 * p**ZZ(n0 + valc) )
    except (ValueError,RuntimeError): pass
    return res

def num_evals(tau1,tau2):
    p = tau1.parent().prime()
    dr1 = find_containing_affinoid(p,tau1).determinant().valuation(p)
    dr2 = find_containing_affinoid(p,tau2).determinant().valuation(p)
    delta = find_center(p,1,tau1,tau2).determinant().valuation(p)
    distance = dr1+dr2-2*delta
    return p + 1  + (p-1) * distance

def compute_tau0(v0,W_M,return_exact = False):
    R.<X>=PolynomialRing(QQ)
    F = v0.domain()
    Cp = v0.codomain()
    w = F.maximal_order().ring_generators()[0]

    assert w.minpoly() == W_M.minpoly()
    W_M0 = W_M.apply_map(v0)
    a,b,c,d = W_M.list()
    tau0_vec = (c*X^2+(d-a)*X-b).roots(F)
    tau0 = v0(tau0_vec[0][0])
    idx = 0
    if W_M0[1,0]*tau0 + W_M0[1,1] != v0(w):
        tau0=v0(tau0_vec[1][0])
        idx = 1
    assert W_M0*Matrix(Cp,2,1,[tau0,1]) == v0(w)*Matrix(Cp,2,1,[tau0,1])
    if return_exact == True:
        return tau0_vec[idx][0]
    else:
        return tau0

def find_tau0_and_gtau(v0,M,W,orientation = None,algorithm = 'guitart_masdeu'):
    F = v0.domain()
    r = F.gen()
    Cp = v0.codomain()
    QQp = Cp.base_ring()
    p = QQp.prime()
    if F.degree() != 2 or len(F.ideal(p).factor()) > 1 or gcd(p,F.disc()) !=1:
        raise ValueError,'Not a valid field'
    w=F.maximal_order().ring_generators()[0]
    #we have to square the unit, so that the determinant is 1
    u=F.units()[0]#**2 # It looks like the square can be removed!
    if F.real_embeddings()[0](u) < 0:
        u = -u
    if F.real_embeddings()[0](u) < 1:
        u = 1/u
    assert F.real_embeddings()[0](u) > 1
    u0vec = w.coordinates_in_terms_of_powers()(u)
    u0vec_inv = w.coordinates_in_terms_of_powers()(u^(-1))
    assert w.minpoly() == W.minpoly()
    if algorithm == 'darmon_pollack':
          if M != 1:
              raise ValueError,'the level (=%s) must be =1'%M
          gtau = u0vec[0]+u0vec[1]*W
          a,b,c,d = W.list()
          tau0 = compute_tau0(v0,W)
          return tau0,gtau,1,find_limits(tau0,gtau,1)

    elif algorithm == 'guitart_masdeu':
        emblist = []
        #we seek for an optimal embedding of conductor M
        Mover2 = 2*ZZ(QQ(M/2).ceil())
        for B in [M2Z([1,0,0,1])] +  [M2Z([1,i,0,M]) for i in range(-Mover2,Mover2+1)] + [M2Z([M,0,0,1])]:
            W_M=B*W*B^-1
            if all([x.is_integral() == 1 for x in W_M.list()]) and ZZ(W_M[1,0])%M == 0:
                if orientation is not None:
                    for ell,r in ZZ(M).factor():
                        if W_M[0,0] % ell != orientation % ell:
                            Wl = Matrix(ZZ,2,2,[0,-1,ell,0])
                            W_M = Wl**(-1)*W_M*Wl
                    assert all([W_M[0,0] % ell == orientation % ell for ell,r in ZZ(M).factor()])

                #computation of tau_0: it's one of the roots of the minimal polynomial of W.
                tau0 = compute_tau0(v0,W_M,return_exact = True)
                if F.class_number() > 1 and find_containing_affinoid(p,v0(tau0)).determinant().valuation(p) % 2 == 1:
                    Wp = Matrix(ZZ,2,2,[0,-1,p,0])
                    W_M = Wp**(-1)*W_M*Wp
                    assert all([W_M[0,0] % ell == orientation % ell for ell,r in ZZ(M).factor()])
                    tau0 = compute_tau0(v0, W_M,return_exact = True)
                    assert find_containing_affinoid(p,v0(tau0)).determinant().valuation(p) % 2 == 0

                gtau_orig_1 = u0vec[0]+u0vec[1]*W_M
                gtau_orig_2 = u0vec_inv[0]+u0vec_inv[1]*W_M
                emblist.extend([(tau0,gtau_orig_1),(tau0,gtau_orig_2)])

        if len(emblist) == 0:
            raise RuntimeError,'No embeddings found !'
        verbose("Found %s initial embeddings."%len(emblist))

        list_embeddings = []
        for tau0,gtau_orig in emblist[:2]:
            while len(list_embeddings) == 0:
                gtau = gtau_orig
                verbose('gtau[0,0] = %s'%gtau[0,0])
                ## First try
                for u1 in is_represented_by_unit(M,ZZ(gtau[0,0]),p):
                    u_M1 = matrix(QQ,2,2,[u1^-1,0,0,u1])
                    gtau1 = u_M1 * gtau
                    tau01 = tau0 / (u1**2) #act_flt(u_M1,tau0)
                    list_embeddings.append((tau01,gtau1,1))

                # #Second try
                if M > 1:
                    a_inv = ZZ((1/Zmod(M)(gtau[0,0])).lift())
                    for u2 in is_represented_by_unit(M,a_inv,p):
                        u_M2 = matrix(QQ,2,2,[u2,0,0,u2^-1])
                        gtau2 = u_M2 * gtau
                        tau02 = u2**2 * tau0 #act_flt(u_M2,tau0)
                        list_embeddings.append((tau02,gtau2,1))

        ## Third try
        new_embs = []
        for tau,gtau,sign in list_embeddings:
            gtauinv = gtau**(-1)
            a,b,c,d = gtauinv.list()
            newtau = (a*tau+b) / (c*tau+d) #act_flt(gtau^(-1),tau)
            new_embs.append((newtau,gtauinv,-sign))
        list_embeddings.extend(new_embs)
        verbose('Found %s embeddings...'%len(list_embeddings))

        # Now choose the best
        opt_evals = None
        opt_tau = None
        num_emb = 0
        for tau,gtau,sign in list_embeddings:
            verbose('Analyzing embedding %s...'%num_emb)
            num_emb += 1
            try:
                V = find_limits(tau,gtau,M,v0)
            except KeyboardInterrupt:
                continue
            if V is None:
                continue
            n_evals = sum([num_evals(t1,t2) for t1,t2 in V])
            verbose('opt_evals = %s'%opt_evals)
            if opt_evals is None or n_evals < opt_evals:
                opt_evals = n_evals
                opt_tau = tau
                opt_gtau = gtau
                opt_sign = sign
                opt_V = V
        if opt_tau is None:
            raise RuntimeError,'No embedding found'
        verbose('The optimal number of evaluations found is %s'%opt_evals)
        return opt_tau,opt_gtau,opt_sign,opt_V
    else:
        raise ValueError, 'Algorithm must be either "guitart_masdeu" or "darmon_pollack"'

def find_optimal_embeddings(F,use_magma = False):
    w=F.maximal_order().ring_generators()[0]
    D = F.discriminant()
    fact = F(1) if D > 0 else w - 1/2 * w.trace()
    ## this matrix gives an optimal embedding of conductor 1
    if F.class_number() == 1:
        return [Matrix(QQ,2,2,[w.trace(),-w.norm(),1,0])]
    elif use_magma == True:
        tmp = magma.function_call('ReducedForms',args =[D],nvals=1)
        G = [[tmp[i+1][j]._sage_() for j in [1,2,3]] for i in range(len(tmp))]
    else:
        G = []
        for I in [F.ideal(cl.gens()) for cl in F.class_group()]:
            alpha,beta = I.integral_basis()
            if QQ((alpha*beta.conjugate() - beta*alpha.conjugate())/fact) < 0:
                alpha,beta = beta,alpha
            nrm = I.norm()
            a = ZZ(alpha.norm()/nrm)
            c = ZZ(beta.norm()/nrm)
            b = ZZ((alpha+beta).norm()/nrm) - a - c
            G.append((a,b,c))
    delta = F.gen() if D%4 == 1 else 2*F.gen()
    r,s = delta.coordinates_in_terms_of_powers()(w)
    return [M2Z([r+s*B,-2*s*C,2*s*A,r-s*B]) for A,B,C in G]

def getcoords(E,u,prec=20,R = None):
    if R is None:
        R = u.parent()
        u = R(u)
    p = R.prime()
    jE = E.j_invariant()

    # Calculate the Tate parameter
    E4 = EisensteinForms(weight=4).basis()[0]
    Delta = CuspForms(weight=12).basis()[0]
    j = (E4.q_expansion(prec+7))**3/Delta.q_expansion(prec+7)
    qE =  (1/j).power_series().reversion()(R(1/jE))

    # Normalize the period by appropriate powers of qE
    un = u * qE**(-(u.valuation()/qE.valuation()).floor())

    precn = (prec/qE.valuation()).floor() + 4
    # formulas in Silverman II (Advanced Topics in the Arithmetic of Elliptic curves, p. 425)
    xx = un/(1-un)**2 + sum( [qE**n*un/(1-qE**n*un)**2 + qE**n/un/(1-qE**n/un)**2-2*qE**n/(1-qE**n)**2 for n in range(1,precn) ])
    yy = un**2/(1-un)**3 + sum( [qE**(2*n)*un**2/(1-qE**n*un)**3 - qE**n/un/(1-qE**n/un)**3+qE**n/(1-qE**n)**2 for n in range(1,precn) ])


    sk = lambda q,k,pprec: sum( [n**k*q**n/(1-q**n) for n in range(1,pprec+1)] )
    n = qE.valuation()
    precp = ((prec+4)/n).floor() + 2;

    tate_a4 = -5  * sk(qE,3,precp)
    tate_a6 = (tate_a4 - 7 * sk(qE,5,precp) )/12
    Eq = EllipticCurve([R(1),R(0),R(0),tate_a4,tate_a6])

    C2 = (Eq.c4() * E.c6()) / (Eq.c6() * E.c4())

    C = R(C2).square_root()
    s = (C - R(E.a1()))/R(2)
    r = (s*(C-s) - R(E.a2())) / 3
    t =  (r*(2*s-C)-R(E.a3())) / 2

    return  ( r + C2 * xx, t + s * C2 * xx + C * C2 * yy )

def period_from_coords(p,E, P, prec = 20):
    r"""
    Given a point `P` in the formal group of the elliptic curve `E` with split multiplicative reduction,
    this produces an element `u` in `\QQ_p^{\times}` mapped to the point `P` by the Tate parametrisation.
    The algorithm return the unique such element in `1+p\ZZ_p`.

    INPUT:

    - ``P`` - a point on the elliptic curve.

    - ``prec`` - the `p`-adic precision, default is 20.

    """
    R = Qp(p,prec)
    if P[0].valuation(p) >= 0:
        raise  ValueError , "The point must lie in the formal group."
    Etate = E.tate_curve(p)
    Eq = Etate.curve(prec = prec)
    isom = Etate._isomorphism(prec=prec)
    C = isom[0]
    r = isom[1]
    s = isom[2]
    t = isom[3]
    xx = r + C**2 * P[0]
    yy = t + s * C**2 * P[0] + C**3 * P[1]
    try:
        EqCp = Eq.change_ring(yy.parent())
        Pq = EqCp([xx,yy])
    except:
        raise RuntimeError, "Bug : Point %s does not lie on the curve "%[xx,yy]

    tt = -xx/yy
    eqhat = Eq.formal()
    eqlog = eqhat.log(prec + 3)
    z = eqlog(tt)
    u = ZZ(1)
    fac = ZZ(1)
    for i in range(1,2*prec+1):
        fac = fac * i
        u = u + z**i/fac
    q = Etate.parameter(prec = prec)
    un = u * q**(-(u.valuation()/q.valuation()).floor())
    return un

def recognize_point(x,y,EF,prec = None):
  F = EF.base_ring()
  Cp = x.parent()
  s = F.gen()
  w = F.maximal_order().ring_generators()[0]
  assert w.minpoly()(Cp.gen()) == 0
  QQp = Cp.base_ring()
  p = Cp.prime()
  if prec is None:
      prec = QQp.precision_cap()
  if x == 0 and y == 0:
      candidate = [0,0,1]
  elif (1/x).valuation() > prec and (1/y).valuation() > prec:
      candidate = [0,1,0]
  else:
      x1 = p**(x.valuation())*QQp(ZZ(x._ntl_rep()[0])) + O(p^prec)
      x2 = p**(x.valuation())*QQp(ZZ(x._ntl_rep()[1])) + O(p^prec)
      y1 = p**(y.valuation())*QQp(ZZ(y._ntl_rep()[0])) + O(p^prec)
      y2 = p**(y.valuation())*QQp(ZZ(y._ntl_rep()[1])) + O(p^prec)
      try:
          x1 = algdep(x1,1).roots(QQ)[0][0]
          x2 = algdep(x2,1).roots(QQ)[0][0]
          y1 = algdep(y1,1).roots(QQ)[0][0]
          y2 = algdep(y2,1).roots(QQ)[0][0]
          candidate =  [ x1+x2*w, y1+y2*w, 1]
      except:
          print 'Something couldnt be recognized...'
          try:
              return EF.lift_x(x),True
          except:
              return [x,y,1],False
  try:
      Pt = EF(candidate)
      print 'Point is in curve:',Pt
      return candidate,True
  except TypeError:
      print 'Point does not appear to lie on curve...'
      return candidate,False

def find_limits(tau,gtau = None,level = 1,v0 = None,method = 2):
    if gtau is None: return []
    if gtau.determinant() == 0:
        raise ValueError,'gtau must have nonzero determinant.'

    if level == 1: # Use Manin trick
        if gtau[0,0] == 0:
            return [(1-1/tau,tau-1)]
        else:
           a,c,b,d = gtau.list()
           if b < 0: a,b,c,d = -a,-b,-c,-d
           if b == 0: return []
           if b == 1:
               return find_limits(tau-a/b,M2Z([0,-1,1,0]), level = 1)
           else:
             d = (1/(Zmod(b)(a))).lift()
             if 2*d > b : d -= b
             c = ZZ((a*d-1)/b)
             a,b,c,d = a,b,c,d if d >= 0 else -a,-b,-c,-d
             return find_limits((b*tau-a)/(d*tau-c),M2Z([0,-1,1,0]),level = 1) + find_limits(tau,M2Z([-c,a,-d,b]),level = 1)
    else:
        if tau.parent().is_exact():
            p = v0.codomain().prime()
        else:
            p = tau.parent().prime()
        if method == 1:
            factorization = factorize_matrix(gtau,level)
            W = []
            verbose('Factored original gtau into %s matrices!'%len(factorization))
            for vv in factorization:
                verbose('findinig lambda for matrix %s'%vv)
                lmb,uu = find_lambda(vv,p,n_results = 1)[0]
                verbose('done')
                W.extend(decompose(vv,lmb,uu))
            assert prod(W) == gtau
            V, n_evals = get_limits_from_decomp(tau,W,v0)
            verbose('n_evals = %s'%n_evals)
            return V
        elif method == 2:
            opt_evals = None
            opt_V = None
            for lmb,uu in find_lambda(gtau,p,n_results = 1):
                #verbose('trying lambda = %s, u = (-)p^%s'%(lmb,uu.valuation(p)))
                dec = decompose(gtau,lmb,uu)
                V,n_evals = get_limits_from_decomp(tau,dec,v0)
                # verbose('n_evals = %s'%n_evals)
                if opt_evals is None or n_evals < opt_evals:
                    opt_V = V
                    opt_evals = n_evals
            return opt_V

def decompose(gtau,lmb,uu):
    if uu == 0:
        return [gtau]

    E_lambda = Matrix(QQ,2,2,[1,lmb,0,1])
    #we know that E_lambda*gtau is a matrix [a,b,c,d] such that c=uu+ta for some unit uu; now we find uu and t
    MM=(E_lambda*gtau).change_ring(QQ)

    a,b,c,d=MM.list()
    t = QQ(c-uu)/QQ(a)
    assert QQ(t).is_S_integral([p])

    E1i=Matrix(QQ,2,2,[1,0,uu*(1-a),1])
    E2i=Matrix(QQ,2,2,[1,-1/uu,0,1])
    E34i=Matrix(QQ,2,2,[1,0,c+t*(1-a),1])
    E_x=(E34i*E2i*E1i)^(-1)*MM
    return [E_lambda^(-1), E34i,E2i,E1i,E_x]

def get_limits_from_decomp(tau,dec,v0):
    oldTau = tau
    V = []
    n_evals = 0
    for E in dec:
        a,b,c,d = (E**(-1)).list()
        # print a.valuation(p),b.valuation(p),c.valuation(p),d.valuation(p)
        # assert a == 1 and d == 1
        assert oldTau.parent().is_exact()
        newTau = (a*oldTau+b)/(c*oldTau+d) #act_flt(E.inverse(),oldTau)
        if c != 0: # lower-triangular
            if tau.parent().is_exact():
                t1 = v0(oldTau)
                t2 = v0(newTau)
            else:
                t1 = oldTau
                t2 = oldTau
            V.append([t1,t2])
            n_evals += num_evals(t1,t2)
        oldTau = newTau
    return V,n_evals

##----------------------------------------------------------------------------
## stark_heegner_points(E,D,Qp)
##
## Input: 
##    E: An elliptic curve over Q
##       of prime conductor p. 
##    D: A  positive discriminant, for which 
##       p is inert in the associated REAL quadratic field.
##    Qp: The p-adic field over which the calculations are to be done.
##
##  Output: 
##    A list of the h corresponding Stark-Heegner points as p-adic points.
##    The trace of the Stark-heegner points, as a global point.
##    The polynomial h_D(x) of degree h satisfied by the Stark-Heegner points.
##
##----------------------------------------------------------------------------
def stark_heegner_points(Phi,E,D,QQp,algorithm = 'guitart_masdeu', idx_orientation = 0,working_prec = None):
  p = QQp.prime()
  print "Computing the Stark-Heegner points of discriminant ", D, " over the elliptic curve:"
  print E
  print "The calculation is being done with p = ", p
  if D % 4 == 0:
      D = ZZ(D/4)
  F.<r>  = QuadraticField(D)
  prec = QQp.precision_cap()
  if working_prec is None:
      working_prec = prec + 2
  # Compute the completion of F at p
  w = F.maximal_order().ring_generators()[0]
  r0,r1 = w.coordinates_in_terms_of_powers()(F.gen())
  Cp = Qp(p,working_prec).extension(w.minpoly(),names = 'g')
  v0 = F.hom([r0+r1*Cp.gen()])
  EoverCp = E.change_ring(Cp)
  level = ZZ(Phi._map._manin.level()/p)
  print "Computing optimal embeddings of level one..."
  Wlist = find_optimal_embeddings(F)
  assert len(Wlist) == F.class_number()
  print "Found %s such embeddings (= h_F)."%len(Wlist)
  J = Cp(1)
  i = 0
  # Find the orientations
  orients = F.maximal_order().ring_generators()[0].minpoly().roots(Zmod(M),multiplicities = False)
  print "Possible orientations: %s"%orients
  if len(Wlist) == 1 or idx_orientation == -1:
      print "Using all orientations, since h_F = 1"
      chosen_orientation = None
  else:
      print "Using orientation = %s"%orients[idx_orientation]
      chosen_orientation = orients[idx_orientation]
  Jlist = []
  emblist = []
  for W in Wlist:
      i += 1
      print i, " Computing period attached to the embedding: %s"%W.list()
      print "Looking for an embedding of the right level"
      tau, gtau,sign,limits = find_tau0_and_gtau(v0,level,W,algorithm = algorithm,orientation = chosen_orientation)
      emblist.append((tau,gtau,sign,limits))
      print "Embedding found, now computing the period..."
      newJ = indef_integral(Phi,tau,gtau,limits = limits)**sign
      Jlist.append(newJ)
      J *= newJ
  #return J
  if J == Cp(1):
      candidate = E(0)
  else:
      x,y = getcoords(E,J,prec)
      success = False
      while success == False and prec > 1:
          print "Trying to recognize point with precision %s"%prec
          candidate,success = recognize_point(x,y,E.change_ring(F),prec = prec)
          prec -= 1
      if success == False:
          print "Could not recognize point"
  # verbose('Point is in curve: %s'%candidate)
  try:
      return E.change_ring(F)(candidate),Jlist,emblist
  except (TypeError,ValueError):
      return candidate,Jlist,emblist


def double_integral_zero_infty(Phi,tau1,tau2):
    p = Phi.parent().prime()
    K = tau1.parent()
    R = PolynomialRing(K,'x')
    x = R.gen()
    R1 = LaurentSeriesRing(K,'r1')
    r1 = R1.gen()
    R1.set_default_prec(Phi.precision_absolute())

    level = Phi._map._manin.level()
    E0inf = [M2Z([0,-1,level,0])]
    E0Zp = [M2Z([p,a,0,1]) for a in range(p)]

    predicted_evals = num_evals(tau1,tau2)

    a,b,c,d = find_center(p,level,tau1,tau2)
    h = M2Z([a,b,c,d])
    E = [h*e0 for e0 in E0Zp + E0inf]

    resadd = 0
    resmul = 1
    total_evals = 0
    percentage = QQ(0)
    ii = 0
    f = (x-tau2)/(x-tau1)
    while len(E) > 0:
        ii += 1
        increment = QQ((100-percentage)/len(E))
        verbose('remaining %s percent (and done %s of %s evaluations)'%(RealField(10)(100-percentage),total_evals,predicted_evals))
        newE = []
        for e in E:
            a,b,c,d = e.list()
            assert ZZ(c) % level == 0
            try:
                y0 = f((a*r1+b)/(c*r1+d))
                val = y0(0)
                if all([xx.valuation(p)>0 for xx in (y0/val - 1).list()]):
                    if total_evals % 100 == 0:
                        Phi._map._codomain.clear_cache()
                    pol = val.log(branch = 0)+((y0.derivative()/y0).integral())
                    V = [0]*pol.valuation() + pol.shift(-pol.valuation()).list()

                    mu_e = Phi._map(M2Z([b,d,a,c])).moments
                    mu_e0 = ZZ(mu_e[0].rational_reconstruction())
                    mu_e = [mu_e0] + map(lambda xx:xx.lift(),mu_e[1:])
                    resadd += sum(starmap(mul,izip(V,mu_e)))
                    resmul *= val**mu_e0
                    percentage += increment
                    total_evals += 1
                else:
                    newE.extend([e*e0 for e0 in E0Zp])
            except ZeroDivisionError:
                #raise RuntimeError,'Probably not enough working precision...'
                newE.extend([e*e0 for e0 in E0Zp])
        E = newE
    verbose('total evaluations = %s'%total_evals)
    val = resmul.valuation()
    return p**val*K.teichmuller(p**(-val)*resmul)*resadd.exp()

##----------------------------------------------------------------------------
##  double_integral(tau1,tau2,r,s)
##  
## Input:  
##    tau1,tau2: Elements of the ``standard affinoid" in H_p consisting 
##               of elements in PP_1(C_p) whose natural image in 
##               P_1(F_p-bar) does not belong to P_1(F_p). 
##    r,s:       Elements of P_1(Q). The cusp r=a/b is
##               represented in the form r=[a,b], with a and b relatively
##               prime integers, and b>=0. By convention infty=[1,0].
##    omega:     The modular form on Gamma_0(p), represented as above.
##
## Output:
##    The ``multiplicative double integral" defined in [Da]. 
##----------------------------------------------------------
def double_integral(Phi,tau1,tau2,r,s):
   if r == [0,0] or s == [0,0]:
       raise ValueError,'r and s must be valid projective coordinates.'
   if r[0] == 0 and s[1] == 0: # From 0 to infinity
       return double_integral_zero_infty(Phi,tau1,tau2)
   elif s[1] == 0:
       a,b = r
       if b < 0: a,b = -a,-b
       if b == 0: return 0
       if b == 1:
         return double_integral(Phi,tau1-a/b,tau2-a/b,[0,1],[1,0])
       else:
         d = (1/(Zmod(b)(a))).lift()
         if 2*d > b : d -= b
         c = ZZ((a*d-1)/b)

         rr = [c,d] if d >= 0 else [-c,-d]
         i1 = double_integral(Phi,(b*tau1-a)/(d*tau1-c),(b*tau2-a)/(d*tau2-c),[0,1],[1,0])
         i2 = double_integral(Phi,tau1,tau2,rr,[1,0])
         return i1*i2
   else:
      i1= double_integral(Phi,tau1,tau2,r,[1,0])
      i2 = double_integral(Phi,tau1,tau2,s,[1,0])
      return i1/i2


##----------------------------------------------------------------------------
##  indef_integral(tau,r,s)
##  
## Input:  
##    tau:       Elements of the ``standard affinoid" in H_p consisting 
##               of elements in PP_1(C_p) whose natural image in 
##               P_1(F_p-bar) does not belong to P_1(F_p). 
##    r,s:       Elements of P_1(Q). The cusp r=a/b is
##               represented in the form r=[a,b], with a and b relatively
##               prime integers, and b>=0. By convention infty=[1,0].
##    omega:     The modular form on Gamma_0(p), represented as above.
##
## Output:
##    The indefinite ``multiplicative double integral" defined in [Da]. 
##----------------------------------------------------------
def indef_integral(Phi,tau,r,s  = None,limits = None):
    p = Phi._map._codomain().parent().base_ring().prime()
    level = ZZ(Phi._map._manin.level()/p)
    I = 1
    if limits is None:
        Vr = find_limits(tau,r,level)
        Vs = find_limits(tau,s,level)
    else:
        assert s is None
        Vr = limits
        Vs = []
    n_evals = sum([num_evals(t1,t2) for t1,t2 in Vr+Vs])
    verbose('Will perform a total of %s evaluations...'%n_evals)

    for t1,t2 in Vr:
        I *= double_integral(Phi,t1,t2,[0,1],[1,0])
    for t1,t2 in Vs:
        I /= double_integral(Phi,t1,t2,[0,1],[1,0])
    return I
