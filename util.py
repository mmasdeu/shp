from sage.modular.pollack_stevens.fund_domain import M2Z

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
