jobs = []

data = load('curve_data/cleandata_33_11.sobj')
outfile = 'curve33.tex'
E = EllipticCurve('33a1')
p = 11
prec = 80
jobs.append((data,outfile,E,p,prec))

data = load('curve_data/cleandata_51_3.sobj')
outfile = 'curve51.tex'
E = EllipticCurve('51a1')
p = 3
prec = 200
jobs.append((data,outfile,E,p,prec))


data = load('curve_data/cleandata_21_3.sobj')
outfile = 'curve21.tex'
E = EllipticCurve('21a1')
p = 3
prec = 80
jobs.append((data,outfile,E,p,prec))

data = load('curve_data/data_35a1_7.sobj')
outfile = 'curve35.tex'
E = EllipticCurve('35a1')
p = 7
prec = 80
jobs.append((data,outfile,E,p,prec))

data = load('curve_data/cleandata_15_5.sobj')
outfile = 'curve15.tex'
E = EllipticCurve('15a1')
p = 5
prec = 80
jobs.append((data,outfile,E,p,prec))


# data = load('data_42a1_7.sobj')
# outfile = 'curve42.tex'
# E = EllipticCurve('42a1')
# p = 7
# prec = 40
# jobs.append((data,outfile,E,p,prec))

data = load('data_105a1_3.sobj')
outfile = 'curve105.tex'
E = EllipticCurve('105a1')
p = 3
prec = 100
jobs.append((data,outfile,E,p,prec))


for data,outfile, E, p, prec in jobs:
    #########################################
    M = ZZ(E.conductor()/p)
    lines = []
    lines2 = []
    all_lines = []
    all_lines.append('\\begin{tabular}{c|c|c}')
    all_lines.append('$D$ & $h$ & $P^+$\\\\\\hline\\hline')
    print 'E = %s'%E
    print 'p = %s'%p
    for disc,h,hp in fields_up_to(p,M,200):
        print '...'
        if not data.has_key(disc):
            newline = "$%s$ & $%s$ & --- \\\\"%(disc,h)
            if h == 1:
                lines.append(newline)
            else:
                lines2.append(newline)
            continue
        P = None
        Plist = []
        Jlist,emblist = data[disc]
        if disc % 4 == 0:
            D = ZZ(disc/4)
        else:
            D = disc
        F = QuadraticField(D,names = 'sqrt'+str(D))
        assert F.class_number() == h
        assert len(Jlist) == h

        # We first try the point defined over F
        J = prod(Jlist)
        xx,yy = getcoords(E,J,prec = prec -2)
        if F.gen().minpoly()(xx.parent().gen()) == 0:
            s = F.gen()
        else:
            s = F.maximal_order().ring_generators()[0]
            assert s.minpoly()(xx.parent().gen()) == 0

        #assert F.gen().minpoly()(xx.parent().gen())==0

        EF = E.change_ring(F)
        x10 = algdep(Qp(p,prec)(p**(xx.valuation())*ZZ(xx._ntl_rep()[0])),1).roots(QQ)[0][0]
        x11 = algdep(Qp(p,prec)(p**(xx.valuation())*ZZ(xx._ntl_rep()[1])),1).roots(QQ)[0][0]
        x1 = x10+x11*s
        y10 = algdep(Qp(p,prec)(p**(yy.valuation())*ZZ(xx._ntl_rep()[0])),1).roots(QQ)[0][0]
        y11 = algdep(Qp(p,prec)(p**(yy.valuation())*ZZ(xx._ntl_rep()[1])),1).roots(QQ)[0][0]
        y1 = y10+y11*s
        try:
            # That would be our first hope
            P = EF([x1,y1])
        except TypeError:
            try:
                # Another way to do it, maybe we missed the y-value?
                P = EF.lift_x(x1)
            except ValueError:
                # print 'This discriminant (%s) didnt work..'%disc
                P = None
        if h > 1: # Now we will try the individual periods
            Plist = []
            for ii in range(h):
                try:
                    xx,yy = getcoords(E,Jlist[ii],prec = prec - 2)
                except NotImplementedError:
                    Plist.append(None)
                    continue
                HCF = F.hilbert_class_field(names = 'a')
                if h == 2:
                    try:
                        mylabel = 'sqrt' + str(ZZ(HCF.gen()**2))
                    except TypeError:
                        mylabel = 'a'
                    HCF = F.hilbert_class_field(names = mylabel)
                EK = E.change_ring(HCF)
                x10poly = algdep(Qp(p,prec)(p**(xx.valuation())*ZZ(xx._ntl_rep()[0])),h)
                try:
                    x10 = x10poly.roots(HCF)[0][0]
                except IndexError:
                    # print 'This discriminant (%s) doesnt work..'%disc
                    Plist.append(None)
                    continue

                rootidx = 0
                x11vec = algdep(Qp(p,prec)(p**(xx.valuation())*ZZ(xx._ntl_rep()[1])),h).roots(HCF)
                while rootidx <= len(x11vec):
                    verbose('Trying idx = %s'%rootidx)
                    x11 = x11vec[rootidx][0]
                    x1 = x10+x11*s
                    try:
                        Plist.append( EK.lift_x(x1))
                        break
                    except ValueError:
                        rootidx += 1
                if rootidx == len(x11vec):
                    # print 'This discriminant (%s) didnt work..'%disc
                    Plist.append([])

        if h == 1 and P is not None:
            n = 1
            while P.is_divisible_by(2):
                P = P.division_points(2)[0]
                n *= 2
            newline = "$%s$ & $%s$ & $%s$ \\\\"%(disc,h,(latex(n)+'\\cdot' if n >1 else '')+latex((P[0],P[1])))
            if len(newline) < 200:
                lines.append(newline)
            else:
                newline = "$%s$ & $%s$ & $%s$ \\\\"%(disc,h,(latex(n)+'\\cdot' if n >1 else '')+'\\Big('+latex(P[0])+',')
                lines.append(newline)
                newline = " &   & \\hspace{1cm}$%s\\Big)$ \\\\"%(latex(P[1]))
                lines.append(newline)


        if h > 1: # and P is None:
            pol = Plist[0][0].minpoly() #absolute ?
            #pol *= pol.denominator()
            newline = '$%s$ & $%s$  & '%(disc,h)
            if pol.degree() > 2:
                curr_deg = 1
                pol1 = []
                while pol != 0:
                    newpol = pol.truncate(curr_deg)
                    pol1.append(newpol)
                    pol -= newpol
                    curr_deg += 2
                    #pol1.append(pol-pol.truncate(4))
                pol1 = list(reversed(pol1))
                lines2.append(newline + '$%s$\\\\'%latex(pol1[0]))
                for ii in range(1,len(pol1)):
                    lines2.append('& & $+ %s$\\\\'%latex(pol1[ii]))
            else:
                newline += '$%s$\\\\'%(latex(pol))
                lines2.append(newline)
            # for ii in range(h):
            #     newline = "$%s_{%s}$ & $%s$ & $%s$\\\\"%(disc,h,ii+1,latex(Plist[ii][0]))
            #     lines2.append(newline)
        print 'Discriminant = %s, h = %s'%(disc,h)
        print "P = %s"%P
        if h > 1:
            print "Plist = %s"%Plist
    for line in lines:
        all_lines.append(line)
    #all_lines[-1] = all_lines[-1][:-4] # Avoid extra line break
    if len(lines2) > 0:
        all_lines[-1] += '&&\\\\\\hline '
        all_lines.append('$D$ & $h$ & $h_D(x)$\\\\\\hline\\hline')
        for line in lines2:
            all_lines.append(line)
    all_lines.append('\\\\\\end{tabular}')

    out = open(outfile,'w')
    for line in all_lines:
        out.write(line)
        out.write('\n')
    out.close()
