
#Hecke.elem_type(::Type{Hecke.NfMorSet{T}}) where {T<:Hecke.LocalField} =
#Hecke.LocalFieldMor{T,T}

function random_ali(o::NfOrd)
     b = basis(o)
   #  L = nf(o)
     n = degree(L)
    return  sum([rand(1:5)*b[i] for i in 1:n])
#return sum( [ r[i]*b[i] for i in 1:n])
end


Hecke.elem_type(::Type{Hecke.NfMorSet{T}}) where {T<:AnticNumberField} =
    Hecke.NumberFieldMor{T,T}
function lattice_gen_theta(psi,P)
    #p = gens(P)[1]     # :rand =false
    p = Int(P.minimum)
    ol = order(P)
    pi = uniformizer(P)
    theta = normal_basis_elt(ol, psi) #: rand = rand)
    v = valuation(theta, P)
    v1 = 1+ Int(floor(ramification_index(P)/(p-1) ))   # absolute_ram_index if over relative 
    v = max(0, v1-v)
    theta = ol( theta*pi^v)
 return theta,v
 end


function normal_basis_elt(O, psi) #rand==false
    G = domain(psi)
    bool = false 
    bas = basis(O)
    if  !bool
       for i in 1:length(bas)
          D = matrix([coefficients(  psi(g)(elem_in_nf(bas[i]))) for g in G])
          if det(D) != 0 
             return bas[i]
             #break i  
            end
        end
     end
    bool = false
    while !bool
       r = random_ali(O)
       D = matrix([coefficients(  psi(g)(elem_in_nf(r))) for g in G])
          if det(D) != 0
             bool = true
             return r            
          end
      end  

 # if not found then one must try with rando element of ol
end

function elem_to_seq(x::GrpAbFinGenElem)
    return [x[i] for i = 1:ngens(parent(x))]
end


 function lattice_ali(P,p,psi)
    o = order(P)
    pi = uniformizer(P)
    G = domain(psi)
    bool = false
    for i in 1:100
       while true
           theta,v = lattice_gen_theta(psi, P)#, p, rand)
           bool = true
           #theta = coefficients(elem_in_nf(theta))
           Gen = [o(psi(g)(elem_in_nf(theta)) ) for g in G ]
           M = matrix([ coefficients(elem_in_nf(x)) for x in Gen])
           bool = rank(M) == length(G)
          if bool
             break
          end
        end
     end
 
  # do somehting more
 # one can choose a large value of second argument
 # ZpGtheta := Lattice(M); create this
 return theta, v+1
 end




function Sunit_group_action(L,prm,psi)
    # Let P be a set of primes then this computes the sunit group and and its G-action
        G = domain(psi)
        GG = [g for g in G]
       ol = maximal_order(L)
       fac = prime_divisors(discriminant(ol))
       for i in prm
           push!(fac, i)
       end
       fac = sort_seq(fac)
       #fac = sort(fac)
       S =NfOrdIdl[]
       for i in fac
           pp = prime_decomposition(ol,i)
           for p in pp
               push!(S,p[1])
           end
       end
       #u,mu = Hecke.sunit_group_fac_elem(S)
       u, mu = Hecke.sunit_group(S)
       #act =GrpAbFinGenMap[]
       tup_act= [] #Tuple{PermGroupElem, PermGroupElem}[]
    
        for i in 1:length(G)
         push!(tup_act,( GG[i], hom(u,u,[mu\(psi(GG[i])(mu(u[j]))) for j in 1:ngens(u)]) ))
        # push!(tup_act,( G[i], hom(u,u,[preimage(mu, psi(G[i])(L( mu(u[j]))) )  for j in 1:ngens(u)]) ))  
         end
    return u,mu,tup_act
    end

function exp_truncated(x::Hecke.LocalFieldElem,n)
    return sum([ x^i//factorial(i) for i in 0:n])
end
        
function Valuation(x)
    if iszero(x)
        return ZZ(precision(x))
    else
        return ZZ(absolute_ramification_index(parent(x)) * valuation(x))
    end
end
function compute_lpmult_mod(L,P,psi,list,theta,m)
    # computes the module with respect to ideal
       lp = list[1]
       inc_lp = list[2]
       psil = list[4]
       Gp = list[3]
       pi = uniformizer(P)
       G = domain(psi)
       GG = [x for x in G]
       H = [x for x in Gp]
       HH = [x for x in H]
       ol = maximal_order(L)
       pil = uniformizer(lp) #  inc_lp(pi.elem_in_nf) #check this
       q,pi_l_q = quo(o,P^m)
       qmul, i_qmul = unit_group(q)
      phi_l_q = pi_l_q*pseudo_inv(i_qmul)
      phi_q_l = i_qmul* pseudo_inv(pi_l_q)
    
     p = P.minimum
       N = Int(ceil( Int(m) / ( valuation(theta, P)- ramification_index(P)/(Int(p)-1))))
     expTheta = inc_lp\(exp_truncated(inc_lp(elem_in_nf(theta)),  N ))
      conjq = [ phi_l_q(ol( psi(g)(elem_in_nf(expTheta)) )) for g in HH]
      S1, pi_qmul_S1 = quo(qmul , sub(qmul,conjq)[1] );  #  check sub function
      S, S_S1 = snf(S1)
      pi_qmul_S = pi_qmul_S1*pseudo_inv(S_S1)
      phi_l_S = phi_l_q*pi_qmul_S;    
     #// G-Wirkung auf S
       function actS(g,s)
              phi_l_S(ol(psi(g)(elem_in_nf(phi_l_S\(s)))))
        end
        ZgenS = [S[i] for i in 1:ngens(S) ];

        #    // G-Wirkung auf L_P^\times / X  als Matrizen
         #check from here
            #M = Vector{fmpz_mat}[];
              M = fmpz_mat[]
             for k in 1:length(HH) # [1..#HH] do
                g = HH[k];
                bilder =Vector[];
               # bilder =fmpz_mat[];
             #  // Wirkung auf pi lokal
                bild = psil(g)(pil);  #wiered coercion
        
                 seq = (phi_l_S(ol( inc_lp\(bild//pil)))).coeff;
                  push!(bilder, append!([1], seq));
                   #bilder = Vector(append!([1], seq))
                 #push!(bilder, matrix(FlintZZ,1, ngens(S)+1,append!([1],seq) ))
        
        
                #bilder := bilder cat [ [0] cat ElementToSequence(actS(g,s) ) : s in ZgenS];
               # bilder := bilder cat [ [0] cat (actS(g,s)).coeff) : s in ZgenS];
                 bilder = vcat(bilder, [append!([0], (actS(g,s)).coeff) for s in ZgenS])
             # bilder = vcat(bilder, [matrix(FlintZZ,1, ngens(S)+1, append!([0], (actS(g,s)).coeff)) for s in ZgenS])
                #push!(M, bilder)  
               push!(M ,  matrix(ZZ, bilder) );
            end
        
           Y =free_abelian_group(length(ZgenS)+1);
          # mmY := map< H -> Aut(Y) | g :-> hom< Y -> Y | 
           #     y :-> Y!Eltseq(Vector(Eltseq(y))*M[ Index(HH,g)]) > >;
            function mmY(g)
                   hom(Y,Y,[Y( y.coeff * M[position_ali(g,HH)]) for y in gens(Y) ])      
               end
        
             X, qX = quo(Y, [order(ZgenS[i])* Y[i+1] for i in 1:length(ZgenS) ]);
        
           #  mmX := map< H -> Aut(X) | g :-> hom< X -> X | x :-> qX( x@@qX @ mmY(g) ) > >; 
             function mmX(g)
                   hom(X,X,[ qX( mmY(g)(qX\(x))) for x in gens(X)])
            end
           # mmX = map_from_func( g .....)

     function lp_X(x)
         qX( Y(  append!([Valuation(x)], (phi_l_S(ol(inc_lp\(  x// pil^(Valuation(x))))  ) ).coeff )  ))
     end
    function X_lp(y)
          yy = (qX\(y)).coeff
           rem_1st= Vector([yy[i] for i in 2:length(yy)])
         pil^(yy[1]) * inc_lp(elem_in_nf( phi_l_S\( S( rem_1st)) ))
     end

     qmm = MapFromFunc(x-> lp_X(x), y->X_lp(y), lp, X)

    return X, mmX, qmm #lp_X, X_lp;
end





function leftCosetRepresentatives(G::PermGroup, H::PermGroup, RepSys ) #-> SeqEnum
#{ Compute a system of representatives of G/H. }

    if RepSys == 0
        R = [one(G)];
        for g in [g for g in G if g != one(G)] 
            if ! any([g in tau*H for tau in R]) 
                push!(R, g);
            end 
        end
    else
        #// first use representatives given by RepSys
        R = [];
        for g in [g for g in RepSys ] 
            if ! any([g in tau*H for tau in R]) 
                Append(~R, g);
            end 
        end 
        RepSys = R;

        for g in [g for g in G if g != one(G)] 
            if ! any([g in tau*H for tau in R])
                push!(R, g);
               # // add also those that arrise by multiplying with
                #// elements in given Rep.System

                for sig in [g*sig : sig in RepSys ]
                    if ! any([sig in tau*H : tau in R])
                        push!(R, sig)
                    end
                end 
            end
        end

    end

    return R;
end 



#=
CartPrd=Iterators.product(GG,GG)
cc = collect(CartPrd)
h = MapFromFunc(x-> psi(x[1])*psi(x[2]) , ii, codomain(psi))
h = MapFromFunc(x-> psi(x[1])*psi(x[2]) , cp, codomain(psi))


=#







function inducedModule(M, H, phi, G )#: RepSys := 0) -> GrpAb, Map, SeqEnum, SeqEnum, SeqEnum
#={ Given a (left) H-module M as abelian group with H-action by phi: H -> Aut(M)
  and H a subgroup of G. Compute the induced module N as a direct sum
  and return N, the G-action on N, a left representation system R of G/H,
  and sequences of embeddings M -> N and projections N -> M according to R.
}=#
    
    #H = domain(phi);
    
    if (length(H) == length(G)) 
        return M, phi, [one(G)], [identity_map(M)], [identity_map(M)]       # [ map< M->M | m:->m > ],  [ map< M->M | m:->m > ];
    end 
    
    #//N, iota := finiteSum(M, #G/#H);
    N, proj, inc = direct_product([M for i in 1:Int(length(G)//length(H))]..., task = :both )
    
    #// Left coset representatives
    R = leftCosetRepresentatives(G, sub(G,H)[1] ,0 )# : RepSys := RepSys);
    
    #// for all g in G, tau in R
    #// compute r in R, h in H  such that  r*h=g*tau
    GG = [g for g in G];
    cosetAct = [[ [[ position_ali(r, R), h] for r in R, h in H if r*h == g*tau][1]   for g in GG] for tau in R];
    
   #= //cosetAct := map< car<G, R> -> car<R, H> |
    //    x :-> [ <r,h> : r in R, h in H | r*h eq x[1]*x[2] ][1]
    //>;
    
    // images from M into N w.r.t. tau in R=#
    B1 = Any[]
    for i = 1:length(inc)
        for m in gens(M)
            push!(B1, inc[i](m))
        end
    end
    B2 = Any[]
    for i = 1:length(inc)
        for m in gens(M)
            push!(B2, [m, i])
        end
    end
    
    #B1 = [inc[i](m) for m in gens(M), i in 1:length(inc)];
    #B2 = [[m, i] for m in gens(M), i in 1:length(inc)];
    images = Any[]
    for g in GG
        im =Any[]
        for i in 1:ngens(N)
            k = position_ali(N[i], B1)
            c = cosetAct[B2[k][2]][position_ali(g, GG)]
            push!(im, inc[c[1]]( phi(c[2])(B2[k][1]) ))
        end
        push!(images, im)
     end



    #// images of g*b using coset action
    #=images = [ [
        inc[c[1]]( phi(c[2])(B2[k][1]) )
        where c = cosetAct[B2[k][2]][position_ali(g, GG)]
        where k = position_ali(N[i], B1) for i in 1:length(gens(N))] 
    ] for g in GG];
    
    #// G-action on M3
    psi = map< G -> Aut(N) | g :-> map< N -> N |
        x :-> &+([ y[i]*img[i]  : i in [1..#y]])  where img := images[Index(GG,g)] where y := Eltseq(x)
    > >;=#
    #=function psi(g)
        return MapFromFunc(x-> sum([elem_to_seq(x)[i]*images[position_ali(g, GG)][i] for i = 1:ngens(N) ]), N, N)
    end=#
      
    psii = MapFromFunc(
                       g-> MapFromFunc(x-> sum([elem_to_seq(x)[i]*images[position_ali(g, GG)][i] for i = 1:ngens(N) ]), N, N), 
                       G,  Hecke.MapParent(N,N, "mapping") 
                        )
    psi = MapFromFunc(g-> hom(N, N, [psii(g)(a) for a in gens(N)]), G, Hecke.MapParent(N,N, "mapping") )
    # psi returns GrpAbFinGenMap    

    #=  function psii(g)
        img = images[position_ali(GG,g)]
        function autN(x)
            elem = elem_to_seq(x)
            return sum([elem[i]*img[i] for i = 1:length(elem))] ) 
        end
        return autN
    end =#
    #=// print "check action";
    // // garantee correct G-action
    // assert &and({ psi(g)(psi(h)(b)) eq psi(g*h)(b) :   b in Generators(N), g in G, h in G});
    // // and correct embedding
    // assert &and({ iota[1](phi(h)(m)) eq  psi(h)(iota[1](m))   : m in Generators(M), h in H});
    =#
    return N, psi, R, inc, proj;
end 



function position_ali(a,G)
    return  findfirst(x->x==a,G)
end

function sort_seq(A)
    B = typeof(A[1])[]
    for a in A
       if !(a in B)
          push!(B,a)
        end
     end
 return B
 end







function gfc(L)
    @assert iszero(signature(L)[2]) 
   o = maximal_order(L)
    G, psi = automorphism_group(PermGroup, L)
    psiL = MapFromFunc(x-> psi(x^-1), G, codomain(psi))
    prm = prime_divisors(discriminant(o))
   # push!(prm, p0)
   # S = NfOrdIdl[]
#    for p in prm
  #      for y in  [x[1] for x in prime_decomposition(o,p)]
    #        push!(S, y)
   #     end 
  #  end
  #sub = subfields(L)
  #@assert length(class_group(L)[1]) ==1
  U, mU , sigU = Sunit_group_action(L,prm,psiL) #sunit_group_fac_elem(S)
  GG = [x for x in G]
  CartPrd=Iterators.product(GG,GG)
  cart = collect(CartPrd)
  #psiU = MapFromFunc(x-> sigU[position_ali(x, GG)], G, parent(sigU[1]))
  function psiU(g)
    return (sigU[position_ali(g,GG)])[2]
  end

  lst = []
  thetaAll = []
for p in prm 
    pl = prime_decomposition(o,p)[1][1]
    pil = uniformizer(pl)
    if  ramification_index(pl) == 1
        theta = one(o)
        m = 0
    else
        theta, m = lattice_gen_theta(psi,pl) #,pl.minimum,false)
    end
    push!(thetaAll, theta)
    lp, mp = Hecke.generic_completion(L,pl)
    GP = [g for g in G if all([ psiL(g)(elem_in_nf(x)) in pl for x in gens(pl)])]
    #GP = sub(G, Gp)
    function psilp(g)
       return pseudo_inv(mp)*psiL(g)*mp
    end
    list = [lp, mp, GP, psilp]
    ML, psiML, qML = compute_lpmult_mod(L,pl,psi,list,theta, m+5);
    indML, psiIndML, RL, kappaML, projML = inducedModule(ML, GP, psiML, G);
    #diagL = MapFromFunc(x -> sum([kappaML[i]( qML( mp( psiL(RL[i]^-1)( mU(x))))) for i = 1:length(kappaML)]), U, indML);
    diagL = let X = indML
            MapFromFunc(x -> sum([kappaML[i]( qML( mp( psiL(RL[i]^-1)( mU(x))))) for i = 1:length(kappaML)]), U, indML)
    end 
    #projML_L= hom<indML->L | x:-> (&+[x@projML[i]@@qML :i in [1..#projML]])@@iotaL   >;
    #projML = map_from_func( x->  mp\(sum([ qML\(projML[i](x)) for i = 1:length(projML) ])), indML, L)  

   #c2 = MapFromFunc(x-> zero(indML), cart, indML)
   c2 = let X = indML
       MapFromFunc(x-> zero(X), cart, X)
     end 
    push!(lst, Tuple([indML, psiIndML, diagL, c2]))
end

function psiM(g)
    return hom(U, U, [U[i] for i in 1:ngens(U)])
end
          
    #psiM = MapFromFunc(x-> hom(U,U,[U[i] for i = 1:ngens(U)]), sub(G, [GG[1]])[1], GrpAbFinGenMap(U) )
 #=   
#indML, psiIndML, RL, kappaML, projML = inducedModule(U, [GG[1]], psiM, G);
#diagL = MapFromFunc( x-> sum([kappaML[i](psiU(RL[i]^-1)(x) ) for i = 1:length(kappaML) ]), U, indML)=#

indMLi, psiIndMLi, RLi, kappaMLi, projMLi = inducedModule(U, [one(G)], psiM, G);
diagLi = let X = indMLi
        MapFromFunc( x-> sum([kappaMLi[i](psiU(RLi[i]^-1)(x) ) for i = 1:length(kappaMLi) ]), U, X)   
    end
#c2 = MapFromFunc(x-> zero(indML), cart, indML)
c2i = let X = indMLi
       MapFromFunc(x-> zero(X), cart, X)
    end
push!(lst, Tuple([indMLi, psiIndMLi, diagLi, c2i]))
#push!(lst, Tuple([indML, psiIndML, diagL, c2]))
JL, projJL, inclJL = direct_product([lst[i][1] for i=1:length(lst)]..., task= :both )
 projJL2 = [ hom(domain(p),codomain(p), [ p(JL[i]) for i =1:ngens(JL)])  for p in projJL ];;
#actJL= [ hom(JL,JL, [sum([inclJL[k](lst[k][2](g)( projJL[k](JL[j]))) for k in 1:length(lst)]) for j in 1:ngens(JL) ]) for g in G] 
actJL = [MapFromFunc(x-> sum([inclJL[k](lst[k][2](h)( projJL[k](x))) for k in 1:length(lst)]), JL, JL)  for h in G];

#psiJL := MapFromFunc( g -> actJL[ position_ali(g,GG), G, Hecke.MapParent(JL,JL, "aut") ;
psiJLL = MapFromFunc( g -> actJL[position_ali(g,GG)], G, Hecke.MapParent(JL,JL, "automorphism")) ;
########change  map from macfrom to hom for cohomology
psiJL = MapFromFunc(g-> hom(JL, JL, [psiJLL(g)(a) for a in gens(JL)]), G, Hecke.MapParent(JL,JL, "mapping") )
ac = [psiJL(g) for g in gens(G)]
cm=Main.GrpCoh.CohomologyModule(G,ac)
return cm, psiJL, JL, [psiL, lst]
end
#=


#=function psiJL(g)
    return actJL[position_ali(g,GG)]
end=#

 #MapFromFunc( g->actJL[position_ali(g,GG)], G, )
 gamma = MapFromFunc(g-> sum( [ inclJL[i](lst[i][4](g)) for i = 1:length(lst)]) , cart, JL) 
#checke c2 the first defined
#gamma := map< car<G, G> -> JL | x :-> &+([ x @ lst[i,4] @ inclJL[i]  : i in [1..#lst] ]) >;


embJL = MapFromFunc(x-> sum([inclJL[i](lst[i][3](x)) for i=1:length(lst) ]) , U, JL)
# embJL := map< US -> JL | x :-> &+([ x @ lst[i,3] @ inclJL[i] : i in [1..#lst]] ) >;
 B = [embJL(g) for g in gens(U)];
    CL, qCL = quo(JL, B);
function psiCL(g)
    return inv(qCL)*psiJL(g)*qCL 
end
#=
MapFromFunc(x-> psiCL(x^-1), G, Hecke.MapParent(CL,CL,"aut"));
function psiCLr(g) 
    return psiCL(g^-1)
end=#
ac = [hom(CL,CL, [psiCL(g)(a) for a in gens(CL)] )  for g in G];
CohL = Main.GrpCoh.CohomologyModule(G,ac)

 CohL = CohomologyModule(G, CL, psiCLr);





end




=#
