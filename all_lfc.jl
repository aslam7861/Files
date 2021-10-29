Hecke.elem_type(::Type{Hecke.NfMorSet{T}}) where {T<:Hecke.LocalField} =
    Hecke.LocalFieldMor{T,T}

#export unramified_extension

Hecke.elem_type(
    ::Type{Hecke.NfMorSet{T}},
) where {T<:Union{FlintQadicField, Hecke.LocalField}} = Hecke.LocalFieldMor{T,T}
#Hecke.elem_type(::Type{Hecke.NfMorSet{T}}) where {T <: Hecke.LocalField} = Hecke.LocalFieldMor{T, T}

function random_elem(L::Hecke.LocalField)
    b = basis(L)
    n = degree(L)
    r = [rand(1:5*n) for i = 1:n]
    return sum([r[i] * b[i] for i = 1:n])
end

function elem_to_seq(a)
    return [coeff(a, i - 1) for i = 1:degree(parent(a))]
end
#######################coerce the element form base field if it lies############
function coercion(a, L)
    b = basis(L)
    seq = elem_to_seq(a)
    @assert sum([seq[i] for i = 2:length(seq)]) == L(0)

    return seq[1] #sum([coeff(a, i - 1) * b[i] for i = 1:length(b)])
end

function gen_local(
    L::Union{FlintQadicField, Hecke.LocalField},
    K::Union{FlintPadicField, FlintQadicField, Hecke.LocalField},
)
    A = []
    push!(A, gen(L))
    L = base_field(L)
    while !(L == K)
        push!(A, gen(L))
        L = base_field(L)
    end
    return A
end

############## compute n such that g = f^n for all elements of x#########

function find_power(g, f, x, max)
    #   local p, m, fX, gX, X;
    X = [x]
    m = (max == 0 ? Infinity() : max)
    p = 0
    fX = [x]
    gX = [g(domain(g)(x)) for x in X]
    while p <= m
        if all([iszero(gX[i] - fX[i]) for i = 1:length(fX)])
            return p
        end
        fX = [f(x) for x in fX]
        p = p + 1
    end
    error("maximum power exceeded!!!")
end;



function Hilbert_Ninety1(c, phi, bas)
#{Computes an element x satisfying x^(phi -1)=c using Hilbert 90 formula}
    L = domain(phi)
    pii = uniformizer(L)
    ee = absolute_ramification_index(parent(c))
    if ee * valuation(phi(pii) // pii - c) >= precision(c)
        return pii
    end
    d = inertia_degree(L) #no bsolute inertia because phi^d =1
    gamma = 1 + bas[length(bas)]
    A = [gamma, c * phi(gamma)]
    for i = 3:d
        push!(A, c * phi(A[i-1]))
    end

    c_frob = sum(A)

    if norm(c_frob) == 0 || ee * valuation(c_frob) >= 1
        gamma = random_elem(L)
        A = [gamma, c * phi(gamma)]
        for i = 3:d
            push!(~A, c * phi(A[i-1]))
        end
        return sum(A)
    else
        return sum(A)
    end
end
function prime_field(L::FlintQadicField)
    base_field(L)
end
function Frobenius_automorphism(L::Union{FlintQadicField, Hecke.LocalField})
    G, mG = automorphism_group(L)
    @assert length(gens(G)) == 1
    return mG(gens(G)[1]), mG(gens(G)[1]^-1)
end

################# This solves frobeniu equations  for all element of C########
function Frobenius_Equations(C, phi, bas)
    set = elem_type(parent(C[1]))[]
    L = parent(C[1])
    for i = 1:length(C)
        if C[i] == L(1)
            push!(set, L(1))
        else
            c = C[i]^-1
            push!(set, Hilbert_Ninety1(c, phi, bas))
        end
    end
    return set
end

#absolute_inertia_degree(K::QadicField) = degree(K)  # made pull request
function maximal_unramified_subextension(L::Hecke.LocalField)
    n = absolute_degree(L)
    inert_deg = absolute_inertia_degree(L)
    if n == inert_deg #Hecke.absolute_inertia_degree(L)
        return L
    end
    L = base_field(L)
    while !(absolute_degree(L) == Hecke.absolute_inertia_degree(L))
        L = base_field(L)
    end
    if absolute_inertia_degree(L) != inert_deg
        error("extensions not in order")
    end
    return L

end

################assuming the valuation of 0 as precision of element########
function Valuation(x)
    if iszero(x)
        return precision(x)
    else
        return absolute_ramification_index(parent(x)) * valuation(x)
    end
end

function continued_automorphism_image(x, m, b)
    y = elem_to_seq(x)
    return sum([parent(x)(m(y[i])) * b^(i - 1) for i = 1:length(y)])
end

function cartesian(G, H)
    @assert length(G) == length(H)
    n = length(G)
    A = Tuple{elem_type(G),elem_type(H)}[]
    H = [x for x in H]
    G = [x for x in G]
    # c = 1 
    for i = 1:n
        for j = 1:n
            push!(A, (G[i], H[j]))
        end
    end
    return A
end

function position_ali(G, a)
    return findfirst(x -> x == a, G)
end

#### extend the frobenius automorphism of K to L where q is length of residue field of K##########


function continue_frobenius(frob, L, q)
    # frob = frob
    K = domain(frob)
    B = reverse(gen_local(L, K))
    @assert length(B) == 1
    #for b in B
    b = B[1]
    #f_p = minimal_polynomial(b);
    f_p = defining_polynomial(parent(b))
    f_pp = polynomial(parent(b), [frob(coeff(f_p, i)) for i = 0:degree(f_p)])
    rts = roots(f_pp, parent(b))
    # G, mG = automorphism_group(parent(b))
    #rts = [mG(x)(b) for x in G] ###seems no connections with min_poly
    #rts = [r[1] for r in roots( polynomial(L,[ frob(x) :  x in Coefficients(f)])) ];
    @assert length(rts) == degree(f_p)
    cont = [
        MapFromFunc(
            x -> sum([
                parent(r)(frob(elem_to_seq(x)[i])) * r^(i - 1) for i = 1:degree(parent(r))
            ]),
            parent(b),
            parent(b),
        ) for r in rts
    ]
    for j = 1:length(cont)
        m = cont[j]
        cand = true
        for i = 0:degree(parent(b))-1
            if Valuation(m(b^i) - (b^i)^q) == 0
                cand = false
                #  return MapFromFunc(x-> m(x), parent(b), parent(b))   
                break
            end
        end
        if cand
            return m
            #return MapFromFunc(x-> m(x), parent(b), parent(b))    
            #return mm
            break
        end
    end
    #return frob
end


function minimal_polynomial(b::Union{qadic, Hecke.LocalFieldElem})
    L = parent(b)
    m = matrix([[L(coeff(b * x, i - 1)) for i = 1:degree(L)] for x in basis(L)])
    h = charpoly(m)
    if iszero(det(sylvester_matrix(h, derivative(h))))
        error("to be implemented")
    else
        return h
    end
end

#=
function minimal_polynomial_check(b::Union{qadic, Hecke.LocalFieldElem})
    L = parent(b)
    m = matrix([[L(coeff(b * x, i - 1)) for i = 1:degree(L)] for x in basis(parent(L))])
    h = charpoly(m)
    if iszero(det(sylvester_matrix(h, derivative(h))))
       error("to be implemented")
    else
       return h 
    end
 end=#

#=
L/Q_p a Galois extension with  inertia degree d ans  G = Gal(L/Q_p). L2 is an unramified extension of degree e_(L/Q_p) and psi maps G to aut(L/Q_p). phi is Frobenius automorphism of L2. Let K2 be the maximal unramified subextension in L2 then this function computes the set of actions of phi and G on Vectorspace(L2,d).    
=#

function galois_act_L_tensor_Knr(OL, OL2, G, psi, phi)

    #   // Test whether algorithm is applicable
    OK = maximal_unramified_subextension(OL) # maximal_unram_subext_simple(OL);
    Zp = Prime_field(OK)
    GG = [g for g in G]
    d = absolute_inertia_degree(L)   #(OL,Zp);
    # // Compute i such that sigma_OK = phi^i for all sigma in G
    #  // and extensions sigmaHut of sigma such that sigmaHut^(-1)=phi^(-i) on K2
    sigmaHut, frobIndex = continuations_with_unram_restriction(OL, G, psi, OL2) # phi);  ## compute this
    #// Frobenius automorphism on \prod L2
    L2 = OL2 #FieldOfFractions(OL2);
    if d == 1
        prodL2_1 = Tuple{elem_type(L2)}[Tuple([L2(0)])]
        prodL2 = parent(prodL2_1[1])
        # else 
        #   "to be implemented"  # prodL2 := CartesianProduct([L2 : y in [1..d] ]);
    end
    V = VectorSpace(OL2, d)
    function frobeniusMap(x, n) #::typeof(prodL2_1[1]))
        if n == 0
            return x
        else
            for j = 1:n
                x = Tuple([i == d ? phi(x[1]) : x[i+1] for i = 1:d])
            end
            # return V([i == d ? phi(x[1]) : x[i+1] for i = 1:d])
        end
        return x
        #return ( Tuple([ phi(x[1])]))
    end
    #  frobeniusMap = map< prodL2 -> prodL2 | x :->  < i eq d select phi(x[1]) else x[i+1]  : i in [1..d]> >;
    # // action of G on \prod L2
    function GAction(x, y) #::elem_type(G), y::elem_type(prodL2))i
        idx = position_ali(GG, x)
        v = frobeniusMap(y, (d - frobIndex[idx]) % d)
        return Tuple([sigmaHut[idx](v[i]) for i = 1:length(v)])
    end
    # Gaction := map< car<G, prodL2> -> prodL2 | x :->
    #    apply_map( (frobeniusMap^((d-frobIndex[Index(GG,x[1])]) mod d))( x[2] ), sigmaHut[Index(GG, x[1])]) >;

    return frobeniusMap, GAction, frobIndex
end

function Prime_field(L)
    parent(absolute_norm(L(1)))
end

function tupleQuotient(t1, t2)
    return Tuple([t1[i] // t2[i] for i = 1:length(t1)])
end
function tupleProduct(t1, t2)
    return Tuple([t1[i] * t2[i] for i = 1:length(t1)])
end

function tupleInverse(t)
    return Tuple([t[i]^(-1) for i = 1:length(t)])
end










#={ Compute the inverse of the given automorphism.  ##"compute its inverse"
     If inv is given, the inverse is computed as a continuation of inv if possible. } 
=#
function inverseAutomorphism(aut, inv)  
    L = domain(aut)
    K = domain(inv)
    invAut = inv
    B = reverse(gen_local(L, K))
    @assert length(B) == 1 #"For more than one need to do more work"
    #for b in B
    b = B[1]
    if (aut(b) == b)
        #invAut = map<Parent(b) -> Parent(b) | x :-> continued_automorphism_image(x, invAut, b) >;
        function invAut(x)
            return sum([invAut(elem_to_seq(x)[i]) * b^(i - 1) for i = 1:degree(parent(b))])
        end
    else
        #f_p = minimal_polynomial(b);
        f_p = defining_polynomial(parent(b))
        #@assert iszero(evaluate(f_p,b))

        f_pp = polynomial(parent(b), [invAut(coeff(f_p, i)) for i = 0:degree(f_p)])
        rts = roots(f_pp, parent(b))
        @assert length(rts) == degree(f_pp)
        #A, mA = automorphism_group(parent(b))
        #rts =[mA(a)(b) for a in A]
        #rts = [r[1] : r in roots( polynomial(L,[ invAut(x) :  x in Coefficients(f)])) ];
        @assert length(rts) == degree(f_p)
        cont = [
            map_from_func(
                x -> sum([
                    parent(r)(invAut(elem_to_seq(x)[i])) * r^(i - 1) for
                    i = 1:length(elem_to_seq(x))
                ]),
                parent(b),
                L,
            ) for r in rts
        ]
    end
    vv = [Valuation(aut(c(b)) - b) for c in cont]
    if all([iszero(a) for a in vv])
        return cont[1]
    else
        vv = [Int(ZZ(a)) for a in vv]
        return cont[indexin(maximum(vv), vv)[1]]
    end

end

########### The local fundamental class#####################################

function canonical_generator(L, K, prec)
    Qp = Prime_field(L)
    Zp = ring_of_integers(Qp)
    d = absolute_inertia_degree(L)
    G, mG = absolute_automorphism_group(L)
    steps = prec + 2
    psi = map_from_func(x -> mG(x^-1), domain(mG), codomain(mG))
    #=function psi(g)
        return mG(g^-1)
    end=#
    d = absolute_inertia_degree(L)

    if d == absolute_degree(L)
        #return ali_cocycle_lfc_G(L,prec)
        pi = uniformizer(K)
        phi = psi(G[1])
        # phi = FrobeniusAutomorphism(L,K);
        #//phi := FrobeniusAutomorphism(L);
        phi = [g for g in G if all([is_equal(psi(g)(b), phi(b)) for b in gen(L, K)])]
        if length(phi) == 0
            # ungenauer
            phi = psi(G[1])  # FrobeniusAutomorphism(L, K);
            phi = [
                g for g in G if all([
                    valuation(psi(g)(b) - phi(b)) >= precision(L) * 95 / 100 for
                    b in gen(L, K)
                ])
            ]
        end
        phi = phi[1]
        GG = [phi^i:i in [0 .. length(G) - 1]]
        function result(x, y)
            if position_ali(GG, x) + position_ali(GG, y) - 2 < length(G)
                return L(1)
            else
                return pi
            end
            return result
        end
    end


    L1 = L
    OL = L
    K1 = K
    e = ramification_index(L1) #,K1);
    OL1 = L1 #ring_of_integers(L1);
    OL2 = unramified_extension(L, e)[1]
    u = uniformizer(K1) * uniformizer(L1)^-e
    gamma1 = Hecke.norm_equation_unramified(OL2, OL1(u))
    pii = gamma1 * OL2(uniformizer(L1))
    # else
    pii = OL2(pii)
    # end if;f
    phi, phiInv = Frobenius_automorphism(OL2)
    GG = [x for x in G]
    #  phi := FrobeniusAutomorphism(OL2, OL);
    #//    phi := FrobeniusAutomorphism(OL2);// "this makes problem in the following action";
    frobAction, GAction, frobIndex = galois_act_L_tensor_Knr(OL, OL2, G, psi, phi)#, phiInv);
    pi_sigma = [(GAction(g, ([pii for i = 1:d])))[1] for g in G]  # add Tuple
    pisigmapi = [OL2((pi_sigma[i] // pii)) for i = 1:length(pi_sigma)]
    u_sigma = Frobenius_Equations(pisigmapi, phi, basis(OL2))
    ee = absolute_ramification_index(L)
    @assert all([
        (Valuation(phi(u_sigma[i]) // u_sigma[i] - pisigmapi[i])) > prec for i = 1:degree(L)
    ])
    d = absolute_inertia_degree(OL) #,Zp);
    L2 = OL2 # FieldOfFractions(OL2);
    #prodOL2 = cart_product([OL2 for y in 1:d ]); # in  TR,  d is 1
    prodOL2 = VectorSpace(OL2, d)
    tup_sigma = []
    GG = [g for g in G]
    for g in GG
        ind = position_ali(GG, g)
        frobIdx = frobIndex[ind]
        if frobIdx == 0 #then
            frobIdx = d
        end
        push!(
            tup_sigma,
            Tuple([u_sigma[ind] * (i <= frobIdx ? OL2(1) : pi_sigma[ind]) for i = 1:d]),
        )
        #push!(tup_sigma, prodOL2( [ u_sigma[ind] * ( i <= frobIdx ? OL2(1) :  pi_sigma[ind] ) for i in 1:d  ]) );
    end
    #   car_G = cartesian(G,G)
    car_G = [(x, y) for x in G, y in G]
    function cc(x) #::typeof($car_G[1]) )
        tt = tupleProduct(
            GAction(x[1], tup_sigma[position_ali(GG, x[2])]),
            tup_sigma[position_ali(GG, x[1])],
        )
        return tupleQuotient(tt, tup_sigma[position_ali(GG, x[1] * x[2])])
    end

    #c = precompute_map(cc);
    c = [[x, cc(x)] for x in car_G]
    #@assert minimum([ minimum([ee*valuation(y[1]-y[i]) for i in 1:length(y)])
    #      for y in [ c(x) for  x in domain(c)]]) >= (prec+1);
    function can_gen(x)#typeof(car_G[1]))
        return (elem_to_seq(c[position_ali(car_G, x)][2][1])[1])^(-1)
    end

    return can_gen, car_G
end



#########################################################


Hecke.elem_type(::Type{Hecke.NfMorSet{T}}) where {T<:Hecke.LocalField} =
    Hecke.LocalFieldMor{T, T}

function all_coeff(f::Hecke.AbstractAlgebra.Generic.Poly)
    return f.coeffs #[coeff(f, i) for i = 0:length(coefficients(f))-1]
end

function random_elem(L::Hecke.LocalField)
    b = basis(L)
    n = degree(L)
    r = [rand(1:5*n) for i = 1:n]
    return sum([r[i] * b[i] for i = 1:n])
end

#=
function Hilbert_Ninety1(c, phi, bas)#->.{Computes an element x satisfying x^(phi -1)=c using Hilbert 90 formula twice at least beta neq 0}
    L = domain(phi)
    pii = uniformizer(L)
    ee = absolute_ramification_index(parent(c))
    if ee * valuation(phi(pii) // pii - c) >= precision(c)
        return pii
    end
    d = Int(absolute_degree(L) // ee)  # InertiaDegree(L);
    # // c := c^(-1); 
    #  // basis := Basis(L) ;
    gamma = 1 + bas[length(bas)]
    A = [gamma, c * phi(gamma)]#@phi];
    for i = 3:d
        push!(A, c * phi(A[i-1]))
    end

    c_frob = sum(A)

    if norm(c_frob) == 0 || ee * valuation(c_frob) >= 1
        gamma = random_elem(L)
        A = [gamma, c * phi(gamma)]
        for i = 3:d
            push!(~A, c * phi(A[i-1]))
        end
        return sum(A)
    else
        return sum(A)
    end
end
function prime_field(L::FlintQadicField)
    base_field(L)
end
function Frobenius_automorphism(L::Union{FlintQadicField, Hecke.LocalField})
    G, mG = automorphism_group(L)
    @assert length(gens(G)) == 1
    return mG(gens(G)[1]), mG(gens(G)[1]^-1)
end

function Frobenius_Equations(C, phi, bas)
    set = elem_type(parent(C[1]))[]
    L = parent(C[1])
    for i = 1:length(C)
        if C[i] == L(1)
            push!(set, L(1))
        else
            c = C[i]^-1
            push!(set, Hilbert_Ninety1(c, phi, bas))
        end
    end
    return set
end
=#
#absolute_inertia_degree(K::QadicField) = degree(K)  # made pull request
function maximal_unramified_subextension(L::Hecke.LocalField)
    n = absolute_degree(L)
    inert_deg = absolute_inertia_degree(L)
    if n == Hecke.absolute_inertia_degree(L)
        return L
    end
    L = base_field(L)
    while !(absolute_degree(L) == Hecke.absolute_inertia_degree(L))
        L = base_field(L)
    end
    if absolute_inertia_degree(L) != inert_deg
        error("extensions not in order")
    end
    return L

end

#=
Given an unramified extension OL2/OL and the Galois group G of OL/Zp
  as well as a map psi_OL_Zp: G -> Aut(OL, Zp).
  Compute a continuation of each automorphism to OL2 and its restriction
  to the unramified subextension of OL2 as a power of the frobenius
  automorphism.
  These continuations are selected in such a way, that the inverse of its
  restriction to the unramified subextension are low powers of the
  frobenius automorphism.
=#

function continuations_with_unram_restriction(OL, G, psi_OL_Zp, OL2)
    OK = maximal_unramified_subextension(OL)
    Qp = Prime_field(OK)
    Zp = (typeof(OK) == FlintPadicField ? OK : Prime_field(OK)) # base_field(OK);
    sigma = [psi_OL_Zp(g) for g in G]
    #=  if typeof(domain(psi_OL_Zp(G.1))) == Hecke.LocalField
           sigma := [map<OL -> OL | x :-> sig(x) > for  sig in sigma];
      end if;=#
    d = degree(OK)
    if d == 1
        frobIndex = [Int(0) for sig in sigma]
        sigmaKnrExponentInv = frobIndex
        # // setze sigma fort mit Identitaet auf unverzweigten Teil
        sigmaHut = []
        for i = 1:length(sigma)
            sig = sigma[i]
            B = gen_local(OL2, OL)
            for r in reverse(B)
                #=function sig_new(x)#::elem_type(parent(r))) 
                    return continued_automorphism_image(x, sig, r)
                end=#
                # sig := map<Parent(r) -> Parent(r) | x:-> continued_automorphism_image(x, sig, r) >;
            	sig_new = map_from_func(x -> continued_automorphism_image(x, sig, r), parent(r), parent(r) )
		        push!(sigmaHut, sig_new)
	        end
            #push!(sigmaHut, sig_new)
        end
    elseif OL == OK
        error("to be implemented")
        #=      // Ausgangssitugation unverzweigt
                                                 
              f := FrobeniusAutomorphism(OK, Zp);
              frobIndex := [find_power(sig, f, OK.1 , InertiaDegree(OK, pAdicRing(OK))) : sig in sigma];
              fInv := inverseAutomorphism(f);
                                                 
              sigmaHut := sigma;
              sigmaKnrExponentInv := [(d-i) mod d : i in frobIndex];
        =#
    else
        f = continue_frobenius(identity_map(Prime_field(OK)), OK, prime(Qp))
        fInv = inverseAutomorphism(f, identity_map(Qp))
        sigmaHut = []
        frobIndex = [find_power(sig, f, gen(OK), d) for sig in sigma]
        f = continue_frobenius(f, OL, prime(Qp))
        fInv = inverseAutomorphism(f, fInv)
        B = reverse(gen_local(OL2, OL))
        fB = []
        for b in B
            f = continue_frobenius(f, parent(b), prime(Zp))
            fInv = inverseAutomorphism(f, fInv)
            seq = [b]
            for i = 1:d-1
                push!(seq, fInv(seq[length(seq)]))
            end
            push!(fB, seq)
        end
        for i = 1:length(sigma)
            sig = sigma[i]
            idx = frobIndex[i]
            # // Liste f^(-idx)(b) fuer die Erzeuger von OL2/OL
            # B = [ seq[((d-idx) mod d) + 1]   for  seq in fB ];
            B = [seq[((d-idx)%d)+1] for seq in fB]
            #// sigma schrittweise fortsetzen
            for r in B
                sig_new = map_from_func(
                    x -> continued_automorphism_image(x, sig, r),
                    parent(r),
                    parent(r),
                ) 
                push!(sigmaHut, sig_new)
            end
        end
        sigmaKnrExponentInv = frobIndex
    end
    return sigmaHut, frobIndex, sigmaKnrExponentInv
end;
