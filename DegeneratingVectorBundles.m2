newPackage(
        "DegeneratingVectorBundles",
        Version => "0.1",
        Date => "",
        Headline => "code from 2025 ICMS workshop on degenerating vector bundles",
        Authors => {
    	    { Name => "Kimuli Philly Ivan", Email => "kpikimuli@gmail.com", HomePage => ""},
    	    { Name => "Diane Maclagan", Email => "d.maclagan@warwick.ac.uk", HomePage => ""},
             { Name => "Mayo Mayo Garcia ", Email => "mayo.mayo-garcia@warwick.ac.uk", HomePage => ""},
            { Name => "Andre Mialebama", Email => "sainteudes@gmail.com", HomePage => ""},
            { Name => "Ignatius Philip Ngwongwo", Email => "igphils.7@gmail.com", HomePage => ""},
	    { Name => "Namanya Caroline", Email => "caronamanya97gmail.com", HomePage => ""},
    	    { Name => "Olasupo Felemu", Email => "ofelemu0@gmail.com", HomePage => ""},
    	    { Name => "Jared Ongaro", Email => "ongaro@uonbi.ac.ke", HomePage => "https://profiles.uonbi.ac.ke/ongaro"},	    
   	    { Name => "Gregory Sankaran", Email => "gksankaran@gmail.com", HomePage => "https://people.bath.ac.uk/masgks"}
	    },
        AuxiliaryFiles => false,
        DebuggingMode => false,
        Reload => true
        )
				
export {
    "moduleToIdeal",
    "grobnerFan",
    "initialModule",
    "isEquivariant",
    "latticeInteriorPoint",
    "allFittingIdeals",
    "isVectorBundle",
    "generateHomogeneousModule",
    "infoInitialModules",
    "byCones",
    "raysProperty",
    "listDegenerations",
    "analyzeDegenerations",
    "groupInitialModules",
    "saveDegeneration",
    -- Methods:
    "Mode",
    "VectorBundle",
    "Random",
    "Correction",
    -- Hash Table Keys
    "intPoint",
    "byCardinality",
    "torsionFree",
    "notEquivariants",
    "fittingIdeals",
    "doubleDual",
    "coneId",
    "reflexives",
    "equivb",
    "isTorsionFree",
    "raysProperties",
    "modulesList",
    "vectorBundles",
    "modules",
    "discrepancy",
    "equivariants"
}

exportFrom("Polyhedra","maxCones")

-* Code section *-


needsPackage "gfanInterface";
needsPackage "Polyhedra";
needsPackage "MinimalPrimes";
needsPackage "WeilDivisors";   


-- Aditional exports
--export {"allFittingIdeals", "groupInitialModules", "raysProperty", "byCones", "latticeInteriorPoint"};


--take a submodule of a free module oplus S e_i and return an ideal in the polynomial
--ring S[e_i]

moduleToIdeal = M ->(
    S := ring M;
--    myChar := char S;                                                                      
    E := {};
    G := {};
    m := rank ambient M;
    shifts := degrees ambient M;
    s := #(entries vars(S))_0;
    degs := apply(degrees(S) ,i->(append(i,0))) | apply(shifts,i->(append(i,1))); -- Makes sure the degrees are correct and the output ideal is homogeneous
    k := s+m;
    e := symbol e;
    S2 :=QQ[e_1..e_m];
     R :=QQ[gens(S)|gens(S2), Degrees => degs]; 
    L := entries transpose gens M;
    for i from 0 to #L-1 do (
         U := L_i;
         for j from 0 to #U-1 do (
             E = E|{sub(U_j,R)*R_(s+j)};
         );
         g := sum(E);
         G = G|{g};
         E := {};
     );
     I := ideal(G);
     return I;
);



--Code to compute the Grobner fan of M

grobnerFan = M ->(
    S := ring M;
    l := numgens(S);
    ---Turn M into an ideal                                                                    
    I := moduleToIdeal(M);
    R := ring I;
    m := rank ambient M;
    k := numgens(R);
--    assert(k == l+m);
    G := gfan(I);
    --Turn into initial ideal                                                                    
    L := apply(G,i->gfanLeadingTerms(i));
--<<L<<endl;
--<<#L<<endl;    
    q := apply(L, monoIdeal-> (
--<<monoIdeal<<endl;	    
	    ideal select(monoIdeal,j->(
		    t := (exponents(j))_0;
--		    p := toList{t_l..t_(k-1)}_0; 
--<<p<<endl;		    
		    sum(k-l,i->t_(i+l))==1
	    ))
    ));
--<<q<<endl;
    --Combine initial ideals with the same e-linear part
    alreadyDone := {};
    coneToCombine:={};
    for i from 0 to #q-1 do
    (
  	if not isMember(i,alreadyDone) then (
     	tt := q_i;
     	alreadyDone = alreadyDone|positions(q,j->j==tt);
     	coneToCombine = coneToCombine|{positions(q,j->j==tt)};
        )
    );
--<<coneToCombine<<endl;
    combinedCones := apply(coneToCombine,element-> (
      Now := apply(element, i-> (
      	      conei := gfanGroebnerCone(G_i);
               coneFromVData((-1)*rays conei, linealitySpace conei)
	      ));
--<<Now<<endl;      
      c := first Now;
      for i from 1 to #Now-1 do
      (
   	c = minkowskiSum(c,Now_i);
      );
      c
    ));
    --Create fan
    F := fan first combinedCones;
    for i from 1 to #combinedCones-1 do (
   	F = addCone(combinedCones_i,F);
    );
    return F;
);




--compute in_{w,s}(M)
--We'll assume that M is homogeneous with respect to standard grading
initialModule = method(Options => {Correction =>{}});

initialModule (Module, List, List):= opts -> (M,w,s)->(
    n:=numgens ring M;
    I:=moduleToIdeal(M);
    degs := degrees ring I;
    SI:=ring I;
    m:=numgens SI - n;
    KI:=coefficientRing SI;
    gensSI := gens SI;
    newW := apply(w,i->-i) | apply(s,i->-i);
    maxWS:=max(w|s);
    if opts#Correction === {} then(
      vec := apply( degs, n-> sum n);
      vec =  vec +(1- min(vec))*splice{n:0, m:1}; 
      if min(vec) <0 and min(newW) < 0 then error "The computation is not feasible. Give a correction vector, please";
      newW = newW + splice{n+m: maxWS };
      if maxWS < 0 then(newW = newW  + maxWS*vec;)
      else(
      -- Check if the all ones vector is in the lineality space of the Grobner fan of M and if it is not we compute a new weight vector  
      if matrix splice{n+m:{1}} %  matrix degs != 0 then(
          newW = newW + splice{n+m:-maxWS } + maxWS*vec;   
      ););
    )
    else(
      newW = newW + (maxWS+1)*opts#Correction;

    );

    degsS:=apply(n,i->({1,0})) | apply(m,i->({0,1}));
    newS := KI[gensSI,Weights=>newW,Degrees=>degsS];
    newI:=sub(I,newS);
    inI:= leadTerm(1,newI); 
    linearGens:= select(flatten entries gens inI,f->((degree(f))_1 ==1));
    moduleGens:=apply(linearGens, g->(
	    C:=coefficients g;
	    apply(m,j->(
		    p:=positions(flatten entries (C_0), i->(first exponents( i))_(n+j)==1);
		    sum(p,l->(sub((flatten entries (C_0))_l,SI_(n+j)=>1)*(flatten entries (C_1))_l))
	    ))
    ));
    image mingens image map(ambient M, , transpose sub(matrix moduleGens,ring M))
)





--Decide whether in_{w,s}(M) is homogeneous with respect to the Z^n grading by deg(x_i)=e_i
--Input: cone sigma from the Grobner fan of M, given as a matrix of rays, n=number of gens
-- of ambient polynomial ring (so we are considering vector bundles on P^{n-1}
isEquivariant = (sigma,n) ->(
    nset:=apply(n,i->i);
    dimsigma:=rank sigma^nset;
    if dimsigma==n then true else false
)


-- Compute the lattice point in the interior of a cone given by its rays, this is used to compute the initial module corresponding to a cone in the Grobner fan
latticeInteriorPoint=(P) ->(
    rp:= rays P;
    l:= entries transpose rp;
    n:=length l;
    C:= toList (rank target rp:0);
    for i from 0 to n-1 do(C=C+l_i);--);
    C= apply(C,c-> truncate (c));-- the solution I found to turn integers in QQ into ZZ
    return C;
)


-- It takes the presentation of the module ie gens image A and returns the list of all fitting ideals
allFittingIdeals = (M) ->(
    m:=rank ambient M;
    C:={};
    for i from 0 to m+2 do(
        I1:= fittingIdeal(i-1,M); 
        C= append(C, I1);
    );
    return C;
)  

-- Check whether the sheafification of the cokernel of A is a vector bundle on a toric variety
-- Input: A matrix A, list L of fitting ideals of A, and I the irrelevant ideal of the toric variety
-- There are two methods: one computes the radical and the other computes the saturation,
--the second one is more expensive but it works in some of the cases where the first one aborts.

isVectorBundle = method(Options => {Mode => "radical"});


isVectorBundle(Module, Ideal) := opts -> (M, I) ->(

    m:= rank ambient M;
    Im := fittingIdeal(0, M);
    I1 := ideal(1_(ring I));
    I0 := ideal(0_(ring I));
    if opts#Mode === "radical" then(
    for i from 1 to m+1 do(
        IM := fittingIdeal(i, M);
        if (Im == I0) then(
            if isSubset(I, radical IM) then(
                return {true, i};
                exit;
            )
        );    
        Im = IM;
    
    );
    return false;
    )
    else(
            for i from 1 to m+1 do(
        IM := fittingIdeal(i, M);
        if (Im == I0) then(
            if saturate(IM,I)== I1 then(
                return {true, i};
                exit;
            )
        );    
        Im = IM;
    
    );
    return false;
    );
)

isVectorBundle (Module, Ideal, ZZ) :=  opts -> (M, I, r) ->(
    p:= false; 
    if opts#Mode === "radical" then(
    p = (isSubset(I, radical fittingIdeal(r, M))) and (fittingIdeal(r-1, M)== ideal(0_(ring I) ));)
    else(
    p = (saturate( fittingIdeal(r, M)),I)== ideal(1_(ring I)) and (fittingIdeal(r-1, M)== ideal(0_(ring I) ));
    );
    return p;
)




-- Input: S is the Cox ring of a toric variety and gives a matrix with l rows of homogeneous entries of multidegree d in oplus S(-shifts_i) for i=1,...,m, where shifts is a list of m elements, and returns the image of the corresponding map from oplus S(-shifts_i) to oplus S(-d)


generateHomogeneousModule  = method(Options => {Mode => "module", Random => 0});

generateHomogeneousModule( Ring, List, ZZ, List) := opts ->(S,shifts, l, d) -> (
    M :={};
    sh := -shifts;
    D :=splice{l:-d};
    if opts#Random == 0 then(
        for i from 0 to #sh-1 do(
        M = M|{for j from 0 to l-1 list sum randomSubset(terms random(d + sh_i,S))};
    );
    )else( if opts#Random != 0 then(
            for i from 0 to #sh-1 do(
        M = M|{for j from 0 to l-1 list sum randomSubset(terms random(d + sh_i,S),opts#Random)};
    ))else(
    for i from 0 to #sh-1 do(
        M = M|{for j from 0 to l-1 list random(d + sh_i,S)};
    );););
    M= map(S^sh, S^D, matrix M);
    if opts#Mode === "module" then(
    M= image M ;);
    return M
);








-- Input: the module M, the Grobner fan F, and the irrelevant ideal of the toric variety I

infoInitialModules = method(Options => {Mode => "radical", VectorBundle => "true", Correction =>{}});


infoInitialModules(Module, Fan, Ideal) := opts ->(M,F,I)-> (
    
    if isHomogeneous M == false then error "The module is not homogeneous";
    n := numgens(ring M);
    m := rank (ambient M);
    S := ring M;
    Lh :={};
    rs:= rays F;
    r := isVectorBundle(coker gens M,I, Mode => opts#Mode);
    -- Obtains a list of hash tables with the cone point and module
    for i from dim(source linealitySpace(F)) to dim(F) do(
        lr:= apply(cones(i,F), c -> (H:= new MutableHashTable; H#cone = rs_c; H#coneId =c ;H));
        Lh = join(Lh, apply(lr, h -> (h#intPoint = latticeInteriorPoint( polyhedron posHull(h#cone));
        h#module = initialModule(M, take(h#intPoint,{0,n-1}), take(h#intPoint,{n,n+m-1}) ,Correction => opts#Correction) ;
        h#quotient = (coker gens h#module) ;  h)));
        );
    -- If the module is not a vector bundle none of its degenerations will be
    -- and if it is a vector bundle all of the degenerations that are vector bundles have the same rank
    if opts#VectorBundle === "all" then(
      Lh = apply (Lh, h->(h#isVectorBundle= isVectorBundle(h#quotient, I, Mode => opts#Mode);h));
    );
    if opts#VectorBundle === "true" then(
    if r === false then(
        Lh = apply (Lh, h-> (h#isVectorBundle= false; h));
    )
    else(
        r= r_1;
        Lh = apply (Lh, h->(h#isVectorBundle= isVectorBundle(h#quotient, I, r, Mode => opts#Mode);h));
    ););
    Lh = apply (Lh, h->(h#doubleDual = reflexify(h#quotient, ReturnMap => true);h));
    -- Check that the torsion submodule is supported on the irrelevant ideal
    Lh = apply (Lh, h->(h#isTorsionFree = isSubset(I, radical annihilator ker h#doubleDual) ;h)); 
    
    Lh = apply (Lh, p->( p#isEquivariant= isEquivariant((p#cone|(linealitySpace(F)|(-1)*linealitySpace(F))) , n); p ) );
    Lh = apply (Lh, h->(h#isReflexive = isSubset(I, radical annihilator coker h#doubleDual) and h#isTorsionFree == true; h)); 
    Lh= prepend(F,Lh);
    return Lh;

)

-- This version only computes the degeneraion and if they are equivariant
infoInitialModules(Module, Fan) := opts ->(M,F)-> (
    if isHomogeneous M == false then error "The module is not homogeneous";
    n := numgens(ring M);
    m := rank (ambient M);
    S := ring M;
    Lh :={};
    rs:= rays F;
    -- Obtains a list of hash tables with the cone point and module
    for i from dim(source linealitySpace(F)) to dim(F) do(
        lr:= apply(cones(i,F), c -> (H:= new MutableHashTable; H#cone= rs_c; H#coneId =c ;H));
        Lh = join(Lh, apply(lr, h -> (h#intPoint = latticeInteriorPoint( polyhedron posHull(h#cone)); h#module = initialModule(M, take(h#intPoint,{0,n-1}), take(h#intPoint,{n,n+m-1}) ,Correction => opts#Correction) ; h#quotient = (coker gens h#module) ;  h)));
    );
    Lh = apply (Lh, h->(h#doubleDual = reflexify(h#quotient, ReturnMap => true);h));    
    Lh = apply (Lh, p->( p#isEquivariant= isEquivariant((p#cone|(linealitySpace(F)|(-1)*linealitySpace(F))) , n); p ) );
    Lh= prepend(F,Lh);
    return Lh;
)




-- Analyze the list of initial modules
-- Auxiliary function to display the information by cones of the same dimension
byCones = (LL)->(tally (apply(LL, p -> #(p#coneId)) ) )

-- Takes the list of hash tables LL and the fan F and checks whether the property is hereditary on the faces of a cone
-- that is, it checks if the cones where are property holds can form a subfan 
raysProperty = (LL)->(
  if LL == {} then return "no info" else(
    allcones :=apply(LL, p ->set p#coneId);
    inter :=  {};
    for i from 0 to #allcones-1 do(
      inter = flatten append (inter, subsets(allcones_i));
      for j from 0 to #allcones-1 do(
      inter = flatten append(inter, intersect(allcones_i, allcones_j));
      );
    );
    set allcones == set inter
    )
)

-- Takes the output of infoInitialModules and gives a summary of the properties of the degenerations selecting the modules with each property
listDegenerations = (L)->(
    A := new MutableHashTable;
    A#fan = L_0;
    A#modules = delete(L_0,L);
    A#modulesList = apply(A#modules, p -> p#module); 
    if member( isTorsionFree, keys A#modules_0) then(
    if member( isVectorBundle, keys A#modules_0) then(
    A#vectorBundles = select( A#modules, p -> p#isVectorBundle =!= false and p#isVectorBundle =!= "no info");)
    A#notVectorBundles = select( A#modules, p -> p#isVectorBundle === false);)
    else( A#vectorBundles ={};);
    A#torsionFree = select( A#modules, p -> p#isTorsionFree == true);
    A#reflexives= select( A#modules, p -> p#isReflexive == true);
    A#equivb = select( A#modules, p -> p#isEquivariant == true and p#isVectorBundle =!= false););
    A#equivariants = select( A#modules, p -> p#isEquivariant == true);
    A#notEquivariants = select( A#modules, p -> p#isEquivariant == false);
    return A;
)



-- Takes the output of listDegenerations and checks that the code is working properly and gives a summary of properties
analyzeDegenerations = (B)->(
    A := new MutableHashTable;
    A#discrepancy = rank linealitySpace( B#fan);
    if member( isTorsionFree, keys B#modules_0) then(
    A#byCardinality = { "total:",   #B#modules, "vectorbundles:", #B#vectorBundles ," reflexives:", #B#reflexives ,"torsion free:", #B#torsionFree,"equivariants:", #B#equivariants, "equivariant vector bundles:", #B#equivb };
    A#raysProperties = { "vectorbundles:", raysProperty(B#vectorBundles), " reflexives:", raysProperty(B#reflexives), "torsion free:", raysProperty(B#torsionFree),  "equivariant vector bundles:", raysProperty(B#equivb), "equivariants:", raysProperty(B#equivariants), "not equivariants:", raysProperty(B#notEquivariants) };
    A#byCones = {"total:", byCones(B#modules ), "vectorbundles:", byCones(B#vectorBundles),  "equivariants:", byCones(B#equivariants), "equivariant vector bundles:", byCones(B#equivb) };)
    else(
    A#byCardinality = { "total:",   #B#modules, "equivariants:", #B#equivariants };
    A#byCones = { "total:", byCones(B#modules ), "equivariants:", byCones(B#equivariants) };
    A#raysProperties = { "equivariants:", raysProperty(B#equivariants), "not equivariants:", raysProperty(B#notEquivariants) }
    );
    return A;
)


-- L=infoInitialModules(M) removind the fan L_0 and grouping by fitting ideals at index i
groupInitialModules = (L,i) ->(
    
    C:={};
    while L =!= {}  do (
        el:= ((first L)#fittingIdeals)_i;
        Lel:= select(L,p -> p#fittingIdeals_i == el);
        C =append(C,  Lel);
        L= select(L,p -> p#fittingIdeals_i != el););
    
    return C;
)

-- Function to save the output of infoInitialModules or the GrobnerFan in a file with descpition text 
-- NOTE: name should be "name.m2" for a m2 file as "name" just gives a .txt file
saveDegeneration = method(Options => {Mode => "none"});

saveDegeneration(List,Ideal, String, String) := opts ->(L, I, text, name)->(
    pre:=concatenate{"-- ", text, "\n S=", toExternalString ring (L_1)#module,  "\n I=",  toString I, "\n M=",  toString (L_1)#module };
    s:= " ";
    l:= " ";
    -- Creates the list of mutable hashtables
    for i from 1 to #L-1 do(
    s= concatenate{s,"L", toString i, "= new MutableHashTable;"  } ;
    );
    K:=keys(L_1);

    -- Fills in the hashtables
    for j from 0 to #K-1 do(
        kj := toString K_j;
        if kj != "doubleDual" then(  
        for i from 1 to #L-1 do(
            s=concatenate{s, "L", toString i, "#",kj,"=", toString (L_i)#(K_j), ";"  } ;
        ););
        s=concatenate{s, "\n"};
    );
    
    -- Creates the list of mutable hashtables
    for i from 1 to #L-1 do(
    l= concatenate{l,"L", toString i,  };
    if i<#L-1 then( l=concatenate{l, ","} );
    );


    c:=concatenate{"F = fan (",toExternalString (rays L_0) ,",", toExternalString (linealitySpace L_0) ,",", toExternalString(maxCones L_0), ");"};

    l= concatenate{"\n L={F,",l, " };" };
    s= concatenate{pre, s,c, l };

    name << s <<close

)

saveDegeneration(Fan, String, String) := opts ->(F,text, name)->(
    pre:=concatenate{"-- ", text, "\n "};
    s:= " ";
    c:=concatenate{"F = fan (",toExternalString (rays F) ,",", toExternalString (linealitySpace F) ,",", toExternalString(maxCones F), ");"};
    s= concatenate{pre, c };
    name << s <<close
)



    
-* Documentation section *-
beginDocumentation()

doc ///
Key
  DegeneratingVectorBundles
Headline
  a package containing the code written at the ICMS workshop in May 2025
Description
  Text 
     This is the code we wrote at ICMS
Acknowledgement
Contributors
References
Caveat
SeeAlso
Subnodes
///

       
       
doc ///
       Key
        grobnerFan
    Headline
      compute the Grobner fan of a module 
    Usage
        grobnerfan(M)
    Inputs
       M : Module 
   Outputs
       G: Fan
  Description
      Text
        This function takes a module M and produces the Grobner fan of
        it.  If M is a submodule of S^m, where S is a polynomial ring
        with n variables, then this a subfan of R^n times R^m, with (w,s), (w',s') in the same cone of the fan if in_(w,s)(M) = in_(w',s')(M).
	The output is a fan in the sense of the Polyhedra package.
      Example
        R=QQ[x,y];
	M=image generateHomogeneousMatrix(2,3,2,2);
	F=grobnerFan M;
	rays F
	maxCones F
///

doc ///
   Key 
      moduleToIdeal 
   Headline 
      turns a submodule of a free module S^r into an ideal in S[e_1..e_r] 
   Usage 
      moduleToIdeal M 
   Inputs 
      M: Module
   Outputs 
      I: Ideal
   Description 
	Text 
           Takes a submodule of a free module oplus S e_i and returns an ideal in the polynomial ring S[e_i]. 
           The output is a graded ideal where Deg(x_i)=(deg(x_i),0) and Deg(e_i)=(deg(e_i),1) where deg(e_i) 
           is the degree of the i-th basis vector of the ambient free module.
	Example
	   S=QQ[x,y, Degrees => {{3},{4}}];
	   M=image(map(S^{{-1},{0},{0}}, S^{{-2},{-2}}, matrix {{x,y},{x^2,-y^2},{x*y,x^2+y^2}}))
	   moduleToIdeal M
///


doc ///
   Key 
      initialModule
   Headline 
      computes the initial module of a module with respect to weight vectors
   Usage 
      initialModule(M,w,s)
   Inputs 
      M: Module
      w: List
      s: List
   Outputs 
      in_(w,s)(M) : Module
   Description 
	Text 
          Takes a submodule of a free module oplus S e_i and returns the
          initial module in_(w,s)(M), where w are the weights on the
	  variables of the ring, and s are the weights on the basis
	  vectors e_i.  The initial module is taken with respect to the
	  min convention, so the initial term of an elemnt is the sum of
	  the terms of lowest weight.  There is an unchecked assumption that the module is homogeneous.
	Example
	   S=QQ[x,y];
	   M=image matrix {{x^2-y^2},{y^2}};
	   initialModule(M,{0,1},{0,1})
   	   initialModule(M,{0,-1},{1,1})
	   initialModule(M,{0,0},{0,1})
///



doc ///
   Key 
      isEquivariant
   Headline 
      determines whether the initial module corresponding a cone of the Grobner fan is equivariant (Z^n graded).
   Usage 
      isEquivariant(sigma,n)
   Inputs 
      sigma:Matrix
      n:ZZ
   Outputs 
      :Boolean
   Description 
	Text 
	  This function takes as input a matrix whose rays span a
	  Grobner cone for the matrix M, and the number n of
	  variables.  The output is true if the projection of the cone
	  to the first n coordinates is full-dimensional (so the
	  corresponding initial module is homogeneous with respect to
	  a Z^n grading).  When using the output of the grobnerFan
	  command one must include the lineality space of the cone.
	Example
	   S=QQ[x,y];
	   M=image matrix {{x^2-y^2},{y^2}};
	   F=grobnerFan M;
	   L = linealitySpace F;
	   C = cones(3,F);
	   R = rays F;
	   isEquivariant(L| (matrix R_0),2)
///

-- MODIFY 				  

doc ///
    Key			      
      isVectorBundle
      (isVectorBundle, Module, Ideal)
      (isVectorBundle, Module, Ideal, ZZ)
      [isVectorBundle, Mode]
    Headline
      decides whether the sheafification of the cokernel of a matrix is a vector bundle of rank r
    Usage
       isVectorBundle(M,I)
       isVectorBundle(M,I,r)
       isVectorBundle(Module, Ideal, ZZ, Mode => "radical")
       isVectorBundle(Module, Ideal, ZZ, Mode => "saturation") 
    Outputs
      B:Boolean
    Inputs
      M:Module
      I:Ideal
      r:ZZ
      Mode => String
        specifies if the functions takes the radical or the saturation 
    Description
        Text
          This function determines whether the sheafification of the cokernel of a matrix A over a polynomial ring is a vector bundle of rank
          r on the corresponding toric variety with irrelevant ideal I.  The output is true if so.
        Example
          S = QQ[x_0,x_1];
          I = ideal( x_0,x_1);
          B = matrix{{x_0^4-x_1^4, x_0^2*x_1^2+4*x_0^4, x_0^3*x_1-14*x_1^4},{x_1, x_0, x_0},{x_0^2-x_1^2, x_0*x_1+4*x_0^2, x_0*x_1+4*x_1^2}};
          M = image map(S^{0,-1,-2}, S^{-3,-3,-3}, B);
          N = coker map(S^{0,-1,-2}, S^{-3,-3,-3}, B);
          isVectorBundle(M,I)
          isVectorBundle(N,I)
///




doc ///
  Key
    infoInitialModules
    (infoInitialModules, Module, Fan, Ideal)
    (infoInitialModules, Module, Fan)
    [infoInitialModules, Mode]
    [infoInitialModules, VectorBundle]
  Headline
    gives a list of hash tables with the information about the degenerations corresponding to the cones in the Grobner fan of a module
  Usage
    L = infoInitialModules(M, F, I)
    L = infoInitialModules(M, F)
  Inputs
    M:Module
    F:Fan
      grobnerFan(M)
    I:Ideal
      irrelevant ideal of the toric variety
    Mode => String
      specifies the mode passed to isVectorBundle (radical or saturation). 
    VectorBundle => String
      specifies if the key isVectorBundle is computed or not. 
  Outputs
    L:List
  Description
    Text
      The function takes an homogeneous submodule M of a free module oplus S e_i, where S is a graded module (the Cox ring of a toric varietay), the Grobner fan F of M, and the irrelevant ideal I of the toric variety. The output is a list of hash tables with the information about the degenerations corresponding to the cones in the Grobner fan of M. 
      The degeneration considered in each cone is the quotient of the initial module of each cone, that is, this function studies degenerations on S^m/M. The list contains as its first element the Grobner fan F of the module and the remaining elements are hash tables, one for each cone in F. The keys of these tables store information such as whether the degeneration is a vector bundle, torsion-free, reflexive or equivariant.  It also stores the infomation about the cone, the point used to compute the initial module and the corresponding initial module.
      Whent the irrelevant ideal is not given, the function only computes the initial modules and whether they are equivariant or not.
      WARNING: for some examples the computation of the radical of the fitting ideals or the saturation with respect to I can abbort, use VectorBundle => "false" to skip this computation.
    Example
      S= QQ[x,y,z,Degrees => {{2},{1},{2}}];
      I= ideal(x,y,z);
      M= image map(S^{{-4}, {0}}, S^{{-6}}, matrix {{y^2+z}, {x^3+ y^6}});
      F= grobnerFan M
      L= infoInitialModules(M,F, I);
      peek L_3
///


doc ///
  Key
    generateHomogeneousModule
    (generateHomogeneousModule, Ring, List, ZZ, List)
    [generateHomogeneousModule, Mode]
    [generateHomogeneousModule, Random]
  Headline
    generates a homogeneous module with given shifts and degree
  Usage
    M = generateHomogeneousModule(S, shifts, l, d)
  Inputs
    S:Ring
      graded ring
    shifts:List
      defines oplus S(-shifts_i)
    l:ZZ
      number of rows of the matrix
    d:List
      degree
    Mode => String
      specifies if the output is a "module" or a "matrix"
    Random => ZZ
      bounds the support of the polynomials: 0 gives the random (usually full) support, and n gives a random support of size n
  Outputs
    M:Module
  Description
    Text
      This function is a source of examples for the package.
    Example
      S = QQ[x, y, z, Degrees => {{1,0}, {1,0}, {0,1}}];
      shifts = {{1, 2},{3,0}};
      d = {4,3};
      M = generateHomogeneousModule(S, shifts, 3, d, Random => 4)
///

doc ///
  Key
    listDegenerations
  Headline
    creates a hash table with the list of degenerations given their properties
  Usage
    A = listDegenerations(L)
  Inputs
    L:List
      the output of infoInitialModules
  Outputs
    A:HashTable
  Description
    Text
      This function takes the output of infoInitialModules and creates a hash table with the list of degenerations given their properties, such as whether they are vector bundles, torsion-free, reflexive, equivariant, non-equivariant and the equivariant vector bundles.  It also includes the fan and the list of modules.
    Example
      S= QQ[x,y,z,Degrees => {{2},{1},{2}}];
      I= ideal(x,y,z);
      M= image map(S^{{-4}, {0}}, S^{{-6}}, matrix {{y^2+z}, {x^3+ y^6}});
      F= grobnerFan M
      L= infoInitialModules(M,F, I);
      LA = listDegenerations(L);
      peek LA
///

doc ///
  Key
    analyzeDegenerations
  Headline
    gives a summary of the properties of the degenerations
  Usage
    A = analyzeDegenerations(B)
  Inputs
    B:HashTable
      the output of listDegenerations
  Outputs
    A:HashTable
  Description
    Text
      The function takes the output of listDegenerations and gives a summary of the properties of the degenerations, how many cones are there of each dimension, the number of cones such that the associated degeneration satisfies a given property, and  whether the the cones with a particular property form a subfan.
    Example
      S= QQ[x,y,z,Degrees => {{2},{1},{2}}];
      I= ideal(x,y,z);
      M= image map(S^{{-4}, {0}}, S^{{-6}}, matrix {{y^2+z}, {x^3+ y^6}});
      F= grobnerFan M
      L= infoInitialModules(M,F, I);
      LA = listDegenerations(L);
      LB = analyzeDegenerations(LA);
      peek LB
///




doc ///
  Key
    saveDegeneration
    (saveDegeneration, List, Ideal, String, String)
    (saveDegeneration, Fan, String, String)
    [saveDegeneration, Mode]
  Headline
    saves the output of infoInitialModules or the GrobnerFan in a file with descpition text 
  Usage
    saveDegeneration(L, I, text, name)
    saveDegeneration(F, text, name)
  Inputs
    L:List
      output of infoInitialModules
    I:Ideal
      irrelevant ideal of the toric variety
    text:String
      description of the file
    name:String
      name of the file
    F:Fan
      output of grobnerFan
  Description
    Text
      This function takes the output of infoInitialModules and saves it in a file with the given name and description.  If the file name is "name.m2" it can be loaded to recover the list of hash tables with the information about the degenerations. However, if the user wants the modules to be defined over the same ring, the file needs to be edited beforehand.
      The function also works for saving the output of grobnerFan, in this case the input is just the fan and the description and name of the file.
///

       
-* Test section *-

TEST ///
  -- Test 1: Check that moduleToIdeal correctly builds an ideal and extends the ring
  S = QQ[x, y];
  M = image matrix {{x, y}, {x^2, y^2}};
  I = moduleToIdeal(M);
  
  -- The output must be an ideal
  assert(instance(I, Ideal));
  
  -- The new ring should have vars from S (2) + vars for the rank of M (2) = 4 total vars
  assert(numgens ring I == 4);
///

TEST ///
  -- Test 2: Chaeck that grobnerFan computes the cones correctly
  S = QQ[x, y];
  M = image matrix {{x^2+y^2, x^2}, {x^2-y^2, y^2}}
  F = grobnerFan(M);
  
  -- The output must be a fan
  assert(instance(F, Fan));
  
  -- The fan has 6 cones of dimension 4
  assert(# cones(4,F)== 6);
///


TEST ///
  -- Test 3: Check for isVectorBundle
  S = QQ[x, y];
  I = ideal(x, y);
  M = coker matrix {{(7/5)*x^3+9*x*y^2}, {4*x^3+10*y^3},{(5/8)*x^3+(8/9)*x^2*y+(1/3)*x*y^2}};
  
  assert(isVectorBundle(M, I)_1 == true);
  
  assert(isVectorBundle(M, I, 2) == true);
  
///
end