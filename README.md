# DegeneratingVectorBundles
Macaulay2 code to study degenerations of coherent sheaves in toric varieties. 

This code is based on a previous package ([DegenerationsVectorBundles.m2](https://github.com/dmaclagan/ICMS/blob/main/DegenerationsVectorBundles.m2)).

Some contributions made consist in generalizing some of the extisting fuctions to be able to consider not only projective spaces, but more general complete toric varieties.
I have also created new functions, the fundamental one is infoInitialModules that given a module, its Gröbner fan and the irrelevan ideal of the toric variety outputs a list of MutableHashTable 
that contains the intial module at each cone, whether it is a reflexive, torsion-free or locally-free sheaf as well as if it is equivariant or not. 
