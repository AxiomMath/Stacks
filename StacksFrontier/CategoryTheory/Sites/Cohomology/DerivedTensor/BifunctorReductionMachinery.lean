module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.TotalComplexDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.LeftFactorTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.RightFactorTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.TensorIsTriangulated

/-!
# Problem Description

This is Lemma 21.17.1 of the Stacks Project (tag 06YM), in the chapter
"Cohomology on Sites", Section 21.17 "Flat resolutions".

Throughout, `(C, O)` is a ringed site, i.e. a site `C` equipped with a sheaf of
rings `O`.  Let `Mod(O)` denote the (abelian) category of sheaves of `O`-modules
on `C`.  This is an additive category with countable direct sums.

**Definition 1 (Tensor product of `O`-modules).**
For two `O`-modules `F` and `G`, their tensor product `F ⊗_O G` is the
sheafification of the presheaf `U ↦ F(U) ⊗_{O(U)} G(U)`.  This gives a functor
`⊗_O : Mod(O) × Mod(O) → Mod(O)` which is additive (bilinear on morphisms) in
each variable.

**Definition 2 (Complexes and the homotopy category).**
`Comp(Mod(O))` is the category of cochain complexes of `O`-modules with
differential of degree `+1`.  The shift `F^•[1]` has `(F^•[1])^n = F^{n+1}` and
differential `-d_F`.  The homotopy category `K(Mod(O))` has complexes as objects
and homotopy classes of chain maps as morphisms; it is triangulated, the
distinguished triangles being those isomorphic to the standard triangles
`A^• → B^• → C(f)^• → A^•[1]` coming from cones of chain maps.

**Definition 3 (Tensor product of complexes; the double complex).**
Given complexes `F^•`, `G^•`, the termwise tensor product is the double complex
`(F^• ⊗_O G^•)^{p,q} = F^p ⊗_O G^q`, with horizontal differential
`d_1 = d_F ⊗ id` and vertical differential `d_2 = (-1)^p · id ⊗ d_G` (Koszul
sign convention).

**Definition 4 (Total complex).**
`Tot(A^{•,•})^n = ⊕_{p+q=n} A^{p,q}`, with differential `d_1 + d_2` on the
`(p,q)` summand.  In particular `Tot(F^• ⊗_O G^•)` is the usual total tensor
product complex.

**Definition 5 (Exact / triangulated functor).**
An exact functor of triangulated categories `D → D'` is a pair `(F, ξ)` with `F`
an *additive* functor and `ξ_X : F(X[1]) → F(X)[1]` a functorial isomorphism,
such that for every distinguished triangle `(X, Y, Z, f, g, h)` of `D`, the
triangle `(F X, F Y, F Z, F f, F g, ξ_X ∘ F h)` is distinguished in `D'`.

## Main Statements

Fix a complex `G^•` of `O`-modules.

* **Statement 1.** `F^• ↦ Tot(G^• ⊗_O F^•)` (fixed complex is the LEFT factor),
  together with a suitable functorial isomorphism
  `ξ : Tot(G^• ⊗_O F^•[1]) ≅ Tot(G^• ⊗_O F^•)[1]`, is an exact functor of
  triangulated categories on `K(Mod(O))`.
* **Statement 2.** `F^• ↦ Tot(F^• ⊗_O G^•)` (fixed complex is the RIGHT factor),
  together with `ξ : Tot(F^•[1] ⊗_O G^•) ≅ Tot(F^• ⊗_O G^•)[1]`, is an exact
  functor of triangulated categories on `K(Mod(O))`.

Concretely each functor: (1) is well defined on `K(Mod(O))` (sends homotopic
maps to homotopic maps); (2) is additive and commutes with the shift up to `ξ`;
(3) sends distinguished triangles to distinguished triangles.

The Stacks proof reduces both to Derived Categories, Remark 13.10.9 (tag 0G6E),
applied to the bilinear functor `⊗_O`: for additive categories `A, B, C` with
`C` having countable direct sums and any functor `⊗ : A × B → C` bilinear on
morphisms, fixing one complex variable and taking `Tot` of the resulting double
complex yields an exact functor of homotopy categories.

"Exact functor of triangulated categories" (Definition 5) means a triangulated
functor (Definition 13.3.3 / tag 014V), NOT an exact functor of abelian
categories.  The functorial isomorphism `ξ` involves Koszul signs (Homology,
Remark 12.18.5 / tag 0FLG).

## Notes on the formalization

* `Mod(O)` is modelled by `SheafOfModules R` where the sheaf of rings `R` is the
  `Sheaf J RingCat` obtained from a sheaf of *commutative* rings
  `O : Sheaf J CommRingCat` (commutativity is what makes the tensor product an
  `O`-module again).  Mathlib provides the monoidal (in fact symmetric monoidal)
  structure on `PresheafOfModules` over a presheaf of commutative rings, but not
  yet on `SheafOfModules`; accordingly the *actual* tensor product `⊗_O` is built
  here (`sheafTensor`) as: forget to presheaves of modules, take the presheaf
  tensor product `MonoidalCategory.curriedTensor`, and sheafify
  (`PresheafOfModules.sheafification`).  This is exactly "sheafification of
  `U ↦ F(U) ⊗_{O(U)} G(U)`" of Definition 1.

* `Tot(- ⊗_O -)` on cochain complexes is `Functor.map₂HomologicalComplexReg` (Mathlib's
  `Functor.map₂HomologicalComplex` with regular kernel reducibility hints) applied
  to `sheafTensor`: its value on `(K₁^•, K₂^•)` is the total complex of the
  double complex `(p, q) ↦ K₁^p ⊗_O K₂^q`, built with the Koszul sign convention
  (Definitions 3 and 4).

* "Exact functor of triangulated categories" (Definition 5) is
  `Functor.IsTriangulated`, defined relative to a chosen `Functor.CommShift ℤ`
  structure -- this `CommShift` datum is precisely the functorial isomorphism `ξ`
  commuting the functor with the shift.  A `Functor.IsTriangulated` functor is
  automatically `Functor.Additive`; we nevertheless record `Φ.Additive`
  explicitly in the conclusions to match Definition 5.

* The two additivity facts about `sheafTensor` (additive, i.e. bilinear on
  morphisms, in each variable) and the existence of the total complexes are
  proved here, not assumed: `presheafOfModules_monoidalPreadditive` supplies the
  `MonoidalPreadditive` structure on `PresheafOfModules` that Mathlib does not
  state, `sheafifyMod_additive` makes sheafification additive, and
  `sheafTensor_additive`, `sheafTensor_obj_additive` and
  `hasMapBifunctor_sheafTensor` follow.  So Statements 1 and 2 assume nothing
  about `⊗_O` beyond the ringed site itself.

* We also state the underlying general reduction (tag 0G6E) as
  `bifunctor_homotopy_isTriangulated`, for an arbitrary additive bifunctor.

## Parts

The declarations live in the following parts, under this module:

* `BifunctorReductionMachinery.TotalComplexDescent`: the tensor complex, additivity, and the descent
  `bifunctorPhi` with the cochain transport `Ψcoch`.
* `BifunctorReductionMachinery.LeftFactorTriangulated`: `bifunctorPhi_isTriangulated`.
* `BifunctorReductionMachinery.RightFactorTriangulated`:
  `bifunctorPhiR` and `bifunctorPhiR_isTriangulated`.
* `BifunctorReductionMachinery.TensorIsTriangulated`: `statement1`, `statement2`,
  `bifunctor_homotopy_isTriangulated` and `bifunctor_homotopy_flip_isTriangulated`.
-/
