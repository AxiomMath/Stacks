module

public import Mathlib
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of chapter 13 (Derived Categories) covered by Mathlib

Each tag registered here is stated in Mathlib; this file only records the correspondence.
-/

add_to_stacks 070H "definition: every chain map from an acyclic complex is null-homotopic"
  CochainComplex.IsKInjective
add_to_stacks 070H "Hom_{K(A)}(M, I) = 0 for every acyclic M"
  CochainComplex.isKInjective_iff_rightOrthogonal

add_to_stacks 070J CochainComplex.isKInjective_of_injective

add_to_stacks 014Y CategoryTheory.Functor.IsTriangulated.instComp

add_to_stacks 0147 "homological functor: sends every distinguished triangle to a sequence
  H(X) → H(Y) → H(Z) exact in the abelian category; it extends `PreservesZeroMorphisms` and
  implies `Additive` (instance), so it is the Stacks notion for an additive functor"
  CategoryTheory.Functor.IsHomological
add_to_stacks 0147 "cohomological functor: Mathlib's form is a homological functor `H : Dᵒᵖ ⥤ A`
  for the opposite pretriangulated structure, whose defining exactness is
  H(Z) → H(Y) → H(X) for each distinguished triangle of `D`"
  CategoryTheory.Functor.map_distinguished_op_exact
add_to_stacks 0148 "the connecting map H(h) : H^n(Z) → H^(n+1)(X), with H^n = `F.shift n`"
  CategoryTheory.Functor.homologySequenceδ
add_to_stacks 0148 "the exact sequence itself, as a `ComposableArrows A 5` from H^n(X) to
  H^(n+1)(Z); the long exact sequence is the family of these over all n"
  CategoryTheory.Functor.homologySequenceComposableArrows₅_exact
add_to_stacks 014C CategoryTheory.IsTriangulated.mk'
add_to_stacks 014E "the cone C(f) of a morphism of complexes" CochainComplex.mappingCone
add_to_stacks 014E "the canonical morphism i : L → C(f)" CochainComplex.mappingCone.inr
add_to_stacks 014E "the canonical morphism p : C(f) → K[1], as a cocycle of degree 1"
  CochainComplex.mappingCone.fst
add_to_stacks 014F "the morphism c : C(f₁) → C(f₂) induced by a homotopy"
  CochainComplex.mappingCone.mapOfHomotopy
add_to_stacks 014F "(a, b, c) is a morphism of triangles in K(A)"
  CochainComplex.mappingCone.trianglehMapOfHomotopy
add_to_stacks 014I "the given direct sum decompositions `B^n = A^n ⊕ C^n` compatible with `α^n` and
  `β^n` (with `s^n` and `π^n`): a termwise split exact sequence is a short complex `S` of cochain
  complexes with a splitting `σ n : (S.map (eval _ _ n)).Splitting` in each degree"
  CategoryTheory.ShortComplex.Splitting
add_to_stacks 014I "the associated morphism of complexes `δ : C^• → A^•[1]`"
  CochainComplex.homOfDegreewiseSplit
add_to_stacks 014I "the degree-`n` component of `δ`, `π^{n+1} ∘ d_B^n ∘ s^n`: it is the
  `(n, n+1)` component of `cocycleOfDegreewiseSplit`"
  CochainComplex.homOfDegreewiseSplit_f
add_to_stacks 014I "the cocycle `(σ p).s ≫ d_B ≫ (σ q).r` underlying `δ`"
  CochainComplex.cocycleOfDegreewiseSplit
add_to_stacks 014I "the triangle `(A^•, B^•, C^•, α, β, δ)` associated to the termwise split
  sequence"
  CochainComplex.triangleOfDegreewiseSplit
add_to_stacks 014S "`K(A)` with its translation functors and distinguished triangles is a
  triangulated category (TR4, on top of the pre-triangulated structure)"
  HomotopyCategory.instIsTriangulatedIntUp
add_to_stacks 014S "the pre-triangulated structure of `K(A)` (TR1, TR2, TR3)"
  HomotopyCategory.instPretriangulatedIntUp
add_to_stacks 014S "Mathlib's distinguished triangles (mapping cones) are the Stacks ones: the
  triangles isomorphic to the triangle of a termwise split exact sequence"
  HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit
add_to_stacks 014V "the functorial isomorphisms ξ : F(X[1]) ≅ F(X)[1] (for every shift by ℤ)"
  CategoryTheory.Functor.CommShift
add_to_stacks 014V "the image triangle (F X, F Y, F Z, F f, F g, ξ_X ∘ F h)"
  CategoryTheory.Functor.mapTriangle
add_to_stacks 014V "exact (triangulated) functor: the image triangle of every distinguished
  triangle is distinguished"
  CategoryTheory.Functor.IsTriangulated
add_to_stacks 05QL "pieces on the right: rotation Y → Z → X[1] → Y[1], last map -f[1]"
  CategoryTheory.Pretriangulated.rot_of_distTriang
add_to_stacks 05QL "pieces on the left: inverse rotation Z[-1] → X → Y → Z, first map -h[-1]"
  CategoryTheory.Pretriangulated.inv_rot_of_distTriang
add_to_stacks 05RF "(1) the kernel Ker(F) of an exact functor F : D ⥤ D': the objects X with
  F(X) = 0, as an `ObjectProperty`; it is strictly full and, by 05RC
  (`CategoryTheory.Functor.isTriangulated_and_isSaturated_kernel`), a saturated
  (pre-)triangulated subcategory"
  CategoryTheory.Functor.kernel
add_to_stacks 05RF "(2) the kernel Ker(H) of a homological functor H : D ⥤ A to an abelian
  category: the objects X with H(X[n]) = 0 for all n : ℤ, as an `ObjectProperty`; it is strictly
  full and, by 05RD (`CategoryTheory.Functor.isTriangulated_and_isSaturated_homologicalKernel`),
  a saturated (pre-)triangulated subcategory"
  CategoryTheory.Functor.homologicalKernel
add_to_stacks 05ST CategoryTheory.Functor.homologySequenceComposableArrows₅_exact
add_to_stacks 05SW "the functor RF : S⁻¹D ⥤ D' itself: Mathlib's total right derived functor, a
  left Kan extension along the localization, defined under `HasRightDerivedFunctor` rather than
  under 05SV derivability; for a right derivable F it exists and is the source's RF
  (`CategoryTheory.Functor.hasRightDerivedFunctor_of_isRightDerivable` and
  `CategoryTheory.Functor.totalRightDerived_isTriangulated_and_isRightDerivedValueAt`)"
  CategoryTheory.Functor.totalRightDerived
add_to_stacks 05SW "the functor LF : S⁻¹D ⥤ D' itself: Mathlib's total left derived functor, a
  right Kan extension along the localization, defined under `HasLeftDerivedFunctor` rather than
  under 05SV derivability; for a left derivable F it exists and is the source's LF
  (`CategoryTheory.Functor.hasLeftDerivedFunctor_of_isLeftDerivable` and
  `CategoryTheory.Functor.totalLeftDerived_isTriangulated_and_isLeftDerivedValueAt`)"
  CategoryTheory.Functor.totalLeftDerived
