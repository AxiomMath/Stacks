module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The pullback-tensor comparison on K-flat representatives

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  The comparison of Stacks 079U,

`Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L`,

is *constructed* by descending `Stacks.Cohomology.DerivedPullbackTensor.modelComparison` — the
comparison at a pair of K-flat complexes, where both sides are computed by ordinary total
tensor complexes — along the localization of pairs of K-flat objects.  The descent is
`CategoryTheory.Localization.liftNatIso`, which characterises the descended transformation only
up to the statement that it *is* a lift; nothing in the construction records what its components
are at a pair of K-flat complexes.

This file records exactly that.  It is the identification the source's own construction of
079U asserts: on K-flat representatives the comparison is the degreewise isomorphism
`f^*(K^p ⊗_{𝒪_Y} L^q) ≅ f^*K^p ⊗_{𝒪_X} f^*L^q` of Stacks 01CD assembled on total complexes.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_kFlatQPair`: at a
  pair of K-flat objects of the homotopy category, the component of 079U is the component of
  `Stacks.Cohomology.DerivedPullbackTensor.modelsComparison`.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_of_kFlat`: at a pair
  of K-flat *cochain complexes* `K, L`, the component of 079U at `(QK, QL)` is
  `Stacks.Cohomology.DerivedPullbackTensor.modelComparison`, with no transport left over.

## Implementation notes

*Why this is not already available.*
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` is
`CategoryTheory.Localization.liftNatIso` applied to
`Stacks.Cohomology.DerivedPullbackTensor.modelsComparison`.  Mathlib's
`CategoryTheory.Localization.liftNatTrans_app` computes a lifted transformation at an object in
the image of the localization functor, in terms of the two `CategoryTheory.Localization.Lifting`
isomorphisms.  Both liftings here are `CategoryTheory.Localization.Lifting.compLeft`, whose
isomorphism is `Iso.refl`, so the two transports collapse and the component is literally the
component of the models comparison.

*From homotopy objects to complexes.*  `Stacks.Cohomology.DerivedPullbackTensor.kFlatQPair` lands
at `Qh` of a homotopy class, not at `Q` of a complex, and
`Stacks.Cohomology.DerivedPullbackTensor.modelsComparison` already conjugates
`Stacks.Cohomology.DerivedPullbackTensor.modelComparison` by the `Q` versus `Qh ∘ quotient`
bridge `Stacks.Cohomology.DerivedPullbackTensor.kFlatQPairIso`.  Conjugating back by the same
bridge — which is naturality of 079U along it — cancels both transports, which is what makes the
second statement an equation between the two comparisons themselves.

*No new hypotheses.*  The four sheafification binders are the ones
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` is itself stated under; both
are `Prop`s and both are inhabited for every ringed space.  `K` and `L` are arbitrary K-flat
cochain complexes, with no boundedness, flatness or quasi-coherence assumption.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

/-- Cancelling an isomorphism against its inverse in the last two factors of a composite.
Stated abstractly: in the concrete goal below the subterm cannot be abstracted into a rewrite
motive, so the reassociation is supplied as a lemma and applied by unification instead. -/
private lemma comp_inv_hom_cancel {C : Type*} [Category C] {W Z₁ Z₂ Z₃ : C}
    (p : W ⟶ Z₁) (q : Z₁ ⟶ Z₂) (e : Z₃ ≅ Z₂) : (p ≫ q ≫ e.inv) ≫ e.hom = p ≫ q := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] kFlatQPair_isLocalization

/-- **The comparison of Stacks 079U at a pair of K-flat objects of the homotopy category is the
models comparison it was descended from.**  Both liftings consumed by
`CategoryTheory.Localization.liftNatIso` are
`CategoryTheory.Localization.Lifting.compLeft`, whose isomorphism is `Iso.refl`, so
`CategoryTheory.Localization.liftNatTrans_app` leaves no transport. -/
theorem derivedPullbackTensorIso_hom_app_kFlatQPair
    (M : (CochainComplex.KFlatBifunctor.kFlatObjects
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).FullSubcategory ×
        (CochainComplex.KFlatBifunctor.kFlatObjects
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).FullSubcategory) :
    (derivedPullbackTensorIso f).hom.app ((kFlatQPair (Y := Y)).obj M) =
      (modelsComparison f).hom.app M := by
  dsimp only [derivedPullbackTensorIso]
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp

/-- A pair of K-flat cochain complexes, read as a pair of K-flat objects of the homotopy
category.  Kept reducible so that the two projections back to `K` and `L` reduce. -/
private abbrev kFlatPairOf
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    (CochainComplex.KFlatBifunctor.kFlatObjects
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).FullSubcategory ×
      (CochainComplex.KFlatBifunctor.kFlatObjects
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).FullSubcategory :=
  (⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K, hK⟩,
    ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L, hL⟩)

/-- **Stacks 079U on K-flat representatives.**  At a pair of K-flat cochain complexes `K, L`
of `𝒪_Y`-modules the comparison

`Lf^*(QK ⊗^L_{𝒪_Y} QL) ≅ Lf^*(QK) ⊗^L_{𝒪_X} Lf^*(QL)`

is `Stacks.Cohomology.DerivedPullbackTensor.modelComparison`, where both sides are computed by
ordinary total tensor complexes and the comparison is the one of Stacks 01CD assembled on them.
This is the identification the construction of 079U asserts and `liftNatIso` does not record. -/
/- No `stacks` attribute: Stacks 079U is already covered, unclaused, by
`derivedPullbackTensorIso` (`PullbackTensorComparison.lean:494`). This is a characterisation of
the components of that comparison — a fact about the construction which `Localization.liftNatIso`
does not record — not a further clause of 079U's statement, so claiming coverage here would
contradict the bare attribute there. -/
theorem derivedPullbackTensorIso_hom_app_of_kFlat
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    (derivedPullbackTensorIso f).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (modelComparison f K L hK hL).hom := by
  have h := (derivedPullbackTensorIso f).hom.naturality
    (kFlatQPairIso (kFlatPairOf K L hK hL)).hom
  rw [derivedPullbackTensorIso_hom_app_kFlatQPair f (kFlatPairOf K L hK hL)] at h
  have key : (modelsComparison f).hom.app (kFlatPairOf K L hK hL) =
      ((pullbackOfTensor f).mapIso (kFlatQPairIso (kFlatPairOf K L hK hL))).hom ≫
        (modelComparison f K L hK hL).hom ≫
          ((tensorOfPullbacks f).mapIso (kFlatQPairIso (kFlatPairOf K L hK hL))).inv := rfl
  have h' : ((pullbackOfTensor f).mapIso (kFlatQPairIso (kFlatPairOf K L hK hL))).hom ≫
        (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (modelsComparison f).hom.app (kFlatPairOf K L hK hL) ≫
        ((tensorOfPullbacks f).mapIso (kFlatQPairIso (kFlatPairOf K L hK hL))).hom := h
  refine (Iso.cancel_iso_hom_left
    ((pullbackOfTensor f).mapIso (kFlatQPairIso (kFlatPairOf K L hK hL))) _ _).1 ?_
  rw [h', key]
  exact comp_inv_hom_cancel _ _ _

end Stacks.Cohomology.DerivedPullbackTensor

end
