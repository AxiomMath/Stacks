module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.ProjectionMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TransportedProjectionMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaOfToposHom

/-!
# The étale projection map is the projection map of the constant ringed topoi

For a morphism of schemes `f : X ⟶ Y` and a commutative ring `Λ`, the projection map
`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f^{-1}K)` on `D(X_étale, Λ)` and `D(Y_étale, Λ)`
(`Stacks.EtaleCohomology.etalePushforwardProjectionMap`) is built from the derived adjunction,
the derived tensor products and the comparison of [Stacks, Tag 07A4] of the morphism of constant
ringed topoi `(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)`, all read through the equivalences
`Stacks.EtaleCohomology.etaleDerivedEquivalence`. Hence it is the map of [Stacks, Tag 0B56] for
that morphism of ringed topoi
(`Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap`) read through the same
equivalences; in particular one is invertible exactly when the other is.

## Main results

* `Stacks.EtaleCohomology.isIso_etalePushforwardProjectionMap_iff`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The étale projection map is invertible exactly when the projection map of [Stacks, Tag 0B56]
for the morphism of constant ringed topoi is**, at the images of the two complexes under
`Stacks.EtaleCohomology.etaleDerivedEquivalence`. -/
theorem isIso_etalePushforwardProjectionMap_iff (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    IsIso (etalePushforwardProjectionMap.{u, r} Λ f E K) ↔
      IsIso (Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap
        (etaleRingedToposHom.{u, r} Λ f) ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj E)
        ((etaleDerivedEquivalence.{u, r} Λ Y).functor.obj K)) :=
  Stacks.CategoryTheory.ProjectionMapTransport.isIso_adjunctionTensorMap_transport_iff
    (etaleDerivedEquivalence.{u, r} Λ Y) (etaleDerivedEquivalence.{u, r} Λ X)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
      (etaleRingedToposHom.{u, r} Λ f))
    (etaleRingedDerivedPullbackIso.{u, r} Λ f) (etaleDerivedPushforwardIsoConj.{u, r} Λ f)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
      (etaleRingedToposHom.{u, r} Λ f)) E K

end Stacks.EtaleCohomology

end
