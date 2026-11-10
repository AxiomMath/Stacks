module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KProjectiveLeftDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimHomPointTensorNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimQcohPointTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelAffinePointTensorFullyFaithful

/-!
# `Hom_{D(𝒪_X)}(𝒪_X, 𝒪_X ⊗_A C)` is `Hom_{D(A)}(A, C)`

Let `X` be an algebraic space with an isomorphism `g : X ≅ h_{Spec A}`, let
`ψ : A ≅ Γ(X, 𝒪_X)` be the induced ring isomorphism and `T_ψ : M ↦ 𝒪_X ⊗_A M` the inverse image
along `X ⟶ (pt, A)`, read on the spaces-étale model of `X`.

The module
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelAffinePointTensorFullyFaithful`
makes `C ↦ Q(T_ψ(C))` fully faithful on maps out of a K-projective complex:
`AlgebraicGeometry.Space.exists_pointTensor_Q_map_eq` lifts a morphism of the derived category to
a map of complexes and `AlgebraicGeometry.Space.pointTensor_Q_map_eq_iff` decides when two such
maps induce the same morphism.  Neither is stated at the first argument the affine leaf of
Stacks 09RI uses, which is the **structure sheaf** `𝒪_X[0]` rather than a point tensor; and the
structure sheaf *is* a point tensor, of the one-term complex `A` in degree `0`
(`AlgebraicGeometry.Space.pointTensorSingleSelfIso`), which is K-projective by
`Stacks.Homology.isKProjective_single`.

This file makes that substitution, so that morphisms

`𝒪_X[0] ⟶ Q(T_ψ(C))`  in  `D(𝒪_X)`

are maps of complexes `A[0] ⟶ C` up to quasi-isomorphism, for an **arbitrary** complex `C` of
`A`-modules — no boundedness, finiteness or projectivity on `C`, which is what the second
argument of Stacks 09RI's clause (1) needs, since
`AlgebraicGeometry.Space.exists_pointTensor_iso_of_isQuasicoherentOnSite_of_isAffineSpace`
presents an object of `D_QCoh(𝒪_X)` as `T_ψ(C)` for an unbounded `C`.

## What is on the model and what is not

Both statements are about the spaces-étale *model* of `X`, where the point tensor lives.  The
unit of the affine leaf of Stacks 09RI lives on the small étale site of `X`; the two sides are
matched by `AlgebraicGeometry.Space.spacesEtaleModelDerivedEquiv`, which is the form
`exists_pointTensor_iso_of_isQuasicoherentOnSite` already states its isomorphism in.  **No
transport of the unit through that equivalence is proved here**, and the leaf statement is not
reached: what is reached is the model-side Hom-group identification, which is one of its inputs.

## Main results

* `AlgebraicGeometry.Space.exists_unit_pointTensor_Q_map_eq`: **every morphism
  `𝒪_X[0] ⟶ Q(T_ψ(C))` is induced by a map of complexes `A[0] ⟶ C`.**
* `AlgebraicGeometry.Space.unit_pointTensor_Q_map_eq_iff`: **two such maps induce the same
  morphism exactly when they agree in `D(A)`.**

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A : Type u} [CommRing A]

variable (hA : B.Contains (Spec (CommRingCat.of A))) (p : Spec (CommRingCat.of A) ⟶ S)
  {X : AlgebraicSpaces B S hS}
  (g : X ≅ ⟨yoneda.obj (BigFppfOver.mk B S hS hA p), isAlgebraicSpace_yoneda B S hS _⟩)

/-- **Every morphism `𝒪_X[0] ⟶ Q(𝒪_X ⊗_A C)` is induced by a map of complexes `A[0] ⟶ C`**, for
an arbitrary complex `C` of `A`-modules.

This is `AlgebraicGeometry.Space.exists_pointTensor_Q_map_eq` at the K-projective first argument
`A[0]`, transported along `AlgebraicGeometry.Space.pointTensorSingleSelfIso`, which identifies
`Q(T_ψ(A[0]))` with `𝒪_X[0]`. -/
theorem exists_unit_pointTensor_Q_map_eq (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (φ : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelRingedTopos B S hS X).O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelRingedTopos B S hS X).O)) ⟶
      DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) :
    ∃ u : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A) ⟶ C,
      (pointTensorSingleSelfIso B S hS
          (representedTildeOfIsoPointRingHom B S hS hA p g)).inv ≫
        DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS
          (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u) = φ := by
  have := Stacks.Homology.isKProjective_single (ModuleCat.of A A)
  obtain ⟨u, hu⟩ := exists_pointTensor_Q_map_eq B S hS hA p g
    ((pointTensorSingleSelfIso B S hS
      (representedTildeOfIsoPointRingHom B S hS hA p g)).hom ≫ φ)
  exact ⟨u, by rw [hu, Iso.inv_hom_id_assoc]⟩

/-- **Two maps of complexes `A[0] ⟶ C` induce the same morphism `𝒪_X[0] ⟶ Q(𝒪_X ⊗_A C)` exactly
when they agree in `D(A)`**, for an arbitrary complex `C` of `A`-modules.

This is `AlgebraicGeometry.Space.pointTensor_Q_map_eq_iff` read through
`AlgebraicGeometry.Space.pointTensorSingleSelfIso`, an isomorphism being cancellable. -/
theorem unit_pointTensor_Q_map_eq_iff (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (u u' : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ C) :
    (pointTensorSingleSelfIso B S hS
          (representedTildeOfIsoPointRingHom B S hS hA p g)).inv ≫
        DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS
          (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u) =
      (pointTensorSingleSelfIso B S hS
          (representedTildeOfIsoPointRingHom B S hS hA p g)).inv ≫
        DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS
          (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u') ↔
      DerivedCategory.Q.map u = DerivedCategory.Q.map u' := by
  rw [cancel_epi]
  exact pointTensor_Q_map_eq_iff B S hS hA p g u u'

end AlgebraicGeometry.Space

end
