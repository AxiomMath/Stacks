module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatDeformation.Deformation

/-!
# Isomorphic flat deformations give isomorphic solutions
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction)
open Stacks.Thickenings.FlatDeformation

universe u

namespace Stacks.Thickenings.FlatDeformation

variable {X S S' : Scheme.{u}} {t : S ⟶ S'} {f : X ⟶ S} [IsClosedImmersion t]
  (hst : t.ker ^ 2 = ⊥)

/-- The maps `transportedMap` along two equal morphisms `ψ₁ = ψ₂` agree. -/
theorem transportedMap_congr {X' X'₂ : Scheme.{u}} (i : X ⟶ X') [IsIso i.base]
    [IsClosedImmersion i] (i₂ : X ⟶ X'₂) [IsIso i₂.base] [IsClosedImmersion i₂]
    {ψ₁ ψ₂ : X'₂ ⟶ X'} (h : ψ₁ = ψ₂) (h₁ : i₂ ≫ ψ₁ = i) (h₂ : i₂ ≫ ψ₂ = i) :
    transportedMap i i₂ h₁ = transportedMap i i₂ h₂ := by
  subst h
  rfl

variable {D₁ D₂ : FlatDeformation t f} [IsIso D₁.i.base] [IsIso D₂.i.base]

omit [IsClosedImmersion t] [IsIso D₁.i.base] [IsIso D₂.i.base] in
/-- The inverse of an isomorphism of flat deformations is compatible with the identifications
of `X`. -/
theorem Iso.comm_i_inv (φ : FlatDeformation.Iso D₁ D₂) : D₂.i ≫ φ.e.inv = D₁.i := by
  rw [← φ.comm_i, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [IsClosedImmersion t] [IsIso D₁.i.base] [IsIso D₂.i.base] in
/-- The inverse of an isomorphism of flat deformations is a morphism over `S'`. -/
theorem Iso.comm_f'_inv (φ : FlatDeformation.Iso D₁ D₂) : φ.e.inv ≫ D₁.f' = D₂.f' := by
  rw [Iso.inv_comp_eq, φ.comm_f']

/-- The isomorphism of transported sheaves induced by an isomorphism of flat deformations. -/
def sheafIso (φ : FlatDeformation.Iso D₁ D₂) : sheaf D₁ ≅ sheaf D₂ where
  hom := transportedMap D₁.i D₂.i φ.comm_i_inv
  inv := transportedMap D₂.i D₁.i φ.comm_i
  hom_inv_id := by
    rw [transportedMap_comp, transportedMap_congr D₁.i D₁.i (Iso.hom_inv_id φ.e) _
      (Category.comp_id _), transportedMap_id]
  inv_hom_id := by
    rw [transportedMap_comp, transportedMap_congr D₂.i D₂.i (Iso.inv_hom_id φ.e) _
      (Category.comp_id _), transportedMap_id]

/-- `sheafIso φ` is compatible with the maps from the thickened base ring. -/
theorem baseRingMap_comp_sheafIso (φ : FlatDeformation.Iso D₁ D₂) :
    baseRingMap D₁ ≫ (sheafIso φ).hom = baseRingMap D₂ := by
  refine ((sheafAdjunction (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom)).homEquiv _ _).injective ?_
  refine (Adjunction.homEquiv_naturality_right _ _ _).trans ?_
  refine (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans ?_
  refine Eq.trans ?_ (Equiv.apply_symm_apply _ _).symm
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V =>
    CommRingCat.hom_ext (RingHom.ext fun a => ?_)))
  exact transportedMap_transportedBase D₁.i D₂.i φ.comm_i_inv D₁.isPullback.w D₂.isPullback.w
    φ.comm_f'_inv V.unop a

/-- **Isomorphic flat deformations give isomorphic solutions of the deformation problem.** -/
def solutionIso (φ : FlatDeformation.Iso D₁ D₂) (c : ideal t f hst ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureHom f).fSharpInverseImage)).obj (conormalModule t f))
    (hc₁ : c = idealMap hst D₁) (hc₂ : c = idealMap hst D₂) :
    Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening.Iso.{u,
        u, u, u, u, u}
      (S := problem t f hst c) (toSolution hst D₁ c hc₁) (toSolution hst D₂ c hc₂) where
  hom := sheafIso φ
  reduction_comm := transportedMap_comp_reduction D₁.i D₂.i φ.comm_i_inv
  baseMap_comm := (Category.assoc _ _ _).trans
    (congrArg ((idIso f (thickenedBaseRing t f)).hom ≫ ·) (baseRingMap_comp_sheafIso φ))
  kernel_comm U g := kernel_comm_of_canonical hst (reduction D₁) (reduction D₂)
    (kernelIncl hst D₁) (kernelIncl hst D₂) (fun U => kernelIncl_injective hst D₂ U.unop)
    (fun U a ha => exists_kernelIncl_eq hst D₂ U.unop a ha)
    (fun U m => reduction_kernelIncl hst D₁ U.unop m) (sheafIso φ).hom
    (transportedMap_comp_reduction D₁.i D₂.i φ.comm_i_inv)
    (fun W j hj => by
      refine (congrArg _ (kernelIncl_canonicalSection hst D₁ W j hj)).trans ?_
      refine Eq.trans ?_ (kernelIncl_canonicalSection hst D₂ W j hj).symm
      exact transportedMap_transportedBase D₁.i D₂.i φ.comm_i_inv D₁.isPullback.w D₂.isPullback.w
        φ.comm_f'_inv W j) U g

end Stacks.Thickenings.FlatDeformation
