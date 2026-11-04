module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus.ChartDefs
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic

/-!
# Sections over an affine base, for the charts of the descent locus

For a scheme `X'` over `Spec B` the global sections of an `𝒪_{X'}`-module are a `B`-module
(`Stacks.Cech.sectionsModule`). This file records how that module structure interacts with
isomorphisms of modules, and computes its rank for a free module when `B ≅ Γ(X', 𝒪)`.

## Main definitions

* `AlgebraicGeometry.DescentLocus.baseSectionsEquivOfIso`: an isomorphism of modules is
  `B`-linear on global sections.

## Main results

* `AlgebraicGeometry.DescentLocus.finrank_sections_of_iso_free`: if `B → Γ(X', 𝒪)` is bijective
  and `M ≅ 𝒪^m`, the global sections of `M` are free of rank `m` over `B`.
* `AlgebraicGeometry.DescentLocus.bijective_globalRingHom_of_isIso`: the hypothesis
  `𝒪 = f_* 𝒪` on a base change gives `B ≅ Γ(X', 𝒪)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.DescentLocus

variable {B : Type u} [CommRing B] {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of B))

/-- An isomorphism of modules on a scheme over `Spec B` is `B`-linear on global sections. -/
def baseSectionsEquivOfIso {M N : X'.Modules} (e : M ≅ N) :
    letI := Stacks.Cech.sectionsModule f' M ⊤
    letI := Stacks.Cech.sectionsModule f' N ⊤
    Γ(M, ⊤) ≃ₗ[B] Γ(N, ⊤) :=
  letI := Stacks.Cech.sectionsModule f' M ⊤
  letI := Stacks.Cech.sectionsModule f' N ⊤
  { (sectionsLinearEquivOfIso e ⊤).toEquiv with
    map_add' := fun a b ↦ (sectionsLinearEquivOfIso e ⊤).map_add a b
    map_smul' := fun c a ↦
      (sectionsLinearEquivOfIso e ⊤).map_smul ((Stacks.Cech.baseRingHom f' ⊤).hom c) a }

@[simp]
theorem baseSectionsEquivOfIso_apply {M N : X'.Modules} (e : M ≅ N) (a : Γ(M, ⊤)) :
    baseSectionsEquivOfIso f' e a = e.hom.app ⊤ a := rfl

/-- **The rank of the sections of a free module over the base.** If the structural map
`B → Γ(X', 𝒪)` is bijective and `M ≅ 𝒪^m`, then `Γ(M, ⊤)` is free of rank `m` over `B`. -/
theorem finrank_sections_of_iso_free [Nontrivial B]
    (hp : Function.Bijective (Stacks.Cech.globalRingHom f').hom) {M : X'.Modules} {m : ℕ}
    (e : M ≅ SheafOfModules.free (ULift.{u} (Fin m))) :
    @Module.finrank B Γ(M, ⊤) _ _ (Stacks.Cech.sectionsModule f' M ⊤) = m := by
  let := Stacks.Cech.sectionsModule f' M ⊤
  let b₀ : Module.Basis (Fin m) Γ(X', ⊤) Γ(M, ⊤) :=
    (freeSectionsBasis X' m).map (sectionsLinearEquivOfIso e ⊤).symm
  rw [Module.finrank_eq_card_basis (basisOverBase f' hp M b₀), Fintype.card_fin]

/-- The structural map `B → Γ(X', 𝒪)` is bijective when the comparison `𝒪_{Spec B} ⟶ f'_* 𝒪`
is an isomorphism. -/
theorem bijective_globalRingHom_of_isIso (h : IsIso f'.toLRSHom.toHom.c) :
    Function.Bijective (Stacks.Cech.globalRingHom f').hom := by
  have h₁ : IsIso (f'.app ⊤) := by
    rw [NatTrans.isIso_iff_isIso_app] at h
    exact h (Opposite.op ⊤)
  have h₂ : IsIso (Stacks.Cech.globalRingHom f') :=
    IsIso.comp_isIso' (AlgebraicGeometry.isIso_toSpecΓ _) h₁
  exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry.DescentLocus
