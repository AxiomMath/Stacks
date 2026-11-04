module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# A coherence for inverse images along two factorizations

Inverse images of sheaves of modules on schemes form a pseudofunctor. This file records the
instance of its coherence needed to compare two identifications of a module obtained by
pulling back along two factorizations of the same morphism: given `r₁ ≫ M = i ≫ r₂` and maps of
modules `τ₁ = τ₂` through `M` and `θ₂ ≫ φ = θ₁` through `r₁`, the composite identifications
`(r₁ ≫ M ≫ c₂)^* ℒ ⟶ 𝒩₁` and `i^* (r₂ ≫ c₂)^* ℒ ⟶ i^* 𝒩₂ ⟶ 𝒩₁` agree.

## Main results

* `Stacks.PolarizedAlgebraization.pullback_two_factorizations`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.PolarizedAlgebraization

section Helpers

variable {A B C D : Scheme.{u}}

/-- The identification of inverse images along equal morphisms is an `eqToHom`. -/
theorem pullbackCongr_hom_app_eq_eqToHom {f g : A ⟶ B} (h : f = g) (N : B.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app N = eqToHom (by rw [h]) := by
  subst h
  rfl

/-- **Associativity of the identifications of inverse images**, componentwise:
`f^* (g, h)⁻¹ ≫ (f, g)` is `(f, g ≫ h)` followed by `(f ≫ g, h)⁻¹`, up to the reassociation. -/
theorem map_pullbackComp_inv_app_comp_hom_app (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (N : D.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app N) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj N) =
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app N ≫ eqToHom (by rw [Category.assoc]) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app N := by
  have hh := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToHom_app, Category.id_comp] at hh
  rw [← cancel_epi ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app N),
    ← cancel_mono ((Scheme.Modules.pullbackComp (f ≫ g) h).hom.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact hh

/-- The identification `(w, c)` of inverse images commutes with replacing `w` by an equal
morphism. -/
theorem pullbackComp_inv_app_comp_eqToHom {w₁ w₂ : A ⟶ B} (h : w₁ = w₂) (c : B ⟶ C)
    (N : C.Modules) :
    (Scheme.Modules.pullbackComp w₁ c).inv.app N ≫
        eqToHom (show (Scheme.Modules.pullback w₁).obj ((Scheme.Modules.pullback c).obj N) =
          (Scheme.Modules.pullback w₂).obj ((Scheme.Modules.pullback c).obj N) by rw [h]) =
      eqToHom (by rw [h]) ≫ (Scheme.Modules.pullbackComp w₂ c).inv.app N := by
  subst h
  simp

end Helpers

variable {X₁ X₂ P₁ P₂ Q : Scheme.{u}} (i : X₁ ⟶ X₂) (r₁ : X₁ ⟶ P₁) (r₂ : X₂ ⟶ P₂) (M : P₁ ⟶ P₂)
  (c₂ : P₂ ⟶ Q) (c₁ : P₁ ⟶ Q) (hc : M ≫ c₂ = c₁) (hr : r₁ ≫ M = i ≫ r₂) (L : Q.Modules)
  {L₁ : P₁.Modules} {L₂ : P₂.Modules}
  {N₁ : X₁.Modules} {N₂ : X₂.Modules}
  (τ₂ : (Scheme.Modules.pullback c₂).obj L ⟶ L₂) (μ : (Scheme.Modules.pullback M).obj L₂ ⟶ L₁)
  (θ₁ : (Scheme.Modules.pullback r₁).obj L₁ ⟶ N₁) (θ₂ : (Scheme.Modules.pullback r₂).obj L₂ ⟶ N₂)
  (φ : (Scheme.Modules.pullback i).obj N₂ ⟶ N₁)

/-- **Two factorizations of the same inverse image agree.** With `τ₁ : c₁^* ℒ ⟶ L₁` equal to
`τ₂ : c₂^* ℒ ⟶ L₂` pulled back along `M` followed by `μ` (through `M ≫ c₂ = c₁`), and `θ₂`
pulled back along `i` followed by `φ` equal to `μ` pulled back along `r₁` followed by `θ₁`
(through `r₁ ≫ M = i ≫ r₂`), the two identifications of `(i ≫ r₂ ≫ c₂)^* ℒ` with `𝒩₁`
agree. -/
theorem pullback_two_factorizations
    (H : (Scheme.Modules.pullback i).map θ₂ ≫ φ =
      (Scheme.Modules.pullbackComp i r₂).hom.app L₂ ≫
        (Scheme.Modules.pullbackCongr hr.symm).hom.app L₂ ≫
        (Scheme.Modules.pullbackComp r₁ M).inv.app L₂ ≫
        (Scheme.Modules.pullback r₁).map μ ≫ θ₁)
    (hj : i ≫ r₂ ≫ c₂ = r₁ ≫ c₁) :
    (Scheme.Modules.pullbackComp i (r₂ ≫ c₂)).hom.app L ≫
        (Scheme.Modules.pullbackCongr hj).hom.app L ≫
        (Scheme.Modules.pullbackComp r₁ c₁).inv.app L ≫
        (Scheme.Modules.pullback r₁).map
          ((Scheme.Modules.pullbackCongr hc.symm).hom.app L ≫
            (Scheme.Modules.pullbackComp M c₂).inv.app L ≫
            (Scheme.Modules.pullback M).map τ₂ ≫ μ) ≫ θ₁ =
      (Scheme.Modules.pullback i).map
          ((Scheme.Modules.pullbackComp r₂ c₂).inv.app L ≫
            (Scheme.Modules.pullback r₂).map τ₂ ≫ θ₂) ≫ φ := by
  subst hc
  have n1 : (Scheme.Modules.pullback i).map ((Scheme.Modules.pullback r₂).map τ₂) ≫
      (Scheme.Modules.pullbackComp i r₂).hom.app L₂ =
      (Scheme.Modules.pullbackComp i r₂).hom.app _ ≫
        (Scheme.Modules.pullback (i ≫ r₂)).map τ₂ :=
    (Scheme.Modules.pullbackComp i r₂).hom.naturality τ₂
  have n2 : (Scheme.Modules.pullback (i ≫ r₂)).map τ₂ ≫
      (Scheme.Modules.pullbackCongr hr.symm).hom.app L₂ =
      (Scheme.Modules.pullbackCongr hr.symm).hom.app _ ≫
        (Scheme.Modules.pullback (r₁ ≫ M)).map τ₂ :=
    (Scheme.Modules.pullbackCongr hr.symm).hom.naturality τ₂
  have n3 : (Scheme.Modules.pullback (r₁ ≫ M)).map τ₂ ≫
      (Scheme.Modules.pullbackComp r₁ M).inv.app L₂ =
      (Scheme.Modules.pullbackComp r₁ M).inv.app _ ≫
        (Scheme.Modules.pullback r₁).map ((Scheme.Modules.pullback M).map τ₂) :=
    (Scheme.Modules.pullbackComp r₁ M).inv.naturality τ₂
  have a1 := map_pullbackComp_inv_app_comp_hom_app r₁ M c₂ L
  have a2 := map_pullbackComp_inv_app_comp_hom_app i r₂ c₂ L
  have b := pullbackComp_inv_app_comp_eqToHom hr.symm c₂ L
  have key : (Scheme.Modules.pullbackComp i (r₂ ≫ c₂)).hom.app L ≫
      (Scheme.Modules.pullbackCongr hj).hom.app L ≫
      (Scheme.Modules.pullbackComp r₁ (M ≫ c₂)).inv.app L ≫
      (Scheme.Modules.pullback r₁).map
        ((Scheme.Modules.pullbackCongr (rfl : M ≫ c₂ = M ≫ c₂).symm).hom.app L) ≫
      (Scheme.Modules.pullback r₁).map ((Scheme.Modules.pullbackComp M c₂).inv.app L) =
      (Scheme.Modules.pullback i).map ((Scheme.Modules.pullbackComp r₂ c₂).inv.app L) ≫
        (Scheme.Modules.pullbackComp i r₂).hom.app _ ≫
        (Scheme.Modules.pullbackCongr hr.symm).hom.app _ ≫
        (Scheme.Modules.pullbackComp r₁ M).inv.app _ := by
    rw [← cancel_mono ((Scheme.Modules.pullbackComp r₁ M).hom.app _)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [a1, reassoc_of% a2, pullbackCongr_hom_app_eq_eqToHom, pullbackCongr_hom_app_eq_eqToHom,
      pullbackCongr_hom_app_eq_eqToHom, eqToHom_refl, CategoryTheory.Functor.map_id]
    rw [b]
    simp
  simp only [Functor.map_comp, Category.assoc]
  rw [H, reassoc_of% n1, reassoc_of% n2, reassoc_of% n3]
  simp only [← Category.assoc] at key ⊢
  rw [key]

end Stacks.PolarizedAlgebraization

end
