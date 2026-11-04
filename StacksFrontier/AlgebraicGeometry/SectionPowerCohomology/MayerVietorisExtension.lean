module

public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.MayerVietorisStep

/-!
# The Mayer--Vietoris step for the extension property

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module and `s ∈ Γ(X, ℒ)`. This file proves that the
extension property `Stacks.Cohomology.SectionPowerAnnihilation.Extends` passes from `U`, `V` and
`U ∩ V` to `U ∪ V`, which is the surjectivity half of the induction step in the proof of
[Stacks, Tag 09MR].

## Main results

* `Stacks.Cohomology.SectionPowerAnnihilation.extends_sup_zero` and
  `Stacks.Cohomology.SectionPowerAnnihilation.extends_sup_succ`: the induction step.

## References

* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules Stacks.Cohomology.TwistedGradedModule
open Stacks.Cohomology.AmbientMayerVietoris
open Stacks.SheafOfModules.SectionPowerComposition (mul assocHom mul_comp map_add_eq_zero
  map_eq_zero_of_le)

universe u

namespace Stacks.Cohomology.SectionPowerAnnihilation

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable {X : Scheme.{u}}
  {L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
  [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L] {s : L.sections}

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

local notation "N" => nonvanishingOpen L s

variable (U V : X.Opens)

/-- If `ξ` restricts on `T₂` to `sᶜ` times the restriction of `η`, then restricting `ξ` to `T₃`
through `T₁` gives `sᶜ` times the restriction of `η` to `T₃`. -/
private theorem res_res_eq_map_mul {T T₁ T₂ T₃ Y : X.Opens} (h₁ : T₁ ≤ T) (h₂ : T₂ ≤ T)
    (h₃₁ : T₃ ≤ T₁) (h₃₂ : T₃ ≤ T₂) (hY : T₂ ≤ Y) (n c : ℕ) (G : X.Modules)
    (η : Hgroup X.ringCatSheaf Y n G) (ξ : Hgroup X.ringCatSheaf T n (twist X L G (c : ℤ)))
    (hξ : resH h₂ n _ ξ = (Hfunctor X.ringCatSheaf T₂ n).map (mul X L s G c) (resH hY n G η)) :
    resH h₃₁ n _ (resH h₁ n _ ξ) =
      (Hfunctor X.ringCatSheaf T₃ n).map (mul X L s G c) (resH (h₃₂.trans hY) n G η) := by
  rw [res_res_eq h₁ h₃₁ h₂ h₃₂, hξ, res_map, res_res]

/-- The restrictions of two extensions of the restrictions of one class agree on
`(U ∩ X_s) ∩ (V ∩ X_s)`. -/
theorem res_sub_eq_zero_of_extensions (n : ℕ) (G : X.Modules) (c : ℕ)
    (η : Hgroup X.ringCatSheaf ((U ⊔ V) ⊓ N : X.Opens) n G)
    (ξU : Hgroup X.ringCatSheaf U n (twist X L G (c : ℤ)))
    (ξV : Hgroup X.ringCatSheaf V n (twist X L G (c : ℤ)))
    (hξU : resH inf_le_left n _ ξU =
      (Hfunctor X.ringCatSheaf (U ⊓ N : X.Opens) n).map (mul X L s G c)
        (resH (le_sup_inf_left (L := L) (s := s) U V) n G η))
    (hξV : resH inf_le_left n _ ξV =
      (Hfunctor X.ringCatSheaf (V ⊓ N : X.Opens) n).map (mul X L s G c)
        (resH (le_sup_inf_right (L := L) (s := s) U V) n G η)) :
    resH (inf_inf_le (L := L) (s := s) U V) n _
      (resH inf_le_left n _ ξU -
        resH inf_le_right n _ ξV) = 0 := by
  exact sub_eq_zero_aux _ _ _ _
    (res_res_eq_map_mul inf_le_left inf_le_left (inf_inf_le (L := L) (s := s) U V) inf_le_left
      (le_sup_inf_left (L := L) (s := s) U V) n c G η ξU hξU)
    (res_res_eq_map_mul inf_le_right inf_le_left (inf_inf_le (L := L) (s := s) U V) inf_le_right
      (le_sup_inf_right (L := L) (s := s) U V) n c G η ξV hξV)

/-- In an abelian group, `f (x - y) = 0` forces `f x = f y`. -/
theorem eq_of_map_sub_eq_zero {B D : Type*} [AddCommGroup B] [AddCommGroup D] (f : B →+ D)
    (x y : B) (h : f (x - y) = 0) : f x = f y := by
  rwa [map_sub, sub_eq_zero] at h

/-- The glued class `Ξ` restricts on `W ∩ X_s` to `sᵉ (sᶜ η)`, given that it restricts to `sᵉ ξ`
on `W` and `ξ` restricts to `sᶜ η` on `W ∩ X_s`. -/
private theorem glued_res_aux (n c e : ℕ) (G : X.Modules) {W : X.Opens} (hW : W ≤ U ⊔ V)
    (hWN : W ⊓ N ≤ (U ⊔ V) ⊓ N) (η : Hgroup X.ringCatSheaf ((U ⊔ V) ⊓ N : X.Opens) n G)
    (ξ : Hgroup X.ringCatSheaf W n (twist X L G (c : ℤ)))
    (hξ : resH (inf_le_left : W ⊓ N ≤ W) n _ ξ =
      (Hfunctor X.ringCatSheaf (W ⊓ N : X.Opens) n).map (mul X L s G c) (resH hWN n G η))
    (Ξ : Hgroup X.ringCatSheaf (U ⊔ V : X.Opens) n (twist X L (twist X L G (c : ℤ)) (e : ℤ)))
    (hΞ : resH hW n _ Ξ =
      (Hfunctor X.ringCatSheaf W n).map (mul X L s (twist X L G (c : ℤ)) e) ξ) :
    resH hWN n _
      (resH (inf_le_left : (U ⊔ V) ⊓ N ≤ U ⊔ V) n _ Ξ -
        (Hfunctor X.ringCatSheaf _ n).map (mul X L s _ e)
          ((Hfunctor X.ringCatSheaf _ n).map (mul X L s G c) η)) = 0 := by
  rw [map_sub, res_res_eq inf_le_left hWN hW inf_le_left, hΞ, res_map, hξ, res_map, res_map,
    sub_self]

/-- The glued class restricts on `U ∩ X_s` to `sᵉ (sᶜ η)`. -/
theorem glued_res_left (n c e : ℕ) (G : X.Modules)
    (η : Hgroup X.ringCatSheaf ((U ⊔ V) ⊓ N : X.Opens) n G)
    (ξU : Hgroup X.ringCatSheaf U n (twist X L G (c : ℤ)))
    (hξU : resH (inf_le_left : U ⊓ N ≤ U) n _ ξU =
      (Hfunctor X.ringCatSheaf (U ⊓ N : X.Opens) n).map (mul X L s G c)
        (resH (le_sup_inf_left (L := L) (s := s) U V) n G η))
    (Ξ : Hgroup X.ringCatSheaf (U ⊔ V : X.Opens) n (twist X L (twist X L G (c : ℤ)) (e : ℤ)))
    (hΞU : resH (le_sup_left : U ≤ U ⊔ V) n _ Ξ =
      (Hfunctor X.ringCatSheaf U n).map (mul X L s (twist X L G (c : ℤ)) e) ξU) :
    resH (le_sup_inf_left (L := L) (s := s) U V) n _
      (resH (inf_le_left : (U ⊔ V) ⊓ N ≤ U ⊔ V) n _ Ξ -
        (Hfunctor X.ringCatSheaf _ n).map (mul X L s _ e)
          ((Hfunctor X.ringCatSheaf _ n).map (mul X L s G c) η)) = 0 := by
  exact glued_res_aux U V n c e G le_sup_left (le_sup_inf_left (L := L) (s := s) U V) η ξU hξU
    Ξ hΞU

/-- The glued class restricts on `V ∩ X_s` to `sᵉ (sᶜ η)`. -/
theorem glued_res_right (n c e : ℕ) (G : X.Modules)
    (η : Hgroup X.ringCatSheaf ((U ⊔ V) ⊓ N : X.Opens) n G)
    (ξV : Hgroup X.ringCatSheaf V n (twist X L G (c : ℤ)))
    (hξV : resH (inf_le_left : V ⊓ N ≤ V) n _ ξV =
      (Hfunctor X.ringCatSheaf (V ⊓ N : X.Opens) n).map (mul X L s G c)
        (resH (le_sup_inf_right (L := L) (s := s) U V) n G η))
    (Ξ : Hgroup X.ringCatSheaf (U ⊔ V : X.Opens) n (twist X L (twist X L G (c : ℤ)) (e : ℤ)))
    (hΞV : resH (le_sup_right : V ≤ U ⊔ V) n _ Ξ =
      (Hfunctor X.ringCatSheaf V n).map (mul X L s (twist X L G (c : ℤ)) e) ξV) :
    resH (le_sup_inf_right (L := L) (s := s) U V) n _
      (resH (inf_le_left : (U ⊔ V) ⊓ N ≤ U ⊔ V) n _ Ξ -
        (Hfunctor X.ringCatSheaf _ n).map (mul X L s _ e)
          ((Hfunctor X.ringCatSheaf _ n).map (mul X L s G c) η)) = 0 := by
  exact glued_res_aux U V n c e G le_sup_right (le_sup_inf_right (L := L) (s := s) U V) η ξV hξV
    Ξ hΞV

/-- **Gluing extensions.** Extensions over `U` and over `V` of the restrictions of a class `η`
over `(U ∪ V) ∩ X_s` glue, after a further power of `s`, to a class `Ξ` over `U ∪ V` whose
restriction to `(U ∪ V) ∩ X_s` differs from `sᵉ (sᶜ η)` by a class restricting to zero on
`U ∩ X_s` and on `V ∩ X_s`. -/
theorem exists_glued (n : ℕ) (hEU : Extends X L s U n) (hEV : Extends X L s V n)
    (hUV : Annihilates X L s (U ⊓ V) n) (G : X.Modules) (hG : G.IsQuasicoherent)
    (η : Hgroup X.ringCatSheaf ((U ⊔ V) ⊓ N : X.Opens) n G) :
    ∃ (c e : ℕ) (Ξ : Hgroup X.ringCatSheaf (U ⊔ V : X.Opens) n
        (twist X L (twist X L G (c : ℤ)) (e : ℤ))),
      resH (le_sup_inf_left (L := L) (s := s) U V) n _
          (resH (inf_le_left : (U ⊔ V) ⊓ N ≤ U ⊔ V) n _ Ξ -
            (Hfunctor X.ringCatSheaf _ n).map (mul X L s _ e)
              ((Hfunctor X.ringCatSheaf _ n).map (mul X L s G c) η)) = 0 ∧
      resH (le_sup_inf_right (L := L) (s := s) U V) n _
          (resH (inf_le_left : (U ⊔ V) ⊓ N ≤ U ⊔ V) n _ Ξ -
            (Hfunctor X.ringCatSheaf _ n).map (mul X L s _ e)
              ((Hfunctor X.ringCatSheaf _ n).map (mul X L s G c) η)) = 0 := by
  obtain ⟨c, ξU, ξV, hξU, hξV⟩ := exists_extensions U V n hEU hEV G hG
    (resH (le_sup_inf_left (L := L) (s := s) U V) n G η)
    (resH (le_sup_inf_right (L := L) (s := s) U V) n G η)
  have hD := res_sub_eq_zero_of_extensions U V n G c η ξU ξV hξU hξV
  obtain ⟨e, he⟩ := hUV _ (inf_inf_le U V) (inf_inf_distrib_right U V N).symm _
    (isQuasicoherent_twist (L := L) G hG c) _ hD
  have he' : resH (inf_le_left : U ⊓ V ≤ U) n _
        ((Hfunctor X.ringCatSheaf U n).map (mul X L s _ e) ξU) =
      resH (inf_le_right : U ⊓ V ≤ V) n _
        ((Hfunctor X.ringCatSheaf V n).map (mul X L s _ e) ξV) := by
    have r1 := res_map (inf_le_left : U ⊓ V ≤ U) n (mul X L s (twist X L G (c : ℤ)) e) ξU
    have r2 := res_map (inf_le_right : U ⊓ V ≤ V) n (mul X L s (twist X L G (c : ℤ)) e) ξV
    exact r1.trans ((eq_of_map_sub_eq_zero _ _ _ he).trans r2.symm)
  obtain ⟨Ξ, hΞU, hΞV⟩ := exists_res_eq (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V) rfl n
    _ _ _ he'
  exact ⟨c, e, Ξ, glued_res_left U V n c e G η ξU hξU Ξ hΞU,
    glued_res_right U V n c e G η ξV hξV Ξ hΞV⟩

/-- **The induction step for the extension property in degree zero.** -/
theorem extends_sup_zero (hEU : Extends X L s U 0) (hEV : Extends X L s V 0)
    (hUV : Annihilates X L s (U ⊓ V) 0) : Extends X L s (U ⊔ V) 0 := by
  intro T hT hTeq G hG η
  subst hTeq
  obtain ⟨c, e, Ξ, h₁, h₂⟩ := exists_glued U V 0 hEU hEV hUV G hG η
  have h0 := eq_zero_of_res_eq_zero (le_sup_inf_left (L := L) (s := s) U V)
    (le_sup_inf_right (L := L) (s := s) U V) (sup_inf_eq (L := L) (s := s) U V) _ _ h₁ h₂
  obtain ⟨ξ', hξ'⟩ := exists_extension_add hT c e η Ξ (sub_eq_zero.mp h0)
  exact ⟨c + e, ξ', hξ'⟩

/-- An identity in abelian groups used in the extension step. -/
theorem map_sub_eq_aux {B D D' : Type*} [AddCommGroup B] [AddCommGroup D] [AddCommGroup D']
    (ρ : B →+ D') (μ : D →+ D') (a y : B) (d z : D) (ha : ρ a = μ d) (hy : ρ y = μ (d - z)) :
    ρ (a - y) = μ z := by
  rw [map_sub, ha, hy, map_sub, sub_sub_cancel]

/-- **The induction step for the extension property in positive degree.** -/
theorem extends_sup_succ (q : ℕ) (hEU : Extends X L s U (q + 1)) (hEV : Extends X L s V (q + 1))
    (hUV : Annihilates X L s (U ⊓ V) (q + 1)) (hEUV : Extends X L s (U ⊓ V) q) :
    Extends X L s (U ⊔ V) (q + 1) := by
  intro T hT hTeq G hG η
  subst hTeq
  obtain ⟨c, e, Ξ, h₁, h₂⟩ := exists_glued U V (q + 1) hEU hEV hUV G hG η
  obtain ⟨γ, hγ⟩ := exists_delta_eq (le_sup_inf_left (L := L) (s := s) U V)
    (le_sup_inf_right (L := L) (s := s) U V) (sup_inf_eq (L := L) (s := s) U V) q _ _ h₁ h₂
  have hGce := isQuasicoherent_twist (L := L) _ (isQuasicoherent_twist (L := L) G hG c) e
  obtain ⟨f, ζ, hζ⟩ := hEUV _ (inf_inf_le U V) (inf_inf_distrib_right U V N).symm _ hGce γ
  have hres := res_delta le_sup_left le_sup_right rfl (le_sup_inf_left (L := L) (s := s) U V)
    (le_sup_inf_right (L := L) (s := s) U V) (sup_inf_eq (L := L) (s := s) U V) inf_le_left
    inf_le_left (inf_le_left : (U ⊔ V) ⊓ N ≤ U ⊔ V) q _ ζ
  have hδ := delta_map (le_sup_inf_left (L := L) (s := s) U V)
    (le_sup_inf_right (L := L) (s := s) U V) (sup_inf_eq (L := L) (s := s) U V) q
    (mul X L s (twist X L (twist X L G (c : ℤ)) (e : ℤ)) f) γ
  have e1 := hres.symm.trans ((congrArg (ConcreteCategory.hom (deltaH _ _ _
    (le_sup_inf_left (L := L) (s := s) U V) (le_sup_inf_right (L := L) (s := s) U V)
    (sup_inf_eq (L := L) (s := s) U V) q _)) hζ).trans (hδ.trans (congrArg (ConcreteCategory.hom
      ((Hfunctor X.ringCatSheaf ((U ⊔ V) ⊓ N : X.Opens) (q + 1)).map
        (mul X L s (twist X L (twist X L G (c : ℤ)) (e : ℤ)) f))) hγ)))
  have key := map_sub_eq_aux _ _ _ _ _ _
    (res_map hT (q + 1) (mul X L s (twist X L (twist X L G (c : ℤ)) (e : ℤ)) f) Ξ) e1
  obtain ⟨ξ₁, hξ₁⟩ := exists_extension_add hT e f _ _ key
  obtain ⟨ξ₂, hξ₂⟩ := exists_extension_add hT c (e + f) η ξ₁ hξ₁
  exact ⟨c + (e + f), ξ₂, hξ₂⟩

end Stacks.Cohomology.SectionPowerAnnihilation

end
