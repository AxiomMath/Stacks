module

public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.PowerComposition
public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.Elements
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.AffineBaseCase

/-!
# The Mayer--Vietoris step for powers of a section acting on cohomology

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module and `s ∈ Γ(X, ℒ)`. For an open `W` and a
degree `n` consider the two properties

* `Annihilates W n`: every class `ξ ∈ Hⁿ(W, 𝒢)` of a quasi-coherent module restricting to zero
  on `W ∩ X_s` satisfies `sᵏ ξ = 0` in `Hⁿ(W, 𝒢 ⊗ ℒ^{⊗ k})` for some `k`;
* `Extends W n`: for every class `η ∈ Hⁿ(W ∩ X_s, 𝒢)` of a quasi-coherent module some `sᵏ η` is the
  restriction of a class of `Hⁿ(W, 𝒢 ⊗ ℒ^{⊗ k})`.

Together, in every degree, they say that the canonical map
`H^n_*(W, ℒ, 𝒢)₍s₎ ⟶ Hⁿ(W ∩ X_s, 𝒢)` of [Stacks, Tag 09MR] is bijective. This file proves that
the annihilation property passes from `U`, `V` and `U ∩ V` to `U ∪ V`, by the five lemma on the
two Mayer--Vietoris sequences of `U ∪ V` and of `(U ∪ V) ∩ X_s`, which is the injectivity half of
the induction step in the proof of [Stacks, Tag 09MR]; the extension property is
`StacksFrontier/AlgebraicGeometry/SectionPowerCohomology/MayerVietorisExtension.lean`.

## Main results

* `Stacks.Cohomology.SectionPowerAnnihilation.annihilates_sup_zero` and
  `Stacks.Cohomology.SectionPowerAnnihilation.annihilates_sup_succ`: the induction step for the
  annihilation property.
* `Stacks.Cohomology.SectionPowerAnnihilation.exists_extension_of_le`: an extension at one power of
  `s` gives one at every higher power.

## References

* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
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

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

variable (s : L.sections)

variable {X} in
/-- Restriction of cohomology along an inclusion of opens of `X`. -/
abbrev resH {T T' : X.Opens} (h : T' ≤ T) (n : ℕ) (G : X.Modules) :
    Hgroup X.ringCatSheaf T n G ⟶ Hgroup X.ringCatSheaf T' n G :=
  Hrestrict X.ringCatSheaf h n G

variable {X} in
/-- The connecting map of the Mayer--Vietoris sequence of a cover `U ∪ V = W` of opens of `X`. -/
abbrev deltaH (W U V : X.Opens) (hU : U ≤ W) (hV : V ≤ W) (hUV : U ⊔ V = W) (n : ℕ)
    (G : X.Modules) :
    Hgroup X.ringCatSheaf (U ⊓ V : X.Opens) n G ⟶ Hgroup X.ringCatSheaf W (n + 1) G :=
  (ambientDelta X.ringCatSheaf W U V hU hV hUV n).app G

/-- **Every class over `W` of a quasi-coherent module restricting to zero on `W ∩ X_s` is killed
by a power of `s`**, in degree `n`. -/
def Annihilates (W : X.Opens) (n : ℕ) : Prop :=
  ∀ (T : X.Opens) (hT : T ≤ W), T = W ⊓ nonvanishingOpen L s →
    ∀ (G : X.Modules), G.IsQuasicoherent → ∀ ξ : Hgroup X.ringCatSheaf W n G,
      resH hT n G ξ = 0 →
        ∃ k : ℕ, (Hfunctor X.ringCatSheaf W n).map (mul X L s G k) ξ = 0

/-- **For every class `η` over `W ∩ X_s` of a quasi-coherent module, some `sᵏ η` extends to `W`**,
in degree `n`. -/
def Extends (W : X.Opens) (n : ℕ) : Prop :=
  ∀ (T : X.Opens) (hT : T ≤ W), T = W ⊓ nonvanishingOpen L s →
    ∀ (G : X.Modules), G.IsQuasicoherent → ∀ η : Hgroup X.ringCatSheaf T n G,
      ∃ (k : ℕ) (ξ : Hgroup X.ringCatSheaf W n (twist X L G (k : ℤ))),
        resH hT n _ ξ = (Hfunctor X.ringCatSheaf T n).map (mul X L s G k) η

variable {X L s}

/-! ### The Mayer--Vietoris sequence on a scheme, on classes -/

section MayerVietoris

variable {W U V : X.Opens} (hU : U ≤ W) (hV : V ≤ W) (hUV : U ⊔ V = W)

/-- Restricting from `T` to `T'` and then to `T''` is restricting from `T` to `T''`. -/
theorem res_res {T T' T'' : X.Opens} (h₁ : T' ≤ T) (h₂ : T'' ≤ T') (n : ℕ) (G : X.Modules)
    (ξ : Hgroup X.ringCatSheaf T n G) :
    resH h₂ n G (resH h₁ n G ξ) =
      resH (h₂.trans h₁) n G ξ :=
  hrestrict_hrestrict X.ringCatSheaf h₁ h₂ n G ξ

/-- Restriction of cohomology commutes with the map induced by a morphism of modules. -/
theorem res_map {T T' : X.Opens} (h : T' ≤ T) (n : ℕ) {G G' : X.Modules} (φ : G ⟶ G')
    (ξ : Hgroup X.ringCatSheaf T n G) :
    resH h n G' ((Hfunctor X.ringCatSheaf T n).map φ ξ) =
      (Hfunctor X.ringCatSheaf T' n).map φ (resH h n G ξ) :=
  hrestrict_map X.ringCatSheaf h n φ ξ

/-- The Mayer--Vietoris connecting map commutes with the map induced by a morphism of modules. -/
theorem delta_map (n : ℕ) {G G' : X.Modules} (φ : G ⟶ G')
    (τ : Hgroup X.ringCatSheaf (U ⊓ V : X.Opens) n G) :
    deltaH W U V hU hV hUV n G'
        ((Hfunctor X.ringCatSheaf (U ⊓ V : X.Opens) n).map φ τ) =
      (Hfunctor X.ringCatSheaf W (n + 1)).map φ
        (deltaH W U V hU hV hUV n G τ) :=
  ambientDelta_map X.ringCatSheaf U V G W hU hV hUV n φ τ

/-- The Mayer--Vietoris connecting maps of the covers `U ∪ V = W` and `U' ∪ V' = W'`, with
`U' ≤ U`, `V' ≤ V` and `W' ≤ W`, commute with restriction. -/
theorem res_delta {W' U' V' : X.Opens} (hU' : U' ≤ W') (hV' : V' ≤ W') (hUV' : U' ⊔ V' = W')
    (kU : U' ≤ U) (kV : V' ≤ V) (kW : W' ≤ W) (n : ℕ) (G : X.Modules)
    (τ : Hgroup X.ringCatSheaf (U ⊓ V : X.Opens) n G) :
    deltaH W' U' V' hU' hV' hUV' n G
        (resH (inf_le_inf kU kV) n G τ) =
      resH kW (n + 1) G
        (deltaH W U V hU hV hUV n G τ) :=
  hrestrict_ambientDelta X.ringCatSheaf hU hV hUV hU' hV' hUV' kU kV kW n G τ

include hUV in
/-- A class over `W` restricting to zero on `U` and on `V` is the image of a class over `U ∩ V`
under the Mayer--Vietoris connecting map. -/
theorem exists_delta_eq (n : ℕ) (G : X.Modules) (ξ : Hgroup X.ringCatSheaf W (n + 1) G)
    (hξU : resH hU (n + 1) G ξ = 0)
    (hξV : resH hV (n + 1) G ξ = 0) :
    ∃ τ : Hgroup X.ringCatSheaf (U ⊓ V : X.Opens) n G,
      deltaH W U V hU hV hUV n G τ = ξ :=
  exists_ambientDelta_eq X.ringCatSheaf U V G W hU hV hUV n ξ hξU hξV

include hUV in
/-- A class over `U ∩ V` killed by the Mayer--Vietoris connecting map is `α| - β|` for classes `α`
over `U` and `β` over `V`. -/
theorem exists_sub_of_delta_eq_zero (n : ℕ) (G : X.Modules)
    (τ : Hgroup X.ringCatSheaf (U ⊓ V : X.Opens) n G)
    (hτ : deltaH W U V hU hV hUV n G τ = 0) :
    ∃ (α : Hgroup X.ringCatSheaf U n G) (β : Hgroup X.ringCatSheaf V n G),
      resH inf_le_left n G α - resH inf_le_right n G β =
        τ :=
  exists_sub_of_ambientDelta_eq_zero X.ringCatSheaf hU hV hUV n G τ hτ

include hUV in
/-- The Mayer--Vietoris connecting map kills `α| - β|` for classes `α` over `U` and `β` over
`V`. -/
theorem delta_sub_eq_zero (n : ℕ) (G : X.Modules) (α : Hgroup X.ringCatSheaf U n G)
    (β : Hgroup X.ringCatSheaf V n G) :
    deltaH W U V hU hV hUV n G
      (resH inf_le_left n G α -
        resH inf_le_right n G β) = 0 :=
  ambientDelta_sub_eq_zero X.ringCatSheaf hU hV hUV n G α β

include hUV in
/-- Classes over `U` and `V` with equal restrictions to `U ∩ V` are the restrictions of one class
over `W`. -/
theorem exists_res_eq (n : ℕ) (G : X.Modules) (α : Hgroup X.ringCatSheaf U n G)
    (β : Hgroup X.ringCatSheaf V n G)
    (h : resH inf_le_left n G α =
      resH inf_le_right n G β) :
    ∃ ξ : Hgroup X.ringCatSheaf W n G,
      resH hU n G ξ = α ∧ resH hV n G ξ = β :=
  exists_restrict_eq_of_restrict_eq X.ringCatSheaf hU hV hUV n G α β h

include hUV in
/-- A degree-zero class over `W` restricting to zero on `U` and on `V` is zero. -/
theorem eq_zero_of_res_eq_zero (G : X.Modules) (ξ : Hgroup X.ringCatSheaf W 0 G)
    (hξU : resH hU 0 G ξ = 0) (hξV : resH hV 0 G ξ = 0) :
    ξ = 0 :=
  eq_zero_of_restrict_eq_zero X.ringCatSheaf U V G W hU hV hUV ξ hξU hξV

end MayerVietoris

/-- Every twist of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_twist (G : X.Modules) (hG : G.IsQuasicoherent) (k : ℕ) :
    (twist X L G (k : ℤ)).IsQuasicoherent :=
  have := hG
  Stacks.Cohomology.TwistedLocalization.isQuasicoherent_twistedModule X L G (k : ℤ)

/-- A class restricting to zero on `T` restricts to zero on every smaller open. -/
theorem hrestrict_eq_zero_of_le {n : ℕ} {G : X.Modules} {W T T' : X.Opens} (hT : T ≤ W)
    (hT' : T' ≤ W) (h : T' ≤ T) (ξ : Hgroup X.ringCatSheaf W n G)
    (hξ : resH hT n G ξ = 0) : resH hT' n G ξ = 0 := by
  calc resH hT' n G ξ
      = resH h n G (resH hT n G ξ) := (res_res hT h n G ξ).symm
    _ = resH h n G 0 := congrArg _ hξ
    _ = 0 := map_zero _

/-- `s^{a + b} ξ` is `sᵇ (sᵃ ξ)`, read through the identification of the twists. -/
private theorem map_mul_add_aux {W : X.Opens} {n : ℕ} (G : X.Modules) (a b : ℕ)
    (ξ : Hgroup X.ringCatSheaf W n G) :
    (Hfunctor X.ringCatSheaf W n).map (mul X L s G (a + b)) ξ =
      (Hfunctor X.ringCatSheaf W n).map (assocHom X L G a b)
        ((Hfunctor X.ringCatSheaf W n).map (mul X L s (twist X L G (a : ℤ)) b)
          ((Hfunctor X.ringCatSheaf W n).map (mul X L s G a) ξ)) := by
  have h3 := map_comp_apply X.ringCatSheaf n W (mul X L s G a)
    (mul X L s (twist X L G (a : ℤ)) b ≫ assocHom X L G a b) ξ
  have h4 := map_comp_apply X.ringCatSheaf n W (mul X L s (twist X L G (a : ℤ)) b)
    (assocHom X L G a b) ((Hfunctor X.ringCatSheaf W n).map (mul X L s G a) ξ)
  have h5 := congrArg (fun φ => (Hfunctor X.ringCatSheaf W n).map φ ξ) (mul_comp X L s G a b)
  exact h5.symm.trans (h3.trans h4)

/-- **Raising the exponent of an extension.** If `sᵇ (sᵃ η)` extends to `W` then so does
`s^{a + b} η`. -/
theorem exists_extension_add {n : ℕ} {G : X.Modules} {W T : X.Opens} (hT : T ≤ W) (a b : ℕ)
    (η : Hgroup X.ringCatSheaf T n G)
    (ξ : Hgroup X.ringCatSheaf W n (twist X L (twist X L G (a : ℤ)) (b : ℤ)))
    (hξ : resH hT n _ ξ =
      (Hfunctor X.ringCatSheaf T n).map (mul X L s (twist X L G (a : ℤ)) b)
        ((Hfunctor X.ringCatSheaf T n).map (mul X L s G a) η)) :
    ∃ ξ' : Hgroup X.ringCatSheaf W n (twist X L G ((a + b : ℕ) : ℤ)),
      resH hT n _ ξ' =
        (Hfunctor X.ringCatSheaf T n).map (mul X L s G (a + b)) η := by
  refine ⟨(Hfunctor X.ringCatSheaf W n).map (assocHom X L G a b) ξ, ?_⟩
  rw [res_map, hξ, map_mul_add_aux]

/-- **An extension at one exponent gives one at every higher exponent.** -/
theorem exists_extension_of_le {n : ℕ} {G : X.Modules} {W T : X.Opens} (hT : T ≤ W) {a k : ℕ}
    (hak : a ≤ k) (η : Hgroup X.ringCatSheaf T n G)
    (ξ : Hgroup X.ringCatSheaf W n (twist X L G (a : ℤ)))
    (hξ : resH hT n _ ξ =
      (Hfunctor X.ringCatSheaf T n).map (mul X L s G a) η) :
    ∃ ξ' : Hgroup X.ringCatSheaf W n (twist X L G (k : ℤ)),
      resH hT n _ ξ' =
        (Hfunctor X.ringCatSheaf T n).map (mul X L s G k) η := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hak
  refine exists_extension_add hT a b η
    ((Hfunctor X.ringCatSheaf W n).map (mul X L s (twist X L G (a : ℤ)) b) ξ) ?_
  exact (res_map hT n _ ξ).trans (congrArg (ConcreteCategory.hom
    ((Hfunctor X.ringCatSheaf T n).map (mul X L s (twist X L G (a : ℤ)) b))) hξ)

/-! ### The induction step -/

section Step

variable (U V : X.Opens)

/-- The open `X_s` where `s` does not vanish. -/
local notation "N" => nonvanishingOpen L s

/-- Two composites of restrictions from `T` to `T'` agree. -/
theorem res_res_eq {T T₁ T₂ T' : X.Opens} (h₁ : T₁ ≤ T) (h₁' : T' ≤ T₁) (h₂ : T₂ ≤ T)
    (h₂' : T' ≤ T₂) (n : ℕ) (G : X.Modules) (ξ : Hgroup X.ringCatSheaf T n G) :
    resH h₁' n G (resH h₁ n G ξ) =
      resH h₂' n G (resH h₂ n G ξ) :=
  (res_res h₁ h₁' n G ξ).trans (res_res h₂ h₂' n G ξ).symm

/-- If `U` and `V` annihilate, a class over `U ∪ V` vanishing on `(U ∪ V) ∩ X_s` has some power
`sᵏ ξ` vanishing on both `U` and `V`. -/
private theorem exists_res_mul_eq_zero {n : ℕ} (hU : Annihilates X L s U n)
    (hV : Annihilates X L s V n) (G : X.Modules) (hG : G.IsQuasicoherent)
    (ξ : Hgroup X.ringCatSheaf (U ⊔ V : X.Opens) n G)
    (hξ : resH (inf_le_left : (U ⊔ V) ⊓ N ≤ U ⊔ V) n G ξ = 0) :
    ∃ k : ℕ, resH le_sup_left n _ ((Hfunctor X.ringCatSheaf (U ⊔ V : X.Opens) n).map
        (mul X L s G k) ξ) = 0 ∧
      resH le_sup_right n _ ((Hfunctor X.ringCatSheaf (U ⊔ V : X.Opens) n).map
        (mul X L s G k) ξ) = 0 := by
  have hξU : resH (inf_le_left : U ⊓ N ≤ U) n G (resH le_sup_left n G ξ) = 0 := by
    rw [res_res_eq le_sup_left inf_le_left inf_le_left (inf_le_inf_right _ le_sup_left), hξ,
      map_zero]
  have hξV : resH (inf_le_left : V ⊓ N ≤ V) n G (resH le_sup_right n G ξ) = 0 := by
    rw [res_res_eq le_sup_right inf_le_left inf_le_left (inf_le_inf_right _ le_sup_right), hξ,
      map_zero]
  obtain ⟨k₁, hk₁⟩ := hU (U ⊓ N) inf_le_left rfl G hG _ hξU
  obtain ⟨k₂, hk₂⟩ := hV (V ⊓ N) inf_le_left rfl G hG _ hξV
  refine ⟨k₁ + k₂, (res_map _ n _ ξ).trans ?_, (res_map _ n _ ξ).trans ?_⟩
  · exact map_eq_zero_of_le X L s U n G (Nat.le_add_right k₁ k₂) _ hk₁
  · exact map_eq_zero_of_le X L s V n G (Nat.le_add_left k₂ k₁) _ hk₂

/-- **The induction step for the annihilation property in degree zero.** -/
theorem annihilates_sup_zero (hU : Annihilates X L s U 0) (hV : Annihilates X L s V 0) :
    Annihilates X L s (U ⊔ V) 0 := by
  intro T hT hTeq G hG ξ hξ
  subst hTeq
  obtain ⟨k, h₁, h₂⟩ := exists_res_mul_eq_zero U V hU hV G hG ξ hξ
  exact ⟨k, eq_zero_of_res_eq_zero le_sup_left le_sup_right rfl _ _ h₁ h₂⟩

/-- `U ∩ X_s ⊆ (U ∪ V) ∩ X_s`. -/
theorem le_sup_inf_left : U ⊓ N ≤ (U ⊔ V) ⊓ N := inf_le_inf_right _ le_sup_left

/-- `V ∩ X_s ⊆ (U ∪ V) ∩ X_s`. -/
theorem le_sup_inf_right : V ⊓ N ≤ (U ⊔ V) ⊓ N := inf_le_inf_right _ le_sup_right

/-- `(U ∩ X_s) ∪ (V ∩ X_s) = (U ∪ V) ∩ X_s`. -/
theorem sup_inf_eq : U ⊓ N ⊔ V ⊓ N = (U ⊔ V) ⊓ N := (inf_sup_right _ _ _).symm

/-- `(U ∩ X_s) ∩ (V ∩ X_s) ⊆ U ∩ V`. -/
theorem inf_inf_le : U ⊓ N ⊓ (V ⊓ N) ≤ U ⊓ V := inf_le_inf inf_le_left inf_le_left

/-- The Mayer--Vietoris connecting map of the cover `U ∩ X_s, V ∩ X_s` of `(U ∪ V) ∩ X_s`. -/
abbrev delta' (q : ℕ) (G : X.Modules) :=
  deltaH _ _ _ (le_sup_inf_left (L := L) (s := s) U V)
    (le_sup_inf_right (L := L) (s := s) U V) (sup_inf_eq (L := L) (s := s) U V) q G

/-- The Mayer--Vietoris connecting map of the cover `U, V` of `U ∪ V`. -/
abbrev delta (q : ℕ) (G : X.Modules) :=
  deltaH (U ⊔ V) U V le_sup_left le_sup_right rfl q G

/-- **First step**: a class over `U ∪ V` restricting to zero on `(U ∪ V) ∩ X_s` becomes, after
multiplication by a power of `s`, the image `δ τ` of a class over `U ∩ V` with `δ'(τ|) = 0`. -/
theorem exists_delta_of_annihilates (q : ℕ) (hU : Annihilates X L s U (q + 1))
    (hV : Annihilates X L s V (q + 1)) (G : X.Modules) (hG : G.IsQuasicoherent)
    (ξ : Hgroup X.ringCatSheaf (U ⊔ V : X.Opens) (q + 1) G)
    (hξ : resH (inf_le_left : (U ⊔ V) ⊓ N ≤ U ⊔ V) (q + 1) G ξ = 0) :
    ∃ (k : ℕ) (τ : Hgroup X.ringCatSheaf (U ⊓ V : X.Opens) q (twist X L G (k : ℤ))),
      delta U V q _ τ = (Hfunctor X.ringCatSheaf (U ⊔ V : X.Opens) (q + 1)).map (mul X L s G k) ξ ∧
      delta' (L := L) (s := s) U V q _
        (resH (inf_inf_le (L := L) (s := s) U V) q _ τ) = 0 := by
  obtain ⟨k, e₁, e₂⟩ := exists_res_mul_eq_zero U V hU hV G hG ξ hξ
  obtain ⟨τ, hτ⟩ := exists_delta_eq le_sup_left le_sup_right rfl q _ _ e₁ e₂
  refine ⟨k, τ, hτ, ?_⟩
  refine (res_delta le_sup_left le_sup_right rfl (le_sup_inf_left U V) (le_sup_inf_right U V)
    (sup_inf_eq U V) inf_le_left inf_le_left inf_le_left q _ τ).trans ?_
  rw [hτ, res_map, hξ, map_zero]

/-- `s^{a + b} ξ` is `sᵇ (sᵃ ξ)`, read through the identification of the twists. -/
theorem map_mul_add (W : X.Opens) (n : ℕ) (G : X.Modules) (a b : ℕ)
    (ξ : Hgroup X.ringCatSheaf W n G) :
    (Hfunctor X.ringCatSheaf W n).map (mul X L s G (a + b)) ξ =
      (Hfunctor X.ringCatSheaf W n).map (assocHom X L G a b)
        ((Hfunctor X.ringCatSheaf W n).map (mul X L s (twist X L G (a : ℤ)) b)
          ((Hfunctor X.ringCatSheaf W n).map (mul X L s G a) ξ)) :=
  map_mul_add_aux G a b ξ

/-- Extensions of two classes with a common exponent. -/
theorem exists_extensions (q : ℕ) (hEU : Extends X L s U q) (hEV : Extends X L s V q)
    (G : X.Modules) (hG : G.IsQuasicoherent) (α : Hgroup X.ringCatSheaf (U ⊓ N : X.Opens) q G)
    (β : Hgroup X.ringCatSheaf (V ⊓ N : X.Opens) q G) :
    ∃ (c : ℕ) (ξα : Hgroup X.ringCatSheaf U q (twist X L G (c : ℤ)))
      (ξβ : Hgroup X.ringCatSheaf V q (twist X L G (c : ℤ))),
      resH inf_le_left q _ ξα =
          (Hfunctor X.ringCatSheaf (U ⊓ N : X.Opens) q).map (mul X L s G c) α ∧
        resH inf_le_left q _ ξβ =
          (Hfunctor X.ringCatSheaf (V ⊓ N : X.Opens) q).map (mul X L s G c) β := by
  obtain ⟨a, ξα, hξα⟩ := hEU (U ⊓ N) inf_le_left rfl G hG α
  obtain ⟨b, ξβ, hξβ⟩ := hEV (V ⊓ N) inf_le_left rfl G hG β
  obtain ⟨ξα', hξα'⟩ := exists_extension_of_le inf_le_left (Nat.le_add_right a b) α ξα hξα
  obtain ⟨ξβ', hξβ'⟩ := exists_extension_of_le inf_le_left (Nat.le_add_left b a) β ξβ hξβ
  exact ⟨a + b, ξα', ξβ', hξα', hξβ'⟩

/-- If `f b = d` and `f c = d` for an additive map `f`, then `f (b - c) = 0`. -/
theorem sub_eq_zero_aux {B D : Type*} [AddCommGroup B] [AddCommGroup D] (f : B →+ D) (b c : B)
    (d : D) (hb : f b = d) (hc : f c = d) : f (b - c) = 0 := by
  rw [map_sub, hb, hc, sub_self]

/-- If `f x = μ rτ`, `f b = μ rα`, `f c = μ rβ` and `rα - rβ = rτ` for additive maps `f` and `μ`,
then `f (x - (b - c)) = 0`. -/
theorem sub_sub_eq_zero_aux {B C D : Type*} [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] (f : B →+ D) (μ : C →+ D) (x b c : B) (rα rβ rτ : C) (hx : f x = μ rτ)
    (hb : f b = μ rα) (hc : f c = μ rβ) (h : rα - rβ = rτ) : f (x - (b - c)) = 0 := by
  rw [map_sub, map_sub, hx, hb, hc, ← map_sub, h, sub_self]

/-- The difference `sᶜ τ - (ξα| - ξβ|)` restricts to zero on `(U ∩ X_s) ∩ (V ∩ X_s)`. -/
theorem res_sub_eq_zero (q : ℕ) (G : X.Modules) (c : ℕ)
    (τ : Hgroup X.ringCatSheaf (U ⊓ V : X.Opens) q G)
    (α : Hgroup X.ringCatSheaf (U ⊓ N : X.Opens) q G)
    (β : Hgroup X.ringCatSheaf (V ⊓ N : X.Opens) q G)
    (hαβ : resH inf_le_left q G α - resH inf_le_right q G β =
      resH (inf_inf_le (L := L) (s := s) U V) q G τ)
    (ξα : Hgroup X.ringCatSheaf U q (twist X L G (c : ℤ)))
    (ξβ : Hgroup X.ringCatSheaf V q (twist X L G (c : ℤ)))
    (hξα : resH inf_le_left q _ ξα =
      (Hfunctor X.ringCatSheaf (U ⊓ N : X.Opens) q).map (mul X L s G c) α)
    (hξβ : resH inf_le_left q _ ξβ =
      (Hfunctor X.ringCatSheaf (V ⊓ N : X.Opens) q).map (mul X L s G c) β) :
    resH (inf_inf_le (L := L) (s := s) U V) q _
      ((Hfunctor X.ringCatSheaf (U ⊓ V : X.Opens) q).map (mul X L s G c) τ -
        (resH inf_le_left q _ ξα -
          resH inf_le_right q _ ξβ)) = 0 := by
  have eA := res_map (inf_inf_le (L := L) (s := s) U V) q (mul X L s G c) τ
  have eB0 := res_res_eq (inf_le_left : U ⊓ V ≤ U) (inf_inf_le (L := L) (s := s) U V)
    (inf_le_left : U ⊓ N ≤ U) (inf_le_left : U ⊓ N ⊓ (V ⊓ N) ≤ U ⊓ N) q _ ξα
  rw [hξα, res_map] at eB0
  have eC0 := res_res_eq (inf_le_right : U ⊓ V ≤ V) (inf_inf_le (L := L) (s := s) U V)
    (inf_le_left : V ⊓ N ≤ V) (inf_le_right : U ⊓ N ⊓ (V ⊓ N) ≤ V ⊓ N) q _ ξβ
  rw [hξβ, res_map] at eC0
  exact sub_sub_eq_zero_aux _ _ _ _ _ _ _ _ eA eB0 eC0 hαβ

/-- **Second step**: a class `τ` over `U ∩ V` with `δ'(τ|) = 0` satisfies `δ (sᵐ τ) = 0` for some
`m`, given the extension property on `U` and `V` and the annihilation property on `U ∩ V`. -/
theorem exists_delta_mul_eq_zero (q : ℕ) (hEU : Extends X L s U q) (hEV : Extends X L s V q)
    (hUV : Annihilates X L s (U ⊓ V) q) (G : X.Modules) (hG : G.IsQuasicoherent)
    (τ : Hgroup X.ringCatSheaf (U ⊓ V : X.Opens) q G)
    (hτ : delta' (L := L) (s := s) U V q G
      (resH (inf_inf_le (L := L) (s := s) U V) q G τ) = 0) :
    ∃ m : ℕ,
      delta U V q _ ((Hfunctor X.ringCatSheaf (U ⊓ V : X.Opens) q).map (mul X L s G m) τ) = 0 := by
  obtain ⟨α, β, hαβ⟩ := exists_sub_of_delta_eq_zero (le_sup_inf_left U V)
    (le_sup_inf_right U V) (sup_inf_eq U V) q G _ hτ
  obtain ⟨c, ξα, ξβ, hξα, hξβ⟩ := exists_extensions U V q hEU hEV G hG α β
  have hZ0 := res_sub_eq_zero U V q G c τ α β hαβ ξα ξβ hξα hξβ
  obtain ⟨e, he⟩ := hUV _ (inf_inf_le U V) (inf_inf_distrib_right U V N).symm _
    (isQuasicoherent_twist (L := L) G hG c) _ hZ0
  rw [map_sub, map_sub, ← res_map, ← res_map, sub_eq_zero] at he
  have hδ := delta_sub_eq_zero le_sup_left le_sup_right rfl q _
    ((Hfunctor X.ringCatSheaf U q).map (mul X L s _ e) ξα)
    ((Hfunctor X.ringCatSheaf V q).map (mul X L s _ e) ξβ)
  rw [← he] at hδ
  refine ⟨c + e, ?_⟩
  rw [map_mul_add, delta_map, hδ, map_zero]

/-- **The induction step for the annihilation property in positive degree.** -/
theorem annihilates_sup_succ (q : ℕ) (hU : Annihilates X L s U (q + 1))
    (hV : Annihilates X L s V (q + 1)) (hEU : Extends X L s U q) (hEV : Extends X L s V q)
    (hUV : Annihilates X L s (U ⊓ V) q) : Annihilates X L s (U ⊔ V) (q + 1) := by
  intro T hT hTeq G hG ξ hξ
  subst hTeq
  obtain ⟨k, τ, hτ, hτ'⟩ := exists_delta_of_annihilates U V q hU hV G hG ξ hξ
  obtain ⟨m, hm⟩ := exists_delta_mul_eq_zero U V q hEU hEV hUV _
    (isQuasicoherent_twist (L := L) G hG k) τ hτ'
  rw [delta_map, hτ] at hm
  exact ⟨k + m, map_add_eq_zero X L s (U ⊔ V) (q + 1) G k m ξ hm⟩

end Step

end Stacks.Cohomology.SectionPowerAnnihilation

end
