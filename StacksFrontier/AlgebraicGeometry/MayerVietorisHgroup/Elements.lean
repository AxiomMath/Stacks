module

public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.Restriction
public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.Classes

/-!
# The Mayer--Vietoris sequence over an ambient open, on cohomology classes

Let `X` be a topological space, `O` a sheaf of rings on `X` and `U ⊔ V = W` an open cover of an
open `W`. This file reads the exactness of the Mayer--Vietoris long exact sequence

`⋯ ⟶ Hⁿ(W,F) ⟶ Hⁿ(U,F) ⊞ Hⁿ(V,F) ⟶ Hⁿ(U ⊓ V,F) ⟶ Hⁿ⁺¹(W,F) ⟶ ⋯`

of `StacksFrontier/AlgebraicGeometry/MayerVietorisHgroup/AmbientOpen.lean` on cohomology classes,
with the two non-connecting maps written as restrictions.

## Main results

* `Stacks.Cohomology.AmbientMayerVietoris.exists_ambientDelta_eq`: a class over `W` restricting
  to zero on `U` and on `V` is in the image of the connecting map.
* `Stacks.Cohomology.AmbientMayerVietoris.exists_sub_of_ambientDelta_eq_zero`: a class over
  `U ⊓ V` killed by the connecting map is a difference of restrictions from `U` and from `V`.
* `Stacks.Cohomology.AmbientMayerVietoris.ambientDelta_sub_eq_zero`: the connecting map kills
  such differences.
* `Stacks.Cohomology.AmbientMayerVietoris.exists_restrict_eq_of_restrict_eq`: classes over `U`
  and over `V` agreeing on `U ⊓ V` come from one class over `W`.
* `Stacks.Cohomology.AmbientMayerVietoris.eq_zero_of_restrict_eq_zero`: in degree zero a class
  over `W` restricting to zero on `U` and on `V` is zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology

universe u

namespace Stacks.Cohomology.AmbientMayerVietoris

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)]
  {W U V : Opens X} (hU : U ≤ W) (hV : V ≤ W) (hUV : U ⊔ V = W)

/-- Equal natural transformations of additive-group-valued functors agree on elements. -/
private theorem app_apply_congr {C : Type*} [Category C] {F F' : C ⥤ AddCommGrpCat.{u}}
    {φ ψ : F ⟶ F'} (h : φ = ψ) (G : C) (x : F.obj G) : φ.app G x = ψ.app G x := by
  rw [h]

/-- The restriction map on cohomology, applied to a class. -/
theorem hrestrictNT_app_apply {T T' : Opens X} (h : T' ≤ T) (n : ℕ) (G : SheafOfModules.{u} O)
    (ξ : Hgroup O T n G) : (HrestrictNT O h n).app G ξ = Hrestrict O h n G ξ := rfl

/-- **Restriction is transitive, on classes.** -/
theorem hrestrict_hrestrict {T T' T'' : Opens X} (h₁ : T' ≤ T) (h₂ : T'' ≤ T') (n : ℕ)
    (G : SheafOfModules.{u} O) (ξ : Hgroup O T n G) :
    Hrestrict O h₂ n G (Hrestrict O h₁ n G ξ) = Hrestrict O (h₂.trans h₁) n G ξ := by
  exact app_apply_congr (hrestrictNT_comp O h₁ h₂ n) G ξ

/-- **The connecting map commutes with restriction to a smaller cover, on classes.** -/
theorem hrestrict_ambientDelta {W' U' V' : Opens X} (hU' : U' ≤ W') (hV' : V' ≤ W')
    (hUV' : U' ⊔ V' = W') (kU : U' ≤ U) (kV : V' ≤ V) (kW : W' ≤ W) (n : ℕ)
    (G : SheafOfModules.{u} O) (τ : Hgroup O (U ⊓ V) n G) :
    (ambientDelta O W' U' V' hU' hV' hUV' n).app G (Hrestrict O (inf_le_inf kU kV) n G τ) =
      Hrestrict O kW (n + 1) G ((ambientDelta O W U V hU hV hUV n).app G τ) := by
  exact congrArg (fun f => f τ)
    (hrestrict_comp_ambientDelta O W U V W' U' V' hU hV hUV hU' hV' hUV' kU kV kW n G)

/-- The first component of the first Mayer--Vietoris map is the restriction to `U`. -/
theorem ambientFirst_fst (n : ℕ) (G : SheafOfModules.{u} O) (ξ : Hgroup O W n G) :
    (biprod.fst : Hfunctor O U n ⊞ Hfunctor O V n ⟶ _).app G
        ((ambientFirst O W U V hU hV n).app G ξ) = Hrestrict O hU n G ξ := by
  have h : ambientFirst O W U V hU hV n ≫ biprod.fst = HrestrictNT O hU n := by
    rw [ambientFirst_eq, biprod.lift_fst]
  exact app_apply_congr h G ξ

/-- The second component of the first Mayer--Vietoris map is the restriction to `V`. -/
theorem ambientFirst_snd (n : ℕ) (G : SheafOfModules.{u} O) (ξ : Hgroup O W n G) :
    (biprod.snd : Hfunctor O U n ⊞ Hfunctor O V n ⟶ _).app G
        ((ambientFirst O W U V hU hV n).app G ξ) = Hrestrict O hV n G ξ := by
  have h : ambientFirst O W U V hU hV n ≫ biprod.snd = HrestrictNT O hV n := by
    rw [ambientFirst_eq, biprod.lift_snd]
  exact app_apply_congr h G ξ

/-- The second Mayer--Vietoris map on the sum of two classes is the difference of their
restrictions. -/
theorem mvSecond_inl_add_inr (n : ℕ) (G : SheafOfModules.{u} O) (α : Hgroup O U n G)
    (β : Hgroup O V n G) :
    (AbsoluteMayerVietoris.mvSecond O U V n).app G
        ((biprod.inl : Hfunctor O U n ⟶ Hfunctor O U n ⊞ Hfunctor O V n).app G α +
          (biprod.inr : Hfunctor O V n ⟶ Hfunctor O U n ⊞ Hfunctor O V n).app G β) =
      Hrestrict O inf_le_left n G α - Hrestrict O inf_le_right n G β := by
  have h₁ : biprod.inl ≫ AbsoluteMayerVietoris.mvSecond O U V n =
      HrestrictNT O (inf_le_left : U ⊓ V ≤ U) n := by
    rw [AbsoluteMayerVietoris.mvSecond_eq, biprod.inl_desc]
  have h₂ : biprod.inr ≫ AbsoluteMayerVietoris.mvSecond O U V n =
      -HrestrictNT O (inf_le_right : U ⊓ V ≤ V) n := by
    rw [AbsoluteMayerVietoris.mvSecond_eq, biprod.inr_desc]
  have e₁ := app_apply_congr h₁ G α
  have e₂ := app_apply_congr h₂ G β
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, NatTrans.app_neg] at e₁ e₂
  rw [map_add, e₁, e₂, sub_eq_add_neg]
  rfl

include hUV in
/-- **Exactness at `Hⁿ(U ⊓ V,F)`.** A class over `U ⊓ V` killed by the connecting map is the
difference of the restrictions of a class over `U` and a class over `V`. -/
theorem exists_sub_of_ambientDelta_eq_zero (n : ℕ) (G : SheafOfModules.{u} O)
    (τ : Hgroup O (U ⊓ V) n G) (hτ : (ambientDelta O W U V hU hV hUV n).app G τ = 0) :
    ∃ (α : Hgroup O U n G) (β : Hgroup O V n G),
      Hrestrict O inf_le_left n G α - Hrestrict O inf_le_right n G β = τ := by
  have hex := (mayerVietorisAmbient_exact O W U V hU hV hUV n G).exact 1
  rw [ShortComplex.ab_exact_iff] at hex
  obtain ⟨x, hx⟩ := hex τ hτ
  refine ⟨(biprod.fst : Hfunctor O U n ⊞ Hfunctor O V n ⟶ _).app G x,
    (biprod.snd : Hfunctor O U n ⊞ Hfunctor O V n ⟶ _).app G x, ?_⟩
  rw [← mvSecond_inl_add_inr, app_biprod_total]
  exact hx

include hUV in
/-- **The connecting map kills differences of restrictions.** -/
theorem ambientDelta_sub_eq_zero (n : ℕ) (G : SheafOfModules.{u} O) (α : Hgroup O U n G)
    (β : Hgroup O V n G) :
    (ambientDelta O W U V hU hV hUV n).app G
      (Hrestrict O inf_le_left n G α - Hrestrict O inf_le_right n G β) = 0 := by
  rw [← mvSecond_inl_add_inr]
  have h : (AbsoluteMayerVietoris.mvSecond O U V n).app G ≫
      (ambientDelta O W U V hU hV hUV n).app G = 0 :=
    (mayerVietorisAmbient_exact O W U V hU hV hUV n G).toIsComplex.zero 1
  rw [← ConcreteCategory.comp_apply, h]
  rfl

include hUV in
/-- **Exactness at `Hⁿ(U,F) ⊞ Hⁿ(V,F)`.** Classes over `U` and over `V` with the same restriction
to `U ⊓ V` are the restrictions of one class over `W`. -/
theorem exists_restrict_eq_of_restrict_eq (n : ℕ) (G : SheafOfModules.{u} O)
    (α : Hgroup O U n G) (β : Hgroup O V n G)
    (h : Hrestrict O inf_le_left n G α = Hrestrict O inf_le_right n G β) :
    ∃ ξ : Hgroup O W n G, Hrestrict O hU n G ξ = α ∧ Hrestrict O hV n G ξ = β := by
  have hex := (mayerVietorisAmbient_exact O W U V hU hV hUV n G).exact 0
  rw [ShortComplex.ab_exact_iff] at hex
  obtain ⟨ξ, hξ'⟩ := hex _ ((mvSecond_inl_add_inr O n G α β).trans (sub_eq_zero.mpr h))
  have hξ : (ambientFirst O W U V hU hV n).app G ξ =
      (biprod.inl : Hfunctor O U n ⟶ Hfunctor O U n ⊞ Hfunctor O V n).app G α +
        (biprod.inr : Hfunctor O V n ⟶ Hfunctor O U n ⊞ Hfunctor O V n).app G β := hξ'
  refine ⟨ξ, ?_, ?_⟩
  · have h₁ := congrArg (fun x => (biprod.fst : Hfunctor O U n ⊞ Hfunctor O V n ⟶ _).app G x)
      hξ
    simp only at h₁
    rw [ambientFirst_fst] at h₁
    rw [h₁, map_add]
    have a := congrArg (fun f => f α) (biprod_inl_fst_app (Hfunctor O U n) (Hfunctor O V n) G)
    have b := congrArg (fun f => f β) (biprod_inr_fst_app (Hfunctor O U n) (Hfunctor O V n) G)
    simp only [ConcreteCategory.comp_apply] at a b
    rw [a, b]
    simp
  · have h₂ := congrArg (fun x => (biprod.snd : Hfunctor O U n ⊞ Hfunctor O V n ⟶ _).app G x)
      hξ
    simp only at h₂
    rw [ambientFirst_snd] at h₂
    rw [h₂, map_add]
    have a := congrArg (fun f => f α) (biprod_inl_snd_app (Hfunctor O U n) (Hfunctor O V n) G)
    have b := congrArg (fun f => f β) (biprod_inr_snd_app (Hfunctor O U n) (Hfunctor O V n) G)
    simp only [ConcreteCategory.comp_apply] at a b
    rw [a, b]
    simp

end Stacks.Cohomology.AmbientMayerVietoris

end
