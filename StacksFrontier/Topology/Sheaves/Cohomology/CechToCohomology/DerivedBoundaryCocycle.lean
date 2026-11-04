module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.RightDerivedConnectingResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.BoundaryCocycle
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneComparison
public import StacksFrontier.Algebra.Homology.Resolution.NatHorseshoe
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# The connecting morphism of sheaf cohomology on Čech cocycles

Let `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` be a short exact sequence of abelian sheaves on a topological space
`X`, let `t ∈ ℱ₃(X)` be a global section, and let `sᵢ ∈ ℱ₂(Uᵢ)` be local lifts of `t` on an open
covering `𝒰` of `X`. The Čech coboundary `s_{i₁} - s_{i₀}` of the lifts is the image of a Čech
`1`-cocycle `ω` of `ℱ₁`. This file proves that the connecting morphism
`H⁰(X, ℱ₃) ⟶ H¹(X, ℱ₁)` of the long exact cohomology sequence — the one attached to the
distinguished triangle of the derived functor `RΓ(X, -)` — sends `t` to the image of the Čech
class of `ω` under the comparison `Ȟ¹(𝒰, ℱ₁) ⟶ H¹(X, ℱ₁)` of [Stacks, Tag 01EQ]. This is the
description of the boundary map in [Stacks, Tag 02AP] (where it is computed by the same
cocycle), identified with the derived-category boundary map.

## Main results

* `Stacks.Cohomology.CechOne.rightDerivedPlusδ_toRightDerivedZero`: **the connecting morphism of
  `RΓ(X, -)` on a global section is the Čech class of the differences of its local lifts.**

## Implementation notes

The proof runs on a compatible short exact sequence `0 → I₁ → I₂ → I₃ → 0` of injective
resolutions, split in each degree ([Stacks, Tag 013T]). By
`Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusδ_resolution` the connecting
morphism is the snake-lemma connecting morphism of `0 → Γ(I₁) → Γ(I₂) → Γ(I₃) → 0`. Lifting the
image of `t` in `Γ(I₃⁰)` to `x₂ ∈ Γ(I₂⁰)` by the splitting, the differences `x₂|_{Uᵢ} - sᵢ` come
from local sections `b'ᵢ` of `I₁⁰`, and `-b'` is a Čech `0`-cochain with coboundary the image of
`ω` whose resolution differential glues to the snake-lemma representative: this is precisely a
representative of the comparison of [Stacks, Tag 01EQ] in the resolution `I₁`.

## References

* [Stacks Project, Tag 02AP](https://stacks.math.columbia.edu/tag/02AP)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 013T](https://stacks.math.columbia.edu/tag/013T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.HigherDirectImagePresheaf

universe u

namespace Stacks.Cohomology.CechOne

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

variable {X : TopCat.{u}}

open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

variable (S : ShortComplex (AbelianSheaf X)) (hS : S.ShortExact)

/-- A cancellation, with every object and morphism a variable so that it applies across the
junction of two presentations of the same object. -/
private theorem cancel_aux {C : Type*} [Category* C] {P Q R T W : C} (a : P ⟶ Q) (b : Q ⟶ R)
    (i : R ⟶ T) (i' : T ⟶ R) (δ : R ⟶ W) (rhs : P ⟶ W) (h : i ≫ i' = 𝟙 _)
    (hδ : a ≫ b ≫ δ = rhs) : (a ≫ b ≫ i) ≫ i' ≫ δ = rhs := by
  simp only [Category.assoc, reassoc_of% h, hδ]

/-- Equal morphisms of abelian sheaves agree on every section. -/
private theorem app_apply_congr {A B : AbelianSheaf X} {φ ψ : A ⟶ B} (h : φ = ψ) (V : Opens X)
    (a) : φ.hom.app (op V) a = ψ.hom.app (op V) a := by
  rw [h]

/-- A morphism of abelian sheaves with a left inverse is injective on sections. -/
theorem injective_app_of_comp_eq_id {A B : AbelianSheaf X} {φ : A ⟶ B} {ψ : B ⟶ A}
    (h : φ ≫ ψ = 𝟙 A) (V : Opens X) : Function.Injective (φ.hom.app (op V)) := by
  intro a a' haa
  have h1 : ψ.hom.app _ (φ.hom.app _ a) = a := app_apply_congr h V a
  have h2 : ψ.hom.app _ (φ.hom.app _ a') = a' := app_apply_congr h V a'
  rw [← h1, ← h2, haa]

section Resolution

variable {S} (I₁ : InjectiveResolution S.X₁) (I₂ : InjectiveResolution S.X₂)
  (I₃ : InjectiveResolution S.X₃)
  (f : I₁.cocomplex ⟶ I₂.cocomplex) (g : I₂.cocomplex ⟶ I₃.cocomplex) (zero : f ≫ g = 0)
  (comm_f : I₁.ι.f 0 ≫ f.f 0 = S.f ≫ I₂.ι.f 0)
  (comm_g : I₂.ι.f 0 ≫ g.f 0 = S.g ≫ I₃.ι.f 0)
  (σ₀ : (ShortComplex.mk (f.f 0) (g.f 0)
    (congrFun (congrArg HomologicalComplex.Hom.f zero) 0)).Splitting)
  (σ₁ : (ShortComplex.mk (f.f 1) (g.f 1)
    (congrFun (congrArg HomologicalComplex.Hom.f zero) 1)).Splitting)
  (hFR : ((ShortComplex.mk f g zero).map
    ((sectionsFunctor X ⊤).mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact)
  (t : S.X₃.val.obj (op ⊤))
  {I : Type u} (Ui : I → Opens X) (hUi : (⊤ : Opens X) = ⨆ i, Ui i)
  (e : CechCochains.Cochain Ui S.X₂.val 0)
  (he : ∀ i : Fin 1 → I, S.g.hom.app (op (CechCochains.inter Ui i)) (e i) =
    S.X₃.val.map (homOfLE le_top).op t)
  (ω : CechCochains.cocycles1 Ui S.X₁.val)
  (hω : ∀ i : Fin 2 → I, S.f.hom.app (op (CechCochains.inter Ui i)) (ω.val i) =
    CechCochains.cechD Ui S.X₂.val 0 e i)

include comm_f comm_g σ₀ σ₁ he hω in
/-- **The snake-lemma connecting morphism of the global sections of a compatible split sequence
of injective resolutions, on a global section, is the Čech class of the differences of its local
lifts.** -/
theorem isoRightDerivedObj_δ_toRightDerivedZero :
    (I₁.isoRightDerivedObj (sectionsFunctor X ⊤) 1).inv
        (hFR.δ 0 1 rfl ((I₃.isoRightDerivedObj (sectionsFunctor X ⊤) 0).hom
          ((sectionsFunctor X ⊤).toRightDerivedZero.app S.X₃ t))) =
      cechH1ToRightDerivedSections X ⊤ Ui hUi S.X₁ (CechCochains.cls Ui S.X₁.val ω) := by
  -- the image of `t` in `Γ(I₃⁰)`, its lift to `Γ(I₂⁰)` and the snake-lemma representative,
  -- as morphisms out of `Γ(ℱ₃)`
  let Γ := sectionsFunctor X ⊤
  let x₃ : Γ.obj S.X₃ ⟶ Γ.obj (I₃.cocomplex.X 0) := Γ.map (I₃.ι.f 0)
  let x₂ : Γ.obj S.X₃ ⟶ Γ.obj (I₂.cocomplex.X 0) := x₃ ≫ Γ.map σ₀.s
  let x₁ : Γ.obj S.X₃ ⟶ Γ.obj (I₁.cocomplex.X 1) :=
    x₂ ≫ Γ.map (I₂.cocomplex.d 0 1) ≫ Γ.map σ₁.r
  have hx₃ : x₃ ≫ Γ.map (I₃.cocomplex.d 0 1) = 0 := by
    have := congrArg Γ.map I₃.ι_f_zero_comp_complex_d
    simp only [Functor.map_comp, Functor.map_zero] at this
    exact this
  have hx₂ : x₂ ≫ Γ.map (g.f 0) = x₃ := by
    have := congrArg Γ.map (I₃.ι.f 0 ≫= σ₀.s_g)
    simp only [Functor.map_comp, Functor.map_id, Category.comp_id, Category.assoc] at this
    exact this
  have hx₁ : x₁ ≫ Γ.map (f.f 1) = x₂ ≫ Γ.map (I₂.cocomplex.d 0 1) := by
    have hid : σ₁.r ≫ f.f 1 = 𝟙 _ - g.f 1 ≫ σ₁.s := eq_sub_of_add_eq σ₁.id
    have hgd : I₃.ι.f 0 ≫ σ₀.s ≫ I₂.cocomplex.d 0 1 ≫ g.f 1 = 0 := by
      rw [← g.comm 0 1, reassoc_of% σ₀.s_g, I₃.ι_f_zero_comp_complex_d]
    have key : I₃.ι.f 0 ≫ σ₀.s ≫ I₂.cocomplex.d 0 1 ≫ σ₁.r ≫ f.f 1 =
        I₃.ι.f 0 ≫ σ₀.s ≫ I₂.cocomplex.d 0 1 := by
      rw [hid, Preadditive.comp_sub, Preadditive.comp_sub, Preadditive.comp_sub,
        Category.comp_id, reassoc_of% hgd, zero_comp, sub_zero]
    have := congrArg Γ.map key
    simp only [Functor.map_comp, Category.assoc] at this
    exact this
  have hδ := hFR.δ_eq 0 1 rfl x₃ hx₃ x₂ hx₂ x₁ hx₁ 2 (by simp)
  set R' := (ShortComplex.mk f g zero).map
    ((sectionsFunctor X ⊤).mapHomologicalComplex (ComplexShape.up ℕ))
  have hx₁d : x₁ ≫ R'.X₁.d 1 2 = 0 := by
    have := hFR.mono_f
    rw [← cancel_mono (R'.f.f 2), Category.assoc, ← R'.f.comm]
    refine ((reassoc_of% hx₁) (R'.X₂.d 1 2)).trans ?_
    show x₂ ≫ R'.X₂.d 0 1 ≫ R'.X₂.d 1 2 = _
    rw [HomologicalComplex.d_comp_d, Limits.comp_zero, Limits.zero_comp]
  have hkey : Γ.toRightDerivedZero.app S.X₃ ≫ (I₃.isoRightDerivedObj Γ 0).hom ≫
      hFR.δ 0 1 rfl = R'.X₁.liftCycles x₁ 2 (by simp) hx₁d ≫
        R'.X₁.homologyπ 1 := by
    rw [I₃.toRightDerivedZero_eq Γ]
    exact cancel_aux _ _ _ _ _ _ (Iso.inv_hom_id _) hδ
  -- the Čech `0`-cochain of `I₁⁰` of the representative
  let xs : CechCochains.Cochain Ui (I₂.cocomplex.X 0).val 0 :=
    fun i => CechCochains.restr _ le_top (x₂ t)
  let y : CechCochains.Cochain Ui (I₂.cocomplex.X 0).val 0 := xs - push Ui (I₂.ι.f 0).hom 0 e
  let b' : CechCochains.Cochain Ui (I₁.cocomplex.X 0).val 0 := push Ui σ₀.r.hom 0 y
  have hx₂t : (g.f 0).hom.app (op ⊤) (x₂ t) = (I₃.ι.f 0).hom.app (op ⊤) t :=
    ConcreteCategory.congr_hom hx₂ t
  have hgy : push Ui (g.f 0).hom 0 y = 0 := by
    funext i
    have h1 : (g.f 0).hom.app _ (xs i) = CechCochains.restr _ le_top
        ((I₃.ι.f 0).hom.app (op ⊤) t) := by
      rw [← hx₂t]
      exact (CechOne.restr_app (g.f 0).hom le_top (x₂ t)).symm
    have h2 : (g.f 0).hom.app _ ((I₂.ι.f 0).hom.app _ (e i)) = CechCochains.restr _ le_top
        ((I₃.ι.f 0).hom.app (op ⊤) t) := by
      refine (app_apply_congr comm_g _ (e i)).trans ?_
      show (I₃.ι.f 0).hom.app _ (S.g.hom.app _ (e i)) = _
      rw [he i]
      exact (CechOne.restr_app (I₃.ι.f 0).hom le_top t).symm
    show (g.f 0).hom.app _ (xs i - (I₂.ι.f 0).hom.app _ (e i)) = 0
    rw [map_sub, h1, h2, sub_self]
  have hfb' : push Ui (f.f 0).hom 0 b' = y := by
    funext i
    have hid : (f.f 0).hom.app _ (σ₀.r.hom.app _ (y i)) +
      σ₀.s.hom.app _ ((g.f 0).hom.app _ (y i)) = y i := app_apply_congr σ₀.id _ (y i)
    have hg0 : (g.f 0).hom.app _ (y i) = 0 := congrFun hgy i
    rwa [hg0, map_zero, add_zero] at hid
  -- the facts the representative is made of
  have hcob : ∀ i : Fin 2 → I, CechCochains.cechD Ui (I₁.cocomplex.X 0).val 0 (-b') i =
      (I₁.ι.f 0).hom.app (op (CechCochains.inter Ui i)) (ω.val i) := by
    intro i
    apply injective_app_of_comp_eq_id σ₀.f_r
    have hxs : CechCochains.cechD Ui (I₂.cocomplex.X 0).val 0 xs = 0 :=
      CechBoundary.cechD_eq_zero_of_restr Ui (x₂ t) (fun _ => le_top) xs (fun _ => rfl)
    have e1 : (f.f 0).hom.app _ (CechCochains.cechD Ui (I₁.cocomplex.X 0).val 0 (-b') i) =
        CechCochains.cechD Ui (I₂.cocomplex.X 0).val 0 (push Ui (I₂.ι.f 0).hom 0 e) i := by
      have := congrFun (push_cechD Ui (f.f 0).hom 0 (-b')) i
      rw [push_apply] at this
      rw [this, map_neg, hfb']
      show CechCochains.cechD Ui _ 0 (-(xs - push Ui (I₂.ι.f 0).hom 0 e)) i = _
      rw [neg_sub, map_sub, hxs, sub_zero]
    rw [e1]
    refine (congrFun (push_cechD Ui (I₂.ι.f 0).hom 0 e) i).symm.trans ?_
    show (I₂.ι.f 0).hom.app _ (CechCochains.cechD Ui _ 0 e i) = _
    rw [← hω i]
    exact (app_apply_congr comm_f _ (ω.val i)).symm
  let cyc := R'.X₁.liftCycles x₁ 2 (by simp) hx₁d t
  have hcyc : R'.X₁.iCycles 1 cyc = x₁ t :=
    ConcreteCategory.congr_hom (R'.X₁.liftCycles_i _ _ _ _) t
  have hres : ∀ i : Fin 1 → I, (I₁.cocomplex.X 1).val.map
      (homOfLE (show CechCochains.inter Ui i ≤ ⊤ from le_top)).op (R'.X₁.iCycles 1 cyc) =
        -((I₁.cocomplex.d 0 1).hom.app (op (CechCochains.inter Ui i))) ((-b') i) := by
    intro i
    rw [hcyc, CechCochains.Cochain.neg_apply, map_neg, neg_neg]
    apply injective_app_of_comp_eq_id σ₁.f_r
    have hx₁t : (f.f 1).hom.app (op ⊤) (x₁ t) = (I₂.cocomplex.d 0 1).hom.app (op ⊤) (x₂ t) :=
      ConcreteCategory.congr_hom hx₁ t
    have e1 := CechOne.restr_app (f.f 1).hom (show CechCochains.inter Ui i ≤ ⊤ from le_top) (x₁ t)
    have e2 := CechOne.restr_app (I₂.cocomplex.d 0 1).hom
      (show CechCochains.inter Ui i ≤ ⊤ from le_top) (x₂ t)
    have e3 : (f.f 1).hom.app _ ((I₁.cocomplex.d 0 1).hom.app _ (b' i)) =
        (I₂.cocomplex.d 0 1).hom.app _ ((f.f 0).hom.app _ (b' i)) :=
      (app_apply_congr (f.comm 0 1) _ (b' i)).symm
    have e4 : (I₂.cocomplex.d 0 1).hom.app _ ((I₂.ι.f 0).hom.app _ (e i)) = 0 :=
      app_apply_congr I₂.ι_f_zero_comp_complex_d _ (e i)
    have hy : (f.f 0).hom.app _ (b' i) = y i := congrFun hfb' i
    refine (e1.symm.trans ?_).trans e3.symm
    show CechCochains.restr _ _ ((f.f 1).hom.app (op ⊤) (x₁ t)) = _
    rw [hx₁t, e2, hy]
    show _ = (I₂.cocomplex.d 0 1).hom.app _ (xs i - (I₂.ι.f 0).hom.app _ (e i))
    rw [map_sub, e4, sub_zero]
  let r : CechOneResolutionRepresentative X ⊤ Ui hUi S.X₁ I₁ ω :=
    { b := -b'
      cycle := cyc
      coboundary := hcob
      restriction := hres }
  rw [cechH1ToRightDerivedSections_apply X ⊤ Ui hUi S.X₁ I₁ ω r]
  congr 1
  exact ConcreteCategory.congr_hom hkey t

end Resolution

/-- **The connecting morphism of sheaf cohomology on a global section is the Čech class of the
differences of its local lifts.** Let `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` be a short exact sequence of abelian
sheaves, `t` a global section of `ℱ₃`, `eᵢ` lifts of `t` to `ℱ₂` on an open covering, and `ω` a
Čech `1`-cocycle of `ℱ₁` whose image is the Čech coboundary `e_{i₁} - e_{i₀}`. Then the connecting
morphism `H⁰(X, ℱ₃) ⟶ H¹(X, ℱ₁)` of the derived functor `RΓ(X, -)`, read in the
injective-resolution convention through `derivedPlusToStandard`, sends `t` to the image of the
class of `ω` under the comparison of [Stacks, Tag 01EQ]. -/
theorem rightDerivedPlusδ_toRightDerivedZero (t : S.X₃.val.obj (op ⊤))
    {I : Type u} (Ui : I → Opens X) (hUi : (⊤ : Opens X) = ⨆ i, Ui i)
    (e : CechCochains.Cochain Ui S.X₂.val 0)
    (he : ∀ i : Fin 1 → I, S.g.hom.app (op (CechCochains.inter Ui i)) (e i) =
      S.X₃.val.map (homOfLE le_top).op t)
    (ω : CechCochains.cocycles1 Ui S.X₁.val)
    (hω : ∀ i : Fin 2 → I, S.f.hom.app (op (CechCochains.inter Ui i)) (ω.val i) =
      CechCochains.cechD Ui S.X₂.val 0 e i) :
    (derivedPlusToStandard (sectionsFunctor X ⊤) 1).hom.app S.X₁
        (CechDelta.rightDerivedPlusδ (sectionsFunctor X ⊤) hS 0
          ((derivedPlusToStandard (sectionsFunctor X ⊤) 0).inv.app S.X₃
            ((sectionsFunctor X ⊤).toRightDerivedZero.app S.X₃ t))) =
      cechH1ToRightDerivedSections X ⊤ Ui hUi S.X₁ (CechCochains.cls Ui S.X₁.val ω) := by
  obtain ⟨I₁, I₂, I₃, f, g, w, hR, cf, cg, hsplit⟩ := hS.exists_injectiveResolution_shortExact
  have hFR : ((ShortComplex.mk f g w).map
      ((sectionsFunctor X ⊤).mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
      (((hsplit n).choose).map (sectionsFunctor X ⊤)).shortExact
  have key := rightDerivedPlusδ_resolution (sectionsFunctor X ⊤) hS I₁ I₂ I₃ f g w cf cg hR hFR 0
  have h₃ : (derivedPlusToStandard (sectionsFunctor X ⊤) 0).inv.app S.X₃ =
      (derivedPlusToStandardObjOfResolution (sectionsFunctor X ⊤) I₃ 0).inv :=
    congrArg Iso.inv (derivedPlusToStandard_app_eq (sectionsFunctor X ⊤) I₃ 0)
  have h₁ : (derivedPlusToStandard (sectionsFunctor X ⊤) 1).hom.app S.X₁ =
      (derivedPlusToStandardObjOfResolution (sectionsFunctor X ⊤) I₁ (0 + 1)).hom :=
    congrArg Iso.hom (derivedPlusToStandard_app_eq (sectionsFunctor X ⊤) I₁ 1)
  rw [h₃, h₁]
  exact (ConcreteCategory.congr_hom key _).trans <|
    isoRightDerivedObj_δ_toRightDerivedZero I₁ I₂ I₃ f g w cf cg (hsplit 0).choose
      (hsplit 1).choose hFR t Ui hUi e he ω hω

end Stacks.Cohomology.CechOne

end
