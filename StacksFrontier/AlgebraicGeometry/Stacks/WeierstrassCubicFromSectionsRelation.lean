module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartCocycle
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicFromSections
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassMonomials

/-!
# The Weierstrass relation among sections of the powers of an invertible module

Let `Z` be an invertible module on a scheme `X` over `Spec B`, and let `z`, `x`, `y` be global
sections of `Z`, `Z^{⊗2}`, `Z^{⊗3}`. If the degree-six sections satisfy the Weierstrass equation
`y² + a₁ zxy + a₃ z³y = x³ + a₂ z²x² + a₄ z⁴x + a₆ z⁶` of a Weierstrass curve `C` over `B`, then
the three sections `zx, y, z³` of `Z^{⊗3}` satisfy the homogeneous cubic of `C` on every chart:
on the nonvanishing open of `sᵢ` the cubic vanishes at the ratios `s₀/sᵢ, s₁/sᵢ, s₂/sᵢ`.

The cubic evaluated at the ratios is the ratio of the degree-nine section `F(s₀, s₁, s₂)` by
`sᵢ³`, because the ratio of a product of sections by a product is the product of the ratios.
That section is `z³` times the Weierstrass equation, computed in the section ring `Γ_*(X, Z)`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.ratioOf_mulSections`: the ratio of a
  product by a product is the product of the ratios.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.satisfiesCubic_weierstrassSections`: the
  Weierstrass equation in degree six gives the cubic relation of the sections `zx, y, z³`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartFromRatios Stacks.AlgebraicGeometry.ProjChartCocycle
open Stacks.ProjectiveFromSections
open ModuliEllipticCurves.PointedFamily (sq cube weierstrassMonomials ySq toSectionRing
  toSectionRing_mulSections toSectionRing_smul toSectionRing_add toSectionRing_injective
  toSectionRing_cube toSectionRing_ySq toSectionRing_weierstrassMonomials)

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

section Ratio

variable {X : Scheme.{u}} (Z : X.Modules) [Stacks.Ample.IsInvertibleModule X Z] {V : X.Opens}

/-- **The ratio of a product by a product is the product of the ratios.** -/
theorem ratioOf_mulSections {n m : ℕ} {t x : Γ(natTensorPow Z n, ⊤)}
    {u y : Γ(natTensorPow Z m, ⊤)}
    (hVt : V ≤ nonvanishingOpen X (natTensorPow Z n) t)
    (hVu : V ≤ nonvanishingOpen X (natTensorPow Z m) u)
    (hVtu : V ≤ nonvanishingOpen X (natTensorPow Z (n + m)) (mulSections Z t u)) :
    ratioOf Z (mulSections Z t u) hVtu (mulSections Z x y) =
      ratioOf Z t hVt x * ratioOf Z u hVu y := by
  refine ratioOf_eq_of_resTop_eq Z _ hVtu ?_
  rw [resTop_mulSections_smul_right Z x (resTop_eq_ratioOf_smul Z u hVu y),
    resTop_mulSections_smul_left Z u (resTop_eq_ratioOf_smul Z t hVt x), smul_smul, mul_comm]

/-- The nonvanishing open of a product contains every open on which both factors are
nonvanishing. -/
theorem le_nonvanishingOpen_mulSections {n m : ℕ} {t : Γ(natTensorPow Z n, ⊤)}
    {u : Γ(natTensorPow Z m, ⊤)} (hVt : V ≤ nonvanishingOpen X (natTensorPow Z n) t)
    (hVu : V ≤ nonvanishingOpen X (natTensorPow Z m) u) :
    V ≤ nonvanishingOpen X (natTensorPow Z (n + m)) (mulSections Z t u) := by
  rw [nonvanishingOpen_mulSections]
  exact le_inf hVt hVu

/-- **The ratio is linear over the global functions.** -/
theorem ratioOf_smul {n : ℕ} {t : Γ(natTensorPow Z n, ⊤)}
    (hV : V ≤ nonvanishingOpen X (natTensorPow Z n) t) (a : Γ(X, ⊤))
    (x : Γ(natTensorPow Z n, ⊤)) :
    ratioOf Z t hV (a • x) = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a * ratioOf Z t hV x := by
  refine ratioOf_eq_of_resTop_eq Z _ hV ?_
  show (natTensorPow Z n).presheaf.map _ (a • x) = _
  rw [Scheme.Modules.map_smul, mul_smul]
  exact congrArg _ (resTop_eq_ratioOf_smul Z t hV x)

/-- The ratio of `Stacks.ProjectiveFromSections` is the ratio of
`Stacks.AlgebraicGeometry.ProjChartFromRatios`. -/
theorem ratio_eq_ratioOf {n : ℕ} (s : Fin 3 → Γ(natTensorPow Z n, ⊤)) (i k : Fin 3) :
    ratio s i k = ratioOf Z (s i) le_rfl (s k) :=
  (eq_div (s i) le_rfl (resTop_eq_ratioOf_smul Z (s i) le_rfl (s k)).symm).symm

end Ratio

section Relation

variable {B : Type u} [CommRing B] (C : WeierstrassCurve B) {X : Scheme.{u}}
  (π : X ⟶ Spec (.of B)) (Z : X.Modules) [Stacks.Ample.IsInvertibleModule X Z]
  (z : Γ(natTensorPow Z 1, ⊤)) (x : Γ(natTensorPow Z 2, ⊤)) (y : Γ(natTensorPow Z 3, ⊤))

/-- The three sections `zx, y, z³` of `Z^{⊗3}`. -/
def weierstrassSections : Fin 3 → Γ(natTensorPow Z 3, ⊤) :=
  ![mulSections Z z x, y, cube Z z]

/-- **The Weierstrass equation in degree six gives the cubic relation of the sections
`zx, y, z³`** on every chart. The coefficients act on sections through `π`. -/
theorem satisfiesCubic_weierstrassSections
    (h : ySq Z y + (Stacks.Cech.baseRingHom π ⊤).hom C.a₁ • weierstrassMonomials Z z x y 4 +
        (Stacks.Cech.baseRingHom π ⊤).hom C.a₃ • weierstrassMonomials Z z x y 2 =
      weierstrassMonomials Z z x y 5 +
        (Stacks.Cech.baseRingHom π ⊤).hom C.a₂ • weierstrassMonomials Z z x y 3 +
        (Stacks.Cech.baseRingHom π ⊤).hom C.a₄ • weierstrassMonomials Z z x y 1 +
        (Stacks.Cech.baseRingHom π ⊤).hom C.a₆ • weierstrassMonomials Z z x y 0) :
    SatisfiesCubic C π (weierstrassSections Z z x y) := by
  intro i
  set s := weierstrassSections Z z x y with hs_def
  set V := nvCover s i
  have hV : V ≤ nonvanishingOpen X (natTensorPow Z 3) (s i) := le_rfl
  set c : B →+* Γ(X, ⊤) := (Stacks.Cech.baseRingHom π ⊤).hom
  set cV : B →+* Γ(X, V) := (Stacks.Cech.baseRingHom π V).hom
  set r : Fin 3 → Γ(X, V) := fun k => ratioOf Z (s i) hV (s k)
  -- the chart ring map is the evaluation at the ratios, read through `topIso`
  have hmap : ∀ {U W W' : X.Opens} (f : op U ⟶ op W) (g : op W ⟶ op W') (e : op U ⟶ op W')
      (b : Γ(X, U)), X.presheaf.map g (X.presheaf.map f b) = X.presheaf.map e b := by
    intro U W W' f g e b
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hbase : ∀ a : B, openBase π V a = V.topIso.inv (cV a) := fun a => by
    rw [openBase, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply]
    exact (hmap _ _ _ _).symm
  have hpoly : chartPolyHom π s i = V.topIso.inv.hom.comp (MvPolynomial.eval₂Hom cV r) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
    · simp only [chartPolyHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.coe_comp,
        Function.comp_apply]
      exact hbase a
    · simp only [chartPolyHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, RingHom.coe_comp,
        Function.comp_apply, r]
      rw [chartRatio, ratio_eq_ratioOf Z s i k]
  rw [hpoly, RingHom.comp_apply]
  refine (congrArg _ ?_).trans (map_zero _)
  -- the cubic at the ratios is the ratio of a degree-nine section by `sᵢ³`
  have hV2 := le_nonvanishingOpen_mulSections Z hV hV
  have hV3 := le_nonvanishingOpen_mulSections Z hV2 hV
  set m : Fin 3 → Fin 3 → Fin 3 → Γ(natTensorPow Z (3 + 3 + 3), ⊤) :=
    fun a b d => mulSections Z (mulSections Z (s a) (s b)) (s d)
  have hm : ∀ a b d, r a * r b * r d = ratioOf Z _ hV3 (m a b d) := fun a b d => by
    simp only [m, r]
    rw [ratioOf_mulSections Z hV2 hV hV3, ratioOf_mulSections Z hV hV hV2]
  have hres : ∀ a : B, cV a = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (c a) := fun a =>
    (Stacks.Cech.map_baseRingHom_apply π (homOfLE (le_top : V ≤ ⊤)).op a).symm
  have hsm : ∀ (a : B) (b d e : Fin 3), cV a * (r b * r d * r e) =
      ratioOf Z _ hV3 (c a • m b d e) := fun a b d e => by
    rw [ratioOf_smul, hm, hres]
  -- the degree-nine relation, from the degree-six one in the section ring
  have key : m 1 1 2 + c C.a₁ • m 0 1 2 + c C.a₃ • m 1 2 2 =
      m 0 0 0 + c C.a₂ • m 0 0 2 + c C.a₄ • m 0 2 2 + c C.a₆ • m 2 2 2 := by
    apply toSectionRing_injective Z (3 + 3 + 3)
    have h' := congrArg (toSectionRing Z 6) h
    set ζ := toSectionRing Z 1 z
    set ξ := toSectionRing Z 2 x
    set η := toSectionRing Z 3 y with hη
    have hw := toSectionRing_weierstrassMonomials Z z x y
    have w : ∀ k, toSectionRing Z 6 (weierstrassMonomials Z z x y k) =
        ![ζ ^ 6, ζ ^ 4 * ξ, ζ ^ 3 * η, ζ ^ 2 * ξ ^ 2, ζ * ξ * η, ξ ^ 3] k := fun k =>
      congrFun hw k
    have h0 : toSectionRing Z 3 (s 0) = ζ * ξ := toSectionRing_mulSections Z z x
    have h1 : toSectionRing Z 3 (s 1) = η := rfl
    have h2 : toSectionRing Z 3 (s 2) = ζ ^ 3 := toSectionRing_cube Z z
    have hmm : ∀ a b d, toSectionRing Z (3 + 3 + 3) (m a b d) =
        toSectionRing Z 3 (s a) * toSectionRing Z 3 (s b) * toSectionRing Z 3 (s d) :=
      fun a b d => by simp only [m, toSectionRing_mulSections]
    simp only [toSectionRing_add, toSectionRing_smul, toSectionRing_ySq, w, Matrix.cons_val,
      Fin.isValue] at h'
    rw [← hη] at h'
    simp only [toSectionRing_add, toSectionRing_smul, hmm, h0, h1, h2]
    linear_combination ζ ^ 3 * h'
  have hcubic : MvPolynomial.eval₂Hom cV r (cubicOf C) =
      ratioOf Z _ hV3 (m 1 1 2 + c C.a₁ • m 0 1 2 + c C.a₃ • m 1 2 2) -
        ratioOf Z _ hV3 (m 0 0 0 + c C.a₂ • m 0 0 2 + c C.a₄ • m 0 2 2 + c C.a₆ • m 2 2 2) := by
    rw [← ratioOfHom_apply, ← ratioOfHom_apply, map_add, map_add, map_add, map_add, map_add,
      ratioOfHom_apply, ratioOfHom_apply, ratioOfHom_apply, ratioOfHom_apply, ratioOfHom_apply,
      ratioOfHom_apply, ratioOfHom_apply, ← hsm, ← hsm, ← hsm, ← hsm, ← hsm, ← hm, ← hm]
    simp only [cubicOf, WeierstrassCurve.Projective.polynomial, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_add, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_pow, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
    ring
  rw [hcubic, key, sub_self]

end Relation

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

end
