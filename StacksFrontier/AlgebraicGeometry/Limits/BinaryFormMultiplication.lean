module
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.BasicUnconditional
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.Defs

public import StacksFrontier.AlgebraicGeometry.GlobalSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.SegreChartProduct.TargetCover
public import StacksFrontier.RingTheory.Polynomial.CoeffMulSpan

/-!
# Multiplication of binary forms, `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ ⟶ ℙⁿ⁺¹_ℤ`

A point of `ℙⁿ` is a binary form `∑ᵢ Xᵢ sⁱ tⁿ⁻ⁱ` of degree `n` up to a scalar, and a point of `ℙ¹`
a binary form `Y₀ t + Y₁ s` of degree one. Multiplying them gives a binary form of degree `n + 1`,
whose coefficients `Z_k = ∑_{i + j = k} XᵢYⱼ` are the homogeneous coordinates of a point of
`ℙⁿ⁺¹`. This file constructs that morphism of the integral models.

On the chart `U_{ab} = pr₁⁻¹D₊(X_a) ∩ pr₂⁻¹D₊(Y_b)` the ratios `xᵢ = Xᵢ/X_a` and `yⱼ = Yⱼ/Y_b` are
functions, and the `n + 2` functions `z_k = ∑_{i + j = k} xᵢyⱼ` are the coefficients of the product
of the polynomials `∑ xᵢ Tⁱ` and `∑ yⱼ Tʲ`, whose `a`-th and `b`-th coefficients are `1`. By
`Polynomial.span_range_coeff_mul_eq_top` they generate the unit ideal, so they define a morphism
`U_{ab} ⟶ ℙⁿ⁺¹` (`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse`). On an overlap
the ratios of one chart are those of the other times the units `X_{a'}/X_a` and `Y_{b'}/Y_b`, so
the two families of coefficients differ by the unit `(X_{a'}/X_a)(Y_{b'}/Y_b)`, and the chart
morphisms glue (`Stacks.SectionsToProjectiveSpace.exists_hom_of_cover_general`).

## Main definitions

* `AlgebraicGeometry.ProjectiveSpace.pullRatio`: the pullback of the ratio `Xᵢ / X_a` along a
  morphism into `D₊(X_a)`.
* `AlgebraicGeometry.ProjectiveSpace.mulCoeffs`: the coefficients of the product of two
  polynomials with given coefficient vectors.
* `AlgebraicGeometry.ProjectiveSpace.mulSource`: the fibre product `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ`.
* `AlgebraicGeometry.ProjectiveSpace.mulChart`: the chart `pr₁⁻¹D₊(X_a) ∩ pr₂⁻¹D₊(Y_b)`, and
  `AlgebraicGeometry.ProjectiveSpace.mulChartCoeffs` the coordinates of the product on it.
* `AlgebraicGeometry.ProjectiveSpace.binaryFormMul`: **the multiplication morphism
  `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ ⟶ ℙⁿ⁺¹_ℤ`.**

## Main results

* `AlgebraicGeometry.ProjectiveSpace.pullRatio_eq_mul`: the cocycle identity
  `Xᵢ/X_a = (X_{a'}/X_a)(Xᵢ/X_{a'})`.
* `AlgebraicGeometry.ProjectiveSpace.pullRatio_SpecMap_awayι`: on `Spec` of a ring mapping
  to the chart ring, the pulled-back ratio is the image of the algebraic ratio.
* `AlgebraicGeometry.ProjectiveSpace.span_range_mulChartCoeffs` and
  `AlgebraicGeometry.ProjectiveSpace.exists_unit_resOfLE_mulChartCoeffs`: the coordinates on a
  chart generate the unit ideal, and agree up to a unit on overlaps.
* `AlgebraicGeometry.ProjectiveSpace.mulChart_ι_binaryFormMul`: on the chart `U_{ab}` the
  multiplication morphism is the morphism defined by the coefficients `z_k`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace HomogeneousLocalization
open Stacks.SectionsToProjectiveSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

section Ratio

variable {m : ℕ} {Y : Scheme.{u}}

/-- **The ratio `Xᵢ / X_a` pulled back along a morphism into `D₊(X_a)`.** For
`φ : Y ⟶ ℙᵐ_ℤ` with `φ(Y) ⊆ D₊(X_a)`, this is the global function `φ^*(Xᵢ/X_a)` on `Y`. -/
def pullRatio (φ : Y ⟶ Proj (coordGrading.{u} m)) (a i : Fin (m + 1))
    (h : ⊤ ≤ φ ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a)) : Γ(Y, ⊤) :=
  (φ.appLE _ ⊤ h).hom ((Proj.awayToSection (coordGrading.{u} m) (MvPolynomial.X a)).hom
    (Stacks.ProjectiveChart.ratio (ULift.{u} ℤ) a i))

/-- The pulled-back ratio depends on the morphism only. -/
theorem pullRatio_congr {φ φ' : Y ⟶ Proj (coordGrading.{u} m)} (e : φ = φ') (a i : Fin (m + 1))
    (h : ⊤ ≤ φ ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a))
    (h' : ⊤ ≤ φ' ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a)) :
    pullRatio φ a i h = pullRatio φ' a i h' := by
  subst e; rfl

/-- `X_a / X_a = 1`. -/
@[simp] theorem pullRatio_self (φ : Y ⟶ Proj (coordGrading.{u} m)) (a : Fin (m + 1))
    (h : ⊤ ≤ φ ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a)) :
    pullRatio φ a a h = 1 := by
  rw [pullRatio, Stacks.ProjectiveChart.ratio_self, map_one, map_one]

/-- **Pulling back a pulled-back ratio.** -/
theorem appTop_pullRatio {Y' : Scheme.{u}} (g : Y' ⟶ Y) (φ : Y ⟶ Proj (coordGrading.{u} m))
    (a i : Fin (m + 1))
    (h : ⊤ ≤ φ ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a))
    (h' : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a)) :
    g.appTop.hom (pullRatio φ a i h) = pullRatio (g ≫ φ) a i h' := by
  have e : φ.appLE _ ⊤ h ≫ g.appTop = (g ≫ φ).appLE _ ⊤ h' := by
    rw [← Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.appLE_top_top g le_top]
    exact Scheme.Hom.appLE_comp_appLE g φ _ ⊤ ⊤ h le_top
  exact congrArg (fun F => F.hom ((Proj.awayToSection (coordGrading.{u} m)
    (MvPolynomial.X a)).hom (Stacks.ProjectiveChart.ratio (ULift.{u} ℤ) a i))) e

/-- On `D₊(X_a X_{a'})` the ratio `Xᵢ / X_a` is `(X_{a'} / X_a) (Xᵢ / X_{a'})`, read in the chart
ring of the product. -/
theorem awayMap_ratio_eq_mul (a a' i : Fin (m + 1)) :
    awayMap (coordGrading.{u} m) (X_mem_coordGrading_one a')
        (rfl : (MvPolynomial.X a * MvPolynomial.X a' : coordRing.{u} m) = _)
        (Stacks.ProjectiveChart.ratio (ULift.{u} ℤ) a i) =
      awayMap (coordGrading.{u} m) (X_mem_coordGrading_one a')
          (rfl : (MvPolynomial.X a * MvPolynomial.X a' : coordRing.{u} m) = _)
          (Stacks.ProjectiveChart.ratio (ULift.{u} ℤ) a a') *
        awayMap (coordGrading.{u} m) (X_mem_coordGrading_one a)
          (mul_comm _ _ : (MvPolynomial.X a * MvPolynomial.X a' : coordRing.{u} m) = _)
          (Stacks.ProjectiveChart.ratio (ULift.{u} ℤ) a' i) := by
  apply HomogeneousLocalization.val_injective
  simp only [Stacks.ProjectiveChart.ratio, Away.isLocalizationElem, awayMap_mk,
    HomogeneousLocalization.val_mul, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]; ring⟩

/-- **The cocycle identity for the pulled-back ratios**: `Xᵢ / X_a = (X_{a'} / X_a)(Xᵢ / X_{a'})`
on a scheme mapping into `D₊(X_a) ∩ D₊(X_{a'})`. -/
theorem pullRatio_eq_mul (φ : Y ⟶ Proj (coordGrading.{u} m)) (a a' i : Fin (m + 1))
    (h : ⊤ ≤ φ ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a))
    (h' : ⊤ ≤ φ ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a')) :
    pullRatio φ a i h = pullRatio φ a a' h * pullRatio φ a' i h' := by
  have hx : ⊤ ≤ φ ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m)
      (MvPolynomial.X a * MvPolynomial.X a') := by
    rw [Proj.basicOpen_mul]
    exact fun y hy => ⟨h hy, h' hy⟩
  have key : ∀ (b : Fin (m + 1))
      (hb : ⊤ ≤ φ ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X b))
      (c : coordRing.{u} m) (hc : c ∈ coordGrading.{u} m 1)
      (hbc : (MvPolynomial.X a * MvPolynomial.X a' : coordRing.{u} m) = MvPolynomial.X b * c)
      (w : Away (coordGrading.{u} m) (MvPolynomial.X b)),
      (φ.appLE _ ⊤ hb).hom ((Proj.awayToSection (coordGrading.{u} m) (MvPolynomial.X b)).hom w) =
        (φ.appLE _ ⊤ hx).hom ((Proj.awayToSection (coordGrading.{u} m)
          (MvPolynomial.X a * MvPolynomial.X a')).hom (awayMap (coordGrading.{u} m) hc hbc w)) := by
    intro b hb c hc hbc w
    have e1 := Proj.awayMap_awayToSection (coordGrading.{u} m) hc hbc
    have e2 := Scheme.Hom.map_appLE φ hx
      (homOfLE (Proj.basicOpen_mono (coordGrading.{u} m) _ _ ⟨_, hbc⟩)).op
    have e3 : CommRingCat.ofHom (awayMap (coordGrading.{u} m) hc hbc) ≫
        Proj.awayToSection (coordGrading.{u} m) (MvPolynomial.X a * MvPolynomial.X a') ≫
          φ.appLE _ ⊤ hx =
        Proj.awayToSection (coordGrading.{u} m) (MvPolynomial.X b) ≫ φ.appLE _ ⊤ hb := by
      rw [← Category.assoc, e1, Category.assoc, e2]
    exact (congrArg (fun F => F.hom w) e3).symm
  rw [pullRatio, pullRatio, pullRatio,
    key a h (MvPolynomial.X a') (X_mem_coordGrading_one a') rfl,
    key a h (MvPolynomial.X a') (X_mem_coordGrading_one a') rfl,
    key a' h' (MvPolynomial.X a) (X_mem_coordGrading_one a) (mul_comm _ _),
    ← map_mul, ← map_mul, awayMap_ratio_eq_mul]

/-- On an open where `X_a` and `X_{a'}` are both nonvanishing, the ratio `X_{a'} / X_a` is a
unit, with inverse `X_a / X_{a'}`. -/
theorem pullRatio_mul_pullRatio (φ : Y ⟶ Proj (coordGrading.{u} m)) (a a' : Fin (m + 1))
    (h : ⊤ ≤ φ ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a))
    (h' : ⊤ ≤ φ ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a')) :
    pullRatio φ a a' h * pullRatio φ a' a h' = 1 := by
  rw [← pullRatio_eq_mul, pullRatio_self]

/-- **On `Spec` of a ring mapping out of the chart ring, the pulled-back ratio is the image of
the algebraic ratio.** For `ψ : (A_{X_a})₀ →+* B`, along `Spec B ⟶ Spec (A_{X_a})₀ ⟶ ℙᵐ` the ratio
`Xᵢ / X_a` pulls back to `ψ (Xᵢ / X_a)`. -/
theorem pullRatio_SpecMap_awayι {B : CommRingCat.{u}} (a i : Fin (m + 1))
    (ψ : CommRingCat.of (Away (coordGrading.{u} m) (MvPolynomial.X a)) ⟶ B)
    (h : ⊤ ≤ (Spec.map ψ ≫ Proj.awayι (coordGrading.{u} m) (MvPolynomial.X a)
      (X_mem_coordGrading_one a) Nat.one_pos) ⁻¹ᵁ
        Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a)) :
    pullRatio (Spec.map ψ ≫ Proj.awayι (coordGrading.{u} m) (MvPolynomial.X a)
        (X_mem_coordGrading_one a) Nat.one_pos) a i h =
      (Scheme.ΓSpecIso B).inv.hom (ψ.hom (Stacks.ProjectiveChart.ratio (ULift.{u} ℤ) a i)) := by
  have hι : (⊤ : (Spec (CommRingCat.of (Away (coordGrading.{u} m) (MvPolynomial.X a)))).Opens) ≤
      Proj.awayι (coordGrading.{u} m) (MvPolynomial.X a) (X_mem_coordGrading_one a)
        Nat.one_pos ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a) :=
    fun x _ => (Proj.opensRange_awayι (coordGrading.{u} m) (MvPolynomial.X a)
      (X_mem_coordGrading_one a) Nat.one_pos).le ⟨x, rfl⟩
  rw [← appTop_pullRatio (Spec.map ψ) _ a i hι h, pullRatio,
    Stacks.AlgebraicGeometry.ProjTwistChain.appLE_awayι_awayToSection Nat.one_pos
      (X_mem_coordGrading_one a) hι, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

end Ratio

section Coeffs

open Polynomial in
/-- **The coefficients of the product of two dehomogenized binary forms.** For coefficient
vectors `x` of length `n + 1` and `y` of length `2`, the `n + 2` coefficients
`z_k = ∑_{i + j = k} xᵢ yⱼ` of `(∑ xᵢ Tⁱ)(y₀ + y₁ T)`. -/
def mulCoeffs {R : Type*} [CommRing R] {n : ℕ} (x : Fin (n + 1) → R) (y : Fin (1 + 1) → R)
    (k : Fin (n + 1 + 1)) : R :=
  open scoped Classical in (ofFn (n + 1) x * ofFn (1 + 1) y).coeff k

open Polynomial in
/-- `mulCoeffs` commutes with ring homomorphisms. -/
theorem map_mulCoeffs {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (x : Fin (n + 1) → R) (y : Fin (1 + 1) → R) (k : Fin (n + 1 + 1)) :
    φ (mulCoeffs x y k) = mulCoeffs (fun i => φ (x i)) (fun j => φ (y j)) k := by
  classical
  rw [mulCoeffs, mulCoeffs, ← coeff_map, Polynomial.map_mul, map_ofFn, map_ofFn]

open Polynomial in
/-- Scaling the two coefficient vectors by `u` and `v` scales the product by `u v`. -/
theorem mulCoeffs_mul {R : Type*} [CommRing R] {n : ℕ} (u v : R) (x : Fin (n + 1) → R)
    (y : Fin (1 + 1) → R) (k : Fin (n + 1 + 1)) :
    mulCoeffs (fun i => u * x i) (fun j => v * y j) k = u * v * mulCoeffs x y k := by
  classical
  have hx : (fun i => u * x i) = u • x := rfl
  have hy : (fun j => v * y j) = v • y := rfl
  rw [mulCoeffs, mulCoeffs, hx, hy]
  simp only [map_smul, smul_eq_C_mul]
  rw [show C u * ofFn (n + 1) x * (C v * ofFn (1 + 1) y) =
      C (u * v) * (ofFn (n + 1) x * ofFn (1 + 1) y) by rw [C_mul]; ring, coeff_C_mul]

open Polynomial in
/-- **The product coefficients generate the unit ideal** as soon as one coefficient of each
factor is `1`. -/
theorem span_range_mulCoeffs {R : Type*} [CommRing R] {n : ℕ} (x : Fin (n + 1) → R)
    (y : Fin (1 + 1) → R) {a : Fin (n + 1)} {b : Fin (1 + 1)} (ha : x a = 1) (hb : y b = 1) :
    Ideal.span (Set.range (mulCoeffs x y)) = ⊤ := by
  classical
  unfold mulCoeffs
  convert span_range_coeff_mul_eq_top (n := n) (m := 1)
    (Nat.lt_succ_iff.1 (ofFn_natDegree_lt (Nat.succ_pos n) x))
    (Nat.lt_succ_iff.1 (ofFn_natDegree_lt (Nat.succ_pos 1) y))
    (a := a) (b := b) (by rwa [ofFn_coeff_eq_val_of_lt _ a.isLt])
    (by rwa [ofFn_coeff_eq_val_of_lt _ b.isLt]) using 3

open Polynomial in
/-- For polynomials of degrees at most `n` and `1`, `mulCoeffs` of their coefficient vectors is
the coefficient vector of their product. -/
theorem mulCoeffs_coeff {R : Type*} [CommRing R] {n : ℕ} {P Q : R[X]} (hP : P.natDegree ≤ n)
    (hQ : Q.natDegree ≤ 1) (k : Fin (n + 1 + 1)) :
    mulCoeffs (fun i : Fin (n + 1) => P.coeff i) (fun j : Fin (1 + 1) => Q.coeff j) k =
      (P * Q).coeff k := by
  classical
  unfold mulCoeffs
  rw [show (fun i : Fin (n + 1) => P.coeff i) = toFn (n + 1) P from rfl,
    show (fun j : Fin (1 + 1) => Q.coeff j) = toFn (1 + 1) Q from rfl,
    ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hP),
    ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hQ)]

end Coeffs

section Glue

variable (n : ℕ)

/-- The fibre product `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ`, with `Spec ℤ` realised as the terminal scheme. -/
abbrev mulSource : Scheme.{u} :=
  pullback (terminal.from (Proj (coordGrading.{u} n))) (terminal.from (Proj (coordGrading.{u} 1)))

/-- The first projection of `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ`. -/
abbrev mulFst : mulSource.{u} n ⟶ Proj (coordGrading.{u} n) := pullback.fst _ _

/-- The second projection of `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ`. -/
abbrev mulSnd : mulSource.{u} n ⟶ Proj (coordGrading.{u} 1) := pullback.snd _ _

/-- The chart `pr₁⁻¹D₊(X_a) ∩ pr₂⁻¹D₊(Y_b)` of `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ`. -/
def mulChart (p : Fin (n + 1) × Fin (1 + 1)) : (mulSource.{u} n).Opens :=
  mulFst n ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X p.1) ⊓
    mulSnd n ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X p.2)

/-- The chart `U_{ab}` lies over `D₊(X_a)`. -/
theorem mulChart_le_fst (p : Fin (n + 1) × Fin (1 + 1)) :
    mulChart.{u} n p ≤ mulFst n ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X p.1) :=
  inf_le_left

/-- The chart `U_{ab}` lies over `D₊(Y_b)`. -/
theorem mulChart_le_snd (p : Fin (n + 1) × Fin (1 + 1)) :
    mulChart.{u} n p ≤ mulSnd n ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X p.2) :=
  inf_le_right

/-- The charts cover `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ`. -/
theorem isOpenCover_mulChart : IsOpenCover (mulChart.{u} n) :=
  Stacks.AlgebraicGeometry.SegreChartProduct.iSup_pullbackOpens_eq_top (ULift.{u} ℤ)
    (Fin (n + 1)) (Fin (1 + 1)) _ _

variable {n}

/-- An open contained in `V` maps into `V` under its own inclusion. -/
theorem top_le_ι_comp_preimage {X Z : Scheme.{u}} {U : X.Opens} (f : X ⟶ Z) {V : Z.Opens}
    (h : U ≤ f ⁻¹ᵁ V) : ⊤ ≤ (U.ι ≫ f) ⁻¹ᵁ V := by
  rw [Scheme.Hom.comp_preimage, ← Scheme.Opens.ι_preimage_self U]
  exact (TopologicalSpace.Opens.map U.ι.base).monotone h

/-- The ratio `Xᵢ / X_a` on an open of `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ` inside `pr₁⁻¹D₊(X_a)`. -/
def fstRatio {U : (mulSource.{u} n).Opens} (a i : Fin (n + 1))
    (h : U ≤ mulFst n ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X a)) :
    Γ(U.toScheme, ⊤) :=
  pullRatio (U.ι ≫ mulFst n) a i (top_le_ι_comp_preimage _ h)

/-- The ratio `Yⱼ / Y_b` on an open of `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ` inside `pr₂⁻¹D₊(Y_b)`. -/
def sndRatio {U : (mulSource.{u} n).Opens} (b j : Fin (1 + 1))
    (h : U ≤ mulSnd n ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X b)) :
    Γ(U.toScheme, ⊤) :=
  pullRatio (U.ι ≫ mulSnd n) b j (top_le_ι_comp_preimage _ h)

/-- **The coordinates of the product on the chart `U_{ab}`**: the coefficients
`z_k = ∑_{i+j=k} (Xᵢ/X_a)(Yⱼ/Y_b)`. -/
def mulChartCoeffs (p : Fin (n + 1) × Fin (1 + 1)) (k : Fin (n + 1 + 1)) :
    Γ((mulChart.{u} n p).toScheme, ⊤) :=
  mulCoeffs (fun i => fstRatio p.1 i (mulChart_le_fst n p))
    (fun j => sndRatio p.2 j (mulChart_le_snd n p)) k

/-- On the chart `U_{ab}` the coordinates of the product generate the unit ideal. -/
theorem span_range_mulChartCoeffs (p : Fin (n + 1) × Fin (1 + 1)) :
    Ideal.span (Set.range (mulChartCoeffs.{u} p)) = ⊤ :=
  span_range_mulCoeffs _ _ (a := p.1) (b := p.2) (pullRatio_self _ _ _) (pullRatio_self _ _ _)

/-- Restricting a pulled-back ratio along an open immersion to a smaller open gives the ratio
there. -/
private theorem resOfLE_pullRatio_ι {m : ℕ} {X : Scheme.{u}} {U V : X.Opens} (hUV : V ≤ U)
    (f : X ⟶ Proj (coordGrading.{u} m)) (a i : Fin (m + 1))
    (h : U ≤ f ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X a)) :
    resOfLE hUV (pullRatio (U.ι ≫ f) a i (top_le_ι_comp_preimage _ h)) =
      pullRatio (V.ι ≫ f) a i (top_le_ι_comp_preimage _ (hUV.trans h)) := by
  rw [resOfLE, appTop_pullRatio _ _ _ _ _
    (by rw [← Category.assoc, Scheme.homOfLE_ι]; exact top_le_ι_comp_preimage _ (hUV.trans h))]
  exact pullRatio_congr (Scheme.homOfLE_ι_assoc _ _ _) _ _ _ _

/-- Restricting a ratio to a smaller open gives the ratio there. -/
theorem resOfLE_fstRatio {U V : (mulSource.{u} n).Opens} (hUV : V ≤ U) (a i : Fin (n + 1))
    (h : U ≤ mulFst n ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X a)) :
    resOfLE hUV (fstRatio a i h) = fstRatio a i (hUV.trans h) :=
  resOfLE_pullRatio_ι hUV _ a i h

/-- Restricting a ratio to a smaller open gives the ratio there. -/
theorem resOfLE_sndRatio {U V : (mulSource.{u} n).Opens} (hUV : V ≤ U) (b j : Fin (1 + 1))
    (h : U ≤ mulSnd n ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X b)) :
    resOfLE hUV (sndRatio b j h) = sndRatio b j (hUV.trans h) :=
  resOfLE_pullRatio_ι hUV _ b j h

/-- On an open inside the chart `U_{ab}`, the restricted coordinates of the product are the
coefficients of the product of the restricted ratios. -/
theorem resOfLE_mulChartCoeffs (p : Fin (n + 1) × Fin (1 + 1)) {V : (mulSource.{u} n).Opens}
    (hV : V ≤ mulChart.{u} n p) (k : Fin (n + 1 + 1)) :
    resOfLE hV (mulChartCoeffs p k) =
      mulCoeffs (fun i => fstRatio p.1 i (hV.trans (mulChart_le_fst n p)))
        (fun j => sndRatio p.2 j (hV.trans (mulChart_le_snd n p))) k := by
  refine (map_mulCoeffs ((mulSource.{u} n).homOfLE hV).appTop.hom _ _ k).trans ?_
  congr 1
  · funext i
    exact resOfLE_fstRatio hV p.1 i (mulChart_le_fst n p)
  · funext j
    exact resOfLE_sndRatio hV p.2 j (mulChart_le_snd n p)

/-- **The charts agree up to a unit on the overlaps.** On `U_{ab} ∩ U_{a'b'}` the coordinates of
the product on the two charts differ by the unit `(X_{a'}/X_a)(Y_{b'}/Y_b)`. -/
theorem exists_unit_resOfLE_mulChartCoeffs (p q : Fin (n + 1) × Fin (1 + 1)) :
    ∃ w : Γ((mulChart.{u} n p ⊓ mulChart.{u} n q : (mulSource.{u} n).Opens).toScheme, ⊤)ˣ,
      ∀ k, resOfLE (inf_le_left : mulChart n p ⊓ mulChart n q ≤ mulChart n p)
          (mulChartCoeffs p k) =
        (w : Γ((mulChart.{u} n p ⊓ mulChart.{u} n q : (mulSource.{u} n).Opens).toScheme, ⊤)) *
          resOfLE (inf_le_right : mulChart n p ⊓ mulChart n q ≤ mulChart n q)
            (mulChartCoeffs q k) := by
  have hp1 := (inf_le_left : mulChart.{u} n p ⊓ mulChart n q ≤ _).trans (mulChart_le_fst n p)
  have hp2 := (inf_le_left : mulChart.{u} n p ⊓ mulChart n q ≤ _).trans (mulChart_le_snd n p)
  have hq1 := (inf_le_right : mulChart.{u} n p ⊓ mulChart n q ≤ _).trans (mulChart_le_fst n q)
  have hq2 := (inf_le_right : mulChart.{u} n p ⊓ mulChart n q ≤ _).trans (mulChart_le_snd n q)
  have e₁ := pullRatio_mul_pullRatio _ _ _ (top_le_ι_comp_preimage _ hp1)
    (top_le_ι_comp_preimage _ hq1)
  have e₂ := pullRatio_mul_pullRatio _ _ _ (top_le_ι_comp_preimage _ hp2)
    (top_le_ι_comp_preimage _ hq2)
  let w₁ : Γ((mulChart.{u} n p ⊓ mulChart.{u} n q : (mulSource.{u} n).Opens).toScheme, ⊤)ˣ :=
    ⟨_, _, e₁, (mul_comm _ _).trans e₁⟩
  let w₂ : Γ((mulChart.{u} n p ⊓ mulChart.{u} n q : (mulSource.{u} n).Opens).toScheme, ⊤)ˣ :=
    ⟨_, _, e₂, (mul_comm _ _).trans e₂⟩
  refine ⟨w₁ * w₂, fun k => ?_⟩
  rw [resOfLE_mulChartCoeffs, resOfLE_mulChartCoeffs, Units.val_mul, ← mulCoeffs_mul]
  congr 1
  · funext i
    exact pullRatio_eq_mul _ _ _ _ _ _
  · funext j
    exact pullRatio_eq_mul _ _ _ _ _ _

variable (n) in
/-- The chart morphisms glue to a morphism `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ ⟶ ℙⁿ⁺¹_ℤ`. -/
theorem exists_mulMorphism : ∃ g : mulSource.{u} n ⟶ projectiveSpaceAtUniverse.{u} (n + 1),
    ∀ p, (mulChart.{u} n p).ι ≫ g =
      toProjectiveSpaceAtUniverse (mulChartCoeffs p) (span_range_mulChartCoeffs p) :=
  exists_hom_of_cover_general Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality
    Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance (mulChart.{u} n) (isOpenCover_mulChart n)
    mulChartCoeffs span_range_mulChartCoeffs exists_unit_resOfLE_mulChartCoeffs

variable (n) in
/-- **The multiplication of binary forms**, `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ ⟶ ℙⁿ⁺¹_ℤ`,
`((X₀ : ⋯ : Xₙ), (Y₀ : Y₁)) ↦ (Z₀ : ⋯ : Z_{n+1})` with `Z_k = ∑_{i+j=k} XᵢYⱼ`. -/
def binaryFormMul : mulSource.{u} n ⟶ projectiveSpaceAtUniverse.{u} (n + 1) :=
  (exists_mulMorphism n).choose

/-- **On the chart `U_{ab}` the multiplication is the morphism defined by the coefficients of
the product of the two dehomogenized forms.** -/
theorem mulChart_ι_binaryFormMul (p : Fin (n + 1) × Fin (1 + 1)) :
    (mulChart.{u} n p).ι ≫ binaryFormMul n =
      toProjectiveSpaceAtUniverse (mulChartCoeffs p) (span_range_mulChartCoeffs p) :=
  (exists_mulMorphism n).choose_spec p

end Glue

end AlgebraicGeometry.ProjectiveSpace

end
