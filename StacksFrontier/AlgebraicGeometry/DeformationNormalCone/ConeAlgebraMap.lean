module

public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.ConormalComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalPushforward

/-!
# The extended Rees algebra maps onto the conormal algebra

Let `i : Z ⟶ X` be an immersion, factored as the closed immersion `g = i.liftCoborder` into the
open `U = i.coborderRange` followed by the inclusion of `U`, and let `ℐ` be the ideal sheaf of `g`.
The conormal algebra of `i` is `𝒞_{Z/X,*} = g^*(⨁ₙ ℐⁿ)`. This file constructs the morphism of
sheaves of `𝒪_U`-algebras

  `Ψ : 𝒪_U[t⁻¹, ℐt] ⟶ g_* 𝒞_{Z/X,*}`

which in degree `n ≥ 0` sends a local section of `ℐⁿ` to its class in `ℐⁿ/ℐⁿ⁺¹` and kills the
negative degrees, in particular the parameter `t⁻¹`. On the relative spectra it is the inclusion
of the normal cone `C_ZX` into the deformation space as the fibre `t⁻¹ = 0`.

## Main definitions

* `Stacks.Deformation.toConormalAdd`, `Stacks.Deformation.toConormalPiece`: the degreewise maps.
* `Stacks.Deformation.toConormalUnitalHom`: the degreewise maps as a unital homomorphism of
  graded algebras into the degenerate grading of `g_* 𝒞_{Z/X,*}`.
* `Stacks.Deformation.toConormalAlgebraHom`: the morphism of sheaves of algebras
  `Ψ : 𝒪_U[t⁻¹, ℐt] ⟶ g_* 𝒞_{Z/X,*}`.

## Main results

* `Stacks.Deformation.toConormalExtAdd_one`: `Ψ` is unital.
* `Stacks.Deformation.toConormalExtAdd_mul`: `Ψ` is multiplicative.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf Stacks.RelativeSpec Stacks.Blowup
  Stacks.Conormal

universe u

namespace Stacks.Deformation

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The degree-`n` component of `Ψ`, `n ≥ 0`, on the sections over an open `W` of
`i.coborderRange`: a section of `ℐⁿ` goes to its pullback in `𝒞_{Z/X,n}` over `g⁻¹W`, included
into the ungraded conormal algebra. -/
def toConormalAdd (n : ℕ) (W : (Opens i.coborderRange.toScheme)ᵒᵖ) :
    ((reesPiece (coborderIdeal i) (n : ℤ)).val.obj W : Type u) →+
      algSections (conormalPushforwardAlgebra i i.liftCoborder) W :=
  AddMonoidHom.mk'
    (fun x => ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
      (conormalAlgebra i).mul_comm_int n (i.liftCoborder ⁻¹ᵁ W.unop)
      (Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) (n : ℤ))
        W.unop (i.liftCoborder ⁻¹ᵁ W.unop) le_rfl x))
    (fun x y => by
      refine Eq.trans (congrArg (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int n (i.liftCoborder ⁻¹ᵁ W.unop)) ?_)
        (ungradedAlgebraSheafIncl_add Z (conormalAlgebra i).algebra
          (conormalAlgebra i).mul_comm_int n (i.liftCoborder ⁻¹ᵁ W.unop) _ _)
      unfold Scheme.Modules.pullbackSection
      rw [map_add]
      exact map_add _ _ _)

/-- `toConormalAdd` sends a section of `ℐⁿ` to the image of its pullback in the ungraded
conormal algebra. -/
theorem toConormalAdd_apply (n : ℕ) (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (x : (reesPiece (coborderIdeal i) (n : ℤ)).val.obj W) :
    toConormalAdd i n W x = ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
      (conormalAlgebra i).mul_comm_int n (i.liftCoborder ⁻¹ᵁ W.unop)
      (Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) (n : ℤ))
        W.unop (i.liftCoborder ⁻¹ᵁ W.unop) le_rfl x) := rfl

/-- `toConormalAdd` commutes with restriction of sections. -/
theorem toConormalAdd_naturality (n : ℕ) {W W' : (Opens i.coborderRange.toScheme)ᵒᵖ}
    (f : W ⟶ W') (x : (reesPiece (coborderIdeal i) (n : ℤ)).val.obj W) :
    ((conormalPushforwardAlgebra i i.liftCoborder).right.obj.map f).hom (toConormalAdd i n W x) =
      toConormalAdd i n W' ((reesPiece (coborderIdeal i) (n : ℤ)).val.map f x) := by
  have hle : W'.unop ≤ W.unop := leOfHom f.unop
  have hf : f = (homOfLE hle).op := Subsingleton.elim _ _
  subst hf
  have hpre : i.liftCoborder ⁻¹ᵁ W'.unop ≤ i.liftCoborder ⁻¹ᵁ W.unop := fun _ hz => hle hz
  refine Eq.trans (ungradedAlgebraSheafIncl_restrict Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int n hpre _) ?_
  exact congrArg (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int n (i.liftCoborder ⁻¹ᵁ W'.unop))
    (pullbackSection_restrict i.liftCoborder (reesPiece (coborderIdeal i) (n : ℤ)) hle hpre x)

/-- `toConormalAdd` is linear over `𝒪_U`: it sends `r • x` to the image of `r` times the image
of `x`. -/
theorem toConormalAdd_smul (n : ℕ) (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (r : i.coborderRange.toScheme.ringCatSheaf.obj.obj W)
    (x : (reesPiece (coborderIdeal i) (n : ℤ)).val.obj W) :
    toConormalAdd i n W (r • x) =
      ((conormalPushforwardAlgebra i i.liftCoborder).hom.hom.app W).hom r *
        toConormalAdd i n W x := by
  refine (congrArg (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int n (i.liftCoborder ⁻¹ᵁ W.unop))
    (pullbackSection_smul i.liftCoborder (reesPiece (coborderIdeal i) (n : ℤ)) W.unop r x)).trans ?_
  refine (congrArg (ungradedCommUnit Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int (i.liftCoborder ⁻¹ᵁ W.unop)).hom
    (Stacks.RelativeSpec.structureMap_mul_incl (conormalAlgebra i).algebra (n : ℤ)
      (op (i.liftCoborder ⁻¹ᵁ W.unop)) ((i.liftCoborder.app W.unop).hom r)
      (Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) (n : ℤ))
        W.unop (i.liftCoborder ⁻¹ᵁ W.unop) le_rfl x)).symm).trans ?_
  exact map_mul (ungradedCommUnit Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int (i.liftCoborder ⁻¹ᵁ W.unop)).hom _ _

/-- `toConormalAdd` depends only on the degree up to equality. -/
theorem toConormalAdd_heq {n m : ℕ} (h : n = m) (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (x : (reesPiece (coborderIdeal i) (n : ℤ)).val.obj W)
    (y : (reesPiece (coborderIdeal i) (m : ℤ)).val.obj W) (hxy : HEq x y) :
    toConormalAdd i n W x = toConormalAdd i m W y := by
  subst h
  rw [eq_of_heq hxy]

/-- Reading a section of `ℐᵐ` in `ℐⁿ`, for `n = m`, does not change it. -/
theorem reesPieceLower_heq {n m : ℕ} (h : n ≤ m) (hnm : n = m) (W : (Opens X)ᵒᵖ)
    (I : X.IdealSheafData) (z : (idealPowerKernel I m).val.obj W) :
    HEq ((reesPieceLower I h).val.app W z) z := by
  subst hnm
  refine heq_of_eq (reesPieceAmbient_injective I (n : ℤ) (Int.natCast_nonneg n) W.unop ?_)
  exact reesPieceAmbient_reesPieceLower I h W.unop z

/-- The inclusions of powers compose. -/
theorem reesPieceLower_comp (I : X.IdealSheafData) {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k)
    (W : (Opens X)ᵒᵖ) (z : (idealPowerKernel I k).val.obj W) :
    (reesPieceLower I (h₁.trans h₂)).val.app W z =
      (reesPieceLower I h₁).val.app W ((reesPieceLower I h₂).val.app W z) := by
  refine reesPieceAmbient_injective I (n : ℤ) (Int.natCast_nonneg n) W.unop ?_
  change idealPowerKernelAmbient I n W.unop _ = idealPowerKernelAmbient I n W.unop _
  rw [reesPieceAmbient_reesPieceLower, reesPieceAmbient_reesPieceLower,
    reesPieceAmbient_reesPieceLower]

/-- **A local section of `ℐᵐ` read in `ℐⁿ` with `n < m` maps to zero in the conormal algebra.** -/
theorem toConormalAdd_reesPieceLower_of_lt {n m : ℕ} (h : n < m)
    (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (z : (idealPowerKernel (coborderIdeal i) m).val.obj W) :
    toConormalAdd i n W ((reesPieceLower (coborderIdeal i) h.le).val.app W z) = 0 := by
  rw [reesPieceLower_comp (coborderIdeal i) (Nat.le_succ n) (Nat.succ_le_of_lt h) W z]
  have h0 := pullbackSection_reesPieceLower_eq_zero i.liftCoborder n W.unop
    ((reesPieceLower (coborderIdeal i) (Nat.succ_le_of_lt h)).val.app W z)
  have hI : ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int
      n (i.liftCoborder ⁻¹ᵁ W.unop) 0 = 0 :=
    (congrArg (ungradedCommUnit Z (conormalAlgebra i).algebra
      (conormalAlgebra i).mul_comm_int (i.liftCoborder ⁻¹ᵁ W.unop)).hom
      (Stacks.GradedAlgebra.incl_zero _ _)).trans (map_zero _)
  exact (congrArg (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int n (i.liftCoborder ⁻¹ᵁ W.unop)) h0).trans hI

/-- The ungraded image of a pulled-back section depends only on the degree up to equality. -/
theorem inclPullbackSection_congr {d d' : ℤ} (h : d = d') (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (z : (reesPiece (coborderIdeal i) d).val.obj W)
    (z' : (reesPiece (coborderIdeal i) d').val.obj W)
    (hz : HEq z z') :
    ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int d
        (i.liftCoborder ⁻¹ᵁ W.unop)
        (Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) d)
          W.unop (i.liftCoborder ⁻¹ᵁ W.unop) le_rfl z) =
      ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int d'
        (i.liftCoborder ⁻¹ᵁ W.unop)
        (Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) d')
          W.unop (i.liftCoborder ⁻¹ᵁ W.unop) le_rfl z') := by
  subst h
  rw [eq_of_heq hz]

/-- The degree-`k` component of `Ψ` on sections, for every `k ∈ ℤ`: `toConormalAdd` in
nonnegative degrees and zero in negative ones. -/
def toConormalExtAdd (k : ℤ) (W : (Opens i.coborderRange.toScheme)ᵒᵖ) :
    ((extReesPiece (coborderIdeal i) k).val.obj W : Type u) →+
      algSections (conormalPushforwardAlgebra i i.liftCoborder) W :=
  if 0 ≤ k then toConormalAdd i k.toNat W else 0

/-- In a nonnegative degree `k`, `toConormalExtAdd` is `toConormalAdd` in degree `k`. -/
theorem toConormalExtAdd_of_nonneg {k : ℤ} (hk : 0 ≤ k) (W : (Opens i.coborderRange.toScheme)ᵒᵖ) :
    toConormalExtAdd i k W = toConormalAdd i k.toNat W := ite_eq_left hk

/-- In a negative degree, `toConormalExtAdd` is zero. -/
theorem toConormalExtAdd_of_neg {k : ℤ} (hk : k < 0) (W : (Opens i.coborderRange.toScheme)ᵒᵖ) :
    toConormalExtAdd i k W = 0 := ite_eq_right (not_le.mpr hk)

/-- **`Ψ` is unital.** -/
theorem toConormalExtAdd_one (W : (Opens i.coborderRange.toScheme)ᵒᵖ) :
    toConormalExtAdd i 0 W ((extReesOne (coborderIdeal i)).eval W) = 1 := by
  rw [toConormalExtAdd_of_nonneg i le_rfl]
  refine Eq.trans ?_ (ungradedAlgebraSheafIncl_one Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int (i.liftCoborder ⁻¹ᵁ W.unop))
  exact congrArg (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int 0 (i.liftCoborder ⁻¹ᵁ W.unop))
    (gradedPullback_one_eval i.liftCoborder (reesGradedAlgebra (coborderIdeal i)) W.unop).symm

/-- `toConormalExtAdd` commutes with restriction of sections. -/
theorem toConormalExtAdd_naturality (k : ℤ) {W W' : (Opens i.coborderRange.toScheme)ᵒᵖ}
    (f : W ⟶ W') (x : (extReesPiece (coborderIdeal i) k).val.obj W) :
    ((conormalPushforwardAlgebra i i.liftCoborder).right.obj.map f).hom
        (toConormalExtAdd i k W x) =
      toConormalExtAdd i k W' ((extReesPiece (coborderIdeal i) k).val.map f x) := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [toConormalExtAdd_of_neg i hk, toConormalExtAdd_of_neg i hk]
    exact map_zero _
  · rw [toConormalExtAdd_of_nonneg i hk, toConormalExtAdd_of_nonneg i hk]
    exact toConormalAdd_naturality i k.toNat f x

/-- `toConormalExtAdd` is linear over `𝒪_U`. -/
theorem toConormalExtAdd_smul (k : ℤ) (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (r : i.coborderRange.toScheme.ringCatSheaf.obj.obj W)
    (x : (extReesPiece (coborderIdeal i) k).val.obj W) :
    toConormalExtAdd i k W (r • x) =
      ((conormalPushforwardAlgebra i i.liftCoborder).hom.hom.app W).hom r *
        toConormalExtAdd i k W x := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [toConormalExtAdd_of_neg i hk, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, mul_zero]
  · rw [toConormalExtAdd_of_nonneg i hk]
    exact toConormalAdd_smul i k.toNat W r x

/-- `toConormalExtAdd` is multiplicative on degrees `p`, `q` with `p + q < 0`. -/
theorem toConormalExtAdd_mul_neg (p q : ℤ) (hpq : p + q < 0)
    (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (x : (extReesPiece (coborderIdeal i) p).val.obj W)
    (y : (extReesPiece (coborderIdeal i) q).val.obj W) :
    toConormalExtAdd i (p + q) W ((extReesMul (coborderIdeal i) p q).app W x y) =
      toConormalExtAdd i p W x * toConormalExtAdd i q W y := by
  rw [toConormalExtAdd_of_neg i hpq]
  rcases lt_or_ge p 0 with hp | hp
  · rw [toConormalExtAdd_of_neg i hp]
    exact (zero_mul _).symm
  · rw [toConormalExtAdd_of_neg i (by omega : q < 0)]
    exact (mul_zero _).symm

/-- `toConormalExtAdd` kills products in degree `p + q ≥ 0` when `p` or `q` is negative. -/
private theorem toConormalExtAdd_extReesMul_eq_zero (p q : ℤ) (hneg : p < 0 ∨ q < 0)
    (hpq : 0 ≤ p + q) (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (x : (extReesPiece (coborderIdeal i) p).val.obj W)
    (y : (extReesPiece (coborderIdeal i) q).val.obj W) :
    toConormalExtAdd i (p + q) W ((extReesMul (coborderIdeal i) p q).app W x y) = 0 := by
  rw [toConormalExtAdd_of_nonneg i hpq]
  exact toConormalAdd_reesPieceLower_of_lt i (m := p.toNat + q.toNat) (by omega) W
    ((reesMultiplication (coborderIdeal i) (p.toNat : ℤ) (q.toNat : ℤ)).app W x y)

/-- `toConormalExtAdd` is multiplicative on degrees `p`, `q` with `p < 0 ≤ p + q`. -/
theorem toConormalExtAdd_mul_left_neg (p q : ℤ) (hp : p < 0) (hpq : 0 ≤ p + q)
    (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (x : (extReesPiece (coborderIdeal i) p).val.obj W)
    (y : (extReesPiece (coborderIdeal i) q).val.obj W) :
    toConormalExtAdd i (p + q) W ((extReesMul (coborderIdeal i) p q).app W x y) =
      toConormalExtAdd i p W x * toConormalExtAdd i q W y := by
  rw [toConormalExtAdd_of_neg i hp]
  exact (toConormalExtAdd_extReesMul_eq_zero i p q (Or.inl hp) hpq W x y).trans (zero_mul _).symm

/-- `toConormalExtAdd` is multiplicative on degrees `p`, `q` with `q < 0 ≤ p + q`. -/
theorem toConormalExtAdd_mul_right_neg (p q : ℤ) (hq : q < 0) (hpq : 0 ≤ p + q)
    (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (x : (extReesPiece (coborderIdeal i) p).val.obj W)
    (y : (extReesPiece (coborderIdeal i) q).val.obj W) :
    toConormalExtAdd i (p + q) W ((extReesMul (coborderIdeal i) p q).app W x y) =
      toConormalExtAdd i p W x * toConormalExtAdd i q W y := by
  rw [toConormalExtAdd_of_neg i hq]
  exact (toConormalExtAdd_extReesMul_eq_zero i p q (Or.inr hq) hpq W x y).trans (mul_zero _).symm

/-- `toConormalExtAdd` is multiplicative on nonnegative degrees `p`, `q`. -/
theorem toConormalExtAdd_mul_nonneg (p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (x : (extReesPiece (coborderIdeal i) p).val.obj W)
    (y : (extReesPiece (coborderIdeal i) q).val.obj W) :
    toConormalExtAdd i (p + q) W ((extReesMul (coborderIdeal i) p q).app W x y) =
      toConormalExtAdd i p W x * toConormalExtAdd i q W y := by
  rw [toConormalExtAdd_of_nonneg i (add_nonneg hp hq), toConormalExtAdd_of_nonneg i hp,
    toConormalExtAdd_of_nonneg i hq]
  have hdeg : ((p + q).toNat : ℤ) = (p.toNat : ℤ) + (q.toNat : ℤ) := by omega
  have hA := inclPullbackSection_congr i hdeg W
    ((extReesMul (coborderIdeal i) p q).app W x y)
    ((reesMultiplication (coborderIdeal i) (p.toNat : ℤ) (q.toNat : ℤ)).app W x y)
    (reesPieceLower_heq (by omega) (by omega) W (coborderIdeal i) _)
  have hC := congrArg (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int ((p.toNat : ℤ) + (q.toNat : ℤ)) (i.liftCoborder ⁻¹ᵁ W.unop))
    (gradedPullback_mul_pullbackSection i.liftCoborder (reesGradedAlgebra (coborderIdeal i))
      (p.toNat : ℤ) (q.toNat : ℤ) W.unop x y)
  have hD := ungradedAlgebraSheafIncl_mul Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int (p.toNat : ℤ) (q.toNat : ℤ) (i.liftCoborder ⁻¹ᵁ W.unop)
    (Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) (p.toNat : ℤ))
      W.unop (i.liftCoborder ⁻¹ᵁ W.unop) le_rfl x)
    (Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) (q.toNat : ℤ))
      W.unop (i.liftCoborder ⁻¹ᵁ W.unop) le_rfl y)
  exact hA.trans (hC.symm.trans hD.symm)

/-- **`Ψ` is multiplicative.** -/
theorem toConormalExtAdd_mul (p q : ℤ) (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (x : (extReesPiece (coborderIdeal i) p).val.obj W)
    (y : (extReesPiece (coborderIdeal i) q).val.obj W) :
    toConormalExtAdd i (p + q) W ((extReesMul (coborderIdeal i) p q).app W x y) =
      toConormalExtAdd i p W x * toConormalExtAdd i q W y := by
  rcases lt_or_ge (p + q) 0 with hpq | hpq
  · exact toConormalExtAdd_mul_neg i p q hpq W x y
  rcases lt_or_ge p 0 with hp | hp
  · exact toConormalExtAdd_mul_left_neg i p q hp hpq W x y
  rcases lt_or_ge q 0 with hq | hq
  · exact toConormalExtAdd_mul_right_neg i p q hq hpq W x y
  exact toConormalExtAdd_mul_nonneg i p q hp hq W x y

/-- The degree-`k` component of `Ψ`, as a morphism of sheaves of `𝒪_U`-modules into the
degree-`k` piece of the degenerate grading of `g_* 𝒞_{Z/X,*}`. -/
def toConormalPiece (k : ℤ) :
    (extReesGradedAlgebra (coborderIdeal i)).piece k ⟶
      (constGraded (conormalPushforwardAlgebra i i.liftCoborder)).piece k where
  val :=
    { app := fun W => ModuleCat.homMk
        (AddCommGrpCat.ofHom (toConormalExtAdd i k W)) (fun r => by
          ext x
          exact (toConormalExtAdd_smul i k W r x).symm)
      naturality := fun f => by
        ext x
        exact (toConormalExtAdd_naturality i k f x).symm }

/-- On sections, `toConormalPiece` is `toConormalExtAdd`. -/
theorem toConormalPiece_app (k : ℤ) (W : (Opens i.coborderRange.toScheme)ᵒᵖ)
    (x : ((extReesGradedAlgebra (coborderIdeal i)).piece k).val.obj W) :
    (toConormalPiece i k).val.app W x = toConormalExtAdd i k W x := rfl

/-- **`Ψ` as a unital homomorphism of sheaves of graded algebras** into the degenerate grading of
`g_* 𝒞_{Z/X,*}`. -/
def toConormalUnitalHom :
    SheafOfModules.GradedAlgebra.UnitalHom (extReesGradedAlgebra (coborderIdeal i))
      (constGraded (conormalPushforwardAlgebra i i.liftCoborder)) where
  app := toConormalPiece i
  map_mul p q W x y := toConormalExtAdd_mul i p q W x y
  map_one W := toConormalExtAdd_one i W

/-- **The morphism of algebra sheaves `Ψ : 𝒪_U[t⁻¹, ℐt] ⟶ g_* 𝒞_{Z/X,*}`**, by the universal
property of the ungraded realization applied to `Stacks.Deformation.toConormalUnitalHom`. -/
def toConormalAlgebraHom :
    extReesAlgebraSheaf (coborderIdeal i) ⟶
      (algebraPushforward i.liftCoborder).obj (conormalAlgebraSheaf i) :=
  (ungradedAlgebraSheafIsoGradedAlgebraSheaf i.coborderRange.toScheme
      (extReesGradedAlgebra (coborderIdeal i)) (extReesGradedAlgebra_mul_comm _)).inv ≫
    ((ungradedAlgebraSheafHomEquiv (extReesGradedAlgebra (coborderIdeal i))
        (extReesGradedAlgebra_mul_comm _) (conormalPushforwardAlgebra i i.liftCoborder)).trans
      (ungradedCommHomEquiv (extReesGradedAlgebra (coborderIdeal i))
        (extReesGradedAlgebra_mul_comm _) (conormalPushforwardAlgebra i i.liftCoborder))).symm
      (toConormalUnitalHom i) ≫
    (algebraPushforward i.liftCoborder).map (ungradedAlgebraSheafIsoGradedAlgebraSheaf Z
      (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int).hom

end Stacks.Deformation

end
