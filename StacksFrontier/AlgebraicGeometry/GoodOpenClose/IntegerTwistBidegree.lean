module

public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.IntegerTwistPower
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerBidegree

/-!
# Multiplicativity of `𝒪_{W₁}(1)^{⊗ n} ≅ 𝒪_{W₁}(n)` in an arbitrary integer bidegree

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring and `W₁ ⊆ Proj 𝒮` the open `W_1` of Tag 01MU. This file
proves that the comparison `Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta` between
`𝒪_{W₁}(1)^{⊗ n}` and `𝒪_{W₁}(n)` is multiplicative in every integer bidegree.

## Main results

* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_mul`: multiplicativity of the comparison in an
  arbitrary integer bidegree — the addition law `Stacks.Ample.tensorPowModuleAddIso` of the tensor
  powers at `(n, m)`, followed by the comparison in degree `n + m`, is the comparisons in the
  degrees `n` and `m` on the two factors, followed by the canonical multiplication
  `Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistMulIso` of the twists at `(n, m)`.
* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistMulIso_assoc` and `twistMulIso_zero_left`,
  `twistMulIso_zero_right`: the associativity constraint and the two unit laws of the canonical
  multiplication of the twists on `W₁`, in arbitrary integer degrees.
* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_one_eq`: the degree one value of the comparison
  family is the canonical `𝒪_{W₁}(1)^{⊗ 1} ≅ 𝒪_{W₁}(1)`.
* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_mul_zero`: multiplicativity in the bidegree
  `(n, 0)` for an arbitrary integer `n`.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample
open Stacks.AlgebraicGeometry.CommonDegreeTwist
open Stacks.RelativeVeryAmple

namespace Stacks.AlgebraicGeometry.GoodOpenIntTwist

universe u

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### The multiplication of the twists on `W₁` is the pulled-back multiplication -/

section Pullback

open Stacks.AlgebraicGeometry.TwistTensor
open Stacks.PullbackTensorCoherence
open Stacks.RingedSpace

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- The open immersion of Tag 01MU's open `W₁` into `Proj 𝒮`, as a morphism of ringed spaces. -/
abbrev goodOpenHom :
    (goodOpen 𝒮).toScheme.toRingedSpace ⟶ (AlgebraicGeometry.Proj 𝒮).toRingedSpace :=
  (goodOpen 𝒮).ι.toLRSHom.toShHom

/-- The canonical multiplication `twistMulIso` of the twists on `W₁`, as a morphism from the tensor
product, in the monoidal structure of Stacks Tag 01CA on the sheaves of modules of the underlying
ringed space of `W₁`, of the twists pulled back along `goodOpenHom` in the degrees `n` and `m`, to
the pulled-back twist in the degree `n + m`. -/
def twistMulHom (n m : ℤ) :
    pullbackTwist 𝒮 (goodOpenHom 𝒮) n ⊗ pullbackTwist 𝒮 (goodOpenHom 𝒮) m ⟶
      pullbackTwist 𝒮 (goodOpenHom 𝒮) (n + m) :=
  (twistMulIso 𝒮 n m).hom

/-- `twistMulHom 𝒮 n m` is the forward morphism of `twistMulIso 𝒮 n m`. -/
theorem twistMulHom_eq (n m : ℤ) : twistMulHom 𝒮 n m = (twistMulIso 𝒮 n m).hom := rfl

/-- The multiplication `twistMulHom` on `W₁` is the multiplication `pullbackTwistMul` of the twists
pulled back along the open immersion `W₁ ⟶ Proj 𝒮`. -/
theorem twistMulHom_eq_pullbackTwistMul (n m : ℤ) :
    twistMulHom 𝒮 n m = pullbackTwistMul 𝒮 (goodOpenHom 𝒮) n m := by
  have hinv : inv (pullbackTensorComparison (goodOpenHom 𝒮)
        (TwistTensor.twist 𝒮 n) (TwistTensor.twist 𝒮 m)) =
      (pullbackTensorModulesIso (goodOpen 𝒮).ι
        (twistingSheaf 𝒮 n) (twistingSheaf 𝒮 m)).inv :=
    IsIso.inv_eq_of_hom_inv_id (pullbackTensorModulesIso (goodOpen 𝒮).ι
      (twistingSheaf 𝒮 n) (twistingSheaf 𝒮 m)).hom_inv_id
  rw [twistMulHom, pullbackTwistMul, hinv]
  rfl

/-- Associativity of the multiplication `twistMulHom` of the twists on `W₁`, in every triple of
integer degrees, up to the transport along `n + (m + k) = n + m + k`. -/
theorem twistMulHom_assoc (n m k : ℤ) :
    twistMulHom 𝒮 n m ▷ pullbackTwist 𝒮 (goodOpenHom 𝒮) k ≫ twistMulHom 𝒮 (n + m) k =
      (α_ (pullbackTwist 𝒮 (goodOpenHom 𝒮) n) (pullbackTwist 𝒮 (goodOpenHom 𝒮) m)
          (pullbackTwist 𝒮 (goodOpenHom 𝒮) k)).hom ≫
        pullbackTwist 𝒮 (goodOpenHom 𝒮) n ◁ twistMulHom 𝒮 m k ≫
          twistMulHom 𝒮 n (m + k) ≫
            eqToHom (congrArg (restrictedTwist 𝒮 (goodOpen 𝒮))
              (show n + (m + k) = n + m + k from by ring)) := by
  rw [twistMulHom_eq_pullbackTwistMul, twistMulHom_eq_pullbackTwistMul,
    twistMulHom_eq_pullbackTwistMul, twistMulHom_eq_pullbackTwistMul]
  exact (pullbackTwistMul_assoc 𝒮 (goodOpenHom 𝒮) n m k).trans <| congrArg (fun φ ↦
    (α_ (pullbackTwist 𝒮 (goodOpenHom 𝒮) n) (pullbackTwist 𝒮 (goodOpenHom 𝒮) m)
        (pullbackTwist 𝒮 (goodOpenHom 𝒮) k)).hom ≫
      pullbackTwist 𝒮 (goodOpenHom 𝒮) n ◁ pullbackTwistMul 𝒮 (goodOpenHom 𝒮) m k ≫
        pullbackTwistMul 𝒮 (goodOpenHom 𝒮) n (m + k) ≫ φ)
    (eqToHom_map (pullbackFunctor (goodOpenHom 𝒮))
      (congrArg (TwistTensor.twist 𝒮) (add_assoc n m k).symm))

end Pullback

/-! ### The three laws of the multiplication of the twists on `W₁` -/

section Monoidal

open Stacks.AlgebraicGeometry.ThetaMul
open Stacks.AlgebraicGeometry.TwistTensor (pullbackTwistMul_one_left pullbackTwistMul_one_right)

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal

/-- Associativity of the canonical multiplication `twistMulIso` of the twists on `W₁`, in every
triple of integer degrees, against the associator of the strict monoidal structure of Stacks Tag
01CA, up to the transport along `n + (m + k) = n + m + k`. -/
theorem twistMulIso_assoc (n m k : ℤ) :
    (twistMulIso 𝒮 n m).hom ▷ twist 𝒮 k ≫ (twistMulIso 𝒮 (n + m) k).hom =
      (α_ (twist 𝒮 n) (twist 𝒮 m) (twist 𝒮 k)).hom ≫
        twist 𝒮 n ◁ (twistMulIso 𝒮 m k).hom ≫
          (twistMulIso 𝒮 n (m + k)).hom ≫
            (twistCongr 𝒮 (show n + (m + k) = n + m + k from by ring)).hom :=
  twistMulHom_assoc 𝒮 n m k

/-- The unit `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit` of the multiplication of the
twists pulled back along `W₁ ⟶ Proj 𝒮` is the inverse of
`Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistZeroIsoUnit`. -/
theorem pullbackTwistUnit_eq_twistZeroIsoUnit_inv :
    Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit 𝒮 (goodOpenHom 𝒮) =
      (twistZeroIsoUnit 𝒮).inv := rfl

/-- The left unit law of the multiplication of the twists on `W₁`, in every integer degree. -/
theorem twistMulIso_zero_left (m : ℤ) :
    (twistZeroIsoUnit 𝒮).inv ▷ twist 𝒮 m ≫ (twistMulIso 𝒮 0 m).hom =
      (λ_ (twist 𝒮 m)).hom ≫ (twistCongr 𝒮 (show m = 0 + m from by ring)).hom := by
  rw [← twistMulHom_eq, twistMulHom_eq_pullbackTwistMul]
  refine Eq.trans (pullbackTwistMul_one_left 𝒮 (goodOpenHom 𝒮) m) ?_
  rw [eqToHom_map]
  rfl

/-- The right unit law of the multiplication of the twists on `W₁`, in every integer degree. -/
theorem twistMulIso_zero_right (n : ℤ) :
    twist 𝒮 n ◁ (twistZeroIsoUnit 𝒮).inv ≫ (twistMulIso 𝒮 n 0).hom =
      (ρ_ (twist 𝒮 n)).hom ≫ (twistCongr 𝒮 (show n = n + 0 from by ring)).hom := by
  rw [← twistMulHom_eq, twistMulHom_eq_pullbackTwistMul]
  refine Eq.trans (pullbackTwistMul_one_right 𝒮 (goodOpenHom 𝒮) n) ?_
  rw [eqToHom_map]
  rfl

/-! ### The two ends of the comparison family -/

/-- The degree zero value of the comparison family is the canonical
`𝒪_{W₁}(1)^{⊗ 0} ≅ 𝒪_{W₁} ≅ 𝒪_{W₁}(0)`, with the two reindexings along `((0 : ℕ) : ℤ) = 0`
removed. -/
theorem theta_zero_hom :
    (theta 𝒮 0).hom =
      (tensorPowModuleZeroIso (goodOpen 𝒮).toScheme (twist 𝒮 1)).hom ≫
        (twistZeroIsoUnit 𝒮).inv := by
  rw [show theta 𝒮 0 = natTheta 𝒮 0 from theta_natCast 𝒮 0, natTheta]
  simp only [Iso.trans_hom, Iso.symm_hom, tensorPowModuleCongr, twistCongr, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The degree one value of the comparison family is the canonical
`𝒪_{W₁}(1)^{⊗ 1} ≅ 𝒪_{W₁}(1)`. -/
theorem theta_one_eq : theta 𝒮 1 = tpowOne 𝒮 := by
  have key := unit_tensorHom_cancel
      (tensorPowModuleZeroIso (goodOpen 𝒮).toScheme (twist 𝒮 1)).hom
      (twistZeroIsoUnit 𝒮).inv
      (tpowOne 𝒮).hom
      ((natTheta 𝒮 0).hom ⊗ₘ (tpowOne 𝒮).hom)
      (twistMulIso 𝒮 0 1).hom
      (twistCongr 𝒮 (show (0 : ℤ) + 1 = 1 from by ring)).hom
      (twistCongr 𝒮 (show (1 : ℤ) = 0 + 1 from by ring)).hom
      ((tpowCongr 𝒮 (show (1 : ℤ) = 0 + 1 from by ring)).hom ≫ (tpowAdd 𝒮 0 1).inv)
      ((tensorPowModuleAddIso (goodOpen 𝒮).toScheme (twist 𝒮 1) 0 1).hom ≫
        (tensorPowModuleCongr (goodOpen 𝒮).toScheme (twist 𝒮 1)
          (show (0 : ℤ) + 1 = 1 from by lia)).hom)
      (congrArg (fun φ ↦ φ ⊗ₘ (tpowOne 𝒮).hom) (theta_zero_hom 𝒮))
      (twistMulIso_zero_left 𝒮 1)
      (by
        simp only [twistCongr, eqToIso.hom, eqToHom_refl, Category.id_comp]
        rfl)
      (tensorPowModuleAddIso_zero_left_int (goodOpen 𝒮).toScheme (twist 𝒮 1) 1)
      (by
        simp only [tensorPowModuleCongr, eqToIso.hom, Iso.inv_hom_id_assoc, eqToHom_refl,
          Category.id_comp]
        rfl)
  refine Iso.ext ?_
  rw [show theta 𝒮 1 = natTheta 𝒮 1 from theta_natCast 𝒮 1, natTheta_succ]
  simp only [Iso.trans_hom, Iso.symm_hom, MonoidalCategory.tensorIso_hom]
  exact key

/-- Multiplicativity of the comparison in the bidegree `(n, 1)`, with the comparison in degree one
on the second factor. -/
theorem theta_mul_one' (n : ℤ) :
    (tpowAdd 𝒮 n 1).hom ≫ (theta 𝒮 (n + 1)).hom =
      ((theta 𝒮 n).hom ⊗ₘ (theta 𝒮 1).hom) ≫ (twistMulIso 𝒮 n 1).hom := by
  rw [theta_one_eq]
  exact theta_mul_one 𝒮 n

/-! ### The chase over the second degree -/

/-- The comparison family commutes with the transport along an equality of degrees. -/
theorem theta_congr {n m : ℤ} (h : m = n) :
    (theta 𝒮 m).hom =
      (tpowCongr 𝒮 h).hom ≫ (theta 𝒮 n).hom ≫ (twistCongr 𝒮 h.symm).hom := by
  cases h
  simp only [tensorPowModuleCongr, twistCongr, eqToIso.hom, eqToHom_refl, Category.id_comp,
    Category.comp_id]

/-- Multiplicativity of the comparison in a bidegree `(p, q)` gives it in every bidegree `(p', q')`
with `p = p'` and `q = q'`. -/
theorem theta_mul_of_eq {p q p' q' : ℤ} (hp : p = p') (hq : q = q')
    (H : (tpowAdd 𝒮 p q).hom ≫ (theta 𝒮 (p + q)).hom =
      ((theta 𝒮 p).hom ⊗ₘ (theta 𝒮 q).hom) ≫ (twistMulIso 𝒮 p q).hom) :
    (tpowAdd 𝒮 p' q').hom ≫ (theta 𝒮 (p' + q')).hom =
      ((theta 𝒮 p').hom ⊗ₘ (theta 𝒮 q').hom) ≫ (twistMulIso 𝒮 p' q').hom := by
  subst hp hq
  exact H

/-- Multiplicativity of the comparison in the bidegree `(n, 0)`, for an arbitrary integer `n`. -/
theorem theta_mul_zero (n : ℤ) :
    (tpowAdd 𝒮 n 0).hom ≫ (theta 𝒮 (n + 0)).hom =
      ((theta 𝒮 n).hom ⊗ₘ (theta 𝒮 0).hom) ≫ (twistMulIso 𝒮 n 0).hom := by
  rw [theta_congr 𝒮 (show n + 0 = n from by ring)]
  exact Eq.trans (Category.assoc _ _ _).symm <| tensorHom_unit_square
    (tensorPowModuleZeroIso (goodOpen 𝒮).toScheme (twist 𝒮 1)).hom
    (twistZeroIsoUnit 𝒮).inv
    (theta 𝒮 n).hom
    ((theta 𝒮 n).hom ⊗ₘ (theta 𝒮 0).hom)
    (twistMulIso 𝒮 n 0).hom
    (twistCongr 𝒮 (show n = n + 0 from by ring)).hom
    ((tensorPowModuleAddIso (goodOpen 𝒮).toScheme (twist 𝒮 1) n 0).hom ≫
      (tensorPowModuleCongr (goodOpen 𝒮).toScheme (twist 𝒮 1)
        (show n + 0 = n from by lia)).hom)
    (congrArg (fun φ ↦ (theta 𝒮 n).hom ⊗ₘ φ) (theta_zero_hom 𝒮))
    (twistMulIso_zero_right 𝒮 n)
    (tensorPowModuleAddIso_zero_right_int (goodOpen 𝒮).toScheme (twist 𝒮 1) n)

/-- Multiplicativity of the comparison in the bidegree `(p, b + c)` is equivalent to the same
square with the transport along `p + (b + c) = p + b + c` moved from the comparison to the
canonical multiplication of the twists. -/
theorem theta_mul_corner_iff (p b c : ℤ) :
    ((tpowAdd 𝒮 p (b + c)).hom ≫ (theta 𝒮 (p + (b + c))).hom =
        ((theta 𝒮 p).hom ⊗ₘ (theta 𝒮 (b + c)).hom) ≫ (twistMulIso 𝒮 p (b + c)).hom) ↔
      (((tpowAdd 𝒮 p (b + c)).hom ≫
            (tpowCongr 𝒮 (show p + (b + c) = p + b + c from by ring)).hom) ≫
          (theta 𝒮 (p + b + c)).hom =
        ((theta 𝒮 p).hom ⊗ₘ (theta 𝒮 (b + c)).hom) ≫ (twistMulIso 𝒮 p (b + c)).hom ≫
          (twistCongr 𝒮 (show p + (b + c) = p + b + c from by ring)).hom) := by
  have h : p + (b + c) = p + b + c := by ring
  rw [theta_congr 𝒮 h, ← cancel_mono (twistCongr 𝒮 h).hom]
  simp only [Category.assoc, twistCongr, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- Multiplicativity of the comparison `𝒪_{W₁}(1)^{⊗ n} ≅ 𝒪_{W₁}(n)` in an arbitrary integer
bidegree: the addition law `Stacks.Ample.tensorPowModuleAddIso` of the tensor powers at `(n, m)`,
followed by the comparison in the degree `n + m`, is the comparisons in the degrees `n` and `m` on
the two factors, followed by the canonical multiplication `twistMulIso` of the twists at `(n, m)` —
the multiplication map `Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap` of
Stacks Tag 01MO read on `W₁`. -/
theorem theta_mul (n m : ℤ) :
    (tpowAdd 𝒮 n m).hom ≫ (theta 𝒮 (n + m)).hom =
      ((theta 𝒮 n).hom ⊗ₘ (theta 𝒮 m).hom) ≫ (twistMulIso 𝒮 n m).hom := by
  induction m using Int.induction_on with
  | zero => exact theta_mul_zero 𝒮 n
  | succ i ih =>
      exact (theta_mul_corner_iff 𝒮 n (i : ℤ) 1).mpr
        (square_step
          (tensorPowModuleAddIso_assoc_int (goodOpen 𝒮).toScheme (twist 𝒮 1) n (i : ℤ) 1)
          (twistMulIso_assoc 𝒮 n (i : ℤ) 1) ih
          (theta_mul_one' 𝒮 (n + (i : ℤ))) (theta_mul_one' 𝒮 (i : ℤ)))
  | pred i ih =>
      exact Stacks.Monoidal.square_step_left
        (tpowAdd 𝒮 1 (-1) ≪≫ tpowCongr 𝒮 (show (1 : ℤ) + -1 = 0 from by ring) ≪≫
          tensorPowModuleZeroIso (goodOpen 𝒮).toScheme (twist 𝒮 1))
        (tensorPowModuleAddIso_assoc_int (goodOpen 𝒮).toScheme (twist 𝒮 1) n
          (-(i : ℤ) - 1) 1)
        (twistMulIso_assoc 𝒮 n (-(i : ℤ) - 1) 1)
        (theta_mul_one' 𝒮 (n + (-(i : ℤ) - 1)))
        (theta_mul_one' 𝒮 (-(i : ℤ) - 1))
        ((theta_mul_corner_iff 𝒮 n (-(i : ℤ) - 1) 1).mp
          (theta_mul_of_eq 𝒮 rfl (show -(i : ℤ) = -(i : ℤ) - 1 + 1 from by lia) ih))

end Monoidal

end Stacks.AlgebraicGeometry.GoodOpenIntTwist

end
