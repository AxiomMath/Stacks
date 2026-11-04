module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwist
public import StacksFrontier.AlgebraicGeometry.TwistGenerator.Negative

/-!
# The invertible homogeneous function of a trivializing open

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `L^⋆ ⟶ X` the
complement of the zero section of the associated line bundle. Over an open `W` of `X` on which
`L` is trivial, the homogeneous function of a generator of `L^{⊗ n}` is a unit whose inverse is
the homogeneous function of a generator of `L^{⊗ -n}`. The generators are those of the family
`Stacks.AlgebraicGeometry.TwistGenerator.genInt`: one section of `L^{⊗ n}` over `W` for every
`n : ℤ`, multiplicative in the nonnegative degrees and extended to the negative ones by the degree
`-1` generator.

## Main definitions

* `Stacks.LineBundle.Situation.laurentGenUnit`: **the unit of the Laurent algebra sections over
  a trivializing open** given by the degree-one generator, with the degree `-1` generator as its
  inverse.

## Main results

* `Stacks.LineBundle.Situation.laurentGenUnit_zpow`: **every integer power of that unit is the
  homogeneous section of the generator family in that degree.**
* `Stacks.LineBundle.Situation.laurentFunctionOfOpen_genInt_mul`: **the homogeneous functions of
  the generator family in degrees `-n` and `n` multiply to `1`.**
* `Stacks.LineBundle.Situation.isHomogeneousLaurentForm_of_smul_genInt`: **the converse of the
  degree bookkeeping over a trivializing affine open**, with no auxiliary pair of sections to
  supply: a form whose product with the function of the degree-`n` generator is homogeneous of
  degree `n + m` is itself homogeneous of degree `m`.

## Implementation notes

The identity `gen (-n) * gen n = 1` is stated in the *ungraded* ring of sections of the Laurent
algebra over `W`, where `Stacks.LineBundle.Situation.laurentAlgebraSheafIncl` is multiplicative
with the degrees adding. Between graded pieces it would be an equation in degree `-n + n`, which
for a variable `n` is not the term `0`; in the ungraded ring it is `u⁻ⁿ * uⁿ = 1` for a single
unit `u`.

The powers of the unit are handled through `Units.val` and `Units.inv` rather than through a
coercion written as a type ascription: the ascription does not reach the instance for the
coercion out of the unit group of this ring of sections.

## References

* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH), clause (1)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU), the tensor powers and
  their multiplication
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.TwistGenerator

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

variable {W : D.X.Opens}
  (e : D.L.over W ≅ SheafOfModules.unit (D.X.ringCatSheaf.over W))

/-- **The unit of the Laurent algebra sections over a trivializing open**: the homogeneous
section of degree one attached to the degree-one generator of the trivialization, whose inverse
is the homogeneous section of degree `-1` attached to the degree `-1` generator. -/
def Situation.laurentGenUnit :
    (Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf W)ˣ where
  val := D.laurentAlgebraSheafIncl 1 W (genOne D.L e)
  inv := D.laurentAlgebraSheafIncl (-1) W (genNegOne D.L e)
  val_inv := by
    refine (D.laurentAlgebraSheafIncl_mul 1 (-1) W (genOne D.L e) (genNegOne D.L e)).trans ?_
    refine Eq.trans (congrArg (D.laurentAlgebraSheafIncl 0 W) (eq_of_heq
      (Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm D.X.sheaf.obj
        D.X.ringCatSheaf.property D.L 1 (-1) (op W) (genOne D.L e) (genNegOne D.L e)))) ?_
    exact Eq.trans (congrArg (D.laurentAlgebraSheafIncl 0 W)
      (mulBilinear_genNegOne_genOne D.L e)) (D.laurentAlgebraSheafIncl_one W)
  inv_val := by
    refine (D.laurentAlgebraSheafIncl_mul (-1) 1 W (genNegOne D.L e) (genOne D.L e)).trans ?_
    exact Eq.trans (congrArg (D.laurentAlgebraSheafIncl 0 W)
      (mulBilinear_genNegOne_genOne D.L e)) (D.laurentAlgebraSheafIncl_one W)

/-- The unit is the homogeneous section of the degree-one generator. -/
theorem Situation.laurentGenUnit_val :
    (D.laurentGenUnit e).val = D.laurentAlgebraSheafIncl 1 W (genOne D.L e) :=
  rfl

/-- The inverse of the unit is the homogeneous section of the degree `-1` generator. -/
theorem Situation.laurentGenUnit_inv :
    (D.laurentGenUnit e).inv = D.laurentAlgebraSheafIncl (-1) W (genNegOne D.L e) :=
  rfl

/-- A power step: if `u ^ k = x` and `x * u = z`, then `u ^ (k + 1) = z`. -/
private theorem pow_succ_eq_of_mul_eq {M : Type*} [Monoid M] {u x z : M} {k : ℕ}
    (ih : u ^ k = x) (h : x * u = z) : u ^ (k + 1) = z := by
  rw [pow_succ, ih, h]

/-- **The nonnegative powers of the unit are the homogeneous sections of the generator
family.** -/
theorem Situation.laurentGenUnit_pow (k : ℕ) :
    (D.laurentGenUnit e).val ^ k =
      D.laurentAlgebraSheafIncl (k : ℤ) W (gen D.L e k) := by
  induction k with
  | zero =>
      exact (pow_zero (D.laurentGenUnit e).val).trans
        (D.laurentAlgebraSheafIncl_one W).symm
  | succ k ih =>
      exact pow_succ_eq_of_mul_eq ih <|
        D.laurentAlgebraSheafIncl_mul (k : ℤ) 1 W (gen D.L e k) (genOne D.L e)

/-- **The negative powers of the unit are the homogeneous sections of the generator family.** -/
theorem Situation.laurentGenUnit_inv_pow (k : ℕ) :
    (D.laurentGenUnit e).inv ^ (k + 1) =
      D.laurentAlgebraSheafIncl (Int.negSucc k) W (genNeg D.L e k) := by
  induction k with
  | zero => exact (pow_one (D.laurentGenUnit e).inv).trans (D.laurentGenUnit_inv e)
  | succ k ih =>
      exact pow_succ_eq_of_mul_eq ih <| D.laurentAlgebraSheafIncl_mul (Int.negSucc k)
        (Int.negSucc 0) W (genNeg D.L e k) (genNegOne D.L e)

/-- **Every integer power of the unit is the homogeneous section of the generator family in that
degree.** -/
theorem Situation.laurentGenUnit_zpow (n : ℤ) :
    (D.laurentGenUnit e ^ n).val = D.laurentAlgebraSheafIncl n W (genInt D.L e n) := by
  cases n with
  | ofNat k =>
      refine Eq.trans (congrArg Units.val (zpow_natCast (D.laurentGenUnit e) k)) ?_
      exact (Units.val_pow_eq_pow_val (D.laurentGenUnit e) k).trans (D.laurentGenUnit_pow e k)
  | negSucc k =>
      refine Eq.trans (congrArg Units.val (zpow_negSucc (D.laurentGenUnit e) k)) ?_
      refine Eq.trans (congrArg Units.val (inv_pow (D.laurentGenUnit e) (k + 1)).symm) ?_
      exact (Units.val_pow_eq_pow_val (D.laurentGenUnit e)⁻¹ (k + 1)).trans
        (D.laurentGenUnit_inv_pow e k)

/-- **The homogeneous sections of the generator family in degrees `-n` and `n` multiply to `1`**
in the Laurent algebra over a trivializing open: they are the `-n`th and `n`th powers of one
unit. -/
theorem Situation.laurentAlgebraSheafIncl_genInt_mul (n : ℤ) :
    D.laurentAlgebraSheafIncl (-n) W (genInt D.L e (-n)) *
        D.laurentAlgebraSheafIncl n W (genInt D.L e n) = 1 := by
  refine Eq.trans (congrArg₂ (· * ·) (D.laurentGenUnit_zpow e (-n)).symm
    (D.laurentGenUnit_zpow e n).symm) ?_
  refine Eq.trans (Units.val_mul (D.laurentGenUnit e ^ (-n)) (D.laurentGenUnit e ^ n)).symm ?_
  refine Eq.trans (congrArg Units.val (congrArg (· * D.laurentGenUnit e ^ n)
    (zpow_neg (D.laurentGenUnit e) n))) ?_
  exact congrArg Units.val (inv_mul_cancel (D.laurentGenUnit e ^ n))

/-- **The homogeneous functions of the generator family in degrees `-n` and `n` multiply to
`1`** on the inverse image of a trivializing open, the universal map of Tag 01LX(3) being a ring
map. -/
theorem Situation.laurentFunctionOfOpen_genInt_mul (n : ℤ) :
    D.laurentFunctionOfOpen (-n) W (genInt D.L e (-n)) *
        D.laurentFunctionOfOpen n W (genInt D.L e n) = 1 :=
  ((map_mul (D.laurentFunctionHom W).hom _ _).symm.trans
    (congrArg (D.laurentFunctionHom W).hom
      (D.laurentAlgebraSheafIncl_genInt_mul e n))).trans
    (map_one (D.laurentFunctionHom W).hom)

/-- **The homogeneous functions of the generator family in degrees `-n` and `n` multiply to `1`
over a trivializing affine open.** -/
theorem Situation.laurentFunction_genInt_mul (U : D.X.affineOpens)
    (eU : D.L.over U.1 ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U.1)) (n : ℤ) :
    D.laurentFunction (-n) U (genInt D.L eU (-n)) *
        D.laurentFunction n U (genInt D.L eU n) = 1 := by
  rw [← D.laurentFunctionOfOpen_affine (-n) U (genInt D.L eU (-n)),
    ← D.laurentFunctionOfOpen_affine n U (genInt D.L eU n)]
  exact D.laurentFunctionOfOpen_genInt_mul eU n

/-- **A form whose product with the homogeneous function of the degree-`n` generator is
homogeneous of degree `n + m` is itself homogeneous of degree `m`**, over a trivializing affine
open. This is `Stacks.LineBundle.Situation.isHomogeneousLaurentForm_of_smul` with the invertible
pair supplied. -/
theorem Situation.isHomogeneousLaurentForm_of_smul_genInt {p : ℕ} {m : ℤ} (U : D.X.affineOpens)
    (eU : D.L.over U.1 ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U.1)) (n : ℤ)
    {ω : (D.laurentFormsAlgebra.piece (p : ℤ)).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1))}
    (hω : D.IsHomogeneousLaurentForm U p (n + m)
      (D.laurentFunction n U (genInt D.L eU n) • ω)) :
    D.IsHomogeneousLaurentForm U p m ω :=
  D.isHomogeneousLaurentForm_of_smul U n (genInt D.L eU n) (genInt D.L eU (-n))
    (D.laurentFunction_genInt_mul U eU n) hω

end Stacks.LineBundle

end
