module

public import StacksFrontier.AlgebraicGeometry.TwistGenerator.Basic

/-!
# The generator family of the tensor powers in negative degrees

Let `S` be a scheme, `ℒ` an invertible `𝒪_S`-module and `W` an open on which `ℒ` is trivial,
with a trivialization `e`. The multiplicative family `gen d` of sections of `ℒ^{⊗ d}` over `W`,
defined in every nonnegative degree by recursion through the Laurent multiplication of
[Stacks, Tag 01CU], extends to the negative degrees: there is one section
`Stacks.AlgebraicGeometry.TwistGenerator.genInt n` of `ℒ^{⊗ n}` over `W` for every `n : ℤ`.

Multiplication by the degree-one generator is bijective on sections in every integer degree
(`TwistGenerator.bijective_mulBilinear_genOne`), so the degree `-1` generator is the section whose
product with `gen 1` is `1`, and the lower degrees are obtained from it by the same recursion as
the positive ones.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistGenerator.genNegOne`: **the degree `-1` generator**, the
  section of `ℒ^{⊗ -1}` over `W` whose product with the degree-one generator is `1`.
* `Stacks.AlgebraicGeometry.TwistGenerator.genNeg`: the family in the negative degrees,
  `genNeg k` a section of `ℒ^{⊗ (-k-1)}`, by recursion through the Laurent multiplication.
* `Stacks.AlgebraicGeometry.TwistGenerator.genInt`: **the family in every integer degree**,
  assembled from `gen` and `genNeg`.

## Main results

* `Stacks.AlgebraicGeometry.TwistGenerator.mulBilinear_genNegOne_genOne`: **the defining
  property of the degree `-1` generator**, `genNegOne * genOne = 1`.
* `Stacks.AlgebraicGeometry.TwistGenerator.genNeg_succ`: the defining recursion of the negative
  family.
* `Stacks.AlgebraicGeometry.TwistGenerator.genInt_natCast`,
  `TwistGenerator.genInt_negSucc`, `TwistGenerator.genInt_zero`,
  `TwistGenerator.genInt_one` and `TwistGenerator.genInt_neg_one`: the family read in each shape
  of degree.
* `Stacks.AlgebraicGeometry.TwistGenerator.bijective_tensorSectionsAt_genInt`: **tensoring with
  the generator of degree `n` is bijective on sections over the trivializing open, for every
  integer `n`** and every module.

## Implementation notes

The negative family is indexed by `Int.negSucc k`, not by `-(k : ℤ)`: `Int.add` reduces on two
`Int.negSucc` arguments, `negSucc m + negSucc n = negSucc (m + n + 1)`, so each recursive step
lands in the declared degree with no cast, while `-(k : ℤ) + -1` does not reduce for a variable
`k`. `genInt` matches on the constructors of `ℤ`, and its reading lemmas hold by `rfl`.

The degree `-1` generator is a choice, made by `Function.surjInv`;
`mulBilinear_genNegOne_genOne` is its defining property.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf structureSheaf)

universe u

namespace Stacks.AlgebraicGeometry.TwistGenerator

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

variable {W : S.Opens} (e : L.over W ≅ SheafOfModules.unit (S.ringCatSheaf.over W))

/-- **The degree `-1` generator**: the section of `ℒ^{⊗ -1}` over `W` whose product with the
degree-one generator is the section `1` of the structure sheaf. -/
def genNegOne : (pow L (-1)).val.obj (op W) :=
  Function.surjInv (f := fun a : (pow L (-1)).val.obj (op W) =>
    (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L (-1) 1).app (op W) a
      (genOne L e)) (bijective_mulBilinear_genOne L e (-1)).2
    (show (pow L (-1 + 1)).val.obj (op W) from (1 : Γ(S, W)))

/-- **The defining property of the degree `-1` generator**: its product with the degree-one
generator is `1`. -/
theorem mulBilinear_genNegOne_genOne :
    (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L (-1) 1).app (op W)
        (genNegOne L e) (genOne L e) =
      (show (pow L (-1 + 1)).val.obj (op W) from (1 : Γ(S, W))) :=
  Function.surjInv_eq (f := fun a : (pow L (-1)).val.obj (op W) =>
    (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L (-1) 1).app (op W) a
      (genOne L e)) (bijective_mulBilinear_genOne L e (-1)).2 _

/-- **The generator family in the negative degrees.** In degree `-1` it is `genNegOne`, and each
lower degree is obtained from the previous one by multiplying with `genNegOne` in the Laurent
algebra of the tensor powers. The index `k` carries the degree `Int.negSucc k`, that is
`-k - 1`. -/
def genNeg : (k : ℕ) → (pow L (Int.negSucc k)).val.obj (op W)
  | 0 => genNegOne L e
  | k + 1 => show (pow L (Int.negSucc k + Int.negSucc 0)).val.obj (op W) from
      (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L
        (Int.negSucc k) (Int.negSucc 0)).app (op W) (genNeg k) (genNegOne L e)

/-- The negative family in degree `-1` is the degree `-1` generator. -/
theorem genNeg_zero : genNeg L e 0 = genNegOne L e := rfl

/-- The defining recursion of the negative family: the generator in degree `-k-2` is the product
of the generator in degree `-k-1` with the degree `-1` generator. -/
theorem genNeg_succ (k : ℕ) :
    genNeg L e (k + 1) =
      (TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L
        (Int.negSucc k) (Int.negSucc 0)).app (op W) (genNeg L e k) (genNegOne L e) := rfl

/-- **The generator family in every integer degree**: one section of `ℒ^{⊗ n}` over the
trivializing open `W` for each `n : ℤ`, the nonnegative degrees from
`Stacks.AlgebraicGeometry.TwistGenerator.gen` and the negative ones from
`TwistGenerator.genNeg`. -/
def genInt : (n : ℤ) → (pow L n).val.obj (op W)
  | Int.ofNat k => gen L e k
  | Int.negSucc k => genNeg L e k

/-- In a nonnegative degree the integer family is the family of `TwistGenerator.gen`. -/
theorem genInt_natCast (k : ℕ) : genInt L e (k : ℤ) = gen L e k := rfl

/-- In a negative degree the integer family is the family of `TwistGenerator.genNeg`. -/
theorem genInt_negSucc (k : ℕ) : genInt L e (Int.negSucc k) = genNeg L e k := rfl

/-- The integer family in degree `0` is the section `1` of the structure sheaf. -/
theorem genInt_zero : genInt L e 0 = (1 : Γ(S, W)) := rfl

/-- The integer family in degree `1` is the degree-one generator. -/
theorem genInt_one : genInt L e 1 = genOne L e :=
  eq_of_heq (TensorPower.mulBilinear_one_mul S.sheaf.obj S.ringCatSheaf.property L 1
    (op W) (genOne L e))

/-- The integer family in degree `-1` is the degree `-1` generator. -/
theorem genInt_neg_one : genInt L e (-1) = genNegOne L e := rfl

/-! ### Tensoring with the generator, in every integer degree -/

/-- Given that tensoring with `g'` is bijective for every module, tensoring with `g` is bijective
if and only if tensoring with the product `g * g'` is. -/
private theorem bijective_tensorSectionsAt_iff_mulBilinear {n m : ℤ} (A : S.Modules)
    (g : (pow L n).val.obj (op W)) (g' : (pow L m).val.obj (op W))
    (hg' : ∀ B : S.Modules, Function.Bijective (fun y : B.val.obj (op W) =>
      tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) B (pow L m) y g')) :
    Function.Bijective (fun y : A.val.obj (op W) =>
        tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) A (pow L n) y g) ↔
      Function.Bijective (fun y : A.val.obj (op W) =>
        tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) A (pow L (n + m)) y
          ((TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L n m).app (op W)
            g g')) :=
  (((bijective_app_of_iso (Invertible.tensorProductIso S.sheaf.obj S.ringCatSheaf.property
      (Iso.refl A) (TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L n m))
      (op W)).comp
    ((bijective_app_of_iso (Invertible.tensorProductAssociator S.sheaf.obj
      S.ringCatSheaf.property A (pow L n) (pow L m)) (op W)).comp
      (hg' (((Tensor.sheafTensor S.sheaf).obj A).obj (pow L n))))).of_comp_iff' _).symm.trans
    (iff_of_eq (congrArg Function.Bijective (funext fun y =>
      (tensorSectionsAt_mulBilinear L A n m y g g').symm)))

/-- **Tensoring with the degree `-1` generator is bijective on sections over `W`** for an
arbitrary second module. -/
theorem bijective_tensorSectionsAt_genNegOne (A : S.Modules) :
    Function.Bijective (fun y : A.val.obj (op W) =>
      tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) A (pow L (-1)) y
        (genNegOne L e)) :=
  (bijective_tensorSectionsAt_iff_mulBilinear L A (genNegOne L e) (genOne L e)
    (bijective_tensorSectionsAt_genOne L e)).mpr
    ((congrArg Function.Bijective (funext fun y =>
      (congrArg (tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) A
        (pow L (-1 + 1)) y) (mulBilinear_genNegOne_genOne L e)).trans
        (GradedAlgebraTwist.tensorSections_rightUnitorInvAt S.sheaf.obj
          S.ringCatSheaf.property (op W) A y).symm)).mpr
      (bijective_app_of_iso
        (Invertible.tensorProductRightUnitor S.sheaf.obj S.ringCatSheaf.property A).symm
        (op W)))

/-- **Tensoring with the generator of degree `-k-1` is bijective on sections over `W`** for
every module. -/
theorem bijective_tensorSectionsAt_genNeg (k : ℕ) (A : S.Modules) :
    Function.Bijective (fun y : A.val.obj (op W) =>
      tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) A (pow L (Int.negSucc k)) y
        (genNeg L e k)) := by
  induction k generalizing A with
  | zero => exact bijective_tensorSectionsAt_genNegOne L e A
  | succ k ih =>
      exact (bijective_tensorSectionsAt_iff_mulBilinear L A (genNeg L e k) (genNegOne L e)
        (bijective_tensorSectionsAt_genNegOne L e)).mp (ih A)

/-- **Tensoring with the generator of degree `n` is bijective on sections over the trivializing
open `W`, for every integer `n`** and every module. -/
theorem bijective_tensorSectionsAt_genInt (n : ℤ) (A : S.Modules) :
    Function.Bijective (fun y : A.val.obj (op W) =>
      tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) A (pow L n) y
        (genInt L e n)) := by
  cases n with
  | ofNat k => exact bijective_tensorSectionsAt_gen L e k A
  | negSucc k => exact bijective_tensorSectionsAt_genNeg L e k A

end Stacks.AlgebraicGeometry.TwistGenerator

end
