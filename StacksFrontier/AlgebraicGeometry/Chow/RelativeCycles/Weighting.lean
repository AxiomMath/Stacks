module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The weighting attached to a family of zero-cycles on the fibres

Let `f : X ⟶ S` be locally of finite type and let `α` be a family of `0`-cycles on the fibres
of `X/S`. Multiplying the coefficient of `α` at a point `x` of `X` by the inseparable degree of
`κ(x)` over `κ(f x)` produces an integer-valued function `w_α` on `X`. For a locally
quasi-finite morphism and a relative `0`-cycle this function is a weighting, and the
separable-degree weighted fibre sum of `w_α` is the sum of the coefficients of `α` weighted by
the full residue-field degrees, since inseparable degree times separable degree is the degree.

## Main definitions

* `Stacks.Chow.relativeCycleWeight` — the function `w_α` attached to a family of `0`-cycles.
* `Stacks.Chow.relativeCycleWeightHom` — the same construction as a homomorphism of abelian
  groups.

## Main results

* `Stacks.Chow.relativeCycleWeight_apply` — the defining formula for `w_α`.
* `Stacks.Chow.relativeCycleWeight_eq_zero_of_notMem_supportOfFamily` — `w_α` vanishes off the
  support of `α`.
* `Stacks.Chow.separableDegreeWeightedFiberSum_relativeCycleWeight` — the separable-degree
  weighted fibre sum of `w_α` is the fibre sum of the coefficients of `α` weighted by the
  residue-field degrees.

## Implementation notes

The source attaches `w_α` to a relative `0`-cycle, but neither the construction nor the
computation of its weighted fibre sum uses the valuative condition, so both are given here for
an arbitrary family of `0`-cycles; a relative `0`-cycle is fed in through the coercion from
`Stacks.Chow.relativeCycles`. The coefficient at `x` is the coefficient of the fibre cycle
`α (f x)` at the canonical point `f.asFiber x` of the scheme-theoretic fibre through `x`, and
the residue-field extension is the one induced by `f.residueFieldMap`.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The function `w_α : X → ℤ` attached to a family `α` of `0`-cycles on the fibres of
`f : X ⟶ S`: the coefficient of `α` at a point `x`, taken on the scheme-theoretic fibre through
`x`, times the inseparable degree `[κ(x) : κ(f x)]_i`. -/
@[stacks 0H5P "the construction of w_α preceding the lemma; none of the lemma's three claims"]
def relativeCycleWeight {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (α : FamilyOfCycles f 0) : X → ℤ :=
  fun x ↦
    letI := (f.residueFieldMap x).hom.toAlgebra
    (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) *
      (Field.finInsepDegree (S.residueField (f x)) (X.residueField x) : ℤ)

/-- The defining formula for `w_α`. -/
theorem relativeCycleWeight_apply {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (α : FamilyOfCycles f 0) (x : X) :
    relativeCycleWeight f α x =
      letI := (f.residueFieldMap x).hom.toAlgebra
      (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) *
        (Field.finInsepDegree (S.residueField (f x)) (X.residueField x) : ℤ) :=
  rfl

/-- The function `w_α` attached to the zero family is zero. -/
@[simp]
theorem relativeCycleWeight_zero {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    relativeCycleWeight f 0 = 0 := by
  funext x
  simp [relativeCycleWeight]

/-- The function `w_α` is additive in `α`. -/
@[simp]
theorem relativeCycleWeight_add {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (α β : FamilyOfCycles f 0) :
    relativeCycleWeight f (α + β) = relativeCycleWeight f α + relativeCycleWeight f β := by
  funext x
  simp [relativeCycleWeight, add_mul]

/-- The function attached to `-α` is `-w_α`. -/
@[simp]
theorem relativeCycleWeight_neg {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (α : FamilyOfCycles f 0) :
    relativeCycleWeight f (-α) = -relativeCycleWeight f α := by
  funext x
  simp [relativeCycleWeight, neg_mul]

/-- The construction `α ↦ w_α` as a homomorphism from the group of families of `0`-cycles on
the fibres of `f` to the group of integer-valued functions on the source. -/
def relativeCycleWeightHom {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    FamilyOfCycles f 0 →+ (X → ℤ) where
  toFun := relativeCycleWeight f
  map_zero' := relativeCycleWeight_zero f
  map_add' := relativeCycleWeight_add f

/-- The homomorphism `relativeCycleWeightHom f` sends `α` to `w_α`. -/
@[simp]
theorem relativeCycleWeightHom_apply {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (α : FamilyOfCycles f 0) : relativeCycleWeightHom f α = relativeCycleWeight f α :=
  rfl

/-- The inseparable degree of the residue field extension at `x` divides `w_α x`. -/
theorem finInsepDegree_dvd_relativeCycleWeight {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (α : FamilyOfCycles f 0) (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    ((Field.finInsepDegree (S.residueField (f x)) (X.residueField x) : ℤ)) ∣
      relativeCycleWeight f α x :=
  Dvd.intro_left _ rfl

/-- The function `w_α` vanishes at every point outside the support of `α`. -/
theorem relativeCycleWeight_eq_zero_of_notMem_supportOfFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (α : FamilyOfCycles f 0) {x : X} (hx : x ∉ supportOfFamily f α) :
    relativeCycleWeight f α x = 0 := by
  have hcoeff : (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) = 0 := by
    by_contra hne
    exact hx ((mem_supportOfFamily f α x).2
      ⟨f x, f.asFiber x, subset_tsupport _ hne, f.fiberι_asFiber x⟩)
  rw [relativeCycleWeight_apply, hcoeff, zero_mul]

/-- The support of `w_α` is contained in the support of `α`. -/
theorem support_relativeCycleWeight_subset {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (α : FamilyOfCycles f 0) :
    Function.support (relativeCycleWeight f α) ⊆ supportOfFamily f α := fun _ hx ↦
  not_imp_comm.1 (relativeCycleWeight_eq_zero_of_notMem_supportOfFamily f α) hx

/-- Weighting `w_α` at a point by the separable degree of the residue field extension there
recovers the coefficient of `α` weighted by the full degree, because inseparable degree times
separable degree is the degree. -/
theorem relativeCycleWeight_mul_finSepDegree {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (α : FamilyOfCycles f 0) (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    relativeCycleWeight f α x *
        (Field.finSepDegree (S.residueField (f x)) (X.residueField x) : ℤ) =
      (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) *
        (Module.finrank (S.residueField (f x)) (X.residueField x) : ℤ) := by
  simp only [relativeCycleWeight]
  rw [mul_assoc, ← Nat.cast_mul, Nat.mul_comm, Field.finSepDegree_mul_finInsepDegree]

open scoped Classical in
/-- The separable-degree weighted fibre sum of `w_α` is the fibre sum of the coefficients of
`α` weighted by the full residue-field degrees. -/
theorem separableDegreeWeightedFiberSum_relativeCycleWeight {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (α : FamilyOfCycles f 0) (s : S) :
    separableDegreeWeightedFiberSum f (relativeCycleWeight f α) s =
      ∑ᶠ x : X, if f x = s then
        letI := (f.residueFieldMap x).hom.toAlgebra
        (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) *
          (Module.finrank (S.residueField (f x)) (X.residueField x) : ℤ)
      else 0 := by
  refine finsum_congr fun x ↦ ?_
  by_cases hx : f x = s <;> simp only [hx, ite_true, ite_false]
  exact relativeCycleWeight_mul_finSepDegree f α x

end Stacks.Chow

end
