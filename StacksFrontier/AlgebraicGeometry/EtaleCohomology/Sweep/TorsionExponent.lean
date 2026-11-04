module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Torsion abelian sheaves with a prescribed exponent

`Stacks.Torsion.torsionSheafProperty` says that every local section of an abelian sheaf is
locally annihilated by some positive integer. The vanishing and finiteness theorems for étale
cohomology need two refinements of it, in which the annihilator is constrained relative to a
fixed natural number `l`: either it is a positive power of `l`, or it is coprime to `l`. Over
a base field one takes `l` to be the exponential characteristic, so the coprime condition is
vacuous in characteristic zero, where `ringExpChar` is `1`.

Both conditions are local in the same sense as torsion itself: the annihilator may depend on
the member of a covering sieve, not only on the section.

## Main definitions

* `Stacks.Torsion.IsPrimePowerTorsion` — every local section is locally annihilated by a
  positive power of `l`.
* `Stacks.Torsion.IsPrimeToCharacteristicTorsion` — every local section is locally
  annihilated by a positive integer coprime to `l`.

## Main results

* `Stacks.Torsion.torsionSheafProperty_of_isPrimePowerTorsion` and
  `Stacks.Torsion.torsionSheafProperty_of_isPrimeToCharacteristicTorsion` — both refinements
  imply torsion.

## References

* [Stacks Project, Tag 0DV7](https://stacks.math.columbia.edu/tag/0DV7)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- An abelian sheaf is `l`-power torsion if every local section is, locally on a covering
sieve, annihilated by a positive power of `l`. -/
@[sga "4 IX 1.1" "p = {l}"]
def IsPrimePowerTorsion (l : ℕ) (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (x : F.obj.obj (Opposite.op U)),
    ∃ R : Sieve U, R ∈ J U ∧
      (∀ (V : C) (f : V ⟶ U), R f →
        (∃ r : ℕ, 0 < r ∧ l ^ r • (F.obj.map f.op x) = 0))

/-- An abelian sheaf is torsion prime to `p` if every local section is, locally on a covering
sieve, annihilated by a positive integer coprime to `p`. Taking `p` to be the exponential
characteristic of a base field makes this vacuous in characteristic zero. -/
@[sga "4 IX 1.1"]
def IsPrimeToCharacteristicTorsion (p : ℕ) (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (x : F.obj.obj (Opposite.op U)),
    ∃ R : Sieve U, R ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), R f →
        ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ n • (F.obj.map f.op x) = 0

/-- A sheaf of `l`-power torsion is torsion, provided `l` is positive: a positive power of a
positive integer is a positive integer. -/
theorem torsionSheafProperty_of_isPrimePowerTorsion {l : ℕ} (hl : 0 < l)
    {F : Sheaf J AddCommGrpCat.{w}} (hF : IsPrimePowerTorsion J l F) :
    torsionSheafProperty J F := by
  intro U x
  obtain ⟨R, hR, hann⟩ := hF U x
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨r, hr, hzero⟩ := hann V f hf
  exact ⟨l ^ r, pow_pos hl r, hzero⟩

/-- A sheaf of torsion prime to `p` is torsion. -/
theorem torsionSheafProperty_of_isPrimeToCharacteristicTorsion {p : ℕ}
    {F : Sheaf J AddCommGrpCat.{w}} (hF : IsPrimeToCharacteristicTorsion J p F) :
    torsionSheafProperty J F := by
  intro U x
  obtain ⟨R, hR, hann⟩ := hF U x
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, hn, -, hzero⟩ := hann V f hf
  exact ⟨n, hn, hzero⟩

end Stacks.Torsion

end
