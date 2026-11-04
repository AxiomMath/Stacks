module

public import Mathlib.Algebra.CharP.Frobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ProperFinitenessStatement
import StacksCore.Tactic.StacksAttribute

/-!
# Statement (4) of Situation 0A52: prime-to-characteristic finiteness

Situation 0A52 fixes an algebraically closed field `k`, a separated finite-type scheme `X` of
dimension at most one over `k`, and a torsion abelian sheaf `F` on the small étale site of `X`.
Statement (4) of that situation reads:

> `H^q_étale(X, F)` is finite if `F` is constructible and torsion prime to `char(k)`.

## Main definitions

* `Stacks.EtaleCohomology.TorsionSheafSituation.FiniteCohomologyOfPrimeToCharacteristic` is
  statement (4): in Situation 0A52, if `F` is constructible and its torsion is prime to the
  characteristic of `k`, then `H^q_étale(X, F)` is finite in every degree.

## Main results

* `Stacks.Torsion.isPrimeToCharacteristicTorsion_one_iff`: at exponent `1` the
  prime-to-the-characteristic torsion condition is exactly torsion.

The remaining results are in the namespace `Stacks.EtaleCohomology.TorsionSheafSituation`.

* `isPrimeToCharacteristicTorsion_of_ringExpChar_eq_one`: in characteristic zero the sheaf of the
  situation is torsion prime to the characteristic.
* `finiteCohomologyOfPrimeToCharacteristic_iff_of_ringExpChar_eq_one`: in characteristic zero
  statement (4) is finiteness of the cohomology of a constructible sheaf, with no torsion side
  condition.
* `finiteCohomologyOfPrimeToCharacteristic_of_subsingleton_of_le_two`: if the cohomology is a
  subsingleton above degree two, statement (4) follows from finiteness in degrees `0`, `1` and
  `2`.

## References

* [Stacks Project, Tag 0A56](https://stacks.math.columbia.edu/tag/0A56)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.Torsion

/-- At exponent `1` the prime-to-the-characteristic torsion condition is exactly torsion. -/
theorem isPrimeToCharacteristicTorsion_one_iff {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (F : Sheaf J AddCommGrpCat.{w}) :
    IsPrimeToCharacteristicTorsion J 1 F ↔ torsionSheafProperty J F := by
  refine ⟨fun hF U x ↦ ?_, fun hF U x ↦ ?_⟩ <;> obtain ⟨R, hR, hann⟩ := hF U x
  · exact ⟨R, hR, fun V f hf ↦ (hann V f hf).imp fun _ ⟨hn, _, hz⟩ ↦ ⟨hn, hz⟩⟩
  · exact ⟨R, hR, fun V f hf ↦
      (hann V f hf).imp fun n ⟨hn, hz⟩ ↦ ⟨hn, Nat.coprime_one_right n, hz⟩⟩

end Stacks.Torsion

namespace Stacks.EtaleCohomology

namespace TorsionSheafSituation

/-- In characteristic zero the torsion hypothesis of statement (4) of Situation 0A52 is
automatic: the sheaf of the situation is torsion prime to the characteristic. -/
theorem isPrimeToCharacteristicTorsion_of_ringExpChar_eq_one (S : TorsionSheafSituation.{u, v})
    (h : ringExpChar S.k = 1) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion S.X.smallEtaleTopology
      (ringExpChar S.k) S.F := by
  rw [h, Stacks.Torsion.isPrimeToCharacteristicTorsion_one_iff]
  exact S.isTorsion

variable (S : TorsionSheafSituation.{u, v}) (B : BigEtaleSite.{u}) (hX : B.Contains S.X)
  [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- Statement (4) of Situation 0A52. For an algebraically closed
field `k`, a separated finite-type scheme `X` of dimension at most one over `k` and a torsion
abelian sheaf `F` on the small étale site of `X`: if `F` is constructible and its torsion is prime
to the characteristic of `k`, then `H^q_étale(X, F)` is finite for every `q`.

"Torsion prime to the characteristic" is taken at the exponential characteristic. -/
@[stacks 0A56 "statement (4) of Situation 0A52, as a predicate on the situation"]
def FiniteCohomologyOfPrimeToCharacteristic : Prop :=
  IsConstructibleEtaleAbelianSheaf.{u, v} B S.X hX S.F →
    Stacks.Torsion.IsPrimeToCharacteristicTorsion S.X.smallEtaleTopology
        (ringExpChar S.k) S.F →
      ∀ q : ℕ, Finite (Sheaf.H.{w} S.F q)

/-- In characteristic zero statement (4) asks exactly that a constructible sheaf of the situation
have finite étale cohomology in every degree. -/
theorem finiteCohomologyOfPrimeToCharacteristic_iff_of_ringExpChar_eq_one
    (h : ringExpChar S.k = 1) :
    FiniteCohomologyOfPrimeToCharacteristic.{u, v, w} S B hX ↔
      (IsConstructibleEtaleAbelianSheaf.{u, v} B S.X hX S.F →
        ∀ q : ℕ, Finite (Sheaf.H.{w} S.F q)) :=
  ⟨fun hf hc ↦ hf hc (S.isPrimeToCharacteristicTorsion_of_ringExpChar_eq_one h),
    fun hf hc _ ↦ hf hc⟩

/-- If the étale cohomology of `F` is a subsingleton above degree two and finite in degrees at most
two, then statement (4) holds. -/
theorem finiteCohomologyOfPrimeToCharacteristic_of_subsingleton_of_le_two
    (hvan : ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H.{w} S.F q))
    (hfin : ∀ q : ℕ, q ≤ 2 → Finite (Sheaf.H.{w} S.F q)) :
    FiniteCohomologyOfPrimeToCharacteristic.{u, v, w} S B hX := fun _ _ q ↦
  if hq : q ≤ 2 then hfin q hq else @Finite.of_subsingleton _ (hvan q (by lia))

end TorsionSheafSituation

end Stacks.EtaleCohomology

end
