module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.UniversallyClosedValuative

/-!
# The valuative criterion of separatedness

Let `B` be a big fppf site containing a scheme `S` and let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`. Three conditions on `f` then agree: that
`f` be separated and universally closed; that `f` satisfy the valuative criterion of Stacks
03IX, both its existence part and its uniqueness part; and that every valuative square for `f`
have exactly one dotted arrow over the given valuation ring, with no extension of the fraction
field and no domination, which is the valuative criterion of Schemes, Stacks 01KD. A unique
dotted arrow is expressed as `Nonempty q.Lift ∧ Subsingleton q.Lift`, and the valuation rings
range over those whose spectra belong to the chosen big site.

## Main results

* `AlgebraicGeometry.Space`
  `.isSeparated_and_universallyClosed_tfae_of_isQuasiCompact_of_isQuasiSeparated`: the
  equivalence of those three conditions.

## References

* [Stacks Project, Tag 0A3Z](https://stacks.math.columbia.edu/tag/0A3Z)
* [Stacks Project, Tag 03KU](https://stacks.math.columbia.edu/tag/03KU)
* [Stacks Project, Tag 03KV](https://stacks.math.columbia.edu/tag/03KV)
* [Stacks Project, Tag 0A3Y](https://stacks.math.columbia.edu/tag/0A3Y)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- For a quasi-compact and quasi-separated morphism `f : X ⟶ Y` of algebraic spaces over `S`,
being separated and universally closed, satisfying the valuative criterion of Stacks 03IX, and
having exactly one dotted arrow in every valuative square over the given valuation ring are
equivalent. -/
@[stacks 0A3Z]
public theorem isSeparated_and_universallyClosed_tfae_of_isQuasiCompact_of_isQuasiSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    List.TFAE
      [IsSeparated B S hS f ∧ UniversallyClosed B S hS f,
        ValuativeCriterion f,
        ∀ q : ValuativeSquare f, Nonempty q.Lift ∧ Subsingleton q.Lift] := by
  have key := universallyClosed_tfae_of_isQuasiCompact_of_isSeparated hX hY f hqc
  have sep := isSeparated_of_isQuasiSeparated_of_valuativeCriterion_uniqueness hX hY f hqs
  tfae_have 1 → 2 := fun h =>
    ⟨((key h.1).out 1 2).mp h.2, valuativeCriterion_uniqueness_of_isSeparated f h.1⟩
  tfae_have 2 → 1 := fun h => ⟨sep h.2, ((key (sep h.2)).out 1 2).mpr h.1⟩
  tfae_have 2 → 3 := fun h =>
    have hl : ∀ q : ValuativeSquare f, Nonempty q.Lift := ((key (sep h.2)).out 2 3).mp h.1
    fun q => ⟨hl q, h.2 q⟩
  tfae_have 3 → 2 := fun h =>
    have hu : ValuativeCriterion.Uniqueness f := fun q => (h q).2
    ⟨((key (sep hu)).out 2 3).mpr fun q => (h q).1, hu⟩
  tfae_finish

end AlgebraicGeometry.Space

end
