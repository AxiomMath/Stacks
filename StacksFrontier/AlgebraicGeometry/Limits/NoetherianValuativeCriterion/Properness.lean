module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Separatedness
public import StacksFrontier.AlgebraicGeometry.UniversallyClosedValuative.Basic

/-!
# The valuative criterion for properness using discrete valuation rings

For a morphism of finite type to a locally Noetherian scheme, properness is equivalent to the
existence of exactly one dotted arrow in every valuative square, and it suffices to test the
squares whose valuation ring is a discrete valuation ring.

## Main results

* `AlgebraicGeometry.isProper_tfae_of_isFiniteType`: the three forms of the valuative criterion
  for properness are equivalent.

## Implementation notes

The two halves of "exactly one dotted arrow" are handled separately: uniqueness on discrete
valuation rings gives separatedness by Tag 0207, that is
`AlgebraicGeometry.isSeparated_tfae_of_locallyOfFiniteType`, and existence on discrete valuation
rings gives universal closedness by Tag 05JY, that is
`AlgebraicGeometry.universallyClosed_tfae_valuative`; together with local finite type these are
exactly properness. Conversely a proper morphism is separated and universally closed, so
Mathlib's `AlgebraicGeometry.IsSeparated.valuativeCriterion` and
`AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion` give both halves for all valuation
rings.

The remaining condition of the source, which restricts the valuation rings further to the
discrete valuation subrings of the residue fields at the generic points of the irreducible
components of the source, is not stated here: unlike the corresponding condition for
separatedness it is not known to this library to imply the others, the source deducing that
implication from Chow's lemma.

## References

* [Stacks Project, Tag 0208](https://stacks.math.columbia.edu/tag/0208)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0208, conditions (1), (2) and (3).** For a morphism of finite type to a
locally Noetherian scheme, properness, the existence of exactly one dotted arrow in every
valuative square, and the existence of exactly one dotted arrow in every valuative square over a
discrete valuation ring are equivalent. -/
@[stacks 0208 "conditions (1), (2) and (3)",
  ega "II 7.3.3" "Noetherian, finite type",
  ega "II 7.3.8" "proper/DVR case", ega "I 3.7.3" "more general"]
theorem isProper_tfae_of_isFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] :
    List.TFAE
      [ IsProper f,
        ValuativeCriterion f,
        ∀ D : ValuativeCommSq f,
          IsDiscreteValuationRing D.R → Nonempty (Unique D.commSq.LiftStruct) ] := by
  tfae_have 1 → 2 := by
    intro hf
    let : IsProper f := hf
    have huc : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at huc
    exact ValuativeCriterion.iff.2 ⟨huc.1, fun D ↦ IsSeparated.valuativeCriterion f D⟩
  tfae_have 2 → 3 := fun hf D _ ↦ hf D
  tfae_have 3 → 1 := by
    intro h
    have hsn : ∀ D : ValuativeCommSq f, IsDiscreteValuationRing D.R →
        Subsingleton D.commSq.LiftStruct ∧ Nonempty D.commSq.LiftStruct :=
      fun D hD ↦ (unique_iff_subsingleton_and_nonempty _).mp (h D hD)
    have hsep : IsSeparated f :=
      ((isSeparated_tfae_of_locallyOfFiniteType f).out 3 1).mp
        fun D hD ↦ (hsn D hD).1
    have hclosed : UniversallyClosed f :=
      ((universallyClosed_tfae_valuative f).out 4 1).mp
        fun D hD ↦ (CommSq.HasLift.iff _).2 (hsn D hD).2
    exact IsProper.mk
  tfae_finish

end AlgebraicGeometry

end
