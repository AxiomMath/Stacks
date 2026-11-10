module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductInstance
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BigComparison

/-!
# Nonempty finite limits in the small crystalline site, unconditionally

Fix a global crystalline situation `(p, (S, I, γ), X)`.  The first assertion of
[Stacks, Tag 07IJ] is that the inclusion functor `Cris(X/S) ⥤ CRIS(X/S)` commutes with finite
nonempty limits; the source reads it off [Stacks, Tag 07IG], whose input is that `CRIS(X/S)` has
all finite nonempty limits, the first clause of [Stacks, Tag 07I9].

`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BigComparison.lean` proves the comparison
for a shape `J` of which `CRIS(X/S)` has limits — the inclusion creates them, so `Cris(X/S)` has
them too and the inclusion preserves them — and carries the existence in `CRIS(X/S)` as the instance
argument `HasLimitsOfShape J (Thickening S)`.  That existence is a theorem of this tree,
`Crystalline.GlobalCrystallineSituation.hasNonemptyFiniteLimits_thickening` of
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductInstance.lean`, which is the
first clause of [Stacks, Tag 07I9] in full: `CRIS(X/S)` has every finite nonempty limit, the binary
products being glued from the affine product patches of a pair and the fibre products being built
from the fibre products of divided power schemes.  `BigComparison.lean` cannot use it, because the
affine layer the glued product rests on imports the small site; this module, downstream of both,
feeds it in and states the assertion of the source as the source states it, for every nonempty
finite shape and with no instance argument left over.

## Main results

* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.ιCreatesLimitOfNonempty` — the
  inclusion `Cris(X/S) ⥤ CRIS(X/S)` creates the limit of every nonempty finite diagram,
  [Stacks, Tag 07IJ].
* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.hasNonemptyFiniteLimits`
  — `Cris(X/S)` has all finite nonempty limits, [Stacks, Tag 07IJ].
* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.ι_preservesNonemptyFiniteLimits`
  — the inclusion `Cris(X/S) ⥤ CRIS(X/S)` commutes with all finite nonempty limits,
  [Stacks, Tag 07IJ].

## What is and is not proved

The first assertion of [Stacks, Tag 07IJ] is proved here in full, under the hypotheses of
[Stacks, Tag 07HQ] alone — a global crystalline situation — and with no hypothesis about the
existence of limits anywhere.  Finite *empty* limits are outside the assertion and remain outside
it: a final object of `CRIS(X/S)`, or of `Cris(X/S)`, does not exist in general, which is why the
source says *nonempty*.

The shape-by-shape tool `ιCreatesLimit` of `BigComparison.lean`, which the first of these three
uses, is kept there, now untagged; the other two come from instance search, through the closure
instance
`Crystalline.GlobalCrystallineSituation.Thickening.isClosedUnderFiniteLimits_isCrystalline`, once
the limits of `CRIS(X/S)` are supplied.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 07HQ](https://stacks.math.columbia.edu/tag/07HQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

namespace CrystallineThickening

/-- **Stacks Project, Tag 07IJ, first assertion.**  The inclusion `Cris(X/S) ⥤ CRIS(X/S)` creates
the limit of every nonempty finite diagram of divided power thickenings of `X` whose maps to `X`
are open immersions: the limit of the diagram in `CRIS(X/S)` exists by clause (1) of
[Stacks, Tag 07I9] and its vertex again has open immersion to `X`, the forgetful functor to
`Sch/X` commuting with limits and a finite nonempty limit of opens of `X` being an open of `X`. -/
@[instance_reducible, stacks 07IJ "the inclusion commutes with finite nonempty limits"]
noncomputable def ιCreatesLimitOfNonempty (S : GlobalCrystallineSituation.{u})
    (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J]
    (F : J ⥤ CrystallineThickening S) :
    CreatesLimit F (ι S) :=
  have := (hasNonemptyFiniteLimits_thickening S).out J
  ιCreatesLimit S J F

/-- **Stacks Project, Tag 07IJ, first assertion.**  The small crystalline category `Cris(X/S)` has
all finite nonempty limits.  They are created by the inclusion from the finite nonempty limits of
`CRIS(X/S)`, which exist by clause (1) of [Stacks, Tag 07I9]. -/
@[stacks 07IJ "nonempty finite limits in Cris(X/S)"]
theorem hasNonemptyFiniteLimits (S : GlobalCrystallineSituation.{u}) :
    _root_.HasNonemptyFiniteLimits (CrystallineThickening S) := by
  refine ⟨fun J _ _ _ ↦ ?_⟩
  have := (hasNonemptyFiniteLimits_thickening S).out J
  infer_instance

/-- **Stacks Project, Tag 07IJ, first assertion.**  The inclusion `Cris(X/S) ⥤ CRIS(X/S)` commutes
with finite nonempty limits.  Every nonempty finite shape is one of which `CRIS(X/S)` has limits,
by clause (1) of [Stacks, Tag 07I9], and the inclusion creates those. -/
@[stacks 07IJ "the inclusion commutes with finite nonempty limits"]
theorem ι_preservesNonemptyFiniteLimits (S : GlobalCrystallineSituation.{u})
    (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesLimitsOfShape J (ι S) :=
  have := (hasNonemptyFiniteLimits_thickening S).out J
  inferInstance

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation

end
