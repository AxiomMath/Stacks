module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical
public import StacksCore.Tactic.StacksAttribute

/-!
# Properties of morphisms that are fpqc local on the base

A property of morphisms of schemes is *fpqc local on the base* when it is stable under
arbitrary base change and descends along any faithfully flat quasi-compact covering family.
This file collects the properties for which both halves are already available: universal
injectivity and being a monomorphism.

## Main results

* `AlgebraicGeometry.UniversallyInjective.isStableUnderBaseChange` and
  `AlgebraicGeometry.universallyInjective_isZariskiLocalAtTarget` give fpqc locality of
  universal injectivity.
* `AlgebraicGeometry.isLocalAtTarget_monomorphisms_fpqc` states that monomorphisms are fpqc
  local on the target.

## Implementation notes

Mathlib's descent and base-change results are adopted directly for universal injectivity;
together they express locality on the base. For monomorphisms the
locality assertion is an instance of `CategoryTheory.MorphismProperty.IsLocalAtTarget` for the
fpqc precoverage of schemes, which packages both preservation under base change and descent
from any fpqc covering family.

## References

* [Stacks Project, Tag 02KW](https://stacks.math.columbia.edu/tag/02KW)
* [Stacks Project, Tag 02YK](https://stacks.math.columbia.edu/tag/02YK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

add_to_stacks 02KW AlgebraicGeometry.UniversallyInjective.isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "partial, sufficiency"
  AlgebraicGeometry.UniversallyInjective.isStableUnderBaseChange
add_to_sga "3 VIB 2.6" "more general" AlgebraicGeometry.UniversallyInjective.isStableUnderBaseChange
add_to_stacks 02KW AlgebraicGeometry.universallyInjective_isZariskiLocalAtTarget

/-- **Stacks Project, Tag 02YK.** Monomorphisms of schemes are fpqc local on the target. -/
@[stacks 02YK, ega "IV 2.7.1" "more general", sga "4 IV 8.5.5"]
instance isLocalAtTarget_monomorphisms_fpqc :
    (MorphismProperty.monomorphisms Scheme.{u}).IsLocalAtTarget Scheme.fpqcPrecoverage := by
  refine .mk_of_isStableUnderBaseChange fun f 𝒰 h => ⟨fun a b hab => ?_⟩
  apply eq_of_zeroHypercover_target
    (s := a ≫ f) (t := f) (𝒰 := 𝒰) (hf := rfl) (hg := hab.symm)
  intro i
  have : Mono (Limits.pullback.snd f (𝒰.f i)) := h i
  apply (cancel_mono (Limits.pullback.snd f (𝒰.f i))).1
  simp only [Limits.pullback.map, Limits.pullback.lift_snd]

end AlgebraicGeometry
