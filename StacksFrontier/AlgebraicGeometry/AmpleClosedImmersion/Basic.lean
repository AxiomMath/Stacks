module

public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Ampleness pulls back along a closed immersion

For a surjective closed immersion `i : Z ⟶ X` of Noetherian schemes and an invertible
`𝒪_X`-module `L`, ampleness of `L` implies ampleness of `i^* L`. This is one implication of
Stacks Tag 09MS, and it needs neither surjectivity of `i` nor any Noetherian hypothesis: all it
uses is that a closed immersion is an affine morphism.

## Main results

* `Stacks.AmpleClosedImmersion.isAmple_modulePullback_of_surjective_isClosedImmersion`: for a
  surjective closed immersion of Noetherian schemes, the pullback of an ample invertible module
  is ample.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.AmpleClosedImmersion

/-- For a surjective closed immersion `i : Z ⟶ X` of Noetherian schemes, ampleness of an
invertible `𝒪_X`-module `L` implies ampleness of `i^* L` (one implication of Stacks Tag 09MS).
Neither surjectivity of `i` nor Noetherianness of `X` is used, and of `i` being a closed
immersion only its being an affine morphism is used. -/
theorem isAmple_modulePullback_of_surjective_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [Surjective i] [IsNoetherian X] (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) :
    IsAmple Z (Stacks.AmpleLocallyClosed.pullbackModule i L) := by
  refine (isAmple_iff_forall_affine_nonvanishingOpen Z
    (Stacks.AmpleLocallyClosed.pullbackModule i L)).mpr
    ⟨Stacks.AmpleLocallyClosed.compactSpace_of_quasiCompact i inferInstance hL.compactSpace,
      fun z => ?_⟩
  obtain ⟨n, hn, s, haff, hxs⟩ :=
    Stacks.AmpleTheory.IsAmple.exists_affine_nonvanishingOpen X L hL (i.base z)
  refine ⟨n, hn, Stacks.NonvanishingPullback.pullbackPowSection i L n s, ?_, ?_⟩ <;>
    rw [show powNonvanishingOpen Z (Stacks.AmpleLocallyClosed.pullbackModule i L) n
          (Stacks.NonvanishingPullback.pullbackPowSection i L n s) =
        i ⁻¹ᵁ powNonvanishingOpen X L n s from
      Opens.ext (Stacks.NonvanishingPullback.sectionPullbackCompatible i L n s)]
  · exact haff.preimage i
  · exact hxs

end Stacks.AmpleClosedImmersion

end
