module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.TwoImmersionsConormalSequence
import StacksCore.Tactic.StacksAttribute

/-!
# Surjectivity of the second arrow of the conormal sequence of two immersions

Let `i : Z ⟶ X` be an immersion of schemes over `p : X ⟶ S`. [Stacks, Tag 01UZ] attaches to it
the sequence

`𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0`

of `𝒪_Z`-modules, which is `Stacks.ConormalSequenceRight.conormalShortComplex`. It is exact at
`i^*Ω_{X/S}` for every immersion, with no hypothesis on `i ≫ p`, by
`Stacks.ConormalSequenceRight.conormalShortComplex_exact`. This file draws from that the
consequence for the sequence of [Stacks, Tag 067L].

## Main results

* `Stacks.ConormalSequenceRight.epi_conormalDifferential_of_isZero`: the conormal differential
  `𝒞_{Z/X} ⟶ i^*Ω_{X/S}` is an epimorphism once `Ω_{Z/S}` is a zero object.
* `Stacks.ConormalSequenceTwoImmersions.epi_conormalDifferential`: for a commutative triangle
  `i ≫ p = j` of immersions, the second arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` of the sequence of
  [Stacks, Tag 067L] is an epimorphism.

## The second arrow of Tag 067L

For a triangle `i ≫ p = j` of immersions the sequence of [Stacks, Tag 067L] is
`𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0`, whose second arrow is the conormal differential of
[Stacks, Tag 01UZ] for `i` over `p`. Exactness at the middle term of the sequence of
[Stacks, Tag 01UZ] identifies the image of that arrow with the kernel of
`i^*Ω_{X/Y} ⟶ Ω_{Z/Y}`; the target vanishes because `j` is an immersion, hence formally
unramified, by [Stacks, Tag 02G4]. So the kernel is everything and the arrow is an epimorphism,
which is the `⟶ 0` at the right-hand end.

## References

* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RelativeDifferentialStalkMap
open scoped TensorProduct

universe u

namespace Stacks.ConormalSequenceRight

/-- **The conormal differential is an epimorphism once the right-hand term of the sequence
vanishes.** The conormal sequence of `i` over `p` is exact at `i^*Ω_{X/S}`, and when `Ω_{Z/S}`
is a zero object the map out of that term is zero, so its kernel is everything. -/
theorem epi_conormalDifferential_of_isZero {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (p : X ⟶ S) (hz : IsZero (Scheme.Hom.relativeDifferentials (i ≫ p))) :
    Epi (conormalDifferential i p) :=
  (ShortComplex.exact_iff_epi _ (hz.eq_zero_of_tgt _)).mp (conormalShortComplex_exact i p)

end Stacks.ConormalSequenceRight

namespace Stacks.ConormalSequenceTwoImmersions

/-- **[Stacks, Tag 067L], surjectivity of the second arrow.** For immersions `i : Z ⟶ X` and
`j : Z ⟶ Y` in a commutative triangle `i ≫ p = j`, the second arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` of
the conormal sequence is an epimorphism, which is the `⟶ 0` at its right-hand end.

The sequence of [Stacks, Tag 01UZ] for `i` over `p` is exact at `i^*Ω_{X/Y}` and continues by
`i^*Ω_{X/Y} ⟶ Ω_{Z/Y}`, whose target vanishes because `j` is an immersion, hence formally
unramified. -/
@[stacks 067L "surjectivity of the second arrow 𝒞_{Z/X} ⟶ i^*Ω_{X/Y}, which is the ⟶ 0 at the
right-hand end of the sequence"]
theorem epi_conormalDifferential {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)
    [IsImmersion i] [IsImmersion j] (h : i ≫ p = j) :
    Epi (Stacks.ConormalSequenceRight.conormalDifferential i p) := by
  refine Stacks.ConormalSequenceRight.epi_conormalDifferential_of_isZero i p ?_
  rw [h]
  exact Scheme.Hom.isZero_relativeDifferentials_of_formallyUnramified j

end Stacks.ConormalSequenceTwoImmersions

end
