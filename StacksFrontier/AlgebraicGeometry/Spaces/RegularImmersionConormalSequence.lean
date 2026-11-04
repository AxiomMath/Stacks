module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.SplitExactConormalSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionSplitConormal

/-!
# The conormal sequence of an `H₁`-regular immersion of algebraic spaces

Let `Z --i--→ Y --j--→ X` be immersions of algebraic spaces over a scheme `S` with `i` an
`H₁`-regular immersion in the sense of [Stacks Project, Tag 06BN] part (2).  Then the canonical
conormal sequence `0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` of [Stacks Project, Tag 06BD] is
exact and étale-locally split.  That is [Stacks Project, Tag 09RZ], the analogue for algebraic
spaces of [Stacks Project, Tag 063N].

## Main results

* `AlgebraicGeometry.Space.isSplitExactConormalSequenceOnEtaleCharts_of_isH1RegularImmersion`:
  **[Stacks Project, Tag 09RZ]**, both of its conclusions, in the shape
  `AlgebraicGeometry.Space.IsSplitExactConormalSequenceOnEtaleCharts`.

## Implementation notes

**Why the conclusion is read on the étale charts of `X`.**  The conormal sequence of a pair of
immersions of algebraic spaces has no left-hand map in this development:
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean`, which carries the
surjectivity clause of [Stacks Project, Tag 06BD], records in its own notes that the sequence
`𝒞_{Y/X} ⊗ 𝒪_Z ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` has no first map there — so on `Z` itself there is no
object whose exactness and local splitness could be asserted.  The development's standing device
for a condition on algebraic spaces is to read the corresponding condition of schemes on the
étale scheme charts of the target; that is how each of the three regularity predicates of
[Stacks Project, Tag 06BN] is defined, and
`AlgebraicGeometry.Space.IsSplitExactConormalSequenceOnEtaleCharts` applies the device to the
conormal condition.  It is the hypothesis that the three clauses of [Stacks Project, Tag 09S1] in
`StacksFrontier/AlgebraicGeometry/Spaces/RegularImmersionSplitConormal.lean` consume, and this file
is what discharges it.

**The sense in which the splitting is étale-local.**  Over each étale chart `c` of `X` the
splitting produced is Zariski-local on the chart: it exists on a neighbourhood of every point of
the base change of `Z`.  Since the charts range over an étale cover of `X`, the splitting is
local for the étale topology on `Z` and is not claimed to be global, nor to be Zariski-local on
`Z`.

**Where `H₁`-regularity enters.**  `AlgebraicGeometry.Space.IsH1RegularImmersion` is
`H₁`-regularity of the base change of `i` to every étale scheme chart of `Y`.  The chart of `Y`
used is the one `j` pulls back from the chart `c` of `X`, which is étale because étaleness of a
morphism of presheaves is stable under base change; the scheme-level `H₁`-regularity so obtained
is handed to
`Stacks.AlgebraicGeometry.isSplitExactConormalSequence_of_isH1RegularImmersion`, where it is what
buys injectivity of the left-hand map and finite local freeness of `𝒞_{Z/Y}`, hence exactness on
the left and the local splitting.  For an arbitrary pair of immersions the sequence is still a
complex, exact in the middle and on the right, but neither of those two conclusions holds.

## What is not proved

* **No statement is made about a conormal sequence on `Z` itself.**  Tag 09RZ is phrased for the
  sequence of [Stacks Project, Tag 06BD] as a sequence of `𝒪_Z`-modules; that sequence does not
  exist as an object in this development, for the reason recorded above, so the conclusion is
  carried only in the chartwise form.
* Algebraicity of `Z`, `Y` and `X` is not needed and is not assumed, as in
  [Stacks Project, Tag 06BP] and [Stacks Project, Tag 09S0] of this development.

## References

* [Stacks Project, Lemma 76.44.5 (Tag 09RZ)](https://stacks.math.columbia.edu/tag/09RZ)
* [Stacks Project, Lemma 31.22.6 (Tag 063N)](https://stacks.math.columbia.edu/tag/063N)
* [Stacks Project, Lemma 76.17.11 (Tag 06BD)](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Definition 76.44.2 (Tag 06BN)](https://stacks.math.columbia.edu/tag/06BN)
* [Stacks Project, Lemma 76.44.6 (Tag 09S1)](https://stacks.math.columbia.edu/tag/09S1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **[Stacks Project, Tag 09RZ].**  Let `i : Z ⟶ Y` and `j : Y ⟶ X` be morphisms of algebraic
spaces over `S` with `j` an immersion and `i` an `H₁`-regular immersion.  Then the conormal
sequence `0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` of [Stacks Project, Tag 06BD] is exact and
locally split, read on the étale scheme charts of `X`:  over every such chart the base changes of
`j` and of `i` are immersions of schemes whose conormal sequence is short exact and splits on a
neighbourhood of every point.

Over a chart `c` of `X` the pair of scheme immersions is the base change of `j` to `c` together
with the base change of `i` to the chart of `Y` that `j` pulls back from `c`.  That chart of `Y`
is étale, because étaleness of a morphism of presheaves is stable under base change, so
`H₁`-regularity of `i` gives it for the base change of `i`; the case of schemes,
[Stacks Project, Tag 063N] in the bundled form
`Stacks.AlgebraicGeometry.isSplitExactConormalSequence_of_isH1RegularImmersion`, then applies.

This is the hypothesis of the three clauses of [Stacks Project, Tag 09S1]; see
`AlgebraicGeometry.Space.isH1RegularImmersion_of_comp_of_isSplitExactConormalSequence` and its
siblings. -/
@[stacks 09RZ "both conclusions — exactness and local splitness — of the conormal sequence of \
Tag 06BD for an H₁-regular immersion, read on the étale scheme charts of X as \
`IsSplitExactConormalSequenceOnEtaleCharts`, which is how this development states every \
condition on algebraic spaces whose scheme analogue it localizes.  The sequence has no \
left-hand map as a sequence of modules on Z in this development, so nothing is asserted about \
it on Z itself; the splitting is étale-local, Zariski-local on each chart of an étale cover, \
and is neither global nor claimed on a single chart", sga "6 VIII 2.2" "partial"]
theorem isSplitExactConormalSequenceOnEtaleCharts_of_isH1RegularImmersion (i : Z ⟶ Y) (j : Y ⟶ X)
    (hj : IsImmersion B S hS j) (hi : IsH1RegularImmersion B S hS i) :
    IsSplitExactConormalSequenceOnEtaleCharts B S hS i j := by
  obtain ⟨hri, hcharts⟩ := hi
  refine ⟨hri, hj.1, fun W c hc => ?_⟩
  have hcY : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hj.1.fst c) := by
    have := MorphismProperty.relative_isStableUnderBaseChange
      (F := yoneda (C := BigFppfOver B S hS))
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (hj.1.isPullback c).flip hc
  obtain ⟨hic, hreg⟩ := hcharts _ (hj.1.fst c) hcY
  have hjc : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (hj.1.snd c)) :=
    hj.2 c (hj.1.fst c) (hj.1.snd c) (hj.1.isPullback c)
  refine ⟨hic, hjc, ?_⟩
  have := hic
  have := hjc
  exact Stacks.AlgebraicGeometry.isSplitExactConormalSequence_of_isH1RegularImmersion _ _ hreg

end AlgebraicGeometry.Space

end
