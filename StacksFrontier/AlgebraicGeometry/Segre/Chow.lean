module

public import StacksFrontier.AlgebraicGeometry.AffineSpaceImmersion.Chow
public import StacksFrontier.AlgebraicGeometry.Segre.Basic

/-!
# Chow's lemma over a Noetherian base, from one monomorphism between the integral models

Chow's lemma over a Noetherian base (Stacks 0200) is proved in
`StacksFrontier/AlgebraicGeometry/ChowNoetherian/Basic.lean` from two hypotheses, both tags of
Chapter 29; `StacksFrontier/AlgebraicGeometry/AffineSpaceImmersion/Chow.lean` discharges the
first (Stacks 01VS for the structure sheaf) for every base, leaving
`AlgebraicGeometry.HasSegreEmbedding` — **Stacks 01WD** — as the only hypothesis.
`StacksFrontier/AlgebraicGeometry/Segre/Basic.lean` reduces that hypothesis, for every base at
once, to `AlgebraicGeometry.HasSegreMonoZ`: a monomorphism of schemes
`ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙᴺ_ℤ`.

This file composes the two, and so records exactly what Chow's lemma over a Noetherian base now
costs in this repository.

## Main results

* `AlgebraicGeometry.hasDenseChowModification_of_hasSegreMonoZ`: **Chow's lemma over a Noetherian
  base, dense-open clause included, granted only a monomorphism between the integral models.**
* `AlgebraicGeometry.hasChowModification_of_hasSegreMonoZ`: the same in the form the proof of
  Chow's lemma over a quasi-compact quasi-separated base (Stacks 0202) consumes.

## Implementation notes

The tag `@[stacks 0200]` is still not attached to anything. These statements are conditional on
`AlgebraicGeometry.HasSegreMonoZ` and 0200 asserts its conclusion outright; the tag belongs on
`AlgebraicGeometry.hasDenseChowModification_of_hasSegreMonoZ` the moment that hypothesis is
proved, and nothing in this repository proves it.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- **Chow's lemma over a Noetherian base (Stacks 0200), granted a monomorphism between the
integral models of projective space.** A separated morphism of finite type over a Noetherian base
admits a proper surjective modification immersed in a projective space over the base, which is an
isomorphism over a dense open subscheme of the source.

The single hypothesis is `AlgebraicGeometry.HasSegreMonoZ`: for all `n` and `m` there are an `N`
and a monomorphism `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙᴺ_ℤ`. -/
theorem hasDenseChowModification_of_hasSegreMonoZ (h : HasSegreMonoZ.{u}) (f : X ⟶ S)
    [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    HasDenseChowModification f :=
  hasDenseChowModification_of_hasSegreEmbedding
    (hasSegreEmbedding_of_hasSegreEmbeddingZ (hasSegreEmbeddingZ_of_hasSegreMonoZ h) S) f

/-- **Chow's lemma over a Noetherian base from a monomorphism between the integral models, in the
form consumed by the proof of Chow's lemma over a quasi-compact quasi-separated base (Stacks
0202).** -/
theorem hasChowModification_of_hasSegreMonoZ (h : HasSegreMonoZ.{u}) (f : X ⟶ S)
    [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    HasChowModification f :=
  (hasDenseChowModification_of_hasSegreMonoZ h f).hasChowModification

end AlgebraicGeometry

end
