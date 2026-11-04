module

public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalenceRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorOfInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpectrum

/-!
# The multiplicative torsor as a relative spectrum that exists

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module.  Its Laurent
algebra `⨁_{n ∈ ℤ} ℒ^{⊗ n}` is a quasi-coherent `𝒪_X`-algebra
(`AlgebraicGeometry.Space.isQuasicoherent_laurentAlgebraSheaf`), so the multiplicative torsor
`q : T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n}) ⟶ X` is the relative spectrum of Stacks 081W of
that algebra.  This file constructs it in two ways, neither taking the parameter `E` below.

`AlgebraicGeometry.Space.multiplicativeTorsor` forms it through
`AlgebraicGeometry.Space.relativeSpec`, which takes as a parameter an inhabitant `E` of
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`, Stacks 081V with the tag's unrestricted
target.  Over any site one of whose algebraic spaces has an affine étale chart with a nonzero
ring of functions, that type is empty
(`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`),
so neither `T` nor `q` can be formed from the hypotheses of Situation 0EDT, and a statement
about them under `E` asserts nothing over any such site.

## Main definitions

* `AlgebraicGeometry.Space.boundedMultiplicativeTorsor`: `T` inside the big fppf site of `X`,
  for a Laurent algebra satisfying the size condition
  `AlgebraicGeometry.Space.AlgebraSheaf.SectionsBelowCutoff` of the corrected Stacks 081V, with
  `AlgebraicGeometry.Space.boundedMultiplicativeTorsorProjection` its projection `q : T ⟶ X`.
* `AlgebraicGeometry.Space.multiplicativeTorsorSpectrum`: `T` with no hypothesis whatsoever,
  on the enlargement `AlgebraicGeometry.Space.relativeSpectrumSite` of the big fppf site of `X`
  that Stacks 03FO supplies, with
  `AlgebraicGeometry.Space.multiplicativeTorsorSpectrumProjection` its projection `q : T ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.sectionsBelowCutoff_laurentAlgebraSheaf_of_antiEquivalence`: the size
  condition on the Laurent algebra follows from `E`.  So the bounded construction is a
  strict generalization of `AlgebraicGeometry.Space.multiplicativeTorsor`: its hypothesis is
  implied by the parameter that one carries, and unlike that parameter it is not refuted.
* `AlgebraicGeometry.Space.isAffineHom_multiplicativeTorsorSpectrumProjection`: `q` is affine,
  under the hypotheses of Situation 0EDT alone.
* `AlgebraicGeometry.Space.isAffineHom_boundedMultiplicativeTorsorProjection`: the same for the
  construction inside the site of `X`.

The size hypothesis of the bounded construction is not a hypothesis of Stacks 0EQG; it renders
the set-theoretic conventions under which Stacks 081V holds.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 03FO](https://stacks.math.columbia.edu/tag/03FO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-! ### The size condition, and what it replaces -/

/-- An inhabitant of the unrestricted Stacks 081V forces the size condition on the Laurent
algebra of `ℒ`. -/
theorem sectionsBelowCutoff_laurentAlgebraSheaf_of_antiEquivalence
    (E : AffineAlgebraAntiEquivalence D.site D.base D.base_mem) :
    AlgebraSheaf.SectionsBelowCutoff D.site D.base D.base_mem
      (X := ⟨X, hp.1⟩) (laurentAlgebraSheaf D p hp L hL) :=
  E.sectionsBelowCutoff
    (laurentQuasicoherentAlgebra D p hp L hL (isQuasicoherent_laurentAlgebraSheaf D p hp L hL))

/-! ### The torsor inside the site of `X` -/

variable (hb : AlgebraSheaf.SectionsBelowCutoff D.site D.base D.base_mem
  (X := ⟨X, hp.1⟩) (laurentAlgebraSheaf D p hp L hL))

/-- The multiplicative torsor `T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n})` of an invertible
`𝒪_X`-module, as an algebraic space affine over `X` in the big fppf site of `X`: the relative
spectrum of Stacks 081W, in the bounded form `AlgebraicGeometry.Space.boundedRelativeSpec`. -/
def boundedMultiplicativeTorsor : AffineOver D.site D.base D.base_mem ⟨X, hp.1⟩ :=
  boundedRelativeSpec D.site D.base D.base_mem
    (laurentQuasicoherentAlgebra D p hp L hL (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)) hb

/-- The algebraic space `T` underlying the multiplicative torsor of `ℒ`, in the site of `X`. -/
abbrev boundedMultiplicativeTorsorSpace : AlgebraicSpaces D.site D.base D.base_mem :=
  (boundedMultiplicativeTorsor D p hp L hL hb).obj.left

/-- The projection `q : T ⟶ X` of the multiplicative torsor of `ℒ`, in the site of `X`. -/
abbrev boundedMultiplicativeTorsorProjection :
    boundedMultiplicativeTorsorSpace D p hp L hL hb ⟶ ⟨X, hp.1⟩ :=
  (boundedMultiplicativeTorsor D p hp L hL hb).obj.hom

/-- The projection `q : T ⟶ X` of the multiplicative torsor of an invertible `𝒪_X`-module is
an affine morphism of algebraic spaces, for the torsor formed inside the big fppf site of
`X`. -/
theorem isAffineHom_boundedMultiplicativeTorsorProjection :
    IsAffineHom D.site D.base D.base_mem
      (boundedMultiplicativeTorsorProjection D p hp L hL hb).hom :=
  (boundedMultiplicativeTorsor D p hp L hL hb).property

/-! ### The torsor with no hypothesis -/

/-- The multiplicative torsor `T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n})` of an invertible
`𝒪_X`-module, as an algebraic space affine over `X`, under the hypotheses of Situation 0EDT
alone: the relative spectrum of Stacks 081W, in the form
`AlgebraicGeometry.Space.relativeSpectrum` that takes no hypothesis on the algebra beyond
quasi-coherence.

It is an algebraic space of `AlgebraicGeometry.Space.relativeSpectrumSite`, an enlargement of the
big fppf site of `X` supplied by Stacks 03FO, and is affine over
`AlgebraicGeometry.Space.relativeSpectrumBase`, which is `X` read there by Stacks 03FP. -/
def multiplicativeTorsorSpectrum :
    AffineOver
      (relativeSpectrumSite
        (laurentQuasicoherentAlgebra D p hp L hL (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)))
      D.base
      (contains_relativeSpectrumSite
        (laurentQuasicoherentAlgebra D p hp L hL (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)))
      (relativeSpectrumBase
        (laurentQuasicoherentAlgebra D p hp L hL
          (isQuasicoherent_laurentAlgebraSheaf D p hp L hL))) :=
  relativeSpectrum
    (laurentQuasicoherentAlgebra D p hp L hL (isQuasicoherent_laurentAlgebraSheaf D p hp L hL))

/-- The algebraic space `T` underlying the multiplicative torsor of `ℒ`, over the enlarged
site. -/
abbrev multiplicativeTorsorSpectrumSpace :
    AlgebraicSpaces
      (relativeSpectrumSite
        (laurentQuasicoherentAlgebra D p hp L hL (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)))
      D.base
      (contains_relativeSpectrumSite
        (laurentQuasicoherentAlgebra D p hp L hL
          (isQuasicoherent_laurentAlgebraSheaf D p hp L hL))) :=
  (multiplicativeTorsorSpectrum D p hp L hL).obj.left

/-- The projection `q : T ⟶ X` of the multiplicative torsor of `ℒ`, over the enlarged
site. -/
abbrev multiplicativeTorsorSpectrumProjection :
    multiplicativeTorsorSpectrumSpace D p hp L hL ⟶
      relativeSpectrumBase
        (laurentQuasicoherentAlgebra D p hp L hL
          (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)) :=
  (multiplicativeTorsorSpectrum D p hp L hL).obj.hom

/-- The projection `q : T ⟶ X` of the multiplicative torsor of an invertible `𝒪_X`-module is
an affine morphism of algebraic spaces, under the hypotheses of Situation 0EDT and no others:
`X/B` good and `ℒ` invertible. -/
@[stacks 0EQG "clause (1), the affineness part only, in Situation 0EDT with X/B good: for an
invertible O_X-module L the projection q of T = Spec_X(⨁_{n ∈ ℤ} L^{⊗n}) is affine.  Carries NO
parameter and no size condition: quasi-coherence of the Laurent algebra is discharged by
isQuasicoherent_laurentAlgebraSheaf, itself resting on triviality of L on an etale covering,
discharged by isLocallyTrivial_of_isInvertibleSheaf from local ringedness of the small etale
site, and T is formed by relativeSpectrum, the unconditional form of Stacks 081W.  This replaces
isAffineHom_multiplicativeTorsorProjection, which asserts the same thing under a parameter
E : AffineAlgebraAntiEquivalence that is EMPTY over any site one of whose algebraic spaces has an
affine etale chart with a nonzero ring of functions
(not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart) and so asserts nothing
there.  q lives over relativeSpectrumSite, the Stacks 03FO enlargement of the site of X;
isAffineHom_boundedMultiplicativeTorsorProjection is the same assertion inside the site of X
itself, under the size condition of the corrected 081V, which E implies.
NOT COVERED by this or any other declaration: the rest of clause (1) -- q surjective, smooth and
of relative dimension 1 -- and clauses (2), (4), (5), (6), (7).  The source derives the three
remaining properties of clause (1) from T x_X U ≅ G_m x U for an etale chart U trivialising L,
and that identification does not exist in this tree: isPullback_affineChartSpec identifies the
relative spectrum over an affine chart with Spec of the algebra's sections there, nothing
identifies the Laurent algebra's sections at a trivialising chart V with O(V)[t,t^{-1}] (the
sheafification step is unaccounted for), and no scheme-level smoothness, surjectivity or
relative-dimension statement about multiplicativeGroupBaseChange exists"]
theorem isAffineHom_multiplicativeTorsorSpectrumProjection :
    IsAffineHom
      (relativeSpectrumSite
        (laurentQuasicoherentAlgebra D p hp L hL (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)))
      D.base
      (contains_relativeSpectrumSite
        (laurentQuasicoherentAlgebra D p hp L hL
          (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)))
      (multiplicativeTorsorSpectrumProjection D p hp L hL).hom :=
  (multiplicativeTorsorSpectrum D p hp L hL).property

end AlgebraicGeometry.Space

end
