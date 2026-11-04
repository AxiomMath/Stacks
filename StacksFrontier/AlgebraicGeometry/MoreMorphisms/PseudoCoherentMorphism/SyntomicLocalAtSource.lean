module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme

/-!
# Source locality of pseudo-coherence for the syntomic topology

Pseudo-coherence of a morphism of schemes is preserved by precomposition with a syntomic
morphism, and that is three quarters of the criterion of Tag 036H for a property to be local on
the source for the syntomic topology: the remaining two hypotheses of the criterion, Zariski
locality on the source and on the target, hold because pseudo-coherence is the affine-local
property attached to `RingHom.PseudoCoherent` (Tag 067Z).

What the criterion leaves is a single statement about affine schemes: if `X' → X` is a surjective
syntomic morphism of affine schemes and `X' → Y` is pseudo-coherent, then `X → Y` is
pseudo-coherent. That statement is the mathematical content of Tag 0698 and is taken here as a
hypothesis.

## Main results

* `AlgebraicGeometry.PseudoCoherent.respectsLeft_syntomic`: precomposition with a syntomic
  morphism preserves pseudo-coherence. A syntomic morphism is flat and locally of finite
  presentation (Tags 01UL and 01UK), hence pseudo-coherent (Tag 0695), and pseudo-coherent
  morphisms compose (Tag 0681).
* `AlgebraicGeometry.pseudoCoherent_isLocalAtSource_of_affine_descent`: pseudo-coherence is
  local on the source for the syntomic topology, given that it descends along a surjective
  syntomic morphism of affine schemes.

## Implementation notes

Syntomic coverings of the source are the covering families of
`AlgebraicGeometry.Scheme.precoverage` of `AlgebraicGeometry.Syntomic`, which are exactly the
syntomic coverings of Tag 0225; `CategoryTheory.MorphismProperty.IsLocalAtSource` at that
precoverage says that a morphism has the property exactly when its composites with the members
of such a covering of its source do, which is the source's notion of being local on the source.

Zariski locality on the target is the instance
`AlgebraicGeometry.pseudoCoherent_isZariskiLocalAtTarget`. Zariski locality on the source is
supplied by `let` rather than by synthesis: Mathlib's
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource` does not apply to
`@AlgebraicGeometry.PseudoCoherent` in type class search, for the reason given at
`AlgebraicGeometry.pseudoCoherent_isZariskiLocalAtTarget`, and the instance
`AlgebraicGeometry.pseudoCoherent_isZariskiLocalAtSource` lives in a module this one does not
import. `CategoryTheory.MorphismProperty.RespectsLeft` is supplied by `let` too, from
`AlgebraicGeometry.PseudoCoherent.respectsLeft_syntomic`.

## References

* [The Stacks Project, Lemma 37.60.13 (0698)](https://stacks.math.columbia.edu/tag/0698)
* [The Stacks Project, Lemma 35.26.4 (036H)](https://stacks.math.columbia.edu/tag/036H)
* [The Stacks Project, Lemma 37.60.2 (0681)](https://stacks.math.columbia.edu/tag/0681)
* [The Stacks Project, Lemma 37.60.6 (0695)](https://stacks.math.columbia.edu/tag/0695)
* [The Stacks Project, Lemma 29.31.6 (01UK)](https://stacks.math.columbia.edu/tag/01UK)
* [The Stacks Project, Lemma 29.31.7 (01UL)](https://stacks.math.columbia.edu/tag/01UL)
* [The Stacks Project, Definition 37.60.2 (067Z)](https://stacks.math.columbia.edu/tag/067Z)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Precomposition with a syntomic morphism preserves pseudo-coherence of morphisms of schemes.

A syntomic morphism is flat and locally of finite presentation, hence pseudo-coherent by
Tag 0695, and a composition of pseudo-coherent morphisms is pseudo-coherent by Tag 0681. -/
theorem PseudoCoherent.respectsLeft_syntomic :
    MorphismProperty.RespectsLeft (@PseudoCoherent.{u} : MorphismProperty Scheme.{u})
      (@Syntomic.{u} : MorphismProperty Scheme.{u}) where
  precomp i hi f hf := by
    have : Flat i := flat hi
    have : LocallyOfFinitePresentation i := locallyOfFinitePresentation hi
    have : PseudoCoherent f := hf
    exact inferInstance

/-- Pseudo-coherence of morphisms of schemes is local on the source for the syntomic topology,
given that pseudo-coherence descends along a surjective syntomic morphism of affine schemes.

The hypothesis `hAffine` is the pseudo-coherent case of the affine descent of Tag 036H, which is
the mathematical content of Tag 0698. -/
theorem pseudoCoherent_isLocalAtSource_of_affine_descent
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Syntomic g → PseudoCoherent (g ≫ f) →
        PseudoCoherent f) :
    MorphismProperty.IsLocalAtSource (@PseudoCoherent.{u} : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Syntomic.{u})) :=
  let := PseudoCoherent.respectsLeft_syntomic.{u}
  let : IsZariskiLocalAtSource (@PseudoCoherent.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.PseudoCoherent)
  isLocalAtSource_syntomic_of_affine_descent (@PseudoCoherent.{u}) hAffine

end AlgebraicGeometry

end
