module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Perfect

/-!
# Pseudo-coherence, perfection and local finite presentation

Pseudo-coherence of a morphism of algebraic spaces implies local finite presentation, and
for a flat morphism the two are equivalent; a flat morphism is moreover perfect exactly
when it is locally of finite presentation.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isPseudoCoherent`:
  **Stacks 06BU**, a pseudo-coherent morphism is locally of finite presentation.
* `AlgebraicGeometry.Space.isPseudoCoherent_of_isFlat_of_isLocallyOfFinitePresentation`:
  **Stacks 06BV**, a flat morphism locally of finite presentation is pseudo-coherent.
* `AlgebraicGeometry.Space.isFlat_and_isPerfect_iff_isFlat_and_isLocallyOfFinitePresentation`:
  **Stacks 06C2**, a flat morphism is perfect exactly when it is locally of finite
  presentation.

## Implementation notes

All four properties involved are the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ applied to a property of
scheme morphisms, so each statement reduces chartwise to its scheme-level counterpart:
Stacks 0682 for the first, Stacks 0695 for the second and Stacks 068A for the third. In
particular none of the three needs the source or target to be algebraic, exactly as in the
source.

## References

* [Stacks Project, Tag 06BU](https://stacks.math.columbia.edu/tag/06BU)
* [Stacks Project, Tag 06BV](https://stacks.math.columbia.edu/tag/06BV)
* [Stacks Project, Tag 06C2](https://stacks.math.columbia.edu/tag/06C2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 06BU.** A pseudo-coherent morphism of algebraic spaces over `S` is locally of
finite presentation. -/
@[stacks 06BU]
theorem isLocallyOfFinitePresentation_of_isPseudoCoherent (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : IsPseudoCoherent B S hS f) :
    IsLocallyOfFinitePresentation B S hS f := fun U V a b h ha hb comm =>
  @_root_.AlgebraicGeometry.locallyOfFinitePresentation_of_pseudoCoherent _ _ _
    (hf U V a b h ha hb comm)

/-- **Stacks 06BV.** A flat morphism of algebraic spaces over `S` which is locally of
finite presentation is pseudo-coherent. -/
@[stacks 06BV]
theorem isPseudoCoherent_of_isFlat_of_isLocallyOfFinitePresentation (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f) :
    IsPseudoCoherent B S hS f := fun U V a b h ha hb comm =>
  @_root_.AlgebraicGeometry.pseudoCoherent_of_flat_of_locallyOfFinitePresentation _ _ _
    (hflat U V a b h ha hb comm) (hfp U V a b h ha hb comm)

/-- **Stacks 06C2.** A morphism of algebraic spaces over `S` is flat and perfect if and
only if it is flat and locally of finite presentation. -/
@[stacks 06C2]
theorem isFlat_and_isPerfect_iff_isFlat_and_isLocallyOfFinitePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    (IsFlat B S hS f ∧ IsPerfect B S hS f) ↔
      (IsFlat B S hS f ∧ IsLocallyOfFinitePresentation B S hS f) := by
  constructor <;> rintro ⟨hflat, hp⟩ <;> refine ⟨hflat, ?_⟩ <;> intro U V a b h ha hb comm
  · exact ((_root_.AlgebraicGeometry.flat_and_perfect_iff_flat_and_locallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map h)).mp
        ⟨hflat U V a b h ha hb comm, hp U V a b h ha hb comm⟩).2
  · exact ((_root_.AlgebraicGeometry.flat_and_perfect_iff_flat_and_locallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map h)).mpr
        ⟨hflat U V a b h ha hb comm, hp U V a b h ha hb comm⟩).2

end AlgebraicGeometry.Space

end
