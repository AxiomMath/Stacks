module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.FlatBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composition and cancellation for pseudo-coherent morphisms of algebraic spaces

A composite of pseudo-coherent morphisms of algebraic spaces over `S` is pseudo-coherent, and a
morphism between two algebraic spaces which are pseudo-coherent over a common base algebraic
space is itself pseudo-coherent.

## Main results

* `AlgebraicGeometry.PseudoCoherent.isEtaleLocalOnSourceAndTarget`: pseudo-coherence of morphisms
  of schemes is étale local on the source and target.
* `AlgebraicGeometry.Space.isPseudoCoherent_comp`: **Stacks 06BT**, the composite of two
  pseudo-coherent morphisms of algebraic spaces over `S` is pseudo-coherent.
* `AlgebraicGeometry.Space.isPseudoCoherent_of_comp`: **Stacks 06BW**, a morphism `f : X ⟶ Y` of
  algebraic spaces over `S` for which both `f ≫ g : X ⟶ Z` and `g : Y ⟶ Z` are pseudo-coherent is
  itself pseudo-coherent.

## Implementation notes

Pseudo-coherence of a morphism of algebraic spaces is the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ applied to the scheme-morphism
property `AlgebraicGeometry.PseudoCoherent` of Stacks 067Z, so each statement is read off its
scheme-level counterpart on charts: Stacks 0681 for the composite and Stacks 0683 for the
cancellation. What carries a chart statement to the every-chart condition is étale locality of
pseudo-coherence of morphisms of schemes on the source and target, Stacks 04QZ. That is the
standing fact of the source's section on pseudo-coherent morphisms of algebraic spaces; here it
is `AlgebraicGeometry.PseudoCoherent.isEtaleLocalOnSourceAndTarget`, which combines the
reduction of Stacks 04R2 carried by
`AlgebraicGeometry.pseudoCoherent_isEtaleLocalOnSourceAndTarget` with source locality for the
étale topology, `AlgebraicGeometry.PseudoCoherent.isLocalAtSource_etalePrecoverage`.

The composite is the case of Stacks 0AML, `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_comp`,
at pseudo-coherence; its two inputs are stability of pseudo-coherence of scheme morphisms under
composition, which is Stacks 0681, and that étale locality. Unlike Stacks 06BU and 06C2 it is not
chartwise reducible to the scheme statement: the charts of the intermediate space produced by the
two hypotheses need not agree, so the square carrying the composite is one whose chart of the
source is merely surjective.

For the cancellation an étale atlas of `Z` is lifted through `g` and the resulting atlas of `Y`
through `f` (Stacks 02X1,
`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`), which produces a square of
étale charts for `f` whose chart of the source is surjective, together with the two factors `α`
and `β` of a chart morphism for `f ≫ g`. The scheme-level cancellation applies to those factors,
and Stacks 03MJ upgrades the one surjective square to every square.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
* [Stacks Project, Tag 067Z](https://stacks.math.columbia.edu/tag/067Z)
* [Stacks Project, Tag 0681](https://stacks.math.columbia.edu/tag/0681)
* [Stacks Project, Tag 0683](https://stacks.math.columbia.edu/tag/0683)
* [Stacks Project, Tag 06BT](https://stacks.math.columbia.edu/tag/06BT)
* [Stacks Project, Tag 06BW](https://stacks.math.columbia.edu/tag/06BW)
* [Stacks Project, Tag 0AML](https://stacks.math.columbia.edu/tag/0AML)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Pseudo-coherence of morphisms of schemes is étale local on the source and target in the sense
of Stacks 04QZ.

Source locality for the étale topology is the one input of the reduction of Stacks 04R2 carried
by `AlgebraicGeometry.pseudoCoherent_isEtaleLocalOnSourceAndTarget`.

The source states this as the standing fact of its section on pseudo-coherent morphisms of
algebraic spaces rather than as a numbered lemma, so no attribute is attached. -/
theorem PseudoCoherent.isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget (@PseudoCoherent.{u} : MorphismProperty Scheme.{u}) :=
  pseudoCoherent_isEtaleLocalOnSourceAndTarget
    PseudoCoherent.isLocalAtSource_etalePrecoverage.{u}

namespace Space

/-- **Stacks 06BT.** A composition of pseudo-coherent morphisms of algebraic spaces over `S` is
pseudo-coherent.

This is the case at pseudo-coherence of Stacks 0AML, the composition law for an every-étale-chart
property, whose inputs are Stacks 0681 and étale locality on the source and target. -/
@[stacks 06BT]
theorem isPseudoCoherent_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsPseudoCoherent B S hS f) (hg : IsPseudoCoherent B S hS g) :
    IsPseudoCoherent B S hS (f ≫ g) :=
  holdsOnEveryEtaleChart_comp B S hS _
    AlgebraicGeometry.PseudoCoherent.isEtaleLocalOnSourceAndTarget.{u} hX hY hZ f g hf hg

/-- **Stacks 06BW.** A morphism of algebraic spaces over `S` between two algebraic spaces
pseudo-coherent over a base algebraic space is pseudo-coherent.

An étale atlas of the base is lifted twice to produce a square of étale charts of `f` whose chart
of the source is surjective, and the scheme-level cancellation of Stacks 0683 applies to the two
factors of the induced chart morphism of `f ≫ g`. -/
@[stacks 06BW, sga "6 III 1.14" "partial"]
theorem isPseudoCoherent_of_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsPseudoCoherent B S hS (f ≫ g)) (hg : IsPseudoCoherent B S hS g) :
    IsPseudoCoherent B S hS f := by
  obtain ⟨W, c, hcSurjective, hcEtale⟩ := hZ.exists_atlas
  obtain ⟨V, d, β, hβ, hdSurjective, hdEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hY hZ g W c hcSurjective hcEtale
  obtain ⟨U, a, α, hα, haSurjective, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V d hdSurjective hdEtale
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@AlgebraicGeometry.PseudoCoherent.{u})
    AlgebraicGeometry.PseudoCoherent.isEtaleLocalOnSourceAndTarget.{u} hX hY f).mpr
    ⟨U, V, a, d, α, haEtale, hdEtale, haSurjective, hα.symm, ?_⟩
  let : AlgebraicGeometry.PseudoCoherent ((BigFppfOver.toScheme B S hS).map β) :=
    hg V W d c β hdEtale hcEtale hβ.symm
  let : AlgebraicGeometry.PseudoCoherent
      ((BigFppfOver.toScheme B S hS).map α ≫ (BigFppfOver.toScheme B S hS).map β) := by
    rw [← CategoryTheory.Functor.map_comp]
    refine hfg U W a c (α ≫ β) haEtale hcEtale ?_
    rw [CategoryTheory.Functor.map_comp, Category.assoc, ← hβ, ← Category.assoc, ← hα,
      Category.assoc]
  exact AlgebraicGeometry.pseudoCoherent_of_comp ((BigFppfOver.toScheme B S hS).map α)
    ((BigFppfOver.toScheme B S hS).map β)

end Space

end AlgebraicGeometry

end
