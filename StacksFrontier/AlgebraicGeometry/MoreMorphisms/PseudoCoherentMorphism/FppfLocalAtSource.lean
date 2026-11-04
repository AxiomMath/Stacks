module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.LocallyQuasiFiniteRefinement

/-!
# Source locality of pseudo-coherence for the fppf topology

Pseudo-coherence of a morphism of schemes is local on the source for the fppf topology, granted
the descent of pseudo-coherence along a surjective finite locally free morphism.

The reduction to that one case is the argument of Tag 0699. An fppf covering of the source is
refined, by Tag 05WN, by a family built in four steps: a Zariski open covering, a surjective
finite locally free morphism, a second Zariski open covering, and a second surjective finite
locally free morphism. Each member of the refinement is flat and locally of finite presentation,
hence pseudo-coherent (Tag 0695), and it factors through a member of the original covering; the
cancellation property of Tag 0683 therefore makes the factoring morphism pseudo-coherent, and
composing with the hypothesis on the original covering (Tag 0681) makes every member of the
refinement pseudo-coherent over the target. The four steps of the refinement are then peeled off
in turn: the two Zariski steps by the Zariski source locality of pseudo-coherence, and the two
finite locally free steps by the assumed descent.

## Main results

* `AlgebraicGeometry.PseudoCoherent.respectsLeft_flat_inf_locallyOfFinitePresentation`:
  precomposition with a flat morphism locally of finite presentation preserves pseudo-coherence.
  Such a morphism is pseudo-coherent (Tag 0695) and pseudo-coherent morphisms compose
  (Tag 0681).
* `AlgebraicGeometry.pseudoCoherent_isLocalAtSource_fppf_of_finiteLocallyFree_descent`:
  pseudo-coherence is local on the source for the fppf topology, given that it descends along a
  surjective finite locally free morphism.

## Implementation notes

The Zariski source locality of pseudo-coherence is supplied by name rather than by instance
synthesis, because the property of ring maps indexing `AlgebraicGeometry.HasRingHomProperty` is
not an output parameter and so cannot be inferred from `AlgebraicGeometry.PseudoCoherent`
alone; the invariance of pseudo-coherence under isomorphisms is extracted from it for the same
reason.

The descent along a surjective finite locally free morphism is deliberately left as a
hypothesis, so the statement below carries no tag; a consumer that discharges it obtains
Tag 0699 outright.

## References

* [The Stacks Project, Lemma 37.60.14 (0699)](https://stacks.math.columbia.edu/tag/0699)
* [The Stacks Project, Lemma 35.36.1 (05WN)](https://stacks.math.columbia.edu/tag/05WN)
* [The Stacks Project, Lemma 37.60.2 (0681)](https://stacks.math.columbia.edu/tag/0681)
* [The Stacks Project, Lemma 37.60.4 (0683)](https://stacks.math.columbia.edu/tag/0683)
* [The Stacks Project, Lemma 37.60.6 (0695)](https://stacks.math.columbia.edu/tag/0695)
* [The Stacks Project, Lemma 29.48.2 (02KB)](https://stacks.math.columbia.edu/tag/02KB)
* [The Stacks Project, Definition 37.60.2 (067Z)](https://stacks.math.columbia.edu/tag/067Z)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A flat morphism locally of finite presentation is pseudo-coherent (Tag 0695). -/
private theorem pseudoCoherent_of_flat_inf_locallyOfFinitePresentation {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) f) :
    PseudoCoherent f := by
  have : Flat f := hf.1
  have : LocallyOfFinitePresentation f := hf.2
  exact inferInstance

/-- A finite locally free morphism is pseudo-coherent, being flat and locally of finite
presentation. -/
private theorem pseudoCoherent_of_isFiniteLocallyFree {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : Stacks.Morphisms.IsFiniteLocallyFree f) : PseudoCoherent f :=
  pseudoCoherent_of_flat_inf_locallyOfFinitePresentation
    ⟨Stacks.Morphisms.IsFiniteLocallyFree.flat _,
      Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation _⟩

/-- Precomposition with a flat morphism locally of finite presentation preserves
pseudo-coherence of morphisms of schemes.

A flat morphism locally of finite presentation is pseudo-coherent by Tag 0695, and a composition
of pseudo-coherent morphisms is pseudo-coherent by Tag 0681. -/
theorem PseudoCoherent.respectsLeft_flat_inf_locallyOfFinitePresentation :
    MorphismProperty.RespectsLeft (@PseudoCoherent.{u} : MorphismProperty Scheme.{u})
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) where
  precomp i hi f hf := by
    have : PseudoCoherent i := pseudoCoherent_of_flat_inf_locallyOfFinitePresentation hi
    have : PseudoCoherent f := hf
    exact inferInstance

/-- Pseudo-coherence of morphisms of schemes is local on the source for the fppf topology,
given that pseudo-coherence descends along a surjective finite locally free morphism.

An fppf covering of the source is refined, by Tag 05WN, by a four-step family: a Zariski open
covering, a surjective finite locally free morphism, a second Zariski open covering, and a
second surjective finite locally free morphism. Every member of the refinement is a composition
of finite locally free morphisms and open immersions, hence flat and locally of finite
presentation (Tag 02KB) and so pseudo-coherent (Tag 0695); it factors through a member of the
original covering, which is itself pseudo-coherent for the same reason, so the factoring
morphism is pseudo-coherent by the cancellation property of Tag 0683. Composing with the
assumption on the original covering (Tag 0681) shows that every member of the refinement is
pseudo-coherent over the target, and the four steps are peeled off in turn using the Zariski
source locality of pseudo-coherence for the two open coverings and the assumed descent for the
two finite locally free morphisms.

The remaining hypothesis is the whole mathematical content left open here; a consumer that
discharges it obtains Tag 0699 outright. -/
theorem pseudoCoherent_isLocalAtSource_fppf_of_finiteLocallyFree_descent
    (hflf : ∀ {T W Y : Scheme.{u}} (h : T ⟶ W) (f : W ⟶ Y), Surjective h →
      Stacks.Morphisms.IsFiniteLocallyFree h → PseudoCoherent (h ≫ f) → PseudoCoherent f) :
    MorphismProperty.IsLocalAtSource (@PseudoCoherent.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage := by
  have hls : IsZariskiLocalAtSource (@PseudoCoherent.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.PseudoCoherent)
  have : MorphismProperty.RespectsIso (@PseudoCoherent.{u}) := hls.toRespects
  refine MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover ?_
  intro X Y f 𝒮
  have hmem (i : 𝒮.I₀) : PseudoCoherent (𝒮.f i) :=
    pseudoCoherent_of_flat_inf_locallyOfFinitePresentation (Scheme.Cover.map_prop 𝒮 i)
  refine ⟨fun hf i ↦ ?_, fun hcomp ↦ ?_⟩
  · have : PseudoCoherent (𝒮.f i) := hmem i
    have : PseudoCoherent f := hf
    exact inferInstance
  obtain ⟨𝒰, W, g, 𝒲, T, h, hg, hh, -, hfac⟩ :=
    Stacks.Topologies.Fppf.exists_openCover_finiteLocallyFree_refinement_of_hasQuasiFiniteSlices
      hasQuasiFiniteSlices X 𝒮
  have key : ∀ j k, PseudoCoherent (h j k ≫ (𝒲 j).f k ≫ g j ≫ 𝒰.f j ≫ f) := by
    intro j k
    obtain ⟨i, l, hl⟩ := hfac j k
    have : PseudoCoherent (h j k) := pseudoCoherent_of_isFiniteLocallyFree (hh j k).2
    have : PseudoCoherent (g j) := pseudoCoherent_of_isFiniteLocallyFree (hg j).2
    have hc : PseudoCoherent (h j k ≫ (𝒲 j).f k ≫ g j ≫ 𝒰.f j) := inferInstance
    have hls₂ : PseudoCoherent (l ≫ 𝒮.f i) := by rw [hl]; exact hc
    have : PseudoCoherent (𝒮.f i) := hmem i
    have : PseudoCoherent l := pseudoCoherent_of_comp l (𝒮.f i)
    have : PseudoCoherent (𝒮.f i ≫ f) := hcomp i
    have hfin : PseudoCoherent (l ≫ 𝒮.f i ≫ f) := inferInstance
    rw [← Category.assoc, hl] at hfin
    simpa only [Category.assoc] using hfin
  have peel₁ : ∀ j k, PseudoCoherent ((𝒲 j).f k ≫ g j ≫ 𝒰.f j ≫ f) := fun j k ↦
    hflf (h j k) _ (hh j k).1 (hh j k).2 (key j k)
  have peel₂ : ∀ j, PseudoCoherent (g j ≫ 𝒰.f j ≫ f) := fun j ↦
    IsZariskiLocalAtSource.of_openCover (𝒲 j) (peel₁ j)
  have peel₃ : ∀ j, PseudoCoherent (𝒰.f j ≫ f) := fun j ↦
    hflf (g j) _ (hg j).1 (hg j).2 (peel₂ j)
  exact IsZariskiLocalAtSource.of_openCover 𝒰 peel₃

end AlgebraicGeometry

end
