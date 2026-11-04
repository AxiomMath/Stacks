module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.Morphism
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.PseudoCoherentMap.Flat

/-!
# Flat perfect morphisms

A perfect morphism of schemes is pseudo-coherent, hence locally of finite presentation, and
conversely a flat morphism locally of finite presentation is perfect. Together these say that
among flat morphisms, perfectness and local finite presentation are the same condition.

## Main results

* `AlgebraicGeometry.pseudoCoherent_of_perfect`: a perfect morphism is pseudo-coherent.
* `AlgebraicGeometry.locallyOfFinitePresentation_of_perfect`: **Stacks 0685**, the unnumbered
  assertion of the section on perfect morphisms that a perfect morphism is pseudo-coherent,
  hence locally of finite presentation.
* `AlgebraicGeometry.perfect_of_flat_of_locallyOfFinitePresentation`: a flat morphism locally of
  finite presentation is perfect.
* `AlgebraicGeometry.flat_and_perfect_iff_flat_and_locallyOfFinitePresentation`: Stacks 068A, the
  equivalence of being flat and perfect with being flat and locally of finite presentation.

## Implementation notes

The forward implication of Stacks 068A needs no flatness: pseudo-coherence is the first
conjunct of perfectness of a ring map, so a perfect morphism is pseudo-coherent, and a
pseudo-coherent morphism is locally of finite presentation by Stacks 0682. The two implications
are therefore recorded separately as instances, at the generality each of them has, and the
equivalence is assembled from them.

Perfectness of the map on sections is a condition on an arbitrary certified derived tensor
product, so extracting it needs one; `StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring`
supplies the canonical one. The derived categories come from `HasDerivedCategory.standard`, which
is only ever a local instance, so it is re-declared here.

## References

* [The Stacks Project, Section 37.61 (0685)](https://stacks.math.columbia.edu/tag/0685)
* [The Stacks Project, Lemma 37.61.4 (068A)](https://stacks.math.columbia.edu/tag/068A)
* [The Stacks Project, Lemma 37.60.3 (0682)](https://stacks.math.columbia.edu/tag/0682)
* [The Stacks Project, Lemma 15.83.4 (067J)](https://stacks.math.columbia.edu/tag/067J)
-/

public section

open CategoryTheory StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- A perfect morphism of schemes is pseudo-coherent: pseudo-coherence of the map on sections is
the first conjunct of perfectness of that map, by Stacks 067H. -/
public instance pseudoCoherent_of_perfect {X S : Scheme.{u}} (f : X ⟶ S) [Perfect f] :
    PseudoCoherent f := by
  rw [HasRingHomProperty.iff_appLE (P := @PseudoCoherent)]
  intro V U e
  exact (Perfect.perfect_appLE f U.1 U.2 V.1 V.2 e
    (canonicalCertifiedDerivedTensoring Γ(S, V.1))).1

/-- **Stacks 0685.** A perfect morphism of schemes is locally of finite presentation: it is
pseudo-coherent, and a pseudo-coherent morphism is locally of finite presentation by Stacks
0682. -/
@[stacks 0685 "the section's unnumbered assertion that a perfect morphism is pseudo-coherent, \
hence locally of finite presentation; the fifteen numbered items of the section carry their \
own tags"]
public theorem locallyOfFinitePresentation_of_perfect {X S : Scheme.{u}} (f : X ⟶ S)
    [Perfect f] : LocallyOfFinitePresentation f :=
  locallyOfFinitePresentation_of_pseudoCoherent f

/-- A flat morphism of schemes which is locally of finite presentation is perfect, because a flat
ring map of finite presentation is perfect by Stacks 067J.

This is the implication (2) `⇒` (1) of Stacks 068A. -/
public instance perfect_of_flat_of_locallyOfFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] : Perfect f where
  perfect_appLE U hU V hV hUV := by
    let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    let : Module.Flat Γ(S, V) Γ(X, U) := f.flat_appLE hV hU hUV
    let : Algebra.FinitePresentation Γ(S, V) Γ(X, U) := f.finitePresentation_appLE hV hU hUV
    intro D
    exact (RingHom.isPerfectRingMap_of_flat_of_finitePresentation Γ(S, V) Γ(X, U)).2
      D.tensor D.comparison D.isLeftDerived

/-- **Stacks 068A.** A morphism of schemes is flat and perfect if and only if it is flat and
locally of finite presentation.

Neither implication uses flatness on the side it starts from: a perfect morphism is always
locally of finite presentation, through `AlgebraicGeometry.pseudoCoherent_of_perfect` and Stacks
0682, and a flat morphism locally of finite presentation is always perfect, through
`AlgebraicGeometry.perfect_of_flat_of_locallyOfFinitePresentation`. -/
@[stacks 068A]
public theorem flat_and_perfect_iff_flat_and_locallyOfFinitePresentation {X S : Scheme.{u}}
    (f : X ⟶ S) : (Flat f ∧ Perfect f) ↔ (Flat f ∧ LocallyOfFinitePresentation f) :=
  ⟨fun ⟨hflat, hperf⟩ =>
      ⟨hflat, @locallyOfFinitePresentation_of_pseudoCoherent _ _ f
        (@pseudoCoherent_of_perfect _ _ f hperf)⟩,
    fun ⟨hflat, hfp⟩ => ⟨hflat, @perfect_of_flat_of_locallyOfFinitePresentation _ _ f hflat hfp⟩⟩

end AlgebraicGeometry

end
