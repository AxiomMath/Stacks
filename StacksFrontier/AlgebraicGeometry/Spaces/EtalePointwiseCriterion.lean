module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.EtaleAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage

/-!
# Étaleness at every point implies étaleness

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is étale at every point of `X` in the sense of
[Stacks Project, Tag 04RH]. Then `f` is étale. This is the implication from condition (2) to
condition (1) of [Stacks Project, Tag 03XT].

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isEtale_of_forall_isEtaleAt`: **Stacks 03XT**, condition (2)
  implies condition (1).

## Implementation notes

Étaleness at a point is the existence of an open subspace containing it on which the morphism
restricts to an étale morphism, so the chosen neighbourhoods of all the points of `X` form a
family of open subspaces whose point sets cover `|X|`. The inclusion of an open subspace is
étale (`AlgebraicGeometry.Space.isEtale_ι_of_isOpenSubspace`), so that family is an étale
covering of `X` in the sense of [Stacks Project, Tag 041E], and étaleness is local on the
source for the étale topology by [Stacks Project, Tag 06F4],
`AlgebraicGeometry.Space.isEtale_isLocalAtSource_etale`; the restriction of `f` to each member
of the covering is étale by hypothesis.

The index type of the covering is the point set `AlgebraicGeometry.Space.points` of `X`, which
lives in `Type (u + 1)`, so the precoverage of [Stacks Project, Tag 03YH] and the locality
instance are instantiated with their index universe at `u + 1`.

The other direction of condition (2) is not proved here, so the attribute names the
implication it covers; condition (7) of the same tag is
`AlgebraicGeometry.Space.isEtale_iff_holdsOnEveryEtaleChart`.

## References

* [Stacks Project, Tag 03XT](https://stacks.math.columbia.edu/tag/03XT)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 04RH](https://stacks.math.columbia.edu/tag/04RH)
* [Stacks Project, Tag 06F4](https://stacks.math.columbia.edu/tag/06F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 03XT, condition (2) implies condition (1).** A morphism of algebraic spaces over
`S` which is étale at every point of its source is étale. -/
theorem isEtale_of_forall_isEtaleAt (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h : ∀ x : points B S hS X, IsEtaleAt B S hS f x) :
    IsEtale B S hS f := by
  classical
  choose U hU x' hx' hUf using h
  let XS : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let YS : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let US : points B S hS X → AlgebraicSpaces B S hS := fun x => ⟨(U x).toFunctor, (hU x).1⟩
  let ιS : ∀ x, US x ⟶ XS := fun x => ObjectProperty.homMk (U x).ι
  have hcov : IsEtaleCovering B S hS (fun x => (US x).obj) (fun x => (ιS x).hom) :=
    ⟨hX, fun x => (hU x).1, fun x => isEtale_ι_of_isOpenSubspace (hU x),
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨x, ⟨x' x, hx' x⟩⟩⟩
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => IsEtale B S hS k.hom
  let _ : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .etale B S hS) :=
    isEtale_isLocalAtSource_etale.{u, u + 1} B S hS
  have hR : Presieve.ofArrows US ιS ∈ Topology.precoverage.{u, u + 1} .etale B S hS XS :=
    ⟨points B S hS X, US, ιS, rfl, hX, fun x => (hU x).1, hcov⟩
  show Q (ObjectProperty.homMk f : XS ⟶ YS)
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := Q) hR ?_
  rintro _ _ ⟨x⟩
  exact hUf x

end AlgebraicGeometry.Space

end
