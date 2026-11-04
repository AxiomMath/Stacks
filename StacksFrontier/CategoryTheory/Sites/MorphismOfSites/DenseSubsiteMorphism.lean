module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs

/-!
# An equivalence of sites is a morphism of sites, and the two morphism-of-sites conditions

`IsMorphismOfSites.{w} F J K` of Stacks 00X1 asks a continuous functor `F : (C, J) ⥤ (D, K)`
for a left exact left adjoint of the direct image on sheaves of sets, at independent object and
morphism universes.  `CategoryTheory.Functor.IsMorphismOfSites` is the same condition written
for two sites whose objects and morphisms share a universe, phrased directly about Mathlib's
chosen `CategoryTheory.Functor.sheafPullback`.  The passage from the small condition to the
general one is `CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSites`; this file adds
the converse, and the one source of morphisms of sites that the general condition has and the
small one cannot express conveniently: a *dense subsite inclusion*, in particular either
direction of an equivalence of sites.

The dense-subsite case is immediate from Mathlib: for `F.IsDenseSubsite J K` the direct image
`F.sheafPushforwardContinuous A J K` is an equivalence of categories of sheaves, so it has a
left adjoint, namely its inverse, and an inverse of an equivalence preserves all limits.  No
exactness has to be checked by hand.

## Main results

* `IsMorphismOfSites.ofIsDenseSubsite`: **a dense subsite inclusion is a morphism of sites**,
  at independent universes.  Applied to the two functors of an equivalence of sites it says
  that an equivalence of sites is a morphism of sites in both directions.
* `IsMorphismOfSites.of_comp_isDenseSubsite`: a functor which becomes a morphism of sites after
  a dense subsite inclusion is one.
* `IsMorphismOfSites.toSmallIsMorphismOfSites`: on a pair of sites whose objects and morphisms
  lie in the universe of the sheaves of sets, the general condition gives the small one.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 03CB](https://stacks.math.columbia.edu/tag/03CB)
* [Stacks Project, Tag 03CH](https://stacks.math.columbia.edu/tag/03CH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u₁ v₁ u₂ v₂

section DenseSubsite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (F : C ⥤ D)

/-- **A dense subsite inclusion is a morphism of sites.** If `F` exhibits `(C, J)` as a dense
subsite of `(D, K)` then the direct image on sheaves of sets is an equivalence of categories,
so its inverse is a left adjoint of it and preserves all limits, in particular finite ones.

Applied to the two functors of an equivalence of sites — both of which are dense subsite
inclusions — this says that an equivalence of sites is a morphism of sites in either
direction. -/
public theorem IsMorphismOfSites.ofIsDenseSubsite [F.IsContinuous J K] [F.IsDenseSubsite J K]
    [∀ X : Dᵒᵖ, HasLimitsOfShape (StructuredArrow X F.op) (Type w)] :
    IsMorphismOfSites.{w} F J K :=
  { __ := ‹F.IsContinuous J K›
    hasExactLeftAdjoint :=
      ⟨(F.sheafPushforwardContinuous (Type w) J K).inv,
        ⟨(F.sheafPushforwardContinuous (Type w) J K).asEquivalence.symm.toAdjunction⟩,
        inferInstance⟩ }

/-- **A functor which becomes a morphism of sites after a dense subsite inclusion is one.**
If `u : (C, J) ⥤ (D, K)` is continuous, `i : (D, K) ⥤ (D', K')` is a dense subsite inclusion
and `u ⋙ i` is a morphism of sites, then so is `u`. The direct image along `i` is an equivalence
of categories of sheaves, so the direct image along `u` is the direct image along `u ⋙ i`
preceded by the inverse of that equivalence; its left adjoint is the left exact left adjoint of
the direct image along `u ⋙ i` followed by the direct image along `i`, again left exact. -/
public theorem IsMorphismOfSites.of_comp_isDenseSubsite {D' : Type*} [Category* D']
    {K' : GrothendieckTopology D'} (u : C ⥤ D) (i : D ⥤ D') [u.IsContinuous J K]
    [i.IsContinuous K K'] [i.IsDenseSubsite K K']
    [∀ X : D'ᵒᵖ, HasLimitsOfShape (StructuredArrow X i.op) (Type w)]
    (h : IsMorphismOfSites.{w} (u ⋙ i) J K') : IsMorphismOfSites.{w} u J K := by
  obtain ⟨L, ⟨adj⟩, hL⟩ := h.hasExactLeftAdjoint
  let P := i.sheafPushforwardContinuous (Type w) K K'
  let E := P.asEquivalence
  let adj' : L ⊣ P ⋙ u.sheafPushforwardContinuous (Type w) J K :=
    adj.ofNatIsoRight (Functor.sheafPushforwardContinuousComp u i (Type w) J K K').symm
  exact
    { __ := ‹u.IsContinuous J K›
      hasExactLeftAdjoint :=
        ⟨L ⋙ P, ⟨(adj'.comp E.toAdjunction).ofNatIsoRight
            ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight E.counitIso _ ≪≫
              Functor.leftUnitor _)⟩,
          comp_preservesFiniteLimits _ _⟩ }

end DenseSubsite

section Small

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D] {F : C ⥤ D}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- **The morphism-of-sites condition at independent universes gives the small one.** On two
sites whose objects and morphisms both lie in the universe of the sheaves of sets, Mathlib's
chosen `CategoryTheory.Functor.sheafPullback` is itself a left adjoint of the direct image, so
any left exact left adjoint is isomorphic to it; and it is right exact for free, being a left
adjoint.

This is the converse of
`CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSites`, and it is what makes a
composite of morphisms of sites built with `isMorphismOfSites_comp` — which is stated at
independent universes — available to `AlgebraicGeometry.RingedSite.Hom`, whose site condition
is the small one. -/
public theorem IsMorphismOfSites.toSmallIsMorphismOfSites (h : IsMorphismOfSites.{w} F J K) :
    F.IsMorphismOfSites J K :=
  have := h.toIsContinuous
  { isContinuous := h.toIsContinuous
    preservesFiniteLimits := by
      obtain ⟨L, ⟨adj⟩, hL⟩ := h.hasExactLeftAdjoint
      have := hL
      exact preservesFiniteLimits_of_natIso
        (adj.leftAdjointUniq (F.sheafAdjunctionContinuous (Type w) J K))
    preservesFiniteColimits := Functor.preservesFiniteColimits_sheafPullback F J K }

end Small

end
