module

public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Grothendieck.FibreInclusionMap
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Morphism

/-!
# The total morphism of topoi of a morphism between simplicial sites

A morphism between simplicial sites in the cocontinuous case is a simplicial family of
cocontinuous functors between the component sites. Applying them degreewise gives a single
functor between the total categories, which is again cocontinuous, and hence induces a morphism
between the total topoi. That morphism commutes with the component morphisms of every simplicial
degree, and its direct image commutes with inverse image to a component.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalFunctor`: the functor between the
  total categories obtained by applying the given functors degreewise.
* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalMorphism`: the induced morphism
  between the total topoi.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalFunctor_isCocontinuous`: the functor
  between the total categories is cocontinuous.
* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalComponentPushforwardIso`: the square
  formed by the total morphism of topoi and the component morphisms of a given simplicial degree
  commutes.
* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalInverseImageRestrictIso`: inverse
  image to a component, applied to the inverse image along the total morphism, is the degreewise
  inverse image applied to inverse image to that component.
* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalPushforwardRestrictIso`: inverse
  image to a component, applied to the direct image along the total morphism, is the degreewise
  direct image applied to inverse image to that component.

## Implementation notes

The functor between the total categories is the one induced on Grothendieck constructions by the
natural transformation of the underlying simplicial diagrams of categories. Its cocontinuity is
reduced to the simplicial degrees: a covering sieve of the image of an object pulls back, along
the component inclusion followed by the total functor, to a covering sieve of that object, and
the component inclusion preserves covering sieves because it is continuous.

The source writes equalities of morphisms of topoi. Since composition of the associated sheaf
functors is only canonical up to isomorphism, the commutative square is expressed by an
isomorphism of direct-image functors; it is the composition comparison of direct images along
cocontinuous functors, applied on both sides of the strict commutation of the underlying site
functors.

The last comparison is not formal: it is a base change for right Kan extensions, and holds
because the square of the component inclusions and the total functor is Guitart exact. Inverse
image along a component inclusion is identified with plain restriction, which is legitimate
because that inclusion is both continuous and cocontinuous, and the comparison is then the base
change of right Kan extensions along the opposite square, transported from presheaves to sheaves
along the fully faithful inclusion of sheaves.

This file treats the cocontinuous case; the continuous case is in
`StacksFrontier/CategoryTheory/Sites/Simplicial/TotalContinuousMorphism.lean`, and the two are
assembled in `StacksFrontier/CategoryTheory/Sites/Simplicial/TotalMorphismOfTopoi.lean`.

## References

* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WD](https://stacks.math.columbia.edu/tag/09WD)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 03L5](https://stacks.math.columbia.edu/tag/03L5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

namespace CocontinuousSimplicialSite.Morphism

variable {C C' : CocontinuousSimplicialSite.{u}}

/-- The functor between the total categories attached to a morphism between simplicial sites in
the cocontinuous case: in each simplicial degree it is the given functor. -/
def totalFunctor (h : CocontinuousSimplicialSite.Morphism C C') :
    Grothendieck C.underlying ⥤ Grothendieck C'.underlying :=
  Grothendieck.map h.hom

/-- The inclusion of the component in simplicial degree `c`, followed by the functor between the
total categories, is the given functor in that degree followed by the inclusion of the component
of the target. -/
theorem ι_comp_totalFunctor (h : CocontinuousSimplicialSite.Morphism C C')
    (c : SimplexCategoryᵒᵖ) :
    Grothendieck.ι C.underlying c ⋙ h.totalFunctor =
      (h.hom.app c).toFunctor ⋙ Grothendieck.ι C'.underlying c :=
  Grothendieck.ι_comp_map h.hom c

/-- The functor between the total categories is cocontinuous for the total topologies. -/
theorem totalFunctor_isCocontinuous (h : CocontinuousSimplicialSite.Morphism C C') :
    h.totalFunctor.IsCocontinuous
      (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) := by
  constructor
  rintro ⟨c, x⟩ S hS
  let _ : (h.hom.app c).toFunctor.IsCocontinuous (topologyOfCoverings (C.coverage c))
      (topologyOfCoverings (C'.coverage c)) := h.isCocontinuous c
  let _ : (Grothendieck.ι C'.underlying c).IsCocontinuous (topologyOfCoverings (C'.coverage c))
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) c.unop
  have hfib : (Grothendieck.ι C.underlying c ⋙ h.totalFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage c))
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) := by
    rw [ι_comp_totalFunctor]
    exact CategoryTheory.isCocontinuous_comp _ _ _ (topologyOfCoverings (C'.coverage c))
  have h1 : Sieve.functorPullback (Grothendieck.ι C.underlying c)
      (Sieve.functorPullback h.totalFunctor S) ∈
      topologyOfCoverings (C.coverage c) x := hfib.cover_lift hS
  have hcont : (Grothendieck.ι C.underlying c).IsContinuous
      (topologyOfCoverings (C.coverage c))
      (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) c.unop
  have hcp := CoverPreserving.of_isContinuous (Grothendieck.ι C.underlying c)
    (topologyOfCoverings (C.coverage c))
    (SimplicialCoverings.totalTopology C.underlying C.coverage)
  exact GrothendieckTopology.superset_covering _
    ((Sieve.functorPushforward_le_iff_le_functorPullback _ _ _).mpr le_rfl) (hcp.cover_preserve h1)

/-- The morphism between the total topoi induced by a morphism between simplicial sites in the
cocontinuous case. -/
@[sga "4 VI 7.4.9" "simplicial case, m_*", stacks 0D96 "case (B), the morphism of total topoi"]
noncomputable def totalMorphism (h : CocontinuousSimplicialSite.Morphism C C') :
    MorphismOfTopoi
      (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u))
      (Sheaf (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u)) := by
  change MorphismOfTopoi
    (Sheaf (SimplicialCoverings.totalTopology C.underlying C.coverage) (Type u))
    (Sheaf (SimplicialCoverings.totalTopology C'.underlying C'.coverage) (Type u))
  letI := h.totalFunctor_isCocontinuous
  exact
    { pushforward := gStar _ _ _ _ h.totalFunctor
      inverseImage := gInv _ _ _ _ h.totalFunctor
      adj := gAdjunction _ _ _ _ h.totalFunctor
      preservesFiniteLimits := main_left_exact _ _ _ _ h.totalFunctor }

/-- The square formed by the total morphism of topoi, the morphism of topoi in simplicial degree
`n`, and the two component morphisms of that degree commutes, as witnessed by a natural
isomorphism of direct-image functors. -/
@[stacks 0D96 "case (B), the commutative square"]
noncomputable def totalComponentPushforwardIso
    (h : CocontinuousSimplicialSite.Morphism C C') (n : SimplexCategory) :
    ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n).pushforward ⋙
        (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).pushforward ≅
      (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).pushforward ⋙
        h.totalMorphism.pushforward := by
  let v := (h.hom.app (Opposite.op n)).toFunctor
  let i := Grothendieck.ι C.underlying (Opposite.op n)
  let i' := Grothendieck.ι C'.underlying (Opposite.op n)
  let Jn := topologyOfCoverings (C.coverage (Opposite.op n))
  let Jn' := topologyOfCoverings (C'.coverage (Opposite.op n))
  let K := SimplicialCoverings.totalTopology C.underlying C.coverage
  let K' := SimplicialCoverings.totalTopology C'.underlying C'.coverage
  letI : v.IsCocontinuous Jn Jn' := h.isCocontinuous (Opposite.op n)
  letI : i.IsCocontinuous Jn K :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
  letI : i'.IsCocontinuous Jn' K' :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
  letI := h.totalFunctor_isCocontinuous
  letI : (v ⋙ i').IsCocontinuous Jn K' := CategoryTheory.isCocontinuous_comp _ _ Jn Jn'
  letI : (i ⋙ h.totalFunctor).IsCocontinuous Jn K' :=
    CategoryTheory.isCocontinuous_comp _ _ Jn K
  change v.sheafPushforwardCocontinuous (Type u) Jn Jn' ⋙
      i'.sheafPushforwardCocontinuous (Type u) Jn' K' ≅
    i.sheafPushforwardCocontinuous (Type u) Jn K ⋙
      h.totalFunctor.sheafPushforwardCocontinuous (Type u) K K'
  exact (sheafPushforwardCocontinuousCompIso Jn Jn' K' v i').symm ≪≫
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} Jn K'
      (h.ι_comp_totalFunctor (Opposite.op n)).symm ≪≫
    sheafPushforwardCocontinuousCompIso Jn K K' i h.totalFunctor

/-- **Stacks 0D96**, case (B). Inverse image to the component of simplicial degree `n`, applied
to the inverse image along the total morphism, is the inverse image in degree `n` applied to the
inverse image to the component of that degree: `h_total^{-1}` is degreewise `h_n^{-1}`.

The two composites of inverse images are the left adjoints of the two composites of direct
images compared by `totalComponentPushforwardIso`, so this is that comparison conjugated by
uniqueness of left adjoints. -/
@[stacks 0D96 "case (B), restriction of the inverse image",
  sga "4 VI 7.4.9" "simplicial, f^{-1}"]
noncomputable def totalInverseImageRestrictIso
    (h : CocontinuousSimplicialSite.Morphism C C') (n : SimplexCategory) :
    h.totalMorphism.inverseImage ⋙
        (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).inverseImage ≅
      (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).inverseImage ⋙
        ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n).inverseImage :=
  (conjugateIsoEquiv
      ((SimplicialSiteSituation.componentMorphism
          (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).adj.comp
        ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n).adj)
      (h.totalMorphism.adj.comp
        (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).adj)).symm
    (h.totalComponentPushforwardIso n)

/-- Inverse image to the component of simplicial degree `n`, applied to the direct image along
the total morphism, is the direct image in degree `n` applied to the inverse image to the
component of that degree. -/
@[sga "4 VI 7.4.9" "simplicial, (7.4.9.2)", stacks 0D96 "case (B), restriction of the direct image"]
noncomputable def totalPushforwardRestrictIso
    (h : CocontinuousSimplicialSite.Morphism C C') (n : SimplexCategory) :
    h.totalMorphism.pushforward ⋙
        (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).inverseImage ≅
      (SimplicialSiteSituation.componentMorphism
          (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).inverseImage ⋙
        ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n).pushforward := by
  let v := (h.hom.app (Opposite.op n)).toFunctor
  let i := Grothendieck.ι C.underlying (Opposite.op n)
  let i' := Grothendieck.ι C'.underlying (Opposite.op n)
  let Jn := topologyOfCoverings (C.coverage (Opposite.op n))
  let Jn' := topologyOfCoverings (C'.coverage (Opposite.op n))
  let K := SimplicialCoverings.totalTopology C.underlying C.coverage
  let K' := SimplicialCoverings.totalTopology C'.underlying C'.coverage
  letI : v.IsCocontinuous Jn Jn' := h.isCocontinuous (Opposite.op n)
  letI : i.IsCocontinuous Jn K :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
  letI : i'.IsCocontinuous Jn' K' :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
  letI : i.IsContinuous Jn K :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
  letI : i'.IsContinuous Jn' K' :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
  letI := h.totalFunctor_isCocontinuous
  let q : TwoSquare i v h.totalFunctor i' :=
    (Grothendieck.ιCompMap h.hom (Opposite.op n)).hom
  letI : q.GuitartExact := Grothendieck.guitartExact_ιCompMap h.hom (Opposite.op n)
  change h.totalFunctor.sheafPushforwardCocontinuous (Type u) K K' ⋙
      i'.sheafPullbackCocontinuous (Type u) Jn' K' ≅
    i.sheafPullbackCocontinuous (Type u) Jn K ⋙ v.sheafPushforwardCocontinuous (Type u) Jn Jn'
  refine Functor.isoWhiskerLeft _
      (i'.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type u) Jn' K') ≪≫ ?_ ≪≫
    Functor.isoWhiskerRight
      (i.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type u) Jn K).symm _
  exact Functor.fullyFaithfulCancelRight (sheafToPresheaf Jn' (Type u))
    (Functor.isoWhiskerLeft (sheafToPresheaf K (Type u))
      (asIso (q.op.ranBaseChange (D := Type u))))

end CocontinuousSimplicialSite.Morphism

end CategoryTheory

end
