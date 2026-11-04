module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteSmallEtale

/-!
# Representable base changes after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'` and let `f : Y ⟶ X` be a morphism of
algebraic spaces over `S` defined using `B`. A cartesian square

```
P ⟶ Y
↓     ↓ f
T ⟶ X
```

with `P` and `T` objects of `B` stays cartesian after enlarging the site: transporting its two
points of `Y` and `X` along the bijections `Y(P) ≃ Y'(P)` and `X(T) ≃ X'(T)` of Stacks 04W1 gives
a cartesian square over `f' : Y' ⟶ X'` with the same morphism of schemes `P ⟶ T`. This is what
makes the representable base changes of `f` the representable base changes of `f'` at the
objects of `B`.

## Main results

* `AlgebraicGeometry.changeBigSiteYonedaHom_naturality`: the comparison of Stacks 03FP, part (1)
  is natural in the test object.
* `AlgebraicGeometry.Space.isPullback_changeBigSiteChart`: the transport of a cartesian square.

## Implementation notes

The square is pushed through the inverse image on sheaves of sets, which preserves finite limits
(`AlgebraicGeometry.inclusionOver_preservesFiniteLimits_sheafPullback`), and then rewritten
along the comparison of Stacks 03FP, part (1) at its two representable corners. The transported
points are the composites of that comparison with the images of the given points
(`AlgebraicGeometry.Space.changeBigSiteChart_hom`), and its naturality takes care of the edge
`P ⟶ T`.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **The comparison of Stacks 03FP, part (1) is natural in the test object.** -/
theorem changeBigSiteYonedaHom_naturality {W T : BigFppfOver B S hS} (d : W ⟶ T) :
    yoneda.map ((inclusionOver h S hS).map d) ≫ changeBigSiteYonedaHom B B' h S hS T =
      changeBigSiteYonedaHom B B' h S hS W ≫
        ((changeBigSite B B' h S hS).map ((schemeSpaceFunctor B S hS).map d)).hom := by
  apply yonedaEquiv.injective
  refine (yonedaEquiv_naturality _ _).symm.trans ?_
  refine Eq.trans ?_ (yonedaEquiv_comp _ _).symm
  have h1 : ∀ U, yonedaEquiv (changeBigSiteYonedaHom B B' h S hS U) =
      changeBigSiteSectionEquiv B B' h S hS ((schemeSpaceFunctor B S hS).obj U) U (𝟙 U) :=
    fun _ => yonedaEquiv.apply_symm_apply _
  refine (congrArg (((changeBigSite B B' h S hS).obj
    ((schemeSpaceFunctor B S hS).obj T)).obj.map ((inclusionOver h S hS).map d).op) (h1 T)).trans ?_
  refine Eq.trans ?_ (congrArg (((changeBigSite B B' h S hS).map
    ((schemeSpaceFunctor B S hS).map d)).hom.app (op ((inclusionOver h S hS).obj W))) (h1 W)).symm
  refine (changeBigSiteSectionEquiv_restrict B B' h S hS ((schemeSpaceFunctor B S hS).obj T) d
    (𝟙 T)).symm.trans ?_
  refine Eq.trans ?_ (changeBigSiteSectionEquiv_map B B' h S hS
    ((schemeSpaceFunctor B S hS).map d) W (𝟙 W))
  congr 1

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **A cartesian square over a morphism of algebraic spaces, with representable corners, stays
cartesian after enlarging the big fppf site.** -/
theorem isPullback_changeBigSiteChart {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {P T : BigFppfOver B S hS} (fst : yoneda.obj P ⟶ X.obj) (snd : P ⟶ T)
    (g : yoneda.obj T ⟶ Y.obj) (hpb : IsPullback fst (yoneda.map snd) f.hom g) :
    IsPullback (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk fst)).hom
      (yoneda.map ((inclusionOver h S hS).map snd)) ((changeBigSite B B' h S hS).map f).hom
      (changeBigSiteChart B B' h S hS Y (CostructuredArrow.mk g)).hom := by
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : HasSheafify J (Type u) := hasSheafify_overTopology B S hS
  let : HasSheafify K (Type u) := hasSheafify_overTopology B' S hS'
  let : J.Subcanonical := subcanonical_overTopology B S hS
  let : K.Subcanonical := subcanonical_overTopology B' S hS'
  let L := i.sheafPullback (Type u) J K
  let : PreservesFiniteLimits L :=
    inclusionOver_preservesFiniteLimits_sheafPullback B B' h S hS
  let PX : Sheaf J (Type u) := ⟨X.obj, X.property.isSheaf⟩
  let PY : Sheaf J (Type u) := ⟨Y.obj, Y.property.isSheaf⟩
  let fS : PX ⟶ PY := ⟨f.hom⟩
  let fstS : J.yoneda.obj P ⟶ PX := ⟨fst⟩
  let gS : J.yoneda.obj T ⟶ PY := ⟨g⟩
  have hSq : IsPullback fstS (J.yoneda.map snd) fS gS :=
    IsPullback.of_map_of_faithful (F := sheafToPresheaf J (Type u)) hpb
  have hL := (hSq.map L).map (sheafToPresheaf K (Type u))
  refine hL.of_iso' (changeBigSiteYonedaIso B B' h S hS P) (Iso.refl _)
    (changeBigSiteYonedaIso B B' h S hS T) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (changeBigSiteChart_hom B B' h S hS X (CostructuredArrow.mk fst)).symm.trans
      (Category.comp_id _).symm
  · exact (changeBigSiteYonedaHom_naturality B B' h S hS snd).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (changeBigSiteChart_hom B B' h S hS Y (CostructuredArrow.mk g)).symm.trans
      (Category.comp_id _).symm

end AlgebraicGeometry.Space

end
