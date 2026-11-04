module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSitePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteUnconditional

/-!
# Charts of algebraic spaces under enlarging the big fppf site

Let `B ⊆ B'` be big fppf sites (`AlgebraicGeometry.IsContained`) and let
`G = AlgebraicGeometry.changeBigSite B B' h S hS` be the inverse image of Stacks 04W1, from
algebraic spaces over `S` on `B` to algebraic spaces over `S` on `B'`. This file records how
`G` interacts with the scheme charts of an algebraic space.

* `G` is the restriction of a left exact functor of sheaves, so it carries cartesian squares of
  algebraic spaces to cartesian squares.
* A point of `G X` with values in an object of `B'` whose scheme is small enough for `B` is the
  transport of a point of `X` (Stacks 04W1, the bijection `X(U) ≃ (G X)(U)`).
* A property of the represented base changes of a representable morphism `f` of algebraic
  spaces is reflected by `G`: every represented base change of `f` along a point of the smaller
  site is carried by `G` to a represented base change of `G f` with the same underlying
  morphism of schemes. In particular the transport of a chart is étale, or surjective, only if
  the chart is.

## Main results

* `AlgebraicGeometry.Space.isPullback_changeBigSite_map`: `G` preserves cartesian squares.
* `AlgebraicGeometry.Space.exists_changeBigSiteChart_eq`: small points of `G X` are transported
  points of `X`.
* `AlgebraicGeometry.Space.presheaf_of_presheaf_changeBigSite_map`: `G` reflects the
  properties of represented base changes of representable morphisms.
* `AlgebraicGeometry.Space.presheaf_of_presheaf_changeBigSiteChart`: the same for the charts.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **Enlarging the big fppf site preserves cartesian squares of algebraic spaces.** The inverse
image of sheaves along the inclusion of sites is left exact, and the inclusion of sheaves into
presheaves both preserves and reflects fibre products. -/
theorem isPullback_changeBigSite_map {P X Y Z : AlgebraicSpaces B S hS} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (hpb : IsPullback fst.hom snd.hom f.hom g.hom) :
    IsPullback ((changeBigSite B B' h S hS).map fst).hom ((changeBigSite B B' h S hS).map snd).hom
      ((changeBigSite B B' h S hS).map f).hom ((changeBigSite B B' h S hS).map g).hom := by
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let L := i.sheafPullback (Type u) J K
  let : PreservesFiniteLimits L :=
    inclusionOver_preservesFiniteLimits_sheafPullback B B' h S hS
  let sh : ∀ W : AlgebraicSpaces B S hS, Sheaf J (Type u) := fun W => ⟨W.obj, W.property.isSheaf⟩
  let fstS : sh P ⟶ sh X := ⟨fst.hom⟩
  let sndS : sh P ⟶ sh Y := ⟨snd.hom⟩
  let fS : sh X ⟶ sh Z := ⟨f.hom⟩
  let gS : sh Y ⟶ sh Z := ⟨g.hom⟩
  have hSq : IsPullback fstS sndS fS gS :=
    IsPullback.of_map_of_faithful (F := sheafToPresheaf J (Type u)) hpb
  exact (hSq.map L).map (sheafToPresheaf K (Type u))

/-- **Small points of the enlarged space are transported points.** A morphism `v : V ⟶ G X` from
an object of the larger site whose scheme lies below the cutoff of the smaller one is, up to the
identification of `V` with an object of the smaller site, the transport of a point of `X`
(Stacks 04W1). -/
theorem exists_changeBigSiteChart_eq {X : AlgebraicSpaces B S hS}
    {V : BigFppfOver B' S (largerContains h hS)}
    (hV : ((BigFppfOver.toScheme B' S (largerContains h hS)).obj V).size < B.cutoff)
    (v : yoneda.obj V ⟶ ((changeBigSite B B' h S hS).obj X).obj) :
    ∃ (T : BigFppfOver B S hS) (e : (inclusionOver h S hS).obj T ≅ V)
      (g : yoneda.obj T ⟶ X.obj),
      yoneda.map e.hom ≫ v = (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk g)).hom := by
  let T : BigFppfOver B S hS := BigFppfOver.mk B S hS hV (B'.inclusion.map V.hom)
  let x : X.obj.obj (op T) := (changeBigSiteSectionEquiv B B' h S hS X T).symm (yonedaEquiv v)
  refine ⟨T, Iso.refl _, yonedaEquiv.symm x, ?_⟩
  apply yonedaEquiv.injective
  refine Eq.trans ?_
    (chartElement_changeBigSiteChart B B' h S hS X (CostructuredArrow.mk _)).symm
  change yonedaEquiv (𝟙 _ ≫ v) = changeBigSiteSectionEquiv B B' h S hS X T
    (yonedaEquiv (yonedaEquiv.symm x))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.id_comp]
  rfl

/-- **Enlarging the big fppf site reflects the properties of represented base changes.** Let
`f : X ⟶ Y` be a representable morphism of algebraic spaces over `S` on the smaller site. If
every represented base change of `G f` has a property `P` of morphisms of schemes, then so does
every represented base change of `f`: a represented base change of `f` along a point of `Y` is
carried by `G` to the represented base change of `G f` along the transported point, which has
the same underlying morphism of schemes. -/
theorem presheaf_of_presheaf_changeBigSite_map (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (h' : MorphismProperty.presheaf (P.inverseImage
      (BigFppfOver.toScheme B' S (largerContains h hS))) ((changeBigSite B B' h S hS).map f).hom) :
    MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS)) f.hom :=
  ⟨hf, fun _ _ g fst snd hpb =>
    h'.property _ _ _ (isPullback_changeBigSiteChart B B' h S hS f fst snd g hpb)⟩

/-- **Enlarging the big fppf site reflects the properties of represented base changes of
charts.** If the transport of a chart `g : T ⟶ X` has every represented base change with a
property `P` of morphisms of schemes, then so has `g`. In particular a chart is étale, or
surjective, as soon as its transport is. -/
theorem presheaf_of_presheaf_changeBigSiteChart (P : MorphismProperty Scheme.{u})
    {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X.obj)
    (h' : MorphismProperty.presheaf (P.inverseImage
      (BigFppfOver.toScheme B' S (largerContains h hS)))
      (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk g)).hom) :
    MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS)) g := by
  let φ : (schemeSpaceFunctor B S hS).obj T ⟶ X :=
    ObjectProperty.homMk (P := fun F => IsAlgebraicSpace B S hS F) g
  have hφ : MorphismProperty.presheaf (P.inverseImage
      (BigFppfOver.toScheme B' S (largerContains h hS)))
        ((changeBigSite B B' h S hS).map φ).hom := by
    rw [changeBigSiteChart_hom, ← changeBigSiteYonedaIso_hom] at h'
    let Q := (P.inverseImage (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf
    have : Q.RespectsIso := MorphismProperty.relative_respectsIso _
    refine (Q.arrow_mk_iso_iff (Arrow.isoMk (changeBigSiteYonedaIso B B' h S hS T)
      (Iso.refl _) ?_)).mp h'
    rfl
  exact presheaf_of_presheaf_changeBigSite_map B B' h S hS P φ
    (X.property.diagonal_representable.of_diag g) hφ

end AlgebraicGeometry.Space

end
