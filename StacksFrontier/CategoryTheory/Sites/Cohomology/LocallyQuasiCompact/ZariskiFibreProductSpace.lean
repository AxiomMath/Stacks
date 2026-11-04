module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonNaturality

/-!
# The space of a fibre product of the locally quasi-compact Zariski site

The inclusion of the locally quasi-compact Zariski site into `TopCat` creates fibre products:
the bounded subcategory is closed under countable limits, and `LC` itself is closed under fibre
products in `TopCat`. Consequently the space underlying a fibre product `Z ×_Y X` of the site is
the topological fibre product, which Mathlib writes as the subspace
`Function.Pullback g f = {p : Z × X // g p.1 = f p.2}` of the product.

This identification is what connects statements about the site's fibre products — the fibre
products appearing in clause (7) of Stacks 0DCU, and in `Over.pullback` generally — with
statements about topological fibre products, in particular with the notion of a universally
closed map of Stacks 005O (4), which is phrased with `Function.Pullback`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiPullbackTopIso`: the inclusion
  into `TopCat` carries a fibre product of the site to the fibre product in `TopCat`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiPullbackHomeo`: the resulting
  homeomorphism of the space of `Z ×_Y X` with `Function.Pullback g f`.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.overPullback_obj_left` and
  `overPullback_obj_hom`: the object `Over.pullback f` produces from `g : Z ⟶ Y` is `Z ×_Y X`
  with its second projection as structure morphism.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiPullbackTopIso_hom_fst` and
  `zariskiPullbackTopIso_hom_snd`: the identification is compatible with the two projections.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiPullbackHomeo_fst` and
  `zariskiPullbackHomeo_snd`: the homeomorphism takes a point of `Z ×_Y X` to the pair of its
  two projections, so it carries `pullback.fst` and `pullback.snd` to `Function.Pullback.fst`
  and `Function.Pullback.snd`.

## Implementation notes

`zariskiPullbackTopIso` is built exactly as in the proof of
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.pullback_openEmbedding_range`: the
creation of fibre products by the inclusion of the bounded subcategory,
`boundedSiteInclusionCreatesPullbacks`, is transported through the inclusion of `LC` into
`TopCat`, and the resulting preservation isomorphism is composed with the comparison
`CategoryTheory.Limits.cospanCompIso` of the two cospans. Mathlib's
`TopCat.pullbackIsoProdSubtype` then replaces the categorical fibre product of `TopCat` by the
subspace of the product.

`boundedSiteInclusionCreatesPullbacks` is made a local instance so that the body of
`zariskiPullbackTopIso` stays a plain composite of two isomorphisms, which is what lets the two
projection lemmas be proved by rewriting with the standard compatibilities of
`CategoryTheory.Limits.preservesLimitIso` and `CategoryTheory.Limits.HasLimit.isoOfNatIso`.
With those in hand the two statements about `zariskiPullbackHomeo` hold by unfolding, because
`TopCat.pullbackIsoProdSubtype` takes a point of the categorical fibre product to the pair of
its projections by definition.

## References

* [Stacks Project, Tag 09WZ](https://stacks.math.columbia.edu/tag/09WZ)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 005O](https://stacks.math.columbia.edu/tag/005O)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w

attribute [local instance] boundedSiteInclusionCreatesPullbacks

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y Z : S.category}
  (f : X ⟶ Y) (g : Z ⟶ Y)

/-- The object of `LC_Zar/X` that `Over.pullback f` produces from `g : Z ⟶ Y` is the fibre
product `Z ×_Y X`: this is the `Z'` of the proof of clause (7) of Stacks 0DCU. -/
@[simp]
theorem overPullback_obj_left :
    ((Over.pullback f).obj (Over.mk g)).left = pullback g f := rfl

/-- The structure morphism of `Z ×_Y X` over `X` is the second projection (Stacks 0DCU, clause
(7)). -/
@[simp]
theorem overPullback_obj_hom :
    ((Over.pullback f).obj (Over.mk g)).hom = pullback.snd g f := rfl

/-- The inclusion of the Zariski site into `TopCat` carries a fibre product of the site to the
fibre product in `TopCat`, because it creates fibre products. -/
def zariskiPullbackTopIso :
    (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj (pullback g f) ≅
      pullback ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map g)
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) :=
  (preservesLimitIso (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop)
      (cospan g f)).trans
    (HasLimit.isoOfNatIso
      (cospanCompIso (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop) g f))

/-- The identification of the space of a fibre product of the site with the topological fibre
product is compatible with the first projection. -/
theorem zariskiPullbackTopIso_hom_fst :
    (zariskiPullbackTopIso S f g).hom ≫
        pullback.fst ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map g)
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) =
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map (pullback.fst g f) := by
  simp [zariskiPullbackTopIso]

/-- The identification of the space of a fibre product of the site with the topological fibre
product is compatible with the second projection. -/
theorem zariskiPullbackTopIso_hom_snd :
    (zariskiPullbackTopIso S f g).hom ≫
        pullback.snd ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map g)
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) =
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map (pullback.snd g f) := by
  simp [zariskiPullbackTopIso]

/-- **The space of a fibre product of the Zariski site is the topological fibre product.** The
space underlying `Z ×_Y X` is homeomorphic to `Function.Pullback g f`, the subspace of
`Z × X` cut out by `g p.1 = f p.2`. -/
def zariskiPullbackHomeo :
    (pullback g f).obj ≃ₜ Function.Pullback (g : Z.obj → Y.obj) (f : X.obj → Y.obj) :=
  TopCat.homeoOfIso ((zariskiPullbackTopIso S f g).trans
    (TopCat.pullbackIsoProdSubtype _ _))

/-- The homeomorphism of the space of `Z ×_Y X` with `Function.Pullback g f` takes a point to
its first projection in the first coordinate. -/
theorem zariskiPullbackHomeo_fst (p : (pullback g f).obj) :
    Function.Pullback.fst (zariskiPullbackHomeo S f g p) =
      (pullback.fst g f : (pullback g f).obj → Z.obj) p :=
  ConcreteCategory.congr_hom (zariskiPullbackTopIso_hom_fst S f g) p

/-- The homeomorphism of the space of `Z ×_Y X` with `Function.Pullback g f` takes a point to
its second projection in the second coordinate. -/
theorem zariskiPullbackHomeo_snd (p : (pullback g f).obj) :
    Function.Pullback.snd (zariskiPullbackHomeo S f g p) =
      (pullback.snd g f : (pullback g f).obj → X.obj) p :=
  ConcreteCategory.congr_hom (zariskiPullbackTopIso_hom_snd S f g) p

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
