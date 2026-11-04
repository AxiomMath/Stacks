module

public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCechCovers

/-! # Representable covers of the presheaves represented by algebraic stacks over a stack

Let `𝒳` be an algebraic stack over `S` with its étale or fppf site, and let `𝒳' ⊆ 𝒳` be a full
subcategory satisfying hypothesis (1) of Stacks 07AK. Consider a 1-morphism `z : 𝒯 ⟶ 𝒳` from an
algebraic stack, faithful on the underlying categories, which carries the distinguished object of
every smooth 1-morphism `(Sch/D) ⟶ 𝒯` into `𝒳'`. The presheaf of sets on `𝒳` represented by `z`
is then covered by the representable presheaf of an object of `𝒳'`, namely the image of the
distinguished object of a smooth atlas of `𝒯`, and the fibre powers of that cover are again
represented by 1-morphisms of the same kind, the iterated 2-fibre products of the atlas over `𝒯`
followed by `z`.

So the class of those presheaves is closed under representable covers in the sense of
`Stacks.Sites.CoverDescent.IsClosedUnderRepresentableCovers`, and the descent of
`StacksFrontier/CategoryTheory/Sites/Cohomology/CoverDescent/Cohomology.lean` applies to all of its
members. This generalizes
`AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_smoothOverAtlas`, whose members are the
ones factoring smoothly through a fixed presentation of `𝒳`; the class here
contains, for a smooth (respectively flat) 1-morphism `f : 𝒳 ⟶ 𝒴` and a smooth (respectively
flat) object `y` of `𝒴`, the presheaf represented by `V ×_{y, 𝒴} 𝒳 ⟶ 𝒳`, which is what
Stacks 0GR3 needs.

## Main definitions

* `AlgebraicGeometry.Stack.RepresentedOverSubsite`: the class of presheaves described above.

## Main results

* `AlgebraicGeometry.Stack.exists_cover_componentPresheaf_atlas`: the cover of the presheaf
  represented by a functor, given by a smooth atlas of its source.
* `AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_representedOverSubsite`: the class is
  closed under representable covers by objects of `𝒳'`.

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites.CoverDescent

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The presheaves represented by algebraic stacks over `𝒳` landing in `𝒳'`.** The class of
presheaves of sets on `𝒳` isomorphic to the presheaf of components of the underlying functor of
a 1-morphism `z : 𝒯 ⟶ 𝒳` from an algebraic stack, where that functor is faithful and carries the
distinguished object of every smooth 1-morphism `(Sch/D) ⟶ 𝒯` into `𝒳'`. -/
def RepresentedOverSubsite (𝒳 : AlgebraicStacks.{u, w} B S hS) (P : ObjectProperty 𝒳.val.val.obj)
    (F : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (𝒯 : AlgebraicStacks.{u, w} B S hS) (z : 𝒯 ⟶ 𝒳),
    (CatFiberedInGroupoids.homFunctor z.hom).Faithful ∧
    (∀ {D : BigFppfOver B S hS} (e : schemeStack.{u, w} B S hS D ⟶ 𝒯),
      AlgebraicStacks.IsSmooth B S hS e →
        P ((CatFiberedInGroupoids.homFunctor (e ≫ z).hom).obj (Over.mk (𝟙 D)))) ∧
    Nonempty (F ≅ componentPresheaf (CatFiberedInGroupoids.homFunctor z.hom))

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (τ : SiteKind) (P : ObjectProperty 𝒳.val.val.obj)
  (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ)

include hcl in
/-- **The cover of the presheaf represented by a functor, given by a smooth atlas of its source.**
For `z : 𝒯 ⥤ 𝒳` over the base and faithful, and a smooth surjective `e : (Sch/D) ⟶ 𝒯` whose
distinguished object lands in `𝒳'`, the map from the representable presheaf of that object to the
presheaf represented by `z` is locally surjective, also after restriction to `𝒳'`, and its fibre
powers are represented by the iterated 2-fibre products of `e` followed by `z`. -/
theorem exists_cover_componentPresheaf_atlas {𝒯 : AlgebraicStacks.{u, w} B S hS}
    (z : 𝒯.val.val.obj ⥤ 𝒳.val.val.obj) (hz : z ⋙ 𝒳.val.val.p = 𝒯.val.val.p) [z.Faithful]
    {D : BigFppfOver B S hS} (e : schemeStack.{u, w} B S hS D ⟶ 𝒯)
    (hesm : AlgebraicStacks.IsSmooth B S hS e) (hesurj : IsSurjective B S hS e)
    (hy : P ((CatFiberedInGroupoids.homFunctor e.hom ⋙ z).obj (Over.mk (𝟙 D)))) :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
    ∃ t : uliftYoneda.{u + 1}.obj (P.ι.obj ⟨_, hy⟩) ⟶ componentPresheaf z,
      Presheaf.IsLocallySurjective (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) t ∧
      Presheaf.IsLocallySurjective
        (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))
        (Functor.whiskerLeft P.ι.op t) ∧
      ∀ r : ℕ, Nonempty (tuplePresheaf t (r + 1) ≅ componentPresheaf
        (CatFiberedInGroupoids.homFunctor (cechTower B S hS e (r + 1)).2.hom ⋙ z)) := by
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  have := isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  let E₀ := componentPresheafIsoOfIsTerminal (CatFiberedInGroupoids.homFunctor e.hom ⋙ z)
    (Over.mkIdTerminal (X := D))
  have := isLocallySurjective_componentPresheafMap_atlas τ
    (@generatesCovering_of_isClosedUnderSitePullback B S hS 𝒳 τ P hcl) z hz e hesm hesurj
  let t := E₀.inv ≫ componentPresheafMap z (CatFiberedInGroupoids.homFunctor e.hom) ≫
    (Iso.refl _).hom
  refine ⟨t, inferInstance, Presheaf.isLocallySurjective_whisker
    (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) P.ι t, fun r => ?_⟩
  obtain ⟨E, -⟩ := exists_tuplePresheaf_iso_cechTower z hz e (r + 1)
  exact ⟨tuplePresheafCompIso E₀.symm _ (Iso.refl _) (r + 1) ≪≫ E⟩

include hcl in
/-- **The presheaves represented by algebraic stacks over `𝒳` landing in `𝒳'` are closed under
representable covers by objects of `𝒳'`.** A member represented by `z : 𝒯 ⟶ 𝒳` is covered by the
image of the distinguished object of a smooth surjective atlas `e : (Sch/D) ⟶ 𝒯`, which lies in
`𝒳'` by assumption on `z`; its fibre powers are represented by the iterated 2-fibre products
`D ×_𝒯 ⋯ ×_𝒯 D` followed by `z`, and those are again members: their projections to `𝒯` are
smooth, so the distinguished object of a smooth 1-morphism into them is carried into `𝒳'`, and
their structure functors are faithful. -/
theorem isClosedUnderRepresentableCovers_representedOverSubsite :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
    IsClosedUnderRepresentableCovers.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
      (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)) P.ι
      (RepresentedOverSubsite 𝒳 P) := by
  rintro F ⟨𝒯, z, hzf, hgood, ⟨eF⟩⟩
  have hz : CatFiberedInGroupoids.homFunctor z.hom ⋙ 𝒳.val.val.p = 𝒯.val.val.p := z.hom.hom.w
  obtain ⟨D, e, hesm, hesurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒯
  have : (schemeStack.{u, w} B S hS D).val.val.p.Faithful :=
    inferInstanceAs (Over.forget D).Faithful
  have hy : P ((CatFiberedInGroupoids.homFunctor e.hom ⋙
      CatFiberedInGroupoids.homFunctor z.hom).obj (Over.mk (𝟙 D))) := hgood e hesm
  obtain ⟨t, ht, htK, htup⟩ := exists_cover_componentPresheaf_atlas τ P hcl _ hz e hesm hesurj hy
  refine ⟨⟨_, hy⟩, (Iso.refl _).hom ≫ t ≫ eF.symm.hom, inferInstance, ?_, fun r => ?_⟩
  · rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]
    infer_instance
  · obtain ⟨E⟩ := htup r
    let c := (cechTower B S hS e (r + 1)).2
    have := faithful_cechTower e (r + 1)
    have hcz : CatFiberedInGroupoids.homFunctor (c ≫ z).hom ⋙ 𝒳.val.val.p =
        (cechTower B S hS e (r + 1)).1.val.val.p := (c ≫ z).hom.hom.w
    refine ⟨_, ⟨(cechTower B S hS e (r + 1)).1, c ≫ z, Functor.Faithful.of_comp_eq hcz,
      fun {D'} e' he' => ?_, ⟨Iso.refl _⟩⟩,
      ⟨tuplePresheafCompIso (Iso.refl _) t eF.symm (r + 1) ≪≫ E⟩⟩
    exact hgood (e' ≫ c)
      (AlgebraicStacks.isSmooth_comp B S hS e' c he' (isSmooth_cechTower e hesm (r + 1)))

end AlgebraicGeometry.Stack
