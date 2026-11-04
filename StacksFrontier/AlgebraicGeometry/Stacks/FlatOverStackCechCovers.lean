module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFlatSubsiteCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCechCovers

/-!
# Representable covers by flat objects of the presheaves represented by flat 1-morphisms

Let `𝒳` be an algebraic stack over `S` with its fppf site, and let `𝒳_flat ⊆ 𝒳` be the full
subcategory of flat objects (**Stacks 0787**). A flat 1-morphism `z : 𝒯 ⟶ 𝒳` from an algebraic
stack with faithful underlying functor represents a presheaf of sets `Ψ(z)` on `𝒳`, its presheaf of
components (`Stacks.Sites.CoverDescent.componentPresheaf`); only the faithfulness of the
underlying functor of `z` matters, which holds for the projection `(Sch/V) ×_𝒴 𝒳 ⟶ 𝒳` of a
2-fibre product with a scheme even when `𝒯` has automorphisms. This file proves that the class of
these presheaves is closed under representable covers by flat objects of `𝒳`, in the sense of
`Stacks.Sites.CoverDescent.IsClosedUnderRepresentableCovers`: a smooth surjective atlas
`e : (Sch/D) ⟶ 𝒯` gives the cover `h_y ⟶ Ψ(z)`, where `y` is the image under `z ∘ e` of the
identity of `D`, which is a flat object because `z ∘ e` is flat; and the fibre powers of that cover
are represented by the iterated 2-fibre products `D ×_𝒯 ⋯ ×_𝒯 D`, flat over `𝒳` through their
projections to `𝒯` followed by `z`.

This is the flat counterpart of
`AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_smoothOverAtlas`, and it is the
geometric input with which the descent of
`StacksFrontier/CategoryTheory/Sites/Cohomology/CoverDescent/Cohomology.lean` compares `Ext` out of
`ℤ_{Ψ(z)}` on `𝒳_fppf` with `Ext` out of its restriction on the flat-fppf site — the step of the
proof of **Stacks 0775** (2) which identifies the cohomology of the 2-fibre product
`(Sch/V) ×_𝒴 𝒳` with that of its restriction to flat objects.

## Main definitions

* `AlgebraicGeometry.Stack.FlatOverStack`: the presheaves on `𝒳` represented by flat
  1-morphisms with faithful underlying functor.

## Main results

* `AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_flatOverStack`: the closure of
  `AlgebraicGeometry.Stack.FlatOverStack` under representable covers by flat objects.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites.CoverDescent

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The presheaves represented by flat 1-morphisms.** The class of presheaves of sets on `𝒳`
consisting of the presheaves of components `Ψ(z)` of the flat 1-morphisms `z : 𝒯 ⟶ 𝒳` of
algebraic stacks whose underlying functor is faithful. -/
def FlatOverStack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (F : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (𝒯 : AlgebraicStacks.{u, w} B S hS) (z : 𝒯 ⟶ 𝒳),
    (CatFiberedInGroupoids.homFunctor z.hom).Faithful ∧ AlgebraicStacks.IsFlat B S hS z ∧
      F = componentPresheaf (CatFiberedInGroupoids.homFunctor z.hom)

/-- **The image of the identity of `D` under a flat 1-morphism out of `(Sch/D)` is a flat
object.** -/
lemma flatObject_atlasObj {𝒳 : AlgebraicStacks.{u, w} B S hS} {D : BigFppfOver B S hS}
    (g : schemeStack.{u, w} B S hS D ⟶ 𝒳) (hg : AlgebraicStacks.IsFlat B S hS g) :
    flatObject B S hS 𝒳.val
      ((CatFiberedInGroupoids.homFunctor g.hom).obj (Over.mk (𝟙 D))) :=
  FlatFppf.flatObject_map B S hS g hg ⟨Over.mk (𝟙 D), flatObject_schemeStack_id.{u, w} B S hS D⟩

/-- **The presheaves represented by flat 1-morphisms are closed under representable covers by
flat objects.** Every member `Ψ(z)` of `AlgebraicGeometry.Stack.FlatOverStack` receives a locally
surjective map from the representable presheaf of a flat object of `𝒳`, locally surjective also
after restriction to the flat objects, whose fibre powers are again members: the cover is given by
the image `y` of the distinguished object of a smooth surjective atlas `e : (Sch/D) ⟶ 𝒯`, flat
because `z ∘ e` is (**Stacks 06PX**), and its fibre powers are represented by the iterated
2-fibre products `D ×_𝒯 ⋯ ×_𝒯 D`, flat over `𝒳` through their projections to `𝒯` followed by
`z`. The local surjectivity is **Stacks 06XH** for the atlas. -/
theorem isClosedUnderRepresentableCovers_flatOverStack (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p (FlatFppf.objectProperty B S hS 𝒳) .fppf 𝒳.val.isFiberedInGroupoids
      (isClosedUnderSitePullback_flatObject 𝒳 (τ := .fppf) (Or.inr rfl))
    IsClosedUnderRepresentableCovers.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      ((FlatFppf.objectProperty B S hS 𝒳).ι.inheritedTopology
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf))
      (FlatFppf.objectProperty B S hS 𝒳).ι (FlatOverStack 𝒳) := by
  have hcl := isClosedUnderSitePullback_flatObject 𝒳 (τ := .fppf) (Or.inr rfl)
  let P := FlatFppf.objectProperty B S hS 𝒳
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P .fppf 𝒳.val.isFiberedInGroupoids hcl
  have := isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P .fppf 𝒳.val.isFiberedInGroupoids hcl
  have hgen := @generatesCovering_of_isClosedUnderSitePullback B S hS 𝒳 .fppf P hcl
  have hfaithD : ∀ D : BigFppfOver B S hS, (schemeStack.{u, w} B S hS D).val.val.p.Faithful :=
    fun D => inferInstanceAs (Over.forget D).Faithful
  intro F hF
  obtain ⟨𝒯, q, hfaith, hq, rfl⟩ := hF
  have hz : CatFiberedInGroupoids.homFunctor q.hom ⋙ 𝒳.val.val.p = 𝒯.val.val.p := q.hom.hom.w
  obtain ⟨D, e, hesm, hesurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒯
  have := hfaithD D
  have hy : P ((CatFiberedInGroupoids.homFunctor e.hom ⋙
      CatFiberedInGroupoids.homFunctor q.hom).obj (Over.mk (𝟙 D))) :=
    flatObject_atlasObj (e ≫ q) (AlgebraicStacks.isFlat_comp B S hS e q
      (AlgebraicStacks.isFlat_of_isSmooth B S hS e hesm) hq)
  let E₀ := componentPresheafIsoOfIsTerminal
    (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor q.hom)
    (Over.mkIdTerminal (X := D))
  have := isLocallySurjective_componentPresheafMap_atlas .fppf hgen
    (CatFiberedInGroupoids.homFunctor q.hom) hz e hesm hesurj
  let t := E₀.inv ≫ componentPresheafMap (CatFiberedInGroupoids.homFunctor q.hom)
    (CatFiberedInGroupoids.homFunctor e.hom) ≫ (Iso.refl _).hom
  have ht : Presheaf.IsLocallySurjective
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) t := inferInstance
  refine ⟨⟨_, hy⟩, t, ht, Presheaf.isLocallySurjective_whisker
    (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf))
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) P.ι t, fun r => ?_⟩
  obtain ⟨E, -⟩ := exists_tuplePresheaf_iso_cechTower (CatFiberedInGroupoids.homFunctor q.hom)
    hz e (r + 1)
  have := faithful_cechTower e (r + 1)
  have : (CatFiberedInGroupoids.homFunctor (cechTower B S hS e (r + 1)).2.hom).Faithful :=
    Functor.Faithful.of_comp_eq (cechTower B S hS e (r + 1)).2.hom.hom.w
  refine ⟨_, ⟨(cechTower B S hS e (r + 1)).1, (cechTower B S hS e (r + 1)).2 ≫ q,
    inferInstanceAs (CatFiberedInGroupoids.homFunctor (cechTower B S hS e (r + 1)).2.hom ⋙
      CatFiberedInGroupoids.homFunctor q.hom).Faithful,
    AlgebraicStacks.isFlat_comp B S hS _ q
      (AlgebraicStacks.isFlat_of_isSmooth B S hS _ (isSmooth_cechTower e hesm (r + 1))) hq,
    rfl⟩, ⟨tuplePresheafCompIso E₀.symm _ (Iso.refl _) (r + 1) ≪≫ E⟩⟩

end AlgebraicGeometry.Stack

end
