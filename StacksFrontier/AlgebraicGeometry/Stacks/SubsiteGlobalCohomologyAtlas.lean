module

public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePrimedFactorizations
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties

/-!
# Global cohomology on the lisse-étale and the flat-fppf site

Parts (1)(a) and (2)(a) of Stacks 0GR0: for an algebraic stack `𝒳` and an abelian sheaf `ℱ` on
`𝒳_étale` (respectively `𝒳_fppf`),

`H^p(𝒳_étale, ℱ) = H^p(𝒳_{lisse,étale}, g⁻¹ℱ)` and `H^p(𝒳_fppf, ℱ) = H^p(𝒳_{flat,fppf}, g⁻¹ℱ)`.

The source proves this by applying Stacks 07AK to the inclusion of the subsite. That is what is
done here: `AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas` is Stacks 07AK for a full
subcategory satisfying its two hypotheses, and both hold for the two subsites with no hypothesis
on the stack. Hypothesis (1), the closure condition, is
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms` and
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`. Hypothesis (2), an object of the
subcategory whose 1-morphism `(Sch/U) ⟶ 𝒳` is smooth and surjective, is
`AlgebraicGeometry.Stack.exists_smooth_surjective_objectMorphism`, proved here.

## Main results

* `AlgebraicGeometry.Stack.exists_smooth_surjective_objectMorphism`: every algebraic stack has an
  object `x` lying over a scheme `U` whose 1-morphism `x : (Sch/U) ⟶ 𝒳` is smooth and surjective.
* `AlgebraicGeometry.Stack.LisseEtale.globalCohomologyIso`: **Stacks 0GR0** (1)(a).
* `AlgebraicGeometry.Stack.FlatFppf.globalCohomologyIso`: **Stacks 0GR0** (2)(a).

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 0GR0](https://stacks.math.columbia.edu/tag/0GR0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A smooth surjective object -/

/-- The 1-morphism `(Sch/U) ⟶ (Sch/U)` named by the identity object `𝟙 U` is surjective: the
morphism of representing presheaves it induces is the Yoneda image of `𝟙 U`. -/
theorem isSurjective_objectMorphism_schemeStack_id (U : BigFppfOver B S hS) :
    IsSurjective B S hS (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS (schemeStack.{u, w} B S hS U).val
          (Functor.Fiber.mk (a := Over.mk (𝟙 U)) rfl)) :
      schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS U) := by
  refine isSurjective_of_isSurjective_representingMap B S hS (yoneda.obj U) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS U)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) _ ?_
  have heq := representingMap_eq_yoneda_map_baseMap B S hS
    (Functor.TwoYoneda.liftBased (Over.forget U)
      (Functor.IsFiberedInGroupoids.over_forget U) (Over.mk (𝟙 U)).left
      (Functor.Fiber.mk (a := Over.mk (𝟙 U)) rfl))
  rw [baseMapOfBasedFunctor_liftBased] at heq
  refine (congrArg (fun f => Space.IsSurjective B S hS f) heq).mpr ?_
  refine Space.isSurjective_yoneda_map B S hS _ ?_
  change Surjective ((BigFppfOver.toScheme B S hS).map (𝟙 U))
  rw [CategoryTheory.Functor.map_id]
  infer_instance

/-- Surjectivity of a 1-morphism out of the category of a scheme is unchanged by first
identifying that scheme with an equal one. -/
theorem isSurjective_of_isSurjective_eqToHom_comp {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {U V : BigFppfOver B S hS} (e : U = V) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (hg : IsSurjective B S hS (Bicategory.InducedBicategory.mkHom
      (Bicategory.InducedBicategory.mkHom (eqToHom (congrArg (fun Z : CatFiberedInGroupoids
          (BigFppfOver B S hS) => Z.val) (congrArg (schemeFibredCategory B S hS) e))) ≫
        g.hom) : schemeStack.{u, w} B S hS U ⟶ 𝒳)) :
    IsSurjective B S hS g := by
  subst e
  intro y
  obtain ⟨z, hz⟩ := hg y
  exact ⟨z, (congrFun (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS
    (Bicategory.InducedBicategory.isoMk (λ_ g.hom)).hom) z).symm.trans hz⟩

/-- **Every algebraic stack has a smooth surjective object.** There is an object `x` of `𝒳`,
lying over a scheme `U`, whose 1-morphism `x : (Sch/U) ⟶ 𝒳` of the 2-Yoneda lemma is smooth and
surjective: the distinguished object of a smooth surjective presentation by a scheme, which is
hypothesis (2) of Stacks 07AK for every full subcategory containing it.

The presentation `a : (Sch/U) ⟶ 𝒳` is the one of `AlgebraicGeometry.Stack.IsAlgebraicStack`; its
distinguished object `x = a(𝟙 U)` is smooth by `AlgebraicGeometry.Stack.smoothObject_map`, and
`x : (Sch/U) ⟶ 𝒳` is 2-isomorphic to the composite of `a` with the 1-morphism named by `𝟙 U`, which
is surjective, by `AlgebraicGeometry.Stack.objectMorphismComp_twoIso`. -/
theorem exists_smooth_surjective_objectMorphism (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    ∃ x : 𝒳.val.val.obj,
      AlgebraicStacks.IsSmooth B S hS (Bicategory.InducedBicategory.mkHom
          (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
            schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳) ∧
        IsSurjective B S hS (Bicategory.InducedBicategory.mkHom
          (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
            schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳) := by
  obtain ⟨U, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  refine ⟨a.hom.hom.toFunctor.obj (Over.mk (𝟙 U)),
    LisseEtale.smoothObject_map.{u, w} B S hS a hasm
      ⟨_, smoothObject_schemeStack_id.{u, w} B S hS U⟩, ?_⟩
  have hcomp := isSurjective_comp B S hS _ a
    (isSurjective_objectMorphism_schemeStack_id.{u, w} B S hS U) hasurj
  refine isSurjective_of_isSurjective_eqToHom_comp B S hS
    (Functor.congr_obj a.hom.hom.w (Over.mk (𝟙 U))).symm _ ?_
  intro y
  obtain ⟨z, hz⟩ := hcomp y
  exact ⟨z, (congrFun (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS
    (Bicategory.InducedBicategory.isoMk
      (objectMorphismComp_twoIso B S hS a (Over.mk (𝟙 U)))).hom) z).symm.trans hz⟩

/-! ### The lisse-étale site -/

namespace LisseEtale

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Hypothesis (1) of Stacks 07AK for the lisse-étale site**, in the form
`AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas` takes it. -/
theorem isClosedUnderSitePullback :
    IsClosedUnderSitePullback B S hS 𝒳.val.val.p (smoothObject.{u, w} B S hS 𝒳) .etale :=
  Or.inl ⟨rfl, fun f hf hy => closedUnderSmoothMorphisms.{u, w} B S hS 𝒳 f hf hy⟩

/-- **Hypothesis (2) of Stacks 07AK for the lisse-étale site**: a smooth object whose 1-morphism
is smooth and surjective. -/
theorem exists_atlas : ∃ x : 𝒳.val.val.obj, smoothObject.{u, w} B S hS 𝒳 x ∧
    AlgebraicStacks.IsSmooth B S hS (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
          schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳) ∧
    IsSurjective B S hS (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
          schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳) :=
  let ⟨x, hsm, hsurj⟩ := exists_smooth_surjective_objectMorphism.{u, w} B S hS 𝒳
  ⟨x, hsm, hsm, hsurj⟩

attribute [local instance] isContinuousInclusion

/-- **Stacks 0GR0, part (1)(a).** For an algebraic stack `𝒳`, every degree `q` and every abelian
sheaf `ℱ` on the étale site of `𝒳`,

`H^q(𝒳_{lisse,étale}, g⁻¹ℱ) ≅ H^q(𝒳_étale, ℱ)`,

naturally in `ℱ`, where `g⁻¹` is restriction to the lisse-étale site of Stacks 0787 — the
inverse image of the morphism of topoi of Stacks 0788, by
`AlgebraicGeometry.Stack.inclusionToposMorphism_inverseImageIso`.

This is Stacks 07AK, `AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas`, for the inclusion of
the smooth objects, with both its hypotheses discharged:
`AlgebraicGeometry.Stack.LisseEtale.isClosedUnderSitePullback` and
`AlgebraicGeometry.Stack.LisseEtale.exists_atlas`. -/
@[stacks 0GR0 "part (1)(a), global cohomology on the lisse-étale site"]
def globalCohomologyIso (q : ℕ) :
    subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳) ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1} (inclusionTopology.{u, w} B S hS 𝒳) q ≅
      Sheaf.functorH.{u + 1, u + 1, u, u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) q :=
  subsiteCohomologyIsoOfAtlas (isClosedUnderSitePullback.{u, w} B S hS 𝒳)
    (exists_atlas.{u, w} B S hS 𝒳) q

end LisseEtale

/-! ### The flat-fppf site -/

namespace FlatFppf

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Hypothesis (1) of Stacks 07AK for the flat-fppf site**, in the form
`AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas` takes it. -/
theorem isClosedUnderSitePullback :
    IsClosedUnderSitePullback B S hS 𝒳.val.val.p (objectProperty B S hS 𝒳) .fppf :=
  Or.inr ⟨rfl, fun f hf hlfp hy => closedUnderFlatMorphisms B S hS 𝒳 f hf hlfp hy⟩

/-- **Hypothesis (2) of Stacks 07AK for the flat-fppf site**: a flat object whose 1-morphism is
smooth and surjective. A smooth object is flat. -/
theorem exists_atlas : ∃ x : 𝒳.val.val.obj, objectProperty B S hS 𝒳 x ∧
    AlgebraicStacks.IsSmooth B S hS (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
          schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳) ∧
    IsSurjective B S hS (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
          schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳) :=
  let ⟨x, hsm, hsurj⟩ := exists_smooth_surjective_objectMorphism.{u, w} B S hS 𝒳
  ⟨x, AlgebraicStacks.isFlat_of_isSmooth B S hS _ hsm, hsm, hsurj⟩

attribute [local instance] isContinuous_inclusion'

/-- **Stacks 0GR0, part (2)(a).** For an algebraic stack `𝒳`, every degree `q` and every abelian
sheaf `ℱ` on the fppf site of `𝒳`,

`H^q(𝒳_{flat,fppf}, g⁻¹ℱ) ≅ H^q(𝒳_fppf, ℱ)`,

naturally in `ℱ`, where `g⁻¹` is restriction to the flat-fppf site of Stacks 0787 — the inverse
image of the morphism of topoi of Stacks 0788, by
`AlgebraicGeometry.Stack.inclusionToposMorphism_inverseImageIso`.

This is Stacks 07AK, `AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas`, for the inclusion of
the flat objects, with both its hypotheses discharged:
`AlgebraicGeometry.Stack.FlatFppf.isClosedUnderSitePullback` and
`AlgebraicGeometry.Stack.FlatFppf.exists_atlas`. -/
@[stacks 0GR0 "part (2)(a), global cohomology on the flat-fppf site"]
def globalCohomologyIso (q : ℕ) :
    subsiteRestriction B S hS 𝒳.val.val.p B.topology (objectProperty B S hS 𝒳) ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1} (inclusionTopology B S hS 𝒳) q ≅
      Sheaf.functorH.{u + 1, u + 1, u, u + 1} (fppfTopology B S hS 𝒳) q :=
  subsiteCohomologyIsoOfAtlas (isClosedUnderSitePullback B S hS 𝒳)
    (exists_atlas.{u, w} B S hS 𝒳) q

end FlatFppf

end AlgebraicGeometry.Stack

end
