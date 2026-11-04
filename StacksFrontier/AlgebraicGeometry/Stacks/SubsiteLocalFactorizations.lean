module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothObject
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.CategoryTheory.Sites.LocalFactorizationCriteria

/-!
# Local factorization through the subsites of an algebraic stack

The inclusion of the smooth objects into the étale site of an algebraic stack `𝒳`, and that of
the flat objects into its fppf site, have local factorizations: every object of `𝒳` is covered
by objects admitting a morphism to an object of the subsite. This is the first of the two
conditions on a subsite in the degree-zero clause of Stacks 07AK.

## Main results

* `AlgebraicGeometry.Stack.flatObject_of_smoothObject`: a smooth object is a flat object.
* `AlgebraicGeometry.Stack.LisseEtale.hasLocalFactorizations_inclusion`: the inclusion of the
  smooth objects has local factorizations for the étale topology of `𝒳`.
* `AlgebraicGeometry.Stack.FlatFppf.hasLocalFactorizations_inclusion`: the inclusion of the flat
  objects has local factorizations for the fppf topology of `𝒳`.

## References

* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The object of `(Sch/U)` given by the identity of `U` is a smooth object. -/
theorem smoothObject_schemeStack_id (U : BigFppfOver B S hS) :
    smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U) (Over.mk (𝟙 U)) := by
  rw [smoothObject_schemeStack_iff]
  change Smooth ((BigFppfOver.toScheme B S hS).map (𝟙 U))
  rw [CategoryTheory.Functor.map_id]
  infer_instance

/-- A smooth object of an algebraic stack is a flat object. -/
theorem flatObject_of_smoothObject (𝒳 : AlgebraicStacks.{u, w} B S hS) {x : 𝒳.val.val.obj}
    (hx : smoothObject.{u, w} B S hS 𝒳 x) : flatObject B S hS 𝒳.val x :=
  (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS _).1
    (AlgebraicStacks.isFlat_of_isSmooth B S hS _ hx)

/-- The smooth object of an algebraic stack named by a smooth 1-morphism from a scheme: the image
of the terminal object of `(Sch/U)` under that 1-morphism. -/
theorem smoothObject_atlas_obj {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (ha : AlgebraicStacks.IsSmooth B S hS a) :
    smoothObject.{u, w} B S hS 𝒳
      ((CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U))) :=
  LisseEtale.smoothObject_map.{u, w} B S hS a ha
    ⟨Over.mk (𝟙 U), smoothObject_schemeStack_id.{u, w} B S hS U⟩

/-- Every object of the étale site of an algebraic stack is covered by one morphism whose source
admits a morphism to a smooth object. -/
private theorem exists_etale_covering_factoring_smoothObject (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (y : 𝒳.val.val.obj) :
    ∃ (Y : 𝒳.val.val.obj) (a : Y ⟶ y),
      Sieve.generate (Presieve.singleton a) ∈
        associatedTopology B S hS 𝒳.val.val.p (etaleTopology B) y ∧
      ∃ (d : 𝒳.val.val.obj) (_ : smoothObject.{u, w} B S hS 𝒳 d), Nonempty (Y ⟶ d) := by
  obtain ⟨U, a, hsmooth, hsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨x, α, hα⟩ := exists_etaleLocalLift B S hS a hsurj hsmooth y
  exact ⟨_, α, hα, _, smoothObject_atlas_obj.{u, w} B S hS a hsmooth,
    ⟨(CatFiberedInGroupoids.homFunctor a.hom).map (Over.homMk x.hom (by simp))⟩⟩

namespace LisseEtale

/-- Every object of the étale site of an algebraic stack is covered by objects admitting a
morphism to a smooth object: condition (1) of Stacks 07AK for the smooth objects. -/
theorem hasLocalFactorizations_inclusion (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Stacks.Sites.HasLocalFactorizations
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι :=
  Stacks.Sites.hasLocalFactorizations_ι_of_exists_singleton_covering_factoring
    (exists_etale_covering_factoring_smoothObject.{u, w} B S hS 𝒳)

end LisseEtale

namespace FlatFppf

/-- Every object of the fppf site of an algebraic stack is covered by objects admitting a
morphism to a flat object: condition (1) of Stacks 07AK for the flat objects. -/
theorem hasLocalFactorizations_inclusion (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Stacks.Sites.HasLocalFactorizations
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (objectProperty B S hS 𝒳).ι := by
  refine Stacks.Sites.hasLocalFactorizations_ι_of_exists_singleton_covering_factoring fun y => ?_
  obtain ⟨Y, a, ha, d, hd, hY⟩ := exists_etale_covering_factoring_smoothObject.{u, w} B S hS 𝒳 y
  exact ⟨Y, a, BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p SiteKind.etale _ ha, d,
    flatObject_of_smoothObject.{u, w} B S hS 𝒳 hd, hY⟩

end FlatFppf

end AlgebraicGeometry.Stack

end
