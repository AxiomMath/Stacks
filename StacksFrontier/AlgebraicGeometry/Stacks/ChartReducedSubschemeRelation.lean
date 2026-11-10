module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartReducedSubschemeInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothProjections

/-!
# The reduced subscheme of a smooth chart is invariant under the relation of the chart

Let `a : U ⟶ 𝒳` be a smooth 1-morphism, representable by algebraic spaces, from the algebraic
stack of a scheme `U` of the big fppf site of `S` to an algebraic stack `𝒳`, and let `T` be a
closed set of points of `𝒳`. Let `Z ⊆ U` be the reduced induced closed subscheme on the part of
`U` lying over `T` (`AlgebraicGeometry.Stack.chartReducedSubscheme`).

On a scheme chart `R` of the relation `U ×_𝒳 U` (Stacks 04T4 (1)), whose two legs are smooth
(Stacks 04T5 (1)), the two pullbacks of `Z` are reduced with the same support, hence equal
(`AlgebraicGeometry.Stack.exists_relationChart`,
`AlgebraicGeometry.Stack.pullback_subobject_chartReducedSubscheme_eq_of_pointsMap_eq`). Every
pair of morphisms to `U` whose images in `𝒳` are joined by a morphism over the identity lifts
étale locally to `R`, so membership of `Z` is transported along such a pair.

## Main results

* `AlgebraicGeometry.Stack.exists_relationChart`: a scheme chart of the relation `U ×_𝒳 U`
  with smooth legs.
* `AlgebraicGeometry.Stack.mem_chartReducedSubscheme_of_hom`: membership of `Z` is transported
  along pairs of morphisms to `U` with isomorphic images in `𝒳`.
* `AlgebraicGeometry.Stack.exists_isHomLift_id_comp_eq`: two morphisms of a category fibred in
  groupoids into one object over one base morphism differ by a morphism over the identity.

## References

* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A section of a presheaf with a surjective étale scheme atlas lifts to the atlas after a
surjective étale morphism, compatibly with the preimages of any two morphisms to a
representable. -/
private theorem exists_lift_atlas {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U W : BigFppfOver B S hS}
    {atl : yoneda.obj R ⟶ F}
    (hatls : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) atl)
    (hatle : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) atl)
    (ρ : F.obj (op W)) (τ σ : F ⟶ yoneda.obj U) {h h' : W ⟶ U} (hτ : τ.app (op W) ρ = h)
    (hσ : σ.app (op W) ρ = h') :
    ∃ (W' : BigFppfOver B S hS) (m : W' ⟶ W) (c : W' ⟶ R),
      Surjective ((BigFppfOver.toScheme B S hS).map m) ∧
      Etale ((BigFppfOver.toScheme B S hS).map m) ∧
      c ≫ yoneda.preimage (atl ≫ τ) = m ≫ h ∧ c ≫ yoneda.preimage (atl ≫ σ) = m ≫ h' := by
  set k₀ : yoneda.obj W ⟶ F := yonedaEquiv.symm ρ with hk₀
  have hsq := hatls.rep.isPullback k₀
  have hlegs : ∀ (σ : F ⟶ yoneda.obj U) (hh : W ⟶ U), σ.app (op W) ρ = hh →
      yoneda.preimage (hatls.rep.fst k₀) ≫ yoneda.preimage (atl ≫ σ) =
        hatls.rep.snd k₀ ≫ hh := by
    intro σ hh hσ
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, Functor.map_preimage,
      ← Category.assoc, hsq.w, Category.assoc]
    congr 1
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, hk₀, Equiv.apply_symm_apply, hσ]
  exact ⟨hatls.rep.pullback k₀, hatls.rep.snd k₀, yoneda.preimage (hatls.rep.fst k₀),
    hatls.property_snd k₀, hatle.property k₀ _ _ hsq, hlegs τ h hτ, hlegs σ h' hσ⟩

/-- The preimage under Yoneda of an étale scheme atlas of an algebraic space followed by a smooth
morphism to a representable is smooth. -/
private theorem smooth_preimage_atlas_comp {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {R U : BigFppfOver B S hS} {atl : yoneda.obj R ⟶ F}
    (hatle : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) atl)
    {σ : F ⟶ yoneda.obj U} (hσ : Space.IsSmooth B S hS σ) :
    Smooth ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (atl ≫ σ))) := by
  refine Space.smooth_of_isSmooth_yonedaMap B S hS _ ?_
  rw [Functor.map_preimage]
  exact Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS R) hF
    (isAlgebraicSpace_yoneda B S hS U) atl _
    (Space.isSmooth_of_isEtale B S hS hF
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS atl).2 hatle)) hσ

/-! ### Charts of the relation of a smooth chart -/

section Relation

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
  (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  (hrep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom)
  (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
    a.hom hrep)

/-- A section of a chart of the relation `U ×_𝒳 U` of `a` gives a morphism of `𝒳` from the image
under `a` of its source to the image under `a` of its target. -/
private theorem nonempty_hom_relationSourceMap_relationTargetMap
    {Rp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hRp : IsAlgebraicSpace B S hS Rp)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeFibredCategory B S hS U) 𝒳.val a.hom.hom).val.p
      (presheafOfCategories (Rp ⋙ typeToCat)).p)
    {W : BigFppfOver B S hS} (ρ : Rp.obj (op W)) :
    Nonempty (a.hom.hom.toFunctor.obj (Over.mk ((SelfIntersection.relationSourceMap
        (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩)
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR).app (op W) ρ)) ⟶
      a.hom.hom.toFunctor.obj (Over.mk ((SelfIntersection.relationTargetMap
        (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩)
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR).app (op W) ρ))) := by
  let eU : StacksRepresentableCFG.EquivalenceOver (schemeFibredCategory B S hS U).val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver U
  set src := SelfIntersection.relationSourceMap
    (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩) eU eR
  set tgt := SelfIntersection.relationTargetMap
    (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩) eU eR
  obtain ⟨r, hr, hρ⟩ := PresheafOfCategories.exists_sectionOfObj eR ρ
  have hy : PresheafOfCategories.sectionOfObj eU r.y (SelfIntersection.relation_obj_y hr) =
      PresheafOfCategories.sectionOfObj eU (Over.mk (src.app (op W) ρ))
        (rfl : (Over.forget U).obj (Over.mk (src.app (op W) ρ)) = W) := by
    rw [← hρ]
    exact (SelfIntersection.relationSourceMap_sectionOfObj
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩) eU eR r hr).symm
  have hx : PresheafOfCategories.sectionOfObj eU r.x (SelfIntersection.relation_obj_x hr) =
      PresheafOfCategories.sectionOfObj eU (Over.mk (tgt.app (op W) ρ))
        (rfl : (Over.forget U).obj (Over.mk (tgt.app (op W) ρ)) = W) := by
    rw [← hρ]
    exact (SelfIntersection.relationTargetMap_sectionOfObj
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩) eU eR r hr).symm
  exact ⟨a.hom.hom.toFunctor.map (Functor.Fiber.fiberInclusion.map
      (PresheafOfCategories.fiberIsoOfSectionOfObj_eq eU _ _ hy).inv) ≫ r.iso.inv ≫
    a.hom.hom.toFunctor.map (Functor.Fiber.fiberInclusion.map
      (PresheafOfCategories.fiberIsoOfSectionOfObj_eq eU _ _ hx).hom)⟩

include hrep hsmooth in
/-- **A scheme chart of the relation `U ×_𝒳 U` of a smooth chart.** Let `a : U ⟶ 𝒳` be a smooth
1-morphism from the algebraic stack of a scheme of the site, representable by algebraic spaces.
There is an object `R` of the site with two smooth morphisms `s, t : R ⟶ U` such that

* at every object of the site over `R` the two composites of `a` with `s` and with `t` are joined
  by a morphism of `𝒳`, and
* every pair `h, h' : W ⟶ U` whose images under `a` are joined by a morphism over the identity of
  `W` is, after a surjective étale morphism `m : W' ⟶ W`, the pair of composites of `s` and `t`
  with a morphism `W' ⟶ R`.

`R` is a scheme atlas of the algebraic space representing the self-intersection `U ×_𝒳 U`
(**Stacks 04T4 (1)**), and the two legs are smooth by **Stacks 04T5 (1)**. -/
theorem exists_relationChart :
    ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
      Smooth ((BigFppfOver.toScheme B S hS).map s) ∧
      Smooth ((BigFppfOver.toScheme B S hS).map t) ∧
      (∀ x : (schemeFibredCategory B S hS R).val.obj,
        Nonempty (a.hom.hom.toFunctor.obj ((Over.map s).obj x) ⟶
          a.hom.hom.toFunctor.obj ((Over.map t).obj x))) ∧
      ∀ (W : BigFppfOver B S hS) (h h' : W ⟶ U)
        (θ : a.hom.hom.toFunctor.obj (Over.mk h) ⟶ a.hom.hom.toFunctor.obj (Over.mk h')),
        𝒳.val.val.p.IsHomLift (𝟙 W) θ →
        ∃ (W' : BigFppfOver B S hS) (m : W' ⟶ W) (c : W' ⟶ R),
          Surjective ((BigFppfOver.toScheme B S hS).map m) ∧
          Etale ((BigFppfOver.toScheme B S hS).map m) ∧
          c ≫ t = m ≫ h ∧ c ≫ s = m ≫ h' := by
  let eU : StacksRepresentableCFG.EquivalenceOver (schemeFibredCategory B S hS U).val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver U
  obtain ⟨Rp, hRp, ⟨eR⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack B S hS
      (schemeFibredCategory B S hS U) 𝒳.val a.hom.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  set src := SelfIntersection.relationSourceMap
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩) eU eR
  set tgt := SelfIntersection.relationTargetMap
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩) eU eR
  have hsrc : Space.IsSmooth B S hS src :=
    SelfIntersection.isSmooth_selfIntersectionPresentation_source (F := a.hom)
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩)
      eU eR hrep hsmooth 𝒳.property
  have htgt : Space.IsSmooth B S hS tgt :=
    SelfIntersection.isSmooth_selfIntersectionPresentation_target (F := a.hom)
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩)
      eU eR hrep hsmooth 𝒳.property
  obtain ⟨R, atl, hatls, hatle⟩ := hRp.exists_atlas
  have hcomp : ∀ (W₀ : BigFppfOver B S hS) (g : W₀ ⟶ R) (σ : Rp ⟶ yoneda.obj U),
      g ≫ yoneda.preimage (atl ≫ σ) = σ.app (op W₀) (atl.app (op W₀) g) :=
    fun W₀ g σ => congrArg (fun φ => φ.app (op W₀) g) (Functor.map_preimage yoneda (atl ≫ σ))
  refine ⟨R, yoneda.preimage (atl ≫ src), yoneda.preimage (atl ≫ tgt),
    smooth_preimage_atlas_comp B S hS hRp hatle hsrc,
    smooth_preimage_atlas_comp B S hS hRp hatle htgt, fun x => ?_, ?_⟩
  · have hmap : ∀ σ : Rp ⟶ yoneda.obj U, (Over.map (yoneda.preimage (atl ≫ σ))).obj x =
        Over.mk (σ.app (op x.left) (atl.app (op x.left) x.hom)) :=
      fun σ => congrArg Over.mk (hcomp x.left x.hom σ)
    rw [hmap src, hmap tgt]
    exact nonempty_hom_relationSourceMap_relationTargetMap B S hS a hRp eR _
  · intro W h h' θ hθ
    have := hθ
    have : 𝒳.val.val.p.IsStronglyCartesian (𝟙 W) θ :=
      𝒳.val.property.isStronglyCartesian_homLift (𝟙 W) θ
    have : IsIso θ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.val.p (𝟙 W) θ
    let r₀ : (SelfIntersection.relation B S hS (schemeFibredCategory B S hS U) 𝒳.val
        a.hom.hom).val.obj :=
      { base := W, x := Over.mk h, y := Over.mk h', hx := rfl, hy := rfl, iso := asIso θ
        vertical := hθ }
    exact exists_lift_atlas B S hS hatls hatle (PresheafOfCategories.sectionOfObj eR r₀ rfl) tgt src
      (SelfIntersection.relationTargetMap_sectionOfObj
        (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩) eU eR r₀ rfl)
      (SelfIntersection.relationSourceMap_sectionOfObj
        (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (R := ⟨Rp, hRp⟩) eU eR r₀ rfl)

variable (T : Set (AlgebraicStacks.points B S hS 𝒳))
  (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T)

/-- Membership of a morphism `h : W ⟶ U` of the site in the reduced induced closed subscheme of
a chart is local for the fppf topology on `W`. -/
theorem mem_chartReducedSubscheme_of_sieve {W : BigFppfOver B S hS} (h : W ⟶ U)
    (hh : (Space.subschemePoints B S hS (chartReducedSubscheme B S hS 𝒳 U a T hT)).sieveOfSection
      (U := op W) h ∈ BigFppfOver.topology B S hS W) :
    h ∈ (Space.subschemePoints B S hS (chartReducedSubscheme B S hS 𝒳 U a T hT)).obj (op W) := by
  have him : AlgebraicGeometry.IsImmersion (chartReducedSubscheme B S hS 𝒳 U a T hT).arrow :=
    have := isClosedImmersion_arrow_chartReducedSubscheme B S hS 𝒳 U a T hT
    inferInstance
  obtain ⟨V, i, e, he⟩ := Space.exists_presentation B S hS _ him
  exact Space.mem_subschemePoints_of_sieveOfSection B S hS i e he h hh

include hrep hsmooth in
/-- **The reduced induced closed subscheme of a smooth chart is invariant in the strong sense.**
Let `a : U ⟶ 𝒳` be a smooth 1-morphism from the algebraic stack of a scheme of the site,
representable by algebraic spaces, and let `T` be a closed set of points of `𝒳`. If `h, h' : W ⟶ U`
are two morphisms of the site whose images under `a` are joined by a morphism of `𝒳` over the
identity of `W`, and `h` factors through the reduced induced closed subscheme `Z` of `U` on the
part lying over `T`, then so does `h'`.

On a scheme chart `R` of the relation `U ×_𝒳 U` the two pullbacks of `Z` agree
(`AlgebraicGeometry.Stack.pullback_subobject_chartReducedSubscheme_eq_of_pointsMap_eq`), and the
pair `(h, h')` lifts to `R` after a surjective étale morphism of `W`
(`AlgebraicGeometry.Stack.exists_relationChart`); membership of `Z` is fppf local. -/
theorem mem_chartReducedSubscheme_of_hom {W : BigFppfOver B S hS} (h h' : W ⟶ U)
    (θ : a.hom.hom.toFunctor.obj (Over.mk h) ⟶ a.hom.hom.toFunctor.obj (Over.mk h'))
    (hθ : 𝒳.val.val.p.IsHomLift (𝟙 W) θ)
    (hh : h ∈ (Space.subschemePoints B S hS (chartReducedSubscheme B S hS 𝒳 U a T hT)).obj
      (op W)) :
    h' ∈ (Space.subschemePoints B S hS (chartReducedSubscheme B S hS 𝒳 U a T hT)).obj
      (op W) := by
  obtain ⟨R, s, t, hs, ht, hst, hlift⟩ := exists_relationChart B S hS a hrep hsmooth
  set Z := chartReducedSubscheme B S hS 𝒳 U a T hT
  have hpts : AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS s ≫ a) =
      AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS t ≫ a) := by
    funext q
    induction q using Quotient.inductionOn with
    | h q =>
      obtain ⟨θ'⟩ := hst q.obj
      exact (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2
        ⟨_, ⟨𝟙 _⟩, ⟨θ'⟩⟩
  have hinv := pullback_subobject_chartReducedSubscheme_eq_of_pointsMap_eq B S hS 𝒳 U R a T hT
    s t hs ht hpts
  obtain ⟨W', m, c, hms, hme, hct, hcs⟩ := hlift W h h' θ hθ
  have hm' : m ≫ h' ∈ (Space.subschemePoints B S hS Z).obj (op W') := by
    have h1 : c ≫ t ∈ (Space.subschemePoints B S hS Z).obj (op W') := by
      rw [hct]
      exact (Space.subschemePoints B S hS Z).map m.op hh
    rw [Space.mem_subschemePoints_iff] at h1 ⊢
    rwa [← hcs, Functor.map_comp, ← Limits.pullback_factors_iff, hinv,
      Limits.pullback_factors_iff, ← Functor.map_comp]
  refine mem_chartReducedSubscheme_of_sieve B S hS a T hT h' ?_
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (Space.sieve_generate_singleton_mem_topology_over B S hS m hms hme)
  rintro V g ⟨_, g', _, ⟨⟩, rfl⟩
  change (g' ≫ m) ≫ h' ∈ (Space.subschemePoints B S hS Z).obj (op V)
  rw [Category.assoc]
  exact (Space.subschemePoints B S hS Z).map g'.op hm'

end Relation

/-! ### Morphisms of a category fibred in groupoids over one base morphism -/

/-- Two morphisms of a category fibred in groupoids into one object, lying over one morphism of
the base, differ by a morphism over the identity. -/
theorem exists_isHomLift_id_comp_eq {X : Type*} [Category X] {p : X ⥤ BigFppfOver B S hS}
    (hp : p.IsFiberedInGroupoids) {x₁ x₂ y : X} {R R' : BigFppfOver B S hS} (f : R ⟶ R')
    (ψ₁ : x₁ ⟶ y) (ψ₂ : x₂ ⟶ y) (h₁ : p.IsHomLift f ψ₁) (h₂ : p.IsHomLift f ψ₂) :
    ∃ θ : x₁ ⟶ x₂, p.IsHomLift (𝟙 R) θ ∧ θ ≫ ψ₂ = ψ₁ := by
  have := h₁
  have := h₂
  have : p.IsStronglyCartesian f ψ₂ := hp.isStronglyCartesian_homLift f ψ₂
  exact ⟨Functor.IsStronglyCartesian.map p f ψ₂ (Category.id_comp f).symm ψ₁, inferInstance,
    Functor.IsStronglyCartesian.fac p f ψ₂ (Category.id_comp f).symm ψ₁⟩

end AlgebraicGeometry.Stack

end
