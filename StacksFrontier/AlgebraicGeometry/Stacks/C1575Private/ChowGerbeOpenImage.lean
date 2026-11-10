module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeFlatCase
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubspaceOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningOpenImmersionIsomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliFiniteTypeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsQuotientOfSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsAlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct

/-!
# The open image of a flat morphism, in the proof of Stacks 0CQ7

In the proof of [Stacks, Tag 0CQ7], after flattening, `f : 𝒳 ⟶ Y` is flat and locally of finite
presentation, so the image of `|f|` is open (Stacks 06R7); it is quasi-compact because `𝒳` is
(`f` quasi-compact and `Y` quasi-compact). Let `W ⊆ Y` be the open subspace with that point set.
Every value of `f` lies in `W` (an object of `𝒳` sees only points in the image), the
corestriction `𝒳 ⟶ W` is surjective, flat (it is the base change of `f` along the monomorphism
`W ⟶ Y`) and locally of finite presentation (Stacks 06Q6), and `V ⊆ W` when `𝒳_V ⟶ V` is a
gerbe, since a gerbe is surjective. This feeds the flat case,
`ChowGerbeLocalIsos.hasProperCompactifiableCover_of_corestrict`.

## Main results

* `isFlat_corestrict`: the corestriction of a flat `f` to an open subspace containing its image is
  flat.
* `isLocallyOfFinitePresentation_corestrict`: the same for locally of finite presentation.
* `hasProperCompactifiableCover_of_isFlat`: the conclusion of Stacks 0CQ7 for a separated,
  quasi-compact, flat and locally finitely presented `f` over a quasi-compact quasi-separated
  `Y`.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeOpenImage

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}

/-- The 1-morphism of the inclusion of an open subspace is a monomorphism of algebraic stacks. -/
theorem isMonomorphism_algebraicSpaceStackMap_ι {W : Subfunctor Y}
    (hW : Space.IsOpenSubspace B S hS W) :
    IsMonomorphism B S hS (algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι) :=
  isMonomorphism_of_isOpenImmersion B S hS _
    (isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion B S hS hW.1 hY hW.2)

/-- **The corestriction of a flat 1-morphism to an open subspace is flat**: it is the base change
of the 1-morphism along the inclusion, which is a monomorphism (Stacks 04ZZ, Stacks 06PY). -/
theorem isFlat_corestrict {W : Subfunctor Y} (hW : Space.IsOpenSubspace B S hS W)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)))
    (hfl : IsFlat B S hS f) :
    IsFlat B S hS (corestrictAlgebraicSpaceStack f W hW.1 hfW) := by
  let fW := corestrictAlgebraicSpaceStack f W hW.1 hfW
  let ι := algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι
  exact isFlat_baseChange B S hS (fW ≫ ι) ι _
    (Bicategory.isTwoFibreProduct_pasteSnd _
      (isTwoFibreProduct_selfCospanSquare B S hS ι (isMonomorphism_algebraicSpaceStackMap_ι hW)) _
      (Bicategory.isTwoFibreProduct_idCospan fW))
    (by rwa [corestrictAlgebraicSpaceStack_comp])

/-- **The corestriction of a 1-morphism locally of finite presentation to an open subspace is
locally of finite presentation** (Stacks 06Q6): the inclusion is locally of finite type. -/
theorem isLocallyOfFinitePresentation_corestrict {W : Subfunctor Y}
    (hW : Space.IsOpenSubspace B S hS W)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)))
    (hlfp : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B S hS (corestrictAlgebraicSpaceStack f W hW.1 hfW) := by
  refine isLocallyOfFinitePresentation_of_comp B S hS _
    (algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι) ?_
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (isLocallyOfFinitePresentation_of_isOpenImmersion B S hS _
        (isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion B S hS hW.1 hY hW.2)))
  rwa [corestrictAlgebraicSpaceStack_comp]

/-- Every value of `f` lies in the open subspace of `Y` whose points are the image of `|f|`. -/
private theorem algebraicSpaceStackSection_mem_openSubspaceOfPoints (ξ : 𝒳.val.val.obj) :
    algebraicSpaceStackSection f ξ ∈ (Space.openSubspaceOfPoints B S hS Y
      (spacePointMap B S hS Y (algebraicSpaceStack.{u, w} B S hS Y hY).val
        (BasedFunctor.id (fibredCategory B S hS Y).val) ⁻¹'
          Set.range (AlgebraicStacks.pointsMap B S hS f))).obj (op (𝒳.val.val.p.obj ξ)) := by
  have key : pointsWithin (algebraicSpaceStack.{u, w} B S hS Y hY)
      (Set.range (AlgebraicStacks.pointsMap B S hS f)) (f.hom.hom.toFunctor.obj ξ) :=
    pointsWithin_obj_of_pointsWithin_preimage B S hS f.hom.hom _ (fun _ _ => ⟨_, rfl⟩)
  rw [mem_openSubspaceOfPoints_spacePointMap_preimage_iff B S hS Y _]
  have heq : (⟨𝒳.val.val.p.obj ξ, Discrete.mk (algebraicSpaceStackSection f ξ)⟩ :
      (fibredCategory B S hS Y).val.obj) = f.hom.hom.toFunctor.obj ξ :=
    obj_eq_of_elementOf_eq rfl (Functor.congr_obj f.hom.hom.w ξ) rfl
  change pointsWithin (algebraicSpaceStack.{u, w} B S hS Y hY) _
    ⟨𝒳.val.val.p.obj ξ, Discrete.mk (algebraicSpaceStackSection f ξ)⟩
  rwa [heq]

/-- If `𝒳_V ⟶ V` is a gerbe, then `V` lies in any open subspace `W` whose points are the
image of `|f|`, since a gerbe is surjective. -/
private theorem le_of_isGerbeOver {V W : Subfunctor Y} (hV : Space.IsOpenSubspace B S hS V)
    (hW : Space.IsOpenSubspace B S hS W)
    (hWpts : Set.range (Space.pointsMap B S hS W.toFunctor W.ι) =
      spacePointMap B S hS Y (algebraicSpaceStack.{u, w} B S hS Y hY).val
        (BasedFunctor.id (fibredCategory B S hS Y).val) ⁻¹'
          Set.range (AlgebraicStacks.pointsMap B S hS f))
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    V ≤ W := by
  refine Space.le_of_range_pointsMap_ι_subset B S hS hW ?_
  rintro _ ⟨v, rfl⟩
  rw [hWpts]
  let Q := twoFibreProductSquareAlgebraicStacks B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f
  obtain ⟨x, hx⟩ := isSurjective_of_isGerbeOver B S hS Q.fst hG
    (spacePointsEquiv B S hS V.toFunctor v)
  refine ⟨AlgebraicStacks.pointsMap B S hS Q.snd x, ?_⟩
  rw [← Function.comp_apply (f := AlgebraicStacks.pointsMap B S hS f),
    ← AlgebraicStacks.pointsMap_comp, ← AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS Q.iso.hom,
    AlgebraicStacks.pointsMap_comp, Function.comp_apply, hx]
  exact pointsMap_algebraicSpaceStackMap_spacePointsEquiv.{u, w} B S hS hV.1 hY V.ι v

/-- **The flat case of [Stacks, Tag 0CQ7], with the open image.** Let `f : 𝒳 ⟶ Y` be separated,
quasi-compact, flat and locally of finite presentation, with `Y` quasi-compact and
quasi-separated, and let `V ⊆ Y` be a quasi-compact open with `𝒳_V ⟶ V` a gerbe. Then the
conclusion of Stacks 0CQ7 holds for `(f, V)`. The image `W` of `|f|` is open (Stacks 06R7) and
quasi-compact, and the corestriction `𝒳 ⟶ W` is surjective, flat and locally of finite
presentation. -/
theorem hasProperCompactifiableCover_of_isFlat
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hf : IsSeparated B S hS f) (hqc : Stack.IsQuasiCompactMorphism B S hS f)
    (hfl : IsFlat B S hS f) (hlfp : IsLocallyOfFinitePresentation B S hS f)
    {V : Subfunctor Y} (hV : Space.IsOpenSubspace B S hS V)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  classical
  let := Stack.pointTopology B S hS 𝒳.val
  let := Stack.pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS Y hY).val
  let Ω := Set.range (AlgebraicStacks.pointsMap B S hS f)
  have hΩ : _root_.IsOpen Ω := (isOpenMap_pointsMap B S hS f hfl hlfp).isOpen_range
  let Ω' := spacePointMap B S hS Y (algebraicSpaceStack.{u, w} B S hS Y hY).val
    (BasedFunctor.id (fibredCategory B S hS Y).val) ⁻¹' Ω
  let W := Space.openSubspaceOfPoints B S hS Y Ω'
  have hW : Space.IsOpenSubspace B S hS W :=
    isOpenSubspace_openSubspaceOfPoints_spacePointMap_preimage B S hS Y hY Ω _ hΩ
  have hWpts : Set.range (Space.pointsMap B S hS W.toFunctor W.ι) = Ω' :=
    Space.range_pointsMap_ι_openSubspaceOfPoints B S hS Ω'
  -- every value of `f` lies in `W`
  have hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)) :=
    algebraicSpaceStackSection_mem_openSubspaceOfPoints
  let fW := corestrictAlgebraicSpaceStack f W hW.1 hfW
  let ι := algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι
  have hfWι : fW ≫ ι = f := corestrictAlgebraicSpaceStack_comp f W hW.1 hfW
  -- the map on points of `ι` is injective
  have hinj : Function.Injective (AlgebraicStacks.pointsMap B S hS ι) := by
    obtain ⟨h1, h2⟩ := full_and_faithful_homFunctor_of_isMonomorphism B S hS ι
      (isMonomorphism_algebraicSpaceStackMap_ι hW)
    exact Stack.pointsMap_injective_of_fullyFaithful B S hS ι
  -- the corestriction is surjective
  have hs : IsSurjective B S hS fW := by
    intro w
    obtain ⟨w₀, rfl⟩ := (spacePointsEquiv B S hS W.toFunctor).surjective w
    obtain ⟨x, hx⟩ : Space.pointsMap B S hS W.toFunctor W.ι w₀ ∈ Ω' := hWpts ▸ ⟨w₀, rfl⟩
    refine ⟨x, hinj ?_⟩
    rw [← Function.comp_apply (f := AlgebraicStacks.pointsMap B S hS ι),
      ← AlgebraicStacks.pointsMap_comp, hfWι]
    exact hx.trans
      (pointsMap_algebraicSpaceStackMap_spacePointsEquiv.{u, w} B S hS hW.1 hY W.ι w₀).symm
  -- `W` is quasi-compact, as an image of the quasi-compact `𝒳`
  have hWqc : Space.IsQuasiCompactSpace B S hS W.toFunctor := by
    let := Stack.pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS W.toFunctor hW.1).val
    have hc : Continuous ((pointsHomeomorphSpace.{u, w} B S hS W.toFunctor hW.1).symm ∘
        AlgebraicStacks.pointsMap B S hS fW) :=
      (pointsHomeomorphSpace.{u, w} B S hS W.toFunctor hW.1).symm.continuous.comp
        (continuous_pointsMap B S hS _ _ fW.hom.hom)
    have : CompactSpace (AlgebraicStacks.points B S hS 𝒳) :=
      isQuasiCompactStack_of_isQuasiCompactMorphism B S hS f hqc
        (isQuasiCompactStack_fibredCategory B S hS Y hY hYqc _)
    exact Space.isQuasiCompactSpace_of_compactSpace_points B S hS hW.1
      (((pointsHomeomorphSpace.{u, w} B S hS W.toFunctor hW.1).symm.surjective.comp
        hs).compactSpace hc)
  exact ChowGerbeLocalIsos.hasProperCompactifiableCover_of_corestrict hYqc hYqs hf hW hWqc hfW hs
    (isFlat_corestrict hW hfW hfl) (isLocallyOfFinitePresentation_corestrict hW hfW hlfp) hV hVqc
    (le_of_isGerbeOver hV hW hWpts hG) hG

end AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeOpenImage

end
