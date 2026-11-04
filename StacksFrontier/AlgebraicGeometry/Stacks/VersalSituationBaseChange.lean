module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosureImageValuativePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal

/-!
# Inputs of the versal situation after a change of base

Let `g : S ⟶ S'` be a morphism of a big fppf site. This file collects the facts needed to read an
algebraic stack over `S'` with a 1-morphism to `S/S'` as a versal situation over `S`
(Stacks 0DQU), as in the proof of Stacks 0DZU, where `S'` is `Spec ℤ` and `S` the spectrum of a
Cohen ring.

* The structure morphism of the algebraic stack of an object `V` of the site is flat, resp.
  locally of finite presentation, when `V ⟶ S` is; this is the hypothesis of Stacks 0DZR, part
  (4), for a base change along `V ⟶ S`.
* If the 1-morphism `a : 𝒳' ⟶ S/S'` of a pair is locally of finite type, then the structure
  morphism over `S` of the algebraic stack Construction B (Stacks 04X5) attaches to the pair is
  locally of finite type. A presentation of `𝒳'` by a scheme `U'` over `S'` has its structure
  morphism factoring through `S` (rigidity of relocalization), and the factorization `U' ⟶ S` is
  the morphism of schemes underlying `a` on the chart, hence locally of finite type; the
  presentation read over `S` is smooth and surjective, and local finite type descends along it.

## Main results

* `AlgebraicGeometry.Stack.isFlat_structureMorphism_schemeStack` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_structureMorphism_schemeStack`.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_structureMorphism_of_changeBaseStructureHom`
  and
  `AlgebraicGeometry.Stack.isLocallyOfFiniteType_structureMorphism_algebraicStackConstructionB`:
  local finite type of the structure morphism over `S`, read from Construction A or B.

The existence of a versal ring at a finite type point of a versal situation is
`AlgebraicGeometry.Stack.exists_isVersalRingAt` (Stacks 0DQX), and the base change of local finite
presentation along a 2-fibre product is
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_baseChange` (Stacks 06Q4).
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

section SchemeStack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of the algebraic stack of an object `V` of the site is the 1-morphism
induced by the morphism `V ⟶ S/S` of the site. -/
theorem structureMorphism_schemeStack_eq (V : BigFppfOver B S hS) :
    structureMorphism B S hS (schemeStack.{u, w} B S hS V) =
      (Bicategory.InducedBicategory.mkHom
        (schemeFibredCategoryMap B S hS (Over.homMk V.hom : V ⟶ Over.mk (𝟙 (B.obj hS)))) :
        schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))) :=
  (eq_structureMorphism.{u, w} B S hS _ _).symm

/-- **The structure morphism of the algebraic stack of a flat object of the site is flat.** -/
theorem isFlat_structureMorphism_schemeStack (V : BigFppfOver B S hS)
    (hV : Flat (B.inclusion.map V.hom)) :
    AlgebraicStacks.IsFlat B S hS (structureMorphism B S hS (schemeStack.{u, w} B S hS V)) := by
  rw [structureMorphism_schemeStack_eq]
  exact isFlat_schemeFibredCategoryMap B S hS _ hV

/-- **The structure morphism of the algebraic stack of an object of the site locally of finite
presentation over `S` is locally of finite presentation.** -/
theorem isLocallyOfFinitePresentation_structureMorphism_schemeStack (V : BigFppfOver B S hS)
    (hV : LocallyOfFinitePresentation (B.inclusion.map V.hom)) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (structureMorphism B S hS (schemeStack.{u, w} B S hS V)) := by
  rw [structureMorphism_schemeStack_eq]
  exact AlgebraicStacks.isLocallyOfFinitePresentation_schemeStackMap B S hS _ hV

/-- **The structure morphism of the algebraic stack of an object of the site locally of finite
type over `S` is locally of finite type.** -/
theorem isLocallyOfFiniteType_structureMorphism_schemeStack (V : BigFppfOver B S hS)
    (hV : LocallyOfFiniteType (B.inclusion.map V.hom)) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (structureMorphism B S hS (schemeStack.{u, w} B S hS V)) := by
  rw [structureMorphism_schemeStack_eq]
  exact isLocallyOfFiniteType_schemeFibredCategoryMap B S hS _ hV

/-- **Local finite type descends from a smooth surjective scheme chart.** If `𝒳` has a smooth,
surjective 1-morphism representable by algebraic spaces from the algebraic stack of an object `V`
of the site locally of finite type over `S`, then `𝒳 ⟶ S` is locally of finite type. -/
private theorem isLocallyOfFiniteType_structureMorphism_of_smooth_surjective_chart
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (V : BigFppfOver B S hS)
    (f₀ : (schemeFibredCategory B S hS V).val ⥤ᵇ 𝒳.val.val)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f₀)
    (hsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      (Bicategory.InducedBicategory.mkHom f₀ : schemeFibredCategory B S hS V ⟶ 𝒳.val) hrep)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
      (Bicategory.InducedBicategory.mkHom f₀ : schemeFibredCategory B S hS V ⟶ 𝒳.val) hrep)
    (hV : LocallyOfFiniteType (B.inclusion.map V.hom)) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS (structureMorphism B S hS 𝒳) := by
  let c : schemeStack.{u, w} B S hS V ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom f₀)
  have hcsm : AlgebraicStacks.IsSmooth B S hS c :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property _ hrep hsmooth
  have hfg : AlgebraicStacks.IsLocallyOfFiniteType B S hS (c ≫ structureMorphism B S hS 𝒳) := by
    rw [comp_structureMorphism]
    exact isLocallyOfFiniteType_structureMorphism_schemeStack B S hS _ hV
  exact AlgebraicStacks.isLocallyOfFiniteType_of_comp_of_fppf B S hS c _ hfg hrep
    ((pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS c hrep).mpr hsurj)
    (AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hcsm)

end SchemeStack

section ConstructionB

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- Relocalizing along `U' ⟶ Spec S'` and then postcomposing with a morphism `ψ : U' ⟶ S/S'`
of the site of `S'` is postcomposition with the underlying morphism `U' ⟶ S`. -/
theorem iteratedSliceBackward_comp_map_comp_iteratedSliceForward
    {U' : BigFppfOver B S' hS'} (ψ : U' ⟶ Over.mk g) :
    Over.iteratedSliceBackward U' ⋙ Over.map ψ ⋙ Over.iteratedSliceForward (Over.mk g) =
      Over.map ψ.left :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ f => heq_of_eq (by
    apply Over.OverMorphism.ext
    rfl))

/-- Relocalizing at `f` and then going back is the identity of `T/f.left`, on the nose. -/
theorem iteratedSliceBackward_comp_iteratedSliceForward {T : Type*} [Category T] {Z : T}
    (f : Over Z) :
    Over.iteratedSliceBackward f ⋙ Over.iteratedSliceForward f = 𝟭 (Over f.left) :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (by
    apply Over.OverMorphism.ext
    rfl))

/-- **A chart of Construction A over `S'` gives a chart over `S`.** Let `f'` be a 1-morphism from
the algebraic stack of `U'` to `changeBase 𝒳`, representable by algebraic spaces, smooth and
surjective, whose composite with `changeBase 𝒳 ⟶ S/S'` is postcomposition with
`ψ : U' ⟶ S/S'`. Then the same functor, read over `S`, is a smooth surjective 1-morphism
representable by algebraic spaces from the algebraic stack of `U'.left ⟶ S` to `𝒳`. -/
private theorem exists_smooth_surjective_chart_of_changeBase (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {U' : BigFppfOver B S' hS'} (ψ : U' ⟶ Over.mk g)
    (f' : (schemeFibredCategory B S' hS' U').val ⥤ᵇ
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳.val).val)
    (hψ : f'.toFunctor ⋙ (𝒳.val.val.p ⋙ Over.iteratedSliceBackward (Over.mk g)) = Over.map ψ)
    (hrep' : IsRepresentableByAlgebraicSpaces B S' hS' f')
    (hsurj' : HasRelativeProperty.{u, u, u + 1, u} B S' hS'
      (Space.surjectiveMorphismProperty B S' hS')
      (Bicategory.InducedBicategory.mkHom f' : schemeFibredCategory B S' hS' U' ⟶
        changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳.val) hrep')
    (hsmooth' : HasRelativeProperty.{u, u, u + 1, u} B S' hS'
      (Space.smoothMorphismProperty B S' hS')
      (Bicategory.InducedBicategory.mkHom f' : schemeFibredCategory B S' hS' U' ⟶
        changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳.val) hrep') :
    ∃ (f₀ : (schemeFibredCategory B S hS (Over.mk ψ.left)).val ⥤ᵇ 𝒳.val.val)
      (hrep : IsRepresentableByAlgebraicSpaces B S hS f₀),
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
        (Bicategory.InducedBicategory.mkHom f₀ :
          schemeFibredCategory B S hS (Over.mk ψ.left) ⟶ 𝒳.val) hrep ∧
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
        (Bicategory.InducedBicategory.mkHom f₀ :
          schemeFibredCategory B S hS (Over.mk ψ.left) ⟶ 𝒳.val) hrep := by
  let a := factorSliceFunctor B S S' hS hS' g (Over.w ψ)
  have hp : f'.toFunctor ⋙ 𝒳.val.val.p = Over.map ψ ⋙ Over.iteratedSliceForward (Over.mk g) := by
    rw [← hψ]
    show f'.toFunctor ⋙ 𝒳.val.val.p = f'.toFunctor ⋙ 𝒳.val.val.p ⋙
      (Over.iteratedSliceBackward (Over.mk g) ⋙ Over.iteratedSliceForward (Over.mk g))
    rw [iteratedSliceBackward_comp_iteratedSliceForward]
    rfl
  let f₀ : (schemeFibredCategory B S hS (Over.mk ψ.left)).val ⥤ᵇ 𝒳.val.val :=
    { toFunctor := Over.iteratedSliceForward (Over.mk ψ.left) ⋙
        (Over.iteratedSliceBackward U' ⋙ f'.toFunctor)
      w := by
        have h3 : Over.iteratedSliceForward (Over.mk ψ.left) ⋙ (Over.iteratedSliceBackward U' ⋙
            (Over.map ψ ⋙ Over.iteratedSliceForward (Over.mk g))) =
              Over.forget (Over.mk ψ.left) := by
          rw [iteratedSliceBackward_comp_map_comp_iteratedSliceForward]
          exact Over.iteratedSliceForward_comp_map (Over.mk ψ.left)
        rwa [← hp] at h3 }
  have hrep : IsRepresentableByAlgebraicSpaces B S hS f₀ :=
    (isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g f₀).1
      ((isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S' hS'
        (𝒳' := changeBaseFiberedInGroupoids B S S' hS hS' g
          (schemeFibredCategory B S hS (Over.mk ψ.left)))
        (𝒳 := schemeFibredCategory B S' hS' U')
        (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳.val)
        f' (BasedFunctor.comp a f') a (Iso.refl _)).1 hrep')
  let 𝒳b := changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳.val
  let Ub := changeBaseFiberedInGroupoids B S S' hS hS' g
    (schemeFibredCategory B S hS (Over.mk ψ.left))
  let f'h : schemeFibredCategory B S' hS' U' ⟶ 𝒳b := Bicategory.InducedBicategory.mkHom f'
  let fb : Ub ⟶ 𝒳b :=
    Bicategory.InducedBicategory.mkHom (changeBaseFunctor B S S' hS hS' g f₀)
  let bId : 𝒳b.val ⥤ᵇ 𝒳b.val := BasedFunctor.id 𝒳b.val
  have _ : Functor.IsEquivalence bId.toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳b.val.obj))
  have _ : (Space.surjectiveMorphismProperty B S' hS').IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S' hS') := inferInstance
  have _ : (Space.smoothMorphismProperty B S' hS').IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S' hS') := inferInstance
  exact ⟨f₀, hrep,
    (hasRelativeProperty_surjective_changeBaseHom_iff.{u, u, u + 1, u} B S S' hS hS' g
        (Bicategory.InducedBicategory.mkHom f₀) hrep).1
      ((hasRelativeProperty_iff_of_equivalences B S' hS'
          (Space.surjectiveMorphismProperty B S' hS') fb f'h a bId (Iso.refl _) hrep').1
        hsurj'),
    (hasRelativeProperty_smooth_changeBaseHom_iff.{u, u, u + 1} B S S' hS hS' g
        (@AlgebraicGeometry.Smooth.{u}) (Bicategory.InducedBicategory.mkHom f₀) hrep).1
      ((hasRelativeProperty_iff_of_equivalences B S' hS'
          (Space.smoothMorphismProperty B S' hS') fb f'h a bId (Iso.refl _) hrep').1
        hsmooth')⟩

/-- **Local finite type descends along Construction A.** Let `𝒳` be an algebraic stack over `S`.
If the 1-morphism `changeBase 𝒳 ⟶ S/S'` that Construction A (Stacks 04X5) equips `𝒳` with is
locally of finite type over `S'`, then the structure morphism `𝒳 ⟶ S` is locally of finite
type.

A presentation `(Sch/U') ⟶ changeBase 𝒳` by a scheme over `S'`, followed by `changeBase 𝒳 ⟶ S/S'`,
is postcomposition with a morphism `ψ : U' ⟶ S/S'` of the site of `S'` (rigidity of
relocalization), which is locally of finite type because the composite is. Its underlying
morphism `U'.left ⟶ S` makes `U'` an object of the site of `S`, locally of finite type over `S`,
and the presentation read over `S` is smooth and surjective (Stacks 04X5); local finite type of
`𝒳 ⟶ S` then descends from the chart (Stacks 06EW). -/
theorem isLocallyOfFiniteType_structureMorphism_of_changeBaseStructureHom
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h : AlgebraicStacks.IsLocallyOfFiniteType B S' hS'
      (Bicategory.InducedBicategory.mkHom (changeBaseStructureHom B S S' hS hS' g 𝒳) :
        changeBaseAlgebraicStack B S S' hS hS' g 𝒳 ⟶ schemeStack.{u, w} B S' hS' (Over.mk g))) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS (structureMorphism B S hS 𝒳) := by
  classical
  obtain ⟨hfib', -, hdiag', U', f', hrep', hprop'⟩ :=
    (changeBaseAlgebraicStack B S S' hS hS' g 𝒳).property
  -- the chart followed by the 1-morphism to `S/S'` is postcomposition with `ψ : U' ⟶ S/S'`
  have hw' : (f'.toFunctor ⋙ (𝒳.val.val.p ⋙ Over.iteratedSliceBackward (Over.mk g))) ⋙
      Over.forget (Over.mk g) = Over.forget U' := by
    show f'.toFunctor ⋙ (𝒳.val.val.p ⋙ (Over.iteratedSliceBackward (Over.mk g) ⋙
      Over.forget (Over.mk g))) = Over.forget U'
    rw [Over.iteratedSliceBackward_forget]
    exact f'.w
  obtain ⟨ψ, hψ⟩ := Over.exists_eq_map_of_comp_forget _ hw'
  let c' : schemeStack.{u, w} B S' hS' U' ⟶ changeBaseAlgebraicStack B S S' hS hS' g 𝒳 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom f')
  have hc' : AlgebraicStacks.IsSmooth B S' hS' c' :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S' hS'
      (fun _ _ k => Space.IsSmooth B S' hS' k)
      (changeBaseAlgebraicStack B S S' hS hS' g 𝒳).property _ hrep'
      (fun V y hy G hG he => (hprop' V y hy G hG he).2)
  have hcft := AlgebraicStacks.isLocallyOfFiniteType_comp B S' hS' c' _
    (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S' hS'
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S' hS' c' hc')) h
  have heq : c' ≫ (Bicategory.InducedBicategory.mkHom (changeBaseStructureHom B S S' hS hS' g 𝒳) :
        changeBaseAlgebraicStack B S S' hS hS' g 𝒳 ⟶ schemeStack.{u, w} B S' hS' (Over.mk g)) =
      schemeStackMap.{u, w} B S' hS' ψ :=
    Bicategory.InducedBicategory.hom_ext (Bicategory.InducedBicategory.hom_ext
      (BasedCategory.BasedFunctor.ext' hψ))
  rw [heq] at hcft
  have hψft : LocallyOfFiniteType (B.inclusion.map ψ.left) := by
    have h1 := locallyOfFiniteType_siteMap_of_isLocallyOfFiniteType B S' hS' _ hcft
    have h2 : siteMap B S' hS' (schemeStackMap.{u, w} B S' hS' ψ) = ψ :=
      schemeMapOfFunctor_overMapBased B S' hS' ψ
    rwa [h2] at h1
  -- the chart read over `S`
  obtain ⟨f₀, hrep, hsurj, hsmooth⟩ := exists_smooth_surjective_chart_of_changeBase B S S' hS hS' g
    𝒳 ψ f' hψ hrep' (fun T z hz G hG hE => (hprop' T z hz G hG hE).1)
    (fun T z hz G hG hE => (hprop' T z hz G hG hE).2)
  -- descent of local finite type along the chart
  exact isLocallyOfFiniteType_structureMorphism_of_smooth_surjective_chart B S hS 𝒳 _ f₀ hrep
    hsurj hsmooth hψft

/-- **The structure morphism of Construction B is locally of finite type** as soon as the
1-morphism `a : 𝒳' ⟶ S/S'` of the pair is: Construction A of Construction B of the pair is the
pair itself (Stacks 04X5), so this is
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_structureMorphism_of_changeBaseStructureHom`. -/
theorem isLocallyOfFiniteType_structureMorphism_algebraicStackConstructionB
    (X : AlgebraicStackPair.{u, w} B S S' hS hS' g)
    (hX : AlgebraicStacks.IsLocallyOfFiniteType B S' hS'
      (Bicategory.InducedBicategory.mkHom X.2 : X.1 ⟶ schemeStack.{u, w} B S' hS' (Over.mk g))) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (structureMorphism B S hS (algebraicStackConstructionB B S S' hS hS' g X)) := by
  refine isLocallyOfFiniteType_structureMorphism_of_changeBaseStructureHom B S S' hS hS' g _ ?_
  have hX' : algebraicStackConstructionA B S S' hS hS' g
      (algebraicStackConstructionB B S S' hS hS' g X) = X :=
    (algebraicStackConstructionObjEquiv.{u, w} B S S' hS hS' g).right_inv X
  revert hX
  generalize algebraicStackConstructionB B S S' hS hS' g X = 𝒳 at hX' ⊢
  subst hX'
  exact id

end ConstructionB

end AlgebraicGeometry.Stack

end
