module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowChangeOfBaseTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemma.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TrivialBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects

/-!
# The hypotheses of Stacks 0CQ8 and a change of base scheme

Let `g : S ⟶ S'` be a morphism of a big fppf site and `f : 𝒳 ⟶ Y` a 1-morphism from an algebraic
stack to an algebraic space over `S`. The hypotheses of Stacks 0CQ8 on `f` — separated and of
finite type — survive viewing `f` over `S'` (`AlgebraicGeometry.Stack.changeBaseToAlgebraicSpace`).
Together with `AlgebraicGeometry.Space.isQuasiCompactSpace_relocalize_iff` and
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_relocalize` for `Y`, and
`AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_changeBase` for the
conclusion, this is what replacing `S` by `Spec(ℤ)` in the proof of Stacks 0CQ8 needs.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_comp_of_full_of_faithful`: separatedness
  is unchanged by postcomposition with a fully faithful 1-morphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFiniteType_of_isEquivalence`: an equivalence is of
  finite type.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_changeBase`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactMorphism_changeBase`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_changeBase` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isFiniteType_changeBase`: Construction A preserves
  these properties.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_changeBaseToAlgebraicSpace` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isFiniteType_changeBaseToAlgebraicSpace`: the two
  hypotheses of Stacks 0CQ8 on `f`, viewed over `S'`.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Separatedness is unchanged by postcomposition with a fully faithful 1-morphism.** The
relative diagonal of `f ≫ e` is the relative diagonal of `f` followed by the comparison
`𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳`, which is an equivalence when `e` is fully faithful; so Stacks 0457 applies
at the identity of `𝒳` and that comparison. -/
theorem isSeparated_comp_of_full_of_faithful (f : 𝒳 ⟶ 𝒴) (e : 𝒴 ⟶ 𝒵)
    [(CatFiberedInGroupoids.homFunctor e.hom).Full]
    [(CatFiberedInGroupoids.homFunctor e.hom).Faithful]
    (hf : IsSeparated B S hS f) : IsSeparated B S hS (f ≫ e) := by
  have : Functor.IsEquivalence (mapBase B S hS f f e).hom.hom.toFunctor :=
    TwoFibreProductOver.isEquivalence_mapBase (CatFiberedInGroupoids.homFunctor_comp_p e.hom)
  have : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  exact Stack.relativeProperty_of_equivalences_symm B S hS
    (fun _ _ k => Space.IsProper B S hS k.hom)
    (relativeDiagonal B S hS f).hom.hom (relativeDiagonal B S hS (f ≫ e)).hom.hom
    (BasedFunctor.id _) (mapBase B S hS f f e).hom.hom
    (eqToIso (congrArg (fun q => q.hom.hom) (relativeDiagonal_comp B S hS f e))) hf

/-- **The identity 1-morphism is of finite type.** -/
theorem isFiniteType_id (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS) :
    IsFiniteType B S hS (𝟙 𝒴) :=
  ⟨isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
    (isLocallyOfFinitePresentation_id B S hS 𝒴),
    isQuasiCompactMorphism_id_algebraicStack B S hS 𝒴⟩

/-- **A 1-morphism whose underlying functor is an equivalence is of finite type.** -/
theorem isFiniteType_of_isEquivalence (k : 𝒳 ⟶ 𝒴)
    (hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom)) :
    IsFiniteType B S hS k := by
  have h := isFiniteType_comp_of_isEquivalence B S hS k (𝟙 𝒴) hk (isFiniteType_id B S hS 𝒴)
  exact ⟨isLocallyOfFiniteType_of_twoIso B S hS
      (Bicategory.InducedBicategory.isoHom (Bicategory.rightUnitor k)) h.1,
    isQuasiCompactMorphism_of_comp_of_isSurjective B S hS (𝟙 𝒳) (k ≫ 𝟙 𝒴) k
      (Bicategory.leftUnitor _ ≪≫ Bicategory.rightUnitor k) (isSurjective_id B S hS 𝒳) h.2⟩

end General


section ChangeOfBase

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS') {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Separatedness (Stacks 04YW) is carried along Construction A.** -/
theorem isSeparated_changeBase (f : 𝒳 ⟶ 𝒴) (hf : IsSeparated B S hS f) :
    IsSeparated B S' hS' (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f) :=
  isProper_relativeDiagonal_changeBase B S S' hS hS' g 𝒳.val 𝒴.val f.hom hf

/-- **Quasi-compactness (Stacks 050U) is carried along Construction A.** A quasi-compact test
stack over `S'` mapping to Construction A of `𝒴` is, together with that 1-morphism, Construction A
of a test stack over `S` by the bijections of Stacks 04X5; the base change over `S'` receives an
equivalence from Construction A of the base change over `S`. -/
theorem isQuasiCompactMorphism_changeBase (f : 𝒳 ⟶ 𝒴) (hf : IsQuasiCompactMorphism B S hS f) :
    IsQuasiCompactMorphism B S' hS'
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f) := by
  intro 𝒵' z' h𝒵'
  obtain ⟨𝒵, h⟩ := (algebraicStackConstructionObjEquiv B S S' hS hS' g).surjective
    ⟨𝒵', z'.hom ≫ changeBaseStructureHom B S S' hS hS' g 𝒴⟩
  obtain rfl : changeBaseAlgebraicStack B S S' hS hS' g 𝒵 = 𝒵' := congrArg Sigma.fst h
  have h2 := (eq_of_heq (Sigma.mk.inj h).2).symm
  let z₀ : 𝒵 ⟶ 𝒴 :=
    (algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒵 𝒴).symm ⟨z'.hom, h2⟩
  have key := (isQuasiCompactStack_changeBaseAlgebraicStack_iff B S S' hS hS' g
    (twoFibreProductAlgebraicStack B S hS z₀ f)).2
    (hf 𝒵 z₀ ((isQuasiCompactStack_changeBaseAlgebraicStack_iff B S S' hS hS' g 𝒵).1 h𝒵'))
  let e : changeBaseAlgebraicStack B S S' hS hS' g (twoFibreProductAlgebraicStack B S hS z₀ f) ⟶
      twoFibreProductAlgebraicStack B S' hS' z'
        (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f) :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (changeBaseTwoFibreProductHom B S S' hS hS' g 𝒴.val 𝒵.val 𝒳.val z₀.hom.hom f.hom.hom))
  have : e.hom.hom.toFunctor.EssSurj :=
    (isEquivalence_changeBaseTwoFibreProductHom B S S' hS hS' g 𝒴.val 𝒵.val 𝒳.val
      z₀.hom.hom f.hom.hom).essSurj
  exact isQuasiCompactStack_of_essSurj B S' hS' e key

/-- **Smoothness out of an algebraic space is carried along Construction A.** A smooth
1-morphism `c` from the stack of an algebraic space `W` over `S` gives a smooth 1-morphism from the
stack of `Λ_g W` over `S'`: Construction A of `c` read through the equivalence `Λ_g W ≃ W`. -/
private theorem isRelativelySmooth_changeBaseFibredCategoryInv_comp_changeBaseHom
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    {𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (c : fibredCategory B S hS W ⟶ 𝒵.val)
    (hc : Stack.IsRelativelySmooth B S hS c) :
    Stack.IsRelativelySmooth B S' hS'
      (Bicategory.InducedBicategory.mkHom (changeBaseFibredCategoryInv B S S' hS hS' g W) ≫
        changeBaseHom B S S' hS hS' g c :
          fibredCategory B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj W) ⟶
            changeBaseFiberedInGroupoids B S S' hS hS' g 𝒵.val) := by
  obtain ⟨hcrep, hcrel⟩ := hc
  have hcrel' := (Stack.hasRelativeProperty_smooth_changeBaseHom_iff B S S' hS hS' g
    (@AlgebraicGeometry.Smooth) c hcrep).2 hcrel
  let IW : fibredCategory B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj W) ⟶
      changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS W) :=
    Bicategory.InducedBicategory.mkHom (changeBaseFibredCategoryInv B S S' hS hS' g W)
  have : Functor.IsEquivalence IW.hom.toFunctor :=
    isEquivalence_changeBaseFibredCategoryInv B S S' hS hS' g W
  have : Functor.IsEquivalence
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒵.val).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 _))
  refine ⟨isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S' hS'
    (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒵).property
    (isRepresentableByAlgebraicSpace_fibredCategory B S' hS' _
      (isAlgebraicSpace_viewOver B S S' hS hS' g W hW)) _, ?_⟩
  exact Stack.relativeProperty_of_equivalences B S' hS' (Space.smoothMorphismProperty B S' hS')
    (𝒳' := fibredCategory B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj W))
    (𝒳 := changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS W))
    (𝒴' := changeBaseFiberedInGroupoids B S S' hS hS' g 𝒵.val)
    (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g 𝒵.val)
    (Bicategory.InducedBicategory.mkHom (changeBaseFibredCategoryInv B S S' hS hS' g W) ≫
        changeBaseHom B S S' hS hS' g c).hom
    (changeBaseHom B S S' hS hS' g c).hom
    IW.hom (BasedFunctor.id _) (Iso.refl _) hcrel'

/-- **Local finite type (Stacks 06FS) is carried along Construction A.** A smooth diagram of
Stacks 06FM over `S` for `f`, with left vertical 1-morphism surjective on objects, is carried to
one over `S'` for Construction A of `f`: its two algebraic spaces are replaced by their
lower-shriek extensions, its two vertical 1-morphisms by Construction A of them read through the
equivalence `Λ_g U ≃ U` of categories of elements (smoothness and surjectivity on objects being
unchanged by Construction A and by an equivalence of the source), and its top horizontal
morphism `h` by `Λ_g h`, which is locally of finite type with `h`. -/
theorem isLocallyOfFiniteType_changeBase (f : 𝒳 ⟶ 𝒴) (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S' hS'
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f) := by
  obtain ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ha, has, hb, hP⟩ :=
    (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳.property 𝒴.property f.hom).1 hf
  refine (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S' hS'
      (fun _ _ h => Space.IsLocallyOfFiniteType B S' hS' h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S' hS')
      (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳).property
      (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒴).property
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f).hom).2 ?_
  let Iu : fibredCategory B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj U) ⟶
      changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS U) :=
    Bicategory.InducedBicategory.mkHom (changeBaseFibredCategoryInv B S S' hS hS' g U)
  let Iv : fibredCategory B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj V) ⟶
      changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS V) :=
    Bicategory.InducedBicategory.mkHom (changeBaseFibredCategoryInv B S S' hS hS' g V)
  have hL : (associatedMap B S' hS' ((OverShriek.relocalizePresheafFunctor g).map h)).1 ≫
      Iv ≫ changeBaseHom B S S' hS hS' g b =
      Iu ≫ changeBaseHom B S S' hS hS' g ((associatedMap B S hS h).1 ≫ b) :=
    Bicategory.InducedBicategory.hom_ext (congrArg
      (fun q => BasedFunctor.comp q (changeBaseFunctor B S S' hS hS' g b.hom))
      (associatedMap_relocalize_comp_inv B S S' hS hS' g h))
  refine ⟨(OverShriek.relocalizePresheafFunctor g).obj U,
    (OverShriek.relocalizePresheafFunctor g).obj V,
    isAlgebraicSpace_viewOver B S S' hS hS' g U hU,
    isAlgebraicSpace_viewOver B S S' hS hS' g V hV,
    Iu ≫ changeBaseHom B S S' hS hS' g a,
    Iv ≫ changeBaseHom B S S' hS hS' g b, (OverShriek.relocalizePresheafFunctor g).map h,
    ⟨eqToIso hL ≪≫ Bicategory.whiskerLeftIso Iu (changeBaseHomIso B S S' hS hS' g η)⟩,
    isRelativelySmooth_changeBaseFibredCategoryInv_comp_changeBaseHom B S S' hS hS' g hU
      (𝒵 := 𝒳) a ha, ?_,
    isRelativelySmooth_changeBaseFibredCategoryInv_comp_changeBaseHom B S S' hS hS' g hV
      (𝒵 := 𝒴) b hb,
    (Space.isLocallyOfFiniteType_relocalize_iff B S hS S' hS' g h).2 hP⟩
  exact Stack.isSurjectiveOnObjects_comp B S' hS' _ _ _
    (CatFiberedInGroupoids.homFunctor Iu)
    (CatFiberedInGroupoids.homFunctor (changeBaseHom B S S' hS hS' g a))
    (CatFiberedInGroupoids.homFunctor_comp_p (changeBaseHom B S S' hS hS' g a))
    (Stack.isSurjectiveOnObjects_of_isEquivalence B S' hS' Iu
      (isEquivalence_changeBaseFibredCategoryInv B S S' hS hS' g U))
    ((Stack.isSurjectiveOnObjects_changeBaseHom_iff B S S' hS hS' g a).2 has)

/-- **Finite type (Stacks 06FS, part (2)) is carried along Construction A.** -/
theorem isFiniteType_changeBase (f : 𝒳 ⟶ 𝒴) (hf : IsFiniteType B S hS f) :
    IsFiniteType B S' hS' (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f) :=
  ⟨isLocallyOfFiniteType_changeBase B S S' hS hS' g f hf.1,
    isQuasiCompactMorphism_changeBase B S S' hS hS' g f hf.2⟩

/-- The comparison of Construction A of the stack of an algebraic space with the stack of its
lower-shriek extension has an underlying functor which is an equivalence. -/
theorem isEquivalence_changeBaseAlgebraicSpaceStackHom {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) :
    Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor
      (changeBaseAlgebraicSpaceStackHom.{u, w} B S S' hS hS' g hY).hom) :=
  isEquivalence_changeBaseFibredCategoryHom B S S' hS hS' g Y

/-- **The separation hypothesis of Stacks 0CQ8 survives a change of base scheme.** If
`f : 𝒳 ⟶ Y` is separated over `S`, then `f` viewed over `S'`
(`AlgebraicGeometry.Stack.changeBaseToAlgebraicSpace`) is separated: Construction A preserves
separatedness, and the comparison with the stack of `Λ_g Y` is fully faithful. -/
theorem isSeparated_changeBaseToAlgebraicSpace {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : IsSeparated B S hS f) :
    IsSeparated B S' hS' (changeBaseToAlgebraicSpace.{u, w} B S S' hS hS' g hY f) := by
  have := isEquivalence_changeBaseAlgebraicSpaceStackHom.{u, w} B S S' hS hS' g hY
  exact isSeparated_comp_of_full_of_faithful B S' hS' _ _
    (isSeparated_changeBase B S S' hS hS' g f hf)

/-- **The finiteness hypothesis of Stacks 0CQ8 survives a change of base scheme.** If
`f : 𝒳 ⟶ Y` is of finite type over `S`, then `f` viewed over `S'`
(`AlgebraicGeometry.Stack.changeBaseToAlgebraicSpace`) is of finite type: Construction A
preserves finite type, and the comparison with the stack of `Λ_g Y` is an equivalence, hence of
finite type. -/
theorem isFiniteType_changeBaseToAlgebraicSpace {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : IsFiniteType B S hS f) :
    IsFiniteType B S' hS' (changeBaseToAlgebraicSpace.{u, w} B S S' hS hS' g hY f) :=
  isFiniteType_comp B S' hS' _ _ (isFiniteType_changeBase B S S' hS hS' g f hf)
    (isFiniteType_of_isEquivalence B S' hS' _
      (isEquivalence_changeBaseAlgebraicSpaceStackHom.{u, w} B S S' hS hS' g hY))

end ChangeOfBase

end AlgebraicGeometry.Stack.AlgebraicStacks
