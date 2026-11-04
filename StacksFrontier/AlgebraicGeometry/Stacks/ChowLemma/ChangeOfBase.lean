module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaReductions
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemma.ChangeOfBaseDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemma.ChangeOfBaseSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemma.EquivalencePrecomposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces

/-!
# The conclusion of Chow's lemma for stacks (Stacks 0CQ8) and a change of base scheme

Let `g : S ⟶ S'` be a morphism of a big fppf site, for instance `S ⟶ Spec(ℤ)`, and let
`f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space over `S`. This file
views `f` over `S'` and proves that the conclusion of Stacks 0CQ8 for the view of `f` gives the
conclusion for `f`.

## Main definitions

* `AlgebraicGeometry.Stack.changeBaseAlgebraicSpaceStackHom`: Construction A of the stack of an
  algebraic space `Y` is the stack of its lower-shriek extension `Λ_g Y`.
* `AlgebraicGeometry.Stack.changeBaseToAlgebraicSpace`: the view of `f : 𝒳 ⟶ Y` over `S'`, a
  1-morphism to the algebraic space `Λ_g Y`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_changeBase`: the
  conclusion of Stacks 0CQ8 descends from `S'` to `S`.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **Construction A of the algebraic stack of an algebraic space is the algebraic stack of its
lower-shriek extension**, as a 1-morphism of algebraic stacks over `S'`. Its underlying functor is
`AlgebraicGeometry.Stack.changeBaseFibredCategoryHom`, an equivalence. -/
noncomputable def changeBaseAlgebraicSpaceStackHom {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) :
    changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g (algebraicSpaceStack.{u, w} B S hS Y hY) ⟶
      algebraicSpaceStack.{u, w} B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj Y)
        (isAlgebraicSpace_viewOver B S S' hS hS' g Y hY) :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (changeBaseFibredCategoryHom B S S' hS hS' g Y))

/-- **A 1-morphism to an algebraic space, viewed over `S'`.** For `f : 𝒳 ⟶ Y` over `S`, the
1-morphism of algebraic stacks over `S'` from Construction A of `𝒳` to the algebraic space
`Λ_g Y`: Construction A of `f`, followed by
`AlgebraicGeometry.Stack.changeBaseAlgebraicSpaceStackHom`. -/
noncomputable abbrev changeBaseToAlgebraicSpace {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) :
    changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳 ⟶
      algebraicSpaceStack.{u, w} B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj Y)
        (isAlgebraicSpace_viewOver B S S' hS hS' g Y hY) :=
  changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f ≫
    changeBaseAlgebraicSpaceStackHom.{u, w} B S S' hS hS' g hY

/-- The 1-morphism attached to an isomorphism of presheaves has an underlying functor which is an
equivalence. -/
theorem isEquivalence_associatedMap_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) :
    Functor.IsEquivalence (associatedMap B S hS e.hom).1.hom.toFunctor := by
  have h₁ : (associatedMap B S hS e.hom).1 ≫ (associatedMap B S hS e.inv).1 = 𝟙 _ := by
    rw [← associatedMap_comp, e.hom_inv_id]
    exact hom_ext_of_obj B S hS fun x => rfl
  have h₂ : (associatedMap B S hS e.inv).1 ≫ (associatedMap B S hS e.hom).1 = 𝟙 _ := by
    rw [← associatedMap_comp, e.inv_hom_id]
    exact hom_ext_of_obj B S hS fun x => rfl
  exact (CategoryTheory.Equivalence.mk (associatedMap B S hS e.hom).1.hom.toFunctor
    (associatedMap B S hS e.inv).1.hom.toFunctor
    (eqToIso (congrArg (fun k => k.hom.toFunctor) h₁).symm)
    (eqToIso (congrArg (fun k => k.hom.toFunctor) h₂))).isEquivalence_functor

namespace AlgebraicStacks

/-- Rewriting the middle of a composite of functors along `α ⋙ β ⋙ ε = κ` and `κ' = ψ ⋙ κ`. -/
private theorem comp_comp_comp_eq_of_eq {C₁ C₂ C₃ C₄ C₅ C₆ C₇ : Type*} [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅] [Category C₆] [Category C₇] {ϕ : C₁ ⥤ C₂}
    {ψ : C₂ ⥤ C₃} {α : C₃ ⥤ C₄} {β : C₄ ⥤ C₅} {ε : C₅ ⥤ C₆} {κ : C₃ ⥤ C₆} {κ' : C₂ ⥤ C₆}
    {T : C₆ ⥤ C₇} (hκ' : κ' = ψ ⋙ κ) (h : α ⋙ β ⋙ ε = κ) :
    ϕ ⋙ ψ ⋙ (α ⋙ β ⋙ ε) ⋙ T = ϕ ⋙ κ' ⋙ T := by
  subst h hκ'
  rfl

/-- The underlying functor of `associatedMap` is compatible with composition. -/
private theorem associatedMap_comp_toFunctor {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ H) :
    (associatedMap B S hS (a ≫ b)).1.hom.toFunctor =
      (associatedMap B S hS a).1.hom.toFunctor ⋙ (associatedMap B S hS b).1.hom.toFunctor :=
  congrArg (fun q => q.hom.toFunctor) (associatedMap_comp B S hS a b)

/-- The underlying functor of a 1-morphism over `S'` out of `Λ_g X₀`, followed by `f`, is that of
Construction A of a morphism `i₀ ≫ g₀ : X₀ ⟶ Y` whose lower-shriek extension factors through it. -/
theorem changeBaseFibredCategoryHom_comp_eq_associatedMap {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    {X Xbar : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S' hS' X)
    (a : algebraicSpaceStack.{u, w} B S' hS' X hX ⟶
      changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳)
    {X₀ Xbar₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (θ : (OverShriek.relocalizePresheafFunctor g).obj X₀ ≅ X) (i : X ⟶ Xbar)
    (gb : Xbar ⟶ (OverShriek.relocalizePresheafFunctor g).obj Y) (i₀ : X₀ ⟶ Xbar₀)
    (g₀ : Xbar₀ ⟶ Y)
    (hΛ : (OverShriek.relocalizePresheafFunctor g).map (i₀ ≫ g₀) = θ.hom ≫ i ≫ gb)
    (hea' : a.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor ⋙
      (changeBaseFibredCategoryHom B S S' hS hS' g Y).toFunctor =
      (associatedMap B S' hS' (i ≫ gb)).1.hom.toFunctor) :
    ((changeBaseFibredCategoryHom B S S' hS hS' g X₀).toFunctor ⋙
      (associatedMap B S' hS' θ.hom).1.hom.toFunctor ⋙ a.hom.hom.toFunctor) ⋙
        f.hom.hom.toFunctor = (associatedMap B S hS (i₀ ≫ g₀)).1.hom.toFunctor := by
  let EX := (changeBaseFibredCategoryHom B S S' hS hS' g X₀).toFunctor
  let EY := (changeBaseFibredCategoryHom B S S' hS hS' g Y).toFunctor
  let EY' := (changeBaseFibredCategoryInv B S S' hS hS' g Y).toFunctor
  let Aθ := (associatedMap B S' hS' θ.hom).1.hom.toFunctor
  let A₀ := (associatedMap B S hS (i₀ ≫ g₀)).1.hom.toFunctor
  have hEE : EY ⋙ EY' = 𝟭 _ :=
    congrArg (fun q => q.toFunctor) (changeBaseFibredCategoryHom_comp_inv B S S' hS hS' g Y)
  have hnat : A₀ ⋙ EY = EX ⋙ (associatedMap B S' hS' ((OverShriek.relocalizePresheafFunctor g).map
      (i₀ ≫ g₀))).1.hom.toFunctor :=
    congrArg (fun q => q.toFunctor)
      (changeBaseFunctor_associatedMap_comp B S S' hS hS' g (i₀ ≫ g₀))
  have h1 : ((EX ⋙ Aθ ⋙ a.hom.hom.toFunctor) ⋙ f.hom.hom.toFunctor) =
      EX ⋙ Aθ ⋙ (a.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor ⋙ EY) ⋙ EY' :=
    (Functor.comp_id _).symm.trans
      (congrArg (fun G => (EX ⋙ Aθ ⋙ a.hom.hom.toFunctor) ⋙ f.hom.hom.toFunctor ⋙ G)
        hEE.symm)
  have h2 : EX ⋙ Aθ ⋙ (a.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor ⋙ EY) ⋙ EY' =
      EX ⋙ (associatedMap B S' hS' (θ.hom ≫ i ≫ gb)).1.hom.toFunctor ⋙ EY' :=
    comp_comp_comp_eq_of_eq (associatedMap_comp_toFunctor B S' hS' _ _) hea'
  have h3 : EX ⋙ (associatedMap B S' hS' (θ.hom ≫ i ≫ gb)).1.hom.toFunctor ⋙ EY' =
      (A₀ ⋙ EY) ⋙ EY' :=
    (congrArg (fun m => EX ⋙ (associatedMap B S' hS' m).1.hom.toFunctor ⋙ EY') hΛ.symm).trans
      (congrArg (fun G => G ⋙ EY') hnat.symm)
  exact h1.trans (h2.trans (h3.trans ((congrArg (fun G => A₀ ⋙ G) hEE).trans (Functor.comp_id _))))

/-- A 1-morphism over `S'` out of `Λ_g X₀`, through `θ : Λ_g X₀ ≅ X` and `a`, is compatible with
the structure 1-morphisms to the stack of `S/S'`, when `a ≫ f` is Construction A of `i ≫ gb` and
`Λ_g (i₀ ≫ g₀) = θ ≫ i ≫ gb`. -/
theorem changeBaseStructureHom_comp_eq {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    {X Xbar : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S' hS' X)
    (a : algebraicSpaceStack.{u, w} B S' hS' X hX ⟶
      changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳)
    {X₀ Xbar₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX₀ : IsAlgebraicSpace B S hS X₀)
    (θ : (OverShriek.relocalizePresheafFunctor g).obj X₀ ≅ X) (i : X ⟶ Xbar)
    (gb : Xbar ⟶ (OverShriek.relocalizePresheafFunctor g).obj Y) (i₀ : X₀ ⟶ Xbar₀)
    (g₀ : Xbar₀ ⟶ Y)
    (hΛ : (OverShriek.relocalizePresheafFunctor g).map (i₀ ≫ g₀) = θ.hom ≫ i ≫ gb)
    (hea' : a.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor ⋙
      (changeBaseFibredCategoryHom B S S' hS hS' g Y).toFunctor =
      (associatedMap B S' hS' (i ≫ gb)).1.hom.toFunctor) :
    ((changeBaseAlgebraicSpaceStackHom.{u, w} B S S' hS hS' g hX₀ ≫
      algebraicSpaceStackMap.{u, w} B S' hS' (isAlgebraicSpace_viewOver B S S' hS hS' g X₀ hX₀)
        hX θ.hom) ≫ a).hom ≫ changeBaseStructureHom B S S' hS hS' g 𝒳 =
      changeBaseStructureHom B S S' hS hS' g (algebraicSpaceStack.{u, w} B S hS X₀ hX₀) := by
  refine Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext' ?_)
  let EX := (changeBaseFibredCategoryHom B S S' hS hS' g X₀).toFunctor
  let EY := (changeBaseFibredCategoryHom B S S' hS hS' g Y).toFunctor
  let σY := (relocalizeElementsStructureHom B S S' hS hS' g Y).toFunctor
  let σX := (relocalizeElementsStructureHom B S S' hS hS' g X₀).toFunctor
  let Aθ := (associatedMap B S' hS' θ.hom).1.hom.toFunctor
  let ι := Over.iteratedSliceBackward (Over.mk g)
  have hf : f.hom.hom.toFunctor ⋙ (fibredCategory B S hS Y).val.p = 𝒳.val.val.p :=
    f.hom.hom.w
  have hLY : EY ⋙ σY = (fibredCategory B S hS Y).val.p ⋙ ι :=
    congrArg (fun q => q.toFunctor) (changeBaseFibredCategoryHom_comp_structureHom
      B S S' hS hS' g Y)
  have hLX : EX ⋙ σX = (fibredCategory B S hS X₀).val.p ⋙ ι :=
    congrArg (fun q => q.toFunctor) (changeBaseFibredCategoryHom_comp_structureHom
      B S S' hS hS' g X₀)
  have hm : (θ.hom ≫ i ≫ gb) ≫ OverShriek.relocalizeToYoneda g Y =
      OverShriek.relocalizeToYoneda g X₀ := by
    rw [← hΛ]
    exact relocalizeToYoneda_naturality B S S' hS hS' g (i₀ ≫ g₀)
  have hL3 : (associatedMap B S' hS' (θ.hom ≫ i ≫ gb)).1.hom.toFunctor ⋙ σY = σX :=
    congrArg (fun q => q.toFunctor) (associatedMap_comp_structureHom B S S' hS hS' g
      (θ.hom ≫ i ≫ gb) hm)
  have h1 : (EX ⋙ Aθ ⋙ a.hom.hom.toFunctor) ⋙ 𝒳.val.val.p ⋙ ι =
      EX ⋙ Aθ ⋙ (a.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor ⋙ EY) ⋙ σY :=
    (congrArg (fun G => (EX ⋙ Aθ ⋙ a.hom.hom.toFunctor) ⋙ G ⋙ ι) hf.symm).trans
      (congrArg (fun G => (EX ⋙ Aθ ⋙ a.hom.hom.toFunctor) ⋙ f.hom.hom.toFunctor ⋙ G)
        hLY.symm)
  have h2 : EX ⋙ Aθ ⋙ (a.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor ⋙ EY) ⋙ σY =
      EX ⋙ (associatedMap B S' hS' (θ.hom ≫ i ≫ gb)).1.hom.toFunctor ⋙ σY :=
    comp_comp_comp_eq_of_eq (associatedMap_comp_toFunctor B S' hS' _ _) hea'
  exact h1.trans (h2.trans ((congrArg (fun G => EX ⋙ G) hL3).trans hLX))

/-- **The conclusion of Stacks 0CQ8 descends along a change of base scheme.** Let `g : S ⟶ S'` be
a morphism of the big fppf site and `f : 𝒳 ⟶ Y` a 1-morphism from an algebraic stack to an
algebraic space over `S`. If the conclusion of Stacks 0CQ8 holds for `f` viewed over `S'` (the
1-morphism `AlgebraicGeometry.Stack.changeBaseToAlgebraicSpace` from Construction A of `𝒳` to the
lower-shriek extension `Λ_g Y`), it holds for `f`.

The algebraic spaces `X ⊆ X̄` of a diagram over `S'` map to `S`, through `X̄ ⟶ Λ_g Y`, so they
descend to `S` by Stacks 04SG, and the open immersion and the proper morphism descend with them
(`AlgebraicGeometry.Space.exists_descent_isOpenImmersion_isProper`). The 1-morphism `X ⟶ 𝒳` over
`S'` is compatible with the two structure 1-morphisms to the stack of `S/S'`, because the 2-cell of
the diagram forces it — a 2-morphism into the category of elements of a presheaf is an identity —
so it is Construction A of a 1-morphism `X₀ ⟶ 𝒳` over `S` by the bijection on 1-morphisms of
Stacks 04X5, up to the equivalence between Construction A of `X₀` and `Λ_g X₀ ≅ X`. Properness
and surjectivity descend along Construction A for a 1-morphism out of an algebraic space
(`AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_changeBase`,
`AlgebraicGeometry.Stack.AlgebraicStacks.isSurjective_of_changeBase`), and the 2-cell over `S`
is an equality of 1-morphisms into the category of elements of `Y`. -/
theorem hasChowCover_of_changeBase {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (h : HasChowCover B S' hS' (isAlgebraicSpace_viewOver B S S' hS hS' g Y hY)
      (changeBaseToAlgebraicSpace.{u, w} B S S' hS hS' g hY f)) :
    HasChowCover B S hS hY f := by
  obtain ⟨X, Xbar, hX, hXbar, a, i, gb, ha, has, hi, hg, ⟨ea⟩⟩ := h
  obtain ⟨X₀, Xbar₀, hX₀, hXbar₀, θ, i₀, g₀, hi₀, hg₀, hΛ⟩ :=
    Space.exists_descent_isOpenImmersion_isProper B S S' hS hS' g hY hX hXbar i gb hi hg
  let k := changeBaseAlgebraicSpaceStackHom.{u, w} B S S' hS hS' g hX₀ ≫
    algebraicSpaceStackMap.{u, w} B S' hS' (isAlgebraicSpace_viewOver B S S' hS hS' g X₀ hX₀)
      hX θ.hom
  have hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom) := by
    have := isEquivalence_associatedMap_of_iso B S' hS' θ
    exact (inferInstance : Functor.IsEquivalence
      ((changeBaseFibredCategoryHom B S S' hS hS' g X₀).toFunctor ⋙
        (associatedMap B S' hS' θ.hom).1.hom.toFunctor))
  have hea : (a ≫ changeBaseToAlgebraicSpace.{u, w} B S S' hS hS' g hY f).hom =
      (algebraicSpaceStackMap.{u, w} B S' hS' hX
        (isAlgebraicSpace_viewOver B S S' hS hS' g Y hY) (i ≫ gb)).hom :=
    hom_eq_of_hom₂ B S' hS' (Bicategory.InducedBicategory.isoHom ea).hom
  have hea' : a.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor ⋙
      (changeBaseFibredCategoryHom B S S' hS hS' g Y).toFunctor =
      (associatedMap B S' hS' (i ≫ gb)).1.hom.toFunctor :=
    congrArg (fun q => q.hom.toFunctor) hea
  let a₀ : algebraicSpaceStack.{u, w} B S hS X₀ hX₀ ⟶ 𝒳 :=
    (algebraicStackConstructionHomEquiv B S S' hS hS' g _ 𝒳).symm
      ⟨(k ≫ a).hom,
        changeBaseStructureHom_comp_eq B S S' hS hS' g hY f hX a hX₀ θ i gb i₀ g₀ hΛ hea'⟩
  have hrep : IsRepresentableByAlgebraicSpaces B S hS a₀.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS X₀ hX₀) a₀.hom
  refine ⟨X₀, Xbar₀, hX₀, hXbar₀, a₀, i₀, g₀,
    isProper_of_changeBase B S S' hS hS' g a₀ hrep
      (isProper_comp_of_isEquivalence B S' hS' k a hk ha),
    isSurjective_of_changeBase B S S' hS hS' g a₀
      (isSurjective_comp_of_isEquivalence B S' hS' k a hk has),
    hi₀, hg₀, ⟨eqToIso ?_⟩⟩
  exact Bicategory.InducedBicategory.hom_ext (Bicategory.InducedBicategory.hom_ext
    (BasedCategory.BasedFunctor.ext'
      (changeBaseFibredCategoryHom_comp_eq_associatedMap B S S' hS hS' g hY f hX a θ i gb i₀ g₀
        hΛ hea')))

end AlgebraicStacks

end AlgebraicGeometry.Stack
