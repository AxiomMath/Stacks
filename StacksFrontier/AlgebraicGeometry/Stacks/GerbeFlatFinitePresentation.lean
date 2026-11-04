module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatDescentAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeIsomGroupSection
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Gerbes with a flat local section are flat and locally of finite presentation

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which exhibits `𝒳` as a gerbe over `𝒴`
(**Stacks 06QC**), and whose base change along some surjective, flat, locally finitely presented
`g : 𝒵 ⟶ 𝒴` admits a section which is flat and locally of finite presentation, is flat and
locally of finite presentation. The statement of **Stacks 06QI** without the local section is
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasFlatLfpLocalSection`: a 1-morphism has a *flat
  local section* when, after a surjective flat locally finitely presented base change, it admits
  a section which is flat and locally of finite presentation.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_of_twoIso` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_iff_of_twoIso`: two
  2-isomorphic 1-morphisms are flat together, and locally of finite presentation together.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_section` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_section`: a
  1-morphism admitting a surjective flat section is flat, and admitting a surjective flat
  locally finitely presented one is locally of finite presentation.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isGerbeOver` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isGerbeOver`: a gerbe
  with a flat local section is flat and locally of finite presentation.

## Implementation notes

The base change in `AlgebraicGeometry.Stack.AlgebraicStacks.HasFlatLfpLocalSection` is the
*canonical* 2-fibre product of Stacks 04T2; its swap is a 2-fibre product of the reversed cospan
(`CategoryTheory.Bicategory.isTwoFibreProduct_swap`).

## References

* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q0](https://stacks.math.columbia.edu/tag/06Q0)
* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 06Q9](https://stacks.math.columbia.edu/tag/06Q9)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 06QH](https://stacks.math.columbia.edu/tag/06QH)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The identity 1-morphism of an algebraic stack over `S` is flat.** -/
private theorem isFlat_id (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    IsFlat B S hS (𝟙 𝒵) := by
  obtain ⟨V, hV, b, hbsm, hbsu⟩ :=
    Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS
      𝒵.property
  obtain ⟨κ⟩ := Stack.nonempty_twoIso_associatedMap_id B S hS V
  refine ⟨V, V, hV, hV, b, b, 𝟙 V, ⟨?_⟩, hbsm, hbsu, hbsm, Space.isFlat_id B S hS hV⟩
  exact Bicategory.whiskerRightIso κ b ≪≫ Bicategory.leftUnitor b ≪≫
    (Bicategory.rightUnitor b).symm

/-- **Flatness depends only on the 2-isomorphism class of a 1-morphism of algebraic stacks over
`S`.** -/
private theorem isFlat_of_twoIso {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f g : 𝒳 ⟶ 𝒴) (e : f.hom ≅ g.hom) (hf : IsFlat B S hS f) :
    IsFlat B S hS g :=
  (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS g).2
    (Stack.hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS
      (fun _ _ h => Space.IsFlat B S hS h) e
      ((isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).1 hf))

/-- **Being locally of finite presentation depends only on the 2-isomorphism class of a
1-morphism of algebraic stacks over `S`.** -/
private theorem isLocallyOfFinitePresentation_of_twoIso
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f g : 𝒳 ⟶ 𝒴) (e : f.hom ≅ g.hom) (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B S hS g :=
  let iff := fun m => Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    𝒳.property 𝒴.property m
  (iff g.hom).2
    (Stack.hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h) e ((iff f.hom).1 hf))

/-- **Two 2-isomorphic 1-morphisms of algebraic stacks over `S` are flat together.** -/
theorem isFlat_iff_of_twoIso {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f g : 𝒳 ⟶ 𝒴) (e : f.hom ≅ g.hom) :
    IsFlat B S hS f ↔ IsFlat B S hS g :=
  ⟨isFlat_of_twoIso B S hS f g e, isFlat_of_twoIso B S hS g f e.symm⟩

/-- **Two 2-isomorphic 1-morphisms of algebraic stacks over `S` are locally of finite
presentation together.** -/
theorem isLocallyOfFinitePresentation_iff_of_twoIso
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f g : 𝒳 ⟶ 𝒴) (e : f.hom ≅ g.hom) :
    IsLocallyOfFinitePresentation B S hS f ↔ IsLocallyOfFinitePresentation B S hS g :=
  ⟨isLocallyOfFinitePresentation_of_twoIso B S hS f g e,
    isLocallyOfFinitePresentation_of_twoIso B S hS g f e.symm⟩

/-! ### Descent along a section -/

/-- **A 1-morphism of algebraic stacks over `S` admitting a surjective flat section is flat.** -/
theorem isFlat_of_section {𝒲 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (π : 𝒲 ⟶ 𝒵) (s : 𝒵 ⟶ 𝒲) (e : s ≫ π ≅ 𝟙 𝒵)
    (hssurj : Stack.IsSurjective B S hS s) (hsflat : IsFlat B S hS s) :
    IsFlat B S hS π :=
  isFlat_of_isSurjective_of_isFlat_comp B S hS s π
    (isFlat_of_twoIso B S hS (𝟙 𝒵) (s ≫ π)
      (Bicategory.InducedBicategory.isoHom e.symm) (isFlat_id B S hS 𝒵))
    hssurj hsflat

/-- **A 1-morphism of algebraic stacks over `S` admitting a surjective flat section which is
locally of finite presentation is locally of finite presentation.** -/
theorem isLocallyOfFinitePresentation_of_section {𝒲 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (π : 𝒲 ⟶ 𝒵) (s : 𝒵 ⟶ 𝒲) (e : s ≫ π ≅ 𝟙 𝒵)
    (hssurj : Stack.IsSurjective B S hS s) (hsflat : IsFlat B S hS s)
    (hslfp : IsLocallyOfFinitePresentation B S hS s) :
    IsLocallyOfFinitePresentation B S hS π :=
  isLocallyOfFinitePresentation_of_comp_of_fppf B S hS s π
    (isLocallyOfFinitePresentation_of_twoIso B S hS (𝟙 𝒵) (s ≫ π)
      (Bicategory.InducedBicategory.isoHom e.symm)
      (isLocallyOfFinitePresentation_id B S hS 𝒵))
    hssurj hsflat hslfp

/-! ### Flatness and local finite presentation from a flat local section -/

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` has a *flat local section* when there
are an algebraic stack `𝒵` over `S` and a surjective, flat, locally finitely presented
1-morphism `g : 𝒵 ⟶ 𝒴` such that the base change `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` of `f` along `g` admits a
section which is flat and locally of finite presentation. -/
abbrev HasFlatLfpLocalSection {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴),
    Stack.IsSurjective B S hS g ∧ IsFlat B S hS g ∧
      IsLocallyOfFinitePresentation B S hS g ∧
      ∃ s : 𝒵 ⟶ (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt,
        Nonempty (s ≫ (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd ≅ 𝟙 𝒵) ∧
          IsFlat B S hS s ∧ IsLocallyOfFinitePresentation B S hS s

/-- The base change of a gerbe 1-morphism along a 1-morphism with a flat, locally finitely
presented section is flat and locally of finite presentation. -/
private theorem isFlat_and_isLocallyOfFinitePresentation_snd_of_isGerbeOver
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hf : IsGerbeOver B S hS f)
    (s : 𝒵 ⟶ (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt)
    (e : s ≫ (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd ≅ 𝟙 𝒵)
    (hsflat : IsFlat B S hS s)
    (hslfp : IsLocallyOfFinitePresentation B S hS s) :
    IsFlat B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd ∧
      IsLocallyOfFinitePresentation B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd := by
  have hgerbe : IsGerbeOver B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd :=
    isGerbeOver_of_isTwoFibreProduct B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g)
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g) hf
  have hssurj : Stack.IsSurjective B S hS s :=
    Stack.isSurjective_of_section_of_isGerbeOver B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd s e hgerbe
  exact ⟨isFlat_of_section B S hS _ s e hssurj hsflat,
    isLocallyOfFinitePresentation_of_section B S hS _ s e hssurj hsflat hslfp⟩

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which exhibits `𝒳` as a gerbe over `𝒴`
and has a flat local section is flat. -/
theorem isFlat_of_isGerbeOver {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsGerbeOver B S hS f) (hloc : HasFlatLfpLocalSection B S hS f) :
    IsFlat B S hS f := by
  obtain ⟨𝒵, g, hgsurj, hgflat, -, s, ⟨e⟩, hsflat, hslfp⟩ := hloc
  exact isFlat_twoFibreProduct_fst_descent B S hS f g
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).swap
    (Bicategory.isTwoFibreProduct_swap
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g))
    hgsurj hgflat
    (isFlat_and_isLocallyOfFinitePresentation_snd_of_isGerbeOver B S hS f g hf s e
      hsflat hslfp).1

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which exhibits `𝒳` as a gerbe over `𝒴`
and has a flat local section is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_of_isGerbeOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsGerbeOver B S hS f) (hloc : HasFlatLfpLocalSection B S hS f) :
    IsLocallyOfFinitePresentation B S hS f := by
  obtain ⟨𝒵, g, hgsurj, hgflat, hglfp, s, ⟨e⟩, hsflat, hslfp⟩ := hloc
  exact isLocallyOfFinitePresentation_of_baseChange B S hS f g hgsurj hgflat hglfp
    (isFlat_and_isLocallyOfFinitePresentation_snd_of_isGerbeOver B S hS f g hf s e
      hsflat hslfp).2

end AlgebraicGeometry.Stack.AlgebraicStacks

end
