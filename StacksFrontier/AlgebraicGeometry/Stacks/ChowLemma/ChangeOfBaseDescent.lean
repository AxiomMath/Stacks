module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBaseQuantifier
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteSource
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Properties of 1-morphisms that descend along Construction A

Let `g : S ⟶ S'` be a morphism of a big fppf site. Construction A of Stacks 04X5 views a
1-morphism `φ` of algebraic stacks over `S` as one over `S'`
(`AlgebraicGeometry.Stack.changeBaseHomAlgebraicStacks`). This file proves that the properties
in the conclusion of Stacks 0CQ8 descend: if the view of `φ` over `S'` has them, so does `φ`.

## Main results

* `AlgebraicGeometry.Stack.universallyClosed_of_changeBaseHom`: universal closedness in the sense
  of Stacks 04XB.
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_changeBase`: quasi-compactness, Stacks 050U.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_changeBase`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isSurjective_of_changeBase`: separatedness and
  surjectivity.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_changeBase`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_changeBase` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_changeBase`: universal closedness
  (Stacks 0513), local finite type (Stacks 06FS) and properness (Stacks 0CL5) of a 1-morphism
  representable by algebraic spaces.

## Implementation notes

For a representable 1-morphism universal closedness is read through Stacks 0512 and local finite
type through Stacks 06FM as conditions of Stacks 04XB, whose descent along Construction A is
`AlgebraicGeometry.Space.universallyClosed_spacesOverSmallerBaseFunctor_of` and
`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_changeBaseHom_iff`. Quasi-compactness is tested on
quasi-compact algebraic stacks over `S`, whose Construction A is quasi-compact
(`AlgebraicGeometry.Stack.isQuasiCompactStack_changeBaseAlgebraicStack_iff`), and Construction A of
a 2-fibre product is equivalent to the 2-fibre product of Construction A
(`AlgebraicGeometry.Stack.changeBaseTwoFibreProductInv`).
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **Universal closedness in the sense of Stacks 04XB descends along Construction A.** -/
theorem universallyClosed_of_changeBaseHom
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (h : UniversallyClosed B S' hS' (changeBaseHom B S S' hS hS' g f)) :
    UniversallyClosed B S hS f := by
  rintro U y hy F hF ⟨E⟩
  have key := h ((Over.map g).obj U) y
    (comp_changeBase_p_eq_map B S S' hS hS' g 𝒴.val U y hy) F hF
    ⟨TwoFibreProductOver.unrelocalizeFstEquivalenceOver_trans g hy f.hom.w E⟩
  exact Space.universallyClosed_spacesOverSmallerBaseFunctor_of B U.left.1 S U.left.2 hS
    U.hom S' hS' g (U.hom ≫ g) rfl F hF key

/-- **Quasi-compactness of a 1-morphism of algebraic stacks (Stacks 050U) descends along
Construction A.** A quasi-compact test stack over `S` is carried to one over `S'`, and
Construction A of the base change is equivalent to the base change of Construction A. -/
theorem isQuasiCompactMorphism_of_changeBase {𝒜 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (φ : 𝒜 ⟶ 𝒳)
    (h : IsQuasiCompactMorphism.{u, w} B S' hS'
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g φ)) :
    IsQuasiCompactMorphism.{u, w} B S hS φ := by
  intro 𝒵 z h𝒵
  have key := h (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒵)
    (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g z)
    ((isQuasiCompactStack_changeBaseAlgebraicStack_iff B S S' hS hS' g 𝒵).2 h𝒵)
  refine (isQuasiCompactStack_changeBaseAlgebraicStack_iff B S S' hS hS' g
    (twoFibreProductAlgebraicStack B S hS z φ)).1 ?_
  let e : twoFibreProductAlgebraicStack B S' hS'
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g z)
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g φ) ⟶
      changeBaseAlgebraicStack B S S' hS hS' g (twoFibreProductAlgebraicStack B S hS z φ) :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (changeBaseTwoFibreProductInv B S S' hS hS' g 𝒳.val 𝒵.val 𝒜.val z.hom.hom φ.hom.hom))
  have : e.hom.hom.toFunctor.EssSurj :=
    (isEquivalence_changeBaseTwoFibreProductInv B S S' hS hS' g 𝒳.val 𝒵.val 𝒜.val
      z.hom.hom φ.hom.hom).essSurj
  exact isQuasiCompactStack_of_essSurj B S' hS' e key

namespace AlgebraicStacks

variable {𝒜 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **Separatedness (Stacks 04YW) descends along Construction A.** -/
theorem isSeparated_of_changeBase (φ : 𝒜 ⟶ 𝒳)
    (h : IsSeparated B S' hS' (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g φ)) :
    IsSeparated B S hS φ :=
  isProper_relativeDiagonal_of_changeBase B S S' hS hS' g 𝒜.val 𝒳.val φ.hom h

/-- **Surjectivity (Stacks 04ZS) descends along Construction A.** -/
theorem isSurjective_of_changeBase (φ : 𝒜 ⟶ 𝒳)
    (h : Stack.IsSurjective B S' hS' (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g φ)) :
    Stack.IsSurjective B S hS φ :=
  (pointsMap_surjective_changeBaseFunctor_iff B S S' hS hS' g 𝒜.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids φ.hom.hom).1 h

/-- Construction A preserves 1-morphisms representable by algebraic spaces. -/
private theorem isRepresentableByAlgebraicSpaces_changeBaseHom (φ : 𝒜 ⟶ 𝒳)
    (hφ : IsRepresentableByAlgebraicSpaces B S hS φ.hom.hom) :
    IsRepresentableByAlgebraicSpaces B S' hS'
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g φ).hom.hom :=
  (isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g φ.hom.hom).2 hφ

/-- **Universal closedness (Stacks 0513) of a 1-morphism representable by algebraic spaces
descends along Construction A.** By Stacks 0512 it is universal closedness in the sense of Stacks
04XB, which descends by `AlgebraicGeometry.Stack.universallyClosed_of_changeBaseHom`. -/
theorem universallyClosed_of_changeBase (φ : 𝒜 ⟶ 𝒳)
    (hφ : IsRepresentableByAlgebraicSpaces B S hS φ.hom.hom)
    (h : UniversallyClosed B S' hS' (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g φ)) :
    UniversallyClosed B S hS φ := by
  have hφ' := isRepresentableByAlgebraicSpaces_changeBaseHom B S S' hS hS' g φ hφ
  have h04XB := (representable_universallyClosed_iff_closedMap_baseChange B S' hS'
    (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g φ) hφ').2 h
  exact (representable_universallyClosed_iff_closedMap_baseChange B S hS φ hφ).1
    (universallyClosed_of_changeBaseHom B S S' hS hS' g φ.hom h04XB)

/-- **Local finite type (Stacks 06FS) of a 1-morphism representable by algebraic spaces descends
along Construction A.** By Stacks 06FM it is the étale-chart condition of Stacks 04XB at local
finite type, which descends by
`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_changeBaseHom_iff`. -/
theorem isLocallyOfFiniteType_of_changeBase (φ : 𝒜 ⟶ 𝒳)
    (hφ : IsRepresentableByAlgebraicSpaces B S hS φ.hom.hom)
    (h : IsLocallyOfFiniteType B S' hS'
      (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g φ)) :
    IsLocallyOfFiniteType B S hS φ := by
  have hφ' := isRepresentableByAlgebraicSpaces_changeBaseHom B S S' hS hS' g φ hφ
  have : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS k.hom) :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  have : MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS k.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S' hS'⦄ (k : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S' hS' k.hom) :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S' hS'
  have : MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S' hS'⦄ (k : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S' hS' k.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S' hS') :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S' hS')
  have hrel' := (Stack.hasPropertyOnEverySmoothDiagram_iff_relative.{u, u, w} B S' hS'
    (fun _ _ k => Space.IsLocallyOfFiniteType B S' hS' k)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S' hS')
    (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒜).property
    (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳).property
    (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g φ).hom hφ').1 h
  have hrel : HasEtaleChartProperty B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u}) φ.hom :=
    (holdsOnEveryEtaleChart_changeBaseHom_iff B S S' hS hS' g _ φ.hom).1 hrel'
  exact (Stack.hasPropertyOnEverySmoothDiagram_iff_relative.{u, u, w} B S hS
    (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    𝒜.property 𝒳.property φ.hom hφ).2 hrel

/-- **Properness (Stacks 0CL5) of a 1-morphism representable by algebraic spaces descends along
Construction A.** -/
theorem isProper_of_changeBase (φ : 𝒜 ⟶ 𝒳)
    (hφ : IsRepresentableByAlgebraicSpaces B S hS φ.hom.hom)
    (h : IsProper B S' hS' (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g φ)) :
    IsProper B S hS φ :=
  ⟨isSeparated_of_changeBase B S S' hS hS' g φ h.1,
    ⟨isLocallyOfFiniteType_of_changeBase B S S' hS hS' g φ hφ h.2.1.1,
      isQuasiCompactMorphism_of_changeBase B S S' hS hS' g φ h.2.1.2⟩,
    universallyClosed_of_changeBase B S S' hS hS' g φ hφ h.2.2⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack
