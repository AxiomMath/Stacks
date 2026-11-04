module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomTotalPresheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceIsoClass
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties

/-!
# Properties of the sheaf of isomorphisms lifting a 2-morphism, read off the relative diagonal

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, `Z` an algebraic space, `x₁, x₂ :
Z ⟶ 𝒳` two points and `α : x₁ ≫ f ⟶ x₂ ≫ f`. The sheaf `Isom^α_{𝒳/𝒴}(x₁, x₂)` of Stacks 06PP,
in its explicit form `AlgebraicGeometry.Stack.relativeIsomorphismTotalPresheaf` (pairs of a point
`z` of `Z` and an isomorphism `x₁(z) ≅ x₂(z)` lifting `α_z`), is the base change of the relative
diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` along the twisted point `(x₁, x₂, α)` of `𝒳 ×_𝒴 𝒳`. So every
property of morphisms of algebraic spaces which `Δ_f` has in the sense of Properties of Stacks,
Section 04XB, is a property of the structure morphism `Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z`. In
particular this morphism is proper when `f` is separated, and surjective, flat and locally of
finite presentation when `f` makes `𝒳` a gerbe over `𝒴`.

## Main results

* `AlgebraicGeometry.Stack.prop_relativeIsomorphismTotalProj_of_relativeDiagonal`: a property of
  `Δ_f` in the sense of Stacks 04XB is a property of `Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z`.
* `AlgebraicGeometry.Stack.isProper_relativeIsomorphismTotalProj_of_isSeparated`: it is proper
  when `f` is separated.
* `isSurjective_isFlat_isLocallyOfFinitePresentation_relativeIsomorphismTotalProj`: it is
  surjective, flat and locally of finite presentation when `f` makes `𝒳` a gerbe over `𝒴`.

## References

* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 0CPL](https://stacks.math.columbia.edu/tag/0CPL)
* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The canonical 2-fibre-product square of the twisted point `(x₁, x₂, α)` of `𝒳 ×_𝒴 𝒳` and the
relative diagonal `Δ_f`; its apex is `Isom^α_{𝒳/𝒴}(x₁, x₂)`. -/
noncomputable abbrev relativeIsomorphismSquare (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (Bicategory.InducedBicategory.mkHom (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α) :
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val ⟶
        twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom)
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)

/-- The relative diagonal `Δ_f` has `P` in the sense of Properties of Stacks, Section 04XB. -/
abbrev RelativeDiagonalHasProp (P : MorphismProperty (AlgebraicSpaces B S hS)) (f : 𝒳 ⟶ 𝒴) :
    Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
    (_hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p =
      Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
          (CatFiberedInGroupoids.homFunctor
            (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))

/-- **A property of the relative diagonal is a property of `Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z`.** If the
relative diagonal `Δ_f` of `f : 𝒳 ⟶ 𝒴` has `P` in the sense of Properties of Stacks,
Section 04XB, then the structure morphism of the sheaf `Isom^α_{𝒳/𝒴}(x₁, x₂)` of pairs of a point
`z` of `Z` and an isomorphism `x₁(z) ≅ x₂(z)` lifting `α_z` has `P`. -/
theorem prop_relativeIsomorphismTotalProj_of_relativeDiagonal
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (f : 𝒳 ⟶ 𝒴) (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f)
    (hP : RelativeDiagonalHasProp B S hS P f) :
    P (ObjectProperty.homMk (PresheafOfCategories.elementsTotalProj Z
        (TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
          𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
          (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w)) :
      (⟨relativeIsomorphismTotalPresheaf B S hS Z hZ f x₁ x₂ α,
        isAlgebraicSpace_relativeIsomorphismTotalPresheaf B S hS Z hZ f x₁ x₂ α⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩) := by
  set R := relativeIsomorphismSquare B S hS Z hZ f x₁ x₂ α with hRdef
  have hR : Bicategory.IsTwoFibreProduct R :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have hfst := prop_baseChange_of_isTwoFibreProduct.{u, u, u} B S hS P 𝒳.val _ _ _ _ R hR hP
  have hrep : IsRepresentableByAlgebraicSpaces B S hS R.fst.hom :=
    isRepresentableByAlgebraicSpaces_relativeIsomorphismSpaceOverSpaceProj B S hS Z hZ f x₁ x₂ α
  set W := TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
    𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
    (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w with hW
  let E := (nonempty_equivalenceOver_relativeIsomorphismSpaceOverSpaceProj B S hS Z hZ f x₁ x₂
    α).some
  let eF := ((E.compRight (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p).ofEq
      (relativeIsomorphismSpaceOverSpaceProj B S hS Z hZ f x₁ x₂ α).w).trans
    (PresheafOfCategories.totalElementsEquivalenceOver Z W)
  have h := (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS P R.fst hrep _ Z
    (isAlgebraicSpace_relativeIsomorphismTotalPresheaf B S hS Z hZ f x₁ x₂ α) hZ eF
    (StacksRepresentableCFG.EquivalenceOver.refl _)).1 hfst
  convert h using 2
  symm
  refine morphismSpaceEquiv_eq_of_comp_eq B S hS _ _ _ _ _ _ _ _ ?_
  have hT : PresheafOfCategories.elementsToTotal Z W ⋙
      PresheafOfCategories.elementsMap (PresheafOfCategories.elementsTotalProj Z W) =
      PresheafOfCategories.discreteProjection W :=
    CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      PresheafOfCategories.elements_hom_ext _ _ rfl)
  have heF : eF.hom.functor = E.hom.functor ⋙ PresheafOfCategories.elementsToTotal Z W := by
    simp only [eF, StacksRepresentableCFG.EquivalenceOver.trans,
      StacksRepresentableCFG.EquivalenceOver.ofEq_hom_functor]
    rfl
  rw [heF]
  exact (congrArg (fun G => E.hom.functor ⋙ G) hT).trans E.hom.w

/-- **`Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z` is proper when `f` is separated.** -/
theorem isProper_relativeIsomorphismTotalProj_of_isSeparated (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsSeparated B S hS f)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    Space.IsProper B S hS (PresheafOfCategories.elementsTotalProj Z
      (TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
        𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
        (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w)) :=
  prop_relativeIsomorphismTotalProj_of_relativeDiagonal B S hS Z hZ
    (spaceProperty B S hS (fun _ _ h => Space.IsProper B S hS h)) f x₁ x₂ α hf

/-- **`Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z` is surjective, flat and locally of finite presentation when `f`
makes `𝒳` a gerbe over `𝒴`.** -/
theorem isSurjective_isFlat_isLocallyOfFinitePresentation_relativeIsomorphismTotalProj
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsGerbeOver B S hS f)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    Space.IsSurjective B S hS (PresheafOfCategories.elementsTotalProj Z
        (TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
          𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
          (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w)) ∧
      Space.IsFlat B S hS (PresheafOfCategories.elementsTotalProj Z
        (TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
          𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
          (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w)) ∧
      Space.IsLocallyOfFinitePresentation B S hS (PresheafOfCategories.elementsTotalProj Z
        (TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
          𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
          (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w)) := by
  obtain ⟨hΔsurj, hΔflat, hΔlfp⟩ := open AlgebraicStacks in
    isSurjective_and_isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal_of_isGerbeOver
      B S hS f hf
  have hΔrep : IsRepresentableByAlgebraicSpaces B S hS
      (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom.hom :=
    isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hflatBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  have hlfpBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hlfpLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf B S hS
  have hsurjRel := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u}
    B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) hΔrep).1 hΔsurj
  have hflatRel := (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) 𝒳.property
    (Stack.twoFibreProductAlgebraicStack B S hS f f).property
    (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom hΔrep).1 hΔflat
  have hlfpRel := (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) 𝒳.property
    (Stack.twoFibreProductAlgebraicStack B S hS f f).property
    (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom hΔrep).1
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
        𝒳.property (Stack.twoFibreProductAlgebraicStack B S hS f f).property
        (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom).1 hΔlfp)
  exact ⟨prop_relativeIsomorphismTotalProj_of_relativeDiagonal B S hS Z hZ
      (spaceProperty B S hS (fun _ _ h => Space.IsSurjective B S hS h)) f x₁ x₂ α hsurjRel,
    prop_relativeIsomorphismTotalProj_of_relativeDiagonal B S hS Z hZ
      (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h)) f x₁ x₂ α hflatRel,
    prop_relativeIsomorphismTotalProj_of_relativeDiagonal B S hS Z hZ
      (spaceProperty B S hS (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h))
      f x₁ x₂ α hlfpRel⟩

end AlgebraicGeometry.Stack

end
