module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatDescentAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Gerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeCharacterization
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonalSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondRelativeDiagonalInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Auxiliary results for the relative diagonal of a gerbe

Results on the relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks that do not depend on its flatness, used for [Stacks, Tag 0CPR] in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonal`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasFlatLfpLocalRelativeDiagonal`: a 1-morphism has an
  *fppf-locally flat and locally finitely presented relative diagonal* when there is a
  surjective, flat, locally finitely presented 1-morphism onto `𝒳 ×_𝒴 𝒳` along which the base
  change of `Δ_f` is flat and locally of finite presentation.
* `AlgebraicGeometry.Stack.AlgebraicStacks.comparisonSquareAlgebraicStacks`: the square of
  [Stacks, Tag 04Z1], which exhibits the comparison `𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` as a base change of
  `Δ_{𝒵/𝒯}`, read in the 2-category of algebraic stacks.

## Main results

All of these live in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`.

* `isLocallyOfFinitePresentation_comp_of_isEquivalence`: local finite presentation is unchanged
  by precomposition with a 1-morphism whose underlying functor is an equivalence.
* `relativeInertiaProjection_eq_comp_fst`: the forgetful 1-morphism of the relative inertia is
  the comparison with `𝒳 ×_{Δ_f, 𝒳 ×_𝒴 𝒳, Δ_f} 𝒳` followed by the first projection.
* `isTwoFibreProduct_comparisonSquareAlgebraicStacks`: the square of [Stacks, Tag 04Z1] is a
  2-fibre product in the 2-category of algebraic stacks.

## Implementation notes

`AlgebraicGeometry.Stack.AlgebraicStacks.HasFlatLfpLocalRelativeDiagonal` is phrased at the
canonical 2-fibre product of [Stacks, Tag 04T2] over the cospan `(Δ_f, q)`.

## References

* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04Z1](https://stacks.math.columbia.edu/tag/04Z1)
* [Stacks Project, Tag 0CPR](https://stacks.math.columbia.edu/tag/0CPR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Local finite presentation along an equivalence -/

/-- **Being locally of finite presentation is unchanged by precomposition with an equivalence.**
If the functor underlying `k : 𝒵 ⟶ 𝒳` is an equivalence of categories and `f : 𝒳 ⟶ 𝒴` is locally
of finite presentation, then so is `k ≫ f`. -/
theorem isLocallyOfFinitePresentation_comp_of_isEquivalence
    {𝒵 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (k : 𝒵 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom))
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B S hS (k ≫ f) := by
  obtain ⟨F, hF, η, ε, -, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒵.val.val.p 𝒳.val.val.p
      𝒵.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor k.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p k.hom) hk
  have he : Functor.IsEquivalence F :=
    (CategoryTheory.Equivalence.mk F (CatFiberedInGroupoids.homFunctor k.hom) ε.symm
      η).isEquivalence_functor
  have hiso : (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩ : 𝒳.val ⟶ 𝒵.val) ≫ k.hom ≅
      𝟙 𝒳.val :=
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
      (F := BasedFunctor.comp ⟨F, hF⟩ k.hom.hom) (G := BasedFunctor.id 𝒳.val.val) ε hε)
  refine (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      𝒵.property 𝒴.property (k ≫ f).hom).2
    (Stack.hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h) (k ≫ f).hom f.hom
      (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩) he ?_
      ((Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
        (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
        𝒳.property 𝒴.property f.hom).1 hf))
  exact (Bicategory.leftUnitor f.hom).symm ≪≫ Bicategory.whiskerRightIso hiso.symm f.hom ≪≫
    Bicategory.associator
      (Bicategory.InducedBicategory.mkHom (⟨F, hF⟩ : 𝒳.val.val ⥤ᵇ 𝒵.val.val)) k.hom f.hom

/-! ### The local form of the flatness of the relative diagonal -/

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` has an *fppf-locally flat and locally
finitely presented relative diagonal* when there are an algebraic stack `𝒲` over `S` and a
surjective, flat, locally finitely presented 1-morphism `q : 𝒲 ⟶ 𝒳 ×_𝒴 𝒳` such that the base
change `𝒲 ×_{𝒳 ×_𝒴 𝒳} 𝒳 ⟶ 𝒲` of the relative diagonal `Δ_f` along `q` is flat and locally of
finite presentation. -/
abbrev HasFlatLfpLocalRelativeDiagonal
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (𝒲 : Stack.AlgebraicStacks.{u, w} B S hS)
    (q : 𝒲 ⟶ Stack.twoFibreProductAlgebraicStack B S hS f f),
    Stack.IsSurjective B S hS q ∧ IsFlat B S hS q ∧
      IsLocallyOfFinitePresentation B S hS q ∧
      IsFlat B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.relativeDiagonalAlgebraicStacks B S hS f) q).snd ∧
      IsLocallyOfFinitePresentation B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.relativeDiagonalAlgebraicStacks B S hS f) q).snd

/-! ### The relative inertia as a base change of the relative diagonal -/

/-- **The forgetful 1-morphism of the relative inertia is the first projection of
`𝒳 ×_{Δ_f, 𝒳 ×_𝒴 𝒳, Δ_f} 𝒳`, read through the comparison 1-morphism.** -/
theorem relativeInertiaProjection_eq_comp_fst
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    Stack.relativeInertiaProjection B S hS f =
      (Bicategory.InducedBicategory.mkHom
          (Stack.relativeInertiaToSecondRelativeDiagonal B S hS f.hom) :
        Stack.relativeInertiaStack B S hS f ⟶
          Stack.twoFibreProductAlgebraicStack B S hS
            (Stack.relativeDiagonalAlgebraicStacks B S hS f)
            (Stack.relativeDiagonalAlgebraicStacks B S hS f)) ≫
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS
          (Stack.relativeDiagonalAlgebraicStacks B S hS f)
          (Stack.relativeDiagonalAlgebraicStacks B S hS f)).fst :=
  rfl

/-! ### The comparison of two fibre products as a base change of the relative diagonal -/

/-- **The square of Stacks 04Z1, read in the 2-category of algebraic stacks.** Its apex is the
2-fibre product `𝒳 ×_𝒵 𝒴` of Stacks 04T2, its first leg is the comparison 1-morphism
`i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` of Stacks 050H, its second leg is the first projection followed by `f`,
and its cospan is `(i × i, Δ_{𝒵/𝒯})`. -/
noncomputable def comparisonSquareAlgebraicStacks
    {𝒳 𝒴 𝒵 𝒯 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    Bicategory.TwoCommSq (Stack.comparisonCospanRight B S hS f g h)
      (Stack.relativeDiagonalAlgebraicStacks B S hS h) where
  pt := Stack.twoFibreProductAlgebraicStack B S hS f g
  fst := Stack.comparison B S hS f g h
  snd := (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).fst ≫ f
  iso := Bicategory.InducedBicategory.isoMk (Stack.comparisonSquare B S hS f g h).iso

/-- **The square of Stacks 04Z1 is a 2-fibre product of algebraic stacks.** -/
noncomputable def isTwoFibreProduct_comparisonSquareAlgebraicStacks
    {𝒳 𝒴 𝒵 𝒯 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    Bicategory.IsTwoFibreProduct (comparisonSquareAlgebraicStacks B S hS f g h) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Stack.isTwoFibreProduct_comparisonSquare B S hS f g h)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
