module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFaithfulBase

/-!
# The diagonal of `Coh_{X/B}` over `B`, reduced to the isomorphism sheaves

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` of finite presentation, the standing
data of Stacks 08KB, and let `𝒳 = Coh_{X/B}`. Stacks 0DLY says that the diagonal
`𝒳 ⟶ 𝒳 ×_B 𝒳` of `𝒳` over `B` is affine and of finite presentation. Its proof reads the base
change of that diagonal along a scheme-valued point `(x, y)` of `𝒳 ×_B 𝒳` over `T` as the
isomorphism sheaf `Isom_𝒳(x, y)`, and identifies this — the two objects lying over one point
`g : T ⟶ B` — with the relative isomorphism functor `Isom(ℱ, 𝒢)` of the two modules on `X_T`
(Stacks 08W6 with `g = h`), which Proposition 08K9 makes an algebraic space affine and of finite
presentation over `T`.

In this file the diagonal over `B` is the relative diagonal of the projection
`Coh_{X/B} ⟶ 𝒮_B`, whose target has a faithful structure functor, so
`AlgebraicGeometry.Stack.exists_isRepresentable_and_prop_relativeDiagonal_of_faithful` reduces the
assertion to the isomorphism sheaves of pairs of objects over a common point of `B`.

## Main definitions

* `AlgebraicGeometry.Space.affineFinitePresentation`: the property of a morphism of algebraic
  spaces of being affine and of finite presentation.

## Main results

* `AlgebraicGeometry.Space.respectsIso_affineFinitePresentation`: that property respects
  isomorphisms.
* `AlgebraicGeometry.Space.coherentRelativeDiagonal_affine_finitePresentation_of_isom`: the
  conclusion of Stacks 0DLY, given that `𝒮_B` is fibred in groupoids and that the isomorphism
  sheaf of two objects of `Coh_{X/B}` over one point of `B` is an algebraic space, affine and of
  finite presentation.

## References

* [Stacks Project, Tag 0DLY](https://stacks.math.columbia.edu/tag/0DLY)
* [Stacks Project, Tag 08W6](https://stacks.math.columbia.edu/tag/08W6)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- The property of a morphism of algebraic spaces over `S` of being affine (Stacks 03WF) and of
finite presentation (Stacks 03XP, part (3)). -/
abbrev affineFinitePresentation : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ g => IsAffineHom B S hS g.hom ∧ IsFinitePresentation B S hS g.hom

variable (B S hS) in
/-- Being affine and of finite presentation respects isomorphisms of algebraic spaces. -/
instance respectsIso_affineFinitePresentation :
    (affineFinitePresentation B S hS).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e g hg => ⟨isAffineHom_iso_comp e.hom.hom hg.1,
      isFinitePresentation_of_arrowIso B S hS g.hom (e.hom ≫ g).hom e.inv.hom (𝟙 _)
        (by simp) hg.2⟩)
    (fun e g hg => ⟨isAffineHom_comp_iso e.hom.hom hg.1,
      isFinitePresentation_of_arrowIso B S hS g.hom (g ≫ e.hom).hom (𝟙 _) e.hom.hom
        (by simp) hg.2⟩)

/-- Let `D` be the standing data of Stacks 08KB, `f : X ⟶ B` of finite presentation, and
`𝒳 = Coh_{X/B}`. Suppose that `𝒮_B` is fibred in groupoids (`hfib`), and that for two objects of
`𝒳` over `U` lying over one point of `B` the isomorphism sheaf is an algebraic space over `U`,
affine and of finite presentation (`hIsom`). Then the diagonal `𝒳 ⟶ 𝒳 ×_B 𝒳` of `𝒳` over `B` —
the relative diagonal of the projection `Coh_{X/B} ⟶ 𝒮_B` — is representable by algebraic
spaces, and every algebraic space representing one of its base changes along a scheme-valued
point over `U` is affine and of finite presentation over `U`. -/
theorem coherentRelativeDiagonal_affine_finitePresentation_of_isom
    (D : CoherentSituation B S hS) (hfib : (baseBasedCategory D.Y).p.IsFiberedInGroupoids)
    (hIsom : letI : (coherentCFG D).val.p.IsFibered :=
        (coherentCFG D).isFiberedInGroupoids.isFibered
      ∀ (U : BigFppfOver B S hS) (x x' : (coherentCFG D).val.p.Fiber U),
        (∃ φ : (coherentToBase D.categoryData).obj x.1 ⟶
            (coherentToBase D.categoryData).obj x'.1,
          (baseBasedCategory D.Y).p.IsHomLift (𝟙 U) φ) →
        ∃ (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
          (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
          Nonempty (G ⋙ uliftFunctor.{u + 1, u} ≅
            ((Over.iteratedSliceBackward U).op ⋙ (coherentCFG D).val.p.isomPresheaf x x') ⋙
              uliftFunctor.{u, u + 1}) ∧
          affineFinitePresentation B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩))) :
    letI 𝒴 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
      CatFiberedInGroupoids.mk (baseBasedCategory D.Y) hfib
    ∃ _hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Stack.relativeDiagonalBasedFunctor B S hS (coherentCFG D) 𝒴
          (coherentToBase D.categoryData)),
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (Stack.twoFibreProduct B S hS 𝒴 (coherentCFG D) (coherentCFG D)
            (coherentToBase D.categoryData) (coherentToBase D.categoryData)).val.obj)
        (_hy : y ⋙ (Stack.twoFibreProduct B S hS 𝒴 (coherentCFG D) (coherentCFG D)
            (coherentToBase D.categoryData) (coherentToBase D.categoryData)).val.p =
          Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) (coherentCFG D).val.p
            (Stack.twoFibreProduct B S hS 𝒴 (coherentCFG D) (coherentCFG D)
              (coherentToBase D.categoryData) (coherentToBase D.categoryData)).val.p y
            (Stack.relativeDiagonalBasedFunctor B S hS (coherentCFG D) 𝒴
              (coherentToBase D.categoryData)).toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        IsAffineHom B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom ∧
          IsFinitePresentation B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  have : (baseBasedCategory D.Y).p.Faithful := baseBasedCategory_faithful D.Y
  exact Stack.exists_isRepresentable_and_prop_relativeDiagonal_of_faithful B S hS (coherentCFG D)
    (CatFiberedInGroupoids.mk (baseBasedCategory D.Y) hfib) (coherentToBase D.categoryData)
    (affineFinitePresentation B S hS) hIsom

end AlgebraicGeometry.Space

end
