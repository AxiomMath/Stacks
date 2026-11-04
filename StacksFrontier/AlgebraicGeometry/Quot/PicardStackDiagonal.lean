module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackIsomAffineFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToBaseFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulRelativeDiagonal

/-!
# The diagonal of the Picard stack over the base (Stacks 0DMA)

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is flat, of finite presentation
and proper. Stacks 0DMA says that the diagonal of `Picardstack_{X/B}` over `B` is affine and of
finite presentation. Its proof: `Picardstack_{X/B}` is an open substack of `Cohstack_{X/B}`
(Stacks 0D03), so this follows from the same statement for `Cohstack_{X/B}` (Stacks 0DLY).

The diagonal of `Picardstack_{X/B}` over `B` is the relative diagonal of the structure morphism
`Picardstack_{X/B} ⟶ 𝒮_B`, which is the natural map of Stacks 0D03 followed by the projection
`Cohstack_{X/B} ⟶ 𝒮_B` (`AlgebraicGeometry.Space.picardToCoherent_comp_coherentToBaseCFG`). The
natural map is fully faithful, so the relative diagonal of the composite is a base change of the
relative diagonal of the projection (Stacks 0CBB,
`AlgebraicGeometry.Stack.isTwoFibreProduct_relativeDiagonalCompSquare`), and inherits
representability by algebraic spaces and every condition of Properties of Stacks, Section 04XB.

## Main results

* `AlgebraicGeometry.Space.relativeDiagonal_picardToBase_of_coherentToBaseCFG`: for any property
  `P` of morphisms of algebraic spaces, if the diagonal of `Cohstack_{X/B}` over `B` is
  representable by algebraic spaces with `P`, then so is the diagonal of `Picardstack_{X/B}`.
* `AlgebraicGeometry.Space.picardRelativeDiagonal_affine_finitePresentation_of_isom`: the diagonal
  of `Picardstack_{X/B}` over `B` is affine and of finite presentation, assuming that the
  isomorphism sheaves of two objects of `Cohstack_{X/B}` over one point of `B` are algebraic
  spaces affine and of finite presentation over that point.
* `AlgebraicGeometry.Space.picardRelativeDiagonal_affine_finitePresentation`: the diagonal of
  `Picardstack_{X/B}` over `B` is affine and of finite presentation.

## References

* [Stacks Project, Tag 0DMA](https://stacks.math.columbia.edu/tag/0DMA)
* [Stacks Project, Tag 0DLY](https://stacks.math.columbia.edu/tag/0DLY)
* [Stacks Project, Tag 0D03](https://stacks.math.columbia.edu/tag/0D03)
* [Stacks Project, Tag 0CBB](https://stacks.math.columbia.edu/tag/0CBB)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `f` be flat and proper (and of finite presentation, part of the standing data `D`), and
`P` a property of morphisms of algebraic spaces over `S`. If the relative diagonal of the
projection `Cohstack_{X/B} ⟶ 𝒮_B` is representable by algebraic spaces and every algebraic space
representing one of its base changes along a scheme-valued point over `U` has `P` over `U`, then
the same holds for the relative diagonal of the structure morphism `Picardstack_{X/B} ⟶ 𝒮_B`. -/
theorem relativeDiagonal_picardToBase_of_coherentToBaseCFG
    (P : MorphismProperty (AlgebraicSpaces B S hS)) (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ (coherentToBaseCFG D)).hom)
    (hΔ : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (Stack.twoFibreProduct B S hS (baseCFG D.Y) (coherentCFG D) (coherentCFG D)
          (coherentToBaseCFG D).hom (coherentToBaseCFG D).hom).val.obj)
      (_hy : y ⋙ (Stack.twoFibreProduct B S hS (baseCFG D.Y) (coherentCFG D) (coherentCFG D)
          (coherentToBaseCFG D).hom (coherentToBaseCFG D).hom).val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) (coherentCFG D).val.p
          (Stack.twoFibreProduct B S hS (baseCFG D.Y) (coherentCFG D) (coherentCFG D)
            (coherentToBaseCFG D).hom (coherentToBaseCFG D).hom).val.p y
          (CatFiberedInGroupoids.homFunctor
            (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ (coherentToBaseCFG D))))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    letI π := picardToBase (modulePushforwardCoherence B S hS) D.toPicardSituation
    ∃ _hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ π).hom,
      ∀ (U : BigFppfOver B S hS)
        (z : BigFppfOver B U.left.1 U.left.2 ⥤
          (Stack.twoFibreProduct B S hS (baseCFG D.Y) _ _ π.hom π.hom).val.obj)
        (_hz : z ⋙ (Stack.twoFibreProduct B S hS (baseCFG D.Y) _ _ π.hom π.hom).val.p =
          Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val.p
            (Stack.twoFibreProduct B S hS (baseCFG D.Y) _ _ π.hom π.hom).val.p z
            (CatFiberedInGroupoids.homFunctor
              (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ π)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  have hj : (CatFiberedInGroupoids.homFunctor (picardToCoherent D hflat hproper)).Full ∧
      (CatFiberedInGroupoids.homFunctor (picardToCoherent D hflat hproper)).Faithful :=
    ⟨(picardToCoherentBasedFullyFaithful D hflat hproper).full,
      (picardToCoherentBasedFullyFaithful D hflat hproper).faithful⟩
  simp only [← picardToCoherent_comp_coherentToBaseCFG D hflat hproper]
  exact ⟨Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_comp.{u, u + 1, u + 1} B S hS
      (picardToCoherent D hflat hproper) (coherentToBaseCFG D) hj hrep,
    Stack.relativeProperty_relativeDiagonal_comp.{u, u + 1, u + 1} B S hS P
      (picardToCoherent D hflat hproper) (coherentToBaseCFG D) hj hΔ⟩

/-- Let `f` be flat and proper (and of finite presentation, part of the standing data `D`), and
assume `hIsom`: for two objects of `Cohstack_{X/B}` over one point `U` of `B`, the isomorphism
sheaf is an algebraic space affine and of finite presentation over `U` (Proposition 08K9). Then
the diagonal of `Picardstack_{X/B}` over `B` — the relative diagonal of the structure morphism
`Picardstack_{X/B} ⟶ 𝒮_B` — is representable by algebraic spaces, and every algebraic space
representing one of its base changes along a scheme-valued point over `U` is affine and of finite
presentation over `U`. -/
theorem picardRelativeDiagonal_affine_finitePresentation_of_isom
    (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom)
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
    letI π := picardToBase (modulePushforwardCoherence B S hS) D.toPicardSituation
    ∃ _hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ π).hom,
      ∀ (U : BigFppfOver B S hS)
        (z : BigFppfOver B U.left.1 U.left.2 ⥤
          (Stack.twoFibreProduct B S hS (baseCFG D.Y) _ _ π.hom π.hom).val.obj)
        (_hz : z ⋙ (Stack.twoFibreProduct B S hS (baseCFG D.Y) _ _ π.hom π.hom).val.p =
          Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val.p
            (Stack.twoFibreProduct B S hS (baseCFG D.Y) _ _ π.hom π.hom).val.p z
            (CatFiberedInGroupoids.homFunctor
              (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ π)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        IsAffineHom B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom ∧
          IsFinitePresentation B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
  let h := coherentRelativeDiagonal_affine_finitePresentation_of_isom D
    (baseCFG D.Y).isFiberedInGroupoids hIsom
  relativeDiagonal_picardToBase_of_coherentToBaseCFG (affineFinitePresentation B S hS) D hflat
    hproper h.1 h.2

/-- Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is flat, proper and of finite
presentation (finite presentation is part of the standing data `D`). The diagonal of
`Picardstack_{X/B}` over `B` is affine and of finite presentation: the relative diagonal of the
structure morphism `Picardstack_{X/B} ⟶ 𝒮_B` is representable by algebraic spaces (Stacks 02ZW),
and every algebraic space representing one of its base changes along a scheme-valued point over
`U` is affine and of finite presentation over `U` (Properties of Stacks, Section 04XB). -/
@[stacks 0DMA]
theorem picardRelativeDiagonal_affine_finitePresentation
    (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) :
    letI π := picardToBase (modulePushforwardCoherence B S hS) D.toPicardSituation
    ∃ _hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ π).hom,
      ∀ (U : BigFppfOver B S hS)
        (z : BigFppfOver B U.left.1 U.left.2 ⥤
          (Stack.twoFibreProduct B S hS (baseCFG D.Y) _ _ π.hom π.hom).val.obj)
        (_hz : z ⋙ (Stack.twoFibreProduct B S hS (baseCFG D.Y) _ _ π.hom π.hom).val.p =
          Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val.p
            (Stack.twoFibreProduct B S hS (baseCFG D.Y) _ _ π.hom π.hom).val.p z
            (CatFiberedInGroupoids.homFunctor
              (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ π)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        IsAffineHom B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom ∧
          IsFinitePresentation B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
  picardRelativeDiagonal_affine_finitePresentation_of_isom D hflat hproper
    (CoherentSituation.coherentIsomPresheaf_affineFinitePresentation D)

end AlgebraicGeometry.Space

end
