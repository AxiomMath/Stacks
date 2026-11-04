module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMComparisonRepresentingMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint

/-!
# The relative dimension of a chart of a quasi-DM algebraic stack over a field spectrum

Let `h : 𝒵 ⟶ Spec k` be a quasi-DM 1-morphism, locally of finite type, from an algebraic stack
over `S` to the algebraic stack of the field spectrum of a field-valued point, and let
`x₁ : T ⟶ 𝒵` be a 1-morphism, locally of finite type, from an algebraic space. At every point `t`
of `T` the relative dimension of `x₁` of **Stacks 0DRG** is at most the dimension of `T` at `t`.

## Main results

* `AlgebraicGeometry.Stack.dimensionAtPoint_representingMap_twoFibreProduct_eq_dimensionAtPoint`:
  an algebraic space representing `T ×_{Spec k} Spec κ`, for two field spectra of the site over
  `Spec k` and `T` locally of finite type over `Spec k`, has at each of its points the dimension
  `T` has at the image point.
* `AlgebraicGeometry.Stack.relativeDimensionAt_le_dimensionAtPoint_of_isQuasiDM`: the relative
  dimension of the chart at `t` is at most `dim_t(T)`.

## References

* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06LT](https://stacks.math.columbia.edu/tag/06LT)
* [Stacks Project, Tag 0CPL](https://stacks.math.columbia.edu/tag/0CPL)
* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DS5](https://stacks.math.columbia.edu/tag/0DS5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A base change of an algebraic space to a field spectrum over a field spectrum has the
dimension of the space at the image point.** Let `Spec k` and `Spec κ` be the recorded bases of
two field-valued points, let `a : T ⟶ Spec k` be a 1-morphism, locally of finite type, from an
algebraic space `T` over `S` and let `b : Spec κ ⟶ Spec k` be any 1-morphism. Then an algebraic
space `Q` representing `T ×_{Spec k} Spec κ` has, at every one of its points, the dimension that
`T` has at the image of that point under the first projection. -/
theorem dimensionAtPoint_representingMap_twoFibreProduct_eq_dimensionAtPoint
    {𝒜 ℬ : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (ν : FieldValuedPoint B S hS 𝒜) (π : FieldValuedPoint B S hS ℬ)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (a : algebraicSpaceStack.{u, w} B S hS T hT ⟶ schemeStack.{u, w} B S hS ν.base)
    (ha : AlgebraicStacks.IsLocallyOfFiniteType B S hS a)
    (b : schemeStack.{u, w} B S hS π.base ⟶ schemeStack.{u, w} B S hS ν.base)
    (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hQ : IsAlgebraicSpace B S hS Q)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProduct B S hS a b).val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p)
    (y : Space.points B S hS Q) :
    Space.dimensionAtPoint B S hS Q hQ y =
      Space.dimensionAtPoint B S hS T hT
        (Space.pointsMap B S hS Q
          (representingMap B S hS (AlgebraicStacks.twoFibreProduct B S hS a b).val
            (fibredCategory B S hS T) Q T eQ
            (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS T).val.p)
            (AlgebraicStacks.twoFibreProductSquare B S hS a b).fst.hom) y) := by
  have hga := isLocallyOfFiniteType_representingMap.{u, w} B S hS T (yoneda.obj ν.base) hT
    (isAlgebraicSpace_yoneda B S hS ν.base)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS T).val.p)
    (PresheafOfCategories.sliceElementsEquivalenceOver ν.base) a ha
  have hfib : (twoFibreProductStructureFunctor B S hS (fibredCategory B S hS T)
      (schemeFibredCategory B S hS π.base) (schemeFibredCategory B S hS ν.base)
      a.hom b.hom).IsFibered :=
    (AlgebraicStacks.twoFibreProduct B S hS a b).val.property.isFibered
  have hsq := (isPullback_representingMap_twoFibreProductSquare B S hS
    (fibredCategory B S hS T) (schemeFibredCategory B S hS π.base)
    (schemeFibredCategory B S hS ν.base) T (yoneda.obj π.base) (yoneda.obj ν.base)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS T).val.p)
    (PresheafOfCategories.sliceElementsEquivalenceOver π.base)
    (PresheafOfCategories.sliceElementsEquivalenceOver ν.base) a.hom b.hom Q eQ).flip
  exact dimensionAtPoint_eq_dimensionAtPoint_of_isPullback_fieldSpectra' B S hS π ν hsq hQ hT
    hga y

/-- **The relative dimension of a chart of a quasi-DM algebraic stack over a field spectrum is at
most the dimension of the chart.** Let `h : 𝒵 ⟶ Spec k` be a quasi-DM 1-morphism, locally of
finite type, to the algebraic stack of the recorded base of a field-valued point, and let
`x₁ : T ⟶ 𝒵` be a 1-morphism, locally of finite type, from an algebraic space over `S`. Then at
every point `t` of `T` the relative dimension of `x₁` of **Stacks 0DRG** is at most `dim_t(T)`. -/
theorem relativeDimensionAt_le_dimensionAtPoint_of_isQuasiDM
    {𝒜 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)} (ν : FieldValuedPoint B S hS 𝒜)
    {𝒵 : AlgebraicStacks.{u, w} B S hS} (h : 𝒵 ⟶ schemeStack.{u, w} B S hS ν.base)
    (hqdm : AlgebraicStacks.IsQuasiDM B S hS h)
    (hh : AlgebraicStacks.IsLocallyOfFiniteType B S hS h)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (x₁ : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒵)
    (hx₁ : AlgebraicStacks.IsLocallyOfFiniteType B S hS x₁)
    (t : Space.points B S hS T) :
    relativeDimensionAt.{u, w} B S hS T hT 𝒵 x₁ hx₁ t ≤
      Space.dimensionAtPoint B S hS T hT t := by
  classical
  obtain ⟨π, q, -, hq, hval⟩ := exists_eq_fieldFibreDimensionAt B S hS T hT 𝒵 x₁ hx₁ t
  set x₂ := fieldValuedPointStackMorphism.{u, w} B S hS 𝒵 π with hx₂def
  obtain ⟨P, hP, ⟨eP⟩⟩ := AlgebraicStacks.isRepresentableByAlgebraicSpace_twoFibreProduct
    B S hS x₁ x₂ (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS π.base)
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := AlgebraicStacks.isRepresentableByAlgebraicSpace_twoFibreProduct
    B S hS (x₁ ≫ h) (x₂ ≫ h) (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS π.base)
  have hcomp : AlgebraicStacks.IsLocallyOfFiniteType B S hS (x₁ ≫ h) :=
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS x₁ h hx₁ hh
  have hsnd := AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS (x₁ ≫ h) (x₂ ≫ h)
    (AlgebraicStacks.twoFibreProductSquare B S hS (x₁ ≫ h) (x₂ ≫ h)).swap
    (Bicategory.isTwoFibreProduct_swap
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (x₁ ≫ h) (x₂ ≫ h)))
    hcomp
  have hgQ0 := isLocallyOfFiniteType_representingMap.{u, w} B S hS Q (yoneda.obj π.base) hQ
    (isAlgebraicSpace_yoneda B S hS π.base) eQ
    (PresheafOfCategories.sliceElementsEquivalenceOver π.base)
    (AlgebraicStacks.twoFibreProductSquare B S hS (x₁ ≫ h) (x₂ ≫ h)).snd hsnd
  have hgQ := Space.isLocallyOfFiniteType_comp' B S hS _ (baseSpectrumIso B S hS π).hom
    (isAlgebraicSpace_yoneda B S hS π.base) (isAlgebraicSpace_yoneda B S hS _) hgQ0
    (Space.isLocallyOfFiniteType_of_isEtale' B S hS _
      (Space.isEtale_of_iso B S hS (baseSpectrumIso B S hS π)))
  obtain ⟨xP, hxP⟩ := (bijective_spacePointMap_representing B S hS P
    (fieldFibreSquare B S hS x₁.hom π).pt eP).surjective q
  have hdimP := fieldFibreDimensionAt_eq_dimensionAtPoint.{u, w} B S hS x₁.hom 𝒵.property
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT) π P hP eP xP
  rw [hxP] at hdimP
  have hkey := AlgebraicStacks.dimensionAtPoint_le_dimensionAtPoint_representingMap_mapBase
    B S hS x₁ x₂ h P Q hP hQ eP eQ hqdm (baseSpacePoint B S hS π) _ hgQ xP
  have htgt := dimensionAtPoint_representingMap_twoFibreProduct_eq_dimensionAtPoint.{u, w}
    B S hS ν π T hT (x₁ ≫ h) hcomp (x₂ ≫ h) Q hQ eQ
    (Space.pointsMap B S hS P
      (representingMap B S hS (AlgebraicStacks.twoFibreProduct B S hS x₁ x₂).val
        (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ h) (x₂ ≫ h)).val P Q eP eQ
        (AlgebraicStacks.mapBase B S hS x₁ x₂ h).hom) xP)
  have hcompfst : (AlgebraicStacks.mapBase B S hS x₁ x₂ h).hom ≫
      (AlgebraicStacks.twoFibreProductSquare B S hS (x₁ ≫ h) (x₂ ≫ h)).fst.hom =
      (fieldFibreSquare B S hS x₁.hom π).fst := rfl
  have hrc := representingMap_comp B S hS P Q T eP eQ
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS T).val.p)
    (AlgebraicStacks.mapBase B S hS x₁ x₂ h).hom
    (AlgebraicStacks.twoFibreProductSquare B S hS (x₁ ≫ h) (x₂ ≫ h)).fst.hom
  rw [hcompfst] at hrc
  have hpt : Space.pointsMap B S hS P
      (representingMap B S hS (fieldFibreSquare B S hS x₁.hom π).pt
        (fibredCategory B S hS T) P T eP
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS T).val.p)
        (fieldFibreSquare B S hS x₁.hom π).fst) xP = t := by
    refine (bijective_spacePointMap_representing B S hS T (fibredCategory B S hS T)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).injective ?_
    rw [spacePointMap_representing_naturality B S hS P T
      (fieldFibreSquare B S hS x₁.hom π).pt (fibredCategory B S hS T) eP
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (fieldFibreSquare B S hS x₁.hom π).fst xP, hxP, hq]
    rfl
  have hfinal := Space.pointsMap_comp_apply B S hS
    (representingMap B S hS (AlgebraicStacks.twoFibreProduct B S hS x₁ x₂).val
      (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ h) (x₂ ≫ h)).val P Q eP eQ
      (AlgebraicStacks.mapBase B S hS x₁ x₂ h).hom)
    (representingMap B S hS (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ h) (x₂ ≫ h)).val
      (fibredCategory B S hS T) Q T eQ
      (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS T).val.p)
      (AlgebraicStacks.twoFibreProductSquare B S hS (x₁ ≫ h) (x₂ ≫ h)).fst.hom) xP
  rw [← hrc] at hfinal
  rw [hval, hdimP]
  exact hkey.trans (le_of_eq (htgt.trans
    (congrArg (Space.dimensionAtPoint B S hS T hT) (hfinal.symm.trans hpt))))

end AlgebraicGeometry.Stack

end
