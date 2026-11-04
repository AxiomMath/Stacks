module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented

/-!
# The dimension of an algebraic stack representable by an algebraic space

Stacks 0AFN defines the dimension of a locally Noetherian algebraic stack at a point and
records that it agrees with the dimension of Stacks 04N5 when the stack is an algebraic space.
This file proves that agreement.

## Main results

* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_zero_of_representing`: for a
  locally Noetherian algebraic stack `𝒵` represented by an algebraic space `W`, the dimension
  of Stacks 0AFN of `𝒵` at a point is the dimension of Stacks 04N5 of `W` there.

## Implementation notes

The two sides live in different ordered monoids — Stacks 04N5 takes values in `WithBot ℕ∞`
and Stacks 0AFN in `EInt` — so the right-hand side is written
`AlgebraicGeometry.Stack.dimensionSubNat δ 0`, the embedding that the formula of Stacks 0AFN
uses on a chart of relative dimension `0`.

That is exactly how the proof runs: a representing equivalence is a smooth chart of relative
dimension `0`, and the dimension formula of Stacks 0DRJ reads the dimension off it. The
1-morphism `W ⟶ 𝒵` of the equivalence is smooth and locally of finite type because its
morphism of representing presheaves of Stacks 04SW is an isomorphism — this is
`AlgebraicGeometry.Stack.representingIsoOfInverse` — and an isomorphism of algebraic spaces is
étale (Stacks 04XX), hence smooth and locally quasi-finite (Stacks 03XU); local quasi-finiteness
is relative dimension `0` everywhere by Stacks 04NV.

## References

* [Stacks Project, Tag 03XU](https://stacks.math.columbia.edu/tag/03XU)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XX](https://stacks.math.columbia.edu/tag/04XX)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AFN, agreement with the dimension of an algebraic space.** Let `𝒵` be a locally
Noetherian algebraic stack over `S` represented by an algebraic space `W`, and let `x ∈ |W|`
have image `z ∈ |𝒵|`. Then the dimension of `𝒵` at `z` is the dimension of `W` at `x`.

The chart of the representing equivalence is smooth, locally of finite type and of relative
dimension `0`, so the formula of Stacks 0DRJ computes the left-hand side as
`dim_x(W) - 0`. -/
@[stacks 0AFN "agreement with the dimension of an algebraic space"]
theorem dimensionAtPoint_eq_dimensionSubNat_zero_of_representing
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS 𝒵)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (x : Space.points B S hS W) (z : points B S hS 𝒵.val.val 𝒵.val.property)
    (hz : spacePointMap B S hS W 𝒵.val
      (representingEquivalence B S hS W 𝒵.val eW).functor x = z) :
    dimensionAtPoint B S hS 𝒵 h𝒵 z =
      dimensionSubNat (Space.dimensionAtPoint B S hS W hW x) 0 := by
  classical
  subst hz
  let a : fibredCategory B S hS W ⟶ 𝒵.val :=
    Bicategory.InducedBicategory.mkHom (representingEquivalence B S hS W 𝒵.val eW).functor
  let b : 𝒵.val ⟶ fibredCategory B S hS W :=
    Bicategory.InducedBicategory.mkHom (representingEquivalence B S hS W 𝒵.val eW).inverse
  have θ : a ≫ b ≅ 𝟙 (fibredCategory B S hS W) :=
    Bicategory.InducedBicategory.isoMk (representingEquivalence B S hS W 𝒵.val eW).unitIso
  have θ' : b ≫ a ≅ 𝟙 𝒵.val :=
    Bicategory.InducedBicategory.isoMk (representingEquivalence B S hS W 𝒵.val eW).counitIso
  have hcmp : (representingIsoOfInverse B S hS W W
      (StacksRepresentableCFG.EquivalenceOver.refl _) eW θ θ').hom =
      representingMap B S hS (fibredCategory B S hS W) 𝒵.val W W
        (StacksRepresentableCFG.EquivalenceOver.refl _) eW a := rfl
  have hetale := Space.isEtale_of_iso B S hS (representingIsoOfInverse B S hS W W
    (StacksRepresentableCFG.EquivalenceOver.refl _) eW θ θ')
  rw [hcmp] at hetale
  have hsmr := Space.isSmooth_of_isEtale B S hS hW hetale
  have hftr := Space.isLocallyOfFiniteType_of_isSmooth B S hS hsmr
  let c : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒵 := Bicategory.InducedBicategory.mkHom a
  have hsm : AlgebraicStacks.IsSmooth B S hS c :=
    (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (isAlgebraicStack_fibredCategory.{u, w} B S hS W hW) 𝒵.property W W hW hW
      (StacksRepresentableCFG.EquivalenceOver.refl _) eW a).mpr hsmr
  have hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS c :=
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (isAlgebraicStack_fibredCategory.{u, w} B S hS W hW) 𝒵.property a).mpr
      ((hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
        (isAlgebraicStack_fibredCategory.{u, w} B S hS W hW) 𝒵.property W W hW hW
        (StacksRepresentableCFG.EquivalenceOver.refl _) eW a).mpr hftr)
  have hd : relativeDimensionAt.{u, w} B S hS W hW 𝒵 c hf x = ((0 : ℕ) : WithBot ℕ∞) :=
    (relativeDimensionAt_eq_iff_hasRelativeDimensionAt_representingMap.{u, w} B S hS W hW 𝒵 c
      hf W hW eW x 0).mpr
      ((Space.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS _ hftr).mp
        (Space.isLocallyQuasiFinite_of_isEtale' B S hS hetale) x)
  have ht := congrFun (spacePointMap_comp B S hS W (fibredCategory B S hS W) 𝒵.val
    (BasedFunctor.id (fibredCategory B S hS W).val)
    (representingEquivalence B S hS W 𝒵.val eW).functor) x
  rw [BasedFunctor.id_comp] at ht
  exact dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒵 h𝒵 _ hW c hsm hf x
    ht.symm 0 hd

end AlgebraicGeometry.Stack

end
