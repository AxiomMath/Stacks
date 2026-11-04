module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionSmoothStacks
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange

/-!
# A closed immersion of algebraic stacks does not raise the dimension at a point

Let `𝒵 ↪ 𝒳` be a closed immersion of locally Noetherian algebraic stacks over `S` and let
`z ∈ |𝒵|` have image `x ∈ |𝒳|`. Then `dim_z(𝒵) ≤ dim_x(𝒳)`. This is **Stacks 0DRY**.

## Main results

* `AlgebraicGeometry.Stack.le_of_add_intCast_le_add_intCast`: an inequality of extended integers
  may be cancelled by a finite summand.
* `AlgebraicGeometry.Stack.exists_relativeStackDimensionAt_eq_intCast`: the relative dimension of
  Stacks 0DRL is finite.
* `AlgebraicGeometry.Stack.exists_relativeStackDimension_eq_intCast`: the same for
  `AlgebraicGeometry.Stack.relativeStackDimension`, without local Noetherianity.
* `AlgebraicGeometry.Stack.dimensionAtPoint_le_of_isClosedImmersion`: the dimension at a point
  does not increase along a closed immersion of locally Noetherian algebraic stacks.
* `AlgebraicGeometry.Stack.dimension_le_of_isClosedImmersion`: the same inequality between the
  dimensions of Stacks 0AFP, the supremum over the points of the one at a point.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 042U](https://stacks.math.columbia.edu/tag/042U)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRN](https://stacks.math.columbia.edu/tag/0DRN)
* [Stacks Project, Tag 0DRP](https://stacks.math.columbia.edu/tag/0DRP)
* [Stacks Project, Tag 0DRY](https://stacks.math.columbia.edu/tag/0DRY)
-/


@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An inequality of extended integers may be cancelled by a finite summand: if `A + c ≤ B + c`
for an integer `c`, then `A ≤ B`. -/
theorem le_of_add_intCast_le_add_intCast {A B : EInt} {c : ℤ}
    (h : A + ((c : ℤ) : EInt) ≤ B + ((c : ℤ) : EInt)) : A ≤ B := by
  have hc : ((c : ℤ) : EInt) = ((((c : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) := rfl
  rw [hc] at h
  induction A using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe A' =>
    induction B using WithBot.recBotCoe with
    | bot =>
      rw [show (⊥ : WithBot (WithTop ℤ)) + ((((c : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) = ⊥
        from rfl, ← WithBot.coe_add, le_bot_iff] at h
      exact absurd h WithBot.coe_ne_bot
    | coe B' =>
      rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at h
      rw [WithBot.coe_le_coe]
      induction A' using WithTop.recTopCoe with
      | top =>
        induction B' using WithTop.recTopCoe with
        | top => exact le_rfl
        | coe b =>
          rw [top_add, ← WithTop.coe_add, top_le_iff] at h
          exact absurd h WithTop.coe_ne_top
      | coe a =>
        induction B' using WithTop.recTopCoe with
        | top => exact le_top
        | coe b =>
          rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
          rw [WithTop.coe_le_coe]
          omega

/-- The relative dimension of a locally-of-finite-type 1-morphism at a point is an integer. -/
private theorem exists_relativeStackDimension_eq_intCast_aux
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    ∃ c : ℤ, relativeStackDimension.{u, w} B S hS f hf t = ((c : ℤ) : EInt) := by
  classical
  obtain ⟨W, hW, h, hsmh, w₀, hw₀⟩ :=
    exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒯 t
  have hh := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS h hsmh
  have hhf := AlgebraicStacks.isLocallyOfFiniteType_comp B S hS h f hh hf
  obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS W hW 𝒯 h hh w₀
  obtain ⟨d', hd'⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS W hW 𝒳 (h ≫ f) hhf w₀
  refine ⟨(d' : ℤ) - (d : ℤ), ?_⟩
  rw [relativeStackDimension_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf t hW h
    hsmh hh hhf w₀ hw₀ d hd, hd']
  rfl

/-- **The relative dimension of Stacks 0DRL is finite.** For a locally-of-finite-type 1-morphism
`f : 𝒯 ⟶ 𝒳` of locally Noetherian algebraic stacks over `S` and a point `t ∈ |𝒯|`, the relative
dimension `dim_t(𝒯_x)` is an integer. -/
theorem exists_relativeStackDimensionAt_eq_intCast
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    ∃ c : ℤ, relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t = ((c : ℤ) : EInt) :=
  exists_relativeStackDimension_eq_intCast_aux B S hS f hf t

/-- **The relative dimension of Stacks 0DRL is finite.** For a locally-of-finite-type 1-morphism
`f : 𝒯 ⟶ 𝒳` of algebraic stacks over `S` and a point `t ∈ |𝒯|`, the relative dimension
`AlgebraicGeometry.Stack.relativeStackDimension` of `f` at `t` is an integer. -/
theorem exists_relativeStackDimension_eq_intCast
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    ∃ c : ℤ, relativeStackDimension.{u, w} B S hS f hf t = ((c : ℤ) : EInt) :=
  exists_relativeStackDimension_eq_intCast_aux B S hS f hf t

/-- If `i : 𝒵 ⟶ 𝒳` is a closed immersion of locally Noetherian algebraic stacks over `S` and
`z ∈ |𝒵|` has image `x ∈ |𝒳|`, then `dim_z(𝒵) ≤ dim_x(𝒳)`, the dimensions being those of
Stacks 0AFN. -/
@[stacks 0DRY]
theorem dimensionAtPoint_le_of_isClosedImmersion
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (i : 𝒵 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsClosedImmersion B S hS i)
    (h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS 𝒵)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (z : points B S hS 𝒵.val.val 𝒵.val.property) :
    dimensionAtPoint B S hS 𝒵 h𝒵 z ≤
      dimensionAtPoint B S hS 𝒳 h𝒳
        (pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom z) := by
  classical
  obtain ⟨U, hU, a, hsma, u, hu⟩ :=
    exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒳
      (pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom z)
  have hfta := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS a hsma
  have h𝒰 : IsLocallyNoetherianStack.{u, w} B S hS
      (algebraicSpaceStack.{u, w} B S hS U hU) :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS a hfta h𝒳
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS i a
  have hQc : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquareAlgebraicStacks B S hS i a).underlying :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      i.hom a.hom
  have hsmfst : AlgebraicStacks.IsSmooth B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS i a).fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS a i
      (twoFibreProductSquareAlgebraicStacks B S hS i a) hQ hsma
  have hftfst := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS _ hsmfst
  have hQN : IsLocallyNoetherianStack.{u, w} B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS i a).pt :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS _ hftfst h𝒵
  obtain ⟨V, hV, ⟨eV⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
    B S hS 𝒵.val 𝒳.val (algebraicSpaceStack.{u, w} B S hS U hU).val i.hom a.hom
    (twoFibreProductSquareAlgebraicStacks B S hS i a).underlying.swap
    (Bicategory.isTwoFibreProduct_swap hQc) hi.1
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)
  obtain ⟨ζ, hζ₁, hζ₂⟩ := exists_point_of_isTwoFibreProduct B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS i a).underlying hQc z
    (stackPointOfSpacePoint B S hS U u) hu.symm
  obtain ⟨v, hv⟩ := (bijective_spacePointMap_representing B S hS V
    (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val eV).surjective ζ
  have hζ₁' : pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val.val
      (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val.property 𝒵.val.property
      (twoFibreProductSquareAlgebraicStacks B S hS i a).fst.hom.hom ζ = z := hζ₁
  have hζ₂' : pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val.val
      (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val.property
      (fibredCategory B S hS U).property
      (twoFibreProductSquareAlgebraicStacks B S hS i a).snd.hom.hom ζ =
      stackPointOfSpacePoint B S hS U u := hζ₂
  let φ := representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val
    (algebraicSpaceStack.{u, w} B S hS U hU).val V U eV
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (twoFibreProductSquareAlgebraicStacks B S hS i a).snd.hom
  let : (Space.immersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isImmersion_isLocalAtTarget_fppf B S hS
  have himm : Space.IsImmersion B S hS φ :=
    prop_representingMap_of_hasRelativeProperty B S hS (Space.immersionProperty B S hS)
      i.hom hi.1
      ((isImmersion_iff_hasRelativeProperty B S hS i.hom hi.1).1
        (fun U' y hy F hF he =>
          Space.isImmersion_of_isClosedImmersion B S hS (hi.2 U' y hy F hF he)))
      (algebraicSpaceStack.{u, w} B S hS U hU).val a.hom
      (twoFibreProductSquareAlgebraicStacks B S hS i a).underlying.swap
      (Bicategory.isTwoFibreProduct_swap hQc) V U hV hU eV
      (StacksRepresentableCFG.EquivalenceOver.refl _)
  have hnat := spacePointMap_representing_naturality B S hS V U
    (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val
    (algebraicSpaceStack.{u, w} B S hS U hU).val eV
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (twoFibreProductSquareAlgebraicStacks B S hS i a).snd.hom v
  have hle : dimensionAtPoint B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS i a).pt hQN ζ ≤
      dimensionAtPoint B S hS (algebraicSpaceStack.{u, w} B S hS U hU) h𝒰
        (stackPointOfSpacePoint B S hS U u) := by
    rw [dimensionAtPoint_eq_dimensionSubNat_zero_of_representing.{u, w} B S hS _ hQN V hV eV v
        ζ hv,
      dimensionAtPoint_eq_dimensionSubNat_zero_of_representing.{u, w} B S hS _ h𝒰 U hU
        (StacksRepresentableCFG.EquivalenceOver.refl _) (Space.pointsMap B S hS V φ v) _
        (by rw [hnat, hv, hζ₂'])]
    exact dimensionSubNat_mono 0
      (Space.dimensionAtPoint_le_of_isImmersion B S hS hV hU φ himm v)
  have hQP := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS i a).fst hsmfst hftfst hQN h𝒵 ζ
  have haP := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth B S hS a hsma hfta
    h𝒰 h𝒳 (stackPointOfSpacePoint B S hS U u)
  have hDRN := relativeStackDimensionAt_fst_eq_relativeStackDimensionAt.{u, w} B S hS i a
    (twoFibreProductSquareAlgebraicStacks B S hS i a) hQ hfta hftfst hQN h𝒰 h𝒵 h𝒳 ζ
  rw [hζ₁'] at hQP
  rw [hζ₂'] at hDRN
  rw [hu] at haP
  obtain ⟨c, hc⟩ := exists_relativeStackDimensionAt_eq_intCast B S hS a hfta h𝒰 h𝒳
    (stackPointOfSpacePoint B S hS U u)
  refine le_of_add_intCast_le_add_intCast (c := c) ?_
  calc dimensionAtPoint B S hS 𝒵 h𝒵 z + ((c : ℤ) : EInt)
      = dimensionAtPoint B S hS (twoFibreProductSquareAlgebraicStacks B S hS i a).pt hQN ζ := by
        rw [hQP, hDRN, hc]
    _ ≤ dimensionAtPoint B S hS (algebraicSpaceStack.{u, w} B S hS U hU) h𝒰
          (stackPointOfSpacePoint B S hS U u) := hle
    _ = dimensionAtPoint B S hS 𝒳 h𝒳
          (pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom z) +
            ((c : ℤ) : EInt) := by rw [haP, hc]

/-- **Stacks 0DRY for the dimension of Stacks 0AFP.** If `i : 𝒵 ⟶ 𝒳` is a closed immersion of
locally Noetherian algebraic stacks over `S`, then `dim(𝒵) ≤ dim(𝒳)`. -/
theorem dimension_le_of_isClosedImmersion
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (i : 𝒵 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsClosedImmersion B S hS i)
    (h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS 𝒵)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) :
    dimension B S hS 𝒵 h𝒵 ≤ dimension B S hS 𝒳 h𝒳 :=
  iSup_le fun z =>
    (dimensionAtPoint_le_of_isClosedImmersion B S hS i hi h𝒵 h𝒳 z).trans
      (le_iSup (fun x => dimensionAtPoint B S hS 𝒳 h𝒳 x) _)

end AlgebraicGeometry.Stack

end
