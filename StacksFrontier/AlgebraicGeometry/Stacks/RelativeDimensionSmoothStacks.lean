module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition

/-!
# The smooth dimension formula for a 1-morphism of algebraic stacks

Let `f : 𝒰 ⟶ 𝒳` be a smooth 1-morphism of locally Noetherian algebraic stacks over `S` and let
`u ∈ |𝒰|` have image `x ∈ |𝒳|`. Then the dimension of `𝒰` at `u` splits as the dimension of
`𝒳` at `x` plus the relative dimension of `f` at `u`:
`dim_u(𝒰) = dim_x(𝒳) + dim_u(𝒰_x)`.
This is **Stacks 0DRP**, the algebraic-stack counterpart of the smooth dimension formula
Stacks 0DRI for algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.dimensionSubNat_eq_add_dimensionSubNat`: the arithmetic of the
  formula, namely that subtracting a natural number `d` from a dimension `δ ≠ -∞` is the same as
  subtracting `d'` from `δ` and then adding `d' - d`.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth`: the
  formula, with local finite type of `f` as a hypothesis alongside smoothness.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionAtPoint_add_relativeStackDimensionAt`:
  the formula for a smooth `f` alone, local finite type of `f` being derived from smoothness by
  `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth`.

## Implementation notes

Local finite type of `f` is a consequence of smoothness; it enters the statement only because
the relative dimension of Stacks 0DRL takes it as an argument.

## References

* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRI](https://stacks.math.columbia.edu/tag/0DRI)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRP](https://stacks.math.columbia.edu/tag/0DRP)
-/


@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Subtracting a natural number `d` from a dimension `δ ≠ -∞` of an algebraic space is the same
as subtracting another natural number `d'` from `δ` and then adding the extended integer
`d' - d`. -/
theorem dimensionSubNat_eq_add_dimensionSubNat {δ : WithBot ℕ∞} (hδ : δ ≠ ⊥) (d d' : ℕ) :
    dimensionSubNat δ d = dimensionSubNat δ d' + dimensionSubNat (d' : WithBot ℕ∞) d := by
  induction δ using WithBot.recBotCoe with
  | bot => exact absurd rfl hδ
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => rfl
    | coe n =>
      have h₁ : dimensionSubNat ((n : ℕ∞) : WithBot ℕ∞) d =
        (((n : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl
      have h₂ : dimensionSubNat ((n : ℕ∞) : WithBot ℕ∞) d' =
        (((n : ℤ) - (d' : ℤ) : ℤ) : EInt) := rfl
      have h₃ : dimensionSubNat ((d' : ℕ) : WithBot ℕ∞) d =
        (((d' : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl
      have h₄ : (((n : ℤ) - (d' : ℤ) : ℤ) : EInt) + (((d' : ℤ) - (d : ℤ) : ℤ) : EInt) =
        ((((n : ℤ) - (d' : ℤ)) + ((d' : ℤ) - (d : ℤ)) : ℤ) : EInt) := rfl
      rw [h₁, h₂, h₃, h₄]
      congr 1
      omega

/-- If `f : 𝒰 ⟶ 𝒳` is a smooth 1-morphism, locally of finite type, of locally Noetherian
algebraic stacks over `S` and `u ∈ |𝒰|` has image `x ∈ |𝒳|`, then
`dim_u(𝒰) = dim_x(𝒳) + dim_u(𝒰_x)`,
the relative dimension being that of Stacks 0DRL and the two dimensions those of Stacks 0AFN. -/
@[stacks 0DRP]
theorem dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒰 : IsLocallyNoetherianStack.{u, w} B S hS 𝒰)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (u : points B S hS 𝒰.val.val 𝒰.val.property) :
    dimensionAtPoint B S hS 𝒰 h𝒰 u =
      dimensionAtPoint B S hS 𝒳 h𝒳
          (pointsMap B S hS 𝒰.val.val 𝒰.val.property 𝒳.val.property f.hom.hom u) +
        relativeStackDimensionAt.{u, w} B S hS f hf h𝒰 h𝒳 u := by
  classical
  obtain ⟨V, hV, h, hsmh, v, hv⟩ :=
    exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒰 u
  have hh := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS h hsmh
  have hhf := AlgebraicStacks.isLocallyOfFiniteType_comp B S hS h f hh hf
  have hsmhf := AlgebraicStacks.isSmooth_comp B S hS h f hsmh hsm
  obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS V hV 𝒰 h hh v
  obtain ⟨d', hd'⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v
  have hx : pointsMap B S hS (fibredCategory B S hS V).val (fibredCategory B S hS V).property
      𝒳.val.property (h ≫ f).hom.hom (stackPointOfSpacePoint B S hS V v) =
      pointsMap B S hS 𝒰.val.val 𝒰.val.property 𝒳.val.property f.hom.hom u := by
    rw [← hv, pointsMap_comp B S hS (fibredCategory B S hS V).val
      (fibredCategory B S hS V).property 𝒰.val.property 𝒳.val.property h.hom.hom f.hom.hom
      (stackPointOfSpacePoint B S hS V v)]
    rfl
  rw [dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒰 h𝒰 u hV h hsmh hh v hv
      d hd,
    dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 _ hV (h ≫ f) hsmhf hhf
      v hx d' hd',
    relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf h𝒰 h𝒳 u hV h
      hsmh hh hhf v hv d hd, hd']
  exact dimensionSubNat_eq_add_dimensionSubNat
    (Space.dimensionAtPoint_ne_bot B S hS V hV v) d d'

/-- If `f : 𝒰 ⟶ 𝒳` is a smooth 1-morphism of locally Noetherian algebraic stacks over `S` and
`u ∈ |𝒰|` has image `x ∈ |𝒳|`, then
`dim_u(𝒰) = dim_x(𝒳) + dim_u(𝒰_x)`,
the relative dimension being that of Stacks 0DRL and the two dimensions those of Stacks 0AFN.
Local finite type of `f`, which the relative dimension takes as an argument, is derived from
smoothness by `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth`. -/
@[stacks 0DRP]
theorem dimensionAtPoint_eq_dimensionAtPoint_add_relativeStackDimensionAt
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (h𝒰 : IsLocallyNoetherianStack.{u, w} B S hS 𝒰)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (u : points B S hS 𝒰.val.val 𝒰.val.property) :
    dimensionAtPoint B S hS 𝒰 h𝒰 u =
      dimensionAtPoint B S hS 𝒳 h𝒳
          (pointsMap B S hS 𝒰.val.val 𝒰.val.property 𝒳.val.property f.hom.hom u) +
        relativeStackDimensionAt.{u, w} B S hS f
          (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hsm) h𝒰 h𝒳 u :=
  dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth B S hS f hsm
    (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hsm) h𝒰 h𝒳 u

end AlgebraicGeometry.Stack

end
