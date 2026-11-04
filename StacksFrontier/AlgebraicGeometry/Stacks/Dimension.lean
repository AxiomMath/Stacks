module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.WithBotTop
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack

/-!
# Dimension of a locally Noetherian algebraic stack, at a point and globally

Let `𝒳` be a locally Noetherian algebraic stack over a scheme `S`. Stacks 0AFN defines the
dimension of `𝒳` at a point `x ∈ |𝒳|` by `dim_x(𝒳) = dim_u(U) - dim_{e(u)}(R_u)`, computed on a
smooth presentation `[U/R] → 𝒳` and a point `u ∈ |U|` above `x`; here `R = U ×_𝒳 U`, the map
`s : R ⟶ U` is the (smooth) source map and `R_u = s^{-1}(u)`. Stacks 0AFP then defines
`dim(𝒳) = sup_{x ∈ |𝒳|} dim_x(𝒳)`.

## Main definitions

* `AlgebraicGeometry.Stack.dimensionSubNat` subtracts a finite relative dimension from a
  possibly infinite dimension of an algebraic space, as an extended integer.
* `AlgebraicGeometry.Stack.dimensionAtPoint` is **Stacks 0AFN**, the dimension of a locally
  Noetherian algebraic stack at a point.
* `AlgebraicGeometry.Stack.dimension` is **Stacks 0AFP**, the dimension of a locally Noetherian
  algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.dimensionAtPoint_le`: each admissible choice in the formula of
  Stacks 0AFN bounds the dimension at the point from above.
* `AlgebraicGeometry.Stack.dimension_eq_bot_of_isEmpty`: a stack with no points has dimension
  `⊥ = -∞`, the value Stacks Remark 0AFQ records for the empty stack.
* `AlgebraicGeometry.Stack.dimensionAtPoint_le_neg_one`: **Stacks 0DS5**, that an algebraic stack
  may have negative dimension — a smooth chart whose relative dimension at a point exceeds the
  dimension of the chart there forces `dim_x(𝒳) ≤ -1`.

## Implementation notes

Both values lie in `EInt`, Mathlib's extended integers `[-∞, ∞]`, i.e. `WithBot (WithTop ℤ)`.
Stacks 0AFR exhibits a classifying stack of negative dimension and Stacks Remark 0AFQ puts
`dim(∅) = -∞`, so neither `ℕ∞` nor `WithTop ℤ` is a possible codomain: the first excludes
negative values and the second has only a conditionally complete order, hence no canonical
value on the empty stack. `EInt` is a `CompleteLinearOrder`, so the supremum of Stacks 0AFP is
total and the empty stack receives `⊥`.

The fibre `R_u` above a point `u` of the object space of a presentation is the fibre product
`U ×_𝒳 Spec κ` of the presenting 1-morphism `U ⟶ 𝒳` with a field-valued point representing the
image of `u`, and `e(u)` is the point of it that `u` determines. So the subtrahend of Stacks
0AFN is the relative dimension at `u` of `U ⟶ 𝒳` in the sense of Stacks 0DRG, which is
`AlgebraicGeometry.Stack.relativeDimensionAt`, and the formula is read off any 1-morphism from
an algebraic space to `𝒳` that is smooth and locally of finite type, rather than off the source
map of a groupoid. Smoothness of that 1-morphism is what makes the subtrahend finite, and it is
required as a natural number in the defining condition.

As for the dimension of an algebraic space at a point (Stacks 04N5), the source defines
`dim_x(𝒳)` as *the* value shared by all admissible choices, and that is realized here by the
infimum of the admissible values, `AlgebraicGeometry.Stack.dimensionAtPoint_le` being the
resulting bound. Independence of the choice is Stacks 0AFM and is not proved here; neither is
the nonemptiness of the set of admissible values, which is the existence of a smooth
presentation together with the finiteness of its relative dimension.

Negativity goes the favourable way for an infimum: a single admissible choice bounds
`dim_x(𝒳)` from above, so one chart with `dim_t(T) < dim_t(T_x)` already forces `dim_x(𝒳) < 0`.
Stacks 0DS5 illustrates this with the classifying stack `[Spec k/𝐆_m]`, whose tautological chart
`Spec k ⟶ [Spec k/𝐆_m]` has `dim(Spec k) = 0` and relative dimension `dim 𝐆_m = 1`, so that the
dimension is `0 - 1 = -1`. That chart is the computation of Stacks 0DRK, which the library does
not have, so it is carried as the hypotheses `m`, `d` and `m < d` of
`AlgebraicGeometry.Stack.dimensionAtPoint_le_neg_one` rather than exhibited; the illustration is
the case `m = 0`, `d = 1`. The other assertion of Stacks 0DS5 — that a quasi-DM 1-morphism has
fibres of non-negative dimension — runs the unfavourable way for an infimum and needs the
independence of Stacks 0AFM, which is not available.

The hypothesis of local Noetherianity is an argument of both definitions but is used in
neither body, exactly as the algebraic-space hypothesis is in Stacks 04N5: it is what gives the
defining condition content, and carrying it lets a client write `dimension B S hS 𝒳 h𝒳 = 0`.

The universe `u` is that of the base scheme and of its relative big fppf site, while `w` is the
descent universe at which algebraicity of `𝒳` is tested; the two are independent.

## References

* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0AFP](https://stacks.math.columbia.edu/tag/0AFP)
* [Stacks Project, Tag 0AFQ](https://stacks.math.columbia.edu/tag/0AFQ)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRK](https://stacks.math.columbia.edu/tag/0DRK)
* [Stacks Project, Tag 0DS5](https://stacks.math.columbia.edu/tag/0DS5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The difference `δ - d` of a dimension `δ ∈ [-∞, ∞]` of an algebraic space and a finite
relative dimension `d`, as an extended integer. -/
noncomputable def dimensionSubNat (δ : WithBot ℕ∞) (d : ℕ) : EInt :=
  WithBotTop.rec (⊥ : EInt) (fun m : ℕ => (((m : ℤ) - (d : ℤ) : ℤ) : EInt)) (⊤ : EInt) δ

/-- `-∞ - d = -∞`. -/
@[simp]
theorem dimensionSubNat_bot (d : ℕ) : dimensionSubNat ⊥ d = ⊥ := rfl

/-- `∞ - d = ∞`. -/
@[simp]
theorem dimensionSubNat_top (d : ℕ) : dimensionSubNat ⊤ d = ⊤ := rfl

/-- For a natural number `m`, `dimensionSubNat m d` is the integer `m - d`. -/
@[simp]
theorem dimensionSubNat_coe (m d : ℕ) :
    dimensionSubNat (m : WithBotTop ℕ) d = (((m : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl

/-- **Stacks 0AFN.** The dimension of a locally Noetherian algebraic stack `𝒳` at a point `x`:
the infimum of `dim_t(T) - dim_t(T_x)` over the 1-morphisms `T ⟶ 𝒳` from an algebraic space
that are smooth and locally of finite type and the points `t ∈ |T|` above `x`. -/
@[stacks 0AFN]
noncomputable def dimensionAtPoint (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (_h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) : EInt :=
  sInf {z : EInt | ∃ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (_hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) (t : Space.points B S hS T),
    pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
        𝒳.val.property f.hom.hom (stackPointOfSpacePoint B S hS T t) = x ∧
      ∃ d : ℕ, relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞) ∧
        z = dimensionSubNat (Space.dimensionAtPoint B S hS T hT t) d}

/-- Every admissible choice in the formula of Stacks 0AFN bounds the dimension at the point
from above: its value is a member of the set whose infimum that dimension is. -/
theorem dimensionAtPoint_le (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) (t : Space.points B S hS T)
    (ht : pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
      𝒳.val.property f.hom.hom (stackPointOfSpacePoint B S hS T t) = x)
    (d : ℕ) (hd : relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞)) :
    dimensionAtPoint B S hS 𝒳 h𝒳 x ≤
      dimensionSubNat (Space.dimensionAtPoint B S hS T hT t) d :=
  sInf_le ⟨T, hT, f, hsm, hf, t, ht, d, hd, rfl⟩

/-- **Stacks 0AFP.** The dimension of a locally Noetherian algebraic stack: the supremum, over
the points of the stack, of its dimension at that point, as an extended integer. -/
@[stacks 0AFP]
noncomputable abbrev dimension (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) : EInt :=
  ⨆ x : points B S hS 𝒳.val.val 𝒳.val.property, dimensionAtPoint B S hS 𝒳 h𝒳 x

/-- A locally Noetherian algebraic stack with no points has dimension `-∞`, which is the value
Stacks Remark 0AFQ attaches to the empty stack. -/
theorem dimension_eq_bot_of_isEmpty (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    [IsEmpty (points B S hS 𝒳.val.val 𝒳.val.property)] :
    dimension B S hS 𝒳 h𝒳 = ⊥ :=
  iSup_of_empty _

/-- Subtracting a relative dimension `d` from a finite dimension `m < d` of an algebraic space
leaves a value at most `-1`. -/
theorem dimensionSubNat_le_neg_one {m d : ℕ} (h : m < d) :
    dimensionSubNat (m : WithBot ℕ∞) d ≤ ((-1 : ℤ) : EInt) := by
  have hz : dimensionSubNat (m : WithBot ℕ∞) d = (((m : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl
  rw [hz, WithBotTop.coe_le_coe]
  omega

/-- The negative-dimension half of Stacks 0DS5, with the chart of Stacks 0DRK as hypotheses. A
locally Noetherian algebraic stack has dimension at most `-1` at a point `x` as soon as some
smooth, locally of finite type 1-morphism `T ⟶ 𝒳` from an algebraic space has, at a point `t`
above `x`, relative dimension `d` exceeding the dimension `m` of `T` at `t`. The classifying stack
`[Spec k/𝐆_m]` is the case `m = 0`, `d = 1`. -/
theorem dimensionAtPoint_le_neg_one (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) (t : Space.points B S hS T)
    (ht : pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
      𝒳.val.property f.hom.hom (stackPointOfSpacePoint B S hS T t) = x)
    (m : ℕ) (hm : Space.dimensionAtPoint B S hS T hT t = (m : WithBot ℕ∞))
    (d : ℕ) (hd : relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞))
    (hmd : m < d) :
    dimensionAtPoint B S hS 𝒳 h𝒳 x ≤ ((-1 : ℤ) : EInt) :=
  (dimensionAtPoint_le B S hS 𝒳 h𝒳 x T hT f hsm hf t ht d hd).trans
    (hm ▸ dimensionSubNat_le_neg_one hmd)

/-- A locally Noetherian algebraic stack of dimension at most `-1` at each of its points has
dimension at most `-1`. -/
theorem dimension_le_neg_one (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h : ∀ x, dimensionAtPoint B S hS 𝒳 h𝒳 x ≤ ((-1 : ℤ) : EInt)) :
    dimension B S hS 𝒳 h𝒳 ≤ ((-1 : ℤ) : EInt) :=
  iSup_le h

end AlgebraicGeometry.Stack

end
