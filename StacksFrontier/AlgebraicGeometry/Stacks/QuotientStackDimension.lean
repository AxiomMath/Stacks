module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.Dimension
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackDimensionFiniteType
public import StacksFrontier.Examples.Stacks.ClassifyingStackSmoothCovering

/-!
# The dimension of a quotient stack is at most `dim X - dim G`

Let `k` be a field, let `X` be an algebraic space locally of finite type over `k` and let `G` be a
group algebraic space locally of finite type over `k` acting on `X`. Stacks 0AFR computes
`dim [X/G] = dim(X) - dim(G)`; in particular `dim BG = dim [Spec k/G] = -dim(G)`, so the dimension
of an algebraic stack can be a negative integer, unlike that of a scheme. This file records the
upper bounds `dim [X/G] ≤ dim(X) - dim(G)` and `dim BG ≤ -dim(G)`, and `dim BG < 0` for a group of
positive dimension, read off the equalities, and the bound of the dimension of an algebraic stack
by one smooth chart.

## Main results

* `AlgebraicGeometry.Stack.dimension_le_dimensionSubNat_of_chart`: one smooth, locally of finite
  type 1-morphism `T ⟶ 𝒳` from an algebraic space, surjective on points and of relative
  dimension `d` at every point, bounds `dim(𝒳)` above by `dim(T) - d`.
* `AlgebraicGeometry.Stack.dimension_quotientStack_le`: `dim [X/G] ≤ dim(X) - dim(G)`.
* `AlgebraicGeometry.Stack.dimension_classifyingStack_le`: `dim BG ≤ -dim(G)`.
* `AlgebraicGeometry.Stack.dimension_classifyingStack_lt_zero`: `dim BG < 0` when `dim(G) > 0`.

## Implementation notes

The equalities of Stacks 0AFR are
`AlgebraicGeometry.Stack.dimension_quotientStack_eq_of_isLocallyOfFiniteType` and
`AlgebraicGeometry.Stack.dimension_classifyingStack_eq_neg_of_isLocallyOfFiniteType`; they rest on
the algebraicity of the quotient (Stacks 04WZ, 04TB, 06FI), the relative dimension of the
tautological chart `X ⟶ [X/G]`
(`AlgebraicGeometry.Stack.relativeDimensionAt_quotientStackModelProjection_eq_dimension`) and the
independence of the chart (Stacks 0AFM), all of which the library proves.

## References

* [Stacks Project, Tag 0AFR](https://stacks.math.columbia.edu/tag/0AFR)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Stack

universe u w

/-- Subtracting a fixed relative dimension from the dimension of an algebraic space is monotone
in that dimension. -/
theorem dimensionSubNat_mono (d : ℕ) {δ δ' : WithBot ℕ∞} (h : δ ≤ δ') :
    dimensionSubNat δ d ≤ dimensionSubNat δ' d := by
  induction δ' using WithBot.recBotCoe with
  | bot => rw [le_bot_iff.mp h]
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      rw [show ((⊤ : ℕ∞) : WithBot ℕ∞) = (⊤ : WithBot ℕ∞) from rfl, dimensionSubNat_top]
      exact le_top
    | coe n =>
      induction δ using WithBot.recBotCoe with
      | bot => rw [dimensionSubNat_bot]; exact bot_le
      | coe a =>
        induction a using ENat.recTopCoe with
        | top =>
          exact absurd (top_le_iff.mp (WithBot.coe_le_coe.mp h)) (ENat.natCast_ne_top n)
        | coe m =>
          have hL : dimensionSubNat ((m : ℕ∞) : WithBot ℕ∞) d =
            (((m : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl
          have hR : dimensionSubNat ((n : ℕ∞) : WithBot ℕ∞) d =
            (((n : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl
          have hmn : m ≤ n := by exact_mod_cast h
          rw [hL, hR, WithBotTop.coe_le_coe]
          omega

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- One smooth, locally of finite type chart `T ⟶ 𝒳` from an algebraic space which is surjective
on points and has relative dimension `d` at every point bounds the dimension of `𝒳` above by
`dim(T) - d`. -/
theorem dimension_le_dimensionSubNat_of_chart (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hsurj : ∀ x : points B S hS 𝒳.val.val 𝒳.val.property, ∃ t : Space.points B S hS T,
      pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
        𝒳.val.property f.hom.hom (stackPointOfSpacePoint B S hS T t) = x)
    (d : ℕ) (hd : ∀ t : Space.points B S hS T,
      relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞)) :
    dimension B S hS 𝒳 h𝒳 ≤ dimensionSubNat (Space.dimension B S hS T hT) d := by
  refine iSup_le fun x => ?_
  obtain ⟨t, ht⟩ := hsurj x
  exact (dimensionAtPoint_le B S hS 𝒳 h𝒳 x T hT f hsm hf t ht d (hd t)).trans
    (dimensionSubNat_mono d (le_iSup (fun s => Space.dimensionAtPoint B S hS T hT s) t))

/-! ### The dimension of `[X/G]` -/

section Quotient

variable {k : Type u} [Field k] (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))
variable (G : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk).obj
    (Space.terminalSpace C (Spec (.of k)) hk).property)

/-- Let `X` be an algebraic space locally of finite type over a field `k`, and let `G` be a group
algebraic space locally of finite type over `k`, not necessarily smooth, acting on `X`. Then the
dimension of `G` is a natural number `m`, and every model of the quotient stack `[X/G]` in the
2-category of algebraic stacks is locally Noetherian of dimension at most `dim(X) - m`. -/
@[stacks 0AFR "upper bound `dim [X/G] ≤ dim X - dim G` for every group algebraic space locally \
of finite type over the field, smooth or not, acting on an algebraic space locally of finite \
type; the equality is `dimension_quotientStack_eq_of_isLocallyOfFiniteType`"]
theorem dimension_quotientStack_le
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (X : Over (Space.terminalSpace C (Spec (.of k)) hk).obj) [ModObj G.obj.X X]
    (hX : IsAlgebraicSpace C (Spec (.of k)) hk X.left)
    (hXft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk X.hom) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver
          (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
            G.obj.X X G.property hX).groupoid).p 𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN ≤
            dimensionSubNat (Space.dimension C (Spec (.of k)) hk X.left hX) m := by
  obtain ⟨m, hm, -, h⟩ :=
    dimension_quotientStack_eq_of_isLocallyOfFiniteType.{u, w} C hk G hGft X hX hXft
  exact ⟨m, hm, fun 𝒬 e => (h 𝒬 e).imp fun _ h => h.le⟩

/-- For a group algebraic space `G` locally of finite type over a field `k`, not necessarily
smooth, the dimension of `G` is a natural number `m`, and every model of the classifying stack
`BG = [Spec k/G]` is locally Noetherian of dimension at most `-m`. -/
@[stacks 0AFR "upper bound `dim BG ≤ -dim G` for every group algebraic space locally of finite \
type over the field, smooth or not; the equality is \
`dimension_classifyingStack_eq_neg_of_isLocallyOfFiniteType`"]
theorem dimension_classifyingStack_le
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN ≤ ((-(m : ℤ) : ℤ) : EInt) := by
  obtain ⟨m, hm, -, h⟩ :=
    dimension_classifyingStack_eq_neg_of_isLocallyOfFiniteType.{u, w} C hk G hGft
  exact ⟨m, hm, fun 𝒬 e => (h 𝒬 e).imp fun _ h => h.le⟩

/-- The dimension of an algebraic stack can be a negative integer: for a group algebraic space `G`
of positive dimension, locally of finite type over a field `k` and not necessarily smooth, every
model of the classifying stack `BG` is locally Noetherian of negative dimension. -/
@[stacks 0AFR "the dimension of an algebraic stack can be a negative integer: every model of \
`BG` has negative dimension, for every group algebraic space of positive dimension locally of \
finite type over the field, smooth or not"]
theorem dimension_classifyingStack_lt_zero
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (hpos : 0 < Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property)
    (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
    (e : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p 𝒬.val.val.p) :
    ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
      dimension C (Spec (.of k)) hk 𝒬 hN < 0 :=
  (dimension_classifyingStack_lt_zero_of_isLocallyOfFiniteType_of_pos.{u, w} C hk G hGft
    hpos).2 𝒬 e

end Quotient

end AlgebraicGeometry.Stack

end
