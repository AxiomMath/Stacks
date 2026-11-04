module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackDimensionField

/-!
# The dimension of a quotient stack by a group of finite type over a field

Let `k` be a field, let `X` be an algebraic space locally of finite type over `k` and let `G` be a
group algebraic space locally of finite type over `k` acting on `X`; `G` need not be smooth, so the
group schemes `μ_p` and `α_p` in characteristic `p` are included. Then the quotient stack `[X/G]`
is an algebraic stack, locally Noetherian, of dimension `dim [X/G] = dim(X) - dim(G)`. In
particular the classifying stack `BG = [Spec k/G]` has dimension `-dim(G)`, a negative integer as
soon as `dim(G) > 0`.

## Main results

* `AlgebraicGeometry.Stack.dimension_quotientStack_eq_of_isLocallyOfFiniteType`:
  `dim [X/G] = dim X - dim G`.
* `AlgebraicGeometry.Stack.dimension_classifyingStack_eq_neg_of_isLocallyOfFiniteType`:
  `dim BG = -dim G`.
* `AlgebraicGeometry.Stack.dimension_classifyingStack_lt_zero_of_isLocallyOfFiniteType_of_pos`:
  `dim BG < 0` when `dim G > 0`.

## References

* [Stacks Project, Tag 0AFR](https://stacks.math.columbia.edu/tag/0AFR)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Stack

universe u w

variable {k : Type u} [Field k] (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))
variable (G : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk).obj
    (Space.terminalSpace C (Spec (.of k)) hk).property)

open scoped CategoryTheory.MonObj

/-- Let `X` be an algebraic space locally of finite type over a field `k`, and let
`G` be a group algebraic space locally of finite type over `k`, not necessarily smooth, acting on
`X`. Then the quotient stack `[X/G]` is an algebraic stack — it has a model `𝒬` in the 2-category
of algebraic stacks — the dimension of `G` is a natural number `m`, and every model of `[X/G]` is
locally Noetherian of dimension `dim(X) - m`. -/
@[stacks 0AFR "`dim [X/G] = dim X - dim G` for every group algebraic space locally of finite type \
over the field, smooth or not, acting on an algebraic space locally of finite type; the quotient \
stack is constructed"]
theorem dimension_quotientStack_eq_of_isLocallyOfFiniteType
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (X : Over (Space.terminalSpace C (Spec (.of k)) hk).obj) [ModObj G.obj.X X]
    (hX : IsAlgebraicSpace C (Spec (.of k)) hk X.left)
    (hXft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk X.hom) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
            G.obj.X X G.property hX).groupoid).p 𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver
          (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
            G.obj.X X G.property hX).groupoid).p 𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN =
            dimensionSubNat (Space.dimension C (Spec (.of k)) hk X.left hX) m :=
  dimension_quotientStack_eq_of_isAlgebraicStack_flat.{u, w} C hk G
    (fun A' => forall_isAlgebraicStack_quotientStack_of_flat.{u, w} A') hGft X hX hXft

/-- For a group algebraic space `G` locally of finite type over a field `k`, not necessarily
smooth, the classifying stack `BG` is an algebraic stack, the dimension of `G` is a natural number
`m`, and every model of `BG` is locally Noetherian of dimension `-m`. -/
@[stacks 0AFR "`dim BG = -dim G` for every group algebraic space locally of finite type over the \
field, smooth or not; the classifying stack is constructed"]
theorem dimension_classifyingStack_eq_neg_of_isLocallyOfFiniteType
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN = ((-(m : ℤ) : ℤ) : EInt) :=
  dimension_classifyingStack_eq_neg_of_isAlgebraicStack_flat.{u, w} C hk G
    (fun A' => forall_isAlgebraicStack_quotientStack_of_flat.{u, w} A') hGft

/-- For a group algebraic space `G` of positive dimension, locally of finite type over a field `k`
and not necessarily smooth, the classifying stack `BG` is an algebraic stack, and every model of
it is locally Noetherian of negative dimension. -/
@[stacks 0AFR "the dimension of an algebraic stack can be a negative integer: `dim BG < 0` for \
every group algebraic space of positive dimension locally of finite type over the field, smooth \
or not"]
theorem dimension_classifyingStack_lt_zero_of_isLocallyOfFiniteType_of_pos
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (hpos : 0 < Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property) :
    (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN < 0 :=
  dimension_classifyingStack_lt_zero_of_isAlgebraicStack_flat.{u, w} C hk G
    (fun A' => forall_isAlgebraicStack_quotientStack_of_flat.{u, w} A') hGft hpos

end AlgebraicGeometry.Stack

end
