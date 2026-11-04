module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionDeligneMumford
public import StacksFrontier.Examples.Stacks.AffineLineQuotientDimension

/-!
# The dimension of an algebraic stack at a point versus the dimension of its point space

Stacks Remark 0DRK compares the dimension `dim_x(𝒳)` of a locally Noetherian algebraic stack at
a point (Stacks 0AFN) with the topologically defined quantity `dim_x |𝒳|`, the local Krull
dimension of the space of points. For Deligne-Mumford stacks which are suitably decent, for
instance quasi-separated, the two agree. For more general algebraic stacks they do not: over a
field, `|[𝔸¹/𝔾ₘ]|` has two points, one a specialisation of the other, so it has dimension one as
a topological space, while `dim_x [𝔸¹/𝔾ₘ] = 0` at both points; at the closed point the two
quantities are `0` and `1`. The classifying stack `[Spec k/𝔾ₘ]` has dimension `-1` at its unique
point.

## Main results

* `Stacks.Examples.remark_0DRK`: **Stacks 0DRK**, all assertions of the remark together.

## Implementation notes

The quotient stacks of the remark are stackifications, with morphisms in a larger universe than
the objects of the 2-category of algebraic stacks on which the dimension is defined. Their
assertions are therefore stated, as in
`Stacks.Examples.AffineLineQuotient.affineLineQuotientStack_points_dimension`, for every object
of that 2-category equivalent over the site to the quotient stack, together with the existence of
one. The remark's "this will typically not be the case" is recorded by the example: at the closed
point `x₀` of `|[𝔸¹/𝔾ₘ]|`, every point specializes to `x₀`, so `dim_{x₀} |𝒳|` is the dimension
`1` of the whole space, which differs from `dim_{x₀}(𝒳) = 0`.

## References

* [Stacks Project, Tag 0DRK](https://stacks.math.columbia.edu/tag/0DRK)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Examples

open AffineLineQuotient

attribute [local instance] Stack.pointTopology

/-- **Stacks 0DRK.** The comparison of the dimension of an algebraic stack at a point (Stacks
0AFN) with the local Krull dimension of its space of points.
1. For a locally Noetherian Deligne-Mumford stack `𝒳` which is decent, `dim_x(𝒳) = dim_x |𝒳|`
   at every point `x`.
2. The same holds when `𝒳` is quasi-separated.
3. Over a field `k`, the quotient stack `[𝔸¹/𝔾ₘ]` of the multiplication action is an algebraic
   stack, and for every object `𝒳` of the 2-category of algebraic stacks equivalent to it, `|𝒳|`
   has exactly two points, one a specialisation of the other, `|𝒳|` has Krull dimension `1`, and
   `𝒳` is locally Noetherian with `dim_x(𝒳) = 0` at both points `x`.
4. Consequently the equality of 1 fails for such an `𝒳`: at some point `dim_x(𝒳) ≠ dim_x |𝒳|`.
5. Over a field `k`, the classifying stack `[Spec k/𝔾ₘ]` is an algebraic stack, and every object
   `𝒳` equivalent to it is locally Noetherian, with a unique point `x`, at which
   `dim_x(𝒳) = -1`. -/
@[stacks 0DRK "the whole remark: dim_x(𝒳) = dim_x |𝒳| for decent (in particular \
quasi-separated) locally Noetherian Deligne-Mumford stacks; for [A¹/Gₘ] over a field |𝒳| has two \
points, one a specialisation of the other, |𝒳| has dimension 1 and dim_x(𝒳) = 0 at both points, \
so the equality fails; [Spec k/Gₘ] has dimension -1 at its unique point"]
theorem remark_0DRK :
    (∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
      (h𝒳 : Stack.IsLocallyNoetherianStack.{u, w} B S hS 𝒳),
      Stack.IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val → Stack.IsDecent B S hS 𝒳.val →
      ∀ x : Stack.points B S hS 𝒳.val.val 𝒳.val.property,
        Stack.dimensionAtPoint B S hS 𝒳 h𝒳 x =
          Stack.dimensionSubNat
            (topologicalKrullDimAt (Stack.points B S hS 𝒳.val.val 𝒳.val.property) x) 0) ∧
    (∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (hZ : B.Contains (⊤_ Scheme.{u}))
      (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
      (h𝒳 : Stack.IsLocallyNoetherianStack.{u, w} B S hS 𝒳),
      Stack.IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val →
      Stack.AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳 →
      ∀ x : Stack.points B S hS 𝒳.val.val 𝒳.val.property,
        Stack.dimensionAtPoint B S hS 𝒳 h𝒳 x =
          Stack.dimensionSubNat
            (topologicalKrullDimAt (Stack.points B S hS 𝒳.val.val 𝒳.val.property) x) 0) ∧
    (∀ (C : BigFppfSite.{u}) (k : Type u) [Field k] (hk : C.Contains (Spec (.of k))),
      (∃ 𝒳 : Stack.AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (affineLineQuotientStack C (Spec (.of k)) hk).p 𝒳.val.val.p)) ∧
      ∀ (𝒳 : Stack.AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_e : StacksRepresentableCFG.EquivalenceOver
          (affineLineQuotientStack C (Spec (.of k)) hk).p 𝒳.val.val.p),
        (∃ x₀ x₁ : Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property,
          x₀ ≠ x₁ ∧ (∀ x, x = x₀ ∨ x = x₁) ∧ x₁ ⤳ x₀) ∧
        topologicalKrullDim (Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property) = 1 ∧
        Stack.IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒳 ∧
        ∀ (h𝒳 : Stack.IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒳) x,
          Stack.dimensionAtPoint C (Spec (.of k)) hk 𝒳 h𝒳 x = 0) ∧
    (∀ (C : BigFppfSite.{u}) (k : Type u) [Field k] (hk : C.Contains (Spec (.of k)))
      (𝒳 : Stack.AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
      (_e : StacksRepresentableCFG.EquivalenceOver
        (affineLineQuotientStack C (Spec (.of k)) hk).p 𝒳.val.val.p)
      (h𝒳 : Stack.IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒳),
      ∃ x : Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property,
        Stack.dimensionAtPoint C (Spec (.of k)) hk 𝒳 h𝒳 x ≠
          Stack.dimensionSubNat
            (topologicalKrullDimAt (Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property)
              x) 0) ∧
    (∀ (C : BigFppfSite.{u}) (k : Type u) [Field k] (hk : C.Contains (Spec (.of k))),
      (∃ 𝒳 : Stack.AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (Stack.classifyingStack C hk (multiplicativeGroupOverField C hk)).val.p 𝒳.val.val.p)) ∧
      ∀ (𝒳 : Stack.AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_e : StacksRepresentableCFG.EquivalenceOver
          (Stack.classifyingStack C hk (multiplicativeGroupOverField C hk)).val.p 𝒳.val.val.p),
        Stack.IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒳 ∧
        ∃ x : Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property,
          (∀ y, y = x) ∧
          ∀ h𝒳 : Stack.IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒳,
            Stack.dimensionAtPoint C (Spec (.of k)) hk 𝒳 h𝒳 x = ((-1 : ℤ) : EInt)) := by
  refine ⟨fun B S hS 𝒳 h𝒳 hDM hdec x =>
      Stack.dimensionAtPoint_eq_topologicalKrullDimAt_of_isDeligneMumfordStack B S hS 𝒳 h𝒳 hDM
        hdec x,
    fun B S hS hZ 𝒳 h𝒳 hDM hqs x =>
      Stack.dimensionAtPoint_eq_topologicalKrullDimAt_of_isDeligneMumfordStack_of_quasiSeparated
        B S hS hZ 𝒳 h𝒳 hDM hqs x,
    fun C k _ hk => affineLineQuotientStack_points_dimension C hk,
    fun C k _ hk 𝒳 e h𝒳 => ?_,
    fun C k _ hk => classifyingStack_multiplicativeGroup_dimension C hk⟩
  obtain ⟨⟨x₀, x₁, -, hall, hspec⟩, hdim, -, hzero⟩ :=
    (affineLineQuotientStack_points_dimension.{u, w} C hk).2 𝒳 e
  refine ⟨x₀, ?_⟩
  rw [hzero h𝒳 x₀, topologicalKrullDimAt_eq_topologicalKrullDim_of_forall_specializes
    (fun y => (hall y).elim (fun h => h ▸ specializes_rfl) (fun h => h ▸ hspec)), hdim]
  decide

end Stacks.Examples

end
