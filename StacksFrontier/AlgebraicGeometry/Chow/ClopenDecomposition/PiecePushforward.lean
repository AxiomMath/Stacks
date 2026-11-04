module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport

/-!
# Pushing a cycle forward from a piece, and restricting it again

Let `X` be a scheme locally of finite type over the base scheme of chapter 42 of the Stacks
Project, and let `V ⊆ X` be an open **and closed** subscheme — a piece of a decomposition
`X = \coprod_i X_i`, or a union of such pieces. Its inclusion is then a closed immersion, hence
proper, and a cycle on `V` pushes forward to a cycle on `X`. The two computations the proof of
Stacks 0FDZ performs on that pushforward are:

* restricting it back to `V` returns the original cycle, and
* restricting it to a piece disjoint from `V` returns zero.

Together these say that the pushforward from `V` is the section of the product decomposition
`Stacks.Chow.cycleGroupClopenEquiv` at the factor `V`. In the source they appear as the sentence
"the left hand side is the cycle on `X` restricting to `(c ∩ β)|_{X_i}` on `X_i` for `i ∈ I` with
`a(i) = j` and `0` else".

Both are coefficient computations. The fibre of `V.ι` over a point of `V` is a single point and
over a point outside `V` is empty, so the locally finite sum defining the pushforward collapses;
the residue degree of an open immersion is one, and delta-dimension is insensitive to passing to
an open subscheme by `Stacks.Chow.relativeDimension_opensι_comp`, so the weight is one.

## Main results

* `Stacks.Chow.residueDegree_eq_one_of_isOpenImmersion` — the residue degree of an open immersion
  is one at every point.
* `Stacks.Chow.opensRestrictCycle_properPushforward_self` — pushing forward from `V` and
  restricting back to `V` is the identity.
* `Stacks.Chow.opensRestrictCycle_properPushforward_of_disjoint` — pushing forward from `V` and
  restricting to a disjoint open subscheme gives zero.

## Implementation notes

Properness of `V.ι` is taken as an instance hypothesis rather than derived, because it holds
exactly when `V` is closed and that is a hypothesis, not an instance. For a piece of a
decomposition it is `Stacks.Chow.IsClopenDecomposition.isProper_ι`; a consumer writes
`haveI := h.isProper_ι i` and then applies the results below.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- The residue degree of an open immersion is one at every point: the residue field map of an
open immersion is an isomorphism. -/
theorem residueDegree_eq_one_of_isOpenImmersion {X' X : Scheme.{u}} (i : X' ⟶ X)
    [IsOpenImmersion i] (x : X') : i.residueDegree x = 1 := by
  rw [← Category.comp_id i, residueDegree_isOpenImmersion_comp i (𝟙 X) x,
    Scheme.Hom.residueDegree_id]

/-- The fibre of the inclusion of an open subscheme over a point of that subscheme is a single
point. -/
theorem preimage_singleton_opensι (V : X.Opens) (z : (V : Scheme.{u})) :
    V.ι.base ⁻¹' {V.ι.base z} = {z} := by
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨fun hw ↦ V.isOpenEmbedding.injective hw, fun hw ↦ hw ▸ rfl⟩

/-- The fibre of the inclusion of an open subscheme over a point of a disjoint open subscheme is
empty. -/
theorem preimage_singleton_opensι_of_disjoint {V W : X.Opens} (hVW : Disjoint V W)
    (z : (W : Scheme.{u})) : V.ι.base ⁻¹' {W.ι.base z} = ∅ := by
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  intro hw
  have hwW : (w.1 : X) ∈ W := by
    have hval : (w.1 : X) = (z.1 : X) := hw
    rw [hval]
    exact z.2
  exact hVW.le_bot (show (w.1 : X) ∈ V ⊓ W from ⟨w.2, hwW⟩)

/-- Pushing a cycle forward along the inclusion of an open and closed subscheme and restricting it
back to that subscheme returns the cycle: the fibre over a point of `V` is that one point, where
the residue degree is one and the delta-dimension is unchanged. -/
theorem opensRestrictCycle_properPushforward_self (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (V : X.Opens) [IsProper V.ι] (k : ℤ)
    (β : CycleGroup C (V.ι ≫ f) k) :
    opensRestrictCycle V (properPushforward C (V.ι ≫ f) f V.ι rfl k β).1 = β.1 := by
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [opensRestrictCycle_apply, properPushforward_apply, preimage_singleton_opensι,
    finsum_mem_singleton, relativeDimension_opensι_comp,
    residueDegree_eq_one_of_isOpenImmersion]
  simp

/-- Pushing a cycle forward along the inclusion of an open and closed subscheme and restricting it
to a disjoint open subscheme gives zero: the fibre over a point of the disjoint subscheme is
empty. -/
theorem opensRestrictCycle_properPushforward_of_disjoint (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (V W : X.Opens) [IsProper V.ι] (hVW : Disjoint V W) (k : ℤ)
    (β : CycleGroup C (V.ι ≫ f) k) :
    opensRestrictCycle W (properPushforward C (V.ι ≫ f) f V.ι rfl k β).1 = 0 := by
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [opensRestrictCycle_apply, properPushforward_apply,
    preimage_singleton_opensι_of_disjoint hVW, finsum_mem_empty]
  rfl

end Stacks.Chow

end
