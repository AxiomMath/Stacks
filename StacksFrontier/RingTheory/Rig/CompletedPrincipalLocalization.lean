module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Comparison
public import StacksFrontier.RingTheory.Rig.ClosedPoint

/-!
# Completed principal localizations of an adic topological ring

For an ideal `I` of a commutative ring `A` and an element `f ∈ A`, the ring
`Rig.CompletedAway I f` is the completion of the principal localization `A[1/f]` along the
extension of `I`.  When `I` is an ideal of definition of a topological ring structure on `A`,
this is the *completed principal localization* `A_{f}` of `A` at `f`.

The choice of ideal of definition is immaterial: any two ideals of definition are mutually
cofinal, so the two completions of `A[1/f]` they produce are isomorphic as `A`-algebras over
`A[1/f]`.

## Main results

* `Rig.exists_pow_le_of_isIdealOfDefinition` — a power of one ideal of definition is contained
  in any other.
* `Rig.exists_completedAway_algEquiv_of` — the completed principal localization is independent
  of the ideal of definition used to form it.
* `Rig.isUnit_algebraMap_completedAway` — the localizing element becomes invertible in the
  completed principal localization.

## References

* [Stacks Project, Tag 0GGE](https://stacks.math.columbia.edu/tag/0GGE)
-/

@[expose] public section

namespace Rig

universe u

add_to_stacks 0GGE "the completed principal localization, along a chosen ideal" CompletedAway

section

variable {A : Type u} [CommRing A]

/-- The localizing element is invertible in the completed principal localization. -/
public theorem isUnit_algebraMap_completedAway (I : Ideal A) (f : A) :
    IsUnit (algebraMap A (CompletedAway I f) f) := by
  have h : IsUnit (algebraMap A (Localization.Away f) f) :=
    IsLocalization.Away.algebraMap_isUnit f
  have hcomp : algebraMap A (CompletedAway I f) f =
      algebraMap (Localization.Away f) (CompletedAway I f)
        (algebraMap A (Localization.Away f) f) := by
    simp [AdicCompletion.algebraMap_apply]
  rw [hcomp]
  exact h.map _

end

section

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- Some power of an ideal of definition is contained in any other ideal of definition. -/
public theorem exists_pow_le_of_isIdealOfDefinition {I J : Ideal A}
    (hI : TopologicalRing.IsIdealOfDefinition I)
    (hJ : TopologicalRing.IsIdealOfDefinition J) : ∃ n : ℕ, I ^ n ≤ J := by
  obtain ⟨n, hn⟩ := hI.2 (J : Set A) (hJ.1.mem_nhds J.zero_mem)
  exact ⟨n, SetLike.coe_subset_coe.mp hn⟩

/-- The completed principal localization is independent of the ideal of definition used to
form it: for ideals of definition `I` and `J` the `I`-adic and `J`-adic completions of `A[1/f]`
are isomorphic as `A`-algebras, compatibly with the maps from `A[1/f]`. -/
@[stacks 0GGE "independence of the ideal of definition"]
public theorem exists_completedAway_algEquiv_of {I J : Ideal A}
    (hI : TopologicalRing.IsIdealOfDefinition I)
    (hJ : TopologicalRing.IsIdealOfDefinition J) (f : A) :
    ∃ e : CompletedAway I f ≃ₐ[A] CompletedAway J f, ∀ x : Localization.Away f,
      e (AdicCompletion.of _ (Localization.Away f) x) =
        AdicCompletion.of _ (Localization.Away f) x := by
  obtain ⟨n, hn⟩ := exists_pow_le_of_isIdealOfDefinition hI hJ
  obtain ⟨m, hm⟩ := exists_pow_le_of_isIdealOfDefinition hJ hI
  have key {I J : Ideal A} {n : ℕ} (h : I ^ n ≤ J) :=
    (Ideal.map_pow (algebraMap A (Localization.Away f)) I n).symm.trans_le (Ideal.map_mono h)
  exact ⟨AdicCompletion.compareAlgEquiv A (key hn) (key hm),
    AdicCompletion.compareAlgEquiv_of A (key hn) (key hm)⟩

end

end Rig

end
