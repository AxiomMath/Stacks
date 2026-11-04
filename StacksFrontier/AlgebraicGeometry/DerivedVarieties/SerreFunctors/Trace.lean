module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.Basic

/-!
# The trace functional of a Serre pairing

Let `S` be a Serre equivalence on a `k`-linear category `C`. Evaluating the Serre pairing on
the identity of `X` gives a linear functional `serreTrace` on `X ⟶ S X`, and the whole pairing
is recovered from it by composition: `S.pairing X Y f g = serreTrace (f ≫ g)`. The trace is
cyclic, in the sense that moving a morphism from the left of a composition to the right
through `S` does not change it.

## Main definitions

* `CategoryTheory.serreTrace` is the linear functional `(X ⟶ S X) → k` obtained by pairing
  against the identity of `X`.

## Main results

* `CategoryTheory.serreTrace_comp` recovers the Serre pairing from the trace.
* `CategoryTheory.serreTrace_cyclic` is cyclic invariance of the trace.
* `CategoryTheory.serrePairing_hom_ext` detects equality of two morphisms into a Serre image
  by their Serre pairings.

## Implementation notes

`Module.Dual k V` is `V →ₗ[k] k`, so the trace is a plain linear functional and composes with
the pre- and post-composition maps `CategoryTheory.Linear.leftComp` and
`CategoryTheory.Linear.rightComp`. Surjectivity of the pairing makes it an extensionality
principle, which is the form in which the trace is used by both the uniqueness and the
exactness results for Serre functors.

## References

* [Stacks Project, Tag 0FY6](https://stacks.math.columbia.edu/tag/0FY6)
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory

universe u v w

variable (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- The trace functional of a Serre equivalence at `X`: the Serre pairing of the identity
of `X`, viewed as a linear functional on `X ⟶ S X`. -/
def serreTrace (S : SerreEquivalence k (C := C)) (X : C) :
    Module.Dual k (X ⟶ S.equivalence.functor.obj X) :=
  S.pairing X X (𝟙 X)

/-- The Serre pairing is the trace of the composition. -/
lemma serreTrace_comp (S : SerreEquivalence k (C := C)) {X Y : C} (f : X ⟶ Y)
    (g : Y ⟶ S.equivalence.functor.obj X) :
    serreTrace k S X (f ≫ g) = S.pairing X Y f g := by
  have h := congrArg (fun ψ => ψ g) (S.pairing_naturality_right (𝟙 X) f)
  simpa [serreTrace, LinearMap.dualMap_apply, Linear.leftComp_apply] using h.symm

/-- Cyclic invariance of the Serre trace. -/
lemma serreTrace_cyclic (S : SerreEquivalence k (C := C)) {X Y : C} (f : X ⟶ Y)
    (g : Y ⟶ S.equivalence.functor.obj X) :
    serreTrace k S Y (g ≫ S.equivalence.functor.map f) =
      serreTrace k S X (f ≫ g) := by
  rw [serreTrace_comp k S f g]
  have h := congrArg (fun ψ => ψ g) (S.pairing_naturality_left f (𝟙 Y))
  simpa [serreTrace, LinearMap.dualMap_apply, Linear.rightComp_apply] using h.symm

/-- Two morphisms into a Serre image agree as soon as all their Serre pairings agree. -/
lemma serrePairing_hom_ext (S : SerreEquivalence k (C := C))
    {X Y : C} {f g : Y ⟶ S.equivalence.functor.obj X}
    (h : ∀ a : X ⟶ Y, S.pairing X Y a f = S.pairing X Y a g) : f = g := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff k (f - g)).mp
  intro ψ
  obtain ⟨a, rfl⟩ := (S.pairing X Y).surjective ψ
  simp only [map_sub, h a, sub_self]

end CategoryTheory
