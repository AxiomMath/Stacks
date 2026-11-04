module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import StacksFrontier.RingTheory.Depth.Defs.Defs

/-!
# Depth is invariant under a ring isomorphism

A ring isomorphism `e : A ≃+* B` matches the `A`-regular sequences in an ideal `I` with the
`B`-regular sequences in `I.map e`, and it matches the condition `I • A = A` with
`I.map e • B = B`.  So `Module.depth A I A = Module.depth B (I.map e) B`, and for local rings the
self-depth along the maximal ideal is an isomorphism invariant.

The statement is wanted whenever a local ring is presented in two ways — for instance the stalk
of a scheme at a point of an open subscheme against the stalk of the ambient scheme at the same
point, where the two are isomorphic but not equal.

## Main results

* `Module.depth_eq_of_ringEquiv`: `Module.depth A I A = Module.depth B (I.map e) B`.
* `Module.depth_self_eq_of_ringEquiv`: the self-depth of a local ring along its maximal ideal is
  invariant under a ring isomorphism.

## Implementation notes

The proof needs nothing but the definition of `Module.depth` and Mathlib's
`AddEquiv.isRegular_congr`.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
-/

@[expose] public section

/-- A ring isomorphism matches the regular sequences in an ideal with those in its image, so the
depth of a ring along an ideal is at most the depth of the target along the image ideal. -/
public theorem Module.depth_le_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (I : Ideal A) : Module.depth A I A ≤ Module.depth B (I.map (e : A →+* B)) B := by
  have hI : I • (⊤ : Submodule A A) = ⊤ ↔ (I.map (e : A →+* B)) • (⊤ : Submodule B B) = ⊤ := by
    simp [Ideal.map_eq_top_of_bijective (e : A →+* B) e.bijective]
  rw [Module.depth, Module.depth]
  by_cases h : I • (⊤ : Submodule A A) = ⊤
  · rw [ite_eq_left h, ite_eq_left (hI.1 h)]
  · rw [ite_eq_right h, ite_eq_right fun hc ↦ h (hI.2 hc)]
    refine iSup₂_le fun rs ⟨hmem, hreg⟩ ↦ ?_
    have hreg' : RingTheory.Sequence.IsRegular B (rs.map (e : A →+* B)) := by
      refine (AddEquiv.isRegular_congr (e := e.toAddEquiv) ?_).1 hreg
      exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x ↦ by
        simp [e.map_mul r x])
    have hmem' : ∀ r ∈ rs.map (e : A →+* B), r ∈ I.map (e : A →+* B) := by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
      exact Ideal.mem_map_of_mem _ (hmem a ha)
    calc ((rs.length : ℕ∞)) = (((rs.map (e : A →+* B)).length : ℕ∞)) := by simp
      _ ≤ _ := le_iSup₂ (f := fun (rs : List B) (_ : rs ∈ {rs : List B |
            (∀ r ∈ rs, r ∈ I.map (e : A →+* B)) ∧ RingTheory.Sequence.IsRegular B rs}) ↦
            ((rs.length : ℕ∞))) _ ⟨hmem', hreg'⟩

/-- The depth of a ring along an ideal is invariant under a ring isomorphism. -/
public theorem Module.depth_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (I : Ideal A) : Module.depth A I A = Module.depth B (I.map (e : A →+* B)) B := by
  refine le_antisymm (Module.depth_le_of_ringEquiv e I) ?_
  have h := Module.depth_le_of_ringEquiv e.symm (I.map (e : A →+* B))
  rwa [Ideal.map_map, show ((e.symm : B →+* A).comp (e : A →+* B)) = RingHom.id A from by
    ext a; simp, Ideal.map_id] at h

/-- **The self-depth of a local ring along its maximal ideal is invariant under a ring
isomorphism.** -/
public theorem Module.depth_self_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Module.depth A (IsLocalRing.maximalIdeal A) A =
      Module.depth B (IsLocalRing.maximalIdeal B) B := by
  rw [Module.depth_eq_of_ringEquiv e (IsLocalRing.maximalIdeal A)]
  congr 1
  exact IsLocalRing.map_ringEquiv_maximalIdeal e

end
