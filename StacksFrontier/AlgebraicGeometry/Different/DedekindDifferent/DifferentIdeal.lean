module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.Support.DedekindDifferentSetup

/-!
# The Dedekind different as an ideal

The Dedekind different of `B/A` is defined as a submodule of the generic fibre `B ⊗[A] Q(A)`. If
`1` belongs to the complementary module — equivalently, if the trace of every element of `B`
already lies in `A` — then the Dedekind different comes from an ideal of `B`, namely the inverse
image of the Dedekind different under the canonical map `B → B ⊗[A] Q(A)`.

## Main definitions

* `Stacks.Discriminant.dedekindDifferentIdeal` is the inverse image of the Dedekind different
  under the canonical map from `B`.

## Main results

* `Stacks.Discriminant.one_mem_complementaryModule_iff` says that `1` lies in the complementary
  module exactly when the generic-fibre trace of every element of `B` lies in `A`.
* `Stacks.Discriminant.dedekindDifferent_eq_map_ideal` says that, when `1` lies in the
  complementary module, the Dedekind different is exactly the image of this ideal.

## Implementation notes

The ideal is defined unconditionally as an inverse image. Under the stated hypothesis its image
under `B → B ⊗[A] Q(A)` equals the original submodule, and that equality is what expresses that
the Dedekind different is an ideal of `B`.

## References

* [Stacks Project, Tag 0BW1](https://stacks.math.columbia.edu/tag/0BW1)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- One lies in the Dedekind complementary module exactly when the generic-fibre trace of every
element of `B` belongs to the canonical image of `A` in its total quotient ring. -/
@[stacks 0BW1 "trace_iff_one_mem"]
theorem one_mem_complementaryModule_iff (setup : DedekindDifferentSetup A B) :
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) :=
      Algebra.TensorProduct.rightAlgebra
    (1 : B ⊗[A] FractionRing A) ∈ setup.complementaryModule ↔
      ∀ b : B, setup.trace (algebraMap B (B ⊗[A] FractionRing A) b) ∈
        Set.range (algebraMap A (FractionRing A)) := by
  simp

/-- The ideal of elements of `B` whose image belongs to the Dedekind different. -/
def dedekindDifferentIdeal (setup : DedekindDifferentSetup A B) : Ideal B :=
  setup.dedekindDifferent.comap
    (Algebra.linearMap B (B ⊗[A] FractionRing A))

/-- If one lies in the complementary module, the Dedekind different is the
image of an ideal of `B`. -/
@[stacks 0BW1 "one_mem_different_ideal"]
theorem dedekindDifferent_eq_map_ideal
    (setup : DedekindDifferentSetup A B)
    (h_one : (1 : B ⊗[A] FractionRing A) ∈ setup.complementaryModule) :
    setup.dedekindDifferent =
      Submodule.map (Algebra.linearMap B (B ⊗[A] FractionRing A))
        (dedekindDifferentIdeal setup : Submodule B B) := by
  refine (Submodule.map_comap_eq_of_le fun x hx => ?_).symm
  obtain ⟨b, hb⟩ := (setup.mem_dedekindDifferent x).mp hx 1 h_one
  exact ⟨b, by simpa using hb⟩

end Stacks.Discriminant
