module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleClosedImmersionCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothRigSurjectiveClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersionAtlas

/-!
# Stacks 0GD6: rig-smooth rig-surjective closed immersions

Let `f : X ⟶ Y` be a closed immersion of locally Noetherian formal algebraic spaces over `S`.
**Stacks 0GD6** says that the following three conditions are equivalent:

1. `f` is rig-smooth and rig-surjective,
2. `f` is rig-étale and rig-surjective, and
3. for every affine formal algebraic space `V` and every morphism `V ⟶ Y` which is
   representable by algebraic spaces and étale the morphism `X ×_Y V ⟶ V` corresponds to a
   surjective morphism `B → A` in `WAdm^{Noeth}` whose kernel `J` has the following property:
   `I * J = 0` for some ideal of definition `I` of `B`.

Condition (3) is `AlgebraicGeometry.FormalSpace.HasAnnihilatedKerOnPullbackCharts`, and the
passage between it and the chart conditions of Stacks 0GD4 and Stacks 0GD5 — including the
ring-theoretic observation whose proof the source omits — is in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothRigSurjectiveClosedImmersion`. What is done
here is the source's "trivial combination" with Stacks 0GD4
(`AlgebraicGeometry.FormalSpace.isRigSmooth_tfae_of_isClosedImmersion'`) and Stacks 0GD5
(`AlgebraicGeometry.FormalSpace.isRigSurjective_iff_hasAnnihilatedKerPow_of_isClosedImmersion`).

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSmooth_and_isRigSurjective_tfae_of_isClosedImmersion'`:
  **Stacks 0GD6**.

## References

* [Stacks Project, Tag 0GD4](https://stacks.math.columbia.edu/tag/0GD4)
* [Stacks Project, Tag 0GD5](https://stacks.math.columbia.edu/tag/0GD5)
* [Stacks Project, Tag 0GD6](https://stacks.math.columbia.edu/tag/0GD6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GD6.** Let `f : X ⟶ Y` be a closed immersion of locally Noetherian formal
algebraic spaces over `S`. Then the following are equivalent: (1) `f` is rig-smooth and
rig-surjective; (2) `f` is rig-étale and rig-surjective; (3) on every affine representable étale
chart `V ⟶ Y` of the target the fibre product `X ×_Y V ⟶ V` is given by a surjection of
`WAdm^{Noeth}` whose kernel is annihilated by some ideal of definition of the source.

The equivalence of the two rigidity notions with the annihilation of the conormal module
`J / J ^ 2` is Stacks 0GD4, the identification of rig-surjectivity with the annihilation of a
power of the kernel is Stacks 0GD5, and the passage from "a power of `J` is annihilated and
`J / J ^ 2` is annihilated" to "`J` is annihilated" is `Rig.exists_idealOfDefinition_mul_eq_bot`,
applied chart by chart in `hasAnnihilatedKer_of_hasAnnihilatedConormal_of_hasAnnihilatedKerPow`.
-/
@[stacks 0GD6]
theorem isRigSmooth_and_isRigSurjective_tfae_of_isClosedImmersion' {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hf : IsClosedImmersion B S hS f) :
    List.TFAE
      [IsRigSmooth B S hS f ∧ IsRigSurjective B S hS f,
        IsRigEtale B S hS f ∧ IsRigSurjective B S hS f,
        HasAnnihilatedKerOnPullbackCharts B S hS f] := by
  have h0GD4 := isRigSmooth_tfae_of_isClosedImmersion' B S hS f hX hY hf
  have h0GD5 := isRigSurjective_iff_hasAnnihilatedKerPow_of_isClosedImmersion B S hS f hX hY hf
  tfae_have 2 → 1 := fun h ↦ ⟨(h0GD4.out 2 1).mp h.1, h.2⟩
  tfae_have 1 → 3 := fun h ↦
    hasAnnihilatedKer_of_hasAnnihilatedConormal_of_hasAnnihilatedKerPow B S hS f
      ((h0GD4.out 1 3).mp h.1) (h0GD5.mp h.2)
  tfae_have 3 → 2 := fun h ↦
    ⟨(h0GD4.out 3 2).mp (hasAnnihilatedConormal_of_hasAnnihilatedKer B S hS f h),
      h0GD5.mpr (hasAnnihilatedKerPow_of_hasAnnihilatedKer B S hS f h)⟩
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
