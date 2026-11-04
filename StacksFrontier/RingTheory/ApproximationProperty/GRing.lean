module

public import StacksFrontier.RingTheory.ApproximationProperty.CohenData
public import StacksFrontier.RingTheory.ApproximationProperty.Core
public import StacksFrontier.RingTheory.ApproximationProperty.FormalFibres

/-!
# A Noetherian local ring with the approximation property is a G-ring

Stacks Project, Example 98.12.8 (Tag 07XI), concludes from the approximation property of the
henselization `Λ_𝔪^h` that `Λ_𝔪^h` is a G-ring, with the comment "insert future reference here";
the discussion in Smoothing Ring Maps, Section 16.1 (Tag 07BX) attributes the result to Rotthaus:
a Noetherian local ring with the approximation property is excellent. This file proves the part
used by the Stacks Project: a Noetherian local ring with the approximation property is a G-ring,
that is, its formal fibres are geometrically regular.

The proof is Rotthaus'. Its reductions (approximation passes to finite algebras, and geometric
regularity of the formal fibres reduces to regularity of the generic formal fibres of local
domains finite over the ring) are in `StacksFrontier.RingTheory.ApproximationProperty.FormalFibres`;
its core (the generic formal fibre of a local domain with the approximation property is regular)
is `Stacks.ApproximationProperty.isRegularLocalRing_localization_of_presentation`, which needs a
presentation of the completion by a complete regular local ring that is ind-smooth over a
Noetherian ring mapping to the original ring. That presentation is
`Stacks.ApproximationProperty.exists_cohenData_indSmooth`, from the Cohen structure theorem and
Popescu's theorem (Tag 07GC).

## Main results

* `IsLocalRing.HasApproximationProperty.core`: the core statement, in every universe.
* `IsLocalRing.HasApproximationProperty.isRegularRingHom_adicCompletion`: a Noetherian local ring
  with the approximation property has geometrically regular formal fibres.
* `IsLocalRing.HasApproximationProperty.isGRing`: a Noetherian local ring with the approximation
  property is a G-ring.

## References

* [C. Rotthaus, *Rings with approximation property*, Math. Ann. 287 (1990), 455–466][Rotthaus]
* [Stacks Project, Tag 07BX](https://stacks.math.columbia.edu/tag/07BX)
* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
-/

@[expose] public section

open IsLocalRing

universe u

namespace IsLocalRing.HasApproximationProperty

/-- **The core of Rotthaus' theorem** (Rotthaus, Claim (3.2)). For every Noetherian local domain
`B` with the approximation property and every prime `P` of the completion `B^∧` with
`P ∩ B = 0`, the local ring `B^∧_P` is regular. -/
theorem core : Core.{u} := by
  intro B _ _ _ _ hB P _ hP
  obtain ⟨R₀, R, _, _, _, _, _, _, hcomplete, ρ, hρ, hcompat, hind, e, y, hy𝔪, hy⟩ :=
    Stacks.ApproximationProperty.exists_cohenData_indSmooth B
  have := hcomplete
  exact Stacks.ApproximationProperty.isRegularLocalRing_localization_of_presentation hB hind ρ hρ
    hcompat y hy𝔪 hy P hP

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- **Rotthaus' theorem, formal fibres.** A Noetherian local ring with the approximation property
has geometrically regular formal fibres: its completion map is regular. -/
theorem isRegularRingHom_adicCompletion (hA : HasApproximationProperty A) :
    IsRegularRingHom (algebraMap A (AdicCompletion (maximalIdeal A) A)) :=
  isRegularRingHom_adicCompletion_of_core hA core

/-- **Rotthaus' theorem** (the G-ring part of Rotthaus, Theorem 1; the reference missing in
Stacks 07XI). A Noetherian local ring with the approximation property is a G-ring. -/
theorem isGRing (hA : HasApproximationProperty A) : IsGRing A :=
  isGRing_of_core hA core

end IsLocalRing.HasApproximationProperty

end
