module

public import StacksFrontier.Homology.PseudoCoherent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherent objects of `D(R)` form a triangulated subcategory

The pseudo-coherent objects of `D(R)` ([Stacks, Tag 064Q]) are closed under isomorphisms,
contain zero, are stable under all shifts and satisfy two out of three in a distinguished
triangle ([Stacks, Tag 064R]).

## Main definitions

* `StacksDraft.PseudoCoherence.isPseudoCoherentObject`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.PseudoCoherence

universe u v

variable (R : Type u) [Ring R]

/-- Pseudo-coherence as a property of the objects of `D(R)`. -/
@[sga "6 I 2.6" "Fiber of D(C)_{C_0-coh}"]
def isPseudoCoherentObject : ObjectProperty (DerivedCategory (ModuleCat.{v} R)) :=
  fun K => IsPseudoCoherent K

/-- Pseudo-coherence is invariant under isomorphism in `D(R)`. -/
instance : (isPseudoCoherentObject.{u, v} R).IsClosedUnderIsomorphisms where
  of_iso e h := IsPseudoCoherent.ofIso h e

/-- The pseudo-coherent objects form a triangulated subcategory of `D(R)`: they contain zero, are
stable under all shifts, and satisfy two out of three in a distinguished triangle
([Stacks, Tag 064R]). -/
instance : (isPseudoCoherentObject.{u, v} R).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, (pseudoCoherent_of_isZero _ (isZero_zero _)).1⟩
  isStableUnderShiftBy a := ⟨fun K hK => (pseudoCoherent_iff_all _).2 fun m => by
    have h := ((pseudoCoherent_iff_all K).1 hK (m + a)).shift a
    rwa [add_sub_cancel_right] at h⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ =>
    (isPseudoCoherent_of_distinguished T hT).2.1 h₁ h₃

end StacksDraft.PseudoCoherence

end
