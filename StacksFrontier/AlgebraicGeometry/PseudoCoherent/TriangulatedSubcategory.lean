module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.BoundedVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherent objects of `D(𝒪_X)` form a triangulated subcategory

On a scheme `X`, the pseudo-coherent objects of `D(𝒪_X)` ([Stacks, Tag 08CB]) are closed under
isomorphisms, contain zero, are stable under all shifts, and satisfy two out of three in a
distinguished triangle ([Stacks, Tag 08CD]).

## Main definitions

* `AlgebraicGeometry.Scheme.isPseudoCoherentObject`: pseudo-coherence as a property of the
  objects of `D(𝒪_X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- Pseudo-coherence ([Stacks, Tag 08CB]) as a property of the objects of `D(𝒪_X)`. -/
@[sga "6 I 2.6" "special case"]
def isPseudoCoherentObject : ObjectProperty (DerivedCategory X.Modules) :=
  fun E => RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E

/-- An object `E` of `D(𝒪_X)` satisfies `X.isPseudoCoherentObject` if and only if it is
pseudo-coherent. -/
theorem isPseudoCoherentObject_iff (E : DerivedCategory X.Modules) :
    X.isPseudoCoherentObject E ↔ RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E :=
  Iff.rfl

/-- An object `E` of `D(𝒪_X)` satisfies `X.isPseudoCoherentObject` if and only if it is
`m`-pseudo-coherent for every integer `m`. -/
theorem isPseudoCoherentObject_iff_forall (E : DerivedCategory X.Modules) :
    X.isPseudoCoherentObject E ↔
      ∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m :=
  RingedSpace.isPseudoCoherent_iff_forall (X := X.toRingedSpace) E

/-- The pseudo-coherent objects of `D(𝒪_X)` are closed under isomorphisms. -/
instance : X.isPseudoCoherentObject.IsClosedUnderIsomorphisms where
  of_iso e h := RingedSpace.IsPseudoCoherent.of_iso (X := X.toRingedSpace) h e

/-- The pseudo-coherent objects of `D(𝒪_X)` form a triangulated subcategory: they contain zero,
are stable under all shifts, and if two vertices of a distinguished triangle are pseudo-coherent,
so is the third. -/
instance : X.isPseudoCoherentObject.IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, (X.isPseudoCoherentObject_iff_forall _).2 fun m => by
    refine @RingedSpace.isPseudoCoherentFrom_of_isLE X.toRingedSpace _ _ m ?_
    exact DerivedCategory.TStructure.t.isLE_of_isZero (isZero_zero _) _⟩
  isStableUnderShiftBy a := ⟨fun E hE => (X.isPseudoCoherentObject_iff_forall _).2 fun m => by
    have h := ((X.isPseudoCoherentObject_iff_forall E).1 hE (m + a)).shift a
    rwa [add_sub_cancel_right] at h⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ =>
    (X.isPseudoCoherentObject_iff_forall _).2 fun m =>
      RingedSpace.isPseudoCoherentFrom_obj₂_of_distinguished (X := X.toRingedSpace) m T hT
        ((X.isPseudoCoherentObject_iff_forall _).1 h₁ m)
        ((X.isPseudoCoherentObject_iff_forall _).1 h₃ m)

end AlgebraicGeometry.Scheme

end
