module

public import StacksFrontier.RingTheory.FormsTrace.FramedCanonical
public import StacksFrontier.RingTheory.FormsTrace.ExistenceTransport

/-!
# Trace maps on forms of algebras that are framed or zero

A `Stacks.FormsTrace.AnyFrame` of an `A`-algebra `B` is a frame of some positive rank. This file
defines the trace maps `Θ_{B/A}` of an algebra which admits a frame, or `0` if it does not, and
shows that they are compatible with every pushout `(A, B) → (A', B')` between such algebras,
provided that `B'` admits a frame or is zero, and `B` admits a frame or is zero. These are the
local data glued to the trace maps of a finite syntomic morphism of schemes.

## Main definitions

* `Stacks.FormsTrace.AnyFrame`: a frame of some positive rank.
* `Stacks.FormsTrace.frameTrace`: the trace maps of a framed algebra, `0` for an algebra with no
  frame.

## Main results

* `Stacks.FormsTrace.frameTrace_formsMap_of_isPushout`: compatibility with pushouts.
* `Stacks.FormsTrace.isFormsTrace_frameTrace`, `isWedgeLinear_frameTrace`,
  `commutesWithD_frameTrace`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra

universe u

namespace Stacks.FormsTrace

/-- **A frame of some positive rank** of an `A`-algebra `B`. -/
structure AnyFrame (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] where
  /-- The rank. -/
  rank : ℕ
  /-- The rank is positive. -/
  [neZero : NeZero rank]
  /-- The frame. -/
  frame : ChartFrame rank A B

attribute [instance] AnyFrame.neZero

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- An algebra with a frame is finite over the base. -/
theorem AnyFrame.finite (F : AnyFrame A B) : Module.Finite A B :=
  Module.Finite.of_basis F.frame.basis

/-- An algebra with a frame is free over the base. -/
theorem AnyFrame.free (F : AnyFrame A B) : Module.Free A B :=
  Module.Free.of_basis F.frame.basis

/-- **The trace maps of two frames agree**, also for frames of different ranks. -/
theorem AnyFrame.trace_eq (F F' : AnyFrame A B) : F.frame.trace = F'.frame.trace := by
  funext p
  refine LinearMap.ext fun x => ?_
  have h := ChartFrame.trace_formsMap_of_isPushout A B F'.frame F.frame p x
  rwa [formsMap_self, formsMap_self] at h

open Classical in
/-- **The trace maps on forms** of an algebra admitting a frame (using any chosen frame), and `0`
for an algebra admitting none. -/
def frameTrace (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ] :=
  if h : Nonempty (AnyFrame A B) then h.some.frame.trace p else 0

/-- On an algebra with a frame, `frameTrace` is the trace of that frame (the choice does not
matter). -/
theorem frameTrace_eq (F : AnyFrame A B) (p : ℕ) : frameTrace A B p = F.frame.trace p := by
  have h : Nonempty (AnyFrame A B) := ⟨F⟩
  rw [frameTrace, dite_eq_left h, AnyFrame.trace_eq h.some F]

/-- `frameTrace` is the trace of any frame, as a family of maps. -/
private theorem frameTrace_eq_trace (F : AnyFrame A B) : frameTrace A B = F.frame.trace :=
  funext (frameTrace_eq F)

/-- An algebra with no frame, which is zero, has `frameTrace = 0`. -/
theorem frameTrace_of_isEmpty (h : IsEmpty (AnyFrame A B)) (p : ℕ) : frameTrace A B p = 0 := by
  rw [frameTrace, dite_eq_right (not_nonempty_iff.mpr h)]

/-- The forms of a zero ring are zero. -/
theorem subsingleton_forms (R : Type u) [CommRing R] [Subsingleton R] (p : ℕ) :
    Subsingleton (⋀[R]^p Ω[R⁄ℤ]) :=
  Module.subsingleton R _

/-- **Compatibility of `frameTrace` with pushouts.** Let `(A, B) → (A', B')` be a pushout of
algebras each of which admits a frame or is zero. Then `Θ_{B'/A'}(g^*x) = f^*Θ_{B/A}(x)`. -/
theorem frameTrace_formsMap_of_isPushout (A' B' : Type u) [CommRing A'] [CommRing B']
    [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B']
    [IsScalarTower A B B'] [Algebra.IsPushout A B A' B']
    (hB : Subsingleton B ∨ Nonempty (AnyFrame A B))
    (hB' : Subsingleton B' ∨ Nonempty (AnyFrame A' B')) (p : ℕ) (x : ⋀[B]^p Ω[B⁄ℤ]) :
    frameTrace A' B' p (formsMap B B' p x) = formsMap A A' p (frameTrace A B p x) := by
  rcases subsingleton_or_nontrivial A' with hA' | hA'
  · have := subsingleton_forms A' p
    exact Subsingleton.elim _ _
  rcases hB with hB | hF
  · have := subsingleton_forms B p
    rw [Subsingleton.elim x 0, map_zero, map_zero, map_zero, map_zero]
  · obtain ⟨F⟩ := hF
    -- `B'` is free of positive rank over the nontrivial ring `A'`, hence nonzero and framed
    rcases hB' with hB' | hF'
    · exact ((ChartFrame.baseChangeBasis A' B' F.frame).ne_zero 0 (Subsingleton.elim _ _)).elim
    obtain ⟨F'⟩ := hF'
    rw [frameTrace_eq F', frameTrace_eq F,
      ChartFrame.trace_formsMap_of_isPushout A' B' F.frame F'.frame]

/-- **Property (1) of Lemma 0FLB** for `frameTrace`, on an algebra which is framed or zero. -/
theorem isFormsTrace_frameTrace [Module.Finite A B] [Module.Projective A B]
    (hB : Subsingleton B ∨ Nonempty (AnyFrame A B)) : IsFormsTrace A B (frameTrace A B) := by
  rcases hB with hB | hF
  · intro p b ω
    rw [Subsingleton.elim b 0, zero_smul, map_zero, map_zero, zero_smul]
  · obtain ⟨F⟩ := hF
    rw [frameTrace_eq_trace F]
    exact F.frame.isFormsTrace_trace

/-- **Property (2) of Proposition 0FLC** for `frameTrace`, on an algebra which is framed or
zero. -/
theorem isWedgeLinear_frameTrace (hB : Subsingleton B ∨ Nonempty (AnyFrame A B)) :
    IsWedgeLinear A B (frameTrace A B) := by
  rcases hB with hB | hF
  · intro q p ω η
    have := subsingleton_forms B p
    rw [Subsingleton.elim η 0]
    simp
  · obtain ⟨F⟩ := hF
    rw [frameTrace_eq_trace F]
    exact F.frame.isWedgeLinear_trace

/-- **Compatibility with `d`** of `frameTrace`, on an algebra which is framed or zero. -/
theorem commutesWithD_frameTrace (hB : Subsingleton B ∨ Nonempty (AnyFrame A B)) :
    CommutesWithD A B (frameTrace A B) := by
  rcases hB with hB | hF
  · intro p η
    have := subsingleton_forms B p
    rw [Subsingleton.elim η 0]
    simp
  · obtain ⟨F⟩ := hF
    rw [frameTrace_eq_trace F]
    exact F.frame.commutesWithD_trace

end Stacks.FormsTrace

end
