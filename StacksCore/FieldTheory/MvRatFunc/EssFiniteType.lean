module

public import Mathlib.RingTheory.EssentialFiniteness
public import StacksCore.FieldTheory.MvRatFunc.Basic

/-! # `MvRatFunc` is finitely generated as field extension -/

@[expose] public section

open Algebra

namespace MvRatFunc

@[stacks 0BU1]
instance essFiniteType (R σ : Type*) [CommRing R] [Finite σ] : EssFiniteType R (MvRatFunc σ R) :=
  inferInstance

end MvRatFunc
