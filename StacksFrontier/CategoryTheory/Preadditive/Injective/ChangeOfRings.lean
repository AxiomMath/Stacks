module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction

import StacksCore.Tactic.StacksAttribute

/-!
# Injectives and restriction of scalars

This file formalizes Stacks Project, Tag 03B8.  For a map of commutative rings
`f : R →+* S`, restriction of scalars takes every injective `S`-module to an injective
`R`-module exactly when `f` is flat.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **Stacks Project, Tag 03B8.**  Every injective `S`-module remains injective after
restriction of scalars along `f : R →+* S` if and only if `f` is flat.

The forward implication uses that extension of scalars along a flat map is exact.  Conversely,
if restriction of scalars preserves injectives, its left adjoint preserves monomorphisms; since
extension of scalars already preserves colimits, it is exact, and hence `S` is flat over `R`. -/
@[stacks 03B8 "flatness criterion"]
theorem ModuleCat.flat_iff_restrictScalars_preservesInjectiveObjects
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.Flat ↔ (ModuleCat.restrictScalars.{u} f).PreservesInjectiveObjects := by
  let U := ModuleCat.restrictScalars.{u} f
  let V := ModuleCat.extendScalars.{u} f
  let adj : V ⊣ U := ModuleCat.extendRestrictScalarsAdj.{u, u, u} f
  let : V.Additive := adj.left_adjoint_additive
  constructor
  · intro hf
    exact preservesInjectiveObjects_of_isExact U V adj
      ⟨ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf,
        (adj.leftAdjoint_preservesColimits.{u, u}).preservesFiniteColimits⟩
  · intro h
    let : V.PreservesMonomorphisms :=
        Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
        adj
    let : PreservesFiniteLimits V := (isExact_of_preservesMonomorphisms U V adj).1
    algebraize [f]
    exact (Module.Flat.iff_preservesFiniteLimits_tensorLeft (ModuleCat.of R S)).2
      (comp_preservesFiniteLimits V U)
