module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import StacksCore.Tactic.StacksAttribute

/-! # Finitely presented modules and finitely presented algebras

Part (2) of [Stacks, Tag 0D46]: if `S` is finitely presented as an `R`-module, then `R → S` is
of finite presentation. Mathlib states this as `Algebra.FinitePresentation.of_finitePresentation`.
-/

@[expose] public section

add_to_stacks 0D46 "(2): S finitely presented as an R-module ⇒ R → S of finite presentation"
  Algebra.FinitePresentation.of_finitePresentation
