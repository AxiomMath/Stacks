module

public import Mathlib.CategoryTheory.RepresentedBy
import StacksCore.Tactic.StacksAttribute

/-! # Basic definitions and constructions
This file adds stacks tags from section 4.3: opposite categories and the Yoneda lemma to some
existing declarations.
-/

@[expose] public section

open CategoryTheory

add_to_stacks 001N "Contravariant functors from `C` to `D` are just functors `Cᵒᵖ ⥤ D` or `C ⥤ Dᵒᵖ`.
  Usually the former form is preferred." CategoryTheory.Functor
add_to_stacks 001N "Turn one representation of a contravariant functor into another" Functor.leftOp
add_to_stacks 001N "Turn one representation of a contravariant functor into another" Functor.rightOp

add_to_stacks 02X6 "A presheaf of sets is just a functor `Cᵒᵖ ⥤ Type u`." CategoryTheory.Functor

add_to_stacks 001Q "Predicate stating that a functor is represented by a given object"
  Functor.IsRepresentedBy
add_to_stacks 001Q "Structure exhibiting a functor as represented by a given object"
  Functor.RepresentableBy
