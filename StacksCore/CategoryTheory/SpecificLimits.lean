module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import StacksCore.Tactic.StacksAttribute

/-! # Basic definitions and constructions
This file adds stacks tags to various mathlib declarations around specific limits and colimits.
-/

@[expose] public section

open CategoryTheory Limits

add_to_stacks 001S "A product is a limiting binary fan, so this in combination with `IsLimit`
  covers binary products. API specific to binary products is provided in the namespace
  `BinaryFan.IsLimit`, while API that holds more generally (like uniqueness up to isomorphism)
  is provided in the namespace `IsLimit`." BinaryFan
add_to_stacks 001S "A constructor for `IsLimit` using the usual data of a binary product"
  BinaryFan.IsLimit.mk
add_to_stacks 001S "Prop-valued typeclass stating that two objects have a product" HasBinaryProduct
add_to_stacks 001S "A choice of product, when one exists" Limits.prod

add_to_stacks 04AO "A coproduct is a limiting binary cofan, so this in combination with `IsColimit`
  covers binary coproducts. API specific to binary coproducts is provided in the namespace
  `BinaryCofan.IsColimit`, while API that holds more generally (like uniqueness up to isomorphism)
  is provided in the namespace `IsColimit`." BinaryCofan
add_to_stacks 04AO "A constructor for `IsColimit` using the usual data of a binary coproduct"
  BinaryCofan.IsColimit.mk
add_to_stacks 04AO "Prop-valued typeclass stating that two objects have a product"
  HasBinaryCoproduct
add_to_stacks 04AO "A choice of coproduct, when one exists" coprod

add_to_stacks 0026 IsPushout
add_to_stacks 08N1 IsPushout

add_to_stacks 0028 "An equalizer is a limiting fork, so this in combination with `IsLimit`
  covers equalizers. API specific to equalizers is provided in the namespace
  `Fork.IsLimit`, while API that holds more generally (like uniqueness up to isomorphism)
  is provided in the namespace `IsLimit`." Fork
add_to_stacks 0028 "A constructor for `IsLimit` using the usual data of an equalizer"
  Fork.IsLimit.mk
add_to_stacks 0028 "Prop-valued typeclass stating that two morphisms have an equalizer" HasEqualizer
add_to_stacks 0028 "A choice of equalizer, when one exists" equalizer

add_to_stacks 002A "A coequalizer is a limiting cofork, so this in combination with `IsColimit`
  covers coequalizers. API specific to coequalizers is provided in the namespace
  `Cofork.IsColimit`, while API that holds more generally (like uniqueness up to isomorphism)
  is provided in the namespace `IsColimit`." Cofork
add_to_stacks 002A "A constructor for `IsColimit` using the usual data of a coequalizer"
  Cofork.IsColimit.mk
add_to_stacks 002A "Prop-valued typeclass stating that two morphisms have a coequalizer"
  HasCoequalizer
add_to_stacks 002A "A choice of coequalizer, when one exists" coequalizer

add_to_stacks 002C "Structure exhibiting an object as initial" IsInitial
add_to_stacks 002C "Structure exhibiting an object as terminal" IsTerminal

add_to_stacks 0034 "Prop-valued typeclass for left exact functors" PreservesFiniteLimits
add_to_stacks 0034 "Prop-valued typeclass for right exact functors" PreservesFiniteColimits

add_to_stacks 0035 "2. => 1." preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts
add_to_stacks 0035 "3. => 1." preservesFiniteLimits_of_preservesTerminal_and_pullbacks

add_to_stacks 0GMN "2. => 1." preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
add_to_stacks 0GMN "3. => 1." preservesFiniteColimits_of_preservesInitial_and_pushouts

add_to_stacks 002I "The functor that a product of a family of objects is a limit of"
  Discrete.functor
add_to_stacks 002I "Prop-valued typeclass stating that a product exists" HasProduct
add_to_stacks 002I "A choice of product, when one exists" piObj

add_to_stacks 002J "The functor that a coproduct of a family of objects is a colimit of"
  Discrete.functor
add_to_stacks 002J "Prop-valued typeclass stating that a coproduct exists" HasCoproduct
add_to_stacks 002J "A choice of coproduct, when one exists" sigmaObj
