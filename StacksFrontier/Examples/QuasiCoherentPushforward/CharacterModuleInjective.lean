module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RingTheory.Flat.Tensor

/-!
# Character modules as injective objects

Over any commutative ring `R` the character module `R^∨ = Hom_ℤ(R, ℚ/ℤ)` is an injective
`R`-module, because `R` is flat over itself. The same is true of an arbitrary product of
copies of `R^∨`. This file records both facts in the categorical form
`CategoryTheory.Injective`, which is the form in which an injective object of
`ModuleCat R` is produced.

## Main results

* `Stacks.Examples.InjectiveTilde.injective_characterModule`: `R^∨` is an injective object
  of `ModuleCat R`.
* `Stacks.Examples.InjectiveTilde.injective_pi_characterModule`: a product of copies of `R^∨`
  is an injective object of `ModuleCat R`.
-/

@[expose] public section

open CategoryTheory

universe w u

namespace Stacks.Examples.InjectiveTilde

/-- The character module of a commutative ring is an injective module over that ring,
since the ring is flat over itself. -/
theorem module_injective_characterModule (R : Type u) [CommRing R] :
    Module.Injective R (CharacterModule R) :=
  Module.Flat.iff_characterModule_injective.mp (inferInstance : Module.Flat R R)

/-- The character module `R^∨` is an injective object of the category of `R`-modules. -/
theorem injective_characterModule (R : Type u) [CommRing R] :
    Injective (ModuleCat.of R (CharacterModule R)) :=
  (Module.injective_iff_injective_object R (CharacterModule R)).mp
    (module_injective_characterModule R)

/-- A product of copies of the character module `R^∨`, indexed by any type, is an injective
object of the category of `R`-modules. -/
theorem injective_pi_characterModule (R : Type u) [CommRing R] (ι : Type w) :
    Injective (ModuleCat.of R (ι → CharacterModule R)) := by
  have : Module.Injective R (CharacterModule R) := module_injective_characterModule R
  exact (Module.injective_iff_injective_object R (ι → CharacterModule R)).mp
    (Module.Injective.pi R fun _ : ι => CharacterModule R)

end Stacks.Examples.InjectiveTilde
