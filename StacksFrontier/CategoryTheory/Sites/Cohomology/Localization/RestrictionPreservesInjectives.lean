module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
import StacksCore.Tactic.StacksAttribute

/-! # Restriction of sheaves of modules to a localized site preserves injectives

Let `(C, J)` be a site, `R` a sheaf of rings on it and `U` an object of `C`. Restriction along
`Over.forget U` sends a sheaf of `R`-modules to a sheaf of `R_U`-modules on the localized site
`C/U`; it is Mathlib's `SheafOfModules.overFunctor R U`, written `j_U^{-1}` in Stacks 03DH, and
its left adjoint is extension by zero `j_{U!}`. Extension by zero is exact (Stacks 03DJ,
`Stacks.Sites.ExtensionByZero.extensionByZero_exact`), so a right adjoint whose left adjoint
preserves monomorphisms preserves injective objects (Stacks 015Z). That is part (1) of Stacks
03F3: the restriction `I|_U` of an injective `R`-module `I` is an injective `R_U`-module.

## Main results

* `Stacks.Cohomology.Localization.preservesInjectiveObjects_overFunctor`: **Stacks 03F3 (1)**.
* `Stacks.Cohomology.Localization.injective_over`: the same statement for one injective module.

## Implementation notes

The sections of the modules, the rings and the site all lie in one universe. That is the
restriction carried by `Stacks.Sites.ExtensionByZero.extensionByZero_preservesMonomorphisms`,
whose proof identifies the sections of the extension-by-zero presheaf with a direct sum over
`Hom(V, U)` and uses Grothendieck's axiom AB4 for `ModuleCat` in that universe; nothing here adds
a restriction of its own. The two sheafification hypotheses are the ones that make `j_{U!}`
available at all, and they are likewise inherited.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.Localization

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 03F3 (1).** Restriction of sheaves of modules to the site localized at an object
preserves injective objects: its left adjoint, extension by zero, is exact. -/
@[stacks 03F3 "part (1)", sga "4 V 4.11" "1) injective case", sga "4 V 2.2" "special case"]
theorem preservesInjectiveObjects_overFunctor :
    (SheafOfModules.overFunctor.{u} R U).PreservesInjectiveObjects :=
  have := Stacks.Sites.ExtensionByZero.extensionByZero_preservesMonomorphisms J R U
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (SheafOfModules.pullbackPushforwardAdjunction
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)))

/-- **Stacks 03F3 (1)**, for one module: the restriction `I|_U` of an injective sheaf of
`R`-modules is an injective sheaf of `R_U`-modules. -/
@[stacks 03F3 "part (1), for one module", sga "4 V 4.11" "1) injective case"]
theorem injective_over (I : SheafOfModules.{u} R) [Injective I] : Injective (I.over U) :=
  have := preservesInjectiveObjects_overFunctor J R U
  Functor.injective_obj (SheafOfModules.overFunctor.{u} R U) I

end Stacks.Cohomology.Localization

end
