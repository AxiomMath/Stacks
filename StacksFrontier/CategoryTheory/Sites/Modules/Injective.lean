module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
import StacksCore.Tactic.StacksAttribute

/-!
# An injective sheaf of modules is injective as a presheaf of modules

Let `R` be a sheaf of rings on a site and let `α : R₀ ⟶ R.obj` be a locally bijective morphism
from a presheaf of rings, so that `PresheafOfModules.sheafification α` is a left adjoint of
`SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α`. Sheafification of presheaves
of modules is exact, so by Stacks Tag 015Z that right adjoint preserves injective objects: an
injective sheaf of `R`-modules is injective as a presheaf of `R₀`-modules.

This is the first step of the proof of [Stacks, Tag 01EP] — "an injective `𝒪_X`-module is also
injective as an object of the category `PMod(𝒪_X)`" — and it is the exact analogue, for sheaves
of modules, of `CategoryTheory.sheafToPresheaf_preservesInjectiveObjects` in
`StacksFrontier/CategoryTheory/Sites/CechInjective.lean`, which is the same statement for sheaves
with values in an abelian category.

## Main results

* `SheafOfModules.forget_restrictScalars_preservesInjectiveObjects`: the functor
  `SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α` preserves injective objects.
* `SheafOfModules.injective_val` and `SheafOfModules.injective_val_of_injective`: **an injective
  sheaf of modules is injective as a presheaf of modules** — [Stacks, Tag 03FB] — in the form of
  an instance and in the form of a statement taking injectivity as an explicit argument.
* `SheafOfModules.forget_preservesInjectiveObjects`: the same statement in functorial form, as
  `(SheafOfModules.forget R).PreservesInjectiveObjects`.

## Implementation notes

Mathlib knows that `PresheafOfModules.sheafification α` preserves finite limits and that it is a
left adjoint, hence preserves colimits and zero morphisms; that it is additive is
`PresheafOfModules.sheafification_additive`, from
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor`. That, together with
the additivity of `SheafOfModules.forget` and of `PresheafOfModules.restrictScalars`, is
everything Stacks Tag 015Z (`preservesInjectiveObjects_of_isExact`) needs.

`SheafOfModules.injective_val` is stated for `α = 𝟙 R.obj`, where
`PresheafOfModules.restrictScalars α` is the identity functor definitionally — which is also how
Mathlib obtains its `Full` instance for that functor — so no transport along an isomorphism of
functors is needed.

`SheafOfModules.forget_preservesInjectiveObjects` is stated separately from
`SheafOfModules.forget_restrictScalars_preservesInjectiveObjects` because instance search keys on
the functor: a consumer that wants `(SheafOfModules.forget R).PreservesInjectiveObjects`, for
instance in order to apply right-derived-functor machinery, does not obtain it from the statement
about the composite with `PresheafOfModules.restrictScalars`.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 03FB](https://stacks.math.columbia.edu/tag/03FB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasSheafify J AddCommGrpCat.{v}]

/-- **Stacks Tag 015Z for sheaves of modules.** The forgetful functor from sheaves of
`R`-modules to presheaves of `R₀`-modules preserves injective objects, because sheafification of
presheaves of modules is an exact left adjoint of it. -/
instance SheafOfModules.forget_restrictScalars_preservesInjectiveObjects :
    (SheafOfModules.forget.{v} R ⋙
      PresheafOfModules.restrictScalars α).PreservesInjectiveObjects :=
  preservesInjectiveObjects_of_isExact _ _ (PresheafOfModules.sheafificationAdjunction α)
    ⟨inferInstance, inferInstance⟩

/-- **An injective sheaf of modules is injective as a presheaf of modules.** This is the step of
[Stacks, Tag 01EP] which uses Stacks Tag 015Z. -/
@[stacks 03FB "an injective sheaf of modules, viewed as a presheaf of modules"]
instance SheafOfModules.injective_val (I : SheafOfModules.{v} R) [Injective I] :
    Injective I.val :=
  Functor.injective_obj
    (SheafOfModules.forget.{v} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) I

/-- **An injective sheaf of modules is injective as a presheaf of modules**, with injectivity of
the sheaf taken as an explicit argument. See `SheafOfModules.injective_val` for the variant
taking it as a typeclass argument. -/
theorem SheafOfModules.injective_val_of_injective {I : SheafOfModules.{v} R}
    (h : Injective I) : Injective I.val :=
  Functor.injective_obj_of_injective
    (SheafOfModules.forget.{v} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) h

/-- **The forgetful functor from sheaves of `R`-modules to presheaves of `R`-modules preserves
injective objects.** This is the functorial form of the statement that an injective sheaf of
modules is injective as a presheaf of modules. -/
@[stacks 03FB "the forgetful functor to presheaves of modules preserves injective
objects"]
instance SheafOfModules.forget_preservesInjectiveObjects :
    (SheafOfModules.forget.{v} R).PreservesInjectiveObjects where
  injective_obj h := SheafOfModules.injective_val_of_injective h

end
