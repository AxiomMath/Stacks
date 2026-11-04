module

public import StacksFrontier.AlgebraicGeometry.GenericPointSheaf.Sections

/-!
# Sections of a product of sheaves of modules

A product of `𝒪_X`-modules is computed objectwise: its sections over an open set are the
product of the sections of the factors. This is the objectwise description of the right-hand
side of the generic-point decomposition of Stacks Tags 0EMF, 02OW and 0EMH.

## Main definitions

* `Stacks.AlgebraicGeometry.GenericPointSheaf.sectionsFunctor`: evaluation of an `𝒪_X`-module
  on an open set, as a functor to modules over the ring of sections there.
* `Stacks.AlgebraicGeometry.GenericPointSheaf.productSectionsIso`: the sections of a product
  are the product of the sections.

## Implementation notes

Mathlib proves that evaluation on `CategoryTheory.SheafOfModules` preserves limits, but
`AlgebraicGeometry.Scheme.Modules` is a `def` rather than an abbreviation, so none of those
instances are found by typeclass search at the scheme level: both
`PreservesLimitsOfShape (Discrete ι) (SheafOfModules.evaluation X.ringCatSheaf (op U))` and the
`PreservesLimit` it should yield fail to synthesize, while
`CategoryTheory.SheafOfModules.evaluationPreservesLimitsOfShape` supplied as an explicit term
typechecks against exactly that goal. `sectionsPreservesLimitsOfShape` below registers it, and
with it in scope the generic `CategoryTheory.Limits.PreservesProduct.iso` applies.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GenericPointSheaf

/-- Evaluation of an `𝒪_X`-module on an open set, as a functor into modules over the ring of
sections on that open set. -/
noncomputable abbrev sectionsFunctor (X : Scheme.{u}) (U : X.Opens) :
    X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (Opposite.op U)) :=
  SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)

variable {X : Scheme.{u}} {ι : Type u}

/-- Evaluation on an open set preserves products of `𝒪_X`-modules. Mathlib has this for
`CategoryTheory.SheafOfModules`; it is not found at the scheme level because
`AlgebraicGeometry.Scheme.Modules` is a `def`. -/
noncomputable instance sectionsPreservesLimitsOfShape (U : X.Opens) :
    PreservesLimitsOfShape (Discrete ι) (sectionsFunctor X U) :=
  SheafOfModules.evaluationPreservesLimitsOfShape (Discrete ι) X.ringCatSheaf (Opposite.op U)

/-- The sections of a product of `𝒪_X`-modules over an open set are the product of the
sections of the factors. -/
noncomputable def productSectionsIso (F : ι → X.Modules) (U : X.Opens) :
    (sectionsFunctor X U).obj (∏ᶜ F) ≅ ∏ᶜ fun i ↦ (sectionsFunctor X U).obj (F i) :=
  PreservesProduct.iso _ F

end Stacks.AlgebraicGeometry.GenericPointSheaf
