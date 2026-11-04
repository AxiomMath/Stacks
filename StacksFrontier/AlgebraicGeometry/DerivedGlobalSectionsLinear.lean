module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.CategoryTheory.Functor.Derived.RightDerivedLinear

/-!
# `A`-linear derived global sections are `A`-linear

Let `A` be a commutative ring and `f : X ⟶ Spec A` a scheme over `A`. The ring map
`A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` makes the category of `𝒪_X`-modules `A`-linear
(`AlgebraicGeometry.Scheme.linearOfRingHom`), hence also its derived category. For this
structure the `A`-linear global sections functor and its unbounded right derived functor
`RΓ(X, -) : D(𝒪_X) ⥤ D(A)` are `A`-linear functors.

## Main definitions

* `AlgebraicGeometry.Scheme.linearOver` — the `A`-linear structure on `𝒪_X`-modules attached to
  the structure morphism `f : X ⟶ Spec A`.

## Main results

* `AlgebraicGeometry.globalSectionsOver_linearOver` — global sections are `A`-linear.
* `AlgebraicGeometry.derivedGlobalSectionsOver_linearOver` — derived global sections are
  `A`-linear.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The `A`-linear structure on the category of `𝒪_X`-modules of a scheme `f : X ⟶ Spec A` over
`A`: a scalar acts through `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`. -/
@[instance_reducible]
def Scheme.linearOver : Linear A X.Modules :=
  Scheme.linearOfRingHom.{u, u} X A ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom

/-- **Global sections over `A` form an `A`-linear functor** for the structure
`AlgebraicGeometry.Scheme.linearOver`. -/
theorem globalSectionsOver_linearOver :
    letI := Scheme.linearOver f
    Functor.Linear A (globalSectionsOver f) := by
  let := Scheme.linearOver f
  refine ⟨fun {M N} g a => ?_⟩
  ext x
  exact Scheme.smul_val_app_top X A ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a g x

/-- **Unbounded derived global sections over `A` form an `A`-linear functor** for the structure
`AlgebraicGeometry.Scheme.linearOver`: a right derived functor of a linear functor along a
linear localization is linear. -/
theorem derivedGlobalSectionsOver_linearOver :
    letI := Scheme.linearOver f
    Functor.Linear A (derivedGlobalSectionsOver f) := by
  let := Scheme.linearOver f
  have := globalSectionsOver_linearOver f
  exact Functor.IsRightDerivedFunctor.linear A (derivedGlobalSectionsOver f)
    (derivedGlobalSectionsOverUnit f) (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

end AlgebraicGeometry
