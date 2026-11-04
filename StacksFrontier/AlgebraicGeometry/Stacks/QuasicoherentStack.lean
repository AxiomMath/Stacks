module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The category of quasi-coherent modules over the big fppf site: `AlgebraicGeometry` spellings

The category of quasi-coherent modules over the big fppf site over a scheme `S`, its projection
to the big fppf slice and the description of its hom-sets are
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Basic`, in the namespace `Stacks.QCoh`;
Stacks 04U2 is registered there. This file carries the `AlgebraicGeometry.*` spellings of that
interface, which outside developments still refer to, as aliases of those declarations.

## Main definitions

* `AlgebraicGeometry.QCohObject`, `AlgebraicGeometry.QCohHom`,
  `AlgebraicGeometry.QCohCategoryData`: the object, hom and category-data types.
* `AlgebraicGeometry.qcohProjection`: the projection to the big fppf slice.
* `AlgebraicGeometry.qcohHomEquivPullbackHom`: the hom-sets as a disjoint union of pullback
  homs.

## Main results

* `AlgebraicGeometry.exists_qcohCategoryData`: the category exists with the displayed
  description of its hom-sets.

## References

* [Stacks Project, Tag 04U2](https://stacks.math.columbia.edu/tag/04U2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme over `S` in the chosen big fppf site, equipped with a quasi-coherent module.
This is `Stacks.QCoh.Object`. -/
abbrev QCohObject := Stacks.QCoh.Object B S hS

/-- The category of quasi-coherent pairs over the big fppf slice, together with its projection
and the identifications of its hom-sets. This is `Stacks.QCoh.CategoryData`. -/
abbrev QCohCategoryData := Stacks.QCoh.CategoryData B S hS

variable {B S hS}

/-- An `f`-map of quasi-coherent modules, together with its morphism of schemes over `S`.
This is `Stacks.QCoh.FMap`. -/
abbrev QCohHom (A C : QCohObject B S hS) : Type u := Stacks.QCoh.FMap A C

/-- **Stacks 04U2**, as `Stacks.QCoh.exists_categoryData`: the category of quasi-coherent pairs
over `S` exists together with its projection to the big fppf slice. -/
theorem exists_qcohCategoryData : Nonempty (QCohCategoryData B S hS) :=
  Stacks.QCoh.exists_categoryData

/-- The projection of the category of quasi-coherent pairs to the big fppf slice. This is
`Stacks.QCoh.projection`. -/
noncomputable abbrev qcohProjection : QCohObject B S hS ⥤ BigFppfOver B S hS :=
  Stacks.QCoh.projection

/-- **Stacks 04U2**, Equation (04U2), as `Stacks.QCoh.homEquivPullbackHom`: a hom-set is the
disjoint union, over the morphisms `f` of the base, of the morphisms from the pullback of the
target module along `f` to the source module. -/
noncomputable abbrev qcohHomEquivPullbackHom (A C : QCohObject B S hS) :
    (A ⟶ C) ≃
      Σ f : A.base ⟶ C.base,
        (Scheme.Modules.pullback (Stacks.QCoh.Object.schemeMap f)).obj C.module ⟶ A.module :=
  Stacks.QCoh.homEquivPullbackHom A C

end AlgebraicGeometry

end
