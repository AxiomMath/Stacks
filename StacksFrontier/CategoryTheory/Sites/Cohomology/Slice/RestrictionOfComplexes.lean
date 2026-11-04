module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Functor
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of complexes of modules to a slice of a ringed site

Let `(C, O)` be a ringed site and `U` an object of `C`. Restricting a sheaf of `O`-modules
along the forgetful functor `C/U ⥤ C` gives a sheaf of `O|_U`-modules; this is Mathlib's
`SheafOfModules.overFunctor`. The constructions of the Hom-complex, pseudo-coherence and
perfectness sections of this chapter are all phrased in terms of its degreewise extension to
cochain complexes, which this file records once as `restrictComplex`.

The only thing needing an argument is that `SheafOfModules.overFunctor` is additive, which is
required before a functor may be applied to a homological complex degreewise. It holds for
every slice of every site: restriction acts on a morphism of sheaves of modules by reindexing
its components along `C/U ⥤ C`, so addition of morphisms is preserved on the nose.

## Main definitions

* `AlgebraicGeometry.RingedSite.restrictComplex`: the degreewise restriction `K|_U` of a
  cochain complex `K` of `O`-modules to the site over `U`.

## Main results

* `SheafOfModules.overFunctor_additive`: restriction of sheaves of modules to a slice is an
  additive functor.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public section

open CategoryTheory

universe w v u m

namespace SheafOfModules

/-- Restriction of sheaves of modules to a slice of the site is additive: it reindexes the
components of a morphism along `Over.forget U`, so sums of morphisms are preserved. -/
instance overFunctor_additive {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (U : C) : (overFunctor.{m} R U).Additive where
  map_add := by intros; rfl

end SheafOfModules

namespace AlgebraicGeometry.RingedSite

/-- The restriction `K|_U` of a cochain complex of `O`-modules to the site over `U`, formed
degreewise. -/
noncomputable abbrev restrictComplex (X : RingedSite.{u, v, w})
    (K : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) :
    CochainComplex (SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ :=
  ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

end AlgebraicGeometry.RingedSite

end
