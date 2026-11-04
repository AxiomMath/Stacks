module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality

/-!
# Restriction of complexes along an arrow of the site, at a free sections universe

Let `(C, O)` be a site carrying a sheaf of rings `O` whose sections lie in an arbitrary
universe `w`, and let `g : V ⟶ U` be an arrow of `C`. This file records the degreewise
restriction `P|_V` of a complex of `O|_U`-modules along `g`, and the fact that it preserves
strict perfection (Stacks 08FL), with `w` a free universe variable.

## Main definitions

* `Stacks.SheafOfModules.restrictComplexAlongGeneral`: the degreewise restriction `P|_V` of a
  complex of `O|_U`-modules along an arrow `g : V ⟶ U` of the site.

## Main results

* `Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general`: restriction along an
  arrow of the site preserves strict perfection.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FM](https://stacks.math.columbia.edu/tag/08FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction of sheaves of modules along an arrow `g : V ⟶ U` of the site preserves finite
colimits. -/
local instance generalPreservesFiniteColimitsOverMap {U V : C} (g : V ⟶ U) :
    PreservesFiniteColimits (SheafOfModules.overMap.{w} R g) :=
  LocalCokernel.overMap_preservesFiniteColimits g

/-- The restriction `P|_V` of a cochain complex of `O|_U`-modules along an arrow `g : V ⟶ U`
of the site, formed degreewise, at a free universe of the sections. -/
abbrev restrictComplexAlongGeneral {U V : C} (g : V ⟶ U)
    (P : CochainComplex (SheafOfModules.{w} (R.over U)) ℤ) :
    CochainComplex (SheafOfModules.{w} (R.over V)) ℤ :=
  ((SheafOfModules.overMap.{w} R g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- **Restriction along an arrow of the site preserves strict perfection**, at a free universe
of the sections. -/
theorem isStrictlyPerfect_restrictComplexAlong_general {U V : C} (g : V ⟶ U)
    {P : CochainComplex (SheafOfModules.{w} (R.over U)) ℤ}
    (hP : IsStrictlyPerfect (R.over U) P) :
    IsStrictlyPerfect (R.over V) (restrictComplexAlongGeneral R g P) :=
  _root_.SheafOfModules.isStrictlyPerfect_map (SheafOfModules.overMap.{w} R g)
    (SheafOfModules.overMapUnitIso (R := R) g) hP

end Stacks.SheafOfModules

end
