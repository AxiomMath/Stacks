module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximations

/-!
# Restriction along an arrow of the site commutes with opcycles

Let `(C, O)` be a ringed site, let `g : V ⟶ U` be an arrow of `C` and let `P` be a complex of
`O|_U`-modules. Restriction along `g` is exact, so it commutes with the opcycles of `P`: the
degree-`k` opcycles of the restricted complex is the restriction of the degree-`k` opcycles
of `P`.

This is the comparison the proof of Stacks 08G7 needs in order to read the local direct-summand
conclusion of Stacks 08FD, which is about the restriction of `Coker(P^{a-1} ⟶ P^a)`, as a
statement about the degree-`a` opcycles of the restricted complex — which is where
`SheafOfModules.isStrictlyPerfect_truncGE` wants it.

## Main definitions

* `Stacks.SheafOfModules.restrictOpcyclesAlongIso`: the opcycles comparison for restriction
  along an arrow of the site.

## Implementation notes

This is the opcycles mirror of `Stacks.SheafOfModules.restrictCyclesAlongIso`, and is built the
same way: `Stacks.SheafOfModules.restrictComplexAlong R g P` and
`((SheafOfModules.overMap R g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P` are the same
term, but `((P.sc k).map (SheafOfModules.overMap R g)).opcycles` and
`(restrictComplexAlong R g P).opcycles k` are only definitionally equal, so Mathlib's
`CategoryTheory.ShortComplex.mapOpcyclesIso` is repackaged with its source spelled in the second
form.

Exactness of restriction along an arrow of the site is
`Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits` and
`overMap_preservesFiniteColimits`, put into instance scope here through
`Stacks.SheafOfModules.preservesFiniteLimitsOverMap` and its colimit counterpart, whose section
hypotheses this file repeats.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{0})
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{0}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{0}]

attribute [local instance] preservesFiniteColimitsOverMap preservesFiniteLimitsOverMap

/-- **An exact functor commutes with the opcycles of a complex**; here the comparison for
restriction along an arrow `g : V ⟶ U` of the site, with its source spelled as the opcycles of
the restricted complex rather than as the opcycles of a mapped short complex. -/
def restrictOpcyclesAlongIso {U V : C} (g : V ⟶ U)
    (P : CochainComplex (_root_.SheafOfModules.{0} (R.over U)) ℤ) (k : ℤ) :
    (restrictComplexAlong R g P).opcycles k ≅
      (SheafOfModules.overMap.{0} R g).obj (P.opcycles k) :=
  ShortComplex.mapOpcyclesIso (P.sc k) (SheafOfModules.overMap.{0} R g)

end Stacks.SheafOfModules

end
