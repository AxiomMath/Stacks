module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands

/-!
# The two spellings of the sheaf of rings of a scheme, and how to cross between them

`Stacks.StrictlyPerfect.structureSheafOfRings X`, for `X` a ringed space, and
`AlgebraicGeometry.Scheme.ringCatSheaf X`, for `X` a scheme, have the same body
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf`. Consequently
`Stacks.StrictlyPerfect.OXMod X.toRingedSpace` and
`AlgebraicGeometry.SheafOfModules X.ringCatSheaf` are the *same type*, carrying the *same*
category and abelian instances, and `structureSheafOfRings_toRingedSpace` below is `rfl`.

What is not the same is their behaviour under typeclass synthesis: `ringCatSheaf` is an `abbrev`
and so reducible, while `structureSheafOfRings` is a plain `def` and so semireducible, and
instance search unfolds only at reducible transparency. A hypothesis
`HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)` is therefore *not* found by
`inferInstance` when `HasDerivedCategory.{w} (OXMod X.toRingedSpace)` is wanted, and conversely.
This is the recurring wall between the pseudo-coherence material, which is stated over
`structureSheafOfRings`, and Mathlib's `tilde` API, which lands in `ringCatSheaf`.

A *lemma* cannot dissolve that wall, because instance synthesis cannot consult a lemma. What does
dissolve it, with no `set_option` and no change to either definition, is to move the instance
across as a **term**: a type ascription is checked at default transparency, where the two
spellings are interchangeable. `hasDerivedCategoryOxMod` and
`hasDerivedCategorySheafOfModules` below are that move, named so it can be used as
`letI := hasDerivedCategoryOxMod ‹_›` at the crossing point.

## Main results

* `Stacks.DerivedQCoh.structureSheafOfRings_toRingedSpace`: the two sheaves of rings are equal.
* `Stacks.DerivedQCoh.oxMod_eq_sheafOfModules`: the two categories of modules are the same type.
* `Stacks.DerivedQCoh.hasDerivedCategoryOxMod` and
  `Stacks.DerivedQCoh.hasDerivedCategorySheafOfModules`: a chosen derived category for one
  spelling is one for the other.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe w u

namespace Stacks.DerivedQCoh

variable (X : Scheme.{u})

/-- The sheaf of rings `Stacks.StrictlyPerfect.structureSheafOfRings` of the underlying ringed
space of a scheme is `AlgebraicGeometry.Scheme.ringCatSheaf`, on the nose. -/
theorem structureSheafOfRings_toRingedSpace :
    StrictlyPerfect.structureSheafOfRings X.toRingedSpace = X.ringCatSheaf := rfl

/-- `Stacks.StrictlyPerfect.OXMod` of the underlying ringed space of a scheme and
`AlgebraicGeometry.SheafOfModules` of its `ringCatSheaf` are the same type. -/
theorem oxMod_eq_sheafOfModules :
    StrictlyPerfect.OXMod.{u, u} X.toRingedSpace = SheafOfModules.{u} X.ringCatSheaf := rfl

/-- A chosen derived category for `SheafOfModules X.ringCatSheaf` is one for
`OXMod X.toRingedSpace`. Instance search does not make this step, because
`Stacks.StrictlyPerfect.structureSheafOfRings` is semireducible; the term-level ascription does,
because it is checked at default transparency. -/
@[instance_reducible]
def hasDerivedCategoryOxMod
    (h : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)) :
    HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) := h

/-- A chosen derived category for `OXMod X.toRingedSpace` is one for
`SheafOfModules X.ringCatSheaf`. -/
@[instance_reducible]
def hasDerivedCategorySheafOfModules
    (h : HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)) :
    HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf) := h

end Stacks.DerivedQCoh

end
