module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectComplexes

/-!
# Functoriality of strict perfectness

Let `R` and `S` be sheaves of rings on sites and let `F` be an exact functor from `R`-modules to
`S`-modules carrying the unit to the unit. Then `F` carries a direct summand of a finite free
`R`-module to a direct summand of a finite free `S`-module, and hence a strictly perfect complex
of `R`-modules to a strictly perfect complex of `S`-modules. Strict perfectness is also stable
under shifting a complex.

The case `F = SheafOfModules.overMap R f`, restriction of `R|_U`-modules along an arrow
`f : V ⟶ U` of the site, is already recorded as
`Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong`; this file supplies the general
statement behind it, and the shift lemma, which the perfect-complexes sections need for functors
other than restriction.

## Main results

* `SheafOfModules.isDirectSummandOfFiniteFree_map` and `SheafOfModules.isStrictlyPerfect_map`:
  transport along an exact unit-preserving functor.
* `SheafOfModules.isStrictlyPerfect_shift`: strict perfectness is stable under shifts.

## Implementation notes

A finite free module is a finite coproduct of copies of the unit, so only preservation of finite
colimits is used, through `SheafOfModules.mapFreeIso`. The statements are for arbitrary sheaves
of rings on sites, with the universe of the sections free, rather than for the structure sheaf of
a ringed site at `Type`-valued sections.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ w

namespace SheafOfModules

section Transport

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- An exact functor of sheaves of modules carrying the unit to the unit carries a direct summand
of a finite free module to a direct summand of a finite free module: a finite free module is a
finite coproduct of copies of the unit, which the functor preserves. -/
theorem isDirectSummandOfFiniteFree_map
    (F : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S) [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (unit R) ≅ unit S) (M : SheafOfModules.{w} R)
    (hM : IsDirectSummandOfFiniteFree R M) :
    IsDirectSummandOfFiniteFree S (F.obj M) := by
  obtain ⟨n, j, r, hjr⟩ := (isDirectSummandOfFiniteFree_iff_free R M).mp hM
  let eF := mapFreeIso F (ULift.{w} (Fin n)) e.symm
  refine (isDirectSummandOfFiniteFree_iff_free S _).mpr
    ⟨n, F.map j ≫ eF.inv, eF.hom ≫ F.map r, ?_⟩
  rw [Category.assoc, ← Category.assoc eF.inv, eF.inv_hom_id, Category.id_comp,
    ← Functor.map_comp, hjr, CategoryTheory.Functor.map_id]

/-- An exact functor of sheaves of modules carrying the unit to the unit carries strictly perfect
complexes to strictly perfect complexes. -/
theorem isStrictlyPerfect_map
    (F : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S) [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (unit R) ≅ unit S) {P : CochainComplex (SheafOfModules.{w} R) ℤ}
    (hP : IsStrictlyPerfect R P) :
    IsStrictlyPerfect S ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  bounded := hP.bounded.subset fun _ hi hz => hi (Functor.map_isZero F hz)
  termDirectSummand i := isDirectSummandOfFiniteFree_map F e (P.X i) (hP.termDirectSummand i)

end Transport

section Shift

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Strict perfectness is stable under shifting a complex: shifting only permutes the terms. -/
theorem isStrictlyPerfect_shift {P : CochainComplex (SheafOfModules.{w} R) ℤ}
    (hP : IsStrictlyPerfect R P) (n : ℤ) : IsStrictlyPerfect R (P⟦n⟧) where
  bounded := by
    simpa only [CochainComplex.shiftFunctor_obj_X', Set.preimage_ofPred_eq] using
      hP.bounded.preimage (add_left_injective n).injOn
  termDirectSummand i := by
    simpa only [CochainComplex.shiftFunctor_obj_X'] using hP.termDirectSummand (i + n)

end Shift

end SheafOfModules

end
