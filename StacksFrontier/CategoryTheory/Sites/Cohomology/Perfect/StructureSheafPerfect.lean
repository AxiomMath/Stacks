module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The structure sheaf is a perfect object, and it is not a zero object

Let `(C, O)` be a ringed site. The structure sheaf placed in degree zero,
`AlgebraicGeometry.RingedSite.derivedStructureSheaf`, is a perfect object of `D(O)` in the sense
of Stacks 08G5: it is represented by the complex `O[0]`, which is strictly perfect (`O` is free
of rank one), and strict perfectness is inherited by every restriction to a slice, so the
identity covering of each object already carries the local models.

The second half of the file records that this object is *not* a zero object as soon as some
section ring of `O` is not the zero ring. That is what the first half is for: a statement
quantified over perfect objects says nothing unless some perfect object is not zero, and the
only unconditional witness of perfection in this library so far was the zero object
(`AlgebraicGeometry.RingedSite.isPerfect_of_isZero`).

**Nothing here is a clause of a Stacks tag and nothing here is tagged.** These are inhabitants
of the hypotheses of the tagged statements about perfect objects — in particular of the four
assertions of Stacks 08JJ and of its ringed-space form Stacks 08DQ — and not part of any
assertion.

## Main results

* `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_unit`: the structure sheaf, as a module over
  itself, is a direct summand of a finite free module — it is free of rank one.
* `AlgebraicGeometry.RingedSite.isStrictlyPerfect_structureSheafComplex`: the complex `O[0]` is
  strictly perfect.
* `AlgebraicGeometry.RingedSite.isPerfectComplex_structureSheafComplex` and
  `AlgebraicGeometry.RingedSite.isPerfect_derivedStructureSheaf`: `O[0]` is a perfect complex and
  the object it represents is a perfect object of `D(O)`.
* `AlgebraicGeometry.RingedSite.not_isZero_derivedStructureSheaf`: that object is not a zero
  object once `O` is not a zero module, because its degree-zero cohomology is `O`.

## Implementation notes

Strict perfectness of `O[0]` is the degreewise statement: the term in degree zero is `O`, which
is the free module on a one-element index type by
`Stacks.SheafOfModules.Invertible.freeUniqueIso`, and every other term is a zero object, which is
the free module on the empty index type.

Perfectness is then read off
`AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfectComplex_of_strictlyPerfectSieve`: the
sieve of arrows over whose source the restriction of `O[0]` is strictly perfect is the whole sieve,
since restriction to a slice is exact and carries the structure sheaf to the structure sheaf of the
slice.

The universes of the objects of the site, of its morphisms and of the sections of the structure
sheaf are independent, as they are for `AlgebraicGeometry.RingedSite.IsPerfectComplex`. The
module sections are the sections of the structure sheaf, so the module universe is the ring
universe and is not a further parameter. Keeping them independent is what lets the witness reach
the small étale ringed site of an algebraic space, which is a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`; see
`AlgebraicGeometry.Space.isPerfect_derivedStructureSheaf`.

The non-vanishing is proved through cohomology rather than through the derived category: the
degree-zero cohomology of `Q(O[0])` is the degree-zero cohomology of `O[0]`, which is `O` by
`HomologicalComplex.singleObjHomologySelfIso`, and the cohomology functor carries a zero object
to a zero object.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The structure sheaf is a direct summand of a finite free module over itself**: it *is* the
free module on a one-element index type, by `Stacks.SheafOfModules.Invertible.freeUniqueIso`, so
the two legs of the retraction may be taken to be the two directions of that isomorphism. -/
theorem isDirectSummandOfFiniteFree_unit :
    IsDirectSummandOfFiniteFree R (_root_.SheafOfModules.unit R) :=
  (isDirectSummandOfFiniteFree_iff_free R _).mpr
    ⟨1, (Invertible.freeUniqueIso (R := R) (ULift.{w} (Fin 1))).inv,
      (Invertible.freeUniqueIso (R := R) (ULift.{w} (Fin 1))).hom, Iso.inv_hom_id _⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The structure sheaf in degree zero is a strictly perfect complex.** Its term in degree zero
is the structure sheaf, free of rank one; every other term is a zero object, free of rank
zero. -/
theorem isStrictlyPerfect_structureSheafComplex :
    IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (structureSheafComplex X) where
  bounded := (Set.finite_singleton (0 : ℤ)).subset (fun i hi => by
    by_contra hne
    exact hi (HomologicalComplex.isZero_single_obj_X _ 0 _ i (by simpa using hne)))
  termDirectSummand i := by
    by_cases h : i = 0
    · subst h
      exact IsDirectSummandOfFiniteFree.of_iso _
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 _ 0 rfl)
        (Stacks.SheafOfModules.isDirectSummandOfFiniteFree_unit _)
    · exact (isDirectSummandOfFiniteFree_iff_free _ _).mpr
        ⟨0, 0, 0, (HomologicalComplex.isZero_single_obj_X _ 0 _ i h).eq_of_src _ _⟩

/-- **The restriction of the structure sheaf complex to a slice is strictly perfect**: restriction
is exact and carries the structure sheaf to the structure sheaf of the slice. -/
theorem isStrictlyPerfect_restrictComplex_structureSheafComplex (V : X.C) :
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
      (X.restrictComplex (structureSheafComplex X) V) :=
  have : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
  Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex _
    (Stacks.SheafOfModules.overFunctorUnitIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)
    (isStrictlyPerfect_structureSheafComplex X)

/-- **Stacks 08G5 is satisfied by the structure sheaf in degree zero.** The complex `O[0]` is a
perfect complex: its restriction to every object of the site is strictly perfect, so the maximal
sieve of each object carries the local models the definition asks for. -/
theorem isPerfectComplex_structureSheafComplex :
    X.IsPerfectComplex (structureSheafComplex X) :=
  InvertibleDerived.isPerfectComplex_of_strictlyPerfectSieve (structureSheafComplex X)
    (fun U => X.J.superset_covering
      (fun W _ _ => isStrictlyPerfect_restrictComplex_structureSheafComplex X W)
      (X.J.top_mem U))

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **The structure sheaf in degree zero is a perfect object of `D(O)`.** It is represented by the
perfect complex `O[0]`, on the nose. -/
theorem isPerfect_derivedStructureSheaf : X.IsPerfect (derivedStructureSheaf X) :=
  ⟨structureSheafComplex X, isPerfectComplex_structureSheafComplex X, ⟨Iso.refl _⟩⟩

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The structure sheaf in degree zero is not a zero object of `D(O)`**, as soon as the
structure sheaf is not a zero module. Its degree-zero cohomology is the structure sheaf, and a
cohomology functor carries a zero object to a zero object. -/
theorem not_isZero_derivedStructureSheaf
    (h : ¬ IsZero (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ¬ IsZero (derivedStructureSheaf X) := by
  intro hz
  refine h (IsZero.of_iso (Functor.map_isZero
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0) hz) ?_)
  exact ((DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).app
    (structureSheafComplex X) ≪≫
      HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 _).symm

end Derived

end AlgebraicGeometry.RingedSite

end
