module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation

/-!
# An invertible module in degree zero is a perfect object

Let `(C, O)` be a ringed site and let `L` be an invertible `O`-module, that is, one for which
tensoring by `L` is an autoequivalence of the category of `O`-modules (Stacks 01CS, 0409).  By
Stacks 0B8N (b) every object `U` of `C` has a covering `{V_i → U}` on whose members `L|_{V_i}` is
a direct summand of a finite free `O|_{V_i}`-module.  The complex `L[0]` is therefore strictly
perfect on each `V_i`, so it is a perfect complex in the sense of Stacks 08G5, and its image in
`D(O)` is a perfect object.

More generally the same holds for any `O`-module which is locally a direct summand of a finite
free module, and the result is stated that way first.

## Main results

* `AlgebraicGeometry.RingedSite.isStrictlyPerfect_single_general`: a
  direct summand of a finite free module, placed in one degree, is a strictly perfect complex.
* `AlgebraicGeometry.RingedSite.isPerfectComplex_single_of_locally`: a module which on a covering
  of every object is a direct summand of a finite free module is a perfect complex in degree
  zero.
* `AlgebraicGeometry.RingedSite.isPerfectComplex_single_of_isInvertible_general` and
  `AlgebraicGeometry.RingedSite.isPerfect_singleFunctor_of_isInvertible_general`: an invertible
  module placed in degree zero is a perfect complex, and a perfect object of `D(O)`.

## Implementation notes

`AlgebraicGeometry.RingedSite.isPerfectComplex_single_of_isInvertible` and
`AlgebraicGeometry.RingedSite.isPerfect_singleFunctor_of_isInvertible` state the invertible case
for a ringed site all of whose universes agree, `AlgebraicGeometry.RingedSite.{u, u, u}`.  The
small étale ringed site of an algebraic space is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`:
its objects live one universe above its morphisms and sections.  The statements here keep the
three universes independent, which is what lets them reach that site; they carry the suffix
`_general` for that reason, after `AlgebraicGeometry.RingedSite.isPerfect_of_locally_general`.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

section StrictlyPerfect

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A direct summand of a finite free module, placed in a single degree, is a strictly perfect
complex** (Stacks 08FL): its only possibly nonzero term is the module itself, and every other
term is zero, the free module on the empty index type. -/
theorem isStrictlyPerfect_single_general (j : ℤ)
    {M : SheafOfModules.{w} R} (hM : IsDirectSummandOfFiniteFree R M) :
    IsStrictlyPerfect R
      ((HomologicalComplex.single (SheafOfModules.{w} R) (ComplexShape.up ℤ) j).obj M) where
  bounded := (Set.finite_singleton j).subset (fun i hi => by
    by_contra hne
    exact hi (HomologicalComplex.isZero_single_obj_X _ j _ i (by simpa using hne)))
  termDirectSummand i := by
    by_cases h : i = j
    · subst h
      exact IsDirectSummandOfFiniteFree.of_iso _
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i M) hM
    · exact (isDirectSummandOfFiniteFree_iff_free _ _).mpr
        ⟨0, 0, 0, (HomologicalComplex.isZero_single_obj_X _ j _ i h).eq_of_src _ _⟩

end StrictlyPerfect

variable (X : RingedSite.{u, v, w})
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The restriction of a module placed in degree `j` to a slice is the restriction of the module,
placed in degree `j`. -/
def restrictSingleIso_general (j : ℤ)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (V : X.C) :
    X.restrictComplex
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj M) V ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj (M.over V) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)
    (ComplexShape.up ℤ) j).app M

/-- **A module which is locally a direct summand of a finite free module is a perfect complex
in degree zero** (Stacks 08G5).  If every object `U` has a covering `{V_i → U}` with each
`M|_{V_i}` a direct summand of a finite free `O|_{V_i}`-module, then `M[j]` is strictly perfect
over each `V_i`, which is what perfectness asks. -/
theorem isPerfectComplex_single_of_locally (j : ℤ)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : ∀ U : X.C, ∃ (I : Type (max u v)) (V : I → X.C) (f : ∀ i, V i ⟶ U),
      Sieve.generate (Presieve.ofArrows V f) ∈ X.J U ∧
        ∀ i, IsDirectSummandOfFiniteFree
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i)) (M.over (V i))) :
    X.IsPerfectComplex ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj M) := by
  refine InvertibleDerived.isPerfectComplex_of_strictlyPerfectSieve _ fun U => ?_
  obtain ⟨I, V, f, hcov, hsum⟩ := hM U
  refine X.J.superset_covering ?_ hcov
  rw [Sieve.generate_le_iff]
  rintro W g ⟨i⟩
  exact InvertibleDerived.isStrictlyPerfect_of_iso _ (restrictSingleIso_general X j M (V i)).symm
    (isStrictlyPerfect_single_general _ j (hsum i))

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **An invertible module, placed in degree zero, is a perfect complex** (Stacks 08G5).  By
Stacks 0B8N (b) it is locally a direct summand of a finite free module. -/
theorem isPerfectComplex_single_of_isInvertible_general
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L] (j : ℤ) :
    X.IsPerfectComplex ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj L) := by
  refine isPerfectComplex_single_of_locally X j L fun U => ?_
  obtain ⟨I, V, f, hcov, hret⟩ :=
    Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L U
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  obtain ⟨n, s, hs⟩ := hret i
  let r := Stacks.SheafOfModules.retractFreeOfIsSplitMono s
  exact (isDirectSummandOfFiniteFree_iff_free _ _).mpr ⟨n, r.i, r.r, r.retract⟩

section Derived

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **An invertible module, placed in degree `j`, is a perfect object of `D(O)`.**  It is
represented by the perfect complex `L[j]`, on the nose. -/
theorem isPerfect_singleFunctor_of_isInvertible_general
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L] (j : ℤ) :
    X.IsPerfect ((DerivedCategory.singleFunctor _ j).obj L) :=
  ⟨_, isPerfectComplex_single_of_isInvertible_general X L j,
    ⟨((DerivedCategory.singleFunctorIsoCompQ _ j).app L).symm⟩⟩

end Derived

end AlgebraicGeometry.RingedSite

end
