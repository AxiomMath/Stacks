module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.Homology.KFlat.Flat

/-! # An ordinary flat algebra in degree zero is K-flat

Let `R` be a commutative ring and let `B` be an `R`-algebra, not assumed commutative. Regard `B`
as a differential graded `R`-algebra concentrated in degree zero,
`DifferentialGradedAlgebra.degreeZero R B`. The complex of `R`-modules underlying its regular
module is then `B` placed in degree zero with zero differential, so it is bounded above and its
terms are `B` itself in degree zero and the zero module elsewhere. By [Stacks, Tag 064K] it is
therefore K-flat as soon as `B` is a flat `R`-module.

This is the bridge that lets [Stacks, Tag 09SA] — whose hypothesis is K-flatness of the
differential graded algebra `B` as a complex of `R`-modules — be applied under the hypothesis
"`B` is flat as an `R`-module" that [Stacks, Tag 09SC] part (3) actually offers.

## Main results

* `DifferentialGradedModule.kFlat_regularModule_degreeZero_of_flat`: if `B` is a flat `R`-module
  then `(regularModule (degreeZero R B)).toCochainComplex` is K-flat.

## Implementation notes

The homogeneous components of `degreeZero R B` are `⊤` in degree zero and `⊥` elsewhere, by
`DifferentialGradedAlgebra.degreeZeroGrading`. Flatness of the degree-zero term is flatness of
`B` transported along `Submodule.topEquiv`; the other terms are subsingletons, hence free, hence
flat, and being zero they also give the bound `IsStrictlyLE 0`.

Universes: the ring, the algebra and the modules live in a single universe `u`, as everywhere in
the differential graded chapter (Tag 09JJ); accordingly K-flatness is read at `.{u, u}`, the
same-universe specialisation of `CochainComplex.KFlat`.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K), a bounded above complex
  of flat modules is K-flat.
* [Stacks Project, Tag 09SA](https://stacks.math.columbia.edu/tag/09SA), the consumer of this
  bridge, and [Tag 09SC](https://stacks.math.columbia.edu/tag/09SC), whose flatness hypothesis it
  converts.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

variable (R : Type u) [CommRing R] (B : Type u) [Ring B] [Algebra R B]

/-- The complex of `R`-modules underlying the regular module of an algebra in degree zero is
concentrated in degree zero, so in particular it vanishes in positive degrees. -/
instance isStrictlyLE_regularModule_degreeZero :
    ((regularModule (degreeZero R B)).toCochainComplex).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  refine ModuleCat.isZero_iff_subsingleton.mpr ?_
  change Subsingleton (degreeZeroGrading R B i)
  rw [degreeZeroGrading_eq_bot R B (by omega)]
  infer_instance

/-- Every term of the complex of `R`-modules underlying the regular module of an algebra in
degree zero is flat, provided the algebra is flat over the base: the degree-zero term is the
algebra itself and the others are zero. -/
instance flat_regularModule_degreeZero_X [Module.Flat R B] (i : ℤ) :
    Module.Flat R (((regularModule (degreeZero R B)).toCochainComplex).X i) := by
  change Module.Flat R (degreeZeroGrading R B i)
  by_cases hi : i = 0
  · rw [hi, degreeZeroGrading_zero]
    exact Module.Flat.of_linearEquiv (Submodule.topEquiv : (⊤ : Submodule R B) ≃ₗ[R] B)
  · rw [degreeZeroGrading_eq_bot R B hi]
    infer_instance

/-- **The K-flatness bridge for an algebra in degree zero.** If `B` is flat as an `R`-module,
then the complex of `R`-modules underlying the regular module of the differential graded algebra
`degreeZero R B` is K-flat.

This is [Stacks, Tag 064K] applied to a complex concentrated in degree zero, and it is what
turns the hypothesis "`B` is flat as an `R`-module" of [Stacks, Tag 09SC] part (3) into the
hypothesis "`B` is K-flat as a complex of `R`-modules" of [Stacks, Tag 09SA]. -/
theorem kFlat_regularModule_degreeZero_of_flat [Module.Flat R B] :
    CochainComplex.KFlat.{u, u} (regularModule (degreeZero R B)).toCochainComplex :=
  CochainComplex.KFlat.kFlat_of_flat.{u, u} _ 0

end DifferentialGradedModule

end
