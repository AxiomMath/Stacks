module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCohomologyIso

/-!
# Tag 09LC's identification at a cocycle representative

`CochainComplex.homologyHomAddEquiv` is the bijection of [Stacks, Tag 09LC] that the
`unit_app_id` clause of
`CochainComplex.derivedHomLiftIdentificationOfNaturality` names: it carries a degree-`n`
cohomology class of `Hom^•(K, Y)` to a morphism `K ⟶ Y⟦n⟧` of the homotopy category. It is a
composite of four identifications, and
`CochainComplex.homologyHomAddEquivOfComplex_apply` already records its value as such; what is
missing for an elementwise computation is the last step, the passage from a cohomology *class* to
a cocycle *representative*.

This file takes that step, and only that step. The composite is not unfolded again: the named
formula `CochainComplex.homologyHomAddEquivOfComplex_apply` is used as it stands, read on the
homotopy category through `CochainComplex.homologyHomAddEquiv_quotient_obj`, and the one place
where a representative is needed — the quotient `CohomologyClass K Y n` of the degree-`n`
cocycles of the complex of cochains — is resolved by `CochainComplex.homCohomologyClassEquiv_mk`
and Mathlib's `CochainComplex.HomComplex.CohomologyClass.toHom_mk`.

The outcome is a closed formula: Tag 09LC's morphism attached to a class represented by a
degree-`n` cocycle `z` of the differential graded module `Hom^•(K, Y)` is the homotopy class of
the cochain map `K ⟶ Y⟦n⟧` that `z` is, by Mathlib's
`CochainComplex.HomComplex.Cocycle.equivHomShift`, followed by the comparison of the two readings
of the shift.

## Main results

* `CochainComplex.homologyHomAddEquiv_quotient_obj_apply`: the value of Tag 09LC's bijection at
  the homotopy class of a complex, which is `CochainComplex.homologyHomAddEquivOfComplex_apply`
  read there.
* `CochainComplex.exists_gradedCocycles_repr`: every class has a cocycle representative, so the
  hypothesis of the next result is never a restriction.
* `CochainComplex.homologyHomAddEquiv_quotient_obj_apply_mk`: **Tag 09LC's identification at a
  cocycle representative.**

## Implementation notes

The representative is taken on the differential-graded-module side, as an element of
`(DGCategory.representableModule (dgCategory B) K Y).gradedCocycles n`, and not on the
`Cochain K Y n` side: that is the side on which `CochainComplex.homGradingEquiv` — hence
`CochainComplex.homEvaluationComparisonIso`, hence the comparison `ν` of
[Stacks, Tag 09LK] — is stated, so a representative chosen there is simultaneously a
representative for the other half of the computation. Choosing it on the `Cochain` side would
force the comparison to be transported back.

The hypothesis is the *forward* equation
`(homologyGradedCohomologyIso B K n).hom.app Y x = Submodule.Quotient.mk z`, so no inverse and no
transport appears in the statement.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the identification of a
  degree-`n` cohomology class of a Hom complex with a morphism into an `n`-fold shift;
  [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose step 3 consumes it.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex

universe w u

namespace CochainComplex

variable (B : Type u) [Category.{0} B] [Preadditive B] (K : CochainComplex B ℤ)
  [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **Tag 09LC's bijection at the homotopy class of a complex.** The value of
`CochainComplex.homologyHomAddEquiv` there is the value of
`CochainComplex.homologyHomAddEquivOfComplex`, which
`CochainComplex.homologyHomAddEquivOfComplex_apply` computes: the class is carried to the
explicit cohomology of `Hom^•(K, Y)`, then to a cohomology class of the complex of cochains,
then to a morphism of the homotopy category, and finally composed with the comparison of the two
readings of the shift. -/
theorem homologyHomAddEquiv_quotient_obj_apply (n : ℤ) (Y : CochainComplex B ℤ)
    (x : ↥((homToDerivedCategoryForget B K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Y))) :
    homologyHomAddEquiv B K n ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Y) x =
      CohomologyClass.homAddEquiv (homCohomologyClassEquiv B K Y n
          ((homologyGradedCohomologyIso B K n).hom.app Y x)) ≫
        (((HomotopyCategory.quotient B (ComplexShape.up ℤ)).commShiftIso (A := ℤ) n).app Y).hom :=
  homologyHomAddEquivOfComplex_apply B K n Y x

/-- **Every class has a cocycle representative.** The explicit cohomology of the differential
graded module `Hom^•(K, Y)` is a quotient of its degree-`n` cocycles, so the hypothesis of
`CochainComplex.homologyHomAddEquiv_quotient_obj_apply_mk` can always be met. -/
theorem exists_gradedCocycles_repr (n : ℤ) (Y : CochainComplex B ℤ)
    (x : ↥((homToDerivedCategoryForget B K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Y))) :
    ∃ z : ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCocycles n),
      (homologyGradedCohomologyIso B K n).hom.app Y x = Submodule.Quotient.mk z := by
  obtain ⟨z, hz⟩ := Quotient.exists_rep ((homologyGradedCohomologyIso B K n).hom.app Y x)
  exact ⟨z, hz.symm⟩

/-- **Tag 09LC's identification at a cocycle representative.** If the degree-`n` cohomology class
`x` of `Hom^•(K, Y)` is represented by the degree-`n` cocycle `z` of the differential graded
module `Hom^•(K, Y)`, then the morphism `K ⟶ Y⟦n⟧` of the homotopy category that `x` is, by
[Tag 09LC], is the homotopy class of the cochain map that `z` is, followed by the comparison of
the two readings of the shift.

The cochain `DGCategory.representableModule`-cocycle `z` is read as a degree-`n` cocycle of the
complex of cochains by `CochainComplex.homCocyclesEquiv`, which is
`CochainComplex.homGradingEquiv` restricted to cocycles — the same degreewise identification that
`CochainComplex.homEvaluationComparisonIso` is built from. So this is the formula against which
the other half of the `unit_app_id` computation can be matched. -/
theorem homologyHomAddEquiv_quotient_obj_apply_mk (n : ℤ) (Y : CochainComplex B ℤ)
    (x : ↥((homToDerivedCategoryForget B K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Y)))
    (z : ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCocycles n))
    (hz : (homologyGradedCohomologyIso B K n).hom.app Y x = Submodule.Quotient.mk z) :
    homologyHomAddEquiv B K n ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Y) x =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          (Cocycle.equivHomShift.symm (homCocyclesEquiv B K Y n z)) ≫
        (((HomotopyCategory.quotient B (ComplexShape.up ℤ)).commShiftIso
          (A := ℤ) n).app Y).hom := by
  rw [homologyHomAddEquiv_quotient_obj_apply, hz]
  rfl

end CochainComplex

end
