module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Composition
public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.Triangulated

/-!
# The cohomological dimension of a sum of ideals

Let `I` and `J` be finitely generated ideals of a commutative ring `A`. Since
`V(I + J) = V(I) ∩ V(J)`, local cohomology supported on `V(I + J)` is iterated local cohomology,
`RΓ_{V(I + J)} = RΓ_{V(J)} ∘ RΓ_{V(I)}` ([Stacks, Tag 0BJC],
`Dualizing.localCohomologyCompIso`). Now `RΓ_{V(I)}(A)` lives in cohomological degrees
`[0, cd(A, I)]`, and `RΓ_{V(J)}` raises the top degree by at most `cd(A, J)` because it does so on
every module placed in a single degree; so the composite lives in degrees `≤ cd(A, I) + cd(A, J)`,
which is the assertion.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_add_le` — **[Stacks, Tag 0ECP]**, the sum bound
  for the cohomological dimension of `I + J`.

## Implementation notes

The bound is stated as `cd(A, I + J) ≤ max (-1) (cd(A, I) + cd(A, J))`. The source writes
`cd(A, I + J) ≤ cd(A, I) + cd(A, J)`, but [Stacks, Tag 0DX8] defines `cd` as "the smallest integer
`d ≥ -1`" with the vanishing property, so a cohomological dimension is never below `-1`; for
`I = J = A`, where both zero loci are empty, the source's inequality reads `-1 ≤ -2` and is false.
Taking the maximum with `-1` is the strongest inequality that holds, and agrees with the source
wherever the source holds.

The passage from a bound on single modules to a bound on a bounded complex is
`Stacks.SmallDerivedCategory.isLE_obj_of_isGE`, the induction over the truncation triangles of the
canonical t-structure. It asks for its bound on `(singleFunctor n).obj M` for every `n`, which
is the degree-zero statement
`Stacks.LocalCohomology.isLE_localCohomologyDerived_of_isLocalCohomologyBound`
transported along the shift, the shift-compatibility of `RΓ_{V(J)}` coming from its being a right
adjoint of a triangulated functor.

## References

* [Stacks Project, Tag 0ECP](https://stacks.math.columbia.edu/tag/0ECP)
* [Stacks Project, Tag 0BJC](https://stacks.math.columbia.edu/tag/0BJC)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

attribute [local instance] derivedPowerTorsionProperty_isClosedUnderIsomorphisms
attribute [local instance] derivedPowerTorsionProperty_isTriangulated

/-- **[Stacks, Tag 0ECP].** For finitely generated ideals `I` and `J` of a commutative ring `A`,
the cohomological dimension of `I + J` is at most the sum of those of `I` and `J`, bounded below
by `-1` because a cohomological dimension always is. -/
@[stacks 0ECP]
theorem cohomologicalDimension_add_le (A : Type u) [CommRing A] (I J : Ideal A)
    (hI : I.FG) (hJ : J.FG) :
    cohomologicalDimension A (I + J) (Submodule.FG.sup hI hJ) ≤
      max (-1 : ℤ) (cohomologicalDimension A I hI + cohomologicalDimension A J hJ) := by
  set dI := cohomologicalDimension A I hI
  set dJ := cohomologicalDimension A J hJ
  let PI := Dualizing.derivedPowerTorsionProperty.{u, u} A I hI
  let PJ := Dualizing.derivedPowerTorsionProperty.{u, u} A J hJ
  let P := Dualizing.derivedPowerTorsionProperty.{u, u} A (I + J) (Submodule.FG.sup hI hJ)
  -- `RΓ_{V(J)}`, as a triangulated endofunctor of `D(A)` compatible with the shift.
  let adjJ := Dualizing.localCohomologyAdjunction.{u, u} A J hJ
  let GJ := (Dualizing.localCohomologyRightAdjoint.{u, u} A J hJ).1
  let : GJ.CommShift ℤ := adjJ.rightAdjointCommShift ℤ
  let : adjJ.CommShift ℤ := adjJ.commShift_of_leftAdjoint ℤ
  let : GJ.IsTriangulated := adjJ.isTriangulated_rightAdjoint
  let : GJ.Additive := adjJ.right_adjoint_additive
  let RJ := GJ ⋙ PJ.ι
  let : RJ.CommShift ℤ := Functor.CommShift.comp _ _
  let : RJ.IsTriangulated := inferInstance
  -- `RΓ_{V(J)}` raises the top cohomological degree by at most `dJ` on a module in any degree.
  have hSingle : ∀ M : ModuleCat.{u} A, (⊤ : ObjectProperty (ModuleCat.{u} A)) M → ∀ n : ℤ,
      (RJ.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M)).IsLE (n + dJ) := by
    intro M _ n
    have h₀ : (RJ.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).IsLE dJ :=
      isLE_localCohomologyDerived_of_isLocalCohomologyBound.{u, u} J hJ dJ
        (isLocalCohomologyBound_cohomologicalDimension A J hJ) M
    -- Stated through the composite functor, which is the shape `isLE_of_iso` searches for.
    have hshift : ((RJ ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-n)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).IsLE (n + dJ) :=
      DerivedCategory.TStructure.t.isLE_shift _ dJ (-n) (n + dJ) (by omega)
    exact DerivedCategory.TStructure.t.isLE_of_iso
      (((RJ.commShiftIso (-n)).app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).symm ≪≫
        RJ.mapIso
          (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-n) n 0
            (by omega)).app M)) (n + dJ)
  -- `RΓ_{V(I)}(A)` lives in cohomological degrees `[0, dI]`.
  let X₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let E := PI.ι.obj ((Dualizing.localCohomologyFunctor.{u, u} A I hI).obj X₀)
  have hEGE : E.IsGE 0 := (DerivedCategory.isGE_iff E 0).2 fun i hi =>
    isZero_localCohomologyModule_of_neg A I hI (ModuleCat.of A A) i hi
  have hELE : E.IsLE dI := (DerivedCategory.isLE_iff E dI).2 fun i hi =>
    (isLocalCohomologyBound_cohomologicalDimension A I hI).2 i hi
  -- Hence the composite lives in degrees `≤ dI + dJ`, and the composite is `RΓ_{V(I + J)}(A)`.
  -- `RΓ_{V(J)}(RΓ_{V(I)}(A))`, spelled as the source of `Dualizing.localCohomologyCompIso`.
  have hcomp : (P.ι.obj ((Dualizing.localCohomologyFunctor.{u, u} A I hI ⋙
      Dualizing.localCohomologyOnPowerTorsion A I J hI hJ).obj X₀)).IsLE (dI + dJ) :=
    Stacks.SmallDerivedCategory.isLE_obj_of_isGE ⊤ RJ dJ hSingle E (fun _ => trivial) 0 dI
  have hfinal : (P.ι.obj ((Dualizing.localCohomologyFunctor.{u, u} A (I + J)
      (Submodule.FG.sup hI hJ)).obj X₀)).IsLE (dI + dJ) :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (P.ι.mapIso ((Dualizing.localCohomologyCompIso.{u, u} A I J hI hJ).app X₀)) (dI + dJ)
  exact cohomologicalDimension_le A (I + J) _ _ ⟨le_max_left _ _, fun n hn =>
    (DerivedCategory.isLE_iff _ (dI + dJ)).1 hfinal n (lt_of_le_of_lt (le_max_right _ _) hn)⟩

end Stacks.LocalCohomology

end
