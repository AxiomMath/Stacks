module

public import StacksFrontier.AlgebraicGeometry.Curves.PointTwistDown
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Degree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree on the Picard group of a smooth curve is onto `ℤ`

Let `X` be a smooth proper curve over an algebraically closed field `k`.  A closed point `x` of
`X` is a `k`-rational point and an effective Cartier divisor, so `𝒪_X(x)` has degree one; hence
the degree homomorphism `Stacks.Picard.ofSchemeDegree : Pic(X) ⟶ ℤ` is surjective, and

`0 ⟶ Pic⁰(X) ⟶ Pic(X) --deg--> ℤ ⟶ 0`

is the short exact sequence with which the proof of [Stacks, Tag 0C1Z] begins.

## Main results

* `Stacks.Picard.exists_ofSchemeDegree_eq_one`: a Picard class of degree one.
* `Stacks.Picard.surjective_ofSchemeDegree`: the degree is onto `ℤ`.
* `Stacks.Picard.shortExact_ofSchemeDegree`: exactness of the sequence above.

## References

* [Stacks Project, Lemma 53.17.1 (Tag 0C1Z)](https://stacks.math.columbia.edu/tag/0C1Z)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Picard

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsProper f] [IsCurve k f] [Smooth f] (hdim : topologicalKrullDim X ≤ 1)

/-- **A Picard class of degree one**: the class of `𝒪_X(x)` for a closed point `x`. -/
theorem exists_ofSchemeDegree_eq_one : ∃ c : ofScheme X, ofSchemeDegree k f hdim c = 1 := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : Nonempty X := (inferInstance : IsIntegral X).nonempty
  obtain ⟨x, -, hxc⟩ := (isClosed_univ (X := X)).exists_closed_singleton Set.univ_nonempty
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hxc⟩ : Closeds X)) :=
    ((smoothAt_closedPoint_tfae_of_isCurve_of_perfectField k f hxc).out 5 4).mp
      (InfinitesimalLifting.smoothAt_of_smooth f x)
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hxc⟩ : Closeds X) with hDdef
  refine ⟨Stacks.SheafOfModules.picardClass X.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) (Stacks.Divisors.modulesInvertibleSheaf D)
    (Stacks.Divisors.stacksIsInvertible_invertibleSheaf D), ?_⟩
  refine (ofSchemeDegree_picardClass k f hdim _ _).trans ?_
  have h1 := invertibleCurveDegree_invertibleSheaf_eq_finrank_cohomologyOverField_zero k f hdim D
  have h2 := finrank_cohomologyOverField_pullback_eq_one k f hxc
    (Scheme.unitModule X)
    (AlgebraicGeometry.SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2)
  rw [finrank_cohomologyOverField_eq_of_iso k (D.subschemeι ≫ f)
    (Scheme.Modules.pullbackUnitIso D.subschemeι) 0] at h2
  refine Eq.trans ?_ (h1.trans ?_)
  · rfl
  · exact_mod_cast h2

/-- **The degree homomorphism of a smooth proper curve over an algebraically closed field is onto
`ℤ`.** -/
theorem surjective_ofSchemeDegree : Function.Surjective (ofSchemeDegree k f hdim) := by
  obtain ⟨c, hc⟩ := exists_ofSchemeDegree_eq_one k f hdim
  exact fun n => ⟨n • c, by rw [map_zsmul, hc, smul_eq_mul, mul_one]⟩

/-- **The short exact sequence `0 ⟶ Pic⁰(X) ⟶ Pic(X) ⟶ ℤ ⟶ 0`** of a smooth proper curve over an
algebraically closed field: the inclusion of `Pic⁰(X)` is injective, its image is the kernel of
the degree, and the degree is onto. -/
@[sga "4½ Arcata 6.2.3" "special case"]
theorem shortExact_ofSchemeDegree :
    Function.Injective (ofSchemeDegreeZero k f hdim).subtype ∧
      Function.Exact (ofSchemeDegreeZero k f hdim).subtype (ofSchemeDegree k f hdim) ∧
      Function.Surjective (ofSchemeDegree k f hdim) :=
  ⟨Subtype.val_injective, fun y => ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.2⟩,
    surjective_ofSchemeDegree k f hdim⟩

end Stacks.Picard

end
