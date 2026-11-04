module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCohomologyIso
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexShiftComparison
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaHomCohomology

/-!
# The two explicit cohomologies of `Hom^•(K, Y)`, bridged on cocycles

The replacement proof of [Stacks, Tag 09LK] computes the degree-`n` cohomology of `Hom^•(K, Y)`
twice, in two different presentations, and step 3 needs them identified.

* `DGCategory.RightModule.gradedCohomology (DGCategory.yonedaRightModule
  (dgCategory B) Y) K n` is a bare `Type` quotient of a submodule of the morphism module
  `(dgCategory B).Hom K Y n`, which is `CochainComplex.HomComplex.Cochain K Y n` itself.
* `DifferentialGradedModule.gradedCohomology (DGCategory.representableModule (dgCategory B) K Y) n`
  is a bundled `ModuleCat` quotient of a submodule of
  `(DGCategory.representableModule (dgCategory B) K Y).grading n`, which is a *range inside a
  direct sum over the degrees*, not a cochain group.

So the two are not the same type and not definitionally comparable: the passage between them is
`CochainComplex.homGradingEquiv`, the identification of the degree-`n` homogeneous part of the
direct sum with the cochains, and that is not a reflexivity. This file builds the passage on
cocycles.

## Why cocycles, and why it is cheap

Both sides are kernels of a differential, and the two differentials agree on the nose once the
grading is identified: the differential of the Yoneda right module is `(dgCategory B).d'` by
`DGCategory.yonedaRightModule_d`, and that is Mathlib's `δ` by
`CochainComplex.dgCategory_d'_eq`, while `CochainComplex.homGradingEquiv` carries the differential
of the differential graded module to `δ` by `CochainComplex.homGradingEquiv_delta`. So the
closedness conditions correspond term for term, and the two closedness proofs below are the ones
`CochainComplex.homCocyclesEquiv` already uses against Mathlib's
`CochainComplex.HomComplex.Cocycle` — the same degreewise content, read against the right module
instead.

## Main definitions

* `CochainComplex.homYonedaCocyclesEquiv`: **the bridge on cocycles.** The degree-`n` cocycles of
  the differential graded module `Hom^•(K, Y)` are the degree-`n` cocycles of the Yoneda right
  module of `Y` at `K`, by `CochainComplex.homGradingEquiv`.
* `CochainComplex.homYonedaCohomologyEquiv`: **the bridge on cohomology**, the identification step
  3 of [Stacks, Tag 09LK] needs between its two computations of `H^n(Hom^•(K, Y))`. It is
  `QuotientAddGroup.congr` of the bridge on cocycles.

## Main results

* `CochainComplex.homYonedaCocyclesEquiv_coe`: the underlying cochain is the one
  `CochainComplex.homGradingEquiv` gives, which is how every computation against the bridge should
  proceed; together with
  `CochainComplex.homEvaluationComparisonIso_hom_app_f_apply` — the same `homGradingEquiv`, read
  as the degreewise component of the comparison of complexes — this is what makes the bridge the
  one step 3's left-hand side actually travels along.
* `CochainComplex.homYonedaCocyclesEquiv_gradedToCocycles`: **the one computation** behind the
  correspondence of the boundaries — the bridge carries the one differential-into-the-cocycles to
  the other. This is where the agreement of the two differentials is used, and it is the only
  place it has to be used: both boundary submodules are `LinearMap.range` of that differential, so
  once it is intertwined the ranges are each other's image and nothing degreewise is left to
  check.
* `CochainComplex.map_homYonedaCocyclesEquiv_gradedBoundaries`: the coboundaries correspond, which
  is what lets the bridge descend to the quotients.
* `CochainComplex.homYonedaCohomologyEquiv_mk`: the bridge on cohomology at a class presented by a
  cocycle, which is the form every computation uses.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose step 3 needs the
  two presentations identified; [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE), the functor
  `Hom(K, -)`.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex

universe u

namespace CochainComplex

variable (B : Type u) [Category.{0} B] [Preadditive B] (K : CochainComplex B ℤ)

/-- **The two presentations of the degree-`n` cocycles of `Hom^•(K, Y)` agree.** A degree-`n`
homogeneous element of the differential graded module `Hom^•(K, Y)` — an element of a range
inside a direct sum over the degrees — is killed by that module's differential exactly when the
*cochain* it is, by `CochainComplex.homGradingEquiv`, is killed by the differential of the Yoneda
right module of `Y` at `K`.

The two differentials are the same map: `DGCategory.yonedaRightModule_d` makes the
right module's differential `(dgCategory B).d'`, `CochainComplex.dgCategory_d'_eq` makes that
Mathlib's `δ`, and `CochainComplex.homGradingEquiv_delta` says `homGradingEquiv` carries the
differential of the differential graded module to `δ`. -/
def homYonedaCocyclesEquiv (Y : CochainComplex B ℤ) (n : ℤ) :
    ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCocycles n) ≃+
      ↥(DGCategory.RightModule.gradedCocycles
        (DGCategory.yonedaRightModule (dgCategory B) Y) K n) where
  toFun z := ⟨homGradingEquiv B K Y n z.1, by
    rw [DGCategory.RightModule.mem_gradedCocycles,
      DGCategory.yonedaRightModule_d,
      dgCategory_d'_eq B (show n + 1 = n + 1 from rfl),
      ← homGradingEquiv_delta B K Y (show n + 1 = n + 1 from rfl) z.1
        ((DGCategory.representableModule (dgCategory B) K Y).gradedDifferential n z.1) rfl,
      LinearMap.mem_ker.mp z.2, map_zero]⟩
  invFun a := ⟨(homGradingEquiv B K Y n).symm a.1, by
    refine LinearMap.mem_ker.mpr ((homGradingEquiv B K Y (n + 1)).injective ?_)
    rw [homGradingEquiv_delta B K Y (show n + 1 = n + 1 from rfl)
        ((homGradingEquiv B K Y n).symm a.1)
        ((DGCategory.representableModule (dgCategory B) K Y).gradedDifferential n
          ((homGradingEquiv B K Y n).symm a.1)) rfl,
      map_zero, LinearEquiv.apply_symm_apply]
    have ha := a.2
    rw [DGCategory.RightModule.mem_gradedCocycles,
      DGCategory.yonedaRightModule_d,
      dgCategory_d'_eq B (show n + 1 = n + 1 from rfl)] at ha
    exact ha⟩
  left_inv z := Subtype.ext ((homGradingEquiv B K Y n).symm_apply_apply z.1)
  right_inv a := Subtype.ext ((homGradingEquiv B K Y n).apply_symm_apply a.1)
  map_add' z z' := Subtype.ext (map_add (homGradingEquiv B K Y n) z.1 z'.1)

/-- The cochain underlying the Yoneda-side cocycle attached to a cocycle of `Hom^•(K, Y)` is the
cochain `CochainComplex.homGradingEquiv` attaches to its underlying homogeneous element. This is
the characterisation every computation against the bridge should use. -/
@[simp] theorem homYonedaCocyclesEquiv_coe (Y : CochainComplex B ℤ) (n : ℤ)
    (z : ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCocycles n)) :
    ((homYonedaCocyclesEquiv B K Y n z).1 :
        (DGCategory.yonedaRightModule (dgCategory B) Y).obj K n) =
      homGradingEquiv B K Y n z.1 :=
  rfl

/-- **The bridge intertwines the two differentials-into-the-cocycles.** This is the single
computation behind the correspondence of the boundaries: both boundary submodules are the range of
the differential corestricted to the cocycles, and the bridge carries one differential to the
other. -/
theorem homYonedaCocyclesEquiv_gradedToCocycles (Y : CochainComplex B ℤ) {i n : ℤ}
    (h : i + 1 = n) (w : (DGCategory.representableModule (dgCategory B) K Y).grading i) :
    homYonedaCocyclesEquiv B K Y n
        ((DGCategory.representableModule (dgCategory B) K Y).gradedToCocycles h w) =
      DGCategory.RightModule.gradedToCocycles
        (DGCategory.yonedaRightModule (dgCategory B) Y) K h
        (homGradingEquiv B K Y i w) :=
  Subtype.ext ((homGradingEquiv_delta B K Y h w
      ((DGCategory.representableModule (dgCategory B) K Y).gradedToCocycles h w).1 rfl).trans
    (dgCategory_d'_eq B h (homGradingEquiv B K Y i w)).symm)

/-- **The coboundaries correspond.** The bridge carries the degree-`n` coboundaries of the
differential graded module `Hom^•(K, Y)` onto the degree-`n` coboundaries of the Yoneda right
module of `Y` at `K`.

Both are `LinearMap.range` of the differential corestricted to the cocycles, and
`CochainComplex.homYonedaCocyclesEquiv_gradedToCocycles` says the bridge carries the one
differential to the other, so the two ranges are each other's image. -/
theorem map_homYonedaCocyclesEquiv_gradedBoundaries (Y : CochainComplex B ℤ) (n : ℤ) :
    AddSubgroup.map (homYonedaCocyclesEquiv B K Y n).toAddMonoidHom
        ((DGCategory.representableModule (dgCategory B) K Y).gradedCoboundaries n).toAddSubgroup =
      (DGCategory.RightModule.gradedBoundaries
        (DGCategory.yonedaRightModule (dgCategory B) Y) K n).toAddSubgroup := by
  have hn : n - 1 + 1 = n := by omega
  refine AddSubgroup.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, rfl⟩ := hz
    exact ⟨homGradingEquiv B K Y (n - 1) w,
      (homYonedaCocyclesEquiv_gradedToCocycles B K Y hn w).symm⟩
  · rintro ⟨u, hu⟩
    refine ⟨(DGCategory.representableModule (dgCategory B) K Y).gradedToCocycles hn
      ((homGradingEquiv B K Y (n - 1)).symm u), ⟨_, rfl⟩, ?_⟩
    refine (homYonedaCocyclesEquiv_gradedToCocycles B K Y hn
      ((homGradingEquiv B K Y (n - 1)).symm u)).trans ?_
    rw [LinearEquiv.apply_symm_apply]
    exact hu

/-- **The bridge, on cohomology.** The explicit degree-`n` cohomology of the differential graded
module `Hom^•(K, Y)` — cocycles inside a range in a direct sum over the degrees, modulo
coboundaries — is the explicit degree-`n` cohomology of the Yoneda right module of `Y` at `K` —
cocycles inside the cochain group `Cochain K Y n`, modulo coboundaries.

This is the identification step 3 of [Stacks, Tag 09LK] needs between its two computations of
`H^n(Hom^•(K, Y))`. -/
def homYonedaCohomologyEquiv (Y : CochainComplex B ℤ) (n : ℤ) :
    ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCohomology n) ≃+
      DGCategory.RightModule.gradedCohomology
        (DGCategory.yonedaRightModule (dgCategory B) Y) K n :=
  QuotientAddGroup.congr
    ((DGCategory.representableModule (dgCategory B) K Y).gradedCoboundaries n).toAddSubgroup
    (DGCategory.RightModule.gradedBoundaries
      (DGCategory.yonedaRightModule (dgCategory B) Y) K n).toAddSubgroup
    (homYonedaCocyclesEquiv B K Y n)
    (map_homYonedaCocyclesEquiv_gradedBoundaries B K Y n)

/-- **The bridge on cohomology, at a class given by a cocycle.** This is the form every
computation uses: a class presented by a cocycle goes to the class of the bridged cocycle, whose
underlying cochain is `CochainComplex.homYonedaCocyclesEquiv_coe`. -/
@[simp] theorem homYonedaCohomologyEquiv_mk (Y : CochainComplex B ℤ) (n : ℤ)
    (z : ↥((DGCategory.representableModule (dgCategory B) K Y).gradedCocycles n)) :
    homYonedaCohomologyEquiv B K Y n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (homYonedaCocyclesEquiv B K Y n z) :=
  rfl

end CochainComplex

end
