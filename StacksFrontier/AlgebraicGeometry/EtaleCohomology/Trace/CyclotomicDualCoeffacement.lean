module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.HomTwistEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricDerivedHomologyTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricGroupHomologyUniversal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationCohomologyNotProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.ElementwiseEffaceableFinite

/-!
# Coeffacing through the cyclotomic dual `M ↦ Hom(M, μ_n)`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure of
`k` separable over `k`, `η̄` a geometric point of `X_k̄`, `Λ` a finite ring with `n = #Λ`
invertible in `k`, and `D(M) = Hom(M, μ_n(k̄))` the cyclotomic dual
(`AlgebraicGeometry.cyclotomicDual`) from finite `Λ`-modules with a continuous action of
`π₁(X, η̄)` to finite `Λᵐᵒᵖ`-modules with a continuous action.

* `D` is an anti-equivalence (`AlgebraicGeometry.isEquivalence_cyclotomicDual`): it is the
  character dual of the Tate twist `M(-1) = Hom(μ_n, M)`
  (`AlgebraicGeometry.geometricTateTwistDualNatIso`), the character dual is an anti-equivalence,
  and the twist is an autoequivalence (`Stacks.GroupCohomology.homTwistEquivalence`), with inverse
  the twist by `Hom(μ_n, ℤ/n)`. This is the biduality `Hom(Hom(M, μ_n), μ_n) = M`.
* If `E = H^*(X_k̄, ℱ_-)` over `Λᵐᵒᵖ` is elementwise effaceable, then the groups `Eᵐ(P)` are finite
  for every `P`
  (`AlgebraicGeometry.finite_geometricRepresentationCohomology_of_elementwiseEffaceable`):
  `E` is then universal, hence equal to the cohomology of `π₁(X_k̄, η̄)`, whose groups are finite.
* Hence, for `m ≥ 1`, every `N` admits an epimorphism `π' : N' ⟶ N` with `Eᵐ(D(π')) = 0`
  (`AlgebraicGeometry.exists_epi_map_cyclotomicDual_eq_zero`): one monomorphism
  `D(N) ⟶ I` kills the finite group `Eᵐ(D(N))`, and it is `D` of an epimorphism.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.Frobenius

universe u

namespace CategoryTheory

/-- **Killing `F ∘ e` by the dual of an epimorphism.** If `e : Aᵒᵖ ≌ A'` is an anti-equivalence
and `ι : e(X) ⟶ I` is a monomorphism killed by a functor `F`, then `ι` is, up to isomorphism,
`e(π)` for an epimorphism `π : P ⟶ X`, and `F(e(π)) = 0`. -/
theorem exists_epi_map_eq_zero_of_equivalence {A A' C : Type*} [Category A] [Category A']
    [Category C] [Limits.HasZeroMorphisms C] (e : Aᵒᵖ ≌ A') (F : A' ⥤ C) (X : A) {I : A'}
    (ι : e.functor.obj (Opposite.op X) ⟶ I) (hι : Mono ι) (hE : F.map ι = 0) :
    ∃ (P : A) (π : P ⟶ X), Epi π ∧ F.map (e.functor.map π.op) = 0 := by
  let πop : Opposite.op X ⟶ e.inverse.obj I := e.unit.app (Opposite.op X) ≫ e.inverse.map ι
  have : Mono πop := mono_comp _ _
  refine ⟨(e.inverse.obj I).unop, πop.unop, unop_epi_of_mono πop, ?_⟩
  have hD : e.functor.map πop = ι ≫ e.counitInv.app I := by
    simp only [πop, Functor.map_comp, Equivalence.fun_inv_map]
    rw [← Category.assoc, Equivalence.functor_unit_comp, Category.id_comp]
  rw [Quiver.Hom.op_unop, hD, Functor.map_comp, hE, Limits.zero_comp]

end CategoryTheory

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (Λ : Type) [Ring Λ] [Finite Λ]

omit [Smooth f] [GeometricallyConnected f] in
include f in
/-- **A curve over a field has a compactification**: an open immersion into a proper (indeed
projective) curve over `k` (Tag 0BXV). -/
theorem nonempty_compactificationOf_of_isCurve : Nonempty (CompactificationOf (Over.mk f)) := by
  obtain ⟨Y, q, j, hj, hjq, hproj, -, -, -, -⟩ :=
    Stacks.CurveProjectiveCompletion.exists_projective_completion_of_dimension_le_one k f
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  exact ⟨⟨StructuredArrow.mk (Y := Over.mk q) (Over.homMk (U := Over.mk f) j hjq),
    ⟨inferInstanceAs (IsOpenImmersion j), isProper_of_isProjectiveMorphism q hproj⟩⟩⟩

omit [Smooth f] in
/-- **The cyclotomic dual `M ↦ Hom(M, μ_n(k̄))`, `n = #Λ`, is an anti-equivalence** from finite
`Λ`-modules with a continuous action of `π₁(X, η̄)` to finite `Λᵐᵒᵖ`-modules with a continuous
action: it is the character dual of the Tate twist `M(-1)`, and the Tate twist is an
autoequivalence (biduality `Hom(Hom(M, μ_n), μ_n) = M`). -/
theorem isEquivalence_cyclotomicDual (hΛ : IsUnit ((Nat.card Λ : ℕ) : k)) :
    letI := connectedSpace_of_isCurve B X f
    (cyclotomicDual B X f kbar y (Nat.card Λ) Λ).IsEquivalence := by
  let := connectedSpace_of_isCurve B X f
  have hA := natCard_cyclotomicIntContinuousModule B X f kbar y (Nat.card Λ)
    (by simpa using hΛ.map (algebraMap k kbar))
  have : (geometricTateTwist B X f kbar y Λ).IsEquivalence :=
    (homTwistEquivalence.{0, u + 1, u + 1} Λ
      (cyclotomicIntContinuousModule B X f kbar y (Nat.card Λ)) hA
      (fun M m ↦ natCard_nsmul_eq_zero Λ m)).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (geometricTateTwistDualNatIso B X f kbar y Λ hΛ)

omit [Algebra.IsSeparable k kbar] in
/-- **Finiteness of `H^q(X_k̄, ℱ_P)` for an elementwise effaceable `ρ ↦ H^*(X_k̄, ℱ_ρ)`**: the
δ-functor is then universal, so it is the cohomology of `π₁(X_k̄, η̄)` (both extend the invariants
in degree zero), whose groups with finite coefficients are finite. -/
theorem finite_geometricRepresentationCohomology_of_elementwiseEffaceable (Λ' : Type) [Ring Λ']
    [Finite Λ'] (hΛ' : IsUnit ((Nat.card Λ' : ℕ) : k))
    (hEff : letI := connectedSpace_of_isCurve B X f
      (geometricRepresentationCohomology.{u, 0} B X
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ' f kbar).ElementwiseEffaceable)
    (q : ℕ)
    (P : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ' (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    Finite (((geometricRepresentationCohomology.{u, 0} B X
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ' f kbar).functor q).obj P) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  let := QuasiCompact.compactSpace_of_compactSpace f
  let := quasiSeparatedSpace_of_quasiSeparated f
  have : IsAlgClosure k kbar := ⟨inferInstance, inferInstance⟩
  let : Fintype Λ' := Fintype.ofFinite Λ'
  have hK := contains_fieldBaseChange_of_isCurve B X f kbar
  obtain ⟨j⟩ := nonempty_compactificationOf_of_isCurve B X f
  have := hEff
  have := isUniversal_geometricGroupCohomology B X Λ' f kbar hK y
  have : (geometricRepresentationCohomology.{u, 0} B X
      (y.map (fieldBaseChangeObjProj B X f kbar hK).hom) Λ' f kbar).IsUniversal :=
    DeltaFunctor.isUniversal_of_elementwiseEffaceable _
  have hcomp : IsIso (geometricComparison B X Λ' f kbar hK y) :=
    inferInstanceAs (IsIso (DeltaFunctor.IsUniversal.isoOfIso
      (geometricComparisonZero B X Λ' f kbar hK y)).hom)
  have hn : IsUnit ((Fintype.card Λ' : ℕ) : kbar) := by
    simpa using hΛ'.map (algebraMap k kbar)
  have := finite_geometricGroupCohomology B X f kbar Λ' y j hn hcomp P q
  exact Finite.of_surjective _
    (bijective_app_of_iso Λ' (asIso (geometricComparison B X Λ' f kbar hK y)) q P).2

/-- **Coeffacement through the cyclotomic dual.** Let `E = H^*(X_k̄, ℱ_-)` on finite
`Λᵐᵒᵖ`-modules with continuous action of `π₁(X, η̄)` be elementwise effaceable, and `n = #Λ`
invertible in `k`. For `m ≥ 1`, every finite `Λ`-module `N` with a continuous action has an
epimorphism `π' : N' ⟶ N` with `Eᵐ(Hom(π', μ_n)) = 0`: one monomorphism `Hom(N, μ_n) ⟶ I` kills
the finite group `Eᵐ(Hom(N, μ_n))`, and since `M ↦ Hom(M, μ_n)` is an anti-equivalence it is
`Hom(π', μ_n)` for an epimorphism `π'`, up to isomorphism. -/
theorem exists_epi_map_cyclotomicDual_eq_zero (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hEff : letI := connectedSpace_of_isCurve B X f
      (geometricRepresentationCohomology.{u, 0} B X
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λᵐᵒᵖ f kbar).ElementwiseEffaceable)
    (m : ℕ) (hm : 1 ≤ m)
    (N : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    ∃ (N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) (π' : N' ⟶ N),
      Epi π' ∧ ((geometricRepresentationCohomology.{u, 0} B X
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λᵐᵒᵖ f kbar).functor m).map
        ((cyclotomicDual B X f kbar y (Nat.card Λ) Λ).map π'.op) = 0 := by
  let := connectedSpace_of_isCurve B X f
  obtain ⟨m, rfl⟩ : ∃ m' : ℕ, m = m' + 1 := ⟨m - 1, by omega⟩
  let E := geometricRepresentationCohomology.{u, 0} B X
    (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λᵐᵒᵖ f kbar
  have : E.ElementwiseEffaceable := hEff
  have := isEquivalence_cyclotomicDual B X f kbar y Λ hΛ
  let D := cyclotomicDual B X f kbar y (Nat.card Λ) Λ
  have hΛop : IsUnit ((Nat.card Λᵐᵒᵖ : ℕ) : k) := by
    rwa [Nat.card_congr MulOpposite.opEquiv.symm]
  have := finite_geometricRepresentationCohomology_of_elementwiseEffaceable B X f kbar y Λᵐᵒᵖ hΛop
    hEff (m + 1) (D.obj (Opposite.op N))
  obtain ⟨I, ι, hι, hE⟩ :=
    DeltaFunctor.ElementwiseEffaceable.exists_mono_map_eq_zero_of_finite (F := E)
      (D.obj (Opposite.op N)) m
  exact exists_epi_map_eq_zero_of_equivalence D.asEquivalence (E.functor (m + 1)) N ι hι hE

end AlgebraicGeometry

end
