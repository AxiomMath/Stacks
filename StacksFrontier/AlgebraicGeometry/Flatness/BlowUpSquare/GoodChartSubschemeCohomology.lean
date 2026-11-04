module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineOpenPullbackModel
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.AffineTildeModel
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartDecalage
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodChartSubschemeSections
public import StacksFrontier.Homology.Eta.Perfect.GoodBaseChangeRingInputs

/-!
# The cohomology of `Li^*Lη_I M` on the closed subscheme of Tag 0GTZ

Let `(X, D, M)` be a good triple, `T ⊆ D` the closed subscheme of More on Flatness, Tag 0GTZ and
`i : T ⟶ X` its inclusion.  Over a good affine chart `(U, A, f, M^•)` the object `Lη_I M` is
represented on `U` by the décalage `η_f M^•` (Tag 0GTV), a bounded complex of finite projective
`A`-modules (Tag 0F7W).  Hence `Li^*Lη_I M` is represented on `T ∩ U = Spec C` by
`η_f M^• ⊗_A C`, where `C = (A ⧸ fA) ⧸ J(M^•, f)`, and its cohomology modules are finite
projective over `C` (Tag 0F81).  So the cohomology sheaves of `Li^*Lη_I M` are finite locally
free: this is part (2) of Tag 0GTZ.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.etaChartModelIso`: the restriction
  of `Lη_I M` to a chart is the complex of sheaves of `η_f M^•`.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.isFiniteLocallyFree_homology_goodChartSubscheme`:
  part (2) of Tag 0GTZ.

## References

* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0F81](https://stacks.math.columbia.edu/tag/0F81)
* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.ComplexAndDivisorSituation

open Stacks.Divisors.Eta (derivedEtaData)
open Stacks.Decalage.DirectSumIdeal

variable {X : Scheme.{u}} (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
  (M : DerivedCategory X.Modules) (hM : RingedSpace.IsPerfect (X := X.toRingedSpace) M)

/-- The triple `(X, D, M)` with `M` read in the standard model of `D(𝒪_X)`. -/
abbrev standardSituation : ComplexAndDivisorSituation.{u, u + 1} :=
  { X := X, D := D, isEffectiveCartierDivisor := hD, M := M, isPerfect := hM }

namespace AffineChart

include hD in
/-- **The décalage on a chart, as a model over the chart's ring.**  The restriction of `Lη_I M`
to an affine chart `(U, A, f, M^•)` is the complex of sheaves of `η_f M^•`, transported along
`U ≅ Spec A`. -/
def etaChartModelIso (C : AffineChart (standardSituation D hD M hM)) :
    (Scheme.Modules.restrictFunctor C.U.1.ι).mapDerivedCategory.obj
        ((derivedEtaData D).functor.obj M) ≅
      (tilde.functor Γ(X, C.U) ⋙ Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom
        ).mapDerivedCategory.obj (DerivedCategory.Q.obj C.etaComplex) :=
  ((RingedSpace.derivedRestrictModulesIsoRestrictFunctor X C.U.1).app _).symm ≪≫
    chartDerivedEtaIso D hD M hM C ≪≫
    DerivedCategory.Q.mapIso
      (Stacks.AffineTilde.transportTildeComplexIsoRestrict Γ(X, C.U) C.U.2.isoSpec.symm
        C.etaComplex) ≪≫
    ((tilde.functor Γ(X, C.U) ⋙ Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom
      ).mapDerivedCategoryFactors.app C.etaComplex).symm

end AffineChart

include hD in
/-- **Stacks Tag 0GTZ, part (2).**  For a good triple `(X, D, M)` and the closed subscheme
`i : T ⟶ D ⟶ X` of Tag 0GTZ, every cohomology sheaf of `Li^*Lη_I M` is finite locally free. -/
theorem isFiniteLocallyFree_homology_goodChartSubscheme
    (hS : (standardSituation D hD M hM).IsGoodTriple) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((DerivedCategory.homologyFunctor
          ((standardSituation D hD M hM).goodChartSubscheme hS).subscheme.Modules n).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (goodChartSubschemeIncl hS).toLRSHom.toShHom).obj
          ((derivedEtaData D).functor.obj M))) := by
  refine Scheme.Modules.isFiniteLocallyFree_of_forall_tilde_model _ fun t => ?_
  obtain ⟨C, hI, ht⟩ := (standardSituation D hD M hM).exists_good_chart_mem_preimage hS
    (((standardSituation D hD M hM).goodChartSubscheme hS).subschemeι t)
  let V := C.subschemeChartOpen hS
  let B := Γ(((standardSituation D hD M hM).goodChartSubscheme hS).subscheme, V.1)
  let φ : Γ(X, C.U) →+* B := C.subschemeSectionMap hS
  have hker : RingHom.ker φ = _ := C.ker_subschemeSectionMap hS hI
  have hfφ : ∀ a ∈ Ideal.span {C.f}, φ a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, hker, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact Submodule.zero_mem _
  let : Algebra Γ(X, C.U) B := φ.toAlgebra
  let : Algebra (Γ(X, C.U) ⧸ Ideal.span {C.f}) B := (Ideal.Quotient.lift _ φ hfφ).toAlgebra
  have : IsScalarTower Γ(X, C.U) (Γ(X, C.U) ⧸ Ideal.span {C.f}) B :=
    .of_algebraMap_eq fun _ => rfl
  have hB : ∀ i, Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
      (Stacks.Decalage.ObstructionIdeal.etaReductionMap C.complex C.f i) B := fun i => by
    refine (etaDirectSumIdeal_le_ker_iff C.complex C.f C.regular hI i B).mp fun y hy => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    show φ a = 0
    rw [← RingHom.mem_ker, hker, Ideal.mem_comap]
    exact le_iSup (etaDirectSumIdeal C.complex C.f) i hy
  obtain ⟨hfin, hproj⟩ :=
    Stacks.Decalage.ObstructionIdeal.finite_projective_homology_extendScalars_etaObject
      C.complex C.f C.regular hI hB n
  exact ⟨V.1, V.2, ht, _, hfin, hproj,
    ⟨restrictHomologyTildeModelIso V.2 _ _
      (restrictDerivedPullbackTildeModelIso (goodChartSubschemeIncl hS) C.U.2 V.2
        (C.subschemeChartOpen_le hS) _ C.etaComplex
        (Stacks.Eta.GoodBaseChange.kFlat_etaObject_toCochainComplex C.complex C.f C.regular hI)
        (C.etaChartModelIso D hD M hM)) n⟩⟩

end AlgebraicGeometry.ComplexAndDivisorSituation
