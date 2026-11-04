module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.ChartLocal
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.Inverse
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleDepthFourVanishing
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowDegree

/-!
# The theorem of the cube: the hypotheses on a chart

For an invertible module `N` on `(A × A) × A`, `A` an abelian variety, and a finite affine open
cover `U` of `A`, the chart complex over every affine open `V` satisfies the standing hypotheses
`Stacks.Cube.ChartHyp` (`Stacks.Cube.chartHyp`); and `A`, `A × A` and `(A × A) × A` are integral
with only constant global functions when the ground field is algebraically closed.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety k A]

/-- An abelian variety is locally Noetherian. -/
instance isLocallyNoetherian_A : IsLocallyNoetherian A.left :=
  LocallyOfFiniteType.isLocallyNoetherian A.hom

/-- The product `A × A` is proper over `k`. -/
instance isProper_B : IsProper (A ⊗ A).hom := by
  change IsProper (pullback.fst A.hom A.hom ≫ A.hom); infer_instance

/-- The projection `(A × A) × A ⟶ A` to the third factor is proper. -/
instance isProper_r : IsProper (r A) := by
  change IsProper (pullback.snd (A ⊗ A).hom A.hom); infer_instance

/-- The product `A × A` is integral. -/
instance isIntegral_B : IsIntegral (B A) := by
  change IsIntegral (pullback A.hom A.hom); infer_instance

/-- The product `A × A` is locally Noetherian. -/
instance isLocallyNoetherian_B : IsLocallyNoetherian (B A) :=
  LocallyOfFiniteType.isLocallyNoetherian (A ⊗ A).hom

/-- The product `A × A` is flat over `k`. -/
instance flat_B : Flat (A ⊗ A).hom := by
  change Flat (pullback.fst A.hom A.hom ≫ A.hom); infer_instance

/-- The projection `(A × A) × A ⟶ A × A` is geometrically integral. -/
instance geometricallyIntegral_q : GeometricallyIntegral (pullback.fst (A ⊗ A).hom A.hom) :=
  inferInstance

/-- The triple product `(A × A) × A` is integral. -/
instance isIntegral_P : IsIntegral (P A) := by
  change IsIntegral (pullback (A ⊗ A).hom A.hom)
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst _ _)

/-- The triple product `(A × A) × A` is proper over `k`. -/
instance isProper_P : IsProper (Stacks.Groupoids.cubeObj A).hom := by
  change IsProper (pullback.fst (A ⊗ A).hom A.hom ≫ (A ⊗ A).hom); infer_instance

/-- The triple product `(A × A) × A` is locally Noetherian. -/
instance isLocallyNoetherian_P : IsLocallyNoetherian (P A) :=
  LocallyOfFiniteType.isLocallyNoetherian (Stacks.Groupoids.cubeObj A).hom

/-- **Over an algebraically closed field, the global functions of an integral proper scheme are
constants.** -/
theorem surjective_globalSections [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsIntegral X] [IsProper f] :
    Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  have : IsDomain Γ(X, ⊤) := (isField_of_universallyClosed k f).isDomain
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hfin : f.appTop.hom.Finite := finite_appTop_of_universallyClosed k f
  have : Module.Finite k Γ(X, ⊤) := by
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
    exact hfin.comp h2
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))).2

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → A.left.Opens)
  (hUaff : ∀ a, IsAffineOpen (U a)) (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)

omit [GrpObj A] [IsAbelianVariety k A] [Fintype ι] [DecidableEq ι] in
include hUaff in
/-- If every `U a` is affine, then every member `U a × U b` of the product cover of `A × A` is
affine. -/
theorem isAffineOpen_coverB (ab : ι × ι) : IsAffineOpen (coverB U ab) :=
  Stacks.AffineProduct.isAffineOpen_prodOpen (bx A) (bz A) (isPullback_B A) (hUaff ab.1)
    (hUaff ab.2)

omit [GrpObj A] [IsAbelianVariety k A] [Fintype ι] [DecidableEq ι] in
include hUaff in
/-- If every `U a` and `V` are affine, then every member `U a × U b × V` of the induced cover of
`P_V` is affine. -/
theorem isAffineOpen_chartCover {V : A.left.Opens} (hV : IsAffineOpen V) (ab : ι × ι) :
    IsAffineOpen (chartCover U V ab) := by
  rw [← (PV V).ι.isAffineOpen_iff_of_isOpenImmersion]
  have h := Stacks.AffineProduct.isAffineOpen_prodOpen (q A) (r A) (IsPullback.of_hasPullback
    (A ⊗ A).hom A.hom) (isAffineOpen_coverB U hUaff ab) hV
  convert h using 1
  rw [chartCover, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  ext x
  show x ∈ PV V ∧ x ∈ q A ⁻¹ᵁ coverB U ab ↔ x ∈ q A ⁻¹ᵁ coverB U ab ∧ x ∈ r A ⁻¹ᵁ V
  exact and_comm

omit [GrpObj A] [IsAbelianVariety k A] [Fintype ι] [DecidableEq ι] in
include hUcov in
/-- If the `U a` cover `A`, then the opens `U a × U b × V` cover `P_V`. -/
theorem chartCover_cov (V : A.left.Opens) :
    (⊤ : (PV V).toScheme.Opens) = ⨆ ab, chartCover U V ab := by
  refine (top_unique fun x _ => ?_).symm
  have h := hcovB U hUcov
  have hx : q A x.1 ∈ (⨆ ab, coverB U ab) := by rw [← h]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hx ⊢
  obtain ⟨ab, hab⟩ := hx
  exact ⟨ab, hab⟩

variable (N : (P A).Modules)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible (P A).presheaf (P A).ringCatSheaf.property N]

omit [GrpObj A] [IsAbelianVariety k A] in
/-- The restriction of an invertible module `N` on `(A × A) × A` to `P_V` is invertible. -/
theorem isInvertible_chartModule (V : A.left.Opens) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (PV V).toScheme.presheaf
      (PV V).toScheme.ringCatSheaf.property (chartModule N V) := by
  have h1 : Stacks.SheafOfModules.IsInvertible (P A).presheaf (P A).ringCatSheaf.2 N :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hN
  have h2 : Stacks.SheafOfModules.IsInvertible (PV V).toScheme.presheaf
      (PV V).toScheme.ringCatSheaf.2 ((Scheme.Modules.pullback (PV V).ι).obj N) :=
    @Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _ (PV V).ι N h1
  have h3 : Stacks.SheafOfModules.IsInvertible (PV V).toScheme.presheaf
      (PV V).toScheme.ringCatSheaf.2 (chartModule N V) :=
    @Stacks.SheafOfModules.isInvertible_of_iso _ _ _ _ _ _ _ _ _
      ((Scheme.Modules.restrictFunctorIsoPullback (PV V).ι).app N).symm h2
  exact h3.toAlgebraicGeometry

omit [Fintype ι] [DecidableEq ι] in
include hUaff hUcov in
/-- **The standing hypotheses hold on every affine chart.** -/
theorem chartHyp {V : A.left.Opens} (hV : IsAffineOpen V) : ChartHyp hV U N := by
  have := isInvertible_chartModule N V
  have : (chartModule N V).IsQuasicoherent :=
    @Stacks.Divisors.isQuasicoherent_of_isInvertible _ (chartModule N V)
      (isInvertible_chartModule N V)
  have : IsProper (chartMap hV) := by unfold chartMap; infer_instance
  have : Flat (chartMap hV) := by unfold chartMap; infer_instance
  have hfl : Scheme.Modules.IsFiniteLocallyFree (chartModule N V) :=
    Stacks.Algebraization.isFiniteLocallyFree_of_isInvertible_scheme _ _
  exact
  { sep := inferInstance
    proper := inferInstance
    qcoh := inferInstance
    coh := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible _ _
    flat := by
      have := (Scheme.Modules.isFiniteLocallyFree_iff (chartModule N V)).mp hfl
      exact AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree _ _
    aff := isAffineOpen_chartCover U hUaff hV
    cov := chartCover_cov U hUcov V }

end Stacks.Cube

end
