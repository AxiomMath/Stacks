module

import StacksFrontier.AlgebraicGeometry.BirationalCurveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicLFunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalCharSeriesRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupportComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Weights in dimension zero

Let `X` be a scheme finite étale over the finite field `k` and `F` an ℓ-adic sheaf on `X`. This
file proves the trace formula of [Tag 03V2](https://stacks.math.columbia.edu/tag/03V2) for `X`, the
vanishing of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` for `i ≠ 0`, the Euler product

`det(1 - π_X^* T | H⁰_c(X_k̄, F)) = ∏_{x ∈ |X|} det(1 - π_x T ^ (deg x) | F_x̄)`,

which is the identity `L(X, F) = ∏ᵢ det(1 - π_X^* T | Hⁱ_c)^{(-1)^{i+1}}` of
[Tag 03V0](https://stacks.math.columbia.edu/tag/03V0) in dimension zero, and the weight bound of
Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3) for `X`.

## Main results

* `topologicalKrullDim_le_zero_of_isFinite`: a scheme finite over a field has dimension zero.
* `LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_etale`:
  the complexes `RΓ_c(X_k̄, F'ₙ)` are perfect.
* `LAdicSheaf.traceAtLevel_geometricPerfectTower_of_etale`: the trace formula at every level.
* `LAdicSheaf.traceFormula_of_etale`: the trace formula of Tag 03V2.
* `LAdicSheaf.charPowerSeries_rationalGeometricCompactlySupportedFrobenius_eq_prod`:
  the Euler product.
* `LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_etale`:
  pointwise `ι`-mixedness of weights `≤ w` gives weights `≤ w + i` on `Hⁱ_c`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem CategoryTheory.FilteredDerived Stacks.Trace

universe u

namespace Stacks.EtaleCohomology

section Geometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsFinite f]

include f

/-- **The ring of global sections of a scheme finite over a field is Artinian**, and the scheme
is affine. -/
theorem isArtinianRing_of_isFinite : IsAffine X ∧ IsArtinianRing Γ(X, ⊤) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  refine ⟨inferInstance, ?_⟩
  let φ : k →+* Γ(X, ⊤) := (f.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hφ : φ.Finite := RingHom.Finite.comp (f.finite_app ⊤ (isAffineOpen_top _))
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  let := φ.toAlgebra
  have : Module.Finite k Γ(X, ⊤) := hφ
  exact IsArtinianRing.of_finite k Γ(X, ⊤)

/-- A scheme finite over a field is a finite discrete space. -/
theorem finite_discreteTopology_of_isFinite : Finite X ∧ DiscreteTopology X := by
  have := (isArtinianRing_of_isFinite f).1
  have : IsArtinianRing Γ(X, ⊤) := (isArtinianRing_of_isFinite f).2
  let e : X ≃ₜ PrimeSpectrum Γ(X, ⊤) := Scheme.homeoOfIso X.isoSpec
  exact ⟨Finite.of_injective e e.injective, e.isEmbedding.discreteTopology⟩

/-- **A scheme finite over a field has dimension zero.** -/
theorem topologicalKrullDim_le_zero_of_isFinite : topologicalKrullDim X ≤ 0 := by
  have := (finite_discreteTopology_of_isFinite f).2
  exact Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space

end Geometry

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

local notation "model" F => LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)

/-- **The stalks of the levels of the torsion-free model are perfect** at every geometric
point. -/
theorem LAdicSheaf.isPerfect_stalk_levelComplex_torsionFreeModel (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (n : ℕ) (s : GeometricPoint X.1) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).mapHomologicalComplex
          (ComplexShape.up ℤ) |>.obj (LAdicSheaf.levelComplex B X ℓ (model F) n).obj)) := by
  let b := LAdicSheaf.flatLevelBasis (model F) s
    (fun m => LAdicSheaf.isPowExact_finiteLevelStalk _ _ m
      (LAdicSheaf.powExact_torsionFreeModel_level F le_rfl m)) n
  let e := (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) s).app
    ((model F).level n)
  let b' := b.map e.toLinearEquiv.symm
  have : Module.Free (ZMod (ℓ ^ (n + 1))) ((Scheme.pointSmallEtale s.hom).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) |>.obj
        (LAdicSheaf.etaleLevel B X ℓ (model F) n)) := Module.Free.of_basis b'
  have : Module.Finite (ZMod (ℓ ^ (n + 1))) ((Scheme.pointSmallEtale s.hom).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) |>.obj
        (LAdicSheaf.etaleLevel B X ℓ (model F) n)) := Module.Finite.of_basis b'
  exact StacksDraft.Perfect.isPerfect_of_iso.{0, u + 1, u + 2} (DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex
      ((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
      (ComplexShape.up ℤ) 0).app (LAdicSheaf.etaleLevel B X ℓ (model F) n)))
    (isPerfect_Q_single_of_projective _)

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **Perfectness of `RΓ_c(X_k̄, F'ₙ)` in dimension zero.**  For `X` finite étale over `k`, the
complexes `RΓ_c(X_k̄, F'ₙ)` of the levels of the torsion-free model of an ℓ-adic sheaf are
perfect. -/
theorem LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_etale [Finite k]
    [Etale f] [IsFinite f] (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n))) := by
  have := Fintype.ofFinite k
  have : Etale (Over.mk f).hom := ‹Etale f›
  have : IsFinite (Over.mk f).hom := ‹IsFinite f›
  exact StacksDraft.Perfect.isPerfect_of_iso.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.mapIso
    (compactSupportFrobeniusCohomologyIsoOfIsProper _ f j kbar _))
    (isPerfect_frobeniusRestriction_of_etale _ (Over.mk f) kbar _
      (LAdicSheaf.isPerfect_stalk_levelComplex_torsionFreeModel B X ℓ F n))

omit [QuasiCompact f] [IsSeparated f] in
open scoped Classical in
/-- **The trace formula of [Stacks, Tag 03V3] at every level, in dimension zero.**  For `X` finite
étale over `k`, the trace of `π_X^*` on `RΓ_c(X_k̄, F'ₙ)` is the sum over the rational points of
the traces of the geometric Frobenius on the stalks of `F'ₙ`. -/
theorem LAdicSheaf.traceAtLevel_geometricPerfectTower_of_etale [Etale f] [IsFinite f]
    (F : LAdicSheaf.{u, u + 1} B X ℓ) [Fintype (rationalPoints f)] (n : ℕ) :
    traceAtLevel (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard (model F)
        (LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F le_rfl)
        (LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_etale B X ℓ f j
          kbar F)) n =
      ∑ y : rationalPoints f, commutativeAdditiveCommutatorQuotientEval (ZMod (ℓ ^ (n + 1)))
        (perfectDerivedTrace (ZMod (ℓ ^ (n + 1))) ⟨_,
          LAdicSheaf.isPerfect_rationalPointStalkComplex_torsionFreeModel B X ℓ f kbar F n y⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} (ZMod (ℓ ^ (n + 1))) kbar p q
            hcard y.1 (LAdicSheaf.levelComplex B X ℓ (model F) n)))) := by
  have : Etale (Over.mk f).hom := ‹Etale f›
  have : IsFinite (Over.mk f).hom := ‹IsFinite f›
  have hstalk := LAdicSheaf.isPerfect_stalk_levelComplex_torsionFreeModel B X ℓ F n
  have hperf := isPerfect_frobeniusRestriction_of_etale _ (Over.mk f) kbar
    (LAdicSheaf.levelComplex B X ℓ (model F) n) hstalk
  have : Fintype (rationalPoints (Over.mk f).hom) := ‹Fintype (rationalPoints f)›
  have key := perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_sum_of_etale'
    (ZMod (ℓ ^ (n + 1))) (Over.mk f) kbar p q hcard _ hperf hstalk
  rw [traceAtLevel, ← map_sum]
  congr 1
  refine (perfectDerivedTrace_congr _ _ ⟨_, hperf⟩
    (DerivedCategory.Plus.ι.mapIso (compactSupportFrobeniusCohomologyIsoOfIsProper _ f j kbar _))
    _ _ ?_).trans (key.trans ?_)
  · exact (DerivedCategory.Plus.ι.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Plus.ι.map
        (compactSupportFrobeniusCohomologyIsoOfIsProper_hom_frobenius
          (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard _)).trans (DerivedCategory.Plus.ι.map_comp _ _))
  · congr 1
    ext x
    simp

omit [IsSeparated f] in
/-- **The trace formula of [Stacks, Tag 03V2] in dimension zero.**  For `X` finite étale over `k`
and an ℓ-adic sheaf `F` on `X`,
`∑_{x ∈ X(k)} Tr(π_x | F_x̄) = ∑ᵢ (-1)ⁱ Tr(π_X^* | Hⁱ_c(X_k̄, F))`. -/
theorem LAdicSheaf.traceFormula_of_etale [Etale f] [IsFinite f] (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 = 1),
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2)) =
      ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom := by
  have := finite_rationalPoints f
  let := Fintype.ofFinite (rationalPoints f)
  exact (LAdicSheaf.alternating_trace_eq_sum_rationalStalkFrobenius_of_levelTraceFormula B X ℓ f j
    kbar p q hcard F _ (LAdicSheaf.traceAtLevel_geometricPerfectTower_of_etale B X ℓ f j kbar p q
      hcard F)).symm

omit [Fintype k] [CharP kbar p] [IsSeparated f] in
/-- **`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` vanishes for `i ≠ 0` in dimension zero.** -/
theorem LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_of_isFinite [Finite k]
    [IsFinite f] (F : LAdicSheaf.{u, u + 1} B X ℓ) {i : ℤ} (hi : i ≠ 0) :
    Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
  have := Fintype.ofFinite k
  rcases lt_or_gt_of_ne hi with h | h
  · exact ModuleCat.subsingleton_of_isZero
      (LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_neg B X ℓ f j kbar F i h)
  · exact ModuleCat.subsingleton_of_isZero
      (LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_two_mul_lt B X ℓ f j kbar
        F 0 (by simpa using topologicalKrullDim_le_zero_of_isFinite f) i (by lia))

/-- An endomorphism of the zero space has no characteristic roots. -/
theorem isCharpolyNormMixedOfWeightLE_of_subsingleton {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Subsingleton V] {q : ℕ} {ι : K →+* ℂ} {i : ℤ}
    (g : Module.End K V) : IsCharpolyNormMixedOfWeightLE q ι i g := fun z hz => by
  have h1 : g.charpoly = 1 := Polynomial.eq_one_of_monic_natDegree_zero g.charpoly_monic
    (by rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton])
  rw [h1, Polynomial.map_one, Polynomial.IsRoot, Polynomial.eval_one] at hz
  exact absurd hz one_ne_zero

section Weights

/-- The local factor of an endomorphism of a finite-dimensional vector space at a degree `d ≠ 0`
is inverted by `PowerSeries.invOfUnit`. -/
private theorem charPowerSeries_mul_invOfUnit {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (g : Module.End K V) {d : ℕ} (hd : d ≠ 0) :
    charPowerSeries g d * PowerSeries.invOfUnit (charPowerSeries g d) 1 = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simpa using constantCoeff_charPowerSeries g hd)

variable [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

omit [CharP kbar p] [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [IsSeparated f] in
/-- **The Euler product in dimension zero.**  For `X` finite étale over `k` and an ℓ-adic sheaf
`F`, `det(1 - π_X^* T | H⁰_c(X_k̄, F)) = ∏_{x ∈ |X|} det(1 - π_x T ^ (deg x) | F_x̄)`. -/
theorem LAdicSheaf.charPowerSeries_rationalGeometricCompactlySupportedFrobenius_eq_prod
    [Etale f] [IsFinite f] (F : LAdicSheaf.{u, u + 1} B X ℓ) [Fintype (closedPoints X.1)] :
    charPowerSeries
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
          0).hom 1 =
      ∏ x : closedPoints X.1, charPowerSeries
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2))
        (residueDegree f x.1) := by
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have hfd := LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_perfect B X ℓ f j
    kbar p q hcard F (LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_etale
      B X ℓ f j kbar F)
  have hzero := fun i (hi : i ≠ 0) =>
    LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_of_isFinite B X ℓ f j kbar
      F hi
  have hfin : {i : ℤ | Nontrivial
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)}.Finite :=
    (Set.finite_singleton 0).subset fun i hi => by
      by_contra h
      have := hzero i h
      exact not_nontrivial _ hi
  have hL := LAdicSheaf.rationalLFunction_eq_gradedCharSeries_of_traceFormula B X ℓ f j kbar p q
    hcard F hfd hfin fun k' _ _ _ _ _ _ _ _ q' hcard' =>
      LAdicSheaf.traceFormula_of_etale B (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar p q'
        hcard' (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F)
  rw [gradedCharSeries_eq_prod _ _ {0} (fun i hi => hzero i (by simpa using hi)),
    Finset.prod_singleton, gradedCharFactor, ite_eq_left Even.zero] at hL
  have hLprod : LAdicSheaf.rationalLFunction B X ℓ F f = ∏ x : closedPoints X.1,
      PowerSeries.invOfUnit (charPowerSeries
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2))
        (residueDegree f x.1)) 1 := by
    ext n
    rw [LAdicSheaf.coeff_rationalLFunction_eq B X ℓ F f (t := Finset.univ) (Finset.subset_univ _)]
    simp only [LAdicSheaf.localFactor_frobeniusMatrices]
  rw [hLprod] at hL
  calc _ = charPowerSeries
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
          0).hom 1 *
        ∏ x : closedPoints X.1, (charPowerSeries
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2))
          (residueDegree f x.1) * PowerSeries.invOfUnit (charPowerSeries
            (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2))
            (residueDegree f x.1)) 1) := by
        simp only [fun x : closedPoints X.1 => charPowerSeries_mul_invOfUnit
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2))
          (residueDegree_pos f x.1 x.2).ne', Finset.prod_const_one, mul_one]
    _ = _ := by
      rw [Finset.prod_mul_distrib, hL, mul_left_comm, charPowerSeries_mul_invOfUnit _ one_ne_zero,
        mul_one]

namespace LAdicSheaf

omit [CharP kbar p] [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [IsSeparated f] in
/-- **Weights in dimension zero.**  Let `X` be finite étale over a finite field `k` with `p ^ q`
elements and `F` an ℓ-adic sheaf on `X`, pointwise `ι`-mixed of weights `≤ w`.  Then every complex
root of the characteristic polynomial of `π_X^*` on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` along `ι` has absolute
value `(p ^ q) ^ (w' / 2)` for an integer `w' ≤ w + i`. -/
@[sga "7 XXI 5.5.2" "special case"]
theorem isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_etale
    [Etale f] [IsFinite f] (F : LAdicSheaf.{u, u + 1} B X ℓ) (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ)
    (hF : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F (p ^ q) ι w) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)] :
    IsCharpolyNormMixedOfWeightLE (p ^ q) ι (w + i)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom := by
  by_cases hi : i = 0
  swap
  · have := LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_of_isFinite B X ℓ
      f j kbar F hi
    exact isCharpolyNormMixedOfWeightLE_of_subsingleton _
  subst hi
  have : Finite X.1 := (finite_discreteTopology_of_isFinite f).1
  let : Fintype (closedPoints X.1) := Fintype.ofFinite _
  have h := LAdicSheaf.charPowerSeries_rationalGeometricCompactlySupportedFrobenius_eq_prod B X ℓ f
    j kbar p q hcard F
  let bV := Module.finBasis ℚ_[ℓ]
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F 0)
  set π := (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F 0)
  rw [charPowerSeries_eq_localCharSeries bV,
    Finset.prod_congr rfl fun x _ => (LAdicSheaf.localCharSeries_frobeniusMatrices B X ℓ F f x
      (residueDegree f x.1)).symm] at h
  have hA : IsUnit (LinearMap.toMatrix bV bV π.hom).det := by
    rw [LinearMap.det_toMatrix]
    exact (LinearMap.isUnit_iff_isUnit_det _).1
      ((Module.End.isUnit_iff _).2 (ConcreteCategory.bijective_of_isIso π))
  have hB : ∀ x ∈ (Finset.univ : Finset (closedPoints X.1)), ∀ y : ℂ,
      (((LAdicSheaf.frobeniusMatrices B X ℓ F f).matrix x).charpoly.map ι).IsRoot y →
      ∃ w' ≤ w, ‖y‖ = (((p ^ q) ^ residueDegree f x.1 : ℕ) : ℝ) ^ ((w' : ℝ) / 2) := by
    intro x _ y hy
    have hc : ((LAdicSheaf.frobeniusMatrices B X ℓ F f).matrix x).charpoly =
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2)).charpoly :=
      LinearMap.charpoly_toMatrix _ _
    rw [hc] at hy
    obtain ⟨w', hw', hy'⟩ := hF x y hy
    refine ⟨w', hw', ?_⟩
    rw [hy', Nat.cast_pow (p ^ q), ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    ring
  intro z hz
  rw [← LinearMap.charpoly_toMatrix π.hom bV] at hz
  obtain ⟨w', hw', hz'⟩ := isCharpolyNormMixedOfWeightLE_of_localCharSeries_eq_prod ι
    (LinearMap.toMatrix bV bV π.hom) hA Finset.univ
    (fun x => (LAdicSheaf.frobeniusMatrices B X ℓ F f).matrix x) (fun x => residueDegree f x.1)
    (fun x _ => (residueDegree_pos f x.1 x.2).ne') h hB z hz
  exact ⟨w', by lia, hz'⟩

end LAdicSheaf

end Weights

end Stacks.EtaleCohomology
