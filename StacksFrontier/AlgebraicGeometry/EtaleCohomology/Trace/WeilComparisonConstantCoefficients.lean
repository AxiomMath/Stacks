module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafStalkFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusFixedPointIntersection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaOpenClosedDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusConstantSelfMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveSelfMapAlternatingTrace
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceModules
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfectOfCtf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories

/-!
# The trace formula with constant coefficients and Weil's formula

[Stacks, Tag 03UJ] remarks that the trace formula [Stacks, Tag 03UG] is much stronger than Weil's
geometric trace formula [Stacks, Tag 03U1], because it applies to coefficient systems and not
merely to constant coefficients. This file makes the constant-coefficient case precise.

Let `X` be a proper smooth curve over a finite field `k` with `q = p ^ f` elements, geometrically
a curve, let `ℓ ≠ p` be a prime and `Λ = ℤ/ℓⁿ`. Write `π̄ = π_X × id` for the base change to
`X_k̄` of the geometric Frobenius.

* For the constant sheaf `Λ` the local term `Tr(π_x | Λ_x̄)` of the trace formula is `1` at every
  rational point. So the trace formula reads `Tr(π_X^* | RΓ(X_k̄, Λ)) = #X(k)`.
* The left hand side is the alternating sum of the traces of the pullback `π̄^*` on the étale
  cohomology groups `Hⁱ(X_k̄, ℤ/ℓⁿ)`, `i = 0, 1, 2`. By [Stacks, Tag 03U3] that sum is
  `1 - Tr_J(π̄^*) + deg π̄` modulo `ℓⁿ`.
* The fixed points of `π̄` are the rational points, each with multiplicity one, so Weil's
  intersection number is `V(π̄) = #X(k)`
  (`Stacks.Frobenius.fixedPointIntersection_geometricFrobeniusBaseChange_eq_natCard`).

## Main results

All in the namespace `Stacks.EtaleCohomology`.

* `isCtf_constantCoefficients`: the constant sheaf `Λ` lies in `D_ctf`.
* `canonicalCompactSupportLefschetzNumber_constantCoefficients_of_canonicalTraceFormula`: where the
  trace formula holds for the constant sheaf `Λ`, the Lefschetz number of `π^*` on `RΓ_c(X_k̄, Λ)`
  is `#X(k)` in `Λ^♮`.
* `canonicalCompactSupportLefschetzNumber_constantCoefficients_eq_sum_trace`: for a proper smooth
  curve, the Lefschetz number with constant coefficients is
  `∑_{i=0}^{2} (-1)^i Tr(π̄^* | Hⁱ(X_k̄, ℤ/ℓⁿ))`.
* `canonicalCompactSupportLefschetzNumber_constantCoefficients_eq_toZModPow`: it is
  `1 - Tr_J(π̄^*) + deg π̄` modulo `ℓⁿ`.

## References

* [Stacks Project, Tag 03UJ](https://stacks.math.columbia.edu/tag/03UJ)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
* [Stacks Project, Tag 03U1](https://stacks.math.columbia.edu/tag/03U1)
* [Stacks Project, Tag 03U3](https://stacks.math.columbia.edu/tag/03U3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.FilteredDerived
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The constant sheaf `Λ` on the small étale site of `X`, as a complex concentrated in degree
zero: the coefficient system of the trace formula with constant coefficients. -/
abbrev constantCoefficients (Λ : Type) [Ring Λ] (X : Scheme.{u}) :
    CochainComplex.Plus (EtaleModules.{u, 0} Λ X) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapCochainComplexPlus.obj
    (constantCoefficientComplex.{u, 0} Λ)

/-- **The constant sheaf `Λ` lies in `D_ctf(X_étale, Λ)`.** -/
theorem isCtf_constantCoefficients (B : BigEtaleSite.{u}) (Λ : Type) [CommRing Λ] (X : B.Scheme) :
    IsCtf B X Λ (DerivedCategory.Q.obj (constantCoefficients Λ X.obj).obj) :=
  IsCtf.of_iso.{u, 0} B X Λ (DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex
      (constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ) 0).app
        (ModuleCat.of Λ (ULift.{u + 1} Λ))).symm) (isCtf_constantModuleSheaf.{u, 0} (Λ := Λ) B X)

/-- A proper curve over a field is projective. -/
theorem isProjective_of_isProper_of_isCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] : IsProjective f :=
  (isProjective_iff_isProjectiveMorphism_of_isAffine f).2
    (isProjectiveMorphism_of_isProper_of_isCurve k f)

/-- **`RΓ(X_k̄, Λ)` is perfect** for a projective curve `X` over `k`, compactified by itself, and
`k̄` an algebraic closure of `k` ([Stacks, Tag 03TV] for the constant sheaf). -/
theorem isPerfect_compactSupportFrobeniusCohomology_constantCoefficients (B : BigEtaleSite.{u})
    (Λ : Type) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] {X : B.Scheme}
    (f : X.obj ⟶ Spec (.of k)) [IsCurve k f] (hproj : IsProjective f) (kbar : Type u) [Field kbar]
    [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar] :
    haveI := hproj.isProper
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f (CompactificationOf.ofProper f) kbar
        (constantCoefficients Λ X.obj))) :=
  have := hproj.isProper
  isPerfect_compactSupportFrobeniusCohomology_of_isCtf_of_isProjective B Λ
    (CompactificationOf.ofProper f) kbar X.property (inferInstanceAs (IsCurve k f)) hproj _
    (isCtf_constantCoefficients B Λ X)

section TraceFormula

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- **With constant coefficients the trace formula counts rational points.** For a scheme `X`
over `k` with finitely many rational points and any compactification `j`, if the trace formula
of [Stacks, Tag 03UG] holds for the constant sheaf `Λ`, then

`Tr(π^* | RΓ_c(X_k̄, Λ)) = #X(k)`

in `Λ^♮`: every local term `Tr(π_x | Λ_x̄)` is `1`. -/
theorem canonicalCompactSupportLefschetzNumber_constantCoefficients_of_canonicalTraceFormula
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Finite (rationalPoints f)]
    (j : CompactificationOf (Over.mk f))
    (h : CanonicalTraceFormula Λ kbar p q hcard f j (constantCoefficients Λ X)) :
    ∃ hX, canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard
        (constantCoefficients Λ X) hX =
      (Nat.card (rationalPoints f) : ℤ) • additiveCommutatorQuotientMk Λ 1 := by
  obtain ⟨hX, hs, heq⟩ := h
  refine ⟨hX, heq.trans ?_⟩
  have hN := isPerfect_constantCoefficientComplex.{u, 0} Λ
  have hloc : ∀ x : rationalPoints f, perfectDerivedTrace Λ ⟨_, hs x⟩
      (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1
        (constantCoefficients Λ X))) = additiveCommutatorQuotientMk Λ 1 := fun x =>
    (perfectDerivedTrace_rationalPointStalkFrobenius_constant Λ kbar p q hcard x.1 _ hN
      (hs x)).trans (perfectDerivedTrace_id_constantCoefficientComplex Λ hN)
  simp_rw [hloc]
  have := Fintype.ofFinite (rationalPoints f)
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    natCast_zsmul]

end TraceFormula

section Curve

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  [Smooth f] (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
  [IsCurve kbar (pullback.snd f (specAlgebraMap k kbar))] (p q : ℕ) [Fact p.Prime] [CharP k p]
  [CharP kbar p] (hcard : Fintype.card k = p ^ q) (ℓ n : ℕ) [Fact ℓ.Prime]

omit [IsProper f] [Smooth f] [IsAlgClosed kbar]
  [IsCurve kbar (pullback.snd f (specAlgebraMap k kbar))] in
/-- A prime `ℓ ≠ p` is invertible in a field of characteristic `p`. -/
theorem isUnit_natCast_of_ne_char (hℓ : ℓ ≠ p) : IsUnit (ℓ : kbar) := by
  refine isUnit_iff_ne_zero.mpr fun h => hℓ ?_
  rw [CharP.cast_eq_zero_iff kbar p] at h
  exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mp h).symm

/-- The constant sheaf `ℤ/N` on `Spec k̄` in its two shapes: the constant complex of the module
`ℤ/N` in degree zero, and the constant sheaf in degree zero. -/
def etaleModuleConstantComplexIsoBaseConstantComplex (N : ℕ) :
    etaleModuleConstantComplex (ZMod N) kbar (constantCoefficientComplex.{u, 0} (ZMod N)) ≅
      baseConstantComplex kbar N :=
  ObjectProperty.isoMk _ ((HomologicalComplex.singleMapHomologicalComplex
    (constantSheaf (Spec (.of kbar)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod N)))
    (ComplexShape.up ℤ) 0).app (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))))

/-- **The trace formula's left hand side with constant coefficients is the alternating sum of the
traces of `π̄^*` on `Hⁱ(X_k̄, ℤ/ℓⁿ)`.** For a proper smooth curve `X` over `k`, compactified by
itself, and `ℓ ≠ p`,

`Tr(π_X^* | RΓ_c(X_k̄, ℤ/ℓⁿ)) = ∑_{i=0}^{2} (-1)^i Tr(π̄^* | Hⁱ(X_k̄, ℤ/ℓⁿ))`,

where on the right `π̄^*` is pullback on étale cohomology with constant coefficients. -/
theorem canonicalCompactSupportLefschetzNumber_constantCoefficients_eq_sum_trace (hℓ : ℓ ≠ p)
    (hX : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ n)) f (CompactificationOf.ofProper f)
        kbar (constantCoefficients (ZMod (ℓ ^ n)) X)))) :
    canonicalCompactSupportLefschetzNumber.{u, 0} (ZMod (ℓ ^ n)) f (CompactificationOf.ofProper f)
        kbar p q hcard (constantCoefficients (ZMod (ℓ ^ n)) X) hX =
      additiveCommutatorQuotientMk (ZMod (ℓ ^ n))
        (∑ i ∈ Finset.range 3, (-1 : ZMod (ℓ ^ n)) ^ i * LinearMap.trace (ZMod (ℓ ^ n)) _
          ((etaleConstantCohomologyPullback
            (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
            (ZMod (ℓ ^ n)) i).toZModLinearMap (ℓ ^ n))) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero⟩
  have hℓ' := isUnit_natCast_of_ne_char kbar p ℓ hℓ
  have h₂ := isPerfect_selfMapCohomology_constant_of_ofProper (ZMod (ℓ ^ n)) f kbar
    (constantCoefficientComplex.{u, 0} (ZMod (ℓ ^ n))) hX
  have h₃ := (isPerfect_selfMapCohomology_iff_of_iso (ZMod (ℓ ^ n))
    (pullback.snd f (specAlgebraMap k kbar))
    (etaleModuleConstantComplexIsoBaseConstantComplex kbar (ℓ ^ n))).mp h₂
  refine (canonicalCompactSupportLefschetzNumber_ofProper_constant_eq_selfMap (ZMod (ℓ ^ n)) f kbar
    p q hcard _ hX h₂).trans ?_
  refine (perfectDerivedTrace_selfMapCohomologyEndo_eq_of_iso (ZMod (ℓ ^ n))
    (pullback.snd f (specAlgebraMap k kbar)) _ _
    (etaleModuleConstantComplexIsoBaseConstantComplex kbar (ℓ ^ n)) h₂ h₃).trans ?_
  have : ∀ N : ℕ, PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod N)
      (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)) := fun N =>
    etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism (ZMod N) _
  exact perfectDerivedTrace_selfMapCohomologyEndo_eq_sum_trace_etaleConstantCohomologyPullback
    (pullback.snd f (specAlgebraMap k kbar)) _ _ ℓ n hℓ' h₃

/-- **The trace formula's left hand side with constant coefficients is `1 - Tr_J(π̄^*) + deg π̄`**
modulo `ℓⁿ`, the right hand side of Weil's formula [Stacks, Tag 03U1] for the geometric
Frobenius, by the degreewise traces of [Stacks, Tag 03U3]. -/
theorem canonicalCompactSupportLefschetzNumber_constantCoefficients_eq_toZModPow (hℓ : ℓ ≠ p)
    (hX : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ n)) f (CompactificationOf.ofProper f)
        kbar (constantCoefficients (ZMod (ℓ ^ n)) X)))) :
    canonicalCompactSupportLefschetzNumber.{u, 0} (ZMod (ℓ ^ n)) f (CompactificationOf.ofProper f)
        kbar p q hcard (constantCoefficients (ZMod (ℓ ^ n)) X) hX =
      additiveCommutatorQuotientMk (ZMod (ℓ ^ n))
        (PadicInt.toZModPow n (1 - AlgebraicGeometry.CurveGraph.jacobianTateTrace
          (pullback.snd f (specAlgebraMap k kbar))
          (IsCurve.topologicalKrullDim_eq_one (k := kbar)
            (f := pullback.snd f (specAlgebraMap k kbar))).le
          (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
          (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) ℓ +
            (AlgebraicGeometry.CurveGraph.curveMapDegree (pullback.snd f (specAlgebraMap k kbar))
              (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
              (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) : ℤ_[ℓ]))) := by
  rw [canonicalCompactSupportLefschetzNumber_constantCoefficients_eq_sum_trace f kbar p q hcard ℓ n
    hℓ hX]
  exact congrArg _ (sum_trace_etaleConstantCohomologyPullback_eq_toZModPow
    (pullback.snd f (specAlgebraMap k kbar))
    (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
    (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) ℓ n
    (isUnit_natCast_of_ne_char kbar p ℓ hℓ))

end Curve

/-- The hypotheses on `X` over `k` and on `X_k̄` hold for `Over.mk f` and its base change. -/
private theorem overMk_instances {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProper f] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [Algebra.IsAlgebraic k kbar] [IsCurve kbar (pullback.snd f (specAlgebraMap k kbar))] :
    LocallyOfFiniteType (Over.mk f).hom ∧ QuasiCompact (Over.mk f).hom ∧
      IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) ∧
      Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) ∧
      IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
  ⟨(inferInstance : LocallyOfFiniteType f), (inferInstance : QuasiCompact f),
    (inferInstance : IsCurve kbar (pullback.snd f (specAlgebraMap k kbar))),
    (inferInstance : Smooth (pullback.snd f (specAlgebraMap k kbar))),
    (inferInstance : IsProper (pullback.snd f (specAlgebraMap k kbar)))⟩

section Assembly

variable (B : BigEtaleSite.{u}) {k : Type u} [Field k] [Fintype k] {p q : ℕ} [Fact p.Prime]
  [CharP k p] (hcard : Fintype.card k = p ^ q) {X : B.Scheme} (f : X.obj ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  [IsCurve kbar (pullback.snd f (specAlgebraMap k kbar))] (ℓ n : ℕ) [Fact ℓ.Prime]

/-- `π̄ = π_X × id` is not the identity of the curve `X_k̄`: it moves some point. -/
theorem geometricFrobeniusBaseChange_ne_id :
    geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard ≠ 𝟙 _ := by
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  obtain ⟨_, _, _, _, _⟩ := overMk_instances f kbar
  intro h
  obtain ⟨c, hc⟩ := exists_geometricFrobeniusBaseChange_base_ne (Over.mk f) kbar p q hcard
  exact hc (by rw [h]; rfl)

/-- **The trace formula with constant coefficients and Weil's formula compute the same number,
granted the two formulas.** -/
theorem traceFormula_constantCoefficients_weil_of (hℓ : ℓ ≠ p)
    (hUG : haveI : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
      CanonicalTraceFormula (ZMod (ℓ ^ n)) kbar p q hcard f (CompactificationOf.ofProper f)
        (constantCoefficients (ZMod (ℓ ^ n)) X.obj))
    (hU1 : ((AlgebraicGeometry.CurveGraph.fixedPointIntersection
          (pullback.snd f (specAlgebraMap k kbar))
          (IsCurve.topologicalKrullDim_eq_one (k := kbar)
            (f := pullback.snd f (specAlgebraMap k kbar))).le
          (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
          (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) : ℤ) : ℤ_[ℓ]) =
        1 - AlgebraicGeometry.CurveGraph.jacobianTateTrace (pullback.snd f (specAlgebraMap k kbar))
          (IsCurve.topologicalKrullDim_eq_one (k := kbar)
            (f := pullback.snd f (specAlgebraMap k kbar))).le
          (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
          (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) ℓ +
          (AlgebraicGeometry.CurveGraph.curveMapDegree (pullback.snd f (specAlgebraMap k kbar))
            (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
            (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) : ℤ_[ℓ])) :
    canonicalCompactSupportLefschetzNumber.{u, 0} (ZMod (ℓ ^ n)) f (CompactificationOf.ofProper f)
        kbar p q hcard (constantCoefficients (ZMod (ℓ ^ n)) X.obj)
        (isPerfect_compactSupportFrobeniusCohomology_constantCoefficients B (ZMod (ℓ ^ n)) f
          (isProjective_of_isProper_of_isCurve f) kbar) =
      (Nat.card (rationalPoints f) : ℤ) • additiveCommutatorQuotientMk (ZMod (ℓ ^ n)) 1 ∧
    canonicalCompactSupportLefschetzNumber.{u, 0} (ZMod (ℓ ^ n)) f (CompactificationOf.ofProper f)
        kbar p q hcard (constantCoefficients (ZMod (ℓ ^ n)) X.obj)
        (isPerfect_compactSupportFrobeniusCohomology_constantCoefficients B (ZMod (ℓ ^ n)) f
          (isProjective_of_isProper_of_isCurve f) kbar) =
      additiveCommutatorQuotientMk (ZMod (ℓ ^ n))
        (∑ i ∈ Finset.range 3, (-1 : ZMod (ℓ ^ n)) ^ i * LinearMap.trace (ZMod (ℓ ^ n)) _
          ((etaleConstantCohomologyPullback
            (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
            (ZMod (ℓ ^ n)) i).toZModLinearMap (ℓ ^ n))) ∧
    AlgebraicGeometry.CurveGraph.fixedPointIntersection (pullback.snd f (specAlgebraMap k kbar))
        (IsCurve.topologicalKrullDim_eq_one (k := kbar)
          (f := pullback.snd f (specAlgebraMap k kbar))).le
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
        (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) =
      Nat.card (rationalPoints f) ∧
    (((Nat.card (rationalPoints f) : ℤ)) : ℤ_[ℓ]) =
      1 - AlgebraicGeometry.CurveGraph.jacobianTateTrace (pullback.snd f (specAlgebraMap k kbar))
        (IsCurve.topologicalKrullDim_eq_one (k := kbar)
          (f := pullback.snd f (specAlgebraMap k kbar))).le
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
        (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) ℓ +
        (AlgebraicGeometry.CurveGraph.curveMapDegree (pullback.snd f (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
          (geometricFrobeniusBaseChange_comp_toBase (Over.mk f) kbar p q hcard) : ℤ_[ℓ]) := by
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : Finite (rationalPoints f) := finite_rationalPoints f
  obtain ⟨_, _, _, _, _⟩ := overMk_instances f kbar
  have hq : q ≠ 0 := ne_zero_of_card_eq_pow hcard
  have hV := fixedPointIntersection_geometricFrobeniusBaseChange_eq_natCard (Over.mk f) kbar p q
    hcard hq (IsCurve.topologicalKrullDim_eq_one (k := kbar)
      (f := pullback.snd f (specAlgebraMap k kbar))).le
  obtain ⟨hX, hL⟩ :=
    canonicalCompactSupportLefschetzNumber_constantCoefficients_of_canonicalTraceFormula
      (ZMod (ℓ ^ n)) kbar p q hcard f (CompactificationOf.ofProper f) hUG
  refine ⟨hL, canonicalCompactSupportLefschetzNumber_constantCoefficients_eq_sum_trace f kbar p q
    hcard ℓ n hℓ _, hV, ?_⟩
  exact (congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hV).symm.trans hU1

end Assembly

end Stacks.EtaleCohomology

end
