module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantCoefficientTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFrobeniusCurveWeil
public import StacksFrontier.LinearAlgebra.BlockTrace

/-!
# The trace of `φ^*` on `RΓ(C, ℤ/ℓ^m)` is the alternating sum of its traces on `Hⁱ(C, ℤ/ℓ^m)`

Let `C` be a smooth proper curve over an algebraically closed field `Ω`, `φ : C ⟶ C` a morphism
over `Ω` and `ℓ` a prime invertible in `Ω`. The pullback action `φ^*` on the perfect complex
`RΓ(C, ℤ/ℓ^m) = RΓ(Spec Ω, Rf_*(f^{-1} ℤ/ℓ^m))` (`Stacks.EtaleCohomology.selfMapCohomologyEndo`)
has trace

`Tr(φ^* | RΓ(C, ℤ/ℓ^m)) = ∑_{i = 0}^{2} (-1)^i Tr(φ^* | Hⁱ(C, ℤ/ℓ^m))`,

where on the right `Hⁱ(C, ℤ/ℓ^m)` is the étale cohomology of the constant sheaf and `φ^*` is
pullback (`Stacks.EtaleCohomology.etaleConstantCohomologyPullback`). Each cohomology module of
`RΓ(C, ℤ/ℓ^m)` is identified with `Hⁱ(C, ℤ/ℓ^m)` through `Hⁱ(C, μ_{ℓ^m})`. The identification
intertwines the two actions (`selfMapCohomologyRootsOfUnityAddEquiv_selfMapCohomologyEndo`,
`sheafHMap_rootsOfUnityConstantHom_etaleCohomologyMapTo`). The modules are free of finite rank
and vanish outside degrees `0, 1, 2`.

With the degreewise traces of [Stacks, Tag 03U3] this gives
`Tr(φ^* | RΓ(C, ℤ/ℓ^m)) = 1 - Tr_J(φ^*) + deg φ` modulo `ℓ^m`.

## Main results

* `perfectDerivedTrace_selfMapCohomologyEndo_eq_sum_trace_etaleConstantCohomologyPullback`:
  `Tr(φ^* | RΓ(C, ℤ/ℓ^m)) = ∑_{i = 0}^{2} (-1)^i Tr(φ^* | Hⁱ(C, ℤ/ℓ^m))`.
* `perfectDerivedTrace_selfMapCohomologyEndo_eq_toZModPow`:
  `Tr(φ^* | RΓ(C, ℤ/ℓ^m)) = 1 - Tr_J(φ^*) + deg φ` modulo `ℓ^m`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (f : C ⟶ Spec (.of Ω))
  [IsCurve Ω f] [Smooth f] [IsProper f] (φ : C ⟶ C) (w : φ ≫ f = f)
  [∀ N : ℕ, PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod N) φ)]

/-- The constant sheaf `ℤ/N` on `Spec Ω`, in degree zero. -/
abbrev baseConstantComplex (Ω : Type u) [Field Ω] (N : ℕ) :
    CochainComplex.Plus (EtaleModules.{u, 0} (ZMod N) (Spec (.of Ω))) :=
  (Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
    (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      (Spec (.of Ω)).smallEtaleTopology)

omit [IsCurve Ω f] [Smooth f] [IsProper f] in
include w in
/-- **The cohomology of `RΓ(C, ℤ/N)` is the étale cohomology of the constant sheaf, compatibly
with `φ^*`.** -/
theorem exists_homology_selfMapCohomology_addEquiv_sheafH {N : ℕ} (hN : IsUnit (N : Ω)) (q : ℕ) :
    ∃ E : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod N)) q).obj
        (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod N) f
          (baseConstantComplex Ω N))) ≃+
        Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod N)) q,
      ∀ y, E (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod N)) q).map
          (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod N) f φ w
            (baseConstantComplex Ω N)))).hom y) =
        etaleConstantCohomologyPullback φ (ZMod N) q (E y) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hN
  have hn0 := ne_zero_of_isUnit_natCast hN
  let R := selfMapCohomologyRootsOfUnityAddEquiv f hζ hn0 q
  let S := sheafHRootsOfUnityConstantAddEquiv f hζ hn0 q
  refine ⟨R.trans S.symm, fun y => ?_⟩
  apply S.injective
  change S (S.symm (R _)) = S (etaleConstantCohomologyPullback φ (ZMod N) q (S.symm (R y)))
  rw [AddEquiv.apply_symm_apply]
  have h2 := sheafHMap_rootsOfUnityConstantHom_etaleCohomologyMapTo f f φ w hζ hn0 q (S.symm (R y))
  rw [← sheafHRootsOfUnityConstantAddEquiv_apply, ← sheafHRootsOfUnityConstantAddEquiv_apply,
    AddEquiv.apply_symm_apply] at h2
  exact (selfMapCohomologyRootsOfUnityAddEquiv_selfMapCohomologyEndo f φ w hζ hn0 q y).trans h2.symm

/-- If `ℓ` is invertible in `Ω`, so is `ℓ ^ m`. -/
private theorem isUnit_natCast_pow {R : Type*} [CommRing R] (ℓ m : ℕ) (hℓ : IsUnit (ℓ : R)) :
    IsUnit (((ℓ ^ m : ℕ)) : R) := by
  rw [Nat.cast_pow]; exact hℓ.pow m

/-- The cohomology modules of `RΓ(C, ℤ/ℓ^m)` are free of finite rank over `ℤ/ℓ^m`. -/
theorem module_free_finite_homology_selfMapCohomology (ℓ m : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : Ω)) (q : ℕ) :
    Module.Free (ZMod (ℓ ^ m)) ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).obj (DerivedCategory.Plus.ι.obj
          (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f (baseConstantComplex Ω (ℓ ^ m))))) ∧
      Module.Finite (ZMod (ℓ ^ m)) ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).obj (DerivedCategory.Plus.ι.obj
          (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f (baseConstantComplex Ω (ℓ ^ m))))) := by
  have hN := isUnit_natCast_pow ℓ m hℓ
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hN
  have hn0 := ne_zero_of_isUnit_natCast hN
  let E : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).obj
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f
        (baseConstantComplex Ω (ℓ ^ m)))) ≃+
      Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod (ℓ ^ m))) q :=
    (selfMapCohomologyRootsOfUnityAddEquiv f hζ hn0 q).trans
      (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 q).symm
  obtain ⟨hF, hFin⟩ := module_free_finite_sheafH_etaleConstantSheaf f ℓ m hℓ q
  let L : _ ≃ₗ[ZMod (ℓ ^ m)] _ := { E with map_smul' := ZMod.map_smul E.toAddMonoidHom }
  exact ⟨Module.Free.of_equiv L.symm, Module.Finite.equiv L.symm⟩

/-- **The trace of `φ^*` on `Hⁱ(RΓ(C, ℤ/ℓ^m))` is its trace on `Hⁱ(C, ℤ/ℓ^m)`.** -/
theorem trace_homology_selfMapCohomologyEndo_eq_trace_etaleConstantCohomologyPullback
    (ℓ m : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Ω)) (q : ℕ) :
    LinearMap.trace (ZMod (ℓ ^ m)) _
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).map
          (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w
            (baseConstantComplex Ω (ℓ ^ m))))).hom =
      LinearMap.trace (ZMod (ℓ ^ m)) _
        ((etaleConstantCohomologyPullback φ (ZMod (ℓ ^ m)) q).toZModLinearMap (ℓ ^ m)) := by
  have hN := isUnit_natCast_pow ℓ m hℓ
  obtain ⟨hF, hFin⟩ := module_free_finite_homology_selfMapCohomology f ℓ m hℓ q
  obtain ⟨E, hE⟩ := exists_homology_selfMapCohomology_addEquiv_sheafH f φ w hN q
  exact AddMonoidHom.trace_toZModLinearMap_eq_of_addEquiv (n := ℓ ^ m) E
    ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).map
      (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w
        (baseConstantComplex Ω (ℓ ^ m))))).hom.toAddMonoidHom _ hE

omit [IsProper f] in
include f in
/-- **`Hⁱ(C, ℤ/N) = 0` for `i ≥ 3`**, for `N` invertible in `Ω`. -/
theorem subsingleton_sheafH_etaleConstantSheaf_of_three_le {N : ℕ} (hN : IsUnit (N : Ω))
    (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod N)) q) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 := ⟨q - 3, by omega⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hN
  have hn0 := ne_zero_of_isUnit_natCast hN
  have : Subsingleton (Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} C N) (r + 3)) :=
    Stacks.Kummer.subsingleton_sheafH_rootsOfUnitySheaf_of_isCurve f hN (r + 3) (by omega)
  exact (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 (r + 3)).injective.subsingleton

/-- **`Hⁱ(RΓ(C, ℤ/N)) = 0` for `i < 0`.** -/
private theorem subsingleton_homology_selfMapCohomology_of_neg {K : Type u} [Field K]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of K)) {N : ℕ} (i : ℤ) (hi : i < 0) :
    Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod N)) i).obj
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod N) g
        (baseConstantComplex K N)))) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (isZero_homology_selfMapCohomology_of_neg (ZMod N) g
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
        (Spec (.of K)).smallEtaleTopology) i hi)

omit [IsProper f] in
/-- **`Hⁱ(RΓ(C, ℤ/N)) = 0` for `i ∉ {0, 1, 2}`**, for `N` invertible in `Ω`. -/
theorem subsingleton_homology_selfMapCohomology_of_notMem {N : ℕ} (hN : IsUnit (N : Ω)) (i : ℤ)
    (hi : i ∉ ({0, 1, 2} : Finset ℤ)) :
    Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod N)) i).obj
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod N) f
        (baseConstantComplex Ω N)))) := by
  rcases lt_or_ge i 0 with hneg | hnn
  · exact subsingleton_homology_selfMapCohomology_of_neg (N := N) f i hneg
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
    have h3 : 3 ≤ q := by
      by_contra h
      apply hi
      interval_cases q <;> simp
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hN
    have hn0 := ne_zero_of_isUnit_natCast hN
    have := subsingleton_sheafH_etaleConstantSheaf_of_three_le f hN q h3
    exact ((selfMapCohomologyRootsOfUnityAddEquiv f hζ hn0 q).trans
      (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 q).symm).injective.subsingleton

/-- **`Tr(φ^* | RΓ(C, ℤ/ℓ^m)) = ∑_{i=0}^{2} (-1)^i Tr(φ^* | Hⁱ(C, ℤ/ℓ^m))`** for a smooth
proper curve `C` over an algebraically closed field and any morphism `φ` over it. -/
theorem perfectDerivedTrace_selfMapCohomologyEndo_eq_sum_trace_etaleConstantCohomologyPullback
    (ℓ m : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Ω))
    (hp : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f (baseConstantComplex Ω (ℓ ^ m))))) :
    perfectDerivedTrace (ZMod (ℓ ^ m)) ⟨_, hp⟩ (DerivedCategory.Plus.ι.map
        (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w (baseConstantComplex Ω (ℓ ^ m)))) =
      additiveCommutatorQuotientMk (ZMod (ℓ ^ m))
        (∑ i ∈ Finset.range 3, (-1 : ZMod (ℓ ^ m)) ^ i * LinearMap.trace (ZMod (ℓ ^ m)) _
          ((etaleConstantCohomologyPullback φ (ZMod (ℓ ^ m)) i).toZModLinearMap (ℓ ^ m))) := by
  classical
  have hN := isUnit_natCast_pow ℓ m hℓ
  have hfree := module_free_finite_homology_selfMapCohomology f ℓ m hℓ
  have htr := trace_homology_selfMapCohomologyEndo_eq_trace_etaleConstantCohomologyPullback
    f φ w ℓ m hℓ
  set K := baseConstantComplex Ω (ℓ ^ m)
  set H : ℤ → ModuleCat.{u + 1} (ZMod (ℓ ^ m)) := fun i =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) i).obj
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f K))
  have hH : HasFiniteProjectiveHomology.{0, u + 1} (ZMod (ℓ ^ m))
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f K)) := fun i => by
    rcases lt_or_ge i 0 with hi | hi
    · have := subsingleton_homology_selfMapCohomology_of_neg (N := ℓ ^ m) f i hi
      exact ⟨inferInstance, inferInstance⟩
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      have : Module.Free (ZMod (ℓ ^ m)) (H q) := (hfree q).1
      exact ⟨inferInstance, (hfree q).2⟩
  rw [perfectDerivedTrace_selfMapCohomologyEndo_eq_sum _ f φ w K hp hH]
  have hterm : ∀ q : ℕ, derivedHomologyTrace (ZMod (ℓ ^ m)) _ hH
      (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w K)) q =
        additiveCommutatorQuotientMk (ZMod (ℓ ^ m)) (LinearMap.trace (ZMod (ℓ ^ m)) _
          ((etaleConstantCohomologyPullback φ (ZMod (ℓ ^ m)) q).toZModLinearMap (ℓ ^ m))) := by
    intro q
    obtain ⟨_, _⟩ : Module.Free (ZMod (ℓ ^ m)) (H q) ∧ Module.Finite (ZMod (ℓ ^ m)) (H q) := hfree q
    rw [← htr q]
    exact Stacks.Trace.projectiveModuleTrace_eq_mk_trace _ _ _
  have hzero : ∀ i : ℤ, i ∉ (({0, 1, 2} : Finset ℤ) : Set ℤ) →
      signedByDegree (ZMod (ℓ ^ m)) i (derivedHomologyTrace (ZMod (ℓ ^ m)) _ hH
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w K)) i) =
        0 := by
    intro i hi
    have hsub : Subsingleton (H i) :=
      subsingleton_homology_selfMapCohomology_of_notMem f hN i fun h => hi (Finset.mem_coe.mpr h)
    unfold derivedHomologyTrace signedByDegree
    simp only [projectiveModuleTrace_eq_zero_of_subsingleton, neg_zero, ite_self]
  rw [finsum_eq_sum_of_support_subset _ (fun i hi => by_contra fun h => hi (hzero i h)),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 := hterm 0
  have h1 := hterm 1
  have h2 := hterm 2
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h2
  rw [h0, h1, h2]
  obtain ⟨e0, e2⟩ : Even (0 : ℤ) ∧ Even (2 : ℤ) := ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
  simp only [signedByDegree, ite_eq_left e0, ite_eq_left e2, ite_eq_right Int.not_even_one,
    pow_zero, pow_one, one_mul, neg_one_mul, neg_one_sq, map_add, map_neg]
  abel

/-- **`Tr(φ^* | RΓ(C, ℤ/ℓ^m)) = 1 - Tr_J(φ^*) + deg φ` modulo `ℓ^m`**, by the degreewise traces of
[Stacks, Tag 03U3]. -/
theorem perfectDerivedTrace_selfMapCohomologyEndo_eq_toZModPow (ℓ m : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : Ω))
    (hp : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f (baseConstantComplex Ω (ℓ ^ m))))) :
    perfectDerivedTrace (ZMod (ℓ ^ m)) ⟨_, hp⟩ (DerivedCategory.Plus.ι.map
        (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w (baseConstantComplex Ω (ℓ ^ m)))) =
      additiveCommutatorQuotientMk (ZMod (ℓ ^ m))
        (PadicInt.toZModPow m (1 - AlgebraicGeometry.CurveGraph.jacobianTateTrace f
          (IsCurve.topologicalKrullDim_eq_one (f := f)).le φ w ℓ +
            (AlgebraicGeometry.CurveGraph.curveMapDegree f φ w : ℤ_[ℓ]))) := by
  rw [perfectDerivedTrace_selfMapCohomologyEndo_eq_sum_trace_etaleConstantCohomologyPullback f φ w ℓ
    m hℓ hp, sum_trace_etaleConstantCohomologyPullback_eq_toZModPow f φ w ℓ m hℓ]

end Stacks.EtaleCohomology

end
