module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantCoefficientTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapFixedPointTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of `φ^*` on `RΓ(C, ℤ/ℓ^m)`, degree by degree

For a smooth proper curve `f : C ⟶ Spec k` over an algebraically closed field and an integral
endomorphism `φ` of `C` over `k`, the endomorphism `φ^*` of `RΓ(C, ℤ/ℓ^m)` of Step 9 of the proof
of [Stacks, Tag 03UG] (`Stacks.EtaleCohomology.selfMapCohomologyEndo`) has finite free cohomology
modules, and

`∑_i (-1)^i Tr(φ^* | H^i(RΓ(C, ℤ/ℓ^m))) = 1 - Tr(φ^* | Pic(C)[ℓ^m]) + deg φ`.

The cohomology of `RΓ(C, ℤ/n)` is identified with `H^i(C, ℤ/n)` through `H^i(C, μ_n)`
(`Stacks.EtaleCohomology.selfMapCohomologyRootsOfUnityAddEquiv`), compatibly with `φ^*`, and the
traces there are those of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantCoefficientTrace`.

## Main results

* `CategoryTheory.FilteredDerived.projectiveModuleTrace_eq_additiveCommutatorQuotientMk_trace` —
  over a commutative ring the trace of a finite free module is the usual trace.
* `Stacks.EtaleCohomology.hasFiniteProjectiveHomology_curveConstantCohomology`.
* `Stacks.EtaleCohomology.finsum_signedByDegree_derivedHomologyTrace_curveConstantCohomologyEndo`.

None of the declarations here is registered.

## References

* [Stacks Project, Tag 03U3](https://stacks.math.columbia.edu/tag/03U3)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u v

namespace CategoryTheory.FilteredDerived

/-- **The trace of a finite free module over a commutative ring** is the usual trace, read in the
additive commutator quotient. -/
@[sga "5 IIIB 5.0" "special case", sga "5 IIIB 5.7" "special case"]
theorem projectiveModuleTrace_eq_additiveCommutatorQuotientMk_trace (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
    (f : Module.End R P) :
    Stacks.Trace.projectiveModuleTrace R P f =
      additiveCommutatorQuotientMk R (LinearMap.trace R P f) := by
  classical
  let b := Module.Free.chooseBasis R P
  let e := b.equivFun
  rw [projectiveModuleTrace_eq_of_split R P f e.symm.toLinearMap e.toLinearMap
    (by ext x; simp), freeModuleTrace_apply, LinearMap.trace_eq_matrix_trace R b f]
  congr 1

end CategoryTheory.FilteredDerived

namespace Stacks.EtaleCohomology

open Stacks.Kummer CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard
  isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Sheaf.monoidalCategory
  etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  (φ : C ⟶ C) (w : φ ≫ f = f) (n : ℕ)

/-- `RΓ(C, ℤ/n)`, computed as `RΓ(Spec k, Rf_*(f^{-1} ℤ/n))`. -/
abbrev curveConstantCohomology : DerivedCategory.Plus (ModuleCat.{u + 1} (ZMod n)) :=
  selfMapCohomology.{u, 0} (ZMod n) f ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
    (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
      (Spec (.of k)).smallEtaleTopology))

/-- The pullback action `φ^*` on `RΓ(C, ℤ/n)`. -/
abbrev curveConstantCohomologyEndo : curveConstantCohomology f n ⟶ curveConstantCohomology f n :=
  selfMapCohomologyEndo.{u, 0} (ZMod n) f φ w ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
    (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
      (Spec (.of k)).smallEtaleTopology))

variable {n} {ζ : k} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)

/-- **`H^i(RΓ(C, ℤ/n)) ≃+ H^i(C, ℤ/n)`**, through `H^i(C, μ_n)` and the choice of `ζ`. -/
def curveConstantCohomologyHomologyAddEquiv (i : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod n)) i).obj
          (curveConstantCohomology f n)) ≃+
      Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod n)) i :=
  (selfMapCohomologyRootsOfUnityAddEquiv f hζ hn i).trans
    (sheafHRootsOfUnityConstantAddEquiv f hζ hn i).symm

omit [IsAlgClosed k] in
include w in
/-- Under `curveConstantCohomologyHomologyAddEquiv`, the action of `φ^*` on `H^i(RΓ(C, ℤ/n))` is
the pullback `φ^*` on `H^i(C, ℤ/n)`, for `φ` integral (so that `φ_*` is exact). -/
theorem curveConstantCohomologyHomologyAddEquiv_map [IsIntegralHom φ] (i : ℕ)
    (x : (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod n)) i).obj
          (curveConstantCohomology f n))) :
    curveConstantCohomologyHomologyAddEquiv f hζ hn i
        (((forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).map
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod n)) i).map
            (curveConstantCohomologyEndo f φ w n))).hom x) =
      etaleConstantCohomologyPullback φ (ZMod n) i
        (curveConstantCohomologyHomologyAddEquiv f hζ hn i x) := by
  have := isMonoidal_W_etaleModules (ZMod n) C
  apply (sheafHRootsOfUnityConstantAddEquiv f hζ hn i).injective
  have hR : sheafHRootsOfUnityConstantAddEquiv f hζ hn i
      (etaleConstantCohomologyPullback φ (ZMod n) i
      (curveConstantCohomologyHomologyAddEquiv f hζ hn i x)) =
      rootsOfUnityPullbackMap.{u, 0, u + 1} φ n i
        (selfMapCohomologyRootsOfUnityAddEquiv f hζ hn i x) := by
    rw [sheafHRootsOfUnityConstantAddEquiv_apply,
      sheafHMap_rootsOfUnityConstantHom_etaleCohomologyMapTo f f φ w hζ hn,
      ← sheafHRootsOfUnityConstantAddEquiv_apply, curveConstantCohomologyHomologyAddEquiv,
      AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [hR, curveConstantCohomologyHomologyAddEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  exact selfMapCohomologyRootsOfUnityAddEquiv_selfMapCohomologyEndo f φ w hζ hn i x

section Curve

variable [IsCurve k f] [Smooth f] [IsProper f]

omit [IsAlgClosed k] [IsCurve k f] [Smooth f] [IsProper f] in
include f in
/-- `H^i(RΓ(C, ℤ/n)) = 0` for `i < 0`. -/
theorem isZero_homology_curveConstantCohomology_of_neg (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod n)) i).obj
      (DerivedCategory.Plus.ι.obj (curveConstantCohomology f n))) :=
  have := etaleModules_enoughInjectives.{u, 0} (ZMod n) C
  (Functor.isZero_rightDerivedPlus_of_neg _ _ i hi).of_iso
    (selfMapCohomologySingleIso.{u, 0} (ZMod n) f _ i)

/-- If `ℓ` is a unit in `k`, so is `ℓ ^ m`. -/
private theorem isUnit_natCast_pow_of_isUnit {ℓ : ℕ} {k : Type*} [Field k] (hℓ : IsUnit (ℓ : k))
    (m : ℕ) : IsUnit (((ℓ ^ m : ℕ)) : k) := by
  rw [Nat.cast_pow]; exact hℓ.pow m

/-- `H^i(RΓ(C, ℤ/ℓ^m))` is a finite free `ℤ/ℓ^m`-module. -/
private theorem module_free_finite_homology_curveConstantCohomology (ℓ m : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) {ζ : k} (hζ : IsPrimitiveRoot ζ (ℓ ^ m)) (hn0 : ℓ ^ m ≠ 0) (i : ℕ) :
    Module.Free (ZMod (ℓ ^ m)) ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) (i : ℤ)).obj
      (DerivedCategory.Plus.ι.obj (curveConstantCohomology f (ℓ ^ m)))) ∧
    Module.Finite (ZMod (ℓ ^ m)) ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) (i : ℤ)).obj
      (DerivedCategory.Plus.ι.obj (curveConstantCohomology f (ℓ ^ m)))) := by
  obtain ⟨_, _⟩ := module_free_finite_sheafH_etaleConstantSheaf f ℓ m hℓ i
  exact module_free_finite_of_addEquiv (n := ℓ ^ m)
    (M := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) (i : ℤ)).obj
      (DerivedCategory.Plus.ι.obj (curveConstantCohomology f (ℓ ^ m))))
    (curveConstantCohomologyHomologyAddEquiv f hζ hn0 i)

/-- **`RΓ(C, ℤ/ℓ^m)` has finite free cohomology modules** (`H⁰`, `H²` of rank one, `H¹` of rank
`2g`, the others zero), as a complex of `ℤ/ℓ^m`-modules. -/
theorem hasFiniteProjectiveHomology_curveConstantCohomology (ℓ m : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) :
    HasFiniteProjectiveHomology.{0, u + 1} (ZMod (ℓ ^ m))
      (DerivedCategory.Plus.ι.obj (curveConstantCohomology f (ℓ ^ m))) := by
  intro i
  rcases lt_or_ge i 0 with hi | hi
  · have := ModuleCat.subsingleton_of_isZero
      (isZero_homology_curveConstantCohomology_of_neg f (ℓ ^ m) i hi)
    exact ⟨inferInstance, Module.Finite.of_finite⟩
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    have hn := isUnit_natCast_pow_of_isUnit hℓ m
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
    obtain ⟨_, h2⟩ := module_free_finite_homology_curveConstantCohomology f ℓ m hℓ hζ
      (ne_zero_of_isUnit_natCast hn) j
    exact ⟨inferInstance, h2⟩

include w in
/-- **The trace of `φ^*` on `H^i(RΓ(C, ℤ/ℓ^m))` is its trace on `H^i(C, ℤ/ℓ^m)`.** -/
theorem derivedHomologyTrace_curveConstantCohomologyEndo [IsIntegralHom φ] (ℓ m : ℕ)
    [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k))
    (hH : HasFiniteProjectiveHomology.{0, u + 1} (ZMod (ℓ ^ m))
      (DerivedCategory.Plus.ι.obj (curveConstantCohomology f (ℓ ^ m)))) (i : ℕ) :
    derivedHomologyTrace _ _ hH
        (DerivedCategory.Plus.ι.map (curveConstantCohomologyEndo f φ w (ℓ ^ m))) i =
      additiveCommutatorQuotientMk _ (LinearMap.trace (ZMod (ℓ ^ m)) _
        ((etaleConstantCohomologyPullback φ (ZMod (ℓ ^ m)) i).toZModLinearMap (ℓ ^ m))) := by
  have hn := isUnit_natCast_pow_of_isUnit hℓ m
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
  have hn0 := ne_zero_of_isUnit_natCast hn
  obtain ⟨_, _⟩ := module_free_finite_homology_curveConstantCohomology f ℓ m hℓ hζ hn0 i
  unfold derivedHomologyTrace
  rw [projectiveModuleTrace_eq_additiveCommutatorQuotientMk_trace]
  congr 1
  refine trace_toZModLinearMap_eq_of_addEquiv
    (M := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) (i : ℤ)).obj
      (DerivedCategory.Plus.ι.obj (curveConstantCohomology f (ℓ ^ m))))
    (curveConstantCohomologyHomologyAddEquiv f hζ hn0 i)
    (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) (i : ℤ)).map
      (DerivedCategory.Plus.ι.map (curveConstantCohomologyEndo f φ w (ℓ ^ m)))).hom.toAddMonoidHom)
    _ (curveConstantCohomologyHomologyAddEquiv_map f φ w hζ hn0 i)

include w in
/-- **`Tr(φ^* | RΓ(C, ℤ/ℓ^m))` degree by degree** (the input `hweil` of Step 9 of the proof of
[Stacks, Tag 03UG] for constant coefficients `ℤ/ℓ^m`): for an integral endomorphism `φ` of a smooth
proper curve `C` over an algebraically closed field `k`,

`∑_i (-1)^i Tr(φ^* | H^i(RΓ(C, ℤ/ℓ^m))) = 1 - Tr(φ^* | Pic(C)[ℓ^m]) + deg φ`. -/
theorem finsum_signedByDegree_derivedHomologyTrace_curveConstantCohomologyEndo [IsIntegralHom φ]
    (ℓ m : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k))
    (hH : HasFiniteProjectiveHomology.{0, u + 1} (ZMod (ℓ ^ m))
      (DerivedCategory.Plus.ι.obj (curveConstantCohomology f (ℓ ^ m)))) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ∑ᶠ i : ℤ, signedByDegree _ i (derivedHomologyTrace _ _ hH
        (DerivedCategory.Plus.ι.map (curveConstantCohomologyEndo f φ w (ℓ ^ m))) i) =
      additiveCommutatorQuotientMk _
        (1 - picardTorsionTrace C (Stacks.Picard.schemePullbackClassHom φ) ℓ m +
        (AlgebraicGeometry.CurveGraph.curveMapDegree f φ w : ZMod (ℓ ^ m))) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hn := isUnit_natCast_pow_of_isUnit hℓ m
  have hzero : ∀ i : ℤ, i ∉ ({0, 1, 2} : Finset ℤ) →
      derivedHomologyTrace _ _ hH
        (DerivedCategory.Plus.ι.map (curveConstantCohomologyEndo f φ w (ℓ ^ m))) i = 0 := by
    intro i hi
    rcases lt_or_ge i 0 with hneg | hnn
    · have := ModuleCat.subsingleton_of_isZero
        (isZero_homology_curveConstantCohomology_of_neg f (ℓ ^ m) i hneg)
      have : Module.Free (ZMod (ℓ ^ m)) ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) i).obj
          (DerivedCategory.Plus.ι.obj (curveConstantCohomology f (ℓ ^ m)))) :=
        Module.Free.of_subsingleton _ _
      have h0 : ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) i).map
          (DerivedCategory.Plus.ι.map (curveConstantCohomologyEndo f φ w (ℓ ^ m)))).hom = 0 :=
        Subsingleton.elim _ _
      unfold derivedHomologyTrace
      rw [projectiveModuleTrace_eq_additiveCommutatorQuotientMk_trace, h0, map_zero, map_zero]
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
      have hj : 3 ≤ j := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        lia
      obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
      have hn0 := ne_zero_of_isUnit_natCast hn
      have hs : Subsingleton (Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} C (ℓ ^ m)) j) :=
        subsingleton_sheafH_rootsOfUnitySheaf_of_isCurve f hn j hj
      have : Subsingleton (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod (ℓ ^ m))) j) :=
        (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 j).injective.subsingleton
      rw [derivedHomologyTrace_curveConstantCohomologyEndo f φ w ℓ m hℓ hH j,
        Subsingleton.elim
          ((etaleConstantCohomologyPullback φ (ZMod (ℓ ^ m)) j).toZModLinearMap _) 0,
        map_zero, map_zero]
  rw [finsum_eq_sum_of_support_subset _ (s := ({0, 1, 2} : Finset ℤ)) ?_]
  · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    have h0 := derivedHomologyTrace_curveConstantCohomologyEndo f φ w ℓ m hℓ hH 0
    have h1 := derivedHomologyTrace_curveConstantCohomologyEndo f φ w ℓ m hℓ hH 1
    have h2 := derivedHomologyTrace_curveConstantCohomologyEndo f φ w ℓ m hℓ hH 2
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h2
    rw [h0, h1, h2, trace_etaleConstantCohomologyPullback_zero f φ hn,
      trace_etaleConstantCohomologyPullback_one f φ w ℓ m hℓ,
      trace_etaleConstantCohomologyPullback_two f φ w hn]
    rw [signedByDegree, signedByDegree, signedByDegree, ite_eq_left Even.zero,
      ite_eq_right Int.not_even_one, ite_eq_left even_two, map_add, map_sub]
    abel
  · intro i hi
    by_contra h
    exact hi (by beta_reduce; rw [hzero i h]; simp [signedByDegree])

end Curve

end Stacks.EtaleCohomology
