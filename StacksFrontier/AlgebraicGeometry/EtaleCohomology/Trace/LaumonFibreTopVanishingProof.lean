module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonUniformInertiaProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreConjugationReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLinearCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementDegree
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaGeometric
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.FundamentalGroupTheorem

/-!
# Vanishing of `H²_c` on the fibres of the Fourier family

For `σ` as in `Stacks.EtaleCohomology.LaumonFibrePurityInput` and `ψ ≠ 1` there is `N` such that
for `n > N` prime to `p` and every fibre `τ = σ' ⊗ χ` of the Fourier family with `a ≠ 0`, the
groups `H²_c(𝔸¹_k̄', ℱ_τ ⊗ ℚ_ℓ)` and `H²_c(𝔸¹_k̄', ℱ_{τ^∨} ⊗ ℚ_ℓ)` vanish
(`Stacks.EtaleCohomology.LaumonFibreTopVanishingInput`). Along the way, the place at `∞` of
`k'(x)` is described by the local ring `k'[X]_(X)` through `X ↦ 1/x`.

## Main results

* `Polynomial.liftInvX_surjective`: `X ↦ 1/x` is onto `k'(x)`.
* `Polynomial.isFractionRing_localizationAtX_invX`: through `X ↦ 1/x`, `k'(x)` is the fraction
  field of `k'[X]_(X)`.
* `Polynomial.algebraMap_X_notMem_range_localizationAtX_invX`: `x` is not in the local ring at
  `∞`.
* `Stacks.EtaleCohomology.laumonFibreTopVanishingInput`: the statement
  `Stacks.EtaleCohomology.LaumonFibreTopVanishingInput` holds.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
* K. Kedlaya, *Fourier transforms and p-adic Weil II*, proof of Theorem 6.4
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Matrix Stacks.FundamentalGroup

universe u

namespace Polynomial

variable (k' : Type*) [Field k'] {K' : Type*} [Field K'] [Algebra k'[X] K']
  [IsFractionRing k'[X] K']

/-- **`X ↦ 1/x` is onto `k'(x)`.** -/
theorem liftInvX_surjective : Function.Surjective (liftInvX k' k' K') := by
  intro z
  let S := (liftInvX k' k' K').fieldRange
  have hpol : ∀ g : k'[X], algebraMap k'[X] K' g ∈ S := fun g ↦ by
    induction g using Polynomial.induction_on with
    | C a =>
      refine ⟨algebraMap k'[X] (FractionRing k'[X]) (C a), ?_⟩
      rw [liftInvX_algebraMap, evalInvX_C, Algebra.algebraMap_self, RingHom.id_apply]
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul]
      refine S.mul_mem h ⟨(algebraMap k'[X] (FractionRing k'[X]) X)⁻¹, ?_⟩
      rw [map_inv₀, liftInvX_algebraMap, evalInvX_X, inv_inv]
  obtain ⟨g, h, -, rfl⟩ := IsFractionRing.div_surjective (A := k'[X]) z
  exact S.div_mem (hpol g) (hpol h)

/-- The algebra structure of `k'[X]_(X)` on `k'(x)` through `X ↦ 1/x`: the local ring at `∞`. -/
abbrev algebraLocalizationAtXInvX : Algebra (LocalizationAtX k') K' :=
  ((liftInvX k' k' K').comp (algebraMap (LocalizationAtX k') (FractionRing k'[X]))).toAlgebra

/-- Through `X ↦ 1/x`, `k'(x)` is the fraction field of the local ring `k'[X]_(X)`. -/
theorem isFractionRing_localizationAtX_invX :
    letI := algebraLocalizationAtXInvX k' (K' := K')
    IsFractionRing (LocalizationAtX k') K' := by
  let := algebraLocalizationAtXInvX k' (K' := K')
  have := isFractionRing_localizationAtX k'
  let e : FractionRing k'[X] ≃+* K' := RingEquiv.ofBijective (liftInvX k' k' K')
    ⟨(liftInvX k' k' K').injective, liftInvX_surjective k'⟩
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (LocalizationAtX k'))
    (AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl)

/-- **`x` is not in the local ring at `∞`.** -/
theorem algebraMap_X_notMem_range_localizationAtX_invX :
    letI := algebraLocalizationAtXInvX k' (K' := K')
    algebraMap k'[X] K' X ∉ Set.range (algebraMap (LocalizationAtX k') K') := by
  let := algebraLocalizationAtXInvX k' (K' := K')
  have := isDiscreteValuationRing_localizationAtX k'
  have := isFractionRing_localizationAtX_invX k' (K' := K')
  rintro ⟨a, ha⟩
  have hπ : algebraMap (LocalizationAtX k') K' (algebraMap k'[X] (LocalizationAtX k') X) =
      (algebraMap k'[X] K' X)⁻¹ := by
    change liftInvX k' k' K' (algebraMap (LocalizationAtX k') (FractionRing k'[X])
      (algebraMap k'[X] (LocalizationAtX k') X)) = _
    rw [← IsScalarTower.algebraMap_apply, liftInvX_algebraMap, evalInvX_X]
  have h1 : algebraMap k'[X] (LocalizationAtX k') X * a = 1 := by
    apply IsFractionRing.injective (LocalizationAtX k') K'
    rw [map_mul, hπ, ha, map_one, inv_mul_cancel₀ (algebraMap_X_ne_zero k' K')]
  exact (irreducible_algebraMap_X_localizationAtX k').not_isUnit (isUnit_iff_exists_inv.2 ⟨a, h1⟩)

end Polynomial

namespace Stacks.EtaleCohomology

/-- The generic point of `Spec k'[X]`, followed by the structure map to `Spec k'`, is `Spec` of
the constants `k' → k'(x)`. -/
theorem fromSpecResidueField_genericPoint_comp_specMap_algebraMap (k' : Type u) [Field k'] :
    letI := specResidueFieldAlgebra (.of (Polynomial k'))
      (genericPoint (Spec (.of (Polynomial k'))))
    (Spec (.of (Polynomial k'))).fromSpecResidueField
        (genericPoint (Spec (.of (Polynomial k')))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))) =
      Spec.map (CommRingCat.ofHom ((algebraMap (Polynomial k')
        ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k')))))).comp Polynomial.C)) := by
  rw [fromSpecResidueField_eq_specMap, ← Spec.map_comp]
  rfl

/-- **Vanishing of `H²_c` on the fibres of the Fourier family**:
`Stacks.EtaleCohomology.LaumonFibreTopVanishingInput` holds. -/
theorem laumonFibreTopVanishingInput : LaumonFibreTopVanishingInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hζ ι' β _ hpure ψ hψ
  classical
  obtain ⟨N, hN⟩ := exists_mem_curvePointInertia_isUnit_restrictScalarsMatrix_sub_one ℓ k U.1 e p
    x E b σ hσ ψ hψ
  refine ⟨N, fun n₀ hn₀ hpn₀ ↦ ?_⟩
  intro k' _ _ _ hX' _ _ x' hx' a c hac p₀ hτ _ _ _ j' kbar' _ _ _ p' n' _ _ hcard'
  have : IrreducibleSpace (Spec (.of (Polynomial k'))) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (Polynomial k')))
  have := Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_polynomial k'
  have := Stacks.GenericFiniteEtale.connectedSpace_pullback_specMap_polynomial k' kbar'
  have : IsAlgClosed kbar' := IsAlgClosure.isAlgClosed k'
  have hℓ' : ℓ ≠ p' :=
    CharP.eq k' inferInstance ((Algebra.charP_iff k k' p).1 inferInstance) ▸ hℓp
  set K' := (Spec (.of (Polynomial k'))).residueField (genericPoint (Spec (.of (Polynomial k'))))
  let alg₁ : Algebra (Polynomial k') K' :=
    specResidueFieldAlgebra (.of (Polynomial k')) (genericPoint (Spec (.of (Polynomial k'))))
  have : IsFractionRing (Polynomial k') K' :=
    isFractionRing_specResidueField_genericPoint (.of (Polynomial k'))
  have : Algebra.IsAlgebraic K' (AlgebraicClosure (SeparableClosure K')) :=
    Algebra.IsAlgebraic.trans K' (SeparableClosure K') _
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso_of_connectedSpace (Spec (.of (Polynomial k')))
    x' ((algebraicClosureGeometricPoint K' (AlgebraicClosure (SeparableClosure K'))).map
      ((Spec (.of (Polynomial k'))).fromSpecResidueField
        (genericPoint (Spec (.of (Polynomial k'))))))
  let algA := Polynomial.algebraLocalizationAtXInvX k' (K' := K')
  have := Polynomial.isDiscreteValuationRing_localizationAtX k'
  have := Polynomial.isFractionRing_localizationAtX_invX k' (K' := K')
  let : Algebra (Polynomial.LocalizationAtX k') (SeparableClosure K') :=
    ((algebraMap K' (SeparableClosure K')).comp
      (algebraMap (Polynomial.LocalizationAtX k') K')).toAlgebra
  have : IsScalarTower (Polynomial.LocalizationAtX k') K' (SeparableClosure K') :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨P, hP⟩ := Ideal.exists_maximal
    (integralClosure (Polynomial.LocalizationAtX k') (SeparableClosure K'))
  have hA : ∃ g : Γ(Spec (.of (Polynomial k')), ⊤),
      ((Spec (.of (Polynomial k'))).evaluation ⊤ (genericPoint (Spec (.of (Polynomial k'))))
        trivial).hom g ∉ Set.range (algebraMap (Polynomial.LocalizationAtX k') K') :=
    ⟨(Scheme.ΓSpecIso (.of (Polynomial k'))).inv.hom Polynomial.X,
      Polynomial.algebraMap_X_notMem_range_localizationAtX_invX k'⟩
  obtain ⟨γ, hγ, hunit⟩ := hN n₀ hn₀ hpn₀ k' x' hx' a c (by simpa using hac) p₀
    (SeparableClosure K') (AlgebraicClosure (SeparableClosure K')) t
    (Polynomial.LocalizationAtX k') P hA
  let alg₃ : Algebra k' K' := ((algebraMap (Polynomial k') K').comp Polynomial.C).toAlgebra
  let : Algebra k' (SeparableClosure K') :=
    ((algebraMap K' (SeparableClosure K')).comp (algebraMap k' K')).toAlgebra
  have : IsScalarTower k' K' (SeparableClosure K') := IsScalarTower.of_algebraMap_eq' rfl
  let f' : Spec (.of (Polynomial k')) ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))
  let j₁ := (Spec (.of (Polynomial k'))).fromSpecResidueField
    (genericPoint (Spec (.of (Polynomial k'))))
  have hgeo : etaleFundamentalGroupBasePointHom t γ ∈
      (etaleFundamentalGroupMap f' x').toMonoidHom.ker := by
    obtain ⟨σL, hσL, rfl⟩ := Subgroup.mem_map.1 hγ
    have hind := ((isEtaleFundamentalGroupHomInducedBy_map j₁ (algebraicClosureGeometricPoint K'
      (AlgebraicClosure (SeparableClosure K')))).comp_baseChange
        (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t)).comp_baseChange
          (isEtaleFundamentalGroupHomInducedBy_map f' x')
    have hJ : (j₁ ≫ 𝟙 _) ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap k' K')) := by
      rw [Category.comp_id]
      exact fromSpecResidueField_genericPoint_comp_specMap_algebraMap k'
    rw [MonoidHom.mem_ker]
    apply Aut.ext
    ext V w
    exact (forall_apply_eq_of_forall_spec_comp_eq K' (SeparableClosure K')
      (AlgebraicClosure (SeparableClosure K')) _ hind V σL (fun g hg ↦
        spec_comp_eq_of_forall_isIntegral σL
          (fun _ hz ↦ inertia_apply_eq_of_isIntegral P σL hσL hz) V g
          (hg.trans (by rw [hJ]))) w).trans rfl
  obtain ⟨φ, hφ⟩ := exists_etaleFundamentalGroupMap_eq_finiteFieldFrobenius_inv p' n' hcard' f' x'
    kbar'
  refine ⟨?_, ?_⟩ <;>
  refine @Equiv.subsingleton _ _ (curveLinearCoinvariantsInput B
    (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') ℓ k' f' j' kbar' p' n' hcard' hℓ' x' E
    b _ ?_ φ hφ).choose.toEquiv
    (invariants_eq_bot_and_subsingleton_coinvariants_of_isUnit _ _ ⟨_, hgeo⟩
      (isUnit_sub_one_of_isUnit_restrictScalarsMatrix b ?_)).2
  · exact hτ
  · exact hunit
  · exact continuous_restrictScalarsRep_contragredient b hτ
  · exact isUnit_restrictScalarsMatrix_contragredient_sub_one b _ _ hunit

end Stacks.EtaleCohomology

end
