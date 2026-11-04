module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.TowerLevels

/-!
# The family layer recursion by strong induction

The family analogue of Tag 09F8's factor induction, the splittable level through a proper normal
intermediate family, and `familyTowerSolvable_all` by strong induction on the degree bound.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

universe u

section TowerFamily

open IsDiscreteValuationRing

/-- **The family analogue of Tag 09F8's factor induction: a solved bottom family, re-entered.**

Given the bottom layers `N i / K` already solved over **one** `K₁` by the packages `D₁`, this
decomposes each member's two compositum layers into conjugate factors, re-enters at the shared base
`integralClosure A K₁`, applies the induction hypothesis **once** to the combined factor family
indexed by `(i : ι) × Fin (mF i)` — so one `K₂` serves every factor of every member — and composes
with `isWeakSolution_of_iterated_packages`.

The bottom family `S` is a **parameter** rather than `integralClosure (B i) (N i)`, for the reason
Tag 09F8 keeps `B` abstract in its own `normal_factor_induction`: an integral closure is a
`Subalgebra`, so `SMul ↥S Z` has two instance paths — `Subalgebra.instSMulSubtypeMem` and
`Algebra.toSMul` — and a tower proved at one call site is then not the instance wanted at the
next. The towers below whose carrier is a subalgebra are therefore written `@IsScalarTower` with
the three `SMul`s given explicitly, which is what that file does in the same places. -/
theorem familyTowerSolvable_of_forall_factorFamily (p : ℕ) [Fact p.Prime]
    {n₂ : ℕ} (hnext : FamilyTowerSolvable.{u} p n₂)
    (ι : Type u) [Finite ι]
    (A K : Type u) (S C N M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (S i)] [∀ i, IsDomain (S i)] [∀ i, IsDiscreteValuationRing (S i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (N i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (S i)] [∀ i, Algebra (S i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (S i) (N i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (N i)] [∀ i, Algebra (N i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (N i)] [∀ i, Algebra (S i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (S i) (C i)] [∀ i, IsScalarTower A (S i) (N i)]
    [∀ i, IsScalarTower A K (N i)]
    [∀ i, IsScalarTower (S i) (C i) (M i)] [∀ i, IsScalarTower (S i) (N i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (N i) (M i)]
    [∀ i, IsExtension A (S i)] [∀ i, IsExtension (S i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (S i) (N i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP (IsLocalRing.ResidueField A) p] [∀ i, ExpChar (IsLocalRing.ResidueField (S i)) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (S i)) (S i)]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (C i)) (C i)]
    [∀ i, Module.Finite (N i) (M i)] [∀ i, Normal (N i) (M i)]
    (hepp : ∀ i, EppCondition A (S i) p)
    (hb₂ : ∀ i, Module.finrank (N i) (M i) ≤ n₂)
    (K₁ : Type u) [Field K₁] [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D₁ : ∀ i, IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (S i) K (N i) K₁)
    (hD₁ : ∀ i, (D₁ i).IsWeakSolution) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₂,
        D.IsWeakSolution := by
  classical
  -- (4) the top-layer packages over the same `K₁`, and the two factor families per member
  let D' : ∀ i, IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₁ :=
    fun i => canonicalBaseChange A (C i) K (M i) K₁
  have hfacH := fun i =>
    exists_finiteFieldFactors_of_package A (S i) K (N i) K₁ (D₁ i)
  choose nH H hH hNH hKH hSH hAH hSNH hASH hAKH hfinH hnH eH heH using hfacH
  let := hH
  let := hNH
  let := hKH
  let := hSH
  let := hAH
  let := hSNH
  let := hASH
  let := hAKH
  let := hfinH
  have hfacF := fun i => exists_finiteFieldFactors_of_package A (C i) K (M i) K₁ (D' i)
  choose mF F hF hMF hKF hCF hAF hCMF hACF hAKF hfinF hmF eF heF using hfacF
  let := hF
  let := hMF
  let := hKF
  let := hCF
  let := hAF
  let := hCMF
  let := hACF
  let := hAKF
  let := hfinF
  -- (5) the `K`-structures the factor-level statements are phrased over
  let algKH : ∀ i k, Algebra K (H i k) := fun i k =>
    ((algebraMap K₁ (H i k)).comp (algebraMap K K₁)).toAlgebra
  let algKF : ∀ i k, Algebra K (F i k) := fun i k =>
    ((algebraMap K₁ (F i k)).comp (algebraMap K K₁)).toAlgebra
  have : ∀ i k, IsScalarTower K K₁ (H i k) := fun _ _ => IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ i k, IsScalarTower K K₁ (F i k) := fun _ _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra K₁ (N i ⊗[K] K₁) := fun _ => Algebra.TensorProduct.rightAlgebra
  let : ∀ i, Algebra K₁ (M i ⊗[K] K₁) := fun _ => Algebra.TensorProduct.rightAlgebra
  let : ∀ i, Algebra K₁ (ReducedTensorTower.Reduction (N i ⊗[K] K₁)) := fun _ =>
    Ideal.Quotient.algebra K₁
  let : ∀ i, Algebra K₁ (ReducedTensorTower.Reduction (M i ⊗[K] K₁)) := fun _ =>
    Ideal.Quotient.algebra K₁
  -- the package carriers' own instance fields, at the family index
  let : ∀ i, CommRing (D₁ i).L₁ := fun i => (D₁ i).commRingL₁
  let : ∀ i, Algebra K (D₁ i).L₁ := fun i => (D₁ i).algebraKL₁
  let : ∀ i, Algebra (N i) (D₁ i).L₁ := fun i => (D₁ i).algebraLL₁
  let : ∀ i, Algebra K₁ (D₁ i).L₁ := fun i => (D₁ i).algebraK₁L₁
  let : ∀ i, CommRing (D' i).L₁ := fun i => (D' i).commRingL₁
  let : ∀ i, Algebra K (D' i).L₁ := fun i => (D' i).algebraKL₁
  let : ∀ i, Algebra (M i) (D' i).L₁ := fun i => (D' i).algebraLL₁
  let : ∀ i, Algebra K₁ (D' i).L₁ := fun i => (D' i).algebraK₁L₁
  let eH' := fun i => reducedTensorFactorsEquiv K (N i) K₁ (D₁ i).L₁ (H i)
    (D₁ i).eL₁ (eH i) (D₁ i).eL₁_right (heH i)
  let eF' := fun i => reducedTensorFactorsEquiv K (M i) K₁ (D' i).L₁ (F i)
    (D' i).eL₁ (eF i) (D' i).eL₁_right (heF i)
  -- (6) the upper layer `M i / N i`, and the projections onto its factors
  let φ : ∀ i k, (M i ⊗[K] K₁) →ₐ[K₁] F i k := fun i k =>
    ((Pi.evalAlgHom K₁ (F i) k).comp (eF' i).toAlgHom).comp (Ideal.Quotient.mkₐ K₁ _)
  have hφleft : ∀ i k (x : M i), φ i k (x ⊗ₜ[K] (1 : K₁)) = algebraMap (M i) (F i k) x :=
    fun i k x => reducedTensorFactorsEquiv_left K (M i) K₁ (D' i).L₁ (F i) (D' i).eL₁ (eF i)
      (D' i).eL₁_right (heF i) (D' i).eL₁_left x k
  have hφright : ∀ i k (x : K₁), φ i k ((1 : M i) ⊗ₜ[K] x) = algebraMap K₁ (F i k) x :=
    fun i k x => (φ i k).commutes x
  have hφ : ∀ i k (x : M i) (y : K₁),
      φ i k (x ⊗ₜ[K] y) = algebraMap (M i) (F i k) x * algebraMap K₁ (F i k) y := by
    intro i k x y
    rw [show x ⊗ₜ[K] y = (x ⊗ₜ[K] (1 : K₁)) * ((1 : M i) ⊗ₜ[K] y) by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
      map_mul, hφleft, hφright]
  have hφsurj : ∀ i k, Function.Surjective (φ i k) := by
    intro i k
    have hev : Function.Surjective (Pi.evalAlgHom K₁ (F i) k) := fun x =>
      ⟨Pi.single k x, by simp⟩
    exact hev.comp ((eF' i).surjective.comp Ideal.Quotient.mk_surjective)
  have : ∀ i k, IsScalarTower K (M i) (F i k) := fun i k =>
    IsScalarTower.of_algebraMap_eq fun x => by
      have ht : (algebraMap K (M i) x) ⊗ₜ[K] (1 : K₁) = (1 : M i) ⊗ₜ[K] algebraMap K K₁ x := by
        show (Algebra.TensorProduct.includeLeft : M i →ₐ[K] _) (algebraMap K (M i) x) =
          (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] _) (algebraMap K K₁ x)
        rw [AlgHom.commutes, AlgHom.commutes]
      have hx := congrArg (φ i k) ht
      rw [hφleft, hφright] at hx
      exact hx.symm
  let algNF : ∀ i k, Algebra (N i) (F i k) := fun i k =>
    ((algebraMap (M i) (F i k)).comp (algebraMap (N i) (M i))).toAlgebra
  have : ∀ i k, IsScalarTower (N i) (M i) (F i k) := fun _ _ =>
    IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ i k, IsScalarTower K (N i) (F i k) := fun i k =>
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K (M i) (F i k),
        IsScalarTower.algebraMap_apply K (N i) (M i)]
      rfl
  -- the bottom-layer ring's own route into the top factors
  let : ∀ i k, Algebra (S i) (F i k) := fun i k =>
    ((algebraMap (M i) (F i k)).comp (algebraMap (S i) (M i))).toAlgebra
  have : ∀ i k, IsScalarTower (S i) (M i) (F i k) := fun i k => by
    first
      | infer_instance
      | exact IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : ∀ i k, IsScalarTower (S i) (N i) (F i k) := fun i k => by
    first
      | infer_instance
      | exact IsScalarTower.of_algebraMap_eq fun _ => rfl
      | exact IsScalarTower.of_algebraMap_eq fun b => by
          rw [IsScalarTower.algebraMap_apply (S i) (M i) (F i k),
            IsScalarTower.algebraMap_apply (S i) (N i) (M i)]
          rfl
  have htSCF : ∀ i k, IsScalarTower (S i) (C i) (F i k) := fun i k => by
    first
      | infer_instance
      | exact IsScalarTower.of_algebraMap_eq fun b => by
          rw [IsScalarTower.algebraMap_apply (S i) (M i) (F i k),
            IsScalarTower.algebraMap_apply (S i) (C i) (M i),
            ← IsScalarTower.algebraMap_apply (C i) (M i) (F i k)]
  have : ∀ i k, IsScalarTower A (S i) (F i k) := fun i k => by
    first
      | infer_instance
      | exact IsScalarTower.of_algebraMap_eq fun a => by
          rw [IsScalarTower.algebraMap_apply A (C i) (F i k),
            IsScalarTower.algebraMap_apply A (S i) (C i),
            ← IsScalarTower.algebraMap_apply (S i) (C i) (F i k)]
  -- (7) each top factor sits over one bottom factor, normally and with the degree bound
  have hfac := fun i k =>
    exists_fieldFactor_normal_and_finrank_le K (N i) (M i) K₁ (F i k) (H i) (eH' i)
      (fun l x => reducedTensorFactorsEquiv_left K (N i) K₁ (D₁ i).L₁ (H i) (D₁ i).eL₁ (eH i)
        (D₁ i).eL₁_right (heH i) (D₁ i).eL₁_left x l) (φ i k) (hφ i k) (hφsurj i k)
  choose jj gg hNHF hfinHF hnormHF hboundHF using hfac
  let : ∀ i k, Algebra (H i (jj i k)) (F i k) := fun i k => (gg i k).toRingHom.toAlgebra
  let := hNHF
  let := hfinHF
  let := hnormHF
  have : ∀ i k, IsScalarTower K₁ (H i (jj i k)) (F i k) := fun i k =>
    IsScalarTower.of_algHom (gg i k)
  -- (8) the re-entry: the base `R = integralClosure A K₁` and the two rings at each factor
  let R := integralClosure A K₁
  obtain ⟨hRdvr, hRext, hRfin, hRc, hRf⟩ := integralClosure_isCompleteDVR A K K₁
  let := hRdvr
  let := hRext
  let := hRfin
  let := hRc
  let := hRf
  have hAintR : Algebra.IsIntegral A R :=
    (Subalgebra.isIntegral_iff _).mpr fun _ hx => hx
  have : PerfectField (IsLocalRing.ResidueField R) :=
    perfectField_residueField_of_finite A R
  have hcharR : CharP (IsLocalRing.ResidueField R) p :=
    charP_of_injective_algebraMap
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField R)).injective p
  have hSSdata := fun i k =>
    integralClosure_isCompleteDVR (S i) (N i) (H i (jj i k))
  choose hSSdvr hSSext hSSfin hSSc hSSf using hSSdata
  let := hSSdvr
  let := hSSext
  let := hSSfin
  let := hSSc
  let := hSSf
  have hTTdata := fun i k => integralClosure_isCompleteDVR (C i) (M i) (F i k)
  choose hTTdvr hTText hTTfin hTTc hTTf using hTTdata
  let := hTTdvr
  let := hTText
  let := hTTfin
  let := hTTc
  let := hTTf
  have htSHF : ∀ i k, IsScalarTower (S i) (H i (jj i k)) (F i k) :=
    fun i k => by
    first
      | infer_instance
      | exact IsScalarTower.of_algebraMap_eq fun b => by
          rw [IsScalarTower.algebraMap_apply (S i) (N i) (F i k),
            IsScalarTower.algebraMap_apply (N i) (H i (jj i k)) (F i k),
            ← IsScalarTower.algebraMap_apply (S i) (N i)
              (H i (jj i k))]
  -- the three integral-closure maps of the re-entered square
  let : ∀ i k, Algebra R
      (integralClosure (S i) (H i (jj i k))) := fun i k =>
    (mapIntegralClosureOfTower A (S i) K₁
      (H i (jj i k))).toRingHom.toAlgebra
  let : ∀ i k, Algebra R (integralClosure (C i) (F i k)) := fun i k =>
    (mapIntegralClosureOfTower A (C i) K₁ (F i k)).toRingHom.toAlgebra
  let : ∀ i k, Algebra (integralClosure (S i) (H i (jj i k)))
      (integralClosure (C i) (F i k)) := fun i k => by
    have := htSHF i k
    have := htSCF i k
    exact (@mapIntegralClosureOfTower (S i) (C i) (H i (jj i k))
      (F i k) _ _ _ _ _ _ _ _ _ (htSCF i k) (htSHF i k)).toRingHom.toAlgebra
  let : ∀ i k, Algebra R (H i (jj i k)) := fun i k =>
    ((algebraMap K₁ (H i (jj i k))).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i k, Algebra R (F i k) := fun i k =>
    ((algebraMap K₁ (F i k)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i k, Algebra (integralClosure (S i) (H i (jj i k))) (F i k) := fun i k =>
    ((algebraMap (H i (jj i k)) (F i k)).comp
      (algebraMap (integralClosure (S i) (H i (jj i k))) (H i (jj i k)))).toAlgebra
  let : ∀ i k, @IsScalarTower R K₁ (H i (jj i k))
      (inferInstance : Algebra R K₁).toSMul (inferInstance : Algebra K₁ (H i (jj i k))).toSMul
      (inferInstance : Algebra R (H i (jj i k))).toSMul := fun _ _ =>
    IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i k, @IsScalarTower R K₁ (F i k)
      (inferInstance : Algebra R K₁).toSMul (inferInstance : Algebra K₁ (F i k)).toSMul
      (inferInstance : Algebra R (F i k)).toSMul := fun _ _ =>
    IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i k, @IsScalarTower (integralClosure (S i) (H i (jj i k))) (H i (jj i k)) (F i k)
      (inferInstance : Algebra (integralClosure (S i) (H i (jj i k))) (H i (jj i k))).toSMul
      (inferInstance : Algebra (H i (jj i k)) (F i k)).toSMul
      (inferInstance : Algebra (integralClosure (S i) (H i (jj i k))) (F i k)).toSMul :=
    fun _ _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i k, @IsScalarTower R (integralClosure (S i) (H i (jj i k))) (H i (jj i k))
      (inferInstance : Algebra R (integralClosure (S i) (H i (jj i k)))).toSMul
      (inferInstance : Algebra (integralClosure (S i) (H i (jj i k))) (H i (jj i k))).toSMul
      (inferInstance : Algebra R (H i (jj i k))).toSMul :=
    fun _ _ => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ i k, @IsScalarTower (integralClosure (S i) (H i (jj i k)))
      (integralClosure (C i) (F i k)) (F i k)
      (inferInstance : Algebra (integralClosure (S i) (H i (jj i k)))
        (integralClosure (C i) (F i k))).toSMul
      (inferInstance : Algebra (integralClosure (C i) (F i k)) (F i k)).toSMul
      (inferInstance : Algebra (integralClosure (S i) (H i (jj i k))) (F i k)).toSMul :=
    fun _ _ => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ i k, @IsScalarTower R (integralClosure (C i) (F i k)) (F i k)
      (inferInstance : Algebra R (integralClosure (C i) (F i k))).toSMul
      (inferInstance : Algebra (integralClosure (C i) (F i k)) (F i k)).toSMul
      (inferInstance : Algebra R (F i k)).toSMul :=
    fun _ _ => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ i k, @IsScalarTower R (integralClosure (S i) (H i (jj i k)))
      (integralClosure (C i) (F i k))
      (inferInstance : Algebra R (integralClosure (S i) (H i (jj i k)))).toSMul
      (inferInstance : Algebra (integralClosure (S i) (H i (jj i k)))
        (integralClosure (C i) (F i k))).toSMul
      (inferInstance : Algebra R (integralClosure (C i) (F i k))).toSMul := fun i k =>
    IsScalarTower.of_algebraMap_eq fun a =>
      Subtype.ext (IsScalarTower.algebraMap_apply K₁ (H i (jj i k)) (F i k) a.1)
  have : ∀ i k, IsScalarTower A R
      (integralClosure (S i) (H i (jj i k))) := fun i k =>
    IsScalarTower.of_algebraMap_eq fun a =>
      ((mapIntegralClosureOfTower A (S i) K₁ (H i (jj i k))).commutes a).symm
  have : ∀ i k, IsExtension R (integralClosure (S i) (H i (jj i k))) :=
    fun i k => (integralClosure_factor_isExtension A (S i) K (N i) K₁
      (H i (jj i k))).choose_spec.choose_spec.1
  have : ∀ i k, IsExtension R (integralClosure (C i) (F i k)) :=
    fun i k => (integralClosure_factor_isExtension A (C i) K (M i) K₁
      (F i k)).choose_spec.choose_spec.1
  have : ∀ i k, IsExtension (integralClosure (S i) (H i (jj i k)))
      (integralClosure (C i) (F i k)) := fun i k =>
    (integralClosure_factor_isExtension (S i) (C i) (N i) (M i) (H i (jj i k))
      (F i k)).choose_spec.choose_spec.1
  have hexpR : ExpChar (IsLocalRing.ResidueField R) p := ExpChar.prime Fact.out
  have : ∀ i k, ExpChar (IsLocalRing.ResidueField (integralClosure (S i) (H i (jj i k)))) p := fun
    i k =>
    expChar_of_injective_algebraMap
      (algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (integralClosure (S i) (H i (jj i k))))).injective p
  have : ∀ i k, IsLocalHom (algebraMap A (integralClosure (S i) (H i (jj i k)))) :=
    fun i k => by
      rw [IsScalarTower.algebraMap_eq A (S i) (integralClosure (S i) (H i (jj i k)))]
      infer_instance
  have hweakRe : ∀ i k, IsWeaklyUnramified R
      (integralClosure (S i) (H i (jj i k))) := fun i k =>
    (isWeaklyUnramified_iff_ramificationIdx_eq_one _ _).mpr
      (isWeakSolution_factor A (S i) K (N i) K₁ (D₁ i) (H i) (eH i) (heH i) (hD₁ i) (jj i k)
        (IsLocalRing.maximalIdeal (integralClosure (S i) (H i (jj i k))))
        (IsLocalRing.maximalIdeal.isMaximal _))
  have heppRe : ∀ i k, EppCondition R
      (integralClosure (S i) (H i (jj i k))) p := fun i k =>
    EppCondition.of_finite_square (hepp i)
  -- (9) the induction hypothesis, once, at the combined factor family
  obtain ⟨K₂, hK₂, hK₁K₂, hRK₂, htowK₂, hfinK₂, hsol₂⟩ :=
    hnext ((i : ι) × Fin (mF i)) R K₁
      (fun x => integralClosure (S x.1) (H x.1 (jj x.1 x.2)))
      (fun x => integralClosure (C x.1) (F x.1 x.2))
      (fun x => H x.1 (jj x.1 x.2)) (fun x => F x.1 x.2)
      (fun x => hweakRe x.1 x.2) (fun x => heppRe x.1 x.2)
      (fun x => le_trans (hboundHF x.1 x.2) (hb₂ x.1))
  let := hK₂
  let := hK₁K₂
  let := hRK₂
  let := htowK₂
  let := hfinK₂
  choose D₂ hD₂ using hsol₂
  -- (10) the base-field data of `K₂ / K`, then the composition member by member
  let : Algebra K K₂ := ((algebraMap K₁ K₂).comp (algebraMap K K₁)).toAlgebra
  have : IsScalarTower K K₁ K₂ := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite K K₂ := Module.Finite.trans K₁ K₂
  let : Algebra A K₂ := ((algebraMap K K₂).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K K₂ := IsScalarTower.of_algebraMap_eq' rfl
  have htARK₁ : IsScalarTower A R K₁ := inferInstance
  have : IsScalarTower A K₁ K₂ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K K₂, IsScalarTower.algebraMap_apply K K₁ K₂,
      ← IsScalarTower.algebraMap_apply A K K₁]
  have hA : ∀ a : A, algebraMap A K₂ a = algebraMap R K₂ (algebraMap A R a) := fun a => by
    rw [IsScalarTower.algebraMap_apply R K₁ K₂, ← IsScalarTower.algebraMap_apply A R K₁,
      ← IsScalarTower.algebraMap_apply A K₁ K₂]
  refine ⟨K₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  refine ⟨canonicalBaseChange A (C i) K (M i) K₂, ?_⟩
  have hB : ∀ (k : Fin (mF i)) (b : C i),
      algebraMap (M i) (F i k) (algebraMap (C i) (M i) b) =
        algebraMap (integralClosure (C i) (F i k)) (F i k)
          (algebraMap (C i) (integralClosure (C i) (F i k)) b) := fun k b => by
    rw [← IsScalarTower.algebraMap_apply (C i) (M i) (F i k),
      ← IsScalarTower.algebraMap_apply (C i) (integralClosure (C i) (F i k)) (F i k)]
  have hsq : ∀ (k : Fin (mF i)) (a : A),
      algebraMap (C i) (integralClosure (C i) (F i k)) (algebraMap A (C i) a) =
        algebraMap R (integralClosure (C i) (F i k)) (algebraMap A R a) := fun k a => by
    apply Subtype.ext
    show algebraMap (C i) (F i k) (algebraMap A (C i) a) =
      algebraMap K₁ (F i k) (algebraMap A K₁ a)
    rw [← IsScalarTower.algebraMap_apply A (C i) (F i k),
      ← IsScalarTower.algebraMap_apply A K₁ (F i k)]
  exact isWeakSolution_of_iterated_packages A (C i) K (M i) K₁ K₂ R
    (canonicalBaseChange A (C i) K (M i) K₂) (F i) (fun k => integralClosure (C i) (F i k))
    hA hB hsq (fun k => D₂ ⟨i, k⟩) (fun k => hD₂ ⟨i, k⟩) (eF' i)
    (fun k x => reducedTensorFactorsEquiv_left K (M i) K₁ (D' i).L₁ (F i) (D' i).eL₁ (eF i)
      (D' i).eL₁_right (heF i) (D' i).eL₁_left x k)

/-- **`FamilyTowerSolvable` with the degree bound weakened to a three-way alternative.**

Identical to `FamilyTowerSolvable` except that the hypothesis `Module.finrank (L i) (M i) ≤ n` is
replaced by: each member is **carried** (`IsWeaklyUnramified A (C i)`), or **terminal** in the
sense `FamilyPrimeDegreeSolvable` consumes, or of degree at most `n`.

This is what makes the recursion on `n` go through, and the reason is a measure obstruction that
the plain statement cannot avoid. A level of the recursion meets a mixed family, and a terminal
member of degree exactly `n` has no split with both parts below `n`: `N i = ⊥` forces the upper
bound to `n`, `N i = ⊤` forces the lower bound to `n`, and a proper normal intermediate field need
not exist. With the alternative above, a degree-`n` terminal member is admitted by its *terminal*
disjunct rather than by a degree bound, so `FamilyTowerSolvableAux p (n - 1)` already solves the
bottom family of a level whose members have degree up to `n` — and the step needs one extension,
not two.

`FamilyTowerSolvable p n` is the special case where every member takes the third disjunct, so this
is a strengthening and not a different statement. -/
abbrev FamilyTowerSolvableAux (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∀ (ι : Type u) [Finite ι]
    (A K : Type u) (B C L M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP (IsLocalRing.ResidueField A) p] [∀ i, ExpChar (IsLocalRing.ResidueField (B i)) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (_hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)] [∀ i, Normal (L i) (M i)]
    (_hepp : ∀ i, EppCondition A (B i) p)
    (_halt : ∀ i, IsWeaklyUnramified A (C i) ∨
      (IsPurelyInseparable (L i) (M i) ∧ Module.finrank (L i) (M i) = p ∨
        IsGalois (L i) (M i) ∧ (Module.finrank (L i) (M i)).Prime) ∨
      Module.finrank (L i) (M i) ≤ n),
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₂,
        D.IsWeakSolution

/-- **The splittable level of the family recursion: a proper normal intermediate family.**

Each member's extension `M i / L i` is split at a normal intermediate field, presented here as an
abstract family `N` so that no carrier is a coercion; the strong induction supplies
`N i := ↥(E i)`. The bottom family is solved by `hfirst` at `n₁`, giving one `K₁`; the upper
factor family is solved by `hnext` at `n₂`, giving one `K₂ ⊇ K₁`; and the two compose. The single
existential sits outside `∀ i` at both levels, so no member's extension is ever combined with
another's. -/
theorem familyTowerSolvable_of_forall_properNormal (p : ℕ) [Fact p.Prime]
    {n₁ n₂ : ℕ}
    (hfirst : FamilyTowerSolvableAux.{u} p n₁) (hnext : FamilyTowerSolvable.{u} p n₂)
    (ι : Type u) [Finite ι]
    (A K : Type u) (B C L M N : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP (IsLocalRing.ResidueField A) p] [∀ i, ExpChar (IsLocalRing.ResidueField (B i)) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)] [∀ i, Normal (L i) (M i)]
    (hepp : ∀ i, EppCondition A (B i) p)
    -- the proper normal intermediate family, presented abstractly
    [∀ i, Field (N i)]
    [∀ i, Algebra (L i) (N i)] [∀ i, Algebra (N i) (M i)]
    [∀ i, Algebra K (N i)] [∀ i, Algebra (B i) (N i)] [∀ i, Algebra A (N i)]
    [∀ i, IsScalarTower K (L i) (N i)] [∀ i, IsScalarTower (B i) (L i) (N i)]
    [∀ i, IsScalarTower A (L i) (N i)] [∀ i, IsScalarTower A K (N i)]
    [∀ i, IsScalarTower A (B i) (N i)]
    [∀ i, IsScalarTower (L i) (N i) (M i)] [∀ i, IsScalarTower K (N i) (M i)]
    [∀ i, IsScalarTower (B i) (N i) (M i)] [∀ i, IsScalarTower A (N i) (M i)]
    [∀ i, Module.Finite (L i) (N i)] [∀ i, Normal (L i) (N i)]
    (hb₁ : ∀ i, IsWeaklyUnramified A (C i) ∨
      (IsPurelyInseparable (L i) (N i) ∧ Module.finrank (L i) (N i) = p ∨
        IsGalois (L i) (N i) ∧ (Module.finrank (L i) (N i)).Prime) ∨
      Module.finrank (L i) (N i) ≤ n₁)
    (hb₂ : ∀ i, Module.finrank (N i) (M i) ≤ n₂) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₂,
        D.IsWeakSolution := by
  classical
  -- (1) the bottom-layer ring and its five facts
  have hdvr : ∀ i, IsDiscreteValuationRing (integralClosure (B i) (N i)) := fun i =>
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete (B i) (L i) (N i)).1
  have hfinBR : ∀ i, Module.Finite (B i) (integralClosure (B i) (N i)) := fun i =>
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete (B i) (L i) (N i)).2
  have hffBR : ∀ i, FaithfulSMul (B i) (integralClosure (B i) (N i)) := fun i =>
    (faithfulSMul_iff_algebraMap_injective (B i) _).mpr (fun x y h => by
      apply IsFractionRing.injective (B i) (L i)
      apply (algebraMap (L i) (N i)).injective
      simpa only [← IsScalarTower.algebraMap_apply (B i) (L i) (N i),
        Subalgebra.coe_algebraMap] using congrArg Subtype.val h)
  have hlocBR : ∀ i, IsLocalHom (algebraMap (B i) (integralClosure (B i) (N i))) := fun i =>
    Algebra.IsIntegral.isLocalHom (B i) _
  have hextBR : ∀ i, IsExtension (B i) (integralClosure (B i) (N i)) := fun i => ⟨⟩
  have hcompR : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure (B i) (N i)))
      (integralClosure (B i) (N i)) := fun i => isAdicComplete_of_finite (B i) _
  have hfracR : ∀ i, IsFractionRing (integralClosure (B i) (N i)) (N i) := fun i =>
    IsIntegralClosure.isFractionRing_of_finite_extension (B i) (L i) (N i) _
  -- (2) the `A`-side of the bottom ring
  let : ∀ i, Algebra A (integralClosure (B i) (N i)) := fun i =>
    ((algebraMap (B i) (integralClosure (B i) (N i))).comp (algebraMap A (B i))).toAlgebra
  have : ∀ i, IsScalarTower A (B i) (integralClosure (B i) (N i)) := fun i =>
    IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ i, IsLocalHom (algebraMap A (integralClosure (B i) (N i))) := fun i =>
    RingHom.isLocalHom_comp (algebraMap (B i) (integralClosure (B i) (N i)))
      (algebraMap A (B i))
  have : ∀ i, FaithfulSMul A (integralClosure (B i) (N i)) := fun i =>
    (faithfulSMul_iff_algebraMap_injective A _).mpr
      ((FaithfulSMul.algebraMap_injective (B i) (integralClosure (B i) (N i))).comp
        (FaithfulSMul.algebraMap_injective A (B i)))
  have : ∀ i, IsExtension A (integralClosure (B i) (N i)) := fun i => ⟨⟩
  have : ∀ i, IsScalarTower A (integralClosure (B i) (N i)) (N i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A (B i) (integralClosure (B i) (N i)),
        ← IsScalarTower.algebraMap_apply (B i) (integralClosure (B i) (N i)) (N i),
        ← IsScalarTower.algebraMap_apply A (B i) (N i)]
  -- (2b) the top ring `C i` is module-finite and complete, and sits over the bottom-layer ring
  have : ∀ i, IsScalarTower A (B i) (M i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A (C i) (M i),
        IsScalarTower.algebraMap_apply A (B i) (C i),
        ← IsScalarTower.algebraMap_apply (B i) (C i) (M i)]
  have : ∀ i, IsIntegralClosure (C i) (B i) (M i) := fun i =>
    isIntegralClosure_of_isAdicComplete (B i) (C i) (L i) (M i)
  have : ∀ i, Module.Finite (B i) (integralClosure (B i) (M i)) := fun i =>
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete (B i) (L i) (M i)).2
  have : ∀ i, Module.Finite (B i) (C i) := fun i => Module.Finite.equiv
    (IsIntegralClosure.equiv (B i) (integralClosure (B i) (M i)) (M i) (C i)).toLinearEquiv
  have : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (C i)) (C i) := fun i =>
    isAdicComplete_of_finite (B i) (C i)
  have : ∀ i, IsScalarTower (integralClosure (B i) (N i)) (N i) (M i) := fun _ => inferInstance
  have : ∀ i, IsScalarTower (B i) (integralClosure (B i) (N i)) (M i) := fun _ => inferInstance
  let fSC : ∀ i, integralClosure (B i) (N i) →ₐ[B i] C i := fun i =>
    IsIntegralClosure.lift (B i) (C i) (M i)
  let : ∀ i, Algebra (integralClosure (B i) (N i)) (C i) := fun i =>
    (fSC i).toRingHom.toAlgebra
  have : ∀ i, IsScalarTower (B i) (integralClosure (B i) (N i)) (C i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun b => ((fSC i).commutes b).symm
  have : ∀ i, IsScalarTower (integralClosure (B i) (N i)) (C i) (M i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun s =>
      (IsIntegralClosure.algebraMap_lift (B i) (C i) (M i) s).symm
  have : ∀ i, IsScalarTower A (integralClosure (B i) (N i)) (C i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A (B i) (C i),
        IsScalarTower.algebraMap_apply (B i) (integralClosure (B i) (N i)) (C i)]
      rfl
  have : ∀ i, FaithfulSMul (integralClosure (B i) (N i)) (C i) := fun i =>
    (faithfulSMul_iff_algebraMap_injective _ (C i)).mpr fun x y h => by
      apply IsFractionRing.injective (integralClosure (B i) (N i)) (N i)
      apply (algebraMap (N i) (M i)).injective
      have h' := congrArg (algebraMap (C i) (M i)) h
      rw [← IsScalarTower.algebraMap_apply (integralClosure (B i) (N i)) (C i) (M i),
        ← IsScalarTower.algebraMap_apply (integralClosure (B i) (N i)) (C i) (M i)] at h'
      exact h'
  have : ∀ i, Algebra.IsIntegral (integralClosure (B i) (N i)) (C i) := fun i =>
    Algebra.IsIntegral.tower_top (R := B i)
  have : ∀ i, IsLocalHom (algebraMap (integralClosure (B i) (N i)) (C i)) := fun i =>
    Algebra.IsIntegral.isLocalHom (integralClosure (B i) (N i)) (C i)
  have : ∀ i, IsExtension (integralClosure (B i) (N i)) (C i) := fun i => ⟨⟩
  -- (3) the induction hypothesis at the bottom family: ONE `K₁` for the whole family
  obtain ⟨K₁, hK₁, hKK₁, hAK₁, htowK₁, hfinK₁, hsol₁⟩ :=
    hfirst ι A K B (fun i => integralClosure (B i) (N i)) L N hweak hepp
      (fun i => (hb₁ i).imp
        (fun h => IsDiscreteValuationRing.isWeaklyUnramified_tower_bot A
          (integralClosure (B i) (N i)) (C i) h)
        id)
  let := hK₁
  let := hKK₁
  let := hAK₁
  let := htowK₁
  let := hfinK₁
  choose D₁ hD₁ using hsol₁
  have : ∀ i, Module.Finite (N i) (M i) := fun i =>
    Module.Finite.of_restrictScalars_finite (L i) (N i) (M i)
  have : ∀ i, Normal (N i) (M i) := fun i => Normal.tower_top_of_normal (L i) (N i) (M i)
  have : ∀ i, ExpChar (IsLocalRing.ResidueField (integralClosure (B i) (N i))) p := fun i =>
    expChar_of_injective_algebraMap
      (algebraMap (IsLocalRing.ResidueField (B i))
        (IsLocalRing.ResidueField (integralClosure (B i) (N i)))).injective p
  exact familyTowerSolvable_of_forall_factorFamily p hnext ι A K
    (fun i => integralClosure (B i) (N i)) C N M
    (fun i => EppCondition.of_module_finite (hepp i)) hb₂ K₁ D₁ hD₁

/-- The auxiliary family statement contains the ordinary degree-bounded statement. -/
theorem familyTowerSolvable_of_aux (p : ℕ) [Fact p.Prime] {n : ℕ}
    (h : FamilyTowerSolvableAux.{u} p n) : FamilyTowerSolvable.{u} p n := by
  intro ι _ A K B C L M
  intros
  rename_i hweak _ _ hepp hdegree
  exact h ι A K B C L M hweak hepp fun i => Or.inr (Or.inr (hdegree i))

/-- The synchronized family recursion, by strong induction on the common degree bound. -/
theorem familyTowerSolvableAux_all (p : ℕ) [Fact p.Prime]
    (hprime : FamilyPrimeDegreeSolvable.{u} p) :
    ∀ n, FamilyTowerSolvableAux.{u} p n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ι _ A K B C L M
    intros
    rename_i hweak _ _ hepp halt
    by_cases hn : n ≤ 1
    · apply familyTowerSolvable_of_forall_terminal_or_isWeaklyUnramified
        p hprime ι A K B C L M hweak hepp
      intro i
      rcases halt i with hcarried | hterminal | hdegree
      · exact Or.inl hcarried
      · exact Or.inr hterminal
      · left
        exact isWeaklyUnramified_of_finrank_eq_one A (B i) (C i) K (L i) (M i)
          (hweak i) (le_antisymm (hdegree.trans hn) Module.finrank_pos)
    · have hn2 : 2 ≤ n := by omega
      have hsplit : ∀ i, ∃ E : IntermediateField (L i) (M i),
          Normal (L i) E ∧
          (IsWeaklyUnramified A (C i) ∨
            (IsPurelyInseparable (L i) E ∧ Module.finrank (L i) E = p ∨
              IsGalois (L i) E ∧ (Module.finrank (L i) E).Prime) ∨
            Module.finrank (L i) E ≤ n - 1) ∧
          Module.finrank E (M i) ≤ n - 1 := by
        intro i
        have htopNormal : Normal (L i) (↥(⊤ : IntermediateField (L i) (M i))) :=
          Normal.of_algEquiv (IntermediateField.topEquiv.symm)
        have htopDegree : Module.finrank (↥(⊤ : IntermediateField (L i) (M i))) (M i) ≤
            n - 1 := by
          have htop : Module.finrank (↥(⊤ : IntermediateField (L i) (M i))) (M i) = 1 :=
            IntermediateField.finrank_eq_one_iff_eq_top.mpr rfl
          omega
        have hcT : (IsWeaklyUnramified A (C i) ∨
            (IsPurelyInseparable (L i) (M i) ∧ Module.finrank (L i) (M i) = p ∨
              IsGalois (L i) (M i) ∧ (Module.finrank (L i) (M i)).Prime)) →
            ∃ E : IntermediateField (L i) (M i),
              Normal (L i) E ∧
              (IsWeaklyUnramified A (C i) ∨
                (IsPurelyInseparable (L i) E ∧ Module.finrank (L i) E = p ∨
                  IsGalois (L i) E ∧ (Module.finrank (L i) E).Prime) ∨
                Module.finrank (L i) E ≤ n - 1) ∧
              Module.finrank E (M i) ≤ n - 1 := by
          rintro (hcarried | ⟨⟨hpi, hp⟩ | ⟨hgal, hp⟩⟩)
          · exact ⟨⊤, htopNormal, Or.inl hcarried, htopDegree⟩
          · let := hpi
            exact ⟨⊤, htopNormal, Or.inr (Or.inl (Or.inl ⟨(IntermediateField.topEquiv
              (F := L i) (E := M i)).symm.isPurelyInseparable,
              by simpa only [IntermediateField.finrank_top'] using hp⟩)), htopDegree⟩
          · let := hgal
            exact ⟨⊤, htopNormal, Or.inr (Or.inl (Or.inr ⟨IsGalois.of_algEquiv
              (IntermediateField.topEquiv (F := L i) (E := M i)).symm,
              by simpa only [IntermediateField.finrank_top'] using hp⟩)), htopDegree⟩
        rcases halt i with hcarried | hterminal | hdegree
        · exact hcT (Or.inl hcarried)
        · exact hcT (Or.inr hterminal)
        · rcases isWeaklyUnramified_or_terminal_or_exists_properNormal
              p A (B i) (C i) K (L i) (M i) (hweak i) with
            hcarried | hterminal | ⟨E, hnormal, hleft, hright⟩
          · exact hcT (Or.inl hcarried)
          · exact hcT (Or.inr hterminal)
          · let := hnormal
            have hmul := Module.finrank_mul_finrank (L i) E (M i)
            have hleft' : Module.finrank (L i) E ≤ n - 1 := by
              have : Module.finrank (L i) E < n := by nlinarith
              omega
            have hright' : Module.finrank E (M i) ≤ n - 1 := by
              have : Module.finrank E (M i) < n := by nlinarith
              omega
            exact ⟨E, hnormal, Or.inr (Or.inr hleft'), hright'⟩
      choose E hnormal hbottom htop using hsplit
      let : ∀ i, Algebra K (E i) := fun i =>
        ((algebraMap (L i) (E i)).comp (algebraMap K (L i))).toAlgebra
      let : ∀ i, Algebra (B i) (E i) := fun i =>
        ((algebraMap (L i) (E i)).comp (algebraMap (B i) (L i))).toAlgebra
      let : ∀ i, Algebra A (E i) := fun i =>
        ((algebraMap (L i) (E i)).comp (algebraMap A (L i))).toAlgebra
      have : ∀ i, IsScalarTower K (L i) (E i) := fun _ =>
        IsScalarTower.of_algebraMap_eq' rfl
      have : ∀ i, IsScalarTower (B i) (L i) (E i) := fun _ =>
        IsScalarTower.of_algebraMap_eq' rfl
      have : ∀ i, IsScalarTower A (L i) (E i) := fun _ =>
        IsScalarTower.of_algebraMap_eq' rfl
      have : ∀ i, IsScalarTower A K (E i) := fun i =>
        IsScalarTower.of_algebraMap_eq fun a => by
          show algebraMap (L i) (E i) (algebraMap A (L i) a) =
            algebraMap (L i) (E i) (algebraMap K (L i) (algebraMap A K a))
          rw [← IsScalarTower.algebraMap_apply A K (L i)]
      have : ∀ i, IsScalarTower A (B i) (E i) := fun i =>
        IsScalarTower.of_algebraMap_eq fun a => by
          show algebraMap (L i) (E i) (algebraMap A (L i) a) =
            algebraMap (L i) (E i) (algebraMap (B i) (L i) (algebraMap A (B i) a))
          rw [← IsScalarTower.algebraMap_apply A (B i) (L i)]
      have : ∀ i, IsScalarTower K (E i) (M i) := fun i =>
        IsScalarTower.of_algebraMap_eq fun k => by
          rw [IsScalarTower.algebraMap_apply K (L i) (M i),
            IsScalarTower.algebraMap_apply (L i) (E i) (M i)]
          rfl
      have : ∀ i, IsScalarTower (B i) (E i) (M i) := fun i =>
        IsScalarTower.of_algebraMap_eq fun b => by
          rw [IsScalarTower.algebraMap_apply (B i) (L i) (M i),
            IsScalarTower.algebraMap_apply (L i) (E i) (M i)]
          rfl
      have : ∀ i, IsScalarTower A (E i) (M i) := fun i =>
        IsScalarTower.of_algebraMap_eq fun a => by
          show algebraMap A (M i) a =
            algebraMap (L i) (M i) (algebraMap A (L i) a)
          calc
            _ = algebraMap K (M i) (algebraMap A K a) :=
              IsScalarTower.algebraMap_apply A K (M i) a
            _ = algebraMap (L i) (M i) (algebraMap K (L i) (algebraMap A K a)) :=
              IsScalarTower.algebraMap_apply K (L i) (M i) _
            _ = _ := congrArg (algebraMap (L i) (M i))
              (IsScalarTower.algebraMap_apply A K (L i) a).symm
      let : ∀ i, Normal (L i) (E i) := hnormal
      exact familyTowerSolvable_of_forall_properNormal p
        (ih (n - 1) (by omega))
        (familyTowerSolvable_of_aux p (ih (n - 1) (by omega)))
        ι A K B C L M (fun i => ↥(E i)) hweak hepp hbottom htop

/-- Every finite normal family is synchronously solvable once the prime-degree family case is. -/
theorem familyTowerSolvable_all (p : ℕ) [Fact p.Prime]
    (hprime : FamilyPrimeDegreeSolvable.{u} p) :
    ∀ n, FamilyTowerSolvable.{u} p n := fun n =>
  familyTowerSolvable_of_aux p (familyTowerSolvableAux_all p hprime n)

end TowerFamily

end Stacks.EppTheorem

end
