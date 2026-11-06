module

public import StacksFrontier.RingTheory.DiscreteValuationRing.SeparableSolution.LocalFormalSmoothness

/-!
# Removing a purely inseparable step from a solution

Tag 0GLV: the purely inseparable degree-`p` step of a solution is replaced by a separable
extension; Tag 0BRN: iterating it, a solution yields a separable solution.
-/

@[expose] public section

namespace IsDiscreteValuationRing

open Polynomial IntermediateField
open scoped TensorProduct

universe uA uB uK uL uK₁ uK₂

/-- The image of a nonzero element under a torsion-free algebra is a non-zero-divisor. -/
private theorem algebraMap_mem_nonZeroDivisors_of_ne_zero {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Module.IsTorsionFree R S] {x : R} (hx : x ≠ 0) :
    algebraMap R S x ∈ nonZeroDivisors S :=
  algebraMap_mem_nonZeroDivisors_of_isTorsionFree (mem_nonZeroDivisors_iff_ne_zero.mpr hx)

/-- If `S` is integral over a local ring `R`, an element of the maximal ideal of `R` maps into
every maximal ideal of `S`. -/
private theorem algebraMap_mem_of_mem_maximalIdeal_of_isIntegral (R S : Type*) [CommRing R]
    [IsLocalRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (q : Ideal S) [q.IsMaximal] :
    algebraMap R S x ∈ q := by
  have hjac := map_maximalIdeal_le_jacobson_of_isIntegral R S (Ideal.mem_map_of_mem _ hx)
  simpa only [Ideal.jacobson_eq_self_of_isMaximal] using
    (Ideal.jacobson_mono (bot_le : (⊥ : Ideal S) ≤ q)) hjac

set_option maxHeartbeats 4000000 in
-- This long proof elaborates past the default `maxHeartbeats` limit.
/-- Let `A → B` be an extension of discrete valuation rings with separable fraction-field
extension `L/K`, where `K` has prime characteristic `p`, and suppose that `B` is Nagata. If
`K → K₁ → K₂` is a tower of finite extensions, `K₂` is a solution for `A → B`, and
`K₂/K₁` is purely inseparable of degree `p`, then some separable extension `K₃/K₁`
is a solution for `A → B`. -/
@[stacks 0GLV]
theorem exists_isSeparable_solution_of_isPurelyInseparable_finrank_eq_prime
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    (K₁ : Type uK₁) (K₂ : Type uK₂)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra K₁ K₂] [Algebra K K₂]
    [Algebra A K₁] [Algebra A K₂]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower A K K₁] [IsScalarTower A K K₂]
    [IsScalarTower K K₁ K₂] [IsScalarTower A K₁ K₂]
    [IsExtension A B]
    [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K K₁] [Module.Finite K₁ K₂]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (hsep : Algebra.IsSeparableExtension K L)
    (hB : IsNagataRing B)
    (hsolution :
      letI : Module.Finite K K₂ := Module.Finite.trans K₁ K₂
      ∃ D₂ : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₂,
          max uL uK₂, uK₂, max uL uK₂} A B K L K₂,
        D₂.IsSolution.{uA, uB, uK, uL, uK₂, max uL uK₂, uK₂, max uL uK₂,
          max uL uK₂})
    (hpi : IsPurelyInseparable K₁ K₂)
    (hdegree : Module.finrank K₁ K₂ = p) :
    ∃ (K₃ : Type uK₁) (_ : Field K₃) (_ : Algebra K₁ K₃) (_ : Algebra K K₃)
      (_ : Algebra A K₃) (_ : IsScalarTower K K₁ K₃) (_ : IsScalarTower A K K₃)
      (_ : IsScalarTower A K₁ K₃) (_ : Module.Finite K K₃),
      Algebra.IsSeparable K₁ K₃ ∧
        ∃ D₃ : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁,
            max uL uK₁, uK₁, max uL uK₁} A B K L K₃,
          D₃.IsSolution.{uA, uB, uK, uL, uK₁, max uL uK₁, uK₁, max uL uK₁,
            max uL uK₁} := by
  classical
  let : Module.Finite K K₂ := Module.Finite.trans K₁ K₂
  obtain ⟨D₂, hD₂⟩ := hsolution
  let D₁ := integralClosureBaseChange A B K L K₁
  let := D₁.commRingL₁
  let := D₁.commRingA₁
  let := D₁.commRingB₁
  let := D₁.algebraKL₁
  let := D₁.algebraLL₁
  let := D₁.algebraK₁L₁
  let := D₁.algebraBL₁
  let := D₁.algebraAA₁
  let := D₁.algebraA₁K₁
  let := D₁.algebraBB₁
  let := D₁.algebraB₁L₁
  let := D₁.algebraAB₁
  let := D₁.algebraA₁B₁
  let := D₁.isScalarTowerKLL₁
  let := D₁.isScalarTowerKK₁L₁
  let := D₁.isScalarTowerBLL₁
  let := D₁.isScalarTowerAA₁K₁
  let := D₁.isScalarTowerBB₁L₁
  let := D₁.isScalarTowerABB₁
  let := D₁.isScalarTowerAA₁B₁
  let := D₁.isIntegralClosureA₁
  let := D₁.isIntegralClosureB₁
  let := D₂.commRingL₁
  let := D₂.commRingA₁
  let := D₂.commRingB₁
  let := D₂.algebraKL₁
  let := D₂.algebraLL₁
  let := D₂.algebraK₁L₁
  let := D₂.algebraBL₁
  let := D₂.algebraAA₁
  let := D₂.algebraA₁K₁
  let := D₂.algebraBB₁
  let := D₂.algebraB₁L₁
  let := D₂.algebraAB₁
  let := D₂.algebraA₁B₁
  let := D₂.isScalarTowerKLL₁
  let := D₂.isScalarTowerKK₁L₁
  let := D₂.isScalarTowerBLL₁
  let := D₂.isScalarTowerAA₁K₁
  let := D₂.isScalarTowerBB₁L₁
  let := D₂.isScalarTowerABB₁
  let := D₂.isScalarTowerAA₁B₁
  let := D₂.isIntegralClosureA₁
  let := D₂.isIntegralClosureB₁
  have hfinA₁ : Module.Finite A D₁.A₁ := integralClosureBaseChange_finite_left A B K L K₁ D₁ hsep hB
  have hfinB₁ : Module.Finite B D₁.B₁ := integralClosureBaseChange_finite_right A B K L K₁ D₁ hB
  have hfinA₂ : Module.Finite A D₂.A₁ := integralClosureBaseChange_finite_left A B K L K₂ D₂ hsep hB
  have hfinB₂ : Module.Finite B D₂.B₁ := integralClosureBaseChange_finite_right A B K L K₂ D₂ hB
  obtain ⟨hDedA₂, hProdB₂, _, _, hPIRA₂, hPIRB₂⟩ :=
    integralClosureBaseChange_isPrincipalIdealRing_of_finite
    A B K L K₂ D₂ hfinA₂ hfinB₂
  obtain ⟨c, a₂, b₂, hcoeffA, hcoeffB, hiA, hiB, hfinA, hfinB, hcomm, hlocA, hlocB⟩ :=
    exists_compatible_adjoinRoot_orders A B K L K₁ K₂ D₁ D₂ p hp hsep hB hpi hdegree
  let P : D₁.A₁[X] := X ^ p - C c
  let φ : D₁.A₁ →+* D₁.B₁ := algebraMap D₁.A₁ D₁.B₁
  let := a₂.toAlgebra
  let := b₂.toAlgebra
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπB : algebraMap A B π ≠ 0 := by
    intro h
    exact hπ.ne_zero (FaithfulSMul.algebraMap_injective A B (by simpa using h))
  have hπBu : ¬ IsUnit (algebraMap A B π) := fun h =>
    hπ.not_isUnit (isUnit_of_map_unit (algebraMap A B) π h)
  have hlocK : IsLocalization.Away (π ^ 2) K :=
    isLocalization_away_of_ne_zero_of_not_isUnit A K (pow_ne_zero 2 hπ.ne_zero)
      (fun h => hπ.not_isUnit ((isUnit_pow_iff (by decide : 2 ≠ 0)).mp h))
  have hlocL : IsLocalization.Away (algebraMap A B (π ^ 2)) L := by
    rw [map_pow]
    exact isLocalization_away_of_ne_zero_of_not_isUnit B L (pow_ne_zero 2 hπB)
      (fun h => hπBu ((isUnit_pow_iff (by decide : 2 ≠ 0)).mp h))
  have : Nontrivial D₁.A₁ := (algebraMap D₁.A₁ K₁).domain_nontrivial
  have : Module.IsTorsionFree A K₁ := Module.IsTorsionFree.trans K
  have : Module.IsTorsionFree A K₂ := Module.IsTorsionFree.trans K
  have : Module.IsTorsionFree B D₁.L₁ := Module.IsTorsionFree.trans L
  have : Module.IsTorsionFree B D₂.L₁ := Module.IsTorsionFree.trans L
  have : Module.IsTorsionFree A D₁.A₁ := IsIntegralClosure.isTorsionFree A K₁
  have : Module.IsTorsionFree A D₂.A₁ := IsIntegralClosure.isTorsionFree A K₂
  have : Module.IsTorsionFree B D₁.B₁ := IsIntegralClosure.isTorsionFree B D₁.L₁
  have : Module.IsTorsionFree B D₂.B₁ := IsIntegralClosure.isTorsionFree B D₂.L₁
  let r : D₁.A₁ := algebraMap A D₁.A₁ (π ^ 2)
  have hπ2 : π ^ 2 ≠ 0 := pow_ne_zero 2 hπ.ne_zero
  have hπB2 : algebraMap A B (π ^ 2) ≠ 0 := by simpa only [map_pow] using pow_ne_zero 2 hπB
  have hφπ : φ r = algebraMap B D₁.B₁ (algebraMap A B (π ^ 2)) :=
    (IsScalarTower.algebraMap_apply A D₁.A₁ D₁.B₁ _).symm.trans
      (IsScalarTower.algebraMap_apply A B D₁.B₁ _)
  have hr : r ∈ nonZeroDivisors D₁.A₁ := algebraMap_mem_nonZeroDivisors_of_ne_zero hπ2
  have hφr : φ r ∈ nonZeroDivisors D₁.B₁ := by
    rw [hφπ]
    exact algebraMap_mem_nonZeroDivisors_of_ne_zero hπB2
  have hregA : a₂ (AdjoinRoot.of P r) ∈ nonZeroDivisors D₂.A₁ := by
    rw [hcoeffA]
    exact algebraMap_mem_nonZeroDivisors_of_ne_zero hπ2
  have hregB : b₂ (AdjoinRoot.of (P.map φ) (φ r)) ∈ nonZeroDivisors D₂.B₁ := by
    rw [hφπ, hcoeffB]
    exact algebraMap_mem_nonZeroDivisors_of_ne_zero hπB2
  have hlocA' : LocalizationEq (AdjoinRoot P) D₂.A₁ (AdjoinRoot.of P r) := hlocA (π ^ 2) hlocK
  have hlocB' : LocalizationEq (AdjoinRoot (P.map φ)) D₂.B₁ (AdjoinRoot.of (P.map φ) (φ r)) := by
    rw [hφπ]
    exact hlocB (algebraMap A B (π ^ 2)) hlocL
  have hP : P.Monic := monic_X_pow_sub_C c hp.ne_zero
  have hPdeg : 1 < P.natDegree := by
    rw [show P.natDegree = p from natDegree_X_pow_sub_C]
    exact hp.one_lt
  obtain ⟨n, hn, A₃, hA₃, aA₃, B₃, hB₃, aB₃, hiA₃, hfinA₃, hiB₃, hfinB₃,
    hlocA₃, hlocB₃, hregA₃, hregB₃, b₃, hcomm₃, eA₃, eB₃, hsquare, hredA₃, hredB₃⟩ :=
    exists_compatible_finite_extensions_of_linear_perturbation D₁.A₁ D₁.B₁ D₂.A₁ D₂.B₁
      φ P hP hPdeg r hiA hiB (algebraMap D₂.A₁ D₂.B₁) hcomm hfinA hfinB
      hr hφr hregA hregB hlocA' hlocB'
  let := hA₃
  let := hB₃
  let := aA₃
  let := aB₃
  let Q : D₁.A₁[X] := P - C (r ^ n) * X
  have hQ : Q.Monic := by
    have heq : Q = X ^ p - C (r ^ n) * X - C c := by dsimp [Q, P]; ring
    rw [heq]
    exact monic_X_pow_sub_C_mul_X_sub_C p hp.one_lt c (r ^ n)
  let : Algebra A A₃ :=
    ((algebraMap (AdjoinRoot Q) A₃).comp (algebraMap A (AdjoinRoot Q))).toAlgebra
  have : IsScalarTower A (AdjoinRoot Q) A₃ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra B B₃ :=
    ((algebraMap (AdjoinRoot (Q.map φ)) B₃).comp (algebraMap B (AdjoinRoot (Q.map φ)))).toAlgebra
  have : IsScalarTower B (AdjoinRoot (Q.map φ)) B₃ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite D₁.A₁ (AdjoinRoot Q) := hQ.finite_quotient
  have : Module.Finite D₁.B₁ (AdjoinRoot (Q.map φ)) := (hQ.map φ).finite_quotient
  have : Module.Finite A (AdjoinRoot Q) := Module.Finite.trans D₁.A₁ _
  have : Module.Finite B (AdjoinRoot (Q.map φ)) := Module.Finite.trans D₁.B₁ _
  have : Module.Finite A A₃ := Module.Finite.trans (AdjoinRoot Q) A₃
  have : Module.Finite B B₃ := Module.Finite.trans (AdjoinRoot (Q.map φ)) B₃
  let Kalg := AdjoinRoot (Q.map (algebraMap D₁.A₁ K₁))
  let : Algebra (AdjoinRoot Q) Kalg :=
    (AdjoinRoot.map (algebraMap D₁.A₁ K₁) Q (Q.map (algebraMap D₁.A₁ K₁)) dvd_rfl).toAlgebra
  have : IsScalarTower A (AdjoinRoot Q) Kalg := IsScalarTower.of_algebraMap_eq fun x => by
    show AdjoinRoot.of _ (algebraMap A K₁ x) =
      AdjoinRoot.map (algebraMap D₁.A₁ K₁) Q _ dvd_rfl (AdjoinRoot.of Q (algebraMap A D₁.A₁ x))
    rw [AdjoinRoot.map_of, ← IsScalarTower.algebraMap_apply]
  have : IsLocalization.Away (algebraMap A D₁.A₁ (π ^ 2)) K₁ :=
    isLocalization_away_of_isIntegralClosure A K K₁ D₁.A₁ (π ^ 2)
  have : IsLocalization.Away (algebraMap A (AdjoinRoot Q) π ^ 2) Kalg := by
    rw [← map_pow]
    exact isLocalization_away_adjoinRoot_map D₁.A₁ K₁ (algebraMap A D₁.A₁ (π ^ 2)) Q
  have hqπsq : algebraMap (AdjoinRoot Q) A₃ (AdjoinRoot.of Q r) = algebraMap A A₃ π ^ 2 := by
    show algebraMap (AdjoinRoot Q) A₃ (algebraMap A (AdjoinRoot Q) (π ^ 2)) = _
    rw [← IsScalarTower.algebraMap_apply, map_pow]
  let eASquare := eA₃.trans (Ideal.quotientEquivAlgOfEq A₃
    (congrArg (fun x : A₃ => Ideal.span {x}) hqπsq)).toRingEquiv
  have hπmem : π ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit
  obtain ⟨aKalg, hAtower, hAtowerA, hAloc, hAcl, hADVR⟩ :=
    exists_isIntegralClosure_of_localizationEq_of_quotient_equiv (T := Kalg) π hπmem hiA₃
      (by
        show LocalizationEq (AdjoinRoot Q) A₃ (algebraMap A (AdjoinRoot Q) π ^ 2)
        rw [← map_pow (algebraMap A (AdjoinRoot Q)) π 2]
        exact hlocA₃)
      (by rw [← hqπsq]; exact hregA₃) _ eASquare
  let := aKalg
  let := hAtower
  let := hAtowerA
  let := hAloc
  let := hAcl
  have : CharP K₁ p := charP_of_injective_algebraMap (algebraMap K K₁).injective p
  have hπK₁ : algebraMap A K₁ π ≠ 0 := by
    intro hz
    apply hπ.ne_zero
    apply IsFractionRing.injective A K
    apply (algebraMap K K₁).injective
    simpa only [← IsScalarTower.algebraMap_apply, map_zero] using hz
  have hQK : Q.map (algebraMap D₁.A₁ K₁) =
      X ^ p - C ((algebraMap A K₁ (π ^ 2)) ^ n) * X - C (algebraMap D₁.A₁ K₁ c) := by
    simp only [Q, P, r, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_C, map_pow, ← IsScalarTower.algebraMap_apply]
    ring
  have hQsep : (Q.map (algebraMap D₁.A₁ K₁)).Separable := by
    rw [hQK]
    exact separable_X_pow_sub_C_mul_X_sub_C K₁ p (algebraMap D₁.A₁ K₁ c)
      ((algebraMap A K₁ (π ^ 2)) ^ n) (by rw [map_pow]; exact pow_ne_zero n (pow_ne_zero 2 hπK₁))
  have : Module.Finite K₁ Kalg := (hQ.map (algebraMap D₁.A₁ K₁)).finite_quotient
  have : IsReduced Kalg := isReduced_adjoinRoot_of_separable hQsep
  have : IsArtinianRing Kalg := IsArtinianRing.of_finite K₁ Kalg
  have : IsReduced (L ⊗[K] Kalg) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated (.inl hsep)
  have hred₁ : IsReduced (L ⊗[K] K₁) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated (.inl hsep)
  let e₁ := integralClosureBaseChangeRightEquiv A B K L K₁ D₁ hred₁
  let i : D₁.B₁ →+* L ⊗[K] K₁ := (integralClosure B (L ⊗[K] K₁)).val.toRingHom.comp e₁.toRingHom
  have hic (y : D₁.A₁) : i (φ y) = 1 ⊗ₜ[K] algebraMap D₁.A₁ K₁ y := by
    show (e₁ (algebraMap D₁.A₁ D₁.B₁ y) : L ⊗[K] K₁) = _
    rw [integralClosureBaseChangeRightEquiv_apply, D₁.ringSquare,
      integralClosureBaseChangeTensorEquiv_right]
    rfl
  have hQB : (Q.map φ).map i = (Q.map (algebraMap D₁.A₁ K₁)).map
      (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁).toRingHom := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext hic
  obtain ⟨jB, hjBcoeff, hjBroot, hjBloc⟩ := exists_isLocalization_away_tensor_adjoinRoot
    i (Q.map φ) (Q.map (algebraMap D₁.A₁ K₁)) hQB
    (algebraMap B D₁.B₁ (algebraMap A B (π ^ 2)))
    (isLocalization_away_of_integralClosure_equiv B L (L ⊗[K] K₁) D₁.B₁ e₁
      (algebraMap A B (π ^ 2)))
  let : Algebra (AdjoinRoot (Q.map φ)) (L ⊗[K] Kalg) := jB.toAlgebra
  let ψ : L ⊗[K] K₁ →ₐ[B] L ⊗[K] Kalg :=
    (Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom K K₁ Kalg)).restrictScalars B
  have hiBcoeff (x : B) : i (algebraMap B D₁.B₁ x) = algebraMap B (L ⊗[K] K₁) x := by
    show (e₁ (algebraMap B D₁.B₁ x) : L ⊗[K] K₁) = _
    rw [e₁.commutes]
    rfl
  have : IsScalarTower B (AdjoinRoot (Q.map φ)) (L ⊗[K] Kalg) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap B (L ⊗[K] Kalg) x = jB (AdjoinRoot.of _ (algebraMap B D₁.B₁ x))
      rw [hjBcoeff, hiBcoeff]
      exact (ψ.commutes x).symm
  have hbg : AdjoinRoot.map φ Q (Q.map φ) dvd_rfl (AdjoinRoot.of Q r) =
      algebraMap B (AdjoinRoot (Q.map φ)) (algebraMap A B π) ^ 2 := by
    rw [AdjoinRoot.map_of]
    calc
      AdjoinRoot.of (Q.map φ) (φ r) = algebraMap A (AdjoinRoot (Q.map φ)) (π ^ 2) := by
        show algebraMap D₁.B₁ (AdjoinRoot (Q.map φ))
          (algebraMap D₁.A₁ D₁.B₁ (algebraMap A D₁.A₁ (π ^ 2))) = _
        rw [← IsScalarTower.algebraMap_apply A D₁.A₁ D₁.B₁,
          ← IsScalarTower.algebraMap_apply A D₁.B₁ (AdjoinRoot (Q.map φ))]
      _ = _ := by rw [map_pow, IsScalarTower.algebraMap_apply A B (AdjoinRoot (Q.map φ))]
  have hjBg : IsLocalization.Away
      (AdjoinRoot.map φ Q (Q.map φ) dvd_rfl (AdjoinRoot.of Q r)) (L ⊗[K] Kalg) := by
    rw [AdjoinRoot.map_of, hφπ]
    exact hjBloc
  have : IsLocalization.Away
      (algebraMap B (AdjoinRoot (Q.map φ)) (algebraMap A B π) ^ 2) (L ⊗[K] Kalg) := hbg ▸ hjBg
  have hBqπsq : algebraMap (AdjoinRoot (Q.map φ)) B₃
      (AdjoinRoot.map φ Q (Q.map φ) dvd_rfl (AdjoinRoot.of Q r)) =
      algebraMap B B₃ (algebraMap A B π) ^ 2 := by
    rw [hbg, map_pow, ← IsScalarTower.algebraMap_apply]
  let eBSquare := eB₃.trans (Ideal.quotientEquivAlgOfEq B₃
    (congrArg (fun x : B₃ => Ideal.span {x}) hBqπsq)).toRingEquiv
  have hπBmem : algebraMap A B π ∈ IsLocalRing.maximalIdeal B :=
    (IsLocalRing.mem_maximalIdeal _).mpr hπBu
  obtain ⟨aLalg, hBtower, hBtowerB, hBloc, hBcl, hBDVR⟩ :=
    exists_isIntegralClosure_of_localizationEq_of_quotient_equiv (T := L ⊗[K] Kalg)
      (algebraMap A B π) hπBmem hiB₃
      (hbg ▸ hlocB₃) (hBqπsq ▸ hregB₃) _ eBSquare
  let := aLalg
  let := hBtower
  let := hBtowerB
  let := hBloc
  let := hBcl
  have hb₃ (z : AdjoinRoot Q) : b₃ (algebraMap (AdjoinRoot Q) A₃ z) =
      algebraMap (AdjoinRoot (Q.map φ)) B₃ (AdjoinRoot.map φ Q (Q.map φ) dvd_rfl z) :=
    DFunLike.congr_fun hcomm₃ z
  let : Algebra A B₃ := ((algebraMap B B₃).comp (algebraMap A B)).toAlgebra
  let : Algebra A₃ B₃ := b₃.toAlgebra
  have : IsScalarTower A B B₃ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A A₃ B₃ := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap B B₃ (algebraMap A B x) =
      b₃ (algebraMap (AdjoinRoot Q) A₃ (algebraMap A (AdjoinRoot Q) x))
    rw [hb₃ (algebraMap A (AdjoinRoot Q) x)]
    show _ = algebraMap (AdjoinRoot (Q.map φ)) B₃
      (AdjoinRoot.map φ Q (Q.map φ) dvd_rfl (AdjoinRoot.of Q (algebraMap A D₁.A₁ x)))
    rw [AdjoinRoot.map_of]
    show _ = algebraMap (AdjoinRoot (Q.map φ)) B₃
      (algebraMap D₁.B₁ (AdjoinRoot (Q.map φ))
        (algebraMap D₁.A₁ D₁.B₁ (algebraMap A D₁.A₁ x)))
    rw [← IsScalarTower.algebraMap_apply A D₁.A₁ D₁.B₁,
      IsScalarTower.algebraMap_apply A B D₁.B₁,
      ← IsScalarTower.algebraMap_apply B D₁.B₁ (AdjoinRoot (Q.map φ)),
      ← IsScalarTower.algebraMap_apply B (AdjoinRoot (Q.map φ)) B₃]
  let fE : A₃ →+* L ⊗[K] Kalg := (algebraMap B₃ (L ⊗[K] Kalg)).comp b₃
  let gE : A₃ →+* L ⊗[K] Kalg :=
    (Algebra.TensorProduct.includeRight : Kalg →ₐ[K] L ⊗[K] Kalg).toRingHom.comp (algebraMap A₃
      Kalg)
  have hfE (z : AdjoinRoot Q) : fE (algebraMap (AdjoinRoot Q) A₃ z) =
      jB (AdjoinRoot.map φ Q (Q.map φ) dvd_rfl z) := by
    show algebraMap B₃ (L ⊗[K] Kalg) (b₃ (algebraMap (AdjoinRoot Q) A₃ z)) = _
    rw [hb₃ z, ← IsScalarTower.algebraMap_apply]
    rfl
  have hgE (z : AdjoinRoot Q) : gE (algebraMap (AdjoinRoot Q) A₃ z) =
      (Algebra.TensorProduct.includeRight : Kalg →ₐ[K] L ⊗[K] Kalg)
        (AdjoinRoot.map (algebraMap D₁.A₁ K₁) Q _ dvd_rfl z) := by
    show (Algebra.TensorProduct.includeRight : Kalg →ₐ[K] L ⊗[K] Kalg)
      (algebraMap A₃ Kalg (algebraMap (AdjoinRoot Q) A₃ z)) = _
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  have hEcomp : fE.comp (algebraMap (AdjoinRoot Q) A₃) = gE.comp (algebraMap (AdjoinRoot Q) A₃) :=
    by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro y
      show fE (algebraMap (AdjoinRoot Q) A₃ (AdjoinRoot.of Q y)) =
        gE (algebraMap (AdjoinRoot Q) A₃ (AdjoinRoot.of Q y))
      rw [hfE, hgE, AdjoinRoot.map_of, AdjoinRoot.map_of, hjBcoeff, hic]
      rfl
    · show fE (algebraMap (AdjoinRoot Q) A₃ (AdjoinRoot.root Q)) =
        gE (algebraMap (AdjoinRoot Q) A₃ (AdjoinRoot.root Q))
      rw [hfE, hgE, AdjoinRoot.map_root, AdjoinRoot.map_root, hjBroot]
      rfl
  have hEreg : fE (algebraMap (AdjoinRoot Q) A₃ (AdjoinRoot.of Q r)) ∈ nonZeroDivisors (L ⊗[K] Kalg)
    := by
    have he : fE (algebraMap (AdjoinRoot Q) A₃ (AdjoinRoot.of Q r)) =
        gE (algebraMap (AdjoinRoot Q) A₃ (AdjoinRoot.of Q r)) := DFunLike.congr_fun hEcomp _
    rw [he, hgE, AdjoinRoot.map_of]
    have hu : IsUnit (algebraMap D₁.A₁ K₁ r) := by
      apply isUnit_iff_ne_zero.mpr
      show algebraMap D₁.A₁ K₁ (algebraMap A D₁.A₁ (π ^ 2)) ≠ 0
      rw [← IsScalarTower.algebraMap_apply, map_pow]
      exact pow_ne_zero 2 hπK₁
    exact ((hu.map (AdjoinRoot.of _)).map
      (Algebra.TensorProduct.includeRight : Kalg →ₐ[K] L ⊗[K] Kalg).toRingHom).mem_nonZeroDivisors
  have hE : fE = gE := ringHom_ext_of_localizationEq (AdjoinRoot.of Q r) hlocA₃ fE gE hEreg hEcomp
  have hQdeg : 0 < (Q.map (algebraMap D₁.A₁ K₁)).natDegree := by
    rw [hQ.natDegree_map]
    have hlin : (C (r ^ n) * X).natDegree ≤ 1 :=
      natDegree_le_of_degree_le (degree_C_mul_X_le _)
    have hdeg : Q.natDegree = P.natDegree :=
      natDegree_sub_eq_left_of_natDegree_lt (hlin.trans_lt hPdeg)
    rw [hdeg]
    omega
  obtain ⟨K₃, hK₃, aK₃, hfinK₃, hsepK₃, qK₃, hqK₃⟩ :=
    exists_finite_isSeparable_quotient_adjoinRoot K₁ (Q.map (algebraMap D₁.A₁ K₁)) hQsep hQdeg
  let := hK₃
  let := aK₃
  let : Algebra K K₃ := ((algebraMap K₁ K₃).comp (algebraMap K K₁)).toAlgebra
  let : Algebra A K₃ := ((algebraMap K K₃).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower K K₁ K₃ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A K K₃ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A K₁ K₃ := IsScalarTower.to₁₃₄ A K K₁ K₃
  have : Module.Finite K K₃ := Module.Finite.trans K₁ K₃
  have hregπA₂ : algebraMap A D₂.A₁ π ∈ nonZeroDivisors D₂.A₁ :=
    algebraMap_mem_nonZeroDivisors_of_ne_zero hπ.ne_zero
  have hregπB₂ : algebraMap B D₂.B₁ (algebraMap A B π) ∈ nonZeroDivisors D₂.B₁ :=
    algebraMap_mem_nonZeroDivisors_of_ne_zero hπB
  have hregπB₃ : algebraMap B B₃ (algebraMap A B π) ∈ nonZeroDivisors B₃ := by
    have hh := hBqπsq ▸ hregB₃
    exact isRegular_iff_mem_nonZeroDivisors.mp
      ((IsRegular.pow_iff (by decide : 0 < 2)).mp (isRegular_iff_mem_nonZeroDivisors.mpr hh))
  have hDVR₂A (m : Ideal D₂.A₁) [m.IsMaximal] :=
    isDiscreteValuationRing_atMaximal_of_finite_of_isPrincipalIdealRing A D₂.A₁ hπmem hregπA₂ m
  have hDVR₂B (m : Ideal D₂.B₁) [m.IsMaximal] :=
    isDiscreteValuationRing_atMaximal_of_finite_of_isPrincipalIdealRing B D₂.B₁ hπBmem hregπB₂ m
  have hmax₂ (q : Ideal D₂.B₁) [q.IsMaximal] :=
    isMaximal_comap_of_finite_local_bases A B D₂.A₁ D₂.B₁ q
  have hmax₃ (q : Ideal B₃) [q.IsMaximal] :=
    isMaximal_comap_of_finite_local_bases A B A₃ B₃ q
  have hi₂ (q : Ideal D₂.B₁) (hq : q.IsMaximal) : let _ := hq.isPrime
      Function.Injective (Localization.localRingHom (q.comap (algebraMap D₂.A₁ D₂.B₁))
        q (algebraMap D₂.A₁ D₂.B₁) rfl) := by
    let := hq
    have := hmax₂ q
    obtain ⟨hdp, hvp⟩ := hDVR₂A (q.comap (algebraMap D₂.A₁ D₂.B₁))
    obtain ⟨hdq, hvq⟩ := hDVR₂B q
    exact localRingHom_injective_of_finite_of_nonZeroDivisor A D₂.A₁ D₂.B₁ q hπmem
      (by simpa only [← IsScalarTower.algebraMap_apply] using hregπB₂)
  have hi₃ (q : Ideal B₃) (hq : q.IsMaximal) : let _ := hq.isPrime
      Function.Injective (Localization.localRingHom (q.comap b₃) q b₃ rfl) := by
    let := hq
    have := hmax₃ q
    obtain ⟨hdp, hvp⟩ := hADVR (q.comap b₃)
    obtain ⟨hdq, hvq⟩ := hBDVR q
    exact localRingHom_injective_of_finite_of_nonZeroDivisor A A₃ B₃ q hπmem
      (by simpa only [← IsScalarTower.algebraMap_apply] using hregπB₃)
  let I₂ := Ideal.span {a₂ (AdjoinRoot.of P r)}
  let J₂ := Ideal.span {b₂ (AdjoinRoot.map φ P (P.map φ) dvd_rfl (AdjoinRoot.of P r))}
  let I₃ := Ideal.span {algebraMap (AdjoinRoot Q) A₃ (AdjoinRoot.of Q r)}
  let J₃ := Ideal.span {algebraMap (AdjoinRoot (Q.map φ)) B₃
                          (AdjoinRoot.map φ Q (Q.map φ) dvd_rfl (AdjoinRoot.of Q r))}
  have hIJ₂ : I₂ ≤ J₂.comap (algebraMap D₂.A₁ D₂.B₁) := by
    apply Ideal.span_le.mpr
    rintro _ rfl
    show algebraMap D₂.A₁ D₂.B₁ (a₂ (AdjoinRoot.of P r)) ∈ J₂
    have hc : algebraMap D₂.A₁ D₂.B₁ (a₂ (AdjoinRoot.of P r)) =
        b₂ (AdjoinRoot.map φ P (P.map φ) dvd_rfl (AdjoinRoot.of P r)) :=
      DFunLike.congr_fun hcomm (AdjoinRoot.of P r)
    rw [hc]
    exact Ideal.subset_span rfl
  have hIJ₃ : I₃ ≤ J₃.comap b₃ := by
    apply Ideal.span_le.mpr
    rintro _ rfl
    show b₃ (algebraMap (AdjoinRoot Q) A₃ (AdjoinRoot.of Q r)) ∈ J₃
    rw [hb₃]
    exact Ideal.subset_span rfl
  let f₂ := Ideal.quotientMap J₂ (algebraMap D₂.A₁ D₂.B₁) hIJ₂
  let f₃ := Ideal.quotientMap J₃ b₃ hIJ₃
  let a := eA₃.toRingHom.comp (Ideal.Quotient.mk I₂)
  let b := eB₃.toRingHom.comp (Ideal.Quotient.mk J₂)
  have hs₃ : (Ideal.Quotient.mk J₃).comp b₃ = f₃.comp (Ideal.Quotient.mk I₃) := by
    ext x
    rfl
  have hs₂ : b.comp (algebraMap D₂.A₁ D₂.B₁) = f₃.comp a := by
    ext x
    show eB₃ (f₂ (Ideal.Quotient.mk I₂ x)) = f₃ (eA₃ (Ideal.Quotient.mk I₂ x))
    exact DFunLike.congr_fun hsquare (Ideal.Quotient.mk I₂ x)
  have hk₂ (q : Ideal D₂.B₁) [q.IsMaximal] : RingHom.ker b ≤ q ^ 2 := by
    rw [RingHom.ker_comp_of_injective _ eB₃.injective, Ideal.mk_ker]
    apply Ideal.span_le.mpr
    rintro _ rfl
    rw [AdjoinRoot.map_of, hφπ, hcoeffB, map_pow, map_pow]
    exact Ideal.pow_mem_pow (algebraMap_mem_of_mem_maximalIdeal_of_isIntegral B D₂.B₁ hπBmem q) 2
  have hk₃ (q : Ideal B₃) [q.IsMaximal] : RingHom.ker (Ideal.Quotient.mk J₃) ≤ q ^ 2 := by
    rw [Ideal.mk_ker]
    apply Ideal.span_le.mpr
    rintro _ rfl
    rw [hBqπsq]
    exact Ideal.pow_mem_pow (algebraMap_mem_of_mem_maximalIdeal_of_isIntegral B B₃ hπBmem q) 2
  have hdeformed := formallySmoothNAdic_atMaximal_of_common_surjective_square
    (algebraMap D₂.A₁ D₂.B₁) b₃ f₃ a b (Ideal.Quotient.mk I₃) (Ideal.Quotient.mk J₃)
    (eA₃.surjective.comp (Ideal.Quotient.mk_surjective))
    (eB₃.surjective.comp (Ideal.Quotient.mk_surjective))
    Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective hs₂ hs₃
    hmax₂ hmax₃ hDVR₂A hDVR₂B hADVR hBDVR hi₂ hi₃ hk₂ hk₃ hD₂
  let D₃ := integralClosureBaseChange A B K L K₃
  let := D₃.commRingL₁
  let := D₃.commRingA₁
  let := D₃.commRingB₁
  let := D₃.algebraKL₁
  let := D₃.algebraLL₁
  let := D₃.algebraK₁L₁
  let := D₃.algebraBL₁
  let := D₃.algebraAA₁
  let := D₃.algebraA₁K₁
  let := D₃.algebraBB₁
  let := D₃.algebraB₁L₁
  let := D₃.algebraAB₁
  let := D₃.algebraA₁B₁
  let := D₃.isScalarTowerKLL₁
  let := D₃.isScalarTowerKK₁L₁
  let := D₃.isScalarTowerBLL₁
  let := D₃.isScalarTowerAA₁K₁
  let := D₃.isScalarTowerBB₁L₁
  let := D₃.isScalarTowerABB₁
  let := D₃.isScalarTowerAA₁B₁
  let := D₃.isIntegralClosureA₁
  let := D₃.isIntegralClosureB₁
  let qA : Kalg →ₐ[A] K₃ := qK₃.restrictScalars A
  let qL : L ⊗[K] Kalg →ₐ[B] L ⊗[K] K₃ :=
    (Algebra.TensorProduct.map (AlgHom.id L L) (qK₃.restrictScalars K)).restrictScalars B
  have hqL : Function.Surjective qL :=
    Algebra.TensorProduct.map_surjective (AlgHom.id L L) (qK₃.restrictScalars K)
      Function.surjective_id hqK₃
  have : Module.Finite K Kalg := Module.Finite.trans K₁ Kalg
  have : IsArtinianRing (L ⊗[K] Kalg) := IsArtinianRing.of_finite L _
  let eAr := IsIntegralClosure.equiv A A₃ Kalg (integralClosure A Kalg)
  let eBr := IsIntegralClosure.equiv B B₃ (L ⊗[K] Kalg) (integralClosure B (L ⊗[K] Kalg))
  let eAt := IsIntegralClosure.equiv A D₃.A₁ K₃ (integralClosure A K₃)
  have hred₃ : IsReduced (L ⊗[K] K₃) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated (.inl hsep)
  let eBt := integralClosureBaseChangeRightEquiv A B K L K₃ D₃ hred₃
  let aC : A₃ →ₐ[A] D₃.A₁ := eAt.symm.toAlgHom.comp (qA.mapIntegralClosure.comp eAr.toAlgHom)
  let bC : B₃ →ₐ[B] D₃.B₁ := eBt.symm.toAlgHom.comp (qL.mapIntegralClosure.comp eBr.toAlgHom)
  have haC : Function.Surjective aC := eAt.symm.surjective.comp
    ((mapIntegralClosure_surjective_of_isArtinianRing qA hqK₃).comp eAr.surjective)
  have hbC : Function.Surjective bC := eBt.symm.surjective.comp
    ((mapIntegralClosure_surjective_of_isArtinianRing qL hqL).comp eBr.surjective)
  have hAr (x : A₃) : (eAr x : Kalg) = algebraMap A₃ Kalg x :=
    IsIntegralClosure.algebraMap_equiv A A₃ Kalg (integralClosure A Kalg) x
  have hBr (x : B₃) : (eBr x : L ⊗[K] Kalg) = algebraMap B₃ (L ⊗[K] Kalg) x :=
    IsIntegralClosure.algebraMap_equiv B B₃ (L ⊗[K] Kalg) (integralClosure B (L ⊗[K] Kalg)) x
  have hAt (x : D₃.A₁) : (eAt x : K₃) = algebraMap D₃.A₁ K₃ x :=
    IsIntegralClosure.algebraMap_equiv A D₃.A₁ K₃ (integralClosure A K₃) x
  have hBt (x : D₃.A₁) : (eBt (algebraMap D₃.A₁ D₃.B₁ x) : L ⊗[K] K₃) =
      1 ⊗ₜ[K] (eAt x : K₃) := by
    rw [hAt, integralClosureBaseChangeRightEquiv_apply, D₃.ringSquare,
      integralClosureBaseChangeTensorEquiv_right]
    rfl
  have hsC : bC.toRingHom.comp b₃ = (algebraMap D₃.A₁ D₃.B₁).comp aC.toRingHom := by
    apply RingHom.ext
    intro x
    apply eBt.injective
    apply Subtype.ext
    show (eBt (eBt.symm (qL.mapIntegralClosure (eBr (b₃ x)))) : L ⊗[K] K₃) =
      (eBt (algebraMap D₃.A₁ D₃.B₁ (eAt.symm (qA.mapIntegralClosure (eAr x)))) : L ⊗[K] K₃)
    rw [eBt.apply_symm_apply, hBt, eAt.apply_symm_apply]
    show qL (eBr (b₃ x) : L ⊗[K] Kalg) = 1 ⊗ₜ[K] qA (eAr x : Kalg)
    rw [hBr, hAr]
    exact congrArg qL (DFunLike.congr_fun hE x)
  have : IsSemisimpleRing (L ⊗[K] Kalg) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  obtain ⟨ε, hε, hkε⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker qL)
  obtain ⟨εB, hεB, hkεB⟩ := ker_mapIntegralClosure_eq_span_idempotent qL hε hkε
  have hkC : RingHom.ker bC = Ideal.span {eBr.symm εB} := by
    show RingHom.ker (eBt.symm.toRingHom.comp
      (qL.mapIntegralClosure.toRingHom.comp eBr.toRingHom)) = _
    rw [RingHom.ker_comp_of_injective _ eBt.symm.injective]
    show (RingHom.ker qL.mapIntegralClosure).comap eBr.toRingHom = _
    rw [hkεB]
    calc
      _ = (Ideal.span {εB}).map eBr.symm.toRingEquiv :=
        (Ideal.map_comap_of_equiv eBr.symm.toRingEquiv).symm
      _ = _ := by rw [Ideal.map_span]; simp
  have hεC : IsIdempotentElem (eBr.symm εB) := hεB.map eBr.symm
  have hfinAD₃ : Module.Finite A D₃.A₁ := integralClosureBaseChange_finite_left A B K L K₃ D₃ hsep
    hB
  have hfinBD₃ : Module.Finite B D₃.B₁ := integralClosureBaseChange_finite_right A B K L K₃ D₃ hB
  obtain ⟨_, _, _, _, hPIRAD₃, hPIRBD₃⟩ :=
    integralClosureBaseChange_isPrincipalIdealRing_of_finite A B K L K₃ D₃ hfinAD₃ hfinBD₃
  have : Module.IsTorsionFree A K₃ := Module.IsTorsionFree.trans K
  have : Module.IsTorsionFree B D₃.L₁ := Module.IsTorsionFree.trans L
  have : Module.IsTorsionFree A D₃.A₁ := IsIntegralClosure.isTorsionFree A K₃
  have : Module.IsTorsionFree B D₃.B₁ := IsIntegralClosure.isTorsionFree B D₃.L₁
  have hregπAD₃ : algebraMap A D₃.A₁ π ∈ nonZeroDivisors D₃.A₁ :=
    algebraMap_mem_nonZeroDivisors_of_ne_zero hπ.ne_zero
  have hregπBD₃ : algebraMap B D₃.B₁ (algebraMap A B π) ∈ nonZeroDivisors D₃.B₁ :=
    algebraMap_mem_nonZeroDivisors_of_ne_zero hπB
  have hsolD₃ : D₃.IsSolution.{uA, uB, uK, uL, uK₁, max uL uK₁, uK₁, max uL uK₁,
      max uL uK₁} := by
    intro q' hq'
    let := hq'
    let q := q'.comap bC.toRingHom
    have hq : q.IsMaximal := Ideal.comap_isMaximal_of_surjective bC.toRingHom hbC
    let p' := q'.comap (algebraMap D₃.A₁ D₃.B₁)
    have hp' : p'.IsMaximal := isMaximal_comap_of_finite_local_bases A B D₃.A₁ D₃.B₁ q'
    let p := q.comap b₃
    have hp : p.IsMaximal := hmax₃ q
    have hpa : p = p'.comap aC.toRingHom := by
      show (q'.comap bC.toRingHom).comap b₃ =
        (q'.comap (algebraMap D₃.A₁ D₃.B₁)).comap aC.toRingHom
      rw [Ideal.comap_comap, Ideal.comap_comap, hsC]
    obtain ⟨hdp, hvp⟩ := hADVR p
    obtain ⟨hdq, hvq⟩ := hBDVR q
    obtain ⟨hdp', hvp'⟩ := isDiscreteValuationRing_atMaximal_of_finite_of_isPrincipalIdealRing
      A D₃.A₁ hπmem hregπAD₃ p'
    obtain ⟨hdq', hvq'⟩ := isDiscreteValuationRing_atMaximal_of_finite_of_isPrincipalIdealRing
      B D₃.B₁ hπBmem hregπBD₃ q'
    have hiD₃ : Function.Injective (Localization.localRingHom p' q' (algebraMap D₃.A₁ D₃.B₁) rfl) :=
      localRingHom_injective_of_finite_of_nonZeroDivisor A D₃.A₁ D₃.B₁ q' hπmem
        (by simpa only [← IsScalarTower.algebraMap_apply] using hregπBD₃)
    have hkq : RingHom.ker bC ≤ q := by
      intro x hx
      show bC x ∈ q'
      rw [show bC x = 0 from hx]
      exact q'.zero_mem
    have hkq₂ : RingHom.ker bC ≤ q ^ 2 := by
      rw [hkC]
      apply Ideal.span_le.mpr
      rintro _ rfl
      have heq : eBr.symm εB ∈ q := hkq (hkC.symm ▸ Ideal.subset_span rfl)
      rw [← hεC.eq, pow_two]
      exact Ideal.mul_mem_mul heq heq
    exact (formallySmoothNAdic_atPrime_iff_of_common_surjective_square
      b₃ (algebraMap D₃.A₁ D₃.B₁) (algebraMap D₃.A₁ D₃.B₁)
      aC.toRingHom bC.toRingHom (RingHom.id D₃.A₁) (RingHom.id D₃.B₁)
      haC hbC Function.surjective_id Function.surjective_id hsC (by simp)
      p q p' q' p' q' rfl rfl rfl hpa rfl (by simp) (by simp)
      (hi₃ q hq) hiD₃ hkq₂ (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id]
        exact bot_le)).mp (hdeformed q hq)
  exact ⟨K₃, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hsepK₃, D₃, hsolD₃⟩

universe uE

/-- A nontrivial finite purely inseparable extension has an intermediate field over which the
whole extension has degree the characteristic exponent. -/
private theorem exists_intermediateField_finrank_eq_expChar
    (F E : Type*) [Field F] [Field E] [Algebra F E] (p : ℕ) [ExpChar F p]
    [Module.Finite F E] [IsPurelyInseparable F E]
    (hne : (⊥ : IntermediateField F E) ≠ ⊤) :
    ∃ M : IntermediateField F E, Module.finrank M E = p := by
  obtain ⟨n, x, htop, hsteps⟩ := IsPurelyInseparable.exists_tower_finrank_eq F E p
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Set.range_eq_empty, IntermediateField.adjoin_empty] at htop
    exact absurd htop hne
  let i : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩
  have hle : ∀ j : Fin n, j ≤ i := by
    intro j
    have hj := j.isLt
    simp only [Fin.le_def, i]
    omega
  have hu : Set.Iio i ∪ ({i} : Set (Fin n)) = Set.univ := by
    ext j
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact lt_or_eq_of_le (hle j)
  refine ⟨IntermediateField.adjoin F (x '' Set.Iio i), ?_⟩
  have hstep := (hsteps i).2.2
  have htop' : (IntermediateField.adjoin F (x '' Set.Iio i))⟮ x i⟯ = ⊤ := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.restrictScalars_top,
      ← IntermediateField.adjoin_union,
      show x '' Set.Iio i ∪ {x i} = Set.range x by
        rw [← Set.image_singleton (f := x), ← Set.image_union, hu, Set.image_univ]]
    exact htop
  rw [htop', IntermediateField.finrank_top'] at hstep
  exact hstep

private theorem charP_of_expChar_of_prime (R : Type*) [AddMonoidWithOne R]
    (p : ℕ) [h : ExpChar R p] (hp : p.Prime) : CharP R p := by
  cases h with
  | zero => exact (hp.ne_one rfl).elim
  | prime => infer_instance

private theorem exists_isSeparableSolution_aux
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B]
    [IsFractionRing A K] [IsFractionRing B L]
    (hsep : Algebra.IsSeparableExtension K L)
    (hB : IsNagataRing B) :
    ∀ (d : ℕ) (K₂ : Type uE) [Field K₂] [Algebra K K₂] [Algebra A K₂]
      [IsScalarTower A K K₂] [Module.Finite K K₂],
      Field.finInsepDegree K K₂ = d →
      (∃ D₂ : IntegralClosureBaseChange.{uA, uB, uK, uL, uE,
          max uL uE, uE, max uL uE} A B K L K₂,
        D₂.IsSolution.{uA, uB, uK, uL, uE,
          max uL uE, uE, max uL uE, max uL uE}) →
      ∃ (K₁ : Type uE) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
        (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
        ∃ D₁ : IntegralClosureBaseChange.{uA, uB, uK, uL, uE,
            max uL uE, uE, max uL uE} A B K L K₁,
          D₁.IsSeparableSolution.{uA, uB, uK, uL, uE,
            max uL uE, uE, max uL uE, max uL uE} := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro K₂ _ _ _ _ _ hd hsolution
    by_cases hK₂sep : Algebra.IsSeparable K K₂
    · refine ⟨K₂, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, ?_⟩
      obtain ⟨D₂, hD₂⟩ := hsolution
      exact ⟨D₂, hD₂, hK₂sep⟩
    · let p := ringExpChar K
      have : ExpChar K p := inferInstance
      have hp : p.Prime := by
        rcases expChar_is_prime_or_one K p with hp | hp
        · exact hp
        · have : Algebra.IsSeparable K K₂ := by
            let : ExpChar K 1 := hp ▸ inferInstance
            let : CharZero K := charZero_of_expChar_one' K
            infer_instance
          exact (hK₂sep this).elim
      let : Fact p.Prime := ⟨hp⟩
      let : CharP K p := charP_of_expChar_of_prime K p hp
      let S : IntermediateField K K₂ := separableClosure K K₂
      have : Module.Finite S K₂ := Module.Finite.of_restrictScalars_finite K S K₂
      have : IsPurelyInseparable S K₂ := by
        show IsPurelyInseparable (separableClosure K K₂) K₂
        infer_instance
      let : CharP S p := charP_of_injective_algebraMap (algebraMap K S).injective p
      have : ExpChar S p := ExpChar.prime hp
      have hbotne : (⊥ : IntermediateField S K₂) ≠ ⊤ := by
        intro hbot
        have : Algebra.IsSeparable K K₂ := by
          rw [← separableClosure.eq_top_iff]
          show S = ⊤
          ext x
          simp only [IntermediateField.mem_top, iff_true]
          have hx : x ∈ (⊥ : IntermediateField S K₂) := by
            rw [hbot]
            trivial
          simpa [IntermediateField.mem_bot] using hx
        exact hK₂sep this
      obtain ⟨T, hT⟩ := exists_intermediateField_finrank_eq_expChar S K₂ p hbotne
      let K₁ : IntermediateField K K₂ := T.restrictScalars K
      let : Algebra A K₁ :=
        ((algebraMap K K₁).comp (algebraMap A K)).toAlgebra
      let : IsScalarTower A K K₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hfiniteKK₁ : Module.Finite K K₁ := inferInstance
      let : IsScalarTower K K₁ K₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      let : IsScalarTower A K₁ K₂ := IsScalarTower.of_algebraMap_eq (fun x => by
        rw [IsScalarTower.algebraMap_apply A K K₂,
          IsScalarTower.algebraMap_apply K K₁ K₂]
        rfl)
      have hpi : IsPurelyInseparable K₁ K₂ :=
        by
          show IsPurelyInseparable T K₂
          exact IsPurelyInseparable.tower_top S T K₂
      let : IsPurelyInseparable K₁ K₂ := hpi
      have hdegree : Module.finrank K₁ K₂ = p := hT
      obtain ⟨K₃, _, _, _, _, _, _, _, _, hK₃sep, D₃, hD₃⟩ :=
        @exists_isSeparable_solution_of_isPurelyInseparable_finrank_eq_prime
          A B K L K₁ K₂
          inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance inferInstance
          hfiniteKK₁ inferInstance p hp inferInstance hsep hB hsolution hpi hdegree
      have hK₁lt : Field.finInsepDegree K K₁ < d := by
        have htower := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic
          (F := K) (E := K₁) (K := K₂)
        have hright : Field.finInsepDegree K₁ K₂ = p := by
          rw [IsPurelyInseparable.finInsepDegree_eq]
          exact hdegree
        rw [hright, hd] at htower
        have hpos : 0 < Field.finInsepDegree K K₁ := by
          unfold Field.finInsepDegree
          exact Module.finrank_pos
        nlinarith [hp.two_le]
      have hK₃degree : Field.finInsepDegree K K₃ = Field.finInsepDegree K K₁ := by
        have htower := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic
          (F := K) (E := K₁) (K := K₃)
        have hsepdegree : Field.finInsepDegree K₁ K₃ = 1 :=
          @Algebra.IsSeparable.finInsepDegree_eq K₁ K₃ _ _ _ hK₃sep
        simpa [hsepdegree] using htower.symm
      apply ih (Field.finInsepDegree K K₁) hK₁lt K₃
      · exact hK₃degree
      · exact ⟨D₃, hD₃⟩

/-- Let `A → B` be an extension of discrete valuation rings with separable fraction-field
extension `L/K`. If `B` is Nagata and there is a solution for `A → B`, then there is a
separable solution for `A → B`. -/
@[stacks 0BRN]
theorem exists_isSeparableSolution_of_exists_isSolution
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B]
    [IsFractionRing A K] [IsFractionRing B L]
    (hsep : Algebra.IsSeparableExtension K L)
    (hB : IsNagataRing B)
    (hsolution :
      ∃ (K₂ : Type uE) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∃ D₂ : IntegralClosureBaseChange.{uA, uB, uK, uL, uE,
          max uL uE, uE, max uL uE} A B K L K₂,
        D₂.IsSolution.{uA, uB, uK, uL, uE,
          max uL uE, uE, max uL uE, max uL uE}) :
    ∃ (K₁ : Type uE) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D₁ : IntegralClosureBaseChange.{uA, uB, uK, uL, uE,
          max uL uE, uE, max uL uE} A B K L K₁,
        D₁.IsSeparableSolution.{uA, uB, uK, uL, uE,
          max uL uE, uE, max uL uE, max uL uE} := by
  obtain ⟨K₂, _, _, _, _, _, hsolution⟩ := hsolution
  exact exists_isSeparableSolution_aux A B K L hsep hB
    (Field.finInsepDegree K K₂) K₂ rfl hsolution

end IsDiscreteValuationRing
