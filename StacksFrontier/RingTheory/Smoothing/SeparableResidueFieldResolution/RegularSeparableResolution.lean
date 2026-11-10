module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.Smooth.FieldExtensionCompleteIntersectionColimit
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.CompleteIntersection.Smooth
public import StacksFrontier.RingTheory.Flat.RegularSequence
public import StacksFrontier.RingTheory.Ideal.RadicalMaximalQuotient
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.Smooth.Localization
public import StacksFrontier.RingTheory.Smoothing.DesingularizationLifting
public import StacksFrontier.RingTheory.Smoothing.ImprovingPresentations
public import StacksFrontier.RingTheory.Smoothing.IndSmooth
public import StacksFrontier.RingTheory.Smoothing.LiftingProblem
public import StacksFrontier.RingTheory.Smoothing.LiftingResolutionsFromEighthPowers
public import StacksFrontier.RingTheory.Smoothing.LocalSmoothingSituation
public import StacksFrontier.RingTheory.Smoothing.ParametersWithPowersInIdeal
public import StacksFrontier.RingTheory.Smoothing.SingularIdealFactorization
public import StacksFrontier.RingTheory.Smoothing.SingularIdeals
public import StacksFrontier.RingTheory.Smoothing.SpreadingOutResolutions
public import StacksFrontier.RingTheory.Smoothing.StablyFreeStrictlyStandardPowers
public import StacksFrontier.RingTheory.Smoothing.StandardnessConditions
public import StacksFrontier.RingTheory.Smoothing.ZeroDimensionalResolution
public import StacksFrontier.RingTheory.Smoothing.SeparableResidueFieldResolution.ParameterPresentation
import all StacksFrontier.RingTheory.Smoothing.SeparableResidueFieldResolution.ParameterPresentation
public import StacksFrontier.RingTheory.Smoothing.SeparableResidueFieldResolution.FilteredColimitOfSmooth
import all StacksFrontier.RingTheory.Smoothing.SeparableResidueFieldResolution.FilteredColimitOfSmooth

/-!
# Resolving a local smoothing situation with separable residue field

Let `k → A → Λ ⊃ q` be a local smoothing situation over a field `k` with `Λ` Noetherian, `q`
minimal over `𝔥_A = √(H_{A/k} Λ)`, `Λ_q` regular local and `κ(q)/k` separable. Then the chain
can be resolved at `q`: it factors as `k → A → B → Λ` with `B` of finite presentation over `k`,
`𝔥_A ⊆ 𝔥_B` and `𝔥_B ⊄ q`.

## Main results

* `Stacks.Smoothing.canBeResolved_of_isRegularLocalRing_of_isSeparableExtension`: the resolution
  above.

## Implementation notes

The construction follows the source: one takes `R = k[x₁, …, x_d]` with `d = dim Λ_q`, forms
`B = A[x_i, z_{ij}]/(x_iⁿ - Σ z_{ij} a_j)` for generators `a_j` of `H_{A/k}` and `n` with
`qⁿΛ_q ⊆ 𝔥_A Λ_q`, improves `B` to `C` with a retraction, makes the `x_i^c` strictly standard,
chooses parameters `π_i` by `exists_parameters_pow_mem_and_annihilator_sq_eq`, and reduces by
`canBeResolved_of_quotient_eighthPowerIdeal` and `canBeResolved_of_localization_dim_zero` to an
Artinian situation that is a filtered colimit of smooth algebras.

## References

* [Stacks Project, Tag 07FE](https://stacks.math.columbia.edu/tag/07FE)
-/

@[expose] public section

namespace Stacks.Smoothing

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w u' v' t

/-- **Stacks 07FE.** Let `k → A → Λ ⊃ q` be a local smoothing situation over a field `k`
with `Λ` Noetherian, `q` minimal over `𝔥_A = √(H_{A/k} Λ)`, `Λ_q` a regular local ring and the
residue field extension `κ(q)/k` separable. Then the chain can be resolved at `q`. -/
@[stacks 07FE]
theorem canBeResolved_of_isRegularLocalRing_of_isSeparableExtension
    (k : Type u) (A : Type v) (Lambda : Type w)
    [Field k] [CommRing A] [CommRing Lambda]
    [Algebra k A] [Algebra k Lambda] [Algebra A Lambda]
    [IsScalarTower k A Lambda] [Algebra.FinitePresentation k A]
    [IsNoetherianRing Lambda] (q : Ideal Lambda) [q.IsPrime]
    (hq : (Ideal.map (algebraMap A Lambda)
      (Stacks.Smoothing.singularIdeal k A)).radical.IsMinimalPrime q)
    [IsRegularLocalRing (Localization.AtPrime q)]
    [Algebra.IsSeparableExtension k q.ResidueField] :
    CanBeResolved k A Lambda q := by
  let S : LocalSmoothingSituation.{u, v, w} := {
    R := k
    A := A
    Λ := Lambda
    q := q
  }
  have hqS : q ∈ S.radicalSingularIdealExtension.minimalPrimes := by
    exact mem_minimalPrimes_of_isMinimalPrime hq
  let J : Ideal Lambda := S.radicalSingularIdealExtension
  have hJq : J ≤ q := hq.le
  let H : Ideal Lambda := Ideal.map (algebraMap A Lambda)
    (Stacks.Smoothing.singularIdeal k A)
  have hqH : q ∈ H.minimalPrimes := by
    change q ∈ H.radical.minimalPrimes at hqS
    rw [Ideal.radical_minimalPrimes] at hqS
    exact hqS
  have hHq : H ≤ q := Ideal.le_radical.trans hJq
  obtain ⟨n, hn, hqI⟩ := exists_power_containment_at_minimalPrime H q hqH
  obtain ⟨d, hd⟩ := exists_nat_eq_ringKrullDim (R := Localization.AtPrime q)
  by_cases hd0 : d = 0
  · exact canBeResolved_of_isRegularLocalRing_dim_zero k A Lambda q hq (by simpa [hd0] using hd)
  have hdpos : 1 ≤ d := by omega
  have : Algebra.FiniteType k A := inferInstance
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hfg : (Stacks.Smoothing.singularIdeal k A).FG :=
    Ideal.fg_of_isNoetherianRing (Stacks.Smoothing.singularIdeal k A)
  obtain ⟨r, a, ha⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hspan : H = Ideal.span
      (Set.range fun j : Fin r => algebraMap A Lambda (a j)) := by
    have hrange :
        (algebraMap A Lambda) '' Set.range a =
          Set.range (fun j : Fin r => algebraMap A Lambda (a j)) := by
      ext x
      constructor
      · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨a j, ⟨j, rfl⟩, rfl⟩
    calc
      H = Ideal.map (algebraMap A Lambda) (Ideal.span (Set.range a)) := by
        simp [H, ha]
      _ = Ideal.span (Set.range fun j : Fin r => algebraMap A Lambda (a j)) := by
        rw [Ideal.map_span, hrange]
  have hAaway (j : Fin r) : Algebra.Smooth k (Localization.Away (a j)) := by
    apply smooth_localization_away_of_mem_singularIdeal k A
    rw [← ha]
    exact Ideal.subset_span ⟨j, rfl⟩
  let R : Type u := MvPolynomial (Fin d) k
  let P := parameterPresentationPolynomial A d r
  let fRP : R →ₐ[k] P :=
    MvPolynomial.aeval (fun i : Fin d => MvPolynomial.X (Sum.inl i))
  let : Algebra R P := fRP.toRingHom.toAlgebra
  let : IsScalarTower k R P :=
    IsScalarTower.of_algebraMap_eq (fun x => (fRP.commutes x).symm)
  let K : Ideal P := parameterPresentationIdeal n a
  let B := P ⧸ K
  have hP_k : Algebra.FiniteType k P :=
    Algebra.FiniteType.trans (R := k) (S := A) (A := P) inferInstance inferInstance
  let : Algebra.FiniteType k P := hP_k
  have hP_R : Algebra.FiniteType R P :=
    Algebra.FiniteType.of_restrictScalars_finiteType k R P
  let : Algebra.FiniteType R P := hP_R
  have hRnoeth : IsNoetherianRing R := inferInstance
  let : IsNoetherianRing R := hRnoeth
  have hPK : K.FG := by
    dsimp [K, parameterPresentationIdeal]
    exact Submodule.fg_span (Set.finite_range _)
  have hPB : Algebra.FinitePresentation R B := by
    let : Algebra.FinitePresentation R P := Algebra.FinitePresentation.of_finiteType.mp hP_R
    exact Algebra.FinitePresentation.quotient hPK
  let : Algebra.FinitePresentation R B := hPB
  have hXB (i : Fin d) : algebraMap R B (MvPolynomial.X i) =
      Ideal.Quotient.mk K (MvPolynomial.X (Sum.inl i)) := by
    rw [IsScalarTower.algebraMap_apply R P B]
    change Ideal.Quotient.mk K (fRP (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
  have hBsmooth (i : Fin d) : Algebra.Smooth R
      (Localization.Away (algebraMap R B (MvPolynomial.X i))) :=
    smooth_parameter_away n a hXB hAaway i
  obtain ⟨C, hCommC, hAlgRC, hAlgBC, hTowerRBC, hFTBC, g,
      nC, PC, eC, hPfiniteC, hprojectiveC, hgSymmetric, hRetract,
      hLocalCI, hLocalSmoothFree⟩ :=
    Stacks.Smoothing.exists_finiteType_retraction_improving_presentation R B
  let : CommRing C := hCommC
  let : Algebra R C := hAlgRC
  let : Algebra B C := hAlgBC
  let : IsScalarTower R B C := hTowerRBC
  let : Algebra.FiniteType B C := hFTBC
  have hBFiniteTypeR : Algebra.FiniteType R B := inferInstance
  have hCFiniteTypeR : Algebra.FiniteType R C :=
    Algebra.FiniteType.trans (R := R) (S := B) (A := C) hBFiniteTypeR hFTBC
  let : Algebra.FiniteType R C := hCFiniteTypeR
  have hCFinitePresentationR : Algebra.FinitePresentation R C :=
    Algebra.FinitePresentation.of_finiteType.mp hCFiniteTypeR
  let : Algebra.FinitePresentation R C := hCFinitePresentationR
  have hCsmooth (i : Fin d) : Algebra.Smooth R
      (Localization.Away (algebraMap R C (MvPolynomial.X i))) := by
    let b : B := algebraMap R B (MvPolynomial.X i)
    let : Algebra.Smooth R (Localization.Away b) := hBsmooth i
    have hci := isLocalCompleteIntersection_algebraMap_of_algebraSmooth
      (R := R) (S := Localization.Away b)
    have h := (hLocalCI b hci).1
    let : Algebra (Localization.Away b)
        (Localization.Away (algebraMap B C b)) :=
      (Localization.awayMap (algebraMap B C) b).toAlgebra
    let : Algebra.Smooth (Localization.Away b)
        (Localization.Away (algebraMap B C b)) := h
    have : IsScalarTower R (Localization.Away b)
        (Localization.Away (algebraMap B C b)) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      rw [IsScalarTower.algebraMap_apply R C (Localization.Away (algebraMap B C b)),
        IsScalarTower.algebraMap_apply R B C,
        IsScalarTower.algebraMap_apply R B (Localization.Away b)]
      change _ = Localization.awayMap (algebraMap B C) b _
      simp [Localization.awayMap, IsLocalization.Away.map]
    have hsm := Algebra.Smooth.comp R (Localization.Away b)
      (Localization.Away (algebraMap B C b))
    rw [IsScalarTower.algebraMap_apply R B C (MvPolynomial.X i)]
    exact hsm
  have hCfree (i : Fin d) :
      Module.Free (Localization.Away (algebraMap R C (MvPolynomial.X i)))
        (KaehlerDifferential R (Localization.Away (algebraMap R C (MvPolynomial.X i)))) := by
    have h := hLocalSmoothFree (algebraMap R B (MvPolynomial.X i)) (hBsmooth i)
    rw [IsScalarTower.algebraMap_apply R B C (MvPolynomial.X i)]
    exact h
  obtain ⟨c, hc, hstandard⟩ := exists_uniform_strictStandard_power
    (R := R) (C := C) (fun i : Fin d => MvPolynomial.X i) hCsmooth hCfree
  obtain ⟨π, hπspan, hπpow, hπann⟩ :=
    Stacks.Smoothing.exists_parameters_pow_mem_and_annihilator_sq_eq Lambda H q n (8 * c) d hn
      (by omega) hqI hd
  have hcoeff (i : Fin d) : ∃ coeff : Fin r → Lambda,
      ∑ j, coeff j * algebraMap A Lambda (a j) = π i ^ n := by
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [← hspan]
    exact hπpow i
  choose coeff hcoeff using hcoeff
  obtain ⟨φ, hφX, hφZ⟩ := exists_parameter_presentation_map n a coeff π hcoeff
  let : Algebra B Lambda := φ.toRingHom.toAlgebra
  let : IsScalarTower A B Lambda :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := B) (A := Lambda)
      (fun x => (φ.commutes x).symm)
  let : Algebra R Lambda := ((algebraMap B Lambda).comp (algebraMap R B)).toAlgebra
  let : IsScalarTower R B Lambda :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := B) (A := Lambda) rfl
  have : IsScalarTower k B Lambda :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := B) (A := Lambda) fun x => by
    rw [IsScalarTower.algebraMap_apply k A Lambda,
      IsScalarTower.algebraMap_apply k A B, ← IsScalarTower.algebraMap_apply A B Lambda]
  have : IsScalarTower k R Lambda :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := R) (A := Lambda) fun x => by
    rw [IsScalarTower.algebraMap_apply k B Lambda,
      IsScalarTower.algebraMap_apply k R B, ← IsScalarTower.algebraMap_apply R B Lambda]
  let ψ : C →ₐ[R] Lambda := (IsScalarTower.toAlgHom R B Lambda).comp g
  let : Algebra C Lambda := ψ.toRingHom.toAlgebra
  let : IsScalarTower R C Lambda :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := C) (A := Lambda)
      (fun x => (ψ.commutes x).symm)
  have : IsScalarTower B C Lambda :=
    IsScalarTower.of_algebraMap_eq (R := B) (S := C) (A := Lambda) fun x => by
    change φ x = φ (g (algebraMap B C x))
    exact congrArg φ (AlgHom.congr_fun hRetract x).symm
  let : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq' (R := A) (S := B) (A := C) rfl
  let : Algebra k C := ((algebraMap R C).comp (algebraMap k R)).toAlgebra
  let : IsScalarTower k R C :=
    IsScalarTower.of_algebraMap_eq' (R := k) (S := R) (A := C) rfl
  have : IsScalarTower k B C :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := B) (A := C) fun x => by
    rw [IsScalarTower.algebraMap_apply k R C,
      IsScalarTower.algebraMap_apply k R B, ← IsScalarTower.algebraMap_apply R B C]
  have : IsScalarTower k A C :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := A) (A := C) fun x => by
    rw [IsScalarTower.algebraMap_apply k B C,
      IsScalarTower.algebraMap_apply k A B, ← IsScalarTower.algebraMap_apply A B C]
  have : IsScalarTower A C Lambda :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := C) (A := Lambda) fun x => by
    rw [IsScalarTower.algebraMap_apply A B Lambda,
      IsScalarTower.algebraMap_apply A B C, ← IsScalarTower.algebraMap_apply B C Lambda]
  have : IsScalarTower k C Lambda :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := C) (A := Lambda) fun x => by
    rw [IsScalarTower.algebraMap_apply k R Lambda,
      IsScalarTower.algebraMap_apply k R C, ← IsScalarTower.algebraMap_apply R C Lambda]
  have hπmap (i : Fin d) : algebraMap R Lambda (MvPolynomial.X i) = π i := by
    rw [IsScalarTower.algebraMap_apply R B Lambda, hXB]
    exact hφX i
  have hπq (i : Fin d) : π i ∈ q :=
    (Ideal.IsPrime.pow_mem_iff_mem (inferInstance : q.IsPrime) n hn).mp (hHq (hπpow i))
  let x : Fin d → R := fun i => MvPolynomial.X i ^ c
  have hxπ (i : Fin d) : algebraMap R Lambda (x i) = π i ^ c := by
    dsimp [x]
    rw [map_pow, hπmap]
  have hxq (i : Fin d) : algebraMap R Lambda (x i) ∈ q := by
    rw [hxπ]
    exact Ideal.pow_mem_of_mem _ (hπq i) c hc
  have hannR (i : Fin d) : ∀ y : R ⧸ eighthPowerPrefixIdeal x i,
      y * Ideal.Quotient.mk _ (x i) = 0 ↔
        y * Ideal.Quotient.mk _ (x i) ^ 2 = 0 :=
    parameter_prefix_ann_stable i
  have hannLambda (i : Fin d) :
      let I := Ideal.map (algebraMap R Lambda) (eighthPowerPrefixIdeal x i)
      ∀ y : Lambda ⧸ I,
        y * Ideal.Quotient.mk I (algebraMap R Lambda (x i)) = 0 ↔
          y * Ideal.Quotient.mk I (algebraMap R Lambda (x i)) ^ 2 = 0 := by
    have hpref : Ideal.map (algebraMap R Lambda) (eighthPowerPrefixIdeal x i) =
        Ideal.span (Set.range fun j : Fin i.val =>
          π (j.castLE (Nat.le_of_lt i.isLt)) ^ (8 * c)) := by
      rw [map_eighthPowerPrefixIdeal_eq_span x (fun j => π j ^ c) i (fun j => hxπ j)]
      simp only [← pow_mul, Nat.mul_comm c 8]
    dsimp only
    rw [hpref]
    intro y
    have h := quotient_ann_stable_pow _ (π i)
      (by simpa only [map_pow] using hπann i) hc y
    simpa only [x, map_pow, hπmap] using h
  have hstandard' (i : Fin d) :
      IsStrictlyStandard (R := R) (A := C) (algebraMap R C (x i)) := by
    simpa only [x, map_pow] using hstandard i
  have : Module.Flat R (Localization.AtPrime q) :=
    flat_polynomial_localization_of_parameters q
      (by
        intro i
        change algebraMap R Lambda (MvPolynomial.X i) ∈ q
        rw [hπmap]
        exact hπq i)
      (by
        change Ideal.map (algebraMap Lambda (Localization.AtPrime q))
          (Ideal.span (Set.range fun i : Fin d => algebraMap R Lambda (MvPolynomial.X i))) = _
        simpa only [hπmap] using hπspan) hd
  have hAC : Ideal.map (algebraMap A C) (Stacks.Smoothing.singularIdeal k A) ≤
      Stacks.Smoothing.singularIdeal R C := by
    rw [← ha, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have := hAaway j
    have : Algebra.Smooth R (Localization.Away (algebraMap A B (a j))) :=
      ⟨formallySmooth_parameter_localization n a j hXB, inferInstance⟩
    rw [IsScalarTower.algebraMap_apply A B C]
    apply mem_singularIdeal_of_smooth_away
    exact smooth_localizationAway_awayMap_of_smooth _
      (hLocalCI _ isLocalCompleteIntersection_algebraMap_of_algebraSmooth).1
  have : Algebra.Smooth k R := ⟨inferInstance, inferInstance⟩
  apply canBeResolved_of_smooth_base q hAC
  let T : LocalSmoothingSituation.{u, v, w} := {
    R := R
    A := C
    Λ := Lambda
    q := q
  }
  apply canBeResolved_of_quotient_eighthPowerIdeal T hdpos x hxq
    (fun i => annihilator_span_singleton_eq_sq_of_forall _ (hannR i))
    (fun i => annihilator_span_singleton_eq_sq_of_forall _ (hannLambda i))
    hstandard'
  let I : Ideal R := eighthPowerIdeal x
  let IC : Ideal C := Ideal.map (algebraMap R C) I
  let IΛ : Ideal Lambda := Ideal.map (algebraMap C Lambda) IC
  have hIrad : I.radical = MvPolynomial.idealOfVars (Fin d) k := by
    have hI : I = Ideal.span (Set.range fun i : Fin d => MvPolynomial.X i ^ (8 * c)) := by
      dsimp [I, eighthPowerIdeal, x]
      congr 1
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, by rw [← pow_mul, Nat.mul_comm c 8]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, by rw [← pow_mul, Nat.mul_comm c 8]⟩
    rw [hI, radical_span_range_pow (fun i : Fin d => MvPolynomial.X i)
      (by omega)]
    change (MvPolynomial.idealOfVars (Fin d) k).radical = _
    exact (polynomial_idealOfVars_isMaximal.isPrime.isRadical).radical
  have hImax : I.radical.IsMaximal := by
    rw [hIrad]
    exact polynomial_idealOfVars_isMaximal
  have : IsLocalRing (R ⧸ I) := isLocalRing_quotient_of_radical_isMaximal hImax
  have hIΛ : IΛ = Ideal.span (Set.range fun i : Fin d => π i ^ (8 * c)) := by
    calc
      IΛ = Ideal.map (algebraMap R Lambda) I := by
        dsimp [IΛ, IC]
        rw [Ideal.map_map, IsScalarTower.algebraMap_eq R C Lambda]
      _ = Ideal.span (Set.range fun i : Fin d => (π i ^ c) ^ 8) :=
        map_eighthPowerIdeal_eq_span x (fun i => π i ^ c) hxπ
      _ = Ideal.span (Set.range fun i : Fin d => π i ^ (8 * c)) := by
        simp only [← pow_mul, Nat.mul_comm c 8]
  have hIΛq : IΛ ≤ q := by
    rw [hIΛ]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.pow_mem_of_mem _ (hπq i) _ (by omega)
  let qbar : Ideal (Lambda ⧸ IΛ) := Ideal.map (Ideal.Quotient.mk IΛ) q
  have : qbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIΛq
  have hqbar_comap : qbar.comap (Ideal.Quotient.mk IΛ) = q := by
    dsimp [qbar]
    rw [Ideal.comap_map_quotientMk, sup_eq_right.mpr hIΛq]
  let L := Localization.AtPrime q
  let J : Ideal L := Ideal.map (algebraMap Lambda L) IΛ
  let Q := L ⧸ Ideal.map (algebraMap R L) I
  have hJ : J = Ideal.map (algebraMap R L) I := by
    dsimp [J, IΛ, IC]
    rw [Ideal.map_map, Ideal.map_map]
    have hmap : ((algebraMap Lambda L).comp (algebraMap C Lambda)).comp
        (algebraMap R C) = algebraMap R L := by
      apply RingHom.ext
      intro t
      calc
        _ = algebraMap Lambda L (algebraMap R Lambda t) :=
          congrArg (algebraMap Lambda L)
            (IsScalarTower.algebraMap_apply R C Lambda _).symm
        _ = _ := (IsScalarTower.algebraMap_apply R Lambda L _).symm
    rw [hmap]
  let : Algebra (R ⧸ I) Q :=
    Ideal.Quotient.algebraQuotientMapQuotient
  have hJpow : J = Ideal.span (Set.range fun i : Fin d =>
      algebraMap Lambda L (π i) ^ (8 * c)) := by
    dsimp [J]
    rw [hIΛ, Ideal.map_span]
    rw [← Set.range_comp']
    simp only [map_pow]
  have hspanL : Ideal.span (Set.range fun i : Fin d =>
      algebraMap Lambda L (π i)) = Ideal.map (algebraMap Lambda L) q := by
    simpa only [Ideal.map_span, ← Set.range_comp'] using hπspan
  have hJrad : J.radical = IsLocalRing.maximalIdeal L := by
    rw [hJpow, radical_span_range_pow
      (fun i : Fin d => algebraMap Lambda L (π i)) (by omega), hspanL,
      IsLocalization.AtPrime.map_eq_maximalIdeal q L]
    exact (IsLocalRing.maximalIdeal.isMaximal L).isPrime.isRadical.radical
  have : IsArtinianRing Q := by
    dsimp [Q]
    apply isArtinianRing_quotient_of_radical_isMaximal
      (Ideal.map (algebraMap R L) I)
    rw [← hJ, hJrad]
    infer_instance
  have hJle : J ≤ IsLocalRing.maximalIdeal L :=
    le_trans Ideal.le_radical hJrad.le
  have hJproper : J ≠ ⊤ := by
    intro htop
    exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top
      (top_unique (htop ▸ hJle))
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
    (hJ.symm ▸ hJproper)
  have : IsLocalRing Q :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.map (algebraMap R L) I))
      Ideal.Quotient.mk_surjective
  have : Module.Flat (R ⧸ I) Q := by
    have : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] L) :=
      Module.Flat.baseChange R (R ⧸ I) L
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor L I).toLinearEquiv
  have : IsArtinianRing (R ⧸ I) :=
    isArtinianRing_quotient_of_radical_isMaximal I hImax
  let m : Ideal (R ⧸ I) := Ideal.map (Ideal.Quotient.mk I) I.radical
  have hm : m = IsLocalRing.maximalIdeal (R ⧸ I) :=
    (IsLocalRing.maximalIdeal_quotient_eq_map_radical hImax).symm
  have hmMax : m.IsMaximal := hm ▸ IsLocalRing.maximalIdeal.isMaximal _
  have hmNilpotent : IsNilpotent m := by
    rw [hm]
    exact (isArtinianRing_iff_isNilpotent_maximalIdeal (R ⧸ I)).mp inferInstance
  have hVarsL : Ideal.map (algebraMap R L)
      (MvPolynomial.idealOfVars (Fin d) k) = IsLocalRing.maximalIdeal L := by
    change Ideal.map (algebraMap R L)
      (Ideal.span (Set.range fun i : Fin d => MvPolynomial.X i)) = _
    rw [Ideal.map_span, ← Set.range_comp']
    have hX : (algebraMap R L) ∘ (fun i : Fin d => MvPolynomial.X i) =
        fun i => algebraMap Lambda L (π i) := by
      funext i
      change algebraMap R L (MvPolynomial.X i) = _
      rw [IsScalarTower.algebraMap_apply R Lambda L, hπmap]
    simp only [Function.comp_def] at hX
    rw [hX, hspanL, IsLocalization.AtPrime.map_eq_maximalIdeal q L]
  have hmQ : Ideal.map (algebraMap (R ⧸ I) Q) m =
      Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R L) I))
        (IsLocalRing.maximalIdeal L) := by
    have hcomp : (algebraMap (R ⧸ I) Q).comp (Ideal.Quotient.mk I) =
        (Ideal.Quotient.mk (Ideal.map (algebraMap R L) I)).comp (algebraMap R L) := by
      apply RingHom.ext
      intro r
      change algebraMap (R ⧸ I) Q (Ideal.Quotient.mk I r) =
        Ideal.Quotient.mk (Ideal.map (algebraMap R L) I) (algebraMap R L r)
      exact Ideal.Quotient.algebraMap_quotient_map_quotient (R := R) (S := L)
        (p := I) r
    calc
      Ideal.map (algebraMap (R ⧸ I) Q) m =
          Ideal.map ((algebraMap (R ⧸ I) Q).comp (Ideal.Quotient.mk I))
            I.radical := by dsimp [m]; rw [Ideal.map_map]
      _ = Ideal.map ((Ideal.Quotient.mk (Ideal.map (algebraMap R L) I)).comp
          (algebraMap R L)) I.radical := by
        rw [hcomp]
      _ = Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R L) I))
          (Ideal.map (algebraMap R L) I.radical) := by rw [Ideal.map_map]
      _ = Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R L) I))
          (IsLocalRing.maximalIdeal L) := by
        rw [hIrad, hVarsL]
  have hmQmax : Ideal.map (algebraMap (R ⧸ I) Q) m =
      IsLocalRing.maximalIdeal Q := by
    rw [hmQ]
    apply IsLocalRing.eq_maximalIdeal
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker, ← hJ]
    exact hJle
  let eR : ((R ⧸ I) ⧸ m) ≃+* k := by
    let f : R →+* k := MvPolynomial.constantCoeff
    have hf : Function.Surjective f := by
      intro x
      exact ⟨MvPolynomial.C x, MvPolynomial.constantCoeff_C (Fin d) x⟩
    let e₁ : ((R ⧸ I) ⧸ m) ≃+* R ⧸ I.radical :=
      DoubleQuot.quotQuotEquivQuotOfLE Ideal.le_radical
    let e₂ : (R ⧸ I.radical) ≃+* k :=
      ((Ideal.quotEquivOfEq hIrad).trans
        (Ideal.quotEquivOfEq polynomial_idealOfVars_eq_ker_constantCoeff)).trans
          (RingHom.quotientKerEquivOfSurjective hf)
    exact e₁.trans e₂
  let eQ : (Q ⧸ Ideal.map (algebraMap (R ⧸ I) Q) m) ≃+*
      q.ResidueField :=
    (Ideal.quotEquivOfEq hmQ).trans
      (DoubleQuot.quotQuotEquivQuotOfLE (hJ.symm ▸ hJle))
  let : m.IsMaximal := hmMax
  let : Field ((R ⧸ I) ⧸ m) := Ideal.Quotient.field m
  have hmQMaximal : (Ideal.map (algebraMap (R ⧸ I) Q) m).IsMaximal := by
    rw [hmQmax]
    exact (IsLocalRing.maximalIdeal.isMaximal Q)
  let : (Ideal.map (algebraMap (R ⧸ I) Q) m).IsMaximal := hmQMaximal
  let : Field (Q ⧸ Ideal.map (algebraMap (R ⧸ I) Q) m) :=
    Ideal.Quotient.field _
  let : Algebra ((R ⧸ I) ⧸ m)
      (Q ⧸ Ideal.map (algebraMap (R ⧸ I) Q) m) :=
    Ideal.Quotient.algebraQuotientMapQuotient (R := R ⧸ I) (S := Q) (p := m)
  have hPoly : (algebraMap L q.ResidueField).comp (algebraMap R L) =
      (algebraMap k q.ResidueField).comp MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext'
    · ext a
      change algebraMap L q.ResidueField
        (algebraMap R L (MvPolynomial.C a)) =
        algebraMap k q.ResidueField (MvPolynomial.constantCoeff (MvPolynomial.C a))
      rw [MvPolynomial.constantCoeff_C]
      change algebraMap L q.ResidueField
        (algebraMap R L (algebraMap k R a)) = algebraMap k q.ResidueField a
      rw [← IsScalarTower.algebraMap_apply k R L,
        ← IsScalarTower.algebraMap_apply k L q.ResidueField]
    · intro i
      change algebraMap L q.ResidueField (algebraMap R L (MvPolynomial.X i)) =
        algebraMap k q.ResidueField
          (MvPolynomial.constantCoeff (MvPolynomial.X i))
      rw [MvPolynomial.constantCoeff_X, map_zero,
        IsScalarTower.algebraMap_apply R Lambda L, hπmap,
        ← IsScalarTower.algebraMap_apply Lambda L q.ResidueField]
      exact Ideal.algebraMap_residueField_eq_zero.mpr (hπq i)
  have heR (p : R) :
      eR (Ideal.Quotient.mk m (Ideal.Quotient.mk I p)) =
        MvPolynomial.constantCoeff p := by
    have hmk : Ideal.Quotient.mk m (Ideal.Quotient.mk I p) =
        DoubleQuot.quotQuotMk I I.radical p := rfl
    rw [hmk]
    simp only [eR, RingEquiv.trans_apply]
    rw [DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk p Ideal.le_radical]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk _ p
  have heQ (p : L) :
      eQ (Ideal.Quotient.mk (Ideal.map (algebraMap (R ⧸ I) Q) m)
        (Ideal.Quotient.mk (Ideal.map (algebraMap R L) I) p)) =
          algebraMap L q.ResidueField p := by
    change (DoubleQuot.quotQuotEquivQuotOfLE (hJ.symm ▸ hJle))
      ((Ideal.quotEquivOfEq hmQ)
        (Ideal.Quotient.mk (Ideal.map (algebraMap (R ⧸ I) Q) m)
          (Ideal.Quotient.mk (Ideal.map (algebraMap R L) I) p))) = _
    have hmk : (Ideal.quotEquivOfEq hmQ)
        (Ideal.Quotient.mk (Ideal.map (algebraMap (R ⧸ I) Q) m)
          (Ideal.Quotient.mk (Ideal.map (algebraMap R L) I) p)) =
          DoubleQuot.quotQuotMk (Ideal.map (algebraMap R L) I)
            (IsLocalRing.maximalIdeal L) p := rfl
    rw [hmk, DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk]
    rfl
  have hcompat (t : (R ⧸ I) ⧸ m) :
      eQ (algebraMap ((R ⧸ I) ⧸ m)
        (Q ⧸ Ideal.map (algebraMap (R ⧸ I) Q) m) t) =
          algebraMap k q.ResidueField (eR t) := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient
      (R := R ⧸ I) (S := Q) (p := m)]
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient
      (R := R) (S := L) (p := I)]
    rw [heQ, heR]
    exact congrArg (fun f : R →+* q.ResidueField => f p) hPoly
  have hcompat' (a : k) :
      eQ.symm (algebraMap k q.ResidueField a) =
        algebraMap ((R ⧸ I) ⧸ m)
          (Q ⧸ Ideal.map (algebraMap (R ⧸ I) Q) m) (eR.symm a) := by
    apply eQ.injective
    rw [eQ.apply_symm_apply, hcompat, eR.apply_symm_apply]
  have hsepResidue : Algebra.IsSeparableExtension
      ((R ⧸ I) ⧸ m) (Q ⧸ Ideal.map (algebraMap (R ⧸ I) Q) m) :=
    isSeparableExtension_of_ringEquiv_square eR.symm eQ.symm hcompat'
      (inferInstance : Algebra.IsSeparableExtension k q.ResidueField)
  let := hsepResidue
  have hPTResidue : IsFilteredColimitOfSmooth.{u, w, max u w} ((R ⧸ I) ⧸ m)
      (Q ⧸ Ideal.map (algebraMap (R ⧸ I) Q) m) :=
    isFilteredColimitOfSmooth_of_isSeparableExtension _ _
  have hPTQ : IsFilteredColimitOfSmooth.{u, w, max u w} (R ⧸ I) Q :=
    isFilteredColimitOfSmooth_of_isNilpotent m hmNilpotent hPTResidue inferInstance
  let T := Lambda ⧸ IΛ
  let D := C ⧸ IC
  let : Algebra (R ⧸ I) T :=
    ((algebraMap D T).comp (algebraMap (R ⧸ I) D)).toAlgebra
  let : IsScalarTower (R ⧸ I) D T :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let Q' := L ⧸ J
  let eQQ' : Q ≃+* Q' := Ideal.quotEquivOfEq hJ.symm
  let : Algebra (R ⧸ I) Q' :=
    (eQQ'.toRingHom.comp (algebraMap (R ⧸ I) Q)).toAlgebra
  let eQQ'A : Q ≃ₐ[R ⧸ I] Q' :=
    AlgEquiv.ofRingEquiv (f := eQQ') (by
      intro x
      rfl)
  have hPTQ' : IsFilteredColimitOfSmooth.{u, w, max u w} (R ⧸ I) Q' :=
    isFilteredColimitOfSmooth_of_algEquiv eQQ'A hPTQ
  let : Algebra T Q' := by
    dsimp [Q', J]
    infer_instance
  have hsub : Algebra.algebraMapSubmonoid T q.primeCompl = qbar.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      intro hmem
      refine hz ?_
      have hzz : (Ideal.Quotient.mk IΛ) z = (Ideal.Quotient.mk IΛ) y := by
        change (Ideal.Quotient.mk IΛ) z = (Ideal.Quotient.mk IΛ) y at hzy
        exact hzy
      have hzbar : (Ideal.Quotient.mk IΛ) z ∈ qbar := by
        rw [hzz]
        exact hmem
      exact hqbar_comap ▸ hzbar
    · intro hx
      refine ⟨y, ?_, rfl⟩
      intro hy
      apply hx
      change y ∈ qbar.comap (Ideal.Quotient.mk IΛ)
      rw [hqbar_comap]
      exact hy
  have : IsLocalization qbar.primeCompl Q' := by
    rw [← hsub]
    dsimp [Q', J]
    infer_instance
  have : IsArtinianRing Q' := eQQ'.isArtinianRing
  have : Nontrivial Q' := eQQ'.symm.nontrivial
  let eLoc : Localization.AtPrime qbar ≃ₐ[T] Q' :=
    Localization.algEquiv qbar.primeCompl Q'
  have hdimQ' : ringKrullDim Q' = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  have hdimT : ringKrullDim (Localization.AtPrime qbar) = 0 :=
    eLoc.toRingEquiv.ringKrullDim.trans hdimQ'
  have hqbar0 : qbar ∈ minimalPrimes T := by
    apply Ideal.height_eq_zero_iff.mp
    exact_mod_cast (IsLocalization.AtPrime.ringKrullDim_eq_height qbar
      (Localization.AtPrime qbar)).symm.trans hdimT
  have hRT (r : R) : algebraMap (R ⧸ I) T (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk IΛ (algebraMap R Lambda r) := by
    change algebraMap D T
      (algebraMap (R ⧸ I) D (Ideal.Quotient.mk I r)) = _
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient,
      Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact congrArg (Ideal.Quotient.mk IΛ)
      (IsScalarTower.algebraMap_apply R C Lambda r).symm
  have : IsScalarTower (R ⧸ I) T Q' := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change eQQ' (algebraMap (R ⧸ I) Q (Ideal.Quotient.mk I r)) = _
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient (R := R) (S := L)
      (p := I), hRT,
      Ideal.Quotient.algebraMap_quotient_map_quotient (R := Lambda) (S := L)
        (p := IΛ)]
    exact Ideal.quotEquivOfEq_mk hJ.symm (algebraMap R L r)
  let eLocR : Localization.AtPrime qbar ≃ₐ[R ⧸ I] Q' :=
    eLoc.restrictScalars (R ⧸ I)
  have hPTLoc : IsFilteredColimitOfSmooth.{u, w, max u w} (R ⧸ I)
      (Localization.AtPrime qbar) :=
    isFilteredColimitOfSmooth_of_algEquiv eLocR.symm hPTQ'
  have : Algebra.FinitePresentation (R ⧸ I) D := by
    exact Algebra.FinitePresentation.equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I).symm
  let HD : Ideal T := Ideal.map (algebraMap D T)
    (Stacks.Smoothing.singularIdeal (R ⧸ I) D)
  by_cases hHD : HD.radical ≤ qbar
  · have hqbarHD : qbar ∈ HD.radical.minimalPrimes := by
      refine ⟨⟨inferInstance, hHD⟩, ?_⟩
      intro p hp hpq
      exact hqbar0.2 ⟨hp.1, bot_le⟩ hpq
    have hunit : ∀ a : R ⧸ I,
        a ∉ qbar.comap (algebraMap (R ⧸ I) T) → IsUnit a := by
      intro a ha
      have hp : (qbar.comap (algebraMap (R ⧸ I) T)).IsPrime :=
        Ideal.IsPrime.comap _
      have hm' : qbar.comap (algebraMap (R ⧸ I) T) =
          IsLocalRing.maximalIdeal (R ⧸ I) :=
        IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isPrime _)
      rw [hm'] at ha
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using ha
    exact canBeResolved_of_isFilteredColimitOfSmooth_localization (R ⧸ I) D T qbar
      hqbarHD hdimT hunit hPTLoc
  · exact canBeResolved_of_singularIdeal_not_le qbar hHD

end Stacks.Smoothing

end
