module

public import StacksFrontier.AlgebraicGeometry.Algebraization.AdicCompletionDepthDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapTransport
public import StacksFrontier.AlgebraicGeometry.Algebraization.ChartPrimePoint
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkAffineOpenComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormulaGeneral
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit
public import StacksFrontier.RingTheory.LocalCohomology.CutoffLocalization
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCriterion

/-!
# The conditions of the bootstrap situation over a completed affine ring, from completed stalks

Let `X` be a Noetherian scheme, `ℐ` an ideal sheaf, `(ℱₙ)` an object of `Coh(X, ℐ)`, and `U` an
affine open with `R = Γ(X, U)`, `I₀ = ℐ(U)`, `A = R^∧` the `I₀`-adic completion and `IA = I₀A`.
Let `L` be an `R`-module with `L/I₀ⁿ⁺¹L ≅ Γ(U, ℱₙ)` compatibly, `M = L^∧`, and `M'` a quotient of
`M` by a submodule killed by a power of `IA`. For a subset `T ⊆ X` let `T_A ⊆ Spec(A)` be the set
of primes containing `IA` whose point of `U` lies in `T`.

The proof of [Stacks, Tag 0EJF] reads its hypotheses (b), (c), (d) — conditions on the completed
stalks `ℱ_y^∧` over `𝒪_{X,y}^∧` — as the assumptions (4) and (6) of [Stacks, Tag 0EFU] for
`A, IA, T_A, M'`; the source omits this ("we omit the proofs of (c) ⇒ (4) and (d) ⇒ (6)").
This file supplies it. At a prime `𝔮 ∈ T_A` over the point `y`,
`Stacks.Algebraization.completedLocalRingAffineOpenAlgEquiv` and
`Stacks.Algebraization.completedStalkAffineOpenAddEquiv` identify `𝒪_{X,y}^∧` with `(A_𝔮)^∧` and
`ℱ_y^∧` with `(M_𝔮)^∧` semilinearly, which transports (6); away from `V(IA)` the completions of
`M_𝔮` and `M'_𝔮` have the same localizations; and (4) descends from the completion by
`Stacks.Algebraization.depth_or_depth_add_dim_of_adicCompletion`.

## Main definitions

* `Stacks.Algebraization.completedAffineLocus` — the locus `T_A`.

## Main results

* `Stacks.Algebraization.completedLocalDepth_of_completedStalkDepth` — assumption (6).
* `Stacks.Algebraization.depth_or_depth_add_dimension_of_completedStalkDepth` — assumption (4).

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}} {I : X.IdealSheafData} {U : X.Opens} (hU : IsAffineOpen U)
  [IsNoetherianRing Γ(X, U)]

/-- The locus `T_A`: the primes of the completed affine ring containing `IA` whose point of `U`
lies in `T`. -/
def completedAffineLocus (T : Set X) :
    Set (PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) :=
  {q | (I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) ≤
      q.asIdeal ∧
    hU.fromSpec (PrimeSpectrum.comap
      (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) q) ∈ T}

/-! ### The point of `U` under a prime of the completed affine ring -/

/-- The point of `U` under a prime of the completed affine ring. -/
def completedAffinePoint (q : PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) : U :=
  ⟨hU.fromSpec (PrimeSpectrum.comap
      (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) q),
    mem_of_fromSpec hU _⟩

omit [IsNoetherianRing Γ(X, U)] in
/-- The prime of `Γ(X, U)` at `completedAffinePoint hU q` is the contraction of `q`. -/
theorem primeIdealOf_completedAffinePoint
    (q : PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) :
    hU.primeIdealOf (completedAffinePoint hU q) =
      PrimeSpectrum.comap (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) q :=
  primeIdealOf_fromSpec hU _

omit [IsNoetherianRing Γ(X, U)] in
/-- If `q` contains `IA`, then `I₀` lies in the prime of `Γ(X, U)` at
`completedAffinePoint hU q`. -/
theorem le_primeIdealOf_completedAffinePoint
    (q : PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))
    (hq : (I.ideal ⟨U, hU⟩).map
      (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) ≤ q.asIdeal) :
    I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf (completedAffinePoint hU q)).asIdeal := by
  rw [primeIdealOf_completedAffinePoint]
  exact Ideal.map_le_iff_le_comap.mp hq

/-- A prime `q` of the completed affine ring containing `IA` is the prime
`affineOpenCompletedPrime I hU` at its point `completedAffinePoint hU q` of `U`. -/
theorem eq_affineOpenCompletedPrime
    (q : PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))
    (hq : (I.ideal ⟨U, hU⟩).map
      (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) ≤ q.asIdeal) :
    q = affineOpenCompletedPrime I hU (completedAffinePoint hU q)
      (le_primeIdealOf_completedAffinePoint hU q hq) :=
  eq_adicPrimeOver (Ideal.fg_of_isNoetherianRing _) _ q hq (by
    rw [primeIdealOf_completedAffinePoint]
    rfl)

/-! ### Fibres of a closed subset under a ring isomorphism -/

/-- Along a ring isomorphism `Ψ : R ≃ S`, the primes of `R` above `Ψ⁻¹ 𝔭'` and `𝔞` are the
contractions of the primes of `S` above `𝔭'` and `Ψ 𝔞`. -/
theorem setOf_prime_comap_eq_image {R S : Type*} [CommRing R] [CommRing S] (Ψ : R ≃+* S)
    (P' : Ideal S) (a : Ideal R) :
    {r : Ideal R | r.IsPrime ∧ P'.comap Ψ ≤ r ∧ a ≤ r} =
      Ideal.comap Ψ '' {r : Ideal S | r.IsPrime ∧ P' ≤ r ∧ a.map Ψ ≤ r} := by
  ext r
  constructor
  · rintro ⟨hr, hPr, har⟩
    refine ⟨r.map Ψ, ⟨Ideal.map_isPrime_of_equiv Ψ, ?_, Ideal.map_mono har⟩,
      Ideal.comap_map_of_bijective _ Ψ.bijective⟩
    rw [← Ideal.map_comap_of_surjective (Ψ : R →+* S) Ψ.surjective P']
    exact Ideal.map_mono hPr
  · rintro ⟨r', ⟨hr', hPr', har'⟩, rfl⟩
    exact ⟨Ideal.comap_isPrime _ _, Ideal.comap_mono hPr', Ideal.map_le_iff_le_comap.mp har'⟩

/-- The dimension of a quotient is unchanged along a ring isomorphism. -/
theorem ringKrullDim_quotient_comap_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (Ψ : R ≃+* S) (P : PrimeSpectrum S) :
    ringKrullDim (R ⧸ (PrimeSpectrum.comap (Ψ : R →+* S) P).asIdeal) =
      ringKrullDim (S ⧸ P.asIdeal) :=
  ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ Ψ
    (Ideal.map_comap_of_surjective (Ψ : R →+* S) Ψ.surjective P.asIdeal).symm)

/-- **Fibres correspond under a ring isomorphism.** -/
theorem setOf_prime_comap_eq_singleton_iff {R S : Type*} [CommRing R] [CommRing S]
    (Ψ : R ≃+* S) (P' : Ideal S) (a : Ideal R) (m : Ideal S) :
    {r : Ideal R | r.IsPrime ∧ P'.comap Ψ ≤ r ∧ a ≤ r} = {m.comap Ψ} ↔
      {r : Ideal S | r.IsPrime ∧ P' ≤ r ∧ a.map Ψ ≤ r} = {m} := by
  rw [setOf_prime_comap_eq_image, ← Set.image_singleton]
  exact (Set.image_injective.mpr (Ideal.comap_injective_of_surjective _ Ψ.surjective)).eq_iff

/-- An ideal contained in `q` extends into the maximal ideal of the localization at `q`. -/
private theorem map_le_maximalIdeal_localization_atPrime {A : Type*} [CommRing A] {q J : Ideal A}
    [q.IsPrime] (h : J ≤ q) :
    J.map (algebraMap A (Localization.AtPrime q)) ≤ maximalIdeal (Localization.AtPrime q) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono h

/-- `setOf_prime_comap_eq_singleton_iff`, with the ideals given up to equality. -/
private theorem setOf_prime_comap_eq_singleton_iff_of_eq {R S : Type*} [CommRing R] [CommRing S]
    (Ψ : R ≃+* S) (P' : Ideal S) (a m : Ideal R) (m' J : Ideal S) (hI : a.map Ψ = J)
    (hm : m = m'.comap Ψ) :
    {r : Ideal R | r.IsPrime ∧ P'.comap Ψ ≤ r ∧ a ≤ r} = {m} ↔
      {r : Ideal S | r.IsPrime ∧ P' ≤ r ∧ J ≤ r} = {m'} := by
  subst hI hm
  exact setOf_prime_comap_eq_singleton_iff Ψ P' a m'

/-! ### The completed local ring and the completed stalk at the point under a prime -/

section Transport

variable [IsLocallyNoetherian X] (q : PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))
  (hqI : (I.ideal ⟨U, hU⟩).map
    (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) ≤ q.asIdeal)

omit [IsNoetherianRing Γ(X, U)] [IsLocallyNoetherian X] in
/-- The extension of `I₀` to `A_𝔮`, mapped along the identity of `A_𝔮`, is the extension of `IA`
along `A → A_𝔮`. -/
theorem map_refl_map_map_completedAffine :
    ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (Localization.AtPrime q.asIdeal))).map
        (RingEquiv.refl (Localization.AtPrime q.asIdeal) : _ →+* _) =
      ((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
          (Localization.AtPrime q.asIdeal)) := by
  have h : ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (Localization.AtPrime q.asIdeal))).map
      (RingEquiv.refl (Localization.AtPrime q.asIdeal) : _ →+* _) =
      (I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (Localization.AtPrime q.asIdeal)) :=
    Ideal.map_id _
  exact h.trans (map_map_completedPrime_localization I hU q).symm

/-- **The completed local ring at the point under `𝔮` is the completed localization `(A_𝔮)^∧`**,
the completion being along `IA·A_𝔮` as in the bootstrap situation. -/
def completedAffineRingEquiv :
    completedLocalRing I (completedAffinePoint hU q).1 ≃+*
      AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
        (Localization.AtPrime q.asIdeal) :=
  (completedLocalRingAffineOpenAlgEquiv I hU (completedAffinePoint hU q)
      (le_primeIdealOf_completedAffinePoint hU q hqI) q
      (eq_affineOpenCompletedPrime hU q hqI)).toRingEquiv.trans
    (AdicCompletion.ringEquivOfRingEquiv (RingEquiv.refl _)
      (map_refl_map_map_completedAffine hU q))

omit [IsLocallyNoetherian X] in
/-- `completedAffineRingEquiv` on the image of an element of `Γ(X, U)`. -/
theorem completedAffineRingEquiv_algebraMap (a : Γ(X, U)) :
    completedAffineRingEquiv hU q hqI
        (algebraMap Γ(X, U) (completedLocalRing I (completedAffinePoint hU q).1) a) =
      algebraMap (Localization.AtPrime q.asIdeal) (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
          (Localization.AtPrime q.asIdeal))
        (algebraMap Γ(X, U) (Localization.AtPrime q.asIdeal) a) := by
  have h1 := (completedLocalRingAffineOpenAlgEquiv I hU (completedAffinePoint hU q)
    (le_primeIdealOf_completedAffinePoint hU q hqI) q
      (eq_affineOpenCompletedPrime hU q hqI)).commutes a
  have h2 := IsScalarTower.algebraMap_apply Γ(X, U) (Localization.AtPrime q.asIdeal)
    (AdicCompletion ((I.ideal ⟨U, hU⟩).map
      (algebraMap Γ(X, U) (Localization.AtPrime q.asIdeal))) (Localization.AtPrime q.asIdeal)) a
  have h3 := AdicCompletion.ringEquivOfRingEquiv_algebraMap
    (RingEquiv.refl (Localization.AtPrime q.asIdeal)) (map_refl_map_map_completedAffine hU q)
    (algebraMap Γ(X, U) (Localization.AtPrime q.asIdeal) a)
  exact (congrArg (AdicCompletion.ringEquivOfRingEquiv
    (RingEquiv.refl (Localization.AtPrime q.asIdeal)) (map_refl_map_map_completedAffine hU q))
      (h1.trans h2)).trans h3

omit [IsNoetherianRing Γ(X, U)] [IsLocallyNoetherian X] in
include hqI in
/-- The stalk of `ℐ` at the point under `𝔮` lies in the maximal ideal. -/
theorem stalk_le_maximalIdeal_completedAffinePoint :
    IdealSheafData.stalk I (completedAffinePoint hU q).1 ≤
      maximalIdeal (X.presheaf.stalk (completedAffinePoint hU q).1) := by
  have := hU.isLocalization_stalk (completedAffinePoint hU q)
  rw [stalk_eq_map_algebraMap_stalk I hU (completedAffinePoint hU q), Ideal.map_le_iff_le_comap]
  intro a ha
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ a).mpr
    (le_primeIdealOf_completedAffinePoint hU q hqI ha)

omit [IsLocallyNoetherian X] in
/-- **The ideal `ℐ𝒪_{X,y}^∧` corresponds to `IA·(A_𝔮)^∧`.** -/
theorem map_completedLocalIdeal_completedAffineRingEquiv :
    (completedLocalIdeal I (completedAffinePoint hU q).1).map
        (completedAffineRingEquiv hU q hqI) =
      (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
          (Localization.AtPrime q.asIdeal))).map
        (algebraMap (Localization.AtPrime q.asIdeal) (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
          (Localization.AtPrime q.asIdeal))) := by
  have e1 : completedLocalIdeal I (completedAffinePoint hU q).1 =
      (I.ideal ⟨U, hU⟩).map
        (algebraMap Γ(X, U) (completedLocalRing I (completedAffinePoint hU q).1)) := by
    have h := congrArg (Ideal.map (algebraMap (X.presheaf.stalk (completedAffinePoint hU q).1)
      (completedLocalRing I (completedAffinePoint hU q).1)))
      (stalk_eq_map_algebraMap_stalk I hU (completedAffinePoint hU q))
    refine h.trans ?_
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have e2 : (completedAffineRingEquiv hU q hqI :
        completedLocalRing I (completedAffinePoint hU q).1 →+*
          AdicCompletion (((I.ideal ⟨U, hU⟩).map
            (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
          (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
            (Localization.AtPrime q.asIdeal)).comp
        (algebraMap Γ(X, U) (completedLocalRing I (completedAffinePoint hU q).1)) =
      (algebraMap (Localization.AtPrime q.asIdeal) (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
          (Localization.AtPrime q.asIdeal))).comp
        (algebraMap Γ(X, U) (Localization.AtPrime q.asIdeal)) :=
    RingHom.ext fun a => completedAffineRingEquiv_algebraMap hU q hqI a
  rw [e1]
  refine (Ideal.map_coe (completedAffineRingEquiv hU q hqI) _).symm.trans ?_
  exact ((Ideal.map_map _ _).trans (congrArg (fun φ => Ideal.map φ (I.ideal ⟨U, hU⟩)) e2)).trans
    ((Ideal.map_map _ _).symm.trans
      (congrArg (Ideal.map _) (map_map_completedPrime_localization I hU q).symm))

/-- **The maximal ideal of `𝒪_{X,y}^∧` corresponds to that of `(A_𝔮)^∧`.** -/
theorem map_completedMaximalIdeal_completedAffineRingEquiv :
    (completedMaximalIdeal I (completedAffinePoint hU q).1).map
        (completedAffineRingEquiv hU q hqI) =
      (maximalIdeal (Localization.AtPrime q.asIdeal)).map
        (algebraMap (Localization.AtPrime q.asIdeal) (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
          (Localization.AtPrime q.asIdeal))) := by
  have hle := stalk_le_maximalIdeal_completedAffinePoint hU q hqI
  have hle' := map_le_maximalIdeal_localization_atPrime hqI
  have := Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal _ hle
  have := Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal _ hle'
  have h1 : completedMaximalIdeal I (completedAffinePoint hU q).1 =
      maximalIdeal (completedLocalRing I (completedAffinePoint hU q).1) :=
    IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ hle
      (Ideal.fg_of_isNoetherianRing _))
  have h2 : (maximalIdeal (Localization.AtPrime q.asIdeal)).map
        (algebraMap (Localization.AtPrime q.asIdeal) (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
          (Localization.AtPrime q.asIdeal))) = maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ hle'
      (Ideal.fg_of_isNoetherianRing _))
  exact (congrArg (fun K => K.map (completedAffineRingEquiv hU q hqI)) h1).trans
    ((IsLocalRing.map_ringEquiv_maximalIdeal (completedAffineRingEquiv hU q hqI)).trans h2.symm)

/-- The maximal ideal of `𝒪_{X,y}^∧` is the contraction of that of `(A_𝔮)^∧`. -/
private theorem completedMaximalIdeal_eq_comap_completedAffineRingEquiv :
    completedMaximalIdeal I (completedAffinePoint hU q).1 =
      ((maximalIdeal (Localization.AtPrime q.asIdeal)).map
        (algebraMap (Localization.AtPrime q.asIdeal) (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
          (Localization.AtPrime q.asIdeal)))).comap (completedAffineRingEquiv hU q hqI) := by
  rw [← map_completedMaximalIdeal_completedAffineRingEquiv hU q hqI]
  exact (Ideal.comap_map_of_bijective _ (completedAffineRingEquiv hU q hqI).bijective).symm

variable (F : Stacks.Coherent.CoherentAdicSystems I)
  {L : Type u} [AddCommGroup L] [Module Γ(X, U) L]
  (ε : ∀ n : ℕ, (L ⧸ (I.ideal ⟨U, hU⟩ ^ (n + 1) • (⊤ : Submodule Γ(X, U) L))) ≃ₗ[Γ(X, U)]
    Γ(F.obj.obj (op n), U))
  (hε : ∀ {m n : ℕ} (h : m ≤ n)
    (z : L ⧸ (I.ideal ⟨U, hU⟩ ^ (n + 1) • (⊤ : Submodule Γ(X, U) L))),
    (F.obj.map (homOfLE h).op).app U (ε n z) =
      ε m (AdicCompletion.transitionMap _ L (Nat.succ_le_succ h) z))

/-- The `Γ(X, U)`-module structure on the formal stalk through the germ map. -/
@[instance_reducible]
def formalStalkSectionsModule (x : U) : Module Γ(X, U) (formalStalk F x.1) :=
  Module.compHom _ (algebraMap Γ(X, U) (X.presheaf.stalk x.1))

include hε in
/-- **The completed stalk at the point under `𝔮` is the completion `(M_𝔮)^∧`**, the completion
being along `IA·A_𝔮` as in the bootstrap situation. -/
def completedAffineAddEquiv :
    completedStalk I F (completedAffinePoint hU q).1 ≃+
      AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
        (LocalizedModule q.asIdeal.primeCompl (AdicCompletion (I.ideal ⟨U, hU⟩) L)) :=
  letI := formalStalkSectionsModule F (completedAffinePoint hU q)
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk (completedAffinePoint hU q).1)
      (formalStalk F (completedAffinePoint hU q).1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  (completedStalkAffineOpenAddEquiv hU F ε (completedAffinePoint hU q)
      (le_primeIdealOf_completedAffinePoint hU q hqI) q
      (eq_affineOpenCompletedPrime hU q hqI) hε).trans
    (AdicCompletion.addEquivOfRingEquiv (RingEquiv.refl _)
      (map_refl_map_map_completedAffine hU q) (AddEquiv.refl _) (fun _ _ => rfl))

include hε in
/-- The module comparison lies over the ring comparison. -/
theorem completedAffineAddEquiv_smul (r : completedLocalRing I (completedAffinePoint hU q).1)
    (z : completedStalk I F (completedAffinePoint hU q).1) :
    completedAffineAddEquiv hU q hqI F ε hε (r • z) =
      completedAffineRingEquiv hU q hqI r • completedAffineAddEquiv hU q hqI F ε hε z := by
  let := formalStalkSectionsModule F (completedAffinePoint hU q)
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk (completedAffinePoint hU q).1)
      (formalStalk F (completedAffinePoint hU q).1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have h1 := completedStalkAffineOpenAddEquiv_smul hU F ε (completedAffinePoint hU q)
    (le_primeIdealOf_completedAffinePoint hU q hqI) q (eq_affineOpenCompletedPrime hU q hqI) hε r z
  have h2 := AdicCompletion.addEquivOfRingEquiv_smul (RingEquiv.refl _)
    (map_refl_map_map_completedAffine hU q) (AddEquiv.refl _) (fun _ _ => rfl)
    (completedLocalRingAffineOpenAlgEquiv I hU (completedAffinePoint hU q)
      (le_primeIdealOf_completedAffinePoint hU q hqI) q (eq_affineOpenCompletedPrime hU q hqI) r)
    (completedStalkAffineOpenAddEquiv hU F ε (completedAffinePoint hU q)
      (le_primeIdealOf_completedAffinePoint hU q hqI) q (eq_affineOpenCompletedPrime hU q hqI) hε z)
  exact (congrArg (AdicCompletion.addEquivOfRingEquiv (RingEquiv.refl _)
    (map_refl_map_map_completedAffine hU q) (AddEquiv.refl _) (fun _ _ => rfl)) h1).trans h2

include hε in
/-- **The depth of the completed stalk at a prime is the depth of `(M_𝔮)^∧` at the
corresponding prime.** -/
theorem completedStalkDepth_comap_completedAffineRingEquiv
    (p' : PrimeSpectrum (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
        (Localization.AtPrime q.asIdeal))) :
    completedStalkDepth I F (completedAffinePoint hU q).1
        (PrimeSpectrum.comap (completedAffineRingEquiv hU q hqI : _ →+* _) p') =
      Module.depth (Localization.AtPrime p'.asIdeal)
        (maximalIdeal (Localization.AtPrime p'.asIdeal))
        (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
          (LocalizedModule q.asIdeal.primeCompl (AdicCompletion (I.ideal ⟨U, hU⟩) L)))) :=
  LocalizedModule.depth_atPrime_comap_eq_of_ringEquiv (completedAffineRingEquiv hU q hqI)
    (completedAffineAddEquiv hU q hqI F ε hε) (completedAffineAddEquiv_smul hU q hqI F ε hε)
    p'.asIdeal

end Transport

/-! ### Localizing a surjection with power-torsion kernel -/

/-- If every element of `K` kills the kernel of `π`, then every element of the extension of `K` to
a localization kills the kernel of the localized map. -/
theorem smul_eq_zero_of_mem_ker_localizedModule_map {A : Type*} [CommRing A] (S : Submonoid A)
    {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (π : M →ₗ[A] M') (K : Ideal A) (he : ∀ a ∈ K, ∀ x ∈ LinearMap.ker π, a • x = 0) :
    ∀ b ∈ K.map (algebraMap A (Localization S)),
      ∀ y ∈ LinearMap.ker (LocalizedModule.map S π), b • y = 0 := by
  intro b hb y hy
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨a, ha, rfl⟩ := hb
    induction y using LocalizedModule.induction_on with
    | h m s =>
      rw [LinearMap.mem_ker, LocalizedModule.map_mk, ← LocalizedModule.zero_mk s,
        LocalizedModule.mk_eq] at hy
      obtain ⟨u, hu⟩ := hy
      simp only [Submonoid.smul_def, smul_zero] at hu
      have hu' : π ((u : A) • (s : A) • m) = 0 := by
        rwa [map_smul, map_smul]
      rw [algebraMap_smul, LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk s,
        LocalizedModule.mk_eq]
      refine ⟨u, ?_⟩
      simp only [Submonoid.smul_def, smul_zero]
      rw [smul_comm (s : A) a, smul_comm (u : A) a]
      exact he a ha _ hu'
  | zero => exact zero_smul _ y
  | add b₁ b₂ _ _ h₁ h₂ => rw [add_smul, h₁, h₂, add_zero]
  | smul r b _ h => rw [smul_eq_mul, mul_smul, h, smul_zero]

/-! ### Assumption (6) -/

section Fields

variable [IsLocallyNoetherian X] (F : Stacks.Coherent.CoherentAdicSystems I)
  {L : Type u} [AddCommGroup L] [Module Γ(X, U) L]
  (ε : ∀ n : ℕ, (L ⧸ (I.ideal ⟨U, hU⟩ ^ (n + 1) • (⊤ : Submodule Γ(X, U) L))) ≃ₗ[Γ(X, U)]
    Γ(F.obj.obj (op n), U))
  (hε : ∀ {m n : ℕ} (h : m ≤ n)
    (z : L ⧸ (I.ideal ⟨U, hU⟩ ^ (n + 1) • (⊤ : Submodule Γ(X, U) L))),
    (F.obj.map (homOfLE h).op).app U (ε n z) =
      ε m (AdicCompletion.transitionMap _ L (Nat.succ_le_succ h) z))
  [Module.Finite (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (AdicCompletion (I.ideal ⟨U, hU⟩) L)]
  {M' : Type u} [AddCommGroup M'] [Module (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) M']
  [Module.Finite (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) M']
  (π : AdicCompletion (I.ideal ⟨U, hU⟩) L →ₗ[AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)] M')
  (hπ : Function.Surjective π) (e : ℕ)
  (he : ∀ a ∈ ((I.ideal ⟨U, hU⟩).map
      (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))) ^ e,
    ∀ x ∈ LinearMap.ker π, a • x = 0)

omit [IsLocallyNoetherian X] in
include hπ he in
/-- Away from `V(IA)`, the localizations of `(M_𝔮)^∧` and `(M'_𝔮)^∧` have the same depth. -/
theorem depth_localized_completedAffine_eq
    (q : PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))
    (p' : Ideal (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
        (Localization.AtPrime q.asIdeal))) [p'.IsPrime]
    (hp' : ¬ (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
          (Localization.AtPrime q.asIdeal))).map
        (algebraMap (Localization.AtPrime q.asIdeal) (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
          (Localization.AtPrime q.asIdeal))) ≤ p') :
    Module.depth (Localization.AtPrime p') (maximalIdeal (Localization.AtPrime p'))
        (LocalizedModule p'.primeCompl (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
          (LocalizedModule q.asIdeal.primeCompl (AdicCompletion (I.ideal ⟨U, hU⟩) L)))) =
      Module.depth (Localization.AtPrime p') (maximalIdeal (Localization.AtPrime p'))
        (LocalizedModule p'.primeCompl (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
          (LocalizedModule q.asIdeal.primeCompl M'))) := by
  refine depth_localized_adicCompletion_eq_of_surjective _
    (LocalizedModule.map q.asIdeal.primeCompl π)
    (LocalizedModule.map_surjective _ _ hπ) e (fun a ha x hx => ?_) p' hp'
  rw [← Ideal.map_pow] at ha
  exact smul_eq_zero_of_mem_ker_localizedModule_map _ π _ he a ha x hx

omit [IsNoetherianRing Γ(X, U)] [IsLocallyNoetherian X] in
/-- `(s : ℕ∞) < d` read in the extended integers. -/
theorem enatToEInt_gt_of_natCast_lt {s : ℕ} {d : ℕ∞} (h : (s : ℕ∞) < d) :
    enatToEInt d > (((s : ℕ) : ℤ) : EInt) := by
  cases d using ENat.recTopCoe with
  | top => exact Stacks.LocalCohomology.eint_natCast_lt_top s
  | coe n =>
    change ((s : ℤ) : EInt) < ((n : ℤ) : EInt)
    exact WithBotTop.coe_lt_coe.mpr (by exact_mod_cast h)

include hε hπ he in
/-- **Assumption (6) of [Stacks, Tag 0EFU] over the completed affine ring.** If at every point
`y ∈ U ∩ T` and every nonmaximal prime `𝔭` of `𝒪_{X,y}^∧` with
`V(𝔭) ∩ V(ℐ𝒪_{X,y}^∧) = {𝔪_y^∧}` the depth of `(ℱ_y^∧)_𝔭` exceeds `s`, then at every
`𝔮 ∈ T_A` and every prime `𝔭'` of `(A_𝔮)^∧` outside `V(IA)` with only the closed point in common
with `V(IA)`, the depth of `((M'_𝔮)^∧)_{𝔭'}` exceeds `s`. -/
theorem completedLocalDepth_of_completedStalkDepth (T : Set X) (s : ℕ)
    (h : ∀ x : U, x.1 ∈ T → ∀ p : PrimeSpectrum (completedLocalRing I x.1),
      p.asIdeal ≠ completedMaximalIdeal I x.1 →
      adicClosedFibreThrough I x.1 p = {completedMaximalIdeal I x.1} →
      (s : ℕ∞) < completedStalkDepth I F x.1 p) :
    ∀ q : PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)),
      q ∈ completedAffineLocus hU T →
      let Aq := Localization.AtPrime q.asIdeal
      let Iq := ((I.ideal ⟨U, hU⟩).map
        (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
          (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) Aq)
      let Mq := LocalizedModule q.asIdeal.primeCompl M'
      let A' := AdicCompletion Iq Aq
      let I' := Iq.map (algebraMap Aq A')
      let m' := (maximalIdeal Aq).map (algebraMap Aq A')
      ∀ p' : PrimeSpectrum A',
        ¬ I' ≤ p'.asIdeal →
        {r' : Ideal A' | r'.IsPrime ∧ p'.asIdeal ≤ r' ∧ I' ≤ r'} = {m'} →
        enatToEInt
          (Module.depth (Localization.AtPrime p'.asIdeal)
            (maximalIdeal (Localization.AtPrime p'.asIdeal))
            (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion Iq Mq))) >
          (((s : ℕ) : ℤ) : EInt) := by
  intro q hq
  dsimp only
  intro p' hp'I hfib
  have hqI := hq.1
  have hI' := map_completedLocalIdeal_completedAffineRingEquiv hU q hqI
  have hPI : ¬ completedLocalIdeal I (completedAffinePoint hU q).1 ≤
      p'.asIdeal.comap (completedAffineRingEquiv hU q hqI) := fun hle =>
    hp'I (hI' ▸ Ideal.map_le_iff_le_comap.mpr hle)
  have hfibP : adicClosedFibreThrough I (completedAffinePoint hU q).1
      (PrimeSpectrum.comap (completedAffineRingEquiv hU q hqI : _ →+* _) p') =
      {completedMaximalIdeal I (completedAffinePoint hU q).1} :=
    (setOf_prime_comap_eq_singleton_iff_of_eq _ _ _ _ _ _ hI'
      (completedMaximalIdeal_eq_comap_completedAffineRingEquiv hU q hqI)).mpr hfib
  have hPm : (PrimeSpectrum.comap (completedAffineRingEquiv hU q hqI : _ →+* _) p').asIdeal ≠
      completedMaximalIdeal I (completedAffinePoint hU q).1 := by
    intro hPm
    exact hPI (le_of_le_of_eq (Ideal.map_mono (stalk_le_maximalIdeal_completedAffinePoint hU q hqI))
      hPm.symm)
  have hdep := h (completedAffinePoint hU q) hq.2 _ hPm hfibP
  have h1 := completedStalkDepth_comap_completedAffineRingEquiv hU q hqI F ε hε p'
  have h2 := depth_localized_completedAffine_eq hU π hπ e he q p'.asIdeal hp'I
  exact enatToEInt_gt_of_natCast_lt (lt_of_lt_of_eq hdep (h1.trans h2))

omit [IsNoetherianRing Γ(X, U)] [IsLocallyNoetherian X] in
/-- The depth at a prime depends only on the prime. -/
theorem depth_atPrime_congr {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {P₁ P₂ : Ideal A} [P₁.IsPrime] [P₂.IsPrime] (h : P₁ = P₂) :
    Module.depth (Localization.AtPrime P₁) (maximalIdeal (Localization.AtPrime P₁))
        (LocalizedModule P₁.primeCompl N) =
      Module.depth (Localization.AtPrime P₂) (maximalIdeal (Localization.AtPrime P₂))
        (LocalizedModule P₂.primeCompl N) := by
  subst h
  rfl

include hε hπ he in
/-- **Assumption (4) of [Stacks, Tag 0EFU] over the completed affine ring, with `s = 1`.** Let
`Γ(X, U)` have a dualizing complex. If at every point `y ∈ U ∩ T'` and every prime `𝔭` of
`𝒪_{X,y}^∧` outside `V(ℐ𝒪_{X,y}^∧)` with `V(𝔭) ∩ V(ℐ𝒪_{X,y}^∧) ≠ {𝔪_y^∧}` either
`depth((ℱ_y^∧)_𝔭) ≥ 1` or `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 1 + d`, then for primes
`𝔭 ⊆ 𝔯 ⊆ 𝔮` of `A` with `𝔭 ∉ V(IA)`, `𝔯 ∈ V(IA) ∖ T'_A` and `𝔮 ∈ T'_A`, either
`depth(M'_𝔭) ≥ 1` or `depth(M'_𝔭) + dim((A/𝔭)_𝔮) > d + 1`. -/
theorem depth_or_depth_add_dimension_of_completedStalkDepth
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} Γ(X, U)), Dualizing.IsDualizingComplex K)
    (T' : Set X) (d : ℤ)
    (hc : ∀ x : U, x.1 ∈ T' → ∀ p : PrimeSpectrum (completedLocalRing I x.1),
      ¬ completedLocalIdeal I x.1 ≤ p.asIdeal →
      adicClosedFibreThrough I x.1 p ≠ {completedMaximalIdeal I x.1} →
      1 ≤ completedStalkDepth I F x.1 p ∨
        enatToEInt (completedStalkDepth I F x.1 p) +
            krullDimToEInt (ringKrullDim (completedLocalRing I x.1 ⧸ p.asIdeal)) >
          ((1 + d : ℤ) : EInt)) :
    ∀ p r q : PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)),
      p.asIdeal ≤ r.asIdeal → r.asIdeal ≤ q.asIdeal →
      p ∉ PrimeSpectrum.zeroLocus (((I.ideal ⟨U, hU⟩).map
        (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) : Ideal _) : Set _) →
      r ∈ PrimeSpectrum.zeroLocus (((I.ideal ⟨U, hU⟩).map
        (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) : Ideal _) : Set _) →
      r ∉ completedAffineLocus hU T' → q ∈ completedAffineLocus hU T' →
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M')) ≥ ((1 : ℤ) : EInt)) ∨
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M')) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
              (Localization.AtPrime q.asIdeal)))) >
        ((d + 1 : ℤ) : EInt)) := by
  intro p r q hpr hrq hp hr hrT hq
  have hqI := hq.1
  -- the local ring `A_𝔮` and its data
  have hJ := map_le_maximalIdeal_localization_atPrime hqI
  have hdualq : ∃ K : DerivedCategory (ModuleCat.{u} (Localization.AtPrime q.asIdeal)),
      Dualizing.IsDualizingComplex K := by
    obtain ⟨K, hK⟩ := hdual
    have hK₁ := Dualizing.isDualizingComplex_adicCompletion (I.ideal ⟨U, hU⟩) K hK
    exact ⟨_, Dualizing.isDualizingComplex_localization q.asIdeal.primeCompl _ hK₁⟩
  have hpq : p.asIdeal ≤ q.asIdeal := hpr.trans hrq
  have hprime := fun t (ht : t ≤ q.asIdeal) [t.IsPrime] =>
    Ideal.isPrime_map_of_isLocalizationAtPrime (S := Localization.AtPrime q.asIdeal) q.asIdeal ht
  have hunder := fun t (ht : t ≤ q.asIdeal) [t.IsPrime] =>
    Ideal.under_map_of_isLocalizationAtPrime (S := Localization.AtPrime q.asIdeal) q.asIdeal ht
  have hPunder := hunder _ hpq
  have hRunder := hunder _ hrq
  have hPR : p.asIdeal.map (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
      (Localization.AtPrime q.asIdeal)) ≤ r.asIdeal.map (algebraMap _ _) := Ideal.map_mono hpr
  have hPJ : ¬ ((I.ideal ⟨U, hU⟩).map
      (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)) ≤
      p.asIdeal.map (algebraMap _ _) := by
    intro hle
    apply hp
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, ← hPunder]
    exact Ideal.map_le_iff_le_comap.mp hle
  have hRJ : ((I.ideal ⟨U, hU⟩).map
      (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)) ≤
      r.asIdeal.map (algebraMap _ _) :=
    Ideal.map_mono <| by rwa [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at hr
  have hRm : r.asIdeal.map (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
      (Localization.AtPrime q.asIdeal)) ≠ maximalIdeal (Localization.AtPrime q.asIdeal) := by
    intro hRm
    apply hrT
    have hrq' : r = q := by
      ext1
      rw [← hRunder, hRm]
      exact IsLocalization.AtPrime.under_maximalIdeal _ q.asIdeal
    rw [hrq']
    exact hq
  -- the hypothesis of the descent, from the completed stalks at the point under `𝔮`
  have hI' := map_completedLocalIdeal_completedAffineRingEquiv hU q hqI
  have hcB : ∀ P'' : PrimeSpectrum (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
        (Localization.AtPrime q.asIdeal)),
      ¬ (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
          (Localization.AtPrime q.asIdeal))).map
          (algebraMap _ _) ≤ P''.asIdeal →
      {r'' | r''.IsPrime ∧ P''.asIdeal ≤ r'' ∧ (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
          (Localization.AtPrime q.asIdeal))).map
          (algebraMap _ _) ≤ r''} ≠
        {(maximalIdeal (Localization.AtPrime q.asIdeal)).map (algebraMap _ _)} →
      1 ≤ Module.depth (Localization.AtPrime P''.asIdeal)
          (maximalIdeal (Localization.AtPrime P''.asIdeal))
          (LocalizedModule P''.asIdeal.primeCompl (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
            (LocalizedModule q.asIdeal.primeCompl M'))) ∨
        enatToEInt (Module.depth (Localization.AtPrime P''.asIdeal)
            (maximalIdeal (Localization.AtPrime P''.asIdeal))
            (LocalizedModule P''.asIdeal.primeCompl (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
              (LocalizedModule q.asIdeal.primeCompl M')))) +
          krullDimToEInt (ringKrullDim (AdicCompletion (((I.ideal ⟨U, hU⟩).map
          (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (Localization.AtPrime q.asIdeal)))
            (Localization.AtPrime q.asIdeal) ⧸ P''.asIdeal)) > ((1 + d : ℤ) : EInt) := by
    intro P'' hP''I hfib
    have hPI : ¬ completedLocalIdeal I (completedAffinePoint hU q).1 ≤
        P''.asIdeal.comap (completedAffineRingEquiv hU q hqI) := fun hle =>
      hP''I (hI'.symm.trans_le (Ideal.map_le_iff_le_comap.mpr hle))
    have hfibP : adicClosedFibreThrough I (completedAffinePoint hU q).1
        (PrimeSpectrum.comap (completedAffineRingEquiv hU q hqI : _ →+* _) P'') ≠
        {completedMaximalIdeal I (completedAffinePoint hU q).1} :=
      mt (setOf_prime_comap_eq_singleton_iff_of_eq _ _ _ _ _ _ hI'
        (completedMaximalIdeal_eq_comap_completedAffineRingEquiv hU q hqI)).mp hfib
    have hdep := hc (completedAffinePoint hU q) hq.2 _ hPI hfibP
    have h1 := completedStalkDepth_comap_completedAffineRingEquiv hU q hqI F ε hε P''
    have h2 := depth_localized_completedAffine_eq hU π hπ e he q P''.asIdeal hP''I
    have hdim := ringKrullDim_quotient_comap_ringEquiv (completedAffineRingEquiv hU q hqI) P''
    rcases hdep with hd | hd
    · exact Or.inl (hd.trans_eq (h1.trans h2))
    · right
      have h3 := congrArg enatToEInt (h1.trans h2)
      have h4 := congrArg krullDimToEInt hdim
      exact lt_of_lt_of_eq hd (congrArg₂ (· + ·) h3 h4)
  have := hprime _ hpq
  have := hprime _ hrq
  have key := depth_or_depth_add_dim_of_adicCompletion hdualq _ hJ
    (LocalizedModule q.asIdeal.primeCompl M') d hcB _ _ hPR hPJ hRJ hRm
  have hdep := (Stacks.LocalCohomology.depth_localizedModule_localizationLocalization (M := M')
    q.asIdeal.primeCompl (p.asIdeal.map (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
      (Localization.AtPrime q.asIdeal)))).symm.trans (depth_atPrime_congr hPunder)
  rcases key with h | h
  · exact Or.inl (enatToEInt_mono (h.trans_eq hdep))
  · right
    rw [show (d + 1 : ℤ) = 1 + d by ring]
    exact lt_of_lt_of_eq h (congrArg (· + _) (congrArg enatToEInt hdep))

end Fields

end Stacks.Algebraization

end
