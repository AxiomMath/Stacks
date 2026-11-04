module

public import StacksFrontier.RingTheory.OrderOfVanishing.Norm
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.MinimalPrimeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.OrderOfVanishingDomain
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Index
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.RingTheory.Norm.BaseChangeProduct
public import StacksFrontier.RingTheory.OrderOfVanishing.RingEquivTransport
public import StacksFrontier.RingTheory.Length.FibreLengthSum
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Formula
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# The order of vanishing of a norm along the branches of a finite reduced extension

For a finite reduced algebra `D` over a reduced Noetherian local ring `O` of dimension one, the
order of vanishing of a norm is computed branch by branch: along each minimal prime `P` of `D`
over a minimal prime `Q` of `O`, and then summed over the maximal ideals of `D`, weighted by
residue degrees.

## Main definitions

* `branchNorm`: The norm `Nm_{Frac(D ⧸ P) / Frac(O ⧸ Q)}` along a branch.
* `quotientDegree`: The residue degree of a prime of `D` over a prime of `O`.
* `ordAtPrime`: The order of vanishing of a fraction of `C` at a prime of `C`.

## Main results

* `ordTotalFracInt_eq_finsum_maximalSpectrum`: `ord_O(σ) = ∑_m [κ(m) : κ(O)] · ord_{D_m}(τ)`
  when `σ` is the product of the branch norms of `τ`.
* `ordTotalFracInt_eq_finsum_of_isPushout`: The same formula when the generic fibres are base
  changes of a finite field extension.
* `ordTotalFracInt_atPrime_eq_finsum`: The corresponding formula at a prime of a reduced
  Noetherian base ring.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors TensorProduct
open IsLocalRing CategoryTheory

universe u

namespace Stacks.NormBranches

/-! ### Transport of `ordInt` between two localizations at one prime -/

/-- For two localizations `R₁`, `R₂` of a domain `R` at the same prime, and embeddings of `K`
into their fraction fields compatible with `R`, the orders of vanishing of the images of `t` in
`R₁` and in `R₂` agree. -/
theorem ordInt_eq_of_isLocalization_atPrime {R : Type u} [CommRing R] [IsDomain R]
    (𝔪 : Ideal R) [𝔪.IsPrime] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] [Algebra R R₁] [Algebra R R₂]
    [IsLocalization.AtPrime R₁ 𝔪] [IsLocalization.AtPrime R₂ 𝔪]
    [IsDomain R₁] [IsDomain R₂]
    [IsNoetherianRing R₁] [Ring.KrullDimLE 1 R₁] [IsNoetherianRing R₂] [Ring.KrullDimLE 1 R₂]
    {K₁ K₂ : Type u} [Field K₁] [Field K₂] [Algebra R₁ K₁] [IsFractionRing R₁ K₁]
    [Algebra R₂ K₂] [IsFractionRing R₂ K₂]
    (ψ₁ : K →+* K₁) (ψ₂ : K →+* K₂)
    (hψ₁ : ∀ r : R, ψ₁ (algebraMap R K r) = algebraMap R₁ K₁ (algebraMap R R₁ r))
    (hψ₂ : ∀ r : R, ψ₂ (algebraMap R K r) = algebraMap R₂ K₂ (algebraMap R R₂ r))
    (t : K) (h₁ : ψ₁ t ≠ 0) (h₂ : ψ₂ t ≠ 0) :
    ordInt R₁ (ψ₁ t) h₁ = ordInt R₂ (ψ₂ t) h₂ := by
  let e : R₁ ≃+* R₂ := (IsLocalization.algEquiv 𝔪.primeCompl R₁ R₂).toRingEquiv
  let E : K₁ ≃+* K₂ := IsFractionRing.ringEquivOfRingEquiv e
  have hE : ∀ r : R₁, E (algebraMap R₁ K₁ r) = algebraMap R₂ K₂ (e r) := fun r =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap e r
  have hcomp : (E : K₁ →+* K₂).comp ψ₁ = ψ₂ := by
    refine IsLocalization.ringHom_ext R⁰ (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [hψ₁, hψ₂, hE]
    congr 1
    exact (IsLocalization.algEquiv 𝔪.primeCompl R₁ R₂).commutes r
  have hEt : E (ψ₁ t) = ψ₂ t := RingHom.congr_fun hcomp t
  have := Stacks.Chow.ordInt_congr e E hE (ψ₁ t) h₁ (by rwa [hEt])
  rw [← this]
  congr 1

/-! ### The order of vanishing extended by zero -/

section OrdIntZ

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsDomain R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

open Classical in
/-- `ordInt` extended by `0` at `0`. -/
def ordIntZ (x : K) : ℤ := if hx : x = 0 then 0 else ordInt R x hx

/-- On a nonzero element, `ordIntZ` is `ordInt`. -/
theorem ordIntZ_of_ne {x : K} (hx : x ≠ 0) : ordIntZ R x = ordInt R x hx := dite_eq_right hx

/-- The order of vanishing of `1` is `0`. -/
theorem ordIntZ_one : ordIntZ R (1 : K) = 0 := by
  rw [ordIntZ_of_ne R one_ne_zero]
  have h := ordInt_mul R (1 : K) 1 one_ne_zero one_ne_zero
  have h' : ordInt R ((1 : K) * 1) (mul_ne_zero one_ne_zero one_ne_zero) =
      ordInt R (1 : K) one_ne_zero := by
    congr 1
    exact mul_one 1
  omega

/-- `ordIntZ` is additive on products of nonzero elements. -/
theorem ordIntZ_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordIntZ R (x * y) = ordIntZ R x + ordIntZ R y := by
  rw [ordIntZ_of_ne R (mul_ne_zero hx hy), ordIntZ_of_ne R hx, ordIntZ_of_ne R hy]
  exact ordInt_mul R x y hx hy

/-- `ordIntZ` of a finite product of nonzero elements is the sum of the `ordIntZ`. -/
theorem ordIntZ_prod {ι : Type*} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, f i ≠ 0) :
    ordIntZ R (∏ i ∈ s, f i) = ∑ i ∈ s, ordIntZ R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ordIntZ_one R
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ordIntZ_mul R (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- `ordIntZ` of a finite product, indexed by a finite type, of nonzero elements is the sum of
the `ordIntZ`. -/
theorem ordIntZ_finprod {ι : Type*} [Finite ι] (f : ι → K) (hf : ∀ i, f i ≠ 0) :
    ordIntZ R (∏ᶠ i, f i) = ∑ᶠ i, ordIntZ R (f i) := by
  have := Fintype.ofFinite ι
  rw [finprod_eq_prod_of_fintype, finsum_eq_sum_of_fintype]
  exact ordIntZ_prod R _ f fun i _ => hf i

end OrdIntZ

/-- A finite sum over a subtype is the sum of the dependent extension by zero. -/
theorem finsum_subtype_eq_finsum_dite {α M : Type*} [AddCommMonoid M] (p : α → Prop)
    [DecidablePred p] (g : Subtype p → M) :
    ∑ᶠ x, g x = ∑ᶠ a, if h : p a then g ⟨a, h⟩ else 0 := by
  have h1 : ∀ a, (if h : p a then g ⟨a, h⟩ else 0) =
      ∑ᶠ (_ : p a), (if h : p a then g ⟨a, h⟩ else 0) := fun a => by
    by_cases ha : p a
    · rw [finsum_eq_dif, dite_eq_left ha, dite_eq_left ha]
    · rw [dite_eq_right ha, finsum_eq_dif, dite_eq_right ha]
  rw [finsum_congr h1, ← finsum_subtype_eq_finsum_cond p]
  exact finsum_congr fun x => by rw [dite_eq_left x.2]

/-! ### Quotients of localizations at a prime -/

section QuotientLocalization

variable {D : Type u} [CommRing D]

/-- The image of a prime containing `P` in `D ⧸ P` is prime. -/
theorem isPrime_map_quotient (P m : Ideal D) [m.IsPrime] (hPm : P ≤ m) :
    (m.map (Ideal.Quotient.mk P)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

/-- The image in `D ⧸ P` of the complement of a prime `m ⊇ P` is the complement of the image
of `m`. -/
theorem algebraMapSubmonoid_quotient_primeCompl (P m : Ideal D) [m.IsPrime] (hPm : P ≤ m) :
    haveI := isPrime_map_quotient P m hPm
    Algebra.algebraMapSubmonoid (D ⧸ P) m.primeCompl =
      (m.map (Ideal.Quotient.mk P)).primeCompl := by
  have := isPrime_map_quotient P m hPm
  ext x
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · rintro ⟨d', hd', hdd'⟩
    show ¬ _ ∈ _
    rw [← hdd']
    show ¬ Ideal.Quotient.mk P d' ∈ _
    rw [SetLike.mem_coe, Ideal.mem_quotient_iff_mem hPm]
    exact hd'
  · exact fun hd => ⟨d, (Ideal.mem_quotient_iff_mem hPm).not.mp hd, rfl⟩

/-- **A quotient of a localization at a prime is a localization of the quotient.** For primes
`P ⊆ m` of `D`, the ring `D_m ⧸ P D_m` is a localization of `D ⧸ P` at the image of `m`. -/
theorem isLocalization_atPrime_quotient_map (P m : Ideal D) [m.IsPrime] (hPm : P ≤ m) :
    haveI := isPrime_map_quotient P m hPm
    IsLocalization.AtPrime (Localization.AtPrime m ⧸ P.map (algebraMap D (Localization.AtPrime m)))
      (m.map (Ideal.Quotient.mk P)) := by
  have := isPrime_map_quotient P m hPm
  have h := (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (D ⧸ P) m.primeCompl)
    (Localization.AtPrime m ⧸ P.map (algebraMap D (Localization.AtPrime m))))
  rwa [algebraMapSubmonoid_quotient_primeCompl P m hPm] at h

end QuotientLocalization

/-! ### A branch of a finite extension -/

section Branch

variable {O D : Type u} [CommRing O] [CommRing D] [Algebra O D]

/-- The map `O ⧸ Q → D ⧸ P` along a branch `P` of `D` over a prime `Q` of `O`. -/
abbrev branchQuotientMap (Q : Ideal O) (P : Ideal D) (h : P.comap (algebraMap O D) = Q) :
    O ⧸ Q →+* D ⧸ P :=
  Ideal.quotientMap P (algebraMap O D) h.ge

/-- The map `O ⧸ Q → D ⧸ P` along a branch is injective. -/
theorem branchQuotientMap_injective (Q : Ideal O) (P : Ideal D)
    (h : P.comap (algebraMap O D) = Q) : Function.Injective (branchQuotientMap Q P h) :=
  Ideal.quotientMap_injective' h.le

/-- The extension of fraction fields `Frac(O ⧸ Q) → Frac(D ⧸ P)` along a branch. -/
abbrev branchFracMap (Q : Ideal O) [Q.IsPrime] (P : Ideal D) [P.IsPrime]
    (h : P.comap (algebraMap O D) = Q) : FractionRing (O ⧸ Q) →+* FractionRing (D ⧸ P) :=
  IsFractionRing.map (branchQuotientMap_injective Q P h)

/-- **The norm along a branch**: `Nm_{Frac(D ⧸ P) / Frac(O ⧸ Q)}`. -/
def branchNorm (Q : Ideal O) [Q.IsPrime] (P : Ideal D) [P.IsPrime]
    (h : P.comap (algebraMap O D) = Q) (t : FractionRing (D ⧸ P)) : FractionRing (O ⧸ Q) :=
  letI := (branchFracMap Q P h).toAlgebra
  Algebra.norm (FractionRing (O ⧸ Q)) t

/-- The residue degree `[D ⧸ P : O ⧸ p]` of a prime `P` of `D` over a prime `p` of `O`, and `0`
off the fibre. -/
def quotientDegree (p : Ideal O) (P : Ideal D) : ℕ :=
  if h : P.comap (algebraMap O D) = p then
    letI := Ideal.Quotient.algebraQuotientOfLEComap h.ge
    Module.finrank (O ⧸ p) (D ⧸ P)
  else 0

/-- The Krull dimension of a localization at a prime is at most that of the ring. -/
theorem krullDimLE_localization_atPrime {R : Type u} [CommRing R] [Ring.KrullDimLE 1 R]
    (m : Ideal R) [m.IsPrime] : Ring.KrullDimLE 1 (Localization.AtPrime m) := by
  rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height m]
  exact le_trans Ideal.height_le_ringKrullDim_of_isPrime
    (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 R))

/-- The minimal prime of `D_m` cut out by a minimal prime `P ⊆ m` of `D`. -/
abbrev localizedMinimalPrime (P : minimalPrimes D) (m : Ideal D) [m.IsPrime] (hm : P.1 ≤ m) :
    minimalPrimes (Localization.AtPrime m) :=
  ⟨P.1.map (algebraMap D (Localization.AtPrime m)),
    Stacks.MinimalPrimeResidueLocalization.map_mem_minimalPrimes D m.primeCompl
      (Localization.AtPrime m) P.2 (Set.disjoint_left.mpr fun _ hx hxP => hx (hm hxP))⟩

/-- The image of a fraction of `D` in the total ring of fractions of `D_m`. -/
abbrev localizedFraction (m : Ideal D) [m.IsPrime] :
    FractionRing D →+* FractionRing (Localization.AtPrime m) :=
  IsLocalization.map _ (algebraMap D (Localization.AtPrime m))
    (IsLocalization.nonZeroDivisors_le_comap m.primeCompl (Localization.AtPrime m))

/-- The maximal ideal of a quotient of a local ring is the image of the maximal ideal. -/
theorem maximalIdeal_quotient_eq_map [IsLocalRing O] (Q : Ideal O) [Q.IsPrime] :
    haveI : IsLocalRing (O ⧸ Q) := .of_surjective' _ Ideal.Quotient.mk_surjective
    maximalIdeal (O ⧸ Q) = (maximalIdeal O).map (Ideal.Quotient.mk Q) := by
  have : IsLocalRing (O ⧸ Q) := .of_surjective' _ Ideal.Quotient.mk_surjective
  exact (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm

/-- The residue degree of `m.map (D → D ⧸ P)` over the maximal ideal of `O ⧸ Q` is the residue
degree of `m` over the maximal ideal of `O`. -/
theorem quotientDegree_branch_eq [IsLocalRing O] (Q : Ideal O) [Q.IsPrime] (P : Ideal D)
    [P.IsPrime] (h : P.comap (algebraMap O D) = Q) (m : Ideal D) [m.IsMaximal] (hPm : P ≤ m)
    (hm : m.comap (algebraMap O D) = maximalIdeal O) :
    letI := (branchQuotientMap Q P h).toAlgebra
    haveI : IsLocalRing (O ⧸ Q) := .of_surjective' _ Ideal.Quotient.mk_surjective
    quotientDegree (maximalIdeal (O ⧸ Q)) (m.map (Ideal.Quotient.mk P)) =
      quotientDegree (maximalIdeal O) m := by
  let := (branchQuotientMap Q P h).toAlgebra
  have : IsLocalRing (O ⧸ Q) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hQm : Q ≤ maximalIdeal O := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have hmax := maximalIdeal_quotient_eq_map Q
  have hc : (m.map (Ideal.Quotient.mk P)).comap (algebraMap (O ⧸ Q) (D ⧸ P)) =
      maximalIdeal (O ⧸ Q) := by
    rw [hmax]
    ext x
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_comap, Ideal.mem_quotient_iff_mem hQm]
    show Ideal.Quotient.mk P (algebraMap O D o) ∈ _ ↔ _
    rw [Ideal.mem_quotient_iff_mem hPm, ← Ideal.mem_comap, hm]
  rw [quotientDegree, dite_eq_left hc, quotientDegree, dite_eq_left hm]
  let := Ideal.Quotient.algebraQuotientOfLEComap hc.ge
  let := Ideal.Quotient.algebraQuotientOfLEComap hm.ge
  refine Algebra.finrank_eq_of_equiv_equiv
    ((Ideal.quotEquivOfEq hmax).trans (DoubleQuot.quotQuotEquivQuotOfLE hQm))
    (DoubleQuot.quotQuotEquivQuotOfLE hPm) ?_
  refine RingHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- **The order of vanishing along a branch, read on the quotient or on the localization.** For a
minimal prime `P ⊆ m` of `D`, the order of vanishing in the localization of `D ⧸ P` at the image
of `m` of the image of a fraction `τ` of `D` is the order of vanishing of `τ` along the branch of
`D_m` through `P`. -/
theorem ordInt_localization_quotient_eq_minimalPrimeOrd [IsNoetherianRing D]
    [Ring.KrullDimLE 1 D] (P : minimalPrimes D) (m : Ideal D) [m.IsPrime] (hPm : P.1 ≤ m)
    [(m.map (Ideal.Quotient.mk P.1)).IsPrime]
    [Algebra (Localization.AtPrime (m.map (Ideal.Quotient.mk P.1))) (FractionRing (D ⧸ P.1))]
    [IsScalarTower (D ⧸ P.1) (Localization.AtPrime (m.map (Ideal.Quotient.mk P.1)))
      (FractionRing (D ⧸ P.1))]
    [IsFractionRing (Localization.AtPrime (m.map (Ideal.Quotient.mk P.1)))
      (FractionRing (D ⧸ P.1))]
    [Ring.KrullDimLE 1 (Localization.AtPrime (m.map (Ideal.Quotient.mk P.1)))]
    (τ : FractionRing D) (hτ : IsUnit τ) (hne : Ring.minimalPrimeFractionMap P τ ≠ 0) :
    haveI := krullDimLE_localization_atPrime m
    haveI : P.1.IsPrime := P.2.1.1
    ordInt (Localization.AtPrime (m.map (Ideal.Quotient.mk P.1)))
        (Ring.minimalPrimeFractionMap P τ) hne =
      Ring.minimalPrimeOrd (localizedMinimalPrime P m hPm) (localizedFraction m τ)
        (hτ.map _) := by
  have := krullDimLE_localization_atPrime m
  have : P.1.IsPrime := P.2.1.1
  have : (P.1.map (algebraMap D (Localization.AtPrime m))).IsPrime :=
    (localizedMinimalPrime P m hPm).2.1.1
  have := Ring.krullDimLE_one_quotient (O := Localization.AtPrime m)
    (P.1.map (algebraMap D (Localization.AtPrime m)))
  have := isLocalization_atPrime_quotient_map P.1 m hPm
  let R₂ := Localization.AtPrime m ⧸ P.1.map (algebraMap D (Localization.AtPrime m))
  have hinj : Function.Injective (algebraMap (D ⧸ P.1) R₂) :=
    IsLocalization.injective (M := (m.map (Ideal.Quotient.mk P.1)).primeCompl) R₂
      (Ideal.primeCompl_le_nonZeroDivisors _)
  let ψ₂ : FractionRing (D ⧸ P.1) →+* FractionRing R₂ := IsFractionRing.map hinj
  have hψ : ψ₂ (Ring.minimalPrimeFractionMap P τ) =
      Ring.minimalPrimeFractionMap (localizedMinimalPrime P m hPm) (localizedFraction m τ) := by
    have hext : ψ₂.comp (Ring.minimalPrimeFractionMap (K := FractionRing D) P) =
        (Ring.minimalPrimeFractionMap (K := FractionRing (Localization.AtPrime m))
          (localizedMinimalPrime P m hPm)).comp (localizedFraction m) := by
      refine IsLocalization.ringHom_ext D⁰ (RingHom.ext fun d => ?_)
      show ψ₂ (Ring.minimalPrimeFractionMap P (algebraMap D (FractionRing D) d)) =
        Ring.minimalPrimeFractionMap (localizedMinimalPrime P m hPm)
          (localizedFraction m (algebraMap D (FractionRing D) d))
      rw [Ring.minimalPrimeFractionMap, Ring.minimalPrimeFractionMap, localizedFraction,
        IsLocalization.map_eq, IsLocalization.map_eq, IsLocalization.map_eq]
      exact IsLocalization.map_eq (S := FractionRing (D ⧸ P.1)) (Q := FractionRing R₂)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj) _
    exact RingHom.congr_fun hext τ
  have hne₂ : ψ₂ (Ring.minimalPrimeFractionMap P τ) ≠ 0 := by
    rw [hψ]
    exact ((hτ.map (localizedFraction m)).map _).ne_zero
  have key := ordInt_eq_of_isLocalization_atPrime (m.map (Ideal.Quotient.mk P.1))
    (K := FractionRing (D ⧸ P.1)) (R₁ := Localization.AtPrime (m.map (Ideal.Quotient.mk P.1)))
    (R₂ := R₂) (K₁ := FractionRing (D ⧸ P.1)) (K₂ := FractionRing R₂) (RingHom.id _) ψ₂
    (fun r => IsScalarTower.algebraMap_apply _ _ _ r)
    (fun r => IsLocalization.map_eq (S := FractionRing (D ⧸ P.1)) (Q := FractionRing R₂)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj) r)
    (Ring.minimalPrimeFractionMap P τ) hne hne₂
  refine key.trans ?_
  unfold Ring.minimalPrimeOrd
  exact Ring.ordTotalFracInt_congr _ (isUnit_iff_ne_zero.mpr hne₂) _ hψ

/-- The maximal ideals of `D ⧸ P` are the maximal ideals of `D` containing `P`. -/
def maximalSpectrumQuotientEquiv (P : Ideal D) :
    MaximalSpectrum (D ⧸ P) ≃ {m : MaximalSpectrum D // P ≤ m.asIdeal} where
  toFun v := ⟨⟨v.asIdeal.comap (Ideal.Quotient.mk P),
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩, fun x hx => by
    change Ideal.Quotient.mk P x ∈ v.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact v.asIdeal.zero_mem⟩
  invFun m := ⟨m.1.asIdeal.map (Ideal.Quotient.mk P), by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      m.1.isMaximal).resolve_left fun htop => ?_
    have h1 := congrArg (Ideal.comap (Ideal.Quotient.mk P)) htop
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_top,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr m.2] at h1
    exact m.1.isMaximal.ne_top h1⟩
  left_inv v := MaximalSpectrum.ext
    (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective v.asIdeal)
  right_inv m := Subtype.ext (MaximalSpectrum.ext (by
    change Ideal.comap _ (Ideal.map _ _) = _
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr m.2]))

/-- The finite `O`-algebra `D` gives a finite `O ⧸ Q`-algebra `D ⧸ P` along a branch. -/
private theorem finite_quotient_branch [Module.Finite O D] (Q : Ideal O) (P : Ideal D)
    (h : P.comap (algebraMap O D) = Q) :
    letI := (branchQuotientMap Q P h).toAlgebra
    Module.Finite (O ⧸ Q) (D ⧸ P) := by
  let : Algebra (O ⧸ Q) (D ⧸ P) := (branchQuotientMap Q P h).toAlgebra
  have : IsScalarTower O (O ⧸ Q) (D ⧸ P) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite O (D ⧸ P) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ O P).toLinearMap Ideal.Quotient.mk_surjective
  exact Module.Finite.of_restrictScalars_finite O _ _

/-- The fraction field map along a branch is compatible with the quotient map. -/
private theorem isScalarTower_branchFrac (Q : Ideal O) [Q.IsPrime] (P : Ideal D) [P.IsPrime]
    (h : P.comap (algebraMap O D) = Q) :
    letI := (branchQuotientMap Q P h).toAlgebra
    letI := (branchFracMap Q P h).toAlgebra
    IsScalarTower (O ⧸ Q) (FractionRing (O ⧸ Q)) (FractionRing (D ⧸ P)) := by
  let : Algebra (O ⧸ Q) (D ⧸ P) := (branchQuotientMap Q P h).toAlgebra
  let : Algebra (FractionRing (O ⧸ Q)) (FractionRing (D ⧸ P)) := (branchFracMap Q P h).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply (O ⧸ Q) (D ⧸ P) (FractionRing (D ⧸ P))]
    exact (IsLocalization.map_eq (S := FractionRing (O ⧸ Q)) (M := (O ⧸ Q)⁰)
      (T := (D ⧸ P)⁰) (Q := FractionRing (D ⧸ P))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (branchQuotientMap_injective Q P h)) a).symm

section Main

variable [IsLocalRing O] [IsNoetherianRing O] [Ring.KrullDimLE 1 O] [Module.Finite O D]

/-- **Stacks 02MJ along one branch.** Let `O` be a Noetherian local ring of dimension at most one,
`D` a finite `O`-algebra, `P` a minimal prime of `D` over the prime `Q` of `O`, and `τ` a unit of
the total ring of fractions of `D`. Then the order of vanishing along `O ⧸ Q` of the norm of the
image of `τ` in `Frac(D ⧸ P)` is the sum, over the maximal ideals `m ⊇ P` of `D`, of the residue
degree of `m` times the order of vanishing of `τ` along the branch of `D_m` through `P`. -/
theorem ordInt_branchNorm_eq_finsum [IsNoetherianRing D] [Ring.KrullDimLE 1 D] (Q : Ideal O)
    [Q.IsPrime] (P : Ideal D) [P.IsPrime] (hP : P ∈ minimalPrimes D)
    (h : P.comap (algebraMap O D) = Q) (τ : FractionRing D) (hτ : IsUnit τ)
    (hny : branchNorm Q P h (Ring.minimalPrimeFractionMap ⟨P, hP⟩ τ) ≠ 0) :
    haveI := Ring.krullDimLE_one_quotient (O := O) Q
    ordInt (O ⧸ Q) (branchNorm Q P h (Ring.minimalPrimeFractionMap ⟨P, hP⟩ τ)) hny =
      ∑ᶠ x : {m : MaximalSpectrum D // P ≤ m.asIdeal},
        (quotientDegree (maximalIdeal O) x.1.asIdeal : ℤ) *
          (haveI := krullDimLE_localization_atPrime x.1.asIdeal
          Ring.minimalPrimeOrd (localizedMinimalPrime ⟨P, hP⟩ x.1.asIdeal x.2)
            (localizedFraction x.1.asIdeal τ) (hτ.map _)) := by
  have := Ring.krullDimLE_one_quotient (O := O) Q
  let : Algebra (O ⧸ Q) (D ⧸ P) := (branchQuotientMap Q P h).toAlgebra
  have : IsLocalRing (O ⧸ Q) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have := finite_quotient_branch Q P h
  let : Algebra (FractionRing (O ⧸ Q)) (FractionRing (D ⧸ P)) := (branchFracMap Q P h).toAlgebra
  have := isScalarTower_branchFrac Q P h
  have : Algebra.IsIntegral (O ⧸ Q) (D ⧸ P) := Algebra.IsIntegral.of_finite _ _
  have : Finite (MaximalSpectrum (D ⧸ P)) := Stacks.Length.finite_maximalSpectrum (A := O ⧸ Q)
  let : Fintype (MaximalSpectrum (D ⧸ P)) := Fintype.ofFinite _
  have : Ring.DimensionLEOne (O ⧸ Q) :=
    ⟨fun {q} hq _ => Ideal.isMaximal_of_isPrime_of_ne_bot q hq⟩
  have : Ring.DimensionLEOne (D ⧸ P) := Ring.DimensionLEOne.of_isIntegral (R := O ⧸ Q) (D ⧸ P)
  let hLv : ∀ v : MaximalSpectrum (D ⧸ P),
      Algebra (Localization.AtPrime v.asIdeal) (FractionRing (D ⧸ P)) := fun v =>
    IsLocalization.localizationAlgebraOfSubmonoidLe
        (Localization.AtPrime v.asIdeal) (FractionRing (D ⧸ P)) v.asIdeal.primeCompl
        (nonZeroDivisors (D ⧸ P)) v.asIdeal.primeCompl_le_nonZeroDivisors
  have : ∀ v : MaximalSpectrum (D ⧸ P),
      IsScalarTower (D ⧸ P) (Localization.AtPrime v.asIdeal) (FractionRing (D ⧸ P)) := fun v =>
    IsLocalization.localization_isScalarTower_of_submonoid_le
        (Localization.AtPrime v.asIdeal) (FractionRing (D ⧸ P)) v.asIdeal.primeCompl
        (nonZeroDivisors (D ⧸ P)) v.asIdeal.primeCompl_le_nonZeroDivisors
  have : ∀ v : MaximalSpectrum (D ⧸ P),
      IsFractionRing (Localization.AtPrime v.asIdeal) (FractionRing (D ⧸ P)) := fun v =>
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.asIdeal.primeCompl
      (Localization.AtPrime v.asIdeal) (FractionRing (D ⧸ P))
  have : ∀ v : MaximalSpectrum (D ⧸ P), Ring.KrullDimLE 1 (Localization.AtPrime v.asIdeal) :=
    fun v => krullDimLE_localization_atPrime v.asIdeal
  have hy : Ring.minimalPrimeFractionMap ⟨P, hP⟩ τ ≠ 0 := (hτ.map _).ne_zero
  refine (ord_norm_eq_sum_inertiaDeg_mul_ord (O ⧸ Q) (D ⧸ P) (FractionRing (O ⧸ Q))
    (FractionRing (D ⧸ P)) (branchQuotientMap_injective Q P h) _ hy _ rfl hny).trans ?_
  rw [← finsum_eq_sum_of_fintype, ← finsum_comp_equiv (maximalSpectrumQuotientEquiv P).symm]
  refine finsum_congr fun x => ?_
  have hxm : x.1.asIdeal.comap (algebraMap O D) = maximalIdeal O :=
    Stacks.Length.comap_asIdeal_eq_maximalIdeal (A := O) x.1
  have : (x.1.asIdeal.map (Ideal.Quotient.mk P)).IsPrime := isPrime_map_quotient P x.1.asIdeal x.2
  let v := (maximalSpectrumQuotientEquiv P).symm x
  let : Algebra (Localization.AtPrime (x.1.asIdeal.map (Ideal.Quotient.mk P)))
      (FractionRing (D ⧸ P)) := hLv v
  have : IsScalarTower (D ⧸ P) (Localization.AtPrime (x.1.asIdeal.map (Ideal.Quotient.mk P)))
      (FractionRing (D ⧸ P)) := (inferInstance : ∀ v : MaximalSpectrum (D ⧸ P),
        IsScalarTower (D ⧸ P) (Localization.AtPrime v.asIdeal) (FractionRing (D ⧸ P))) v
  have : IsFractionRing (Localization.AtPrime (x.1.asIdeal.map (Ideal.Quotient.mk P)))
      (FractionRing (D ⧸ P)) := (inferInstance : ∀ v : MaximalSpectrum (D ⧸ P),
        IsFractionRing (Localization.AtPrime v.asIdeal) (FractionRing (D ⧸ P))) v
  have : Ring.KrullDimLE 1 (Localization.AtPrime (x.1.asIdeal.map (Ideal.Quotient.mk P))) :=
    krullDimLE_localization_atPrime _
  congr 1
  · exact_mod_cast quotientDegree_branch_eq Q P h x.1.asIdeal x.2 hxm
  · exact ordInt_localization_quotient_eq_minimalPrimeOrd ⟨P, hP⟩ x.1.asIdeal x.2 τ hτ hy

omit [IsNoetherianRing O] in
/-- The extension of fraction fields along a branch is finite. -/
theorem finite_branchFrac (Q : Ideal O) [Q.IsPrime] (P : Ideal D) [P.IsPrime]
    (h : P.comap (algebraMap O D) = Q) :
    letI := (branchFracMap Q P h).toAlgebra
    Module.Finite (FractionRing (O ⧸ Q)) (FractionRing (D ⧸ P)) := by
  have := Ring.krullDimLE_one_quotient (O := O) Q
  let : Algebra (O ⧸ Q) (D ⧸ P) := (branchQuotientMap Q P h).toAlgebra
  have : IsLocalRing (O ⧸ Q) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have := finite_quotient_branch Q P h
  let : Algebra (FractionRing (O ⧸ Q)) (FractionRing (D ⧸ P)) := (branchFracMap Q P h).toAlgebra
  have := isScalarTower_branchFrac Q P h
  exact finiteDimensional_fractionRing_of_finite (O ⧸ Q) (D ⧸ P) _ _
    (branchQuotientMap_injective Q P h)

omit [IsNoetherianRing O] in
/-- The norm along a branch of a nonzero element is nonzero. -/
theorem branchNorm_ne_zero (Q : Ideal O) [Q.IsPrime] (P : Ideal D) [P.IsPrime]
    (h : P.comap (algebraMap O D) = Q) {t : FractionRing (D ⧸ P)} (ht : t ≠ 0) :
    branchNorm Q P h t ≠ 0 := by
  let := (branchFracMap Q P h).toAlgebra
  have := finite_branchFrac Q P h
  have : Module.Free (FractionRing (O ⧸ Q)) (FractionRing (D ⧸ P)) :=
    Module.Free.of_divisionRing _ _
  exact Algebra.norm_ne_zero_iff.mpr ht

end Main

/-! ### Summing over the branches -/

section Assembly

variable [IsNoetherianRing D] [Ring.KrullDimLE 1 D]

open Classical in
/-- The order of vanishing of `τ` along the branch of `D_m` through a minimal prime `P` of `D`,
and `0` when `P ⊄ m`. -/
def branchOrd (P : minimalPrimes D) (m : MaximalSpectrum D) (τ : FractionRing D)
    (hτ : IsUnit τ) : ℤ :=
  if h : P.1 ≤ m.asIdeal then
    haveI := krullDimLE_localization_atPrime m.asIdeal
    Ring.minimalPrimeOrd (localizedMinimalPrime P m.asIdeal h) (localizedFraction m.asIdeal τ)
      (hτ.map _)
  else 0

open Classical in
/-- The norm along the branch `P` over `Q`, and `1` when `P` does not lie over `Q`. -/
def branchNormOf (Q : minimalPrimes O) (P : minimalPrimes D) (τ : FractionRing D) :
    FractionRing (O ⧸ Q.1) :=
  haveI := Q.2.1.1
  haveI := P.2.1.1
  if h : P.1.comap (algebraMap O D) = Q.1 then
    branchNorm Q.1 P.1 h (Ring.minimalPrimeFractionMap P τ)
  else 1

variable [IsLocalRing O] [IsNoetherianRing O] [Ring.KrullDimLE 1 O] [Module.Finite O D]

omit [IsNoetherianRing D] [Ring.KrullDimLE 1 D] [IsNoetherianRing O] in
/-- The norm along a branch of a unit of the total ring of fractions is nonzero. -/
theorem branchNormOf_ne_zero (Q : minimalPrimes O) (P : minimalPrimes D) (τ : FractionRing D)
    (hτ : IsUnit τ) : branchNormOf Q P τ ≠ 0 := by
  have := Q.2.1.1
  have := P.2.1.1
  unfold branchNormOf
  split_ifs with h
  · exact branchNorm_ne_zero Q.1 P.1 h ((hτ.map _).ne_zero)
  · exact one_ne_zero

/-- Stacks 02MJ along one branch, summed over all maximal ideals. -/
theorem ordIntZ_branchNormOf (Q : minimalPrimes O) (P : minimalPrimes D) (τ : FractionRing D)
    (hτ : IsUnit τ) :
    haveI := Q.2.1.1
    haveI := Ring.krullDimLE_one_quotient (O := O) Q.1
    ordIntZ (O ⧸ Q.1) (branchNormOf Q P τ) =
      if P.1.comap (algebraMap O D) = Q.1 then
        ∑ᶠ m : MaximalSpectrum D, (quotientDegree (maximalIdeal O) m.asIdeal : ℤ) *
          branchOrd P m τ hτ
      else 0 := by
  classical
  have := Q.2.1.1
  have := P.2.1.1
  have := Ring.krullDimLE_one_quotient (O := O) Q.1
  by_cases h : P.1.comap (algebraMap O D) = Q.1
  · rw [ite_eq_left h, ordIntZ_of_ne _ (branchNormOf_ne_zero Q P τ hτ)]
    have hb : branchNormOf Q P τ = branchNorm Q.1 P.1 h (Ring.minimalPrimeFractionMap P τ) := by
      unfold branchNormOf
      rw [dite_eq_left h]
    have hne := branchNorm_ne_zero Q.1 P.1 h ((hτ.map (Ring.minimalPrimeFractionMap P)).ne_zero)
    rw [show ordInt (O ⧸ Q.1) (branchNormOf Q P τ) (branchNormOf_ne_zero Q P τ hτ) =
      ordInt (O ⧸ Q.1) (branchNorm Q.1 P.1 h (Ring.minimalPrimeFractionMap P τ)) hne by
        congr 1]
    rw [ordInt_branchNorm_eq_finsum Q.1 P.1 P.2 h τ hτ hne,
      finsum_subtype_eq_finsum_dite (fun m : MaximalSpectrum D => P.1 ≤ m.asIdeal)]
    refine finsum_congr fun m => ?_
    unfold branchOrd
    split_ifs with hm
    · rfl
    · rw [mul_zero]
  · rw [ite_eq_right h]
    have hb : branchNormOf Q P τ = 1 := by
      unfold branchNormOf
      rw [dite_eq_right h]
    rw [hb]
    exact ordIntZ_one _

/-- **The order of vanishing at a maximal ideal, over the branches.** For `D` reduced and `D_m` of
dimension one, the order of vanishing of `τ` in `D_m` is the sum over the minimal primes `P` of `D`
of the order of vanishing along the branch through `P`. -/
theorem ordTotalFracInt_localization_eq_finsum_branchOrd [IsReduced D] (m : MaximalSpectrum D)
    (hdim : ringKrullDim (Localization.AtPrime m.asIdeal) = 1) (τ : FractionRing D)
    (hτ : IsUnit τ) :
    haveI := krullDimLE_localization_atPrime m.asIdeal
    Ring.ordTotalFracInt (Localization.AtPrime m.asIdeal) (localizedFraction m.asIdeal τ)
        (hτ.map _) =
      ∑ᶠ P : minimalPrimes D, branchOrd P m τ hτ := by
  classical
  have := krullDimLE_localization_atPrime m.asIdeal
  rw [Ring.ordTotalFracInt_eq_finsum_minimalPrimeOrd hdim,
    ← finsum_comp_equiv (Stacks.MinimalPrimeResidueLocalization.minimalPrimesEquivDisjoint D
      m.asIdeal.primeCompl (Localization.AtPrime m.asIdeal)).symm,
    finsum_subtype_eq_finsum_dite]
  refine finsum_congr fun P => ?_
  have hiff : Disjoint (m.asIdeal.primeCompl : Set D) ((P : Ideal D) : Set D) ↔
      P.1 ≤ m.asIdeal := by
    refine ⟨fun hd x hx => ?_, fun hle => Set.disjoint_left.mpr fun _ hx hxP => hx (hle hxP)⟩
    by_contra hxm
    exact Set.disjoint_left.mp hd hxm hx
  unfold branchOrd
  by_cases hP : P.1 ≤ m.asIdeal
  · rw [dite_eq_left (hiff.mpr hP), dite_eq_left hP]
    rfl
  · rw [dite_eq_right (fun h => hP (hiff.mp h)), dite_eq_right hP]

omit [IsNoetherianRing D] [IsNoetherianRing O] [Ring.KrullDimLE 1 O] in
/-- The local rings of `D` at its maximal ideals are one-dimensional, when `O` is and the minimal
primes of `D` lie over minimal primes of `O`. -/
theorem ringKrullDim_localization_eq_one (hO : ringKrullDim O = 1)
    (htf : ∀ P ∈ minimalPrimes D, P.comap (algebraMap O D) ∈ minimalPrimes O)
    (m : MaximalSpectrum D) : ringKrullDim (Localization.AtPrime m.asIdeal) = 1 := by
  have : Algebra.IsIntegral O D := Algebra.IsIntegral.of_finite _ _
  have hcomap : m.asIdeal.comap (algebraMap O D) = maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) m.asIdeal)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal]
  have hle : (m.asIdeal.height : WithBot ℕ∞) ≤ 1 :=
    le_trans Ideal.height_le_ringKrullDim_of_isPrime
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 D))
  have hne : m.asIdeal.height ≠ 0 := by
    intro h0
    have hmin := htf _ (Ideal.height_eq_zero_iff.mp h0)
    rw [hcomap] at hmin
    have h1 := Ideal.height_eq_zero_iff.mpr hmin
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h1] at hO
    exact absurd hO (by decide)
  rw [le_antisymm (by exact_mod_cast hle) (Order.one_le_iff_ne_zero.mpr hne)]
  rfl

/-- **The order of vanishing of a norm over a finite reduced extension of a reduced local ring.**
Let `O` be a reduced Noetherian local ring of dimension one and `D` a finite reduced `O`-algebra
whose minimal primes lie over minimal primes of `O`. Let `σ` and `τ` be units of the total rings
of fractions of `O` and `D` such that, at every minimal prime `Q` of `O`, the image of `σ` in
`Frac(O ⧸ Q)` is the product of the norms of the images of `τ` along the branches `P` of `D`
over `Q`. Then

`ord_O(σ) = ∑_m [κ(m) : κ(O)] · ord_{D_m}(τ)`,

the sum over the maximal ideals of `D`. -/
theorem ordTotalFracInt_eq_finsum_maximalSpectrum [IsReduced O] [IsReduced D]
    (hO : ringKrullDim O = 1)
    (htf : ∀ P ∈ minimalPrimes D, P.comap (algebraMap O D) ∈ minimalPrimes O)
    (σ : FractionRing O) (hσ : IsUnit σ) (τ : FractionRing D) (hτ : IsUnit τ)
    (hnorm : ∀ Q : minimalPrimes O,
      Ring.minimalPrimeFractionMap Q σ = ∏ᶠ P : minimalPrimes D, branchNormOf Q P τ) :
    Ring.ordTotalFracInt O σ hσ =
      ∑ᶠ m : MaximalSpectrum D, (quotientDegree (maximalIdeal O) m.asIdeal : ℤ) *
        (haveI := krullDimLE_localization_atPrime m.asIdeal
        Ring.ordTotalFracInt (Localization.AtPrime m.asIdeal) (localizedFraction m.asIdeal τ)
          (hτ.map _)) := by
  classical
  have : Finite (minimalPrimes O) := (minimalPrimes.finite_of_isNoetherianRing O).to_subtype
  have : Finite (minimalPrimes D) := (minimalPrimes.finite_of_isNoetherianRing D).to_subtype
  have : Finite (MaximalSpectrum D) := Stacks.Length.finite_maximalSpectrum (A := O)
  let := Fintype.ofFinite (minimalPrimes O)
  let := Fintype.ofFinite (minimalPrimes D)
  let := Fintype.ofFinite (MaximalSpectrum D)
  have hQ : ∀ Q : minimalPrimes O, Ring.minimalPrimeOrd Q σ hσ =
      ∑ P : minimalPrimes D, if P.1.comap (algebraMap O D) = Q.1 then
        ∑ m : MaximalSpectrum D, (quotientDegree (maximalIdeal O) m.asIdeal : ℤ) *
          branchOrd P m τ hτ else 0 := by
    intro Q
    have := Q.2.1.1
    have := Ring.krullDimLE_one_quotient (O := O) Q.1
    have h1 : Ring.minimalPrimeOrd Q σ hσ =
        ordIntZ (O ⧸ Q.1) (Ring.minimalPrimeFractionMap Q σ) := by
      rw [ordIntZ_of_ne _ (hσ.map (Ring.minimalPrimeFractionMap Q)).ne_zero]
      rfl
    rw [h1, hnorm Q, ordIntZ_finprod _ _ fun P => branchNormOf_ne_zero Q P τ hτ,
      finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [ordIntZ_branchNormOf Q P τ hτ, finsum_eq_sum_of_fintype]
  rw [Ring.ordTotalFracInt_eq_finsum_minimalPrimeOrd hO, finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl fun Q _ => hQ Q, Finset.sum_comm, finsum_eq_sum_of_fintype]
  have hP : ∀ P : minimalPrimes D, (∑ Q : minimalPrimes O,
      if P.1.comap (algebraMap O D) = Q.1 then
        ∑ m : MaximalSpectrum D, (quotientDegree (maximalIdeal O) m.asIdeal : ℤ) *
          branchOrd P m τ hτ else 0) =
      ∑ m : MaximalSpectrum D, (quotientDegree (maximalIdeal O) m.asIdeal : ℤ) *
          branchOrd P m τ hτ := by
    intro P
    rw [Finset.sum_eq_single_of_mem (⟨P.1.comap (algebraMap O D), htf P.1 P.2⟩ : minimalPrimes O)
      (Finset.mem_univ _), ite_eq_left rfl]
    exact fun Q _ hQne => ite_eq_right fun hc => hQne (Subtype.ext hc.symm)
  rw [Finset.sum_congr rfl fun P _ => hP P, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.mul_sum, ordTotalFracInt_localization_eq_finsum_branchOrd m
    (ringKrullDim_localization_eq_one hO htf m) τ hτ, finsum_eq_sum_of_fintype]

end Assembly

end Branch

/-! ### The generic fibre of a branch -/

section GenericFibre

/-- The map `R ⧸ p → R_p` at a minimal prime `p` of a reduced ring: `p R_p` is the maximal ideal
of the field `R_p`, hence zero. -/
def quotientToAtPrime {R : Type u} [CommRing R] [IsReduced R] {p : Ideal R} [p.IsPrime]
    (hp : p ∈ minimalPrimes R) : R ⧸ p →+* Localization.AtPrime p :=
  Ideal.Quotient.lift p (algebraMap R (Localization.AtPrime p)) fun x hx => by
    let := (isField_localizationAtPrime_of_minimal R p hp).toField
    have h1 : algebraMap R (Localization.AtPrime p) x ∈ maximalIdeal (Localization.AtPrime p) := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
      exact Ideal.mem_map_of_mem _ hx
    rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h1

/-- `quotientToAtPrime` sends the class of `x` to the image of `x` in `R_p`. -/
theorem quotientToAtPrime_mk {R : Type u} [CommRing R] [IsReduced R] {p : Ideal R} [p.IsPrime]
    (hp : p ∈ minimalPrimes R) (x : R) :
    quotientToAtPrime hp (Ideal.Quotient.mk p x) = algebraMap R (Localization.AtPrime p) x := rfl

/-- The map `R ⧸ p → R_p` at a minimal prime of a reduced ring is injective. -/
theorem quotientToAtPrime_injective {R : Type u} [CommRing R] [IsReduced R] {p : Ideal R}
    [p.IsPrime] (hp : p ∈ minimalPrimes R) : Function.Injective (quotientToAtPrime hp) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [quotientToAtPrime_mk] at hy
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ x).mp hy
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have : (s : R) * x ∈ p := by simp [hs]
  exact (‹p.IsPrime›.mem_or_mem this).resolve_left s.2

/-- **The localization of a reduced ring at a minimal prime `p` is the fraction field of
`R ⧸ p`.** -/
theorem isFractionRing_quotient_atPrime {R : Type u} [CommRing R] [IsReduced R] {p : Ideal R}
    [p.IsPrime] (hp : p ∈ minimalPrimes R) :
    letI := (quotientToAtPrime hp).toAlgebra
    letI := (isField_localizationAtPrime_of_minimal R p hp).toField
    IsFractionRing (R ⧸ p) (Localization.AtPrime p) := by
  let := (quotientToAtPrime hp).toAlgebra
  let := (isField_localizationAtPrime_of_minimal R p hp).toField
  have : FaithfulSMul (R ⧸ p) (Localization.AtPrime p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (quotientToAtPrime_injective hp)
  refine IsFractionRing.of_field (R ⧸ p) (Localization.AtPrime p) fun z => ?_
  obtain ⟨x, hx⟩ := IsLocalization.surj p.primeCompl z
  have hsm : algebraMap (R ⧸ p) (Localization.AtPrime p) (Ideal.Quotient.mk p (x.2 : R)) ≠ 0 :=
    fun h => x.2.2 (Ideal.Quotient.eq_zero_iff_mem.mp
      (quotientToAtPrime_injective hp (h.trans (map_zero _).symm)))
  exact ⟨Ideal.Quotient.mk p x.1, Ideal.Quotient.mk p (x.2 : R), (eq_div_iff hsm).2 hx⟩

/-- **The norm of a base change, on a reduced generic fibre.** If `T` is the base change of a
finite field extension `L / K` along `K → F`, with `F` a field and `T` reduced, then the image in
`F` of the norm `Nm_{L/K}(t)` is the product, over the maximal ideals `q` of `T`, of the norms over
`F` of the images of `t` in the residue fields `T ⧸ q`. -/
theorem algebraMap_norm_eq_prod_norm_quotient (K L F T : Type u) [Field K] [Field L] [Field F]
    [CommRing T] [Algebra K L] [Algebra K F] [Algebra K T] [Algebra L T] [Algebra F T]
    [IsScalarTower K L T] [IsScalarTower K F T] [Algebra.IsPushout K F L T]
    [Module.Finite K L] [IsReduced T] [Fintype (MaximalSpectrum T)] (t : L) :
    haveI : Module.Finite F T := Module.Finite.equiv (Algebra.IsPushout.equiv K F L T).toLinearEquiv
    algebraMap K F (Algebra.norm K t) =
      ∏ q : MaximalSpectrum T, Algebra.norm F (Ideal.Quotient.mk q.asIdeal (algebraMap L T t)) := by
  let e : (F ⊗[K] L) ≃ₐ[F] T := Algebra.IsPushout.equiv K F L T
  have : Module.Finite F T := Module.Finite.equiv e.toLinearEquiv
  rw [← Stacks.Norm.norm_eq_prod_quotient (algebraMap L T t),
    ← Stacks.Norm.norm_tmul_one (A := F) t, ← Algebra.norm_eq_of_algEquiv e (1 ⊗ₜ[K] t)]
  congr 1
  rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]

section Fibre

variable {O D : Type u} [CommRing O] [CommRing D] [Algebra O D] [Module.Finite O D]
  (Q : minimalPrimes O)

/-- The image in `D` of the complement of a minimal prime `Q` of `O`. -/
abbrev fibreSubmonoid : Submonoid D :=
  haveI := Q.2.1.1
  Algebra.algebraMapSubmonoid D Q.1.primeCompl

omit [Module.Finite O D] in
/-- A prime of `D` is disjoint from the image of `O ∖ Q` exactly when it contracts into `Q`. -/
theorem disjoint_algebraMapSubmonoid_iff (P : Ideal D) :
    haveI := Q.2.1.1
    Disjoint (fibreSubmonoid (D := D) Q : Set D) (P : Set D) ↔ P.comap (algebraMap O D) ≤ Q.1 := by
  have := Q.2.1.1
  refine ⟨fun hd o ho => ?_, fun hle => Set.disjoint_left.mpr ?_⟩
  · by_contra hoQ
    exact Set.disjoint_left.mp hd ⟨o, hoQ, rfl⟩ ho
  · rintro _ ⟨o, ho, rfl⟩ hoP
    exact ho (hle hoP)

/-- A prime of `D` contracting into the minimal prime `Q` contracts to `Q` and is minimal, when
the minimal primes of `D` lie over minimal primes of `O`. -/
theorem comap_eq_and_mem_minimalPrimes
    (_htf : ∀ P ∈ minimalPrimes D, P.comap (algebraMap O D) ∈ minimalPrimes O)
    (P : Ideal D) [P.IsPrime] (hle : P.comap (algebraMap O D) ≤ Q.1) :
    P.comap (algebraMap O D) = Q.1 ∧ P ∈ minimalPrimes D := by
  have : Algebra.IsIntegral O D := Algebra.IsIntegral.of_finite _ _
  have hQ : P.comap (algebraMap O D) = Q.1 :=
    le_antisymm hle (Q.2.2 ⟨Ideal.IsPrime.comap _, bot_le⟩ hle)
  refine ⟨hQ, ?_⟩
  obtain ⟨P₀, hP₀, hle₀⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal D) ≤ P)
  have : P₀.IsPrime := hP₀.1.1
  have hc₀ : P₀.comap (algebraMap O D) = Q.1 :=
    le_antisymm ((Ideal.comap_mono hle₀).trans hle)
      (Q.2.2 ⟨Ideal.IsPrime.comap _, bot_le⟩ ((Ideal.comap_mono hle₀).trans hle))
  rcases hle₀.lt_or_eq with hlt | heq
  · have := Ideal.IsIntegral.comap_lt_comap (R := O) hlt
    rw [hc₀, hQ] at this
    exact absurd this (lt_irrefl _)
  · rw [← heq]
    exact hP₀

variable (htf : ∀ P ∈ minimalPrimes D, P.comap (algebraMap O D) ∈ minimalPrimes O)
include htf

/-- The expansion to `D_Q` of a minimal prime of `D` over `Q` is maximal. -/
theorem isMaximal_map_fibre (P : minimalPrimes D) (hP : P.1.comap (algebraMap O D) = Q.1) :
    (P.1.map (algebraMap D (Localization (fibreSubmonoid (D := D) Q)))).IsMaximal := by
  have := P.2.1.1
  have hd : Disjoint (fibreSubmonoid (D := D) Q : Set D) (P.1 : Set D) :=
    (disjoint_algebraMapSubmonoid_iff Q P.1).mpr hP.le
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint (fibreSubmonoid (D := D) Q)
    (Localization (fibreSubmonoid (D := D) Q)) P.1 P.2.1.1 hd
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hprime.ne_top
  have hmd := (IsLocalization.isPrime_iff_isPrime_disjoint (fibreSubmonoid (D := D) Q)
    (Localization (fibreSubmonoid (D := D) Q)) m).mp hm.isPrime
  have := hmd.1
  have hmc := comap_eq_and_mem_minimalPrimes Q htf (m.under D)
    ((disjoint_algebraMapSubmonoid_iff Q _).mp hmd.2)
  have hPm : P.1 ≤ m.under D := fun _ hx => hle (Ideal.mem_map_of_mem _ hx)
  have heq : m.under D = P.1 := le_antisymm (hmc.2.2 ⟨P.2.1.1, bot_le⟩ hPm) hPm
  rwa [← heq, IsLocalization.map_under (fibreSubmonoid (D := D) Q)]

/-- **The maximal ideals of the generic fibre `D_Q` are the minimal primes of `D` over `Q`.** -/
def maximalSpectrumFibreEquiv :
    MaximalSpectrum (Localization (fibreSubmonoid (D := D) Q)) ≃
      {P : minimalPrimes D // P.1.comap (algebraMap O D) = Q.1} where
  toFun q :=
    haveI := ((IsLocalization.isPrime_iff_isPrime_disjoint (fibreSubmonoid (D := D) Q)
      (Localization (fibreSubmonoid (D := D) Q)) q.asIdeal).mp q.isMaximal.isPrime).1
    have h := comap_eq_and_mem_minimalPrimes Q htf (q.asIdeal.under D)
      ((disjoint_algebraMapSubmonoid_iff Q _).mp
        ((IsLocalization.isPrime_iff_isPrime_disjoint (fibreSubmonoid (D := D) Q)
          (Localization (fibreSubmonoid (D := D) Q)) q.asIdeal).mp q.isMaximal.isPrime).2)
    ⟨⟨q.asIdeal.under D, h.2⟩, h.1⟩
  invFun P := ⟨P.1.1.map (algebraMap D _), isMaximal_map_fibre Q htf P.1 P.2⟩
  left_inv _ := MaximalSpectrum.ext (IsLocalization.map_under (fibreSubmonoid (D := D) Q) _ _)
  right_inv P := Subtype.ext (Subtype.ext (IsLocalization.under_map_of_isPrime_disjoint
    (fibreSubmonoid (D := D) Q) _ P.1.2.1.1
    ((disjoint_algebraMapSubmonoid_iff Q P.1.1).mpr P.2.le)))

/-- **The residue field of the generic fibre `D_Q` at a branch `P` is `Frac(D ⧸ P)`.** -/
theorem isFractionRing_quotient_fibre (P : minimalPrimes D)
    (hP : P.1.comap (algebraMap O D) = Q.1) :
    haveI := P.2.1.1
    haveI := isMaximal_map_fibre Q htf P hP
    letI := Ideal.Quotient.field
      (P.1.map (algebraMap D (Localization (fibreSubmonoid (D := D) Q))))
    IsFractionRing (D ⧸ P.1) (Localization (fibreSubmonoid (D := D) Q) ⧸
      P.1.map (algebraMap D (Localization (fibreSubmonoid (D := D) Q)))) := by
  have := P.2.1.1
  have := isMaximal_map_fibre Q htf P hP
  let := Ideal.Quotient.field
    (P.1.map (algebraMap D (Localization (fibreSubmonoid (D := D) Q))))
  set T := Localization (fibreSubmonoid (D := D) Q)
  have hM : Algebra.algebraMapSubmonoid (D ⧸ P.1) (fibreSubmonoid (D := D) Q) ≤
      (D ⧸ P.1)⁰ := by
    rintro _ ⟨_, ⟨o, ho, rfl⟩, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ho ?_
    rw [← hP, SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hinj : Function.Injective (algebraMap (D ⧸ P.1) (T ⧸ P.1.map (algebraMap D T))) :=
    IsLocalization.injective (M := Algebra.algebraMapSubmonoid (D ⧸ P.1)
      (fibreSubmonoid (D := D) Q)) _ hM
  have : FaithfulSMul (D ⧸ P.1) (T ⧸ P.1.map (algebraMap D T)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field (D ⧸ P.1) _ fun z => ?_
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid (D ⧸ P.1)
    (fibreSubmonoid (D := D) Q)) z
  have hs : algebraMap (D ⧸ P.1) (T ⧸ P.1.map (algebraMap D T)) (s : D ⧸ P.1) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (D ⧸ P.1) (T ⧸ P.1.map (algebraMap D T)))]
    exact fun h => nonZeroDivisors.ne_zero (hM s.2) (hinj h)
  exact ⟨x, s, (eq_div_iff hs).2 hx⟩

end Fibre

/-- A finite product over a subtype is the product of the dependent extension by one. -/
theorem finprod_subtype_eq_finprod_dite {α M : Type*} [CommMonoid M] (p : α → Prop)
    [DecidablePred p] (g : Subtype p → M) :
    ∏ᶠ x, g x = ∏ᶠ a, if h : p a then g ⟨a, h⟩ else 1 := by
  have h1 : ∀ a, (if h : p a then g ⟨a, h⟩ else 1) =
      ∏ᶠ (_ : p a), (if h : p a then g ⟨a, h⟩ else 1) := fun a => by
    by_cases ha : p a
    · rw [finprod_eq_dif, dite_eq_left ha, dite_eq_left ha]
    · rw [dite_eq_right ha, finprod_eq_dif, dite_eq_right ha]
  rw [finprod_congr h1, ← finprod_subtype_eq_finprod_cond p]
  exact finprod_congr fun x => by rw [dite_eq_left x.2]

section NormFibre

variable {O D : Type u} [CommRing O] [CommRing D] [Algebra O D] [Module.Finite O D]
  [IsReduced O] [IsReduced D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D]
  (htf : ∀ P ∈ minimalPrimes D, P.comap (algebraMap O D) ∈ minimalPrimes O)

/-- The field `O_Q` at a minimal prime `Q` of `O`. -/
abbrev fibreField (Q : minimalPrimes O) : Type u :=
  haveI := Q.2.1.1
  Localization.AtPrime Q.1

/-- The generic fibre `D_Q` of `D` over a minimal prime `Q` of `O`. -/
abbrev fibreRing (Q : minimalPrimes O) : Type u := Localization (fibreSubmonoid (D := D) Q)

/-- The map `Q(O) → O_Q`. -/
def locFracO (Q : minimalPrimes O) : FractionRing O →+* fibreField Q :=
  haveI := Q.2.1.1
  IsLocalization.lift (M := O⁰) (g := algebraMap O (fibreField Q)) fun y =>
    IsLocalization.map_units (M := Q.1.primeCompl) (fibreField Q)
      ⟨(y : O), fun hy => notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hy Q.2 y.2⟩

omit [IsReduced O] in
/-- `locFracO` sends the image of `o ∈ O` to the image of `o` in `O_Q`. -/
theorem locFracO_algebraMap (Q : minimalPrimes O) (o : O) :
    locFracO Q (algebraMap O (FractionRing O) o) = algebraMap O (fibreField Q) o :=
  IsLocalization.lift_eq _ _

include htf in
omit [IsReduced O] [IsReduced D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- A nonzerodivisor of `D` is a unit in the generic fibre `D_Q`. -/
theorem isUnit_algebraMap_fibreRing (Q : minimalPrimes O) (y : D⁰) :
    IsUnit (algebraMap D (fibreRing (D := D) Q) y) := by
  by_contra hy
  obtain ⟨m, hm, hym⟩ := exists_max_ideal_of_mem_nonunits (show
    algebraMap D (fibreRing (D := D) Q) y ∈ nonunits _ from hy)
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (show (y : D) ∈ m.under D from hym)
    (maximalSpectrumFibreEquiv Q htf ⟨m, hm⟩).1.2 y.2

/-- The map `Q(D) → D_Q`. -/
def locFracD (Q : minimalPrimes O) : FractionRing D →+* fibreRing (D := D) Q :=
  IsLocalization.lift (M := D⁰) (g := algebraMap D (fibreRing (D := D) Q))
    (isUnit_algebraMap_fibreRing htf Q)

omit [IsReduced O] [IsReduced D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- `locFracD` sends the image of `d ∈ D` to the image of `d` in `D_Q`. -/
theorem locFracD_algebraMap (Q : minimalPrimes O) (d : D) :
    locFracD htf Q (algebraMap D (FractionRing D) d) = algebraMap D (fibreRing (D := D) Q) d :=
  IsLocalization.lift_eq _ _

/-- The identification `Frac(O ⧸ Q) ≃ O_Q` at a minimal prime. -/
def fracQuotEquivFibreField (Q : minimalPrimes O) :
    haveI := Q.2.1.1
    FractionRing (O ⧸ Q.1) ≃+* fibreField Q :=
  haveI := Q.2.1.1
  letI := (quotientToAtPrime Q.2).toAlgebra
  letI := (isField_localizationAtPrime_of_minimal O Q.1 Q.2).toField
  haveI := isFractionRing_quotient_atPrime Q.2
  (FractionRing.algEquiv (O ⧸ Q.1) (fibreField Q)).toRingEquiv

/-- `fracQuotEquivFibreField` sends the class of `o ∈ O` to the image of `o` in `O_Q`. -/
theorem fracQuotEquivFibreField_algebraMap (Q : minimalPrimes O) (o : O) :
    haveI := Q.2.1.1
    fracQuotEquivFibreField Q (algebraMap (O ⧸ Q.1) (FractionRing (O ⧸ Q.1))
      (Ideal.Quotient.mk Q.1 o)) = algebraMap O (fibreField Q) o := by
  have := Q.2.1.1
  let := (quotientToAtPrime Q.2).toAlgebra
  let := (isField_localizationAtPrime_of_minimal O Q.1 Q.2).toField
  have := isFractionRing_quotient_atPrime Q.2
  exact (FractionRing.algEquiv (O ⧸ Q.1) (fibreField Q)).commutes _

/-- The image of a fraction of `O` in `Frac(O ⧸ Q)` corresponds to its image in `O_Q`. -/
theorem fracQuotEquivFibreField_minimalPrimeFractionMap (Q : minimalPrimes O)
    (σ : FractionRing O) :
    fracQuotEquivFibreField Q (Ring.minimalPrimeFractionMap Q σ) = locFracO Q σ := by
  have := Q.2.1.1
  have h : ((fracQuotEquivFibreField Q : FractionRing (O ⧸ Q.1) →+* fibreField Q).comp
      (Ring.minimalPrimeFractionMap (K := FractionRing O) Q)) = locFracO Q := by
    refine IsLocalization.ringHom_ext O⁰ (RingHom.ext fun o => ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [Ring.minimalPrimeFractionMap, IsLocalization.map_eq, fracQuotEquivFibreField_algebraMap,
      locFracO_algebraMap]
  exact RingHom.congr_fun h σ

include htf in
/-- The identification `Frac(D ⧸ P) ≃ D_Q ⧸ P D_Q` at a minimal prime `P` of `D` over `Q`. -/
def fracQuotEquivFibreQuot (Q : minimalPrimes O) (P : minimalPrimes D)
    (hP : P.1.comap (algebraMap O D) = Q.1) :
    haveI := P.2.1.1
    FractionRing (D ⧸ P.1) ≃+* fibreRing (D := D) Q ⧸
      P.1.map (algebraMap D (fibreRing (D := D) Q)) :=
  haveI := P.2.1.1
  haveI := isMaximal_map_fibre Q htf P hP
  letI := Ideal.Quotient.field (P.1.map (algebraMap D (fibreRing (D := D) Q)))
  haveI := isFractionRing_quotient_fibre Q htf P hP
  (FractionRing.algEquiv (D ⧸ P.1) _).toRingEquiv

omit [IsReduced O] [IsReduced D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- `fracQuotEquivFibreQuot` sends the class of `d ∈ D` to the class of the image of `d` in
`D_Q ⧸ P D_Q`. -/
theorem fracQuotEquivFibreQuot_algebraMap (Q : minimalPrimes O) (P : minimalPrimes D)
    (hP : P.1.comap (algebraMap O D) = Q.1) (d : D) :
    haveI := P.2.1.1
    fracQuotEquivFibreQuot htf Q P hP (algebraMap (D ⧸ P.1) (FractionRing (D ⧸ P.1))
      (Ideal.Quotient.mk P.1 d)) =
        Ideal.Quotient.mk _ (algebraMap D (fibreRing (D := D) Q) d) := by
  have := P.2.1.1
  have := isMaximal_map_fibre Q htf P hP
  let := Ideal.Quotient.field (P.1.map (algebraMap D (fibreRing (D := D) Q)))
  have := isFractionRing_quotient_fibre Q htf P hP
  exact (FractionRing.algEquiv (D ⧸ P.1) _).commutes _

omit [IsReduced O] [IsReduced D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- The image of a fraction `τ` of `D` in `Frac(D ⧸ P)` corresponds to the class in
`D_Q ⧸ P D_Q` of its image in `D_Q`. -/
theorem fracQuotEquivFibreQuot_minimalPrimeFractionMap (Q : minimalPrimes O)
    (P : minimalPrimes D) (hP : P.1.comap (algebraMap O D) = Q.1) (τ : FractionRing D) :
    fracQuotEquivFibreQuot htf Q P hP (Ring.minimalPrimeFractionMap P τ) =
      Ideal.Quotient.mk _ (locFracD htf Q τ) := by
  have := P.2.1.1
  have h : ((fracQuotEquivFibreQuot htf Q P hP).toRingHom.comp
      (Ring.minimalPrimeFractionMap (K := FractionRing D) P)) =
      (Ideal.Quotient.mk (P.1.map (algebraMap D (fibreRing (D := D) Q)))).comp
        (locFracD htf Q) := by
    refine IsLocalization.ringHom_ext D⁰ (RingHom.ext fun d => ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [Ring.minimalPrimeFractionMap, IsLocalization.map_eq, fracQuotEquivFibreQuot_algebraMap,
      locFracD_algebraMap]
  exact RingHom.congr_fun h τ

omit [IsReduced D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D] in
/-- **The norm along a branch, read in the generic fibre.** -/
theorem branchNorm_eq_fibre (Q : minimalPrimes O) (P : minimalPrimes D)
    (hP : P.1.comap (algebraMap O D) = Q.1) (t : FractionRing (D ⧸ P.1)) :
    haveI := Q.2.1.1
    haveI := P.2.1.1
    letI := (isField_localizationAtPrime_of_minimal O Q.1 Q.2).toField
    branchNorm Q.1 P.1 hP t = (fracQuotEquivFibreField Q).symm
      (Algebra.norm (fibreField Q) (fracQuotEquivFibreQuot htf Q P hP t)) := by
  have := Q.2.1.1
  have := P.2.1.1
  let := (isField_localizationAtPrime_of_minimal O Q.1 Q.2).toField
  let := (branchFracMap Q.1 P.1 hP).toAlgebra
  refine Algebra.norm_eq_of_equiv_equiv (fracQuotEquivFibreField Q)
    (fracQuotEquivFibreQuot htf Q P hP) ?_ t
  refine IsLocalization.ringHom_ext (O ⧸ Q.1)⁰
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun o => ?_))
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  rw [fracQuotEquivFibreField_algebraMap]
  show _ = fracQuotEquivFibreQuot htf Q P hP (branchFracMap Q.1 P.1 hP
    (algebraMap (O ⧸ Q.1) (FractionRing (O ⧸ Q.1)) (Ideal.Quotient.mk Q.1 o)))
  rw [branchFracMap, IsFractionRing.map, IsLocalization.map_eq]
  show _ = fracQuotEquivFibreQuot htf Q P hP (algebraMap (D ⧸ P.1) (FractionRing (D ⧸ P.1))
    (Ideal.Quotient.mk P.1 (algebraMap O D o)))
  rw [fracQuotEquivFibreQuot_algebraMap, ← Ideal.Quotient.mk_algebraMap,
    ← IsScalarTower.algebraMap_apply O (fibreField Q) (fibreRing (D := D) Q),
    IsScalarTower.algebraMap_apply O D (fibreRing (D := D) Q)]

omit [Ring.KrullDimLE 1 D] in
/-- **The norm identity over a minimal prime, from the generic fibre.** Let `Q` be a minimal prime
of `O`, and suppose the generic fibre `D_Q` is the base change of a finite field extension `L/K`
along a homomorphism `κ : K → O_Q`, through `λ : L → D_Q`. If `σ ∈ Q(O)` reads as `κ(Nm_{L/K}(t))`
in `O_Q` and `τ ∈ Q(D)` reads as `λ(t)` in `D_Q`, then the image of `σ` in `Frac(O ⧸ Q)` is the
product over the branches `P` of `D` over `Q` of the norms of the images of `τ`. -/
theorem minimalPrimeFractionMap_eq_finprod_branchNormOf (Q : minimalPrimes O) (K L : Type u)
    [Field K] [Field L] [Algebra K L] [Module.Finite K L] (κ : K →+* fibreField Q)
    (lam : L →+* fibreRing (D := D) Q)
    (hpush : IsPushout (CommRingCat.ofHom κ) (CommRingCat.ofHom (algebraMap K L))
      (CommRingCat.ofHom (algebraMap (fibreField Q) (fibreRing (D := D) Q)))
      (CommRingCat.ofHom lam))
    (σ : FractionRing O) (τ : FractionRing D) (t : L)
    (hσt : locFracO Q σ = κ (Algebra.norm K t)) (hτt : locFracD htf Q τ = lam t) :
    Ring.minimalPrimeFractionMap Q σ = ∏ᶠ P : minimalPrimes D, branchNormOf Q P τ := by
  classical
  have := Q.2.1.1
  let : Field (fibreField Q) := (isField_localizationAtPrime_of_minimal O Q.1 Q.2).toField
  let : Algebra K (fibreField Q) := κ.toAlgebra
  let : Algebra L (fibreRing (D := D) Q) := lam.toAlgebra
  let : Algebra K (fibreRing (D := D) Q) :=
    ((algebraMap (fibreField Q) (fibreRing (D := D) Q)).comp κ).toAlgebra
  have : IsScalarTower K (fibreField Q) (fibreRing (D := D) Q) := .of_algebraMap_eq' rfl
  have hw : (algebraMap (fibreField Q) (fibreRing (D := D) Q)).comp κ =
      lam.comp (algebraMap K L) := by
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
      using congrArg CommRingCat.Hom.hom hpush.w
  have : IsScalarTower K L (fibreRing (D := D) Q) := .of_algebraMap_eq' hw
  have : Algebra.IsPushout K (fibreField Q) L (fibreRing (D := D) Q) :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  have : Finite (minimalPrimes D) := (minimalPrimes.finite_of_isNoetherianRing D).to_subtype
  have : Finite (MaximalSpectrum (fibreRing (D := D) Q)) :=
    Finite.of_equiv _ (maximalSpectrumFibreEquiv Q htf).symm
  let := Fintype.ofFinite (MaximalSpectrum (fibreRing (D := D) Q))
  have hcore := algebraMap_norm_eq_prod_norm_quotient K L (fibreField Q) (fibreRing (D := D) Q) t
  rw [← (fracQuotEquivFibreField Q).symm_apply_apply (Ring.minimalPrimeFractionMap Q σ),
    fracQuotEquivFibreField_minimalPrimeFractionMap, hσt]
  show (fracQuotEquivFibreField Q).symm (algebraMap K (fibreField Q) (Algebra.norm K t)) = _
  rw [hcore, map_prod, ← finprod_eq_prod_of_fintype,
    ← finprod_comp_equiv (maximalSpectrumFibreEquiv Q htf).symm, finprod_subtype_eq_finprod_dite]
  refine finprod_congr fun P => ?_
  have := P.2.1.1
  unfold branchNormOf
  by_cases hP : P.1.comap (algebraMap O D) = Q.1
  · rw [dite_eq_left hP, dite_eq_left hP, branchNorm_eq_fibre htf Q P hP,
      fracQuotEquivFibreQuot_minimalPrimeFractionMap, hτt]
    rfl
  · rw [dite_eq_right hP, dite_eq_right hP]

end NormFibre

end GenericFibre

/-! ### The order of vanishing of a norm, from the generic fibres -/

section Main

variable {O D : Type u} [CommRing O] [CommRing D] [Algebra O D] [IsLocalRing O]
  [IsNoetherianRing O] [Ring.KrullDimLE 1 O] [Module.Finite O D] [IsNoetherianRing D]
  [Ring.KrullDimLE 1 D] [IsReduced O] [IsReduced D]

/-- **The order of vanishing of a norm over a finite reduced extension of a reduced local ring of
dimension one, from the generic fibres.** Let `O` be a reduced Noetherian local ring of dimension
one, `D` a finite reduced `O`-algebra whose minimal primes lie over minimal primes of `O`, and
`L/K` a finite extension of fields. Suppose that at every minimal prime `Q` of `O` the generic
fibre `D_Q` is the base change of `L/K` along some `κ_Q : K → O_Q`, through `λ_Q : L → D_Q`, and
that `σ ∈ Q(O)`, `τ ∈ Q(D)` read as `κ_Q(Nm_{L/K}(t))` and `λ_Q(t)` there. Then

`ord_O(σ) = ∑_m [κ(m) : κ(O)] · ord_{D_m}(τ)`,

the sum over the maximal ideals of `D`. -/
theorem ordTotalFracInt_eq_finsum_of_isPushout (hO : ringKrullDim O = 1)
    (htf : ∀ P ∈ minimalPrimes D, P.comap (algebraMap O D) ∈ minimalPrimes O) (K L : Type u)
    [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    (κ : ∀ Q : minimalPrimes O, K →+* fibreField Q)
    (lam : ∀ Q : minimalPrimes O, L →+* fibreRing (D := D) Q)
    (hpush : ∀ Q : minimalPrimes O, IsPushout (CommRingCat.ofHom (κ Q))
      (CommRingCat.ofHom (algebraMap K L))
      (CommRingCat.ofHom (algebraMap (fibreField Q) (fibreRing (D := D) Q)))
      (CommRingCat.ofHom (lam Q)))
    (σ : FractionRing O) (hσ : IsUnit σ) (τ : FractionRing D) (hτ : IsUnit τ) (t : L)
    (hσt : ∀ Q : minimalPrimes O, locFracO Q σ = κ Q (Algebra.norm K t))
    (hτt : ∀ Q : minimalPrimes O, locFracD htf Q τ = lam Q t) :
    Ring.ordTotalFracInt O σ hσ =
      ∑ᶠ m : MaximalSpectrum D, (quotientDegree (maximalIdeal O) m.asIdeal : ℤ) *
        (haveI := krullDimLE_localization_atPrime m.asIdeal
        Ring.ordTotalFracInt (Localization.AtPrime m.asIdeal) (localizedFraction m.asIdeal τ)
          (hτ.map _)) :=
  ordTotalFracInt_eq_finsum_maximalSpectrum hO htf σ hσ τ hτ fun Q =>
    minimalPrimeFractionMap_eq_finprod_branchNormOf htf Q K L (κ Q) (lam Q) (hpush Q) σ τ t
      (hσt Q) (hτt Q)

end Main

/-! ### Transport between two models of a localization at a prime -/

section Transport

/-- The image of a fraction of `R` in the total ring of fractions of a localization of `R`. -/
abbrev fracMapOfLocalization {R : Type u} [CommRing R] (M : Submonoid R) (R₁ : Type u)
    [CommRing R₁] [Algebra R R₁] [IsLocalization M R₁] :
    FractionRing R →+* FractionRing R₁ :=
  IsLocalization.map _ (algebraMap R R₁) (IsLocalization.nonZeroDivisors_le_comap M R₁)

/-- **The order of vanishing does not depend on the model of the localization at a prime.** -/
theorem ordTotalFracInt_eq_of_isLocalization_atPrime {R : Type u} [CommRing R] (𝔮 : Ideal R)
    [𝔮.IsPrime] {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] [Algebra R R₁] [Algebra R R₂]
    [IsLocalization.AtPrime R₁ 𝔮] [IsLocalization.AtPrime R₂ 𝔮]
    [IsNoetherianRing R₁] [Ring.KrullDimLE 1 R₁] [Nontrivial R₁]
    [IsNoetherianRing R₂] [Ring.KrullDimLE 1 R₂] [Nontrivial R₂]
    (x : FractionRing R) (h₁ : IsUnit (fracMapOfLocalization 𝔮.primeCompl R₁ x))
    (h₂ : IsUnit (fracMapOfLocalization 𝔮.primeCompl R₂ x)) :
    Ring.ordTotalFracInt R₁ (fracMapOfLocalization 𝔮.primeCompl R₁ x) h₁ =
      Ring.ordTotalFracInt R₂ (fracMapOfLocalization 𝔮.primeCompl R₂ x) h₂ := by
  let e : R₁ ≃+* R₂ := (IsLocalization.algEquiv 𝔮.primeCompl R₁ R₂).toRingEquiv
  have hφ : R₁⁰ ≤ R₂⁰.comap (e : R₁ →+* R₂) := fun y hy =>
    (MulEquivClass.map_nonZeroDivisors e).le ⟨y, hy, rfl⟩
  have hφ' : R₂⁰ ≤ R₂⁰.comap (RingHom.id R₂) := fun y hy => hy
  refine Ring.ordTotalFracInt_eq_of_map_eq (C := R₂) (L := FractionRing R₂) (e : R₁ →+* R₂)
    (RingHom.id R₂) hφ hφ' (fun y => (Stacks.OrderOfVanishing.ord_eq_of_ringEquiv e y).symm)
    (fun _ => rfl) h₁ h₂ ?_
  have hext : (IsLocalization.map (T := R₂⁰) (FractionRing R₂) (e : R₁ →+* R₂) hφ).comp
      (fracMapOfLocalization 𝔮.primeCompl R₁) =
      (IsLocalization.map (T := R₂⁰) (FractionRing R₂) (RingHom.id R₂) hφ').comp
        (fracMapOfLocalization 𝔮.primeCompl R₂) := by
    refine IsLocalization.ringHom_ext R⁰ (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, fracMapOfLocalization, IsLocalization.map_eq]
    congr 1
    exact (IsLocalization.algEquiv 𝔮.primeCompl R₁ R₂).commutes r
  exact RingHom.congr_fun hext x

end Transport

/-! ### The global form: a finite reduced extension of a reduced ring, at a prime -/

section Global

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] [Module.Finite A C]
  [IsNoetherianRing A] [IsNoetherianRing C] [IsReduced A] [IsReduced C] (𝔭 : Ideal A)
  [𝔭.IsPrime]

open Classical in
/-- The order of vanishing of the image of a fraction of `C` in the localization of `C` at a
prime, and `0` if that local ring has dimension `> 1` or the image is not a unit. -/
def ordAtPrime (𝔮 : PrimeSpectrum C) (x : FractionRing C) : ℤ :=
  if h : Ring.KrullDimLE 1 (Localization.AtPrime 𝔮.asIdeal) ∧
      IsUnit (fracMapOfLocalization 𝔮.asIdeal.primeCompl (Localization.AtPrime 𝔮.asIdeal) x) then
    haveI := h.1
    Ring.ordTotalFracInt (Localization.AtPrime 𝔮.asIdeal) _ h.2
  else 0

include 𝔭 in
omit [Module.Finite A C] [IsNoetherianRing A] [IsNoetherianRing C] [IsReduced A] [IsReduced C] in
/-- The minimal primes of `C_𝔭` lie over minimal primes of `A_𝔭` when the minimal primes of `C`
lie over minimal primes of `A`. -/
theorem comap_mem_minimalPrimes_localization
    (htf : ∀ P ∈ minimalPrimes C, P.comap (algebraMap A C) ∈ minimalPrimes A) :
    ∀ P ∈ minimalPrimes (Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl)),
      P.comap (algebraMap (Localization.AtPrime 𝔭)
        (Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl))) ∈
        minimalPrimes (Localization.AtPrime 𝔭) := by
  intro P hP
  have := hP.1.1
  have hP₀ : P.comap (algebraMap C (Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl)))
      ∈ minimalPrimes C :=
    Stacks.MinimalPrimeResidueLocalization.under_mem_minimalPrimes C
      (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) _ hP
  have hQ₀ := htf _ hP₀
  have hdisj : Disjoint (𝔭.primeCompl : Set A)
      (((P.comap (algebraMap C (Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl)))).comap
        (algebraMap A C) : Ideal A) : Set A) := by
    rw [Set.disjoint_left]
    intro a ha haP
    have hu : IsUnit (algebraMap C (Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl))
        (algebraMap A C a)) :=
      IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl))
        (⟨algebraMap A C a, a, ha, rfl⟩ : Algebra.algebraMapSubmonoid C 𝔭.primeCompl)
    exact hP.1.1.ne_top (Ideal.eq_top_of_isUnit_mem _ haP hu)
  have hmem := Stacks.MinimalPrimeResidueLocalization.map_mem_minimalPrimes A 𝔭.primeCompl
    (Localization.AtPrime 𝔭) hQ₀ hdisj
  convert hmem using 1
  have : (P.comap (algebraMap (Localization.AtPrime 𝔭)
      (Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl)))).IsPrime :=
    Ideal.IsPrime.comap _
  rw [← IsLocalization.map_under 𝔭.primeCompl (Localization.AtPrime 𝔭)
    (P.comap (algebraMap (Localization.AtPrime 𝔭)
      (Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl))))]
  congr 1
  rw [Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, Ideal.comap_comap,
    ← IsScalarTower.algebraMap_eq]

local notation "Aₚ" => Localization.AtPrime 𝔭
local notation "Cₚ" => Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl)

omit [IsNoetherianRing A] [IsNoetherianRing C] [IsReduced A] [IsReduced C] in
/-- The residue degree of a maximal ideal of `C_𝔭` over `A_𝔭` is the residue degree of its
contraction to `C` over `𝔭`. -/
theorem quotientDegree_eq_primeResidueDegree (m : MaximalSpectrum Cₚ) :
    quotientDegree (maximalIdeal Aₚ) m.asIdeal =
      Stacks.Length.primeResidueDegree (algebraMap A C) 𝔭
        (m.asIdeal.comap (algebraMap C Cₚ)) := by
  have := Stacks.Length.isLocalHom_algebraMap_localization (A := Aₚ) m
  rw [← Stacks.Length.finrank_residueField_eq_primeResidueDegree 𝔭 m.asIdeal
    (Stacks.Length.comap_comap_asIdeal_eq 𝔭 m).symm]
  have hc : m.asIdeal.comap (algebraMap Aₚ Cₚ) = maximalIdeal Aₚ :=
    Stacks.Length.comap_asIdeal_eq_maximalIdeal m
  rw [quotientDegree, dite_eq_left hc]
  let := Ideal.Quotient.algebraQuotientOfLEComap hc.ge
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (IsLocalization.AtPrime.equivQuotMaximalIdeal m.asIdeal (Localization.AtPrime m.asIdeal)) ?_
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

omit [IsReduced A] [IsReduced C] in
omit [IsNoetherianRing A] in
/-- The order of vanishing at a maximal ideal of `C_𝔭` is the order of vanishing at its
contraction to `C`. -/
theorem ordTotalFracInt_localization_eq_ordAtPrime [Ring.KrullDimLE 1 Aₚ]
    (m : MaximalSpectrum Cₚ) (τ : FractionRing C) (hτ : IsUnit τ) :
    haveI : Ring.KrullDimLE 1 Cₚ := Stacks.Chow.krullDimLE_one_of_isIntegral Aₚ Cₚ
    haveI := krullDimLE_localization_atPrime m.asIdeal
    Ring.ordTotalFracInt (Localization.AtPrime m.asIdeal)
        (localizedFraction m.asIdeal
          (fracMapOfLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) Cₚ τ))
        ((hτ.map _).map _) =
      ordAtPrime ⟨m.asIdeal.comap (algebraMap C Cₚ), inferInstance⟩ τ := by
  have : Ring.KrullDimLE 1 Cₚ := Stacks.Chow.krullDimLE_one_of_isIntegral Aₚ Cₚ
  have := krullDimLE_localization_atPrime m.asIdeal
  set 𝔮 : Ideal C := m.asIdeal.comap (algebraMap C Cₚ) with h𝔮
  have : Ring.KrullDimLE 1 (Localization.AtPrime 𝔮) := Ring.krullDimLE_iff.mpr (by
    rw [ringKrullDim_eq_of_ringEquiv (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) m.asIdeal).toRingEquiv]
    exact Ring.krullDimLE_iff.mp inferInstance)
  have hu : IsUnit (fracMapOfLocalization 𝔮.primeCompl (Localization.AtPrime 𝔮) τ) := hτ.map _
  rw [ordAtPrime, dite_eq_left ⟨inferInstance, hu⟩]
  have heq : localizedFraction m.asIdeal
      (fracMapOfLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) Cₚ τ) =
      fracMapOfLocalization 𝔮.primeCompl (Localization.AtPrime m.asIdeal) τ := by
    have hext : (localizedFraction m.asIdeal).comp (fracMapOfLocalization
        (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) Cₚ) =
        fracMapOfLocalization 𝔮.primeCompl (Localization.AtPrime m.asIdeal) := by
      refine IsLocalization.ringHom_ext C⁰ (RingHom.ext fun c => ?_)
      simp only [RingHom.comp_apply, fracMapOfLocalization, localizedFraction,
        IsLocalization.map_eq]
      rfl
    exact RingHom.congr_fun hext τ
  rw [Ring.ordTotalFracInt_congr _ _ (by rw [← heq]; exact (hτ.map _).map _) heq]
  exact ordTotalFracInt_eq_of_isLocalization_atPrime 𝔮 τ _ _

/-- **The order of vanishing of a norm over a finite reduced extension, at a prime of the base.**
Let `A` be a reduced Noetherian ring, `C` a finite reduced `A`-algebra whose minimal primes lie
over minimal primes of `A`, `𝔭` a prime of `A` with `A_𝔭` of dimension one, and `L/K` a finite
extension of fields. Suppose that at every minimal prime `Q` of `A_𝔭` the generic fibre of
`C_𝔭` over `Q` is the base change of `L/K`, and that `σ ∈ Q(A)`, `τ ∈ Q(C)` read as
`Nm_{L/K}(t)` and `t` there. Then

`ord_{A_𝔭}(σ) = ∑_{𝔮 ∩ A = 𝔭} [κ(𝔮) : κ(𝔭)] · ord_{C_𝔮}(τ)`. -/
theorem ordTotalFracInt_atPrime_eq_finsum (hdim : ringKrullDim Aₚ = 1)
    (htf : ∀ P ∈ minimalPrimes C, P.comap (algebraMap A C) ∈ minimalPrimes A) (K L : Type u)
    [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    (κ : ∀ Q : minimalPrimes Aₚ, K →+* fibreField Q)
    (lam : ∀ Q : minimalPrimes Aₚ, L →+* fibreRing (D := Cₚ) Q)
    (hpush : ∀ Q : minimalPrimes Aₚ, IsPushout (CommRingCat.ofHom (κ Q))
      (CommRingCat.ofHom (algebraMap K L))
      (CommRingCat.ofHom (algebraMap (fibreField Q) (fibreRing (D := Cₚ) Q)))
      (CommRingCat.ofHom (lam Q)))
    (σ : FractionRing A) (hσ : IsUnit σ) (τ : FractionRing C) (hτ : IsUnit τ) (t : L)
    (hσt : ∀ Q : minimalPrimes Aₚ,
      locFracO Q (fracMapOfLocalization 𝔭.primeCompl Aₚ σ) = κ Q (Algebra.norm K t))
    (hτt : ∀ Q : minimalPrimes Aₚ,
      haveI : Ring.KrullDimLE 1 Aₚ := Ring.krullDimLE_iff.mpr hdim.le
      haveI : Ring.KrullDimLE 1 Cₚ := Stacks.Chow.krullDimLE_one_of_isIntegral Aₚ Cₚ
      locFracD (comap_mem_minimalPrimes_localization 𝔭 htf) Q
        (fracMapOfLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) Cₚ τ) = lam Q t) :
    haveI : Ring.KrullDimLE 1 Aₚ := Ring.krullDimLE_iff.mpr hdim.le
    Ring.ordTotalFracInt Aₚ (fracMapOfLocalization 𝔭.primeCompl Aₚ σ) (hσ.map _) =
      ∑ᶠ 𝔮 ∈ {𝔮 : PrimeSpectrum C | 𝔮.asIdeal.comap (algebraMap A C) = 𝔭},
        (Stacks.Length.primeResidueDegree (algebraMap A C) 𝔭 𝔮.asIdeal : ℤ) *
          ordAtPrime 𝔮 τ := by
  have : Ring.KrullDimLE 1 Aₚ := Ring.krullDimLE_iff.mpr hdim.le
  have : Ring.KrullDimLE 1 Cₚ := Stacks.Chow.krullDimLE_one_of_isIntegral Aₚ Cₚ
  rw [ordTotalFracInt_eq_finsum_of_isPushout hdim (comap_mem_minimalPrimes_localization 𝔭 htf) K L
    κ lam hpush _ (hσ.map _) _ (hτ.map _) t hσt hτt,
    ← Stacks.Length.image_comap_maximalSpectrum 𝔭,
    finsum_mem_image (Stacks.Length.injOn_comap_maximalSpectrum 𝔭), finsum_mem_univ]
  refine finsum_congr fun m => ?_
  rw [quotientDegree_eq_primeResidueDegree 𝔭 m, ordTotalFracInt_localization_eq_ordAtPrime 𝔭 m τ hτ]

omit [Module.Finite A C] [IsNoetherianRing A] [IsNoetherianRing C] [IsReduced A] [IsReduced C] in
/-- **The generic fibre of `C_𝔭` over a minimal prime `Q` of `A_𝔭` is the localization of `C`
at the complement of the contraction of `Q`.** -/
theorem isLocalization_fibreRing (Q : minimalPrimes Aₚ) :
    haveI := Q.2.1.1
    IsLocalization (Algebra.algebraMapSubmonoid C (Q.1.comap (algebraMap A Aₚ)).primeCompl)
      (fibreRing (D := Cₚ) Q) := by
  have := Q.2.1.1
  set Q' : Ideal A := Q.1.comap (algebraMap A Aₚ) with hQ'
  have hQ'p : Q' ≤ 𝔭 := by
    intro a ha
    by_contra hap
    have hu : IsUnit (algebraMap A Aₚ a) := IsLocalization.map_units Aₚ (⟨a, hap⟩ : 𝔭.primeCompl)
    exact Q.2.1.1.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
  set M := Algebra.algebraMapSubmonoid C 𝔭.primeCompl
  set N := fibreSubmonoid (D := Cₚ) Q
  have := IsLocalization.localization_localization_isLocalization M N (fibreRing (D := Cₚ) Q)
  refine (IsLocalization.iff_of_le_of_exists_dvd _
    (IsLocalization.localizationLocalizationSubmodule M N) ?_ ?_).mpr inferInstance
  · rintro _ ⟨a, ha, rfl⟩
    rw [IsLocalization.mem_localizationLocalizationSubmodule]
    refine ⟨⟨algebraMap Aₚ Cₚ (algebraMap A Aₚ a), algebraMap A Aₚ a, ha, rfl⟩, 1, ?_⟩
    simp only [OneMemClass.coe_one, map_one, mul_one]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · intro x hx
    rw [IsLocalization.mem_localizationLocalizationSubmodule] at hx
    obtain ⟨⟨_, o, ho, rfl⟩, ⟨_, s, hs, rfl⟩, e⟩ := hx
    obtain ⟨a, s', rfl⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl o
    have ha : a ∉ Q' := by
      intro haQ
      apply ho
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Q.1.mul_mem_right _ haQ
    have e2 : algebraMap C Cₚ x = algebraMap Aₚ Cₚ (IsLocalization.mk' Aₚ a s') *
        algebraMap C Cₚ (algebraMap A C s) := e
    have hAC : ∀ b : A, algebraMap C Cₚ (algebraMap A C b) = algebraMap Aₚ Cₚ (algebraMap A Aₚ b) :=
      fun b => by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have e' : algebraMap C Cₚ (x * algebraMap A C s') =
        algebraMap C Cₚ (algebraMap A C a * algebraMap A C s) := by
      rw [map_mul, e2, map_mul, hAC s', hAC a, mul_right_comm, ← map_mul,
        IsLocalization.mk'_spec]
    obtain ⟨⟨_, t, ht, rfl⟩, htm⟩ := (IsLocalization.eq_iff_exists M Cₚ).mp e'
    refine ⟨algebraMap A C (t * a * s), ⟨t * a * s, ?_, rfl⟩, ⟨algebraMap A C (t * s'), ?_⟩⟩
    · intro hmem
      rcases (Ideal.IsPrime.comap _ : Q'.IsPrime).mem_or_mem hmem with h1 | h1
      · rcases (Ideal.IsPrime.comap _ : Q'.IsPrime).mem_or_mem h1 with h2 | h2
        · exact ht (hQ'p h2)
        · exact ha h2
      · exact hs (hQ'p h1)
    · simp only [map_mul] at htm ⊢
      linear_combination (-1 : C) * htm

end Global

end Stacks.NormBranches

end
