module

public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.FormalFibres.Examples
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Serre.FlatAscent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Associated primes of the completion of a universally catenary local domain

Let `A` be a Noetherian local domain which is universally catenary and whose formal fibres
satisfy Serre's condition `(S₁)`. Every associated prime of the completion `A^∧` is minimal,
and `A^∧` is equidimensional, so `dim(A^∧ / 𝔭) = dim(A)` for every associated prime `𝔭`.

## Main results

* `hasSerreCondition_one_of_isDomain`: a domain satisfies `(S₁)`.
* `hasSerreCondition_one_adicCompletion_of_formalFibres`: `(S₁)` ascends from a local domain to
  its completion when every formal fibre satisfies `(S₁)`.
* `mem_minimalPrimes_of_isAssociatedPrimeStacks_self`: over a ring satisfying `(S₁)` every
  associated prime of the ring itself is minimal.
* `le_ringKrullDim_quotient_adicCompletion_iff`: a lower bound holds for the dimension of every
  associated quotient of `A^∧` exactly when it holds for `dim(A)`.

## References

* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u

/-- The depth of `M` over `I` is at least one if some element of `I` acts regularly on `M`. -/
theorem Module.one_le_depth_of_isSMulRegular {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A)
    (t : A) (ht : t ∈ I) (hreg : IsSMulRegular M t) :
    1 ≤ Module.depth A I M := by
  rw [Module.depth]
  split_ifs with htop
  · exact le_top
  · have hne : ⊤ ≠ Ideal.ofList [t] • (⊤ : Submodule A M) := fun heq =>
      htop (top_le_iff.mp (heq.le.trans
        (Submodule.smul_mono_left (by simpa [Ideal.ofList] using ht))))
    calc
      (1 : ℕ∞) = (([t] : List A).length : ℕ∞) := by simp
      _ ≤ _ := le_iSup₂_of_le [t] ⟨by simpa using ht,
        (RingTheory.Sequence.isRegular_iff M [t]).mpr
          ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff M t).mpr hreg, hne⟩⟩ (by simp)

/-- A domain satisfies Serre's condition `(S₁)`. -/
theorem hasSerreCondition_one_of_isDomain {A : Type*} [CommRing A] [IsDomain A] :
    HasSerreCondition A 1 := by
  intro p hp
  let L := Localization.AtPrime p
  have : IsDomain L := IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  by_cases hd : ringKrullDim L = 0
  · show min (1 : WithBot ℕ∞) (ringKrullDim L) ≤
      (Module.depth L (maximalIdeal L) L : WithBot ℕ∞)
    rw [hd]
    norm_num
  · have hmax : maximalIdeal L ≠ ⊥ := by
      intro hbot
      exact hd (ringKrullDim_eq_zero_of_isField
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot))
    obtain ⟨t, ht, htnz⟩ := (Submodule.ne_bot_iff (maximalIdeal L)).mp hmax
    have hdepth : (1 : WithBot ℕ∞) ≤ (Module.depth L (maximalIdeal L) L : WithBot ℕ∞) := by
      exact_mod_cast Module.one_le_depth_of_isSMulRegular (maximalIdeal L) t ht
        (IsSMulRegular.of_ne_zero htnz)
    show min (1 : WithBot ℕ∞) (ringKrullDim L) ≤
      (Module.depth L (maximalIdeal L) L : WithBot ℕ∞)
    exact (min_le_left _ _).trans hdepth

/-- If every formal fibre `A^∧ ⊗_A κ(𝔮)` of a Noetherian local domain `A` satisfies `(S₁)`, then
so does the completion `A^∧`. -/
@[ega "IV 6.4.3" "special case"]
theorem hasSerreCondition_one_adicCompletion_of_formalFibres
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hFibres : ∀ q : PrimeSpectrum A,
      HasSerreCondition
        (AdicCompletion (maximalIdeal A) A ⊗[A] q.asIdeal.ResidueField) 1) :
    HasSerreCondition (AdicCompletion (maximalIdeal A) A) 1 := by
  let B := AdicCompletion (maximalIdeal A) A
  show ∀ (q : Ideal B) [q.IsPrime],
    min (1 : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime q)) ≤
      (Module.depth (Localization.AtPrime q)
        (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) : WithBot ℕ∞)
  refine min_le_depth_atPrime_of_flat (R := A) (S := B) (k := 1) (fun p hp Q hQ => ?_)
    hasSerreCondition_one_of_isDomain
  exact HasSerreCondition.of_ringEquiv
    (Algebra.TensorProduct.comm A B p.ResidueField).toRingEquiv
    (hFibres ⟨p, hp⟩) Q

/-- A minimal prime of a Noetherian ring is associated to the ring itself. -/
theorem mem_associatedPrimes_self_of_mem_minimalPrimes
    {B : Type*} [CommRing B] [IsNoetherianRing B]
    {p : Ideal B} (hp : p ∈ minimalPrimes B) : p ∈ associatedPrimes B B := by
  have hann : Module.annihilator B B = ⊥ :=
    Module.annihilator_eq_bot.mpr
      ((faithfulSMul_iff_algebraMap_injective B B).mpr fun {_ _} a => a)
  change p ∈ (⊥ : Ideal B).minimalPrimes at hp
  rw [← hann] at hp
  exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B B hp

/-- Over a Noetherian ring satisfying `(S₁)` every associated prime of the ring itself is
minimal. -/
theorem mem_minimalPrimes_of_isAssociatedPrimeStacks_self
    {B : Type*} [CommRing B] [IsNoetherianRing B]
    (hSerre : HasSerreCondition B 1) (p : Ideal B)
    (hp : IsAssociatedPrimeStacks B B p) : p ∈ minimalPrimes B := by
  have : p.IsPrime := hp.1
  have hmoduleSerre : ∀ q : PrimeSpectrum B,
      min 1 (Module.supportDim (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl B)) ≤
        (Module.depth (Localization.AtPrime q.asIdeal)
          (maximalIdeal (Localization.AtPrime q.asIdeal))
          (LocalizedModule q.asIdeal.primeCompl B) : WithBot ℕ∞) := by
    intro q
    let e : LocalizedModule q.asIdeal.primeCompl B ≃ₗ[Localization.AtPrime q.asIdeal]
        Localization.AtPrime q.asIdeal :=
      (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl B).trans
        (TensorProduct.AlgebraTensorModule.rid B (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal))
    rw [supportDim_eq_of_linearEquiv e, Module.supportDim_self_eq_ringKrullDim]
    exact hSerre q.asIdeal
  have hminimalAss :=
    (Module.forall_minimal_mem_associatedPrimes_iff_min_one_supportDim_le_depth
      (R := B) (M := B)).2 hmoduleSerre
  have hpM : p ∈ associatedPrimes B B := by
    obtain ⟨hp', x, hx⟩ := hp
    exact AssociatedPrimes.mem_iff.2
      (isAssociatedPrime_iff.mpr ⟨hp', x, by simpa using hx.symm⟩)
  obtain ⟨p₀, hp₀, hp₀p⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := p) bot_le
  have hp₀M : p₀ ∈ associatedPrimes B B := mem_associatedPrimes_self_of_mem_minimalPrimes hp₀
  have : p = p₀ := le_antisymm ((hminimalAss p hpM).2 hp₀M hp₀p) hp₀p
  rwa [this]

/-- Over an equidimensional spectrum every minimal prime has quotient of full dimension. -/
@[ega "IV 5.1.1" "(5.1.1.5)"]
theorem ringKrullDim_quotient_eq_of_equidimensional
    {R : Type*} [CommRing R] [IsNoetherianRing R] [Nontrivial R] [FiniteRingKrullDim R]
    (hR : TopologicalSpace.Equidimensional (PrimeSpectrum R))
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ringKrullDim (R ⧸ p) = ringKrullDim R := by
  obtain ⟨q, hq, hdim⟩ := exists_mem_minimalPrimes_ringKrullDim_quotient_eq R
  exact (specEquidimensional_iff_equidimensional.mpr hR p hp q hq).trans hdim

/-- Let `A` be a universally catenary Noetherian local domain whose formal fibres satisfy `(S₁)`.
Then a bound `n ≤ dim(A^∧ / 𝔭)` holds for every associated prime `𝔭` of the completion exactly
when `n ≤ dim(A)`. -/
@[ega "IV 7.2.5" "(b) ⇒ (a), special case", ega "IV 7.8.3" "more general", ega "IV 7.8.4" "partial"]
theorem le_ringKrullDim_quotient_adicCompletion_iff
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (n : WithBot ℕ∞) (huc : Ring.IsUniversallyCatenary A)
    (hFibres : ∀ q : PrimeSpectrum A,
      HasSerreCondition
        (AdicCompletion (maximalIdeal A) A ⊗[A] q.asIdeal.ResidueField) 1) :
    (∀ p : Ideal (AdicCompletion (maximalIdeal A) A),
      IsAssociatedPrimeStacks (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal A) A) p →
        n ≤ ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ p)) ↔
      n ≤ ringKrullDim A := by
  let B := AdicCompletion (maximalIdeal A) A
  have hbot : (⊥ : Ideal A) ∈ minimalPrimes A := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]; simp
  have hEqQuot : TopologicalSpace.Equidimensional
      (PrimeSpectrum (B ⧸ (⊥ : Ideal A).map (algebraMap A B))) :=
    (isUniversallyCatenary_iff_isFormallyCatenary A).mp huc ⊥ hbot
  rw [Ideal.map_bot] at hEqQuot
  have hEqB : TopologicalSpace.Equidimensional (PrimeSpectrum B) :=
    TopologicalSpace.Equidimensional.of_homeomorph
      (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.quotientBot B).symm) hEqQuot
  have hdimMin : ∀ p ∈ minimalPrimes B, ringKrullDim (B ⧸ p) = ringKrullDim B :=
    fun p hp => ringKrullDim_quotient_eq_of_equidimensional hEqB p hp
  have hSerre : HasSerreCondition B 1 :=
    hasSerreCondition_one_adicCompletion_of_formalFibres hFibres
  constructor
  · intro h
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (show (⊥ : Ideal B) ≠ ⊤ from bot_ne_top)
    obtain ⟨hp', x, hx⟩ := isAssociatedPrime_iff.mp (AssociatedPrimes.mem_iff.mp
      (mem_associatedPrimes_self_of_mem_minimalPrimes hp))
    have hq := h p ⟨hp', x, by simpa using hx.symm⟩
    rwa [hdimMin p hp, ← _root_.ringKrullDim_adicCompletion_maximalIdeal (A := A)] at hq
  · intro h p hp
    rwa [hdimMin p (mem_minimalPrimes_of_isAssociatedPrimeStacks_self hSerre p hp),
      ← _root_.ringKrullDim_adicCompletion_maximalIdeal (A := A)]

end
