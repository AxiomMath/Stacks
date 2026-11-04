module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Examples of Jacobson and non-Jacobson rings

A Noetherian domain of dimension at most one with infinitely many maximal ideals, such as `ℤ`, is a
Jacobson ring, while a domain with finitely many maximal ideals is Jacobson only if it is a field.
An infinite product of fields is a Jacobson ring. For `R = ℤ_{(2)}`, which is not Jacobson, the
localization `R[1/2]` is `ℚ` and the closed point of `Spec ℚ` maps to the generic point of
`Spec R`; likewise the localization of `ℤ` at all nonzero elements sends the closed point of its
spectrum to the generic point of `Spec ℤ`, which is not closed.

## Main results

* `isJacobsonRing_of_domain_noetherian_dim_le_one_infinite_maximalSpectrum`: a Noetherian domain in
  which every nonzero prime is maximal and which has infinitely many maximal ideals is a Jacobson
  ring.
* `int_isJacobsonRing`: `ℤ` is a Jacobson ring.
* `isJacobsonRing_of_finiteType_int`: a finite type algebra over `ℤ` is a Jacobson ring.
* `isField_of_isDomain_finite_maximalIdeal`: a Jacobson domain with finitely many maximal ideals is
  a field.
* `nonempty_ringEquiv_rat`: `ℤ_{(2)}[1/2] ≃+* ℚ`.
* `comap_closedPoint_eq_genericPoint`: `Spec ℚ ⟶ Spec ℤ_{(2)}[1/2] ⟶ Spec ℤ_{(2)}` sends the closed
  point to the generic point.
* `specMapZQ_specQPoint_eq_genericPoint`: `Spec ℚ ⟶ Spec ℤ` sends the point of `Spec ℚ` to the
  generic point.
* `specMapLoc_specLocPoint_not_isClosed`: the image of the closed point of `Spec ((ℤ ∖ {0})⁻¹ ℤ)`
  in `Spec ℤ` is not closed.
* `prod_field_isJacobsonRing`: a product of fields indexed by an infinite type is a Jacobson ring.

## References

* [Stacks Project, Tag 00G4](https://stacks.math.columbia.edu/tag/00G4)
* [Stacks Project, Tag 00G5](https://stacks.math.columbia.edu/tag/00G5)
* [Stacks Project, Tag 00G7](https://stacks.math.columbia.edu/tag/00G7)
* [Stacks Project, Tag 00G8](https://stacks.math.columbia.edu/tag/00G8)
* [Stacks Project, Tag 00GC](https://stacks.math.columbia.edu/tag/00GC)
* [Stacks Project, Tag 02CC](https://stacks.math.columbia.edu/tag/02CC)
-/

@[expose] public section


open Ideal

/-- If `x ∈ M` and `M` is maximal, then the image of `M` in `R ⧸ span {x}` is maximal. -/
private lemma image_isMaximal_of_mem
    {R : Type*} [CommRing R] (x : R) (M : Ideal R) (hM : M.IsMaximal)
    (hxM : x ∈ M) :
    (M.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R)))).IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact MulEquiv.isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient M).mp hM)
    (DoubleQuot.quotQuotEquivQuotOfLE ((Ideal.span_singleton_le_iff_mem M).mpr hxM)).toMulEquiv

/-- In a domain `R` where every nonzero prime is maximal, every prime ideal of `R ⧸ (x)` is maximal
for any nonzero `x`. -/
private theorem quot_prime_isMaximal
    (R : Type*) [CommRing R] [IsDomain R]
    (hdim : ∀ I : Ideal R, I.IsPrime → I ≠ ⊥ → I.IsMaximal)
    (x : R) (hx_ne : x ≠ 0)
    (Q : Ideal (R ⧸ Ideal.span ({x} : Set R))) (hQ : Q.IsPrime) : Q.IsMaximal := by
  set π : R →+* R ⧸ Ideal.span ({x} : Set R) := Ideal.Quotient.mk _
  have hx_in_P : x ∈ Q.comap π := by
    rw [Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))]
    exact Q.zero_mem
  have hP_ne_bot : Q.comap π ≠ ⊥ := fun h => hx_ne <| by
    simpa [Ideal.mem_bot] using (h ▸ hx_in_P : x ∈ (⊥ : Ideal R))
  rw [← Ideal.map_comap_of_surjective π Ideal.Quotient.mk_surjective Q]
  exact image_isMaximal_of_mem x _ (hdim _ (hQ.comap π) hP_ne_bot) hx_in_P

/-- A nontrivial Noetherian ring whose primes are all maximal has finitely many maximal ideals. -/
private lemma finite_maximalSpectrum_of_dim_zero
    (S : Type*) [CommRing S] [Nontrivial S] [IsNoetherianRing S]
    (h : ∀ Q : Ideal S, Q.IsPrime → Q.IsMaximal) :
    Finite (MaximalSpectrum S) := by
  have : Finite (minimalPrimes S) :=
    (minimalPrimes.finite_of_isNoetherianRing S).to_subtype
  apply Finite.of_injective
    (fun m : MaximalSpectrum S => (⟨m.asIdeal, by
      refine ⟨⟨m.isMaximal.isPrime, bot_le⟩, ?_⟩
      intro Q hQ hQm
      exact le_of_eq (IsMaximal.eq_of_le (h Q hQ.left) m.isMaximal.ne_top hQm).symm⟩
        : minimalPrimes S))
  intro _ _ hm
  exact MaximalSpectrum.ext (Subtype.ext_iff.mp hm)

/-- When `x ∈ M`, taking the image of `M` in `R ⧸ span {x}` and pulling it back recovers `M`. -/
private lemma comap_map_eq_of_mem
    {R : Type*} [CommRing R] (x : R) (M : Ideal R) (hxM : x ∈ M) :
    (M.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R)))).comap
        (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) = M := by
  simp [comap_map_quotientMk, (Ideal.span_singleton_le_iff_mem M).mpr hxM]

/-- If every maximal ideal of `R` contains `x`, finiteness of `MaximalSpectrum (R ⧸ (x))` transfers
to finiteness of `MaximalSpectrum R`. -/
private lemma finite_maximalSpectrum_of_quotient_finite
    (R : Type*) [CommRing R] (x : R)
    (hx_jac : ∀ M : Ideal R, M.IsMaximal → x ∈ M)
    (hfin : Finite (MaximalSpectrum (R ⧸ Ideal.span ({x} : Set R)))) :
    Finite (MaximalSpectrum R) := by
  let π : R →+* R ⧸ Ideal.span ({x} : Set R) := Ideal.Quotient.mk _
  let f : MaximalSpectrum R → MaximalSpectrum (R ⧸ Ideal.span ({x} : Set R)) :=
    fun M => ⟨M.asIdeal.map π,
      image_isMaximal_of_mem x M.asIdeal M.isMaximal (hx_jac M.asIdeal M.isMaximal)⟩
  refine Finite.of_injective f fun M₁ M₂ h => MaximalSpectrum.ext ?_
  rw [← comap_map_eq_of_mem x M₁.asIdeal (hx_jac _ M₁.isMaximal),
      ← comap_map_eq_of_mem x M₂.asIdeal (hx_jac _ M₂.isMaximal)]
  exact congrArg (·.asIdeal.comap π) h

/-- Let `R` be a Noetherian domain in which every nonzero prime is maximal. If a nonzero element
`x` lies in every maximal ideal of `R`, then `R` has only finitely many maximal ideals. -/
private lemma finite_maximalSpectrum_of_nonzero_jacobson
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ∀ I : Ideal R, I.IsPrime → I ≠ ⊥ → I.IsMaximal)
    (x : R) (hx_ne : x ≠ 0)
    (hx_jac : ∀ M : Ideal R, M.IsMaximal → x ∈ M) :
    Finite (MaximalSpectrum R) := by
  have hne_top : Ideal.span ({x} : Set R) ≠ ⊤ := by
    obtain ⟨M, hM⟩ : ∃ M : Ideal R, M.IsMaximal := exists_maximal R
    intro h
    exact hM.ne_top <| eq_top_of_isUnit_mem M (hx_jac M hM) (by simp_all)
  have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) :=
    Ideal.Quotient.nontrivial_iff.mpr hne_top
  have : IsNoetherianRing (R ⧸ Ideal.span ({x} : Set R)) :=
    Ideal.Quotient.isNoetherianRing _
  exact finite_maximalSpectrum_of_quotient_finite R x hx_jac <|
    finite_maximalSpectrum_of_dim_zero _ (quot_prime_isMaximal R hdim x hx_ne)

/-- A Noetherian domain in which every nonzero prime ideal is maximal and which has infinitely many
maximal ideals is a Jacobson ring. -/
@[stacks 00G4,
  ega "IV 10.4.3" "principal ideal ring",
  ega "IV 10.5.2" "special case",
  ega "IV 10.7.1" "partial"]
theorem isJacobsonRing_of_domain_noetherian_dim_le_one_infinite_maximalSpectrum
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ∀ I : Ideal R, I.IsPrime → I ≠ ⊥ → I.IsMaximal)
    (hinf : Infinite (MaximalSpectrum R)) :
    IsJacobsonRing R := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hPbot : P = ⊥
  · subst hPbot
    refine le_antisymm ?_ Ideal.le_jacobson
    intro x hx
    by_contra hne
    have hx_ne : x ≠ 0 := fun h => hne (h ▸ Submodule.zero_mem _)
    have hx_in_max : ∀ M : Ideal R, M.IsMaximal → x ∈ M := fun M hM =>
      (Submodule.mem_sInf.mp hx) M ⟨bot_le, hM⟩
    exact (finite_maximalSpectrum_of_nonzero_jacobson R hdim x hx_ne hx_in_max).false
  · have : P.IsMaximal := hdim P hP hPbot
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- `ℤ` has infinitely many maximal ideals. -/
private lemma int_infinite_maximalSpectrum : Infinite (MaximalSpectrum ℤ) := by
  let f : {p : ℕ // Nat.Prime p} → MaximalSpectrum ℤ := fun p =>
    { asIdeal := Ideal.span {(p.val : ℤ)}
      isMaximal := PrincipalIdealRing.isMaximal_of_irreducible <| by
        simpa using (Int.prime_iff_natAbs_prime.mpr (by simpa using p.property)).irreducible }
  have hf : Function.Injective f := fun p q hpq => Subtype.ext <| by
    have h : Ideal.span ({(p.val : ℤ)} : Set ℤ) = Ideal.span ({(q.val : ℤ)} : Set ℤ) := by
      simpa using congrArg MaximalSpectrum.asIdeal hpq
    rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff] at h
    rcases h with heq | hneg
    · exact_mod_cast heq
    · have hp_pos : (0 : ℤ) < p.val := by exact_mod_cast p.property.pos
      linarith [hneg ▸ hp_pos]
  have : Infinite {p : ℕ // Nat.Prime p} := Nat.infinite_setOfPred_prime.to_subtype
  exact Infinite.of_injective f hf

/-- The ring `ℤ` is a Jacobson ring. -/
@[stacks 00G4, ega "IV 10.4.3" "example ℤ"]
theorem int_isJacobsonRing : IsJacobsonRing ℤ :=
  isJacobsonRing_of_domain_noetherian_dim_le_one_infinite_maximalSpectrum ℤ
    (fun _ _ h => IsPrime.to_maximal_ideal h)
    int_infinite_maximalSpectrum

end

@[expose] public section

/-- A finite type algebra over `ℤ` is a Jacobson ring. -/
@[stacks 00GC]
theorem isJacobsonRing_of_finiteType_int (B : Type*) [CommRing B] [Algebra ℤ B]
    [Algebra.FiniteType ℤ B] : IsJacobsonRing B :=
  have := int_isJacobsonRing
  isJacobsonRing_of_finiteType (A := ℤ)

/-- A Jacobson domain with finitely many maximal ideals is a field. -/
@[stacks 00G5, ega "IV 10.7.1" "partial"]
theorem isField_of_isDomain_finite_maximalIdeal
    {R : Type*} [CommRing R] [IsDomain R] [IsJacobsonRing R]
    (hfin : {m : Ideal R | m.IsMaximal}.Finite) :
    IsField R := by
  by_contra hnf
  have hbot_not_max : ¬ (⊥ : Ideal R).IsMaximal := fun h =>
    hnf (Ring.isField_iff_maximal_bot.mpr h)
  have hjac : (⊥ : Ideal R).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.mp inferInstance ⊥ inferInstance
  have hne : ∀ m ∈ hfin.toFinset, m ≠ (⊥ : Ideal R) := by
    intro m hm hmbot
    rw [Set.Finite.mem_toFinset] at hm
    exact hbot_not_max (hmbot ▸ hm)
  have hex : ∀ m ∈ hfin.toFinset, ∃ x, x ∈ m ∧ x ≠ (0 : R) := fun m hm =>
    (Submodule.ne_bot_iff m).mp (hne m hm)
  classical
  choose f hf using hex
  set p : R := ∏ m ∈ hfin.toFinset.attach, f m.val m.property with hp
  have hp_ne : p ≠ 0 := by
    rw [hp, Finset.prod_ne_zero_iff]
    rintro ⟨m, hm⟩ -
    exact (hf m hm).right
  have hp_mem : p ∈ (⊥ : Ideal R).jacobson := by
    show p ∈ sInf {J : Ideal R | ⊥ ≤ J ∧ J.IsMaximal}
    rw [Submodule.mem_sInf]
    rintro J ⟨-, hJmax⟩
    have hJS : J ∈ hfin.toFinset := hfin.mem_toFinset.mpr hJmax
    rw [hp, ← Finset.mul_prod_erase hfin.toFinset.attach (fun m => f m.val m.property)
      (Finset.mem_attach hfin.toFinset ⟨J, hJS⟩)]
    exact Ideal.mul_mem_right _ J (hf J hJS).left
  rw [hjac] at hp_mem
  exact hp_ne (Ideal.mem_bot.mp hp_mem)

end

@[expose] public section

/-!
### The localization `ℤ_{(2)}[1/2]`

For `R = ℤ_{(2)}`, the localization `R_2 = R[1/2]` is isomorphic to `ℚ`, and
`Spec ℚ ⟶ Spec R_2 ⟶ Spec R` sends the closed point of `Spec ℚ` to the generic point of `Spec R`.
-/


/-- The prime ideal `(2) ⊂ ℤ`. -/
def twoIdeal : Ideal ℤ := Ideal.span {(2 : ℤ)}

/-- The ideal `(2) ⊂ ℤ` is prime. -/
instance twoIdeal_isPrime : twoIdeal.IsPrime :=
  (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr
    (Int.prime_iff_natAbs_prime.mpr (by decide))

/-- The local ring `ℤ_{(2)}`, i.e. `ℤ` localised at the prime `(2)`. -/
@[ega "0 19.8.3" "p = 2"]
abbrev StacksZ2loc : Type := Localization.AtPrime twoIdeal

/-- The localization `ℤ_{(2)}[1/2]` of `ℤ_{(2)}` at the element `2`. -/
abbrev StacksR_at_2 : Type := Localization.Away ((2 : ℤ) : StacksZ2loc)

/-- The element `(2 : ℤ)` mapped into `StacksZ2loc = ℤ_{(2)}` is nonzero. -/
lemma two_ne_zero_stacksZ2loc : ((2 : ℤ) : StacksZ2loc) ≠ 0 := by
  have hinj : Function.Injective (algebraMap ℤ StacksZ2loc) :=
    IsLocalization.injective StacksZ2loc twoIdeal.primeCompl_le_nonZeroDivisors
  intro h
  exact absurd (hinj (a₁ := 2) (a₂ := 0) (by simpa using h)) (by norm_num)

/-- Powers of `(2 : ℤ) : StacksZ2loc` are nonzero divisors of `StacksZ2loc`. -/
lemma powers_two_le_nonZeroDivisors_stacksZ2loc :
    Submonoid.powers ((2 : ℤ) : StacksZ2loc) ≤ nonZeroDivisors StacksZ2loc :=
  Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero two_ne_zero_stacksZ2loc)

/-- Every nonzero integer is `2 ^ k * m` with `k : ℕ` and `m ∉ twoIdeal`, that is, `m` odd. -/
lemma int_eq_pow_two_mul_odd (n : ℤ) (hn : n ≠ 0) :
    ∃ k : ℕ, ∃ m : ℤ, m ∉ twoIdeal ∧ n = 2 ^ k * m := by
  obtain ⟨c, h1, h2⟩ :=
    (Int.finiteMultiplicity_iff (a := 2).mpr ⟨by decide, hn⟩).exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, fun h => h2 (Ideal.mem_span_singleton.mp h), h1⟩

/-- The image of `twoIdeal.primeCompl` under `algebraMap ℤ StacksZ2loc` lies in the nonzero
divisors of `StacksZ2loc`. -/
lemma map_primeCompl_le_nonZeroDivisors_stacksZ2loc :
    Submonoid.map (algebraMap ℤ StacksZ2loc) twoIdeal.primeCompl ≤
      nonZeroDivisors StacksZ2loc := by
  rintro _ ⟨a, ha, rfl⟩
  exact (IsLocalization.map_units StacksZ2loc
    (⟨a, ha⟩ : twoIdeal.primeCompl)).mem_nonZeroDivisors

/-- Every element of the iterated-localization submonoid is a nonzero divisor of `ℤ`. -/
lemma localizationLocalizationSubmodule_twoIdeal_le_nonZeroDivisors :
    IsLocalization.localizationLocalizationSubmodule twoIdeal.primeCompl
        (Submonoid.powers ((2 : ℤ) : StacksZ2loc)) ≤ nonZeroDivisors ℤ := by
  have hsup : Submonoid.powers ((2 : ℤ) : StacksZ2loc) ⊔
      Submonoid.map (algebraMap ℤ StacksZ2loc) twoIdeal.primeCompl ≤
        nonZeroDivisors StacksZ2loc :=
    sup_le powers_two_le_nonZeroDivisors_stacksZ2loc
      map_primeCompl_le_nonZeroDivisors_stacksZ2loc
  exact fun x hx => mem_nonZeroDivisors_iff_ne_zero.mpr fun hx0 =>
    mem_nonZeroDivisors_iff_ne_zero.mp (hsup hx) (by rw [hx0, map_zero])

/-- Every nonzero integer lies in
`localizationLocalizationSubmodule twoIdeal.primeCompl (powers 2)`, the preimage in `ℤ` of the join
of `Submonoid.powers (2 : StacksZ2loc)` and the image of `twoIdeal.primeCompl`. -/
lemma int_mem_localizationLocalizationSubmodule_twoIdeal_of_ne_zero (n : ℤ) (hn : n ≠ 0) :
    n ∈ IsLocalization.localizationLocalizationSubmodule twoIdeal.primeCompl
        (Submonoid.powers ((2 : ℤ) : StacksZ2loc)) := by
  obtain ⟨k, m, hm, hnk⟩ := int_eq_pow_two_mul_odd n hn
  show (algebraMap ℤ StacksZ2loc) n ∈
      Submonoid.powers ((2 : ℤ) : StacksZ2loc) ⊔
        Submonoid.map (algebraMap ℤ StacksZ2loc) twoIdeal.primeCompl
  rw [show (algebraMap ℤ StacksZ2loc) n =
      ((2 : ℤ) : StacksZ2loc) ^ k * (algebraMap ℤ StacksZ2loc) m by
    rw [hnk, map_mul, map_pow]; simp [eq_intCast]]
  exact Submonoid.mul_mem _
    ((le_sup_left : Submonoid.powers ((2 : ℤ) : StacksZ2loc) ≤ _) ⟨k, rfl⟩)
    ((le_sup_right :
        Submonoid.map (algebraMap ℤ StacksZ2loc) twoIdeal.primeCompl ≤ _) ⟨m, hm, rfl⟩)

/-- `StacksR_at_2 = (ℤ_{(2)})[1/2]` is a fraction ring of `ℤ`. -/
instance isFractionRing_stacksR_at_2 : IsFractionRing ℤ StacksR_at_2 := by
  have hL : IsLocalization
      (IsLocalization.localizationLocalizationSubmodule twoIdeal.primeCompl
        (Submonoid.powers ((2 : ℤ) : StacksZ2loc))) StacksR_at_2 :=
    IsLocalization.localization_localization_isLocalization _ _ _
  unfold IsFractionRing
  refine @IsLocalization.isLocalization_of_is_exists_mul_mem _ _ _ _ _
    (IsLocalization.localizationLocalizationSubmodule twoIdeal.primeCompl
      (Submonoid.powers ((2 : ℤ) : StacksZ2loc)))
    (nonZeroDivisors ℤ) hL
    localizationLocalizationSubmodule_twoIdeal_le_nonZeroDivisors ?_
  intro ⟨x, hx⟩
  exact ⟨1, by
    simpa using int_mem_localizationLocalizationSubmodule_twoIdeal_of_ne_zero x
      (mem_nonZeroDivisors_iff_ne_zero.mp hx)⟩

/-- `ℤ_{(2)}[1/2]` is isomorphic to `ℚ` as a ring. -/
@[stacks 00G7]
theorem nonempty_ringEquiv_rat : Nonempty (StacksR_at_2 ≃+* ℚ) :=
  ⟨(IsLocalization.algEquiv (nonZeroDivisors ℤ) StacksR_at_2 ℚ).toRingEquiv⟩

/-- For any ring isomorphism `e : ℤ_{(2)}[1/2] ≃+* ℚ`, the composite
`Spec ℚ → Spec ℤ_{(2)}[1/2] → Spec ℤ_{(2)}` sends the closed point of `Spec ℚ` to the generic point
`⟨⊥, _⟩` of `Spec ℤ_{(2)}`. -/
theorem comap_closedPoint_eq_genericPoint (e : StacksR_at_2 ≃+* ℚ) :
    PrimeSpectrum.comap (algebraMap StacksZ2loc StacksR_at_2)
      (PrimeSpectrum.comap (e : StacksR_at_2 →+* ℚ) (IsLocalRing.closedPoint ℚ)) =
        ⟨⊥, Ideal.isPrime_bot⟩ := by
  apply PrimeSpectrum.ext
  show ((IsLocalRing.closedPoint ℚ).asIdeal.comap (e : StacksR_at_2 →+* ℚ)).comap
      (algebraMap StacksZ2loc StacksR_at_2) = (⊥ : Ideal StacksZ2loc)
  rw [show (IsLocalRing.closedPoint ℚ).asIdeal = (⊥ : Ideal ℚ) by
        simp [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot],
    Ideal.comap_bot_of_injective (e : StacksR_at_2 →+* ℚ) e.injective,
    Ideal.comap_bot_of_injective (algebraMap StacksZ2loc StacksR_at_2)
      (IsLocalization.injective StacksR_at_2 powers_two_le_nonZeroDivisors_stacksZ2loc)]

end

@[expose] public section


/-!
### Localizing `ℤ` at all nonzero elements

The map `Spec ((ℤ \ {0})⁻¹ ℤ) ⟶ Spec ℤ`, and likewise `Spec ℚ ⟶ Spec ℤ`, sends the unique closed
point to the generic point `(0)` of `Spec ℤ`, which is not closed.
-/

/-- The localization of `ℤ` at the multiplicative set of all nonzero elements: `(ℤ \ {0})⁻¹ ℤ`. -/
@[ega "0 19.8.3"]
abbrev IntLocalization : Type := Localization (nonZeroDivisors ℤ)

/-- The isomorphism `(ℤ \ {0})⁻¹ ℤ ≃+* ℚ`. -/
noncomputable def intLocalizationEquivRat : IntLocalization ≃+* ℚ :=
  (IsLocalization.algEquiv (nonZeroDivisors ℤ) IntLocalization ℚ).toRingEquiv

/-- `(ℤ \ {0})⁻¹ ℤ` is a field. -/
noncomputable instance : Field IntLocalization := IsFractionRing.toField ℤ

/-- The point of `Spec((ℤ \ {0})⁻¹ ℤ)` given by the zero ideal. -/
def specLocPoint : PrimeSpectrum IntLocalization :=
  ⟨(⊥ : Ideal IntLocalization), Ideal.isPrime_bot⟩

/-- The unique point of `Spec(ℚ)`: the zero ideal. -/
def specQPoint : PrimeSpectrum ℚ :=
  ⟨(⊥ : Ideal ℚ), Ideal.isPrime_bot⟩

/-- The generic point of `Spec(ℤ)`: the zero ideal. -/
def specZGenericPoint : PrimeSpectrum ℤ :=
  ⟨(⊥ : Ideal ℤ), Ideal.isPrime_bot⟩

/-- The induced map on prime spectra coming from the localization map `ℤ → (ℤ \ {0})⁻¹ ℤ`. -/
noncomputable def specMapLoc : PrimeSpectrum IntLocalization → PrimeSpectrum ℤ :=
  PrimeSpectrum.comap (algebraMap ℤ IntLocalization)

/-- The induced map on prime spectra coming from the inclusion `ℤ → ℚ`. -/
def specMapZQ : PrimeSpectrum ℚ → PrimeSpectrum ℤ :=
  PrimeSpectrum.comap (algebraMap ℤ ℚ)

/-- `Spec((ℤ \ {0})⁻¹ ℤ)` has a unique point, namely `specLocPoint`. -/
theorem specLoc_unique (p : PrimeSpectrum IntLocalization) : p = specLocPoint :=
  PrimeSpectrum.ext (Ideal.eq_bot_of_prime _)

/-- `Spec(ℚ)` has a unique point, namely `specQPoint`. -/
theorem specQ_unique (p : PrimeSpectrum ℚ) : p = specQPoint :=
  PrimeSpectrum.ext (Ideal.eq_bot_of_prime _)

/-- A point of a prime spectrum with no other points is closed. -/
private theorem isClosed_singleton_of_forall_eq {R : Type*} [CommRing R] {p : PrimeSpectrum R}
    (h : ∀ q, q = p) : IsClosed ({p} : Set (PrimeSpectrum R)) := by
  convert isClosed_univ
  exact Set.eq_univ_of_forall fun q => h q

/-- The unique point of `Spec((ℤ \ {0})⁻¹ ℤ)` is closed. -/
theorem specLocPoint_isClosed :
    IsClosed ({specLocPoint} : Set (PrimeSpectrum IntLocalization)) :=
  isClosed_singleton_of_forall_eq specLoc_unique

/-- The unique point of `Spec(ℚ)` is closed. -/
theorem specQPoint_isClosed : IsClosed ({specQPoint} : Set (PrimeSpectrum ℚ)) :=
  isClosed_singleton_of_forall_eq specQ_unique

/-- The closure of the generic point in `Spec(ℤ)` is the whole space. -/
lemma closure_singleton_specZGenericPoint :
    closure ({specZGenericPoint} : Set (PrimeSpectrum ℤ)) = Set.univ := by
  rw [PrimeSpectrum.closure_singleton]
  exact PrimeSpectrum.zeroLocus_bot

/-- The zero ideal of `ℤ` is a generic point of `Spec(ℤ)`. -/
theorem specZGenericPoint_isGenericPoint :
    IsGenericPoint specZGenericPoint (Set.univ : Set (PrimeSpectrum ℤ)) :=
  closure_singleton_specZGenericPoint

/-- The localization map `ℤ → (ℤ \ {0})⁻¹ ℤ` sends the unique (closed) point of
`Spec((ℤ \ {0})⁻¹ ℤ)` to the generic point `(0)` of `Spec(ℤ)`. -/
theorem specMapLoc_specLocPoint_eq_genericPoint :
    specMapLoc specLocPoint = specZGenericPoint :=
  PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (IsFractionRing.injective ℤ IntLocalization))

/-- The inclusion `ℤ → ℚ` sends the unique point of `Spec(ℚ)` to the generic point `(0)` of
`Spec(ℤ)`. -/
@[stacks 00G8]
theorem specMapZQ_specQPoint_eq_genericPoint :
    specMapZQ specQPoint = specZGenericPoint :=
  PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (algebraMap ℤ ℚ).injective_int)

/-- The image of the closed point of `Spec((ℤ \ {0})⁻¹ ℤ)` under the localization map is not closed
in `Spec(ℤ)`. -/
theorem specMapLoc_specLocPoint_not_isClosed :
    ¬ IsClosed ({specMapLoc specLocPoint} : Set (PrimeSpectrum ℤ)) := by
  rw [specMapLoc_specLocPoint_eq_genericPoint]
  intro hclosed
  have hsub := hclosed.closure_subset (s := ({specZGenericPoint} : Set _))
  rw [closure_singleton_specZGenericPoint] at hsub
  have hne : (⟨twoIdeal, inferInstance⟩ : PrimeSpectrum ℤ) ≠ specZGenericPoint := by
    intro heq
    have := congrArg PrimeSpectrum.asIdeal heq
    simp [specZGenericPoint, twoIdeal] at this
  exact hne (hsub (Set.mem_univ _))

end

/-!
### An infinite product of fields
-/


@[expose] public section

/-- Let `A` be an infinite type and `(k α)` a family of fields. Then the product ring `∀ α, k α` is
a Jacobson ring. -/
@[stacks 02CC]
theorem prod_field_isJacobsonRing
    (A : Type*) [Infinite A] (k : A → Type*) [∀ α, Field (k α)] :
    IsJacobsonRing (∀ α, k α) := by
  have hmax : ∀ p : Ideal (∀ α, k α), p.IsPrime → p.IsMaximal := by
    intro p hp
    apply Ideal.Quotient.maximal_of_isField
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hex : x * x⁻¹ * x = x := by
      funext α
      by_cases h : x α = 0 <;> simp [h]
    have h0 : x * x⁻¹ * (1 - x * x⁻¹) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, hex, sub_self]
    rcases hp.mem_or_mem (h0 ▸ p.zero_mem) with he | hne
    · exact absurd (hex ▸ Ideal.Quotient.eq_zero_iff_mem.2 (p.mul_mem_right x he)) ha
    · refine ⟨Ideal.Quotient.mk p x⁻¹, ?_⟩
      rw [← map_mul, ← map_one (Ideal.Quotient.mk p), Ideal.Quotient.eq, ← neg_sub]
      exact p.neg_mem hne
  refine ⟨fun I hI => (congrArg sInf ?_).trans ((Ideal.radical_eq_sInf I).symm.trans hI.radical)⟩
  ext J
  exact and_congr_right fun _ => ⟨Ideal.IsMaximal.isPrime, hmax J⟩
end
