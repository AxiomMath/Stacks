module

public import StacksFrontier.RingTheory.LocalCohomology.SupportedSectionsProZero
public import StacksFrontier.RingTheory.LocalCohomology.FormalTorsionProZero

/-!
# Sections with support of the levels of a formal module are essentially constant

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `(F_n)` an inverse system of finite
`R`-modules whose transitions `F_{n+1} → F_n` are surjective with kernel `I^{n+1} F_{n+1}`: the
levels `F_n = M / I^{n+1} M` of a finite module `M` over the `I`-adic completion `R^∧`. Let
`T ⊆ Spec(R)` be stable under specialization and contained in `V(I)`.

This file proves the case `s = 0` of Stacks, Tag 0EIE in the form needed by Stacks, Tag 0EJE: the
images of the sections with support in `T` of the higher levels in a fixed level `F_n` are
eventually the image `Λ_n` of the sections with support in `T` of `M`, and these images are
annihilated by a fixed power of `I`. The hypothesis is local at the primes `𝔮 ∈ T`: for every
compatible system `Λ` of submodules of the levels annihilated by a power of `I` and of depth at
least one at `𝔮` in the uniform form below, the torsion supported at the closed point of the
localized quotients `F_k / Λ_k` is pro-zero. Over a scheme this local statement is supplied by
the completed stalk at the point `𝔮`.

The proof passes to the module `M` of compatible families. Its sections `H = H⁰_T(M)` with
support in `T` (computed over the completion) are annihilated by a power of `I`, and `M / H` has
no associated prime in `T`; by Artin–Rees and prime avoidance this gives the depth condition at
each `𝔮 ∈ T`. The local hypothesis then makes the sections with support in `T` of the quotient
levels `F_k / Λ_k` pro-zero locally at every prime, hence pro-zero
(`Stacks.LocalCohomology.exists_forall_sectionsWithSupportIn_map_eq_zero`), which is the
assertion.

## Main results

* `Stacks.LocalCohomology.exists_primeSpectrum_adicCompletion_comap_eq` and
  `Stacks.LocalCohomology.primeSpectrum_adicCompletion_eq_of_comap_eq` — the primes of the
  completion containing `I` are those of `R`.
* `Stacks.LocalCohomology.mem_sectionsWithSupportIn_of_mk_mem` — the quotient of a module by its
  sections with support in `T` has no nonzero sections with support in `T`.
* `Stacks.LocalCohomology.exists_sectionsWithSupportIn_map_eq` — the essential constancy.

## References

* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.LocalCohomology

/-! ### Primes of the completion -/

section Completion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Elements congruent modulo an ideal lie in it simultaneously. -/
private theorem mem_iff_of_sub_mem {S : Type*} [CommRing S] (P : Ideal S) {a b : S}
    (h : a - b ∈ P) : a ∈ P ↔ b ∈ P :=
  ⟨fun ha => by simpa using P.sub_mem ha h, fun hb => by simpa using P.add_mem h hb⟩

/-- An element of the completion is congruent to an element of the ring modulo any power of the
extended ideal. -/
theorem exists_sub_algebraMap_mem_map_pow (hI : I.FG) (a : AdicCompletion I R) (n : ℕ) :
    ∃ r : R, a - algebraMap R (AdicCompletion I R) r ∈
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  obtain ⟨r, hr⟩ := Stacks.Coherent.completion_exists_approximation I hI a n
  refine ⟨r, ?_⟩
  rw [← mem_pow_smul_top_iff_mem_map_pow_smul_top I n] at hr
  simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hr

/-- **Every prime containing `I` is the contraction of a prime of the completion containing
`I`.** -/
theorem exists_primeSpectrum_adicCompletion_comap_eq (hI : I.FG) (p : PrimeSpectrum R)
    (hp : I ≤ p.asIdeal) :
    ∃ 𝔮 : PrimeSpectrum (AdicCompletion I R),
      I.map (algebraMap R (AdicCompletion I R)) ≤ 𝔮.asIdeal ∧
        PrimeSpectrum.comap (algebraMap R (AdicCompletion I R)) 𝔮 = p := by
  let e : AdicCompletion I R →+* R ⧸ I := (AdicCompletion.evalOneₐ I).toRingHom
  have hker : RingHom.ker e = I.map (algebraMap R (AdicCompletion I R)) :=
    AdicCompletion.ker_evalOneₐ_eq_map I hI
  have hp' : (p.asIdeal.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  refine ⟨⟨(p.asIdeal.map (Ideal.Quotient.mk I)).comap e, Ideal.comap_isPrime _ _⟩, ?_, ?_⟩
  · rw [← hker]
    intro x hx
    change e x ∈ p.asIdeal.map (Ideal.Quotient.mk I)
    rw [RingHom.mem_ker.mp hx]
    exact (p.asIdeal.map (Ideal.Quotient.mk I)).zero_mem
  · ext r
    change e (algebraMap R _ r) ∈ p.asIdeal.map (Ideal.Quotient.mk I) ↔ r ∈ p.asIdeal
    have : e (algebraMap R _ r) = Ideal.Quotient.mk I r :=
      (AdicCompletion.evalOneₐ I).commutes r
    rw [this, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hp]

/-- **Two primes of the completion containing `I` with the same contraction are equal.** -/
theorem primeSpectrum_adicCompletion_eq_of_comap_eq (hI : I.FG)
    {𝔮 𝔮' : PrimeSpectrum (AdicCompletion I R)}
    (h : I.map (algebraMap R (AdicCompletion I R)) ≤ 𝔮.asIdeal)
    (h' : I.map (algebraMap R (AdicCompletion I R)) ≤ 𝔮'.asIdeal)
    (hc : PrimeSpectrum.comap (algebraMap R (AdicCompletion I R)) 𝔮 =
      PrimeSpectrum.comap (algebraMap R (AdicCompletion I R)) 𝔮') : 𝔮 = 𝔮' := by
  have key : ∀ {𝔮 𝔮' : PrimeSpectrum (AdicCompletion I R)},
      I.map (algebraMap R (AdicCompletion I R)) ≤ 𝔮.asIdeal →
      I.map (algebraMap R (AdicCompletion I R)) ≤ 𝔮'.asIdeal →
      PrimeSpectrum.comap (algebraMap R (AdicCompletion I R)) 𝔮 =
        PrimeSpectrum.comap (algebraMap R (AdicCompletion I R)) 𝔮' →
      𝔮.asIdeal ≤ 𝔮'.asIdeal := by
    intro 𝔮 𝔮' h h' hc a ha
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_map_pow I hI a 1
    rw [pow_one] at hr
    rw [mem_iff_of_sub_mem _ (h hr)] at ha
    have hr𝔮 : r ∈ (PrimeSpectrum.comap (algebraMap R (AdicCompletion I R)) 𝔮).asIdeal := ha
    rw [hc] at hr𝔮
    exact (mem_iff_of_sub_mem _ (h' hr)).mpr hr𝔮
  exact PrimeSpectrum.ext (le_antisymm (key h h' hc) (key h' h hc.symm))

end Completion

/-! ### The quotient by the sections with support -/

section Quotient

variable {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)) {M : Type u} [AddCommGroup M]
  [Module A M]

/-- **An element whose class modulo the sections with support in `T` is supported in `T` is
itself supported in `T`.** -/
theorem mem_sectionsWithSupportIn_of_mk_mem (m : M)
    (hm : Submodule.Quotient.mk (p := sectionsWithSupportIn A T M) m ∈
      sectionsWithSupportIn A T (M ⧸ sectionsWithSupportIn A T M)) :
    m ∈ sectionsWithSupportIn A T M := by
  rw [mem_sectionsWithSupportIn_iff] at hm ⊢
  intro 𝔓 h𝔓
  by_cases hle : Ideal.torsionOf A _ (Submodule.Quotient.mk
      (p := sectionsWithSupportIn A T M) m) ≤ 𝔓.asIdeal
  · exact hm hle
  obtain ⟨a, ha, ha𝔓⟩ := Set.not_subset.mp hle
  have ham : a • m ∈ sectionsWithSupportIn A T M := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact (Ideal.mem_torsionOf_iff _ a).mp ha
  rw [mem_sectionsWithSupportIn_iff] at ham
  apply ham
  intro b hb
  have : b * a ∈ Ideal.torsionOf A M m := by
    rw [Ideal.mem_torsionOf_iff, mul_smul]
    exact (Ideal.mem_torsionOf_iff _ b).mp hb
  exact (𝔓.isPrime.mem_or_mem (h𝔓 this)).resolve_right ha𝔓

/-- **No prime of a specialization-stable `T` is associated to the quotient of a module by its
sections with support in `T`.** -/
theorem notMem_associatedPrimes_quotient_sectionsWithSupportIn
    (hT : StableUnderSpecialization T) {𝔮 : PrimeSpectrum A} (h𝔮 : 𝔮 ∈ T) :
    𝔮.asIdeal ∉ associatedPrimes A (M ⧸ sectionsWithSupportIn A T M) := by
  intro h
  obtain ⟨-, x, hx⟩ := h
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hmem : Submodule.Quotient.mk (p := sectionsWithSupportIn A T M) m ∈
      sectionsWithSupportIn A T (M ⧸ sectionsWithSupportIn A T M) := by
    rw [mem_sectionsWithSupportIn_iff]
    intro 𝔓 h𝔓
    have h1 : (⊥ : Submodule A (M ⧸ sectionsWithSupportIn A T M)).colon
        {Submodule.Quotient.mk m} ≤ 𝔓.asIdeal := fun a ha => h𝔓 (by
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at ha
      exact (Ideal.mem_torsionOf_iff _ a).mpr ha)
    have h2 : 𝔮.asIdeal ≤ 𝔓.asIdeal := by
      rw [hx]
      exact (Ideal.radical_mono h1).trans 𝔓.isPrime.radical.le
    exact hT ((PrimeSpectrum.le_iff_specializes 𝔮 𝔓).mp h2) h𝔮
  have h0 := (Submodule.Quotient.mk_eq_zero _).mpr (mem_sectionsWithSupportIn_of_mk_mem T m hmem)
  apply 𝔮.isPrime.ne_top
  rw [hx, h0, Ideal.radical_eq_top]
  exact (Ideal.eq_top_iff_one _).mpr (by
    rw [Submodule.mem_colon_singleton, smul_zero]; exact Submodule.zero_mem _)

end Quotient

/-! ### An Artin–Rees consequence -/

/-- If an ideal is spanned by `s` and each element of `s` sends `x` into `N`, so does the ideal. -/
private theorem smul_mem_of_span_eq {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {s : Set A} {J : Ideal A} (hs : Ideal.span s = J) (N : Submodule A M) (x : M)
    (h : ∀ a ∈ s, a • x ∈ N) : ∀ a ∈ J, a • x ∈ N := by
  intro a ha
  have hle : Ideal.span s ≤ N.colon {x} :=
    Ideal.span_le.mpr fun b hb => Submodule.mem_colon_singleton.mpr (h b hb)
  exact Submodule.mem_colon_singleton.mp (hle (hs ▸ ha))

/-- **Artin–Rees for a colon.** If no nonzero element of a finite module `N` over a Noetherian ring
is annihilated by the ideal `Q`, then there is a `c` such that an element `x` with
`Q x ⊆ J^{n+c} N` lies in `J^n N`. -/
theorem exists_mem_pow_smul_top_of_forall_smul_mem {A : Type u} [CommRing A] [IsNoetherianRing A]
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N] (J Q : Ideal A)
    (hQ : ∀ z : N, (∀ a ∈ Q, a • z = 0) → z = 0) :
    ∃ c, ∀ n (x : N), (∀ a ∈ Q, a • x ∈ J ^ (n + c) • (⊤ : Submodule A N)) →
      x ∈ J ^ n • (⊤ : Submodule A N) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian Q : Q.FG)
  let φ : N →ₗ[A] (s → N) := LinearMap.pi fun a => (a : A) • LinearMap.id
  have hφapp : ∀ (z : N) (a : s), φ z a = (a : A) • z := fun _ _ => rfl
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    apply hQ z
    exact fun a ha => (Submodule.mem_bot A).mp (smul_mem_of_span_eq hs ⊥ z
      (fun b hb => by rw [Submodule.mem_bot, ← hφapp z ⟨b, hb⟩, hz]; rfl) a ha)
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul J (LinearMap.range φ)
  refine ⟨c, fun n x hx => ?_⟩
  have h₁ : φ x ∈ J ^ (n + c) • (⊤ : Submodule A (s → N)) := by
    rw [← Finset.univ_sum_single (φ x)]
    refine Submodule.sum_mem _ fun a _ => ?_
    have h := Submodule.mem_map_of_mem (f := LinearMap.single A (fun _ : s => N) a)
      (hx a (by rw [← hs]; exact Submodule.subset_span a.2))
    rw [Submodule.map_smul''] at h
    rw [hφapp]
    exact Submodule.smul_mono le_rfl le_top h
  have h₂ : φ x ∈ J ^ n • LinearMap.range φ := by
    have h₃ : φ x ∈ J ^ (n + c) • ⊤ ⊓ LinearMap.range φ := ⟨h₁, LinearMap.mem_range_self φ x⟩
    rw [hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel] at h₃
    exact Submodule.smul_mono le_rfl inf_le_right h₃
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h₂
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp h₂
  rwa [← hφ hyx]

/-- **An ideal with no prime strictly between it and `𝔮` is `𝔮`-primary up to a unit**: there are
`e` and `t ∉ 𝔮` with `t 𝔮^e ⊆ 𝔞`. -/
theorem exists_pow_mul_mem_of_forall_isPrime {A : Type u} [CommRing A] [IsNoetherianRing A]
    (𝔞 : Ideal A) (q : PrimeSpectrum A)
    (h : ∀ p : Ideal A, p.IsPrime → 𝔞 ≤ p → p ≤ q.asIdeal → p = q.asIdeal) :
    ∃ e, ∀ a ∈ q.asIdeal ^ e, ∃ t ∉ q.asIdeal, t * a ∈ 𝔞 := by
  classical
  by_cases h𝔞 : 𝔞 ≤ q.asIdeal
  swap
  · obtain ⟨t, ht𝔞, htq⟩ := Set.not_subset.mp h𝔞
    exact ⟨0, fun a _ => ⟨t, htq, 𝔞.mul_mem_right a ht𝔞⟩⟩
  let S : Set (Ideal A) := {p | p ∈ 𝔞.minimalPrimes ∧ ¬ p ≤ q.asIdeal}
  have hSfin : S.Finite := (Ideal.finite_minimalPrimes_of_isNoetherianRing A 𝔞).subset
    fun p hp => hp.1
  choose! u hu huq using fun p (hp : p ∈ S) => Set.not_subset.mp hp.2
  let t := ∏ p ∈ hSfin.toFinset, u p
  have ht : t ∉ q.asIdeal :=
    q.asIdeal.primeCompl.prod_mem fun p hp => huq p (hSfin.mem_toFinset.mp hp)
  have htS : ∀ p ∈ S, t ∈ p := fun p hp =>
    Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem u (hSfin.mem_toFinset.mpr hp)) (hu p hp)
  have hle : Ideal.span {t} * q.asIdeal ≤ 𝔞.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J ⟨h𝔞J, hJ⟩ => ?_
    obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le h𝔞J
    by_cases hpq : p ≤ q.asIdeal
    · have := h p hp.1.1 hp.1.2 hpq
      rw [this] at hpJ
      exact Ideal.mul_le_right.trans hpJ
    · have htp := htS p ⟨hp, hpq⟩
      exact Ideal.mul_le_left.trans ((Ideal.span_singleton_le_iff_mem _).mpr (hpJ htp))
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (Ideal.fg_of_isNoetherianRing _)
  refine ⟨e, fun a ha => ⟨t ^ e, fun h => ht (q.isPrime.mem_of_pow_mem e h), he ?_⟩⟩
  rw [mul_pow, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ha

/-! ### The essential constancy -/

section Tower

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
  (F : ℕᵒᵖ ⥤ ModuleCat.{u} R)

/-- The transition map `F_k → F_m` of an inverse system of modules, for `m ≤ k`. -/
abbrev towerMap {m k : ℕ} (h : m ≤ k) : F.obj (op k) →ₗ[R] F.obj (op m) :=
  (F.map (homOfLE h).op).hom

omit [IsNoetherianRing R] in
/-- The transition maps compose: `F_l → F_k → F_m` is the transition map `F_l → F_m`. -/
theorem towerMap_towerMap {l k m : ℕ} (h₁ : m ≤ k) (h₂ : k ≤ l) (x : F.obj (op l)) :
    towerMap F h₁ (towerMap F h₂ x) = towerMap F (h₁.trans h₂) x := by
  change (F.map (homOfLE h₂).op ≫ F.map (homOfLE h₁).op).hom x = _
  rw [← F.map_comp]
  rfl

/-- **The local hypothesis at a prime `𝔮`.** For every compatible system `Λ` of submodules of the
levels, annihilated by a fixed power of `I` and of depth at least one at `𝔮` in the uniform form
that an element killed by `𝔮` modulo `Λ_{k+d}` locally at `𝔮` maps into `Λ_k` locally at `𝔮`, the
elements of `F_{m₂}` killed by a power of `𝔮` modulo `Λ_{m₂}` locally at `𝔮` map into `Λ_m`
locally at `𝔮`, for `m₂` large. -/
def LocalTorsionProZeroAt (q : PrimeSpectrum R) : Prop :=
  ∀ Λ : ∀ n, Submodule R (F.obj (op n)),
    (∀ n, (Λ (n + 1)).map (towerMap F (Nat.le_succ n)) = Λ n) →
    (∃ c, ∀ n, ∀ a ∈ I ^ c, ∀ x ∈ Λ n, a • x = 0) →
    (∃ d, ∀ k (x : F.obj (op (k + d))),
      (∀ a ∈ q.asIdeal, ∃ t ∉ q.asIdeal, t • a • x ∈ Λ (k + d)) →
        ∃ t ∉ q.asIdeal, t • towerMap F (Nat.le_add_right k d) x ∈ Λ k) →
    ∀ m, ∃ m₂, ∃ h : m ≤ m₂, ∀ x : F.obj (op m₂),
      (∃ e, ∀ a ∈ q.asIdeal ^ e, ∃ t ∉ q.asIdeal, t • a • x ∈ Λ m₂) →
        ∃ t ∉ q.asIdeal, t • towerMap F h x ∈ Λ m

/-- **Stacks 0EIE for `s = 0`, in the form used by Stacks 0EJE.** For an adic inverse system of
finite modules over a Noetherian ring and a specialization-stable `T ⊆ V(I)` satisfying the local
hypothesis at every point of `T`, there are submodules `Λ_n` of the levels, annihilated by a fixed
power of `I`, such that the image in `F_n` of the sections with support in `T` of `F_m` is `Λ_n`
for all large `m`. -/
theorem exists_sectionsWithSupportIn_map_eq
    (hsurj : ∀ n, Function.Surjective (towerMap F (Nat.le_succ n)))
    (hker : ∀ n, LinearMap.ker (towerMap F (Nat.le_succ n)) =
      I ^ (n + 1) • (⊤ : Submodule R (F.obj (op (n + 1)))))
    [∀ n, Module.Finite R (F.obj (op n))]
    (T : Set (PrimeSpectrum R)) (hT : StableUnderSpecialization T)
    (hTI : ∀ q ∈ T, I ≤ q.asIdeal) (hloc : ∀ q ∈ T, LocalTorsionProZeroAt I F q) :
    ∃ (Λ : ∀ n, Submodule R (F.obj (op n))) (c : ℕ),
      (∀ n, ∀ a ∈ I ^ c, ∀ x ∈ Λ n, a • x = 0) ∧
      ∀ n, ∃ m₀, n ≤ m₀ ∧ ∀ m (h : n ≤ m), m₀ ≤ m →
        (sectionsWithSupportIn R T (F.obj (op m))).map (towerMap F h) = Λ n := by
  classical
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  -- the module of compatible families and its completion
  let L : ModuleCat.{u} R := limit F
  have hLc : IsAdicComplete I L :=
    Stacks.Coherent.moduleLimit_isAdicComplete F hsurj hker hIfg
  let Mh := AdicCompletion I L
  have : Module.Finite (AdicCompletion I R) Mh :=
    Stacks.Coherent.finite_adicCompletion_of_finite_reduction hIfg L
      (Stacks.Coherent.moduleLimit_zeroQuotient_finite F hsurj hker hIfg inferInstance)
  let e : L ≃ₗ[R] Mh := Stacks.Coherent.completeModuleEquivAdicCompletion I
  let ρ : ∀ n, Mh →ₗ[R] F.obj (op n) := fun n =>
    (limit.π F (op n)).hom ∘ₗ e.symm.toLinearMap
  have hρsurj : ∀ n, Function.Surjective (ρ n) := fun n =>
    (Stacks.Coherent.moduleLimit_projection_surjective F hsurj n).comp e.symm.surjective
  have hρker : ∀ n, LinearMap.ker (ρ n) = I ^ (n + 1) • (⊤ : Submodule R Mh) := fun n =>
    Stacks.Coherent.ker_comp_linearEquiv_pow_smul_top (I ^ (n + 1)) e.symm _
      (Stacks.Coherent.moduleLimit_projection_ker F hsurj hker hIfg n)
  have hρtr : ∀ {m k : ℕ} (h : m ≤ k) (x : Mh), towerMap F h (ρ k x) = ρ m x := by
    intro m k h x
    change (limit.π F (op k) ≫ F.map (homOfLE h).op).hom (e.symm x) = _
    rw [limit.w]
    rfl
  have hρzero : ∀ n (a : AdicCompletion I R) (y : Mh),
      a ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ (n + 1) → ρ n (a • y) = 0 := by
    intro n a y ha
    rw [← LinearMap.mem_ker, hρker, ← mem_pow_smul_top_iff_mem_map_pow_smul_top]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  have hρsmul : ∀ n (a : AdicCompletion I R) (r : R),
      a - algebraMap R (AdicCompletion I R) r ∈ (I.map (algebraMap R (AdicCompletion I R))) ^
        (n + 1) → ∀ y : Mh, ρ n (a • y) = r • ρ n y := by
    intro n a r har y
    have := hρzero n _ y har
    rw [sub_smul, map_sub, algebraMap_smul, sub_eq_zero] at this
    rw [this, map_smul]
  -- the locus over the completion and the sections with support in it
  let T' : Set (PrimeSpectrum (AdicCompletion I R)) :=
    {𝔮 | I.map (algebraMap R (AdicCompletion I R)) ≤ 𝔮.asIdeal ∧
      PrimeSpectrum.comap (algebraMap R (AdicCompletion I R)) 𝔮 ∈ T}
  have hT' : StableUnderSpecialization T' := by
    intro 𝔮 𝔮' h h𝔮
    refine ⟨h𝔮.1.trans ((PrimeSpectrum.le_iff_specializes 𝔮 𝔮').mpr h), ?_⟩
    have hle : PrimeSpectrum.comap (algebraMap R (AdicCompletion I R)) 𝔮 ≤
        PrimeSpectrum.comap (algebraMap R (AdicCompletion I R)) 𝔮' :=
      Ideal.comap_mono ((PrimeSpectrum.le_iff_specializes 𝔮 𝔮').mpr h)
    exact hT ((PrimeSpectrum.le_iff_specializes _ _).mp hle) h𝔮.2
  let H := sectionsWithSupportIn (AdicCompletion I R) T' Mh
  let Λ : ∀ n, Submodule R (F.obj (op n)) := fun n => (H.restrictScalars R).map (ρ n)
  have hΛmap : ∀ {m k : ℕ} (h : m ≤ k), (Λ k).map (towerMap F h) = Λ m := by
    intro m k h
    change ((H.restrictScalars R).map (ρ k)).map (towerMap F h) = (H.restrictScalars R).map (ρ m)
    rw [← Submodule.map_comp]
    have hcomp : towerMap F h ∘ₗ ρ k = ρ m := LinearMap.ext fun x => hρtr h x
    rw [hcomp]
  -- a power of `I` annihilates `H`
  obtain ⟨c, hc⟩ : ∃ c, ∀ a ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ c, ∀ h ∈ H,
      a • h = 0 := by
    obtain ⟨g, hg⟩ := (IsNoetherian.noetherian H : H.FG)
    have hgen : ∀ x ∈ g, ∃ c, (I.map (algebraMap R (AdicCompletion I R))) ^ c ≤
        Ideal.torsionOf (AdicCompletion I R) Mh x := by
      intro x hx
      have hxH : x ∈ H := hg ▸ Submodule.subset_span hx
      rw [mem_sectionsWithSupportIn_iff] at hxH
      have : I.map (algebraMap R (AdicCompletion I R)) ≤
          (Ideal.torsionOf (AdicCompletion I R) Mh x).radical := by
        rw [← PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
        exact fun 𝔓 h𝔓 => (hxH h𝔓).1
      exact Ideal.exists_pow_le_of_le_radical_of_fg this (Ideal.fg_of_isNoetherianRing _)
    choose! c hc using hgen
    refine ⟨g.sup c, fun a ha h hh => ?_⟩
    rw [← hg] at hh
    induction hh using Submodule.span_induction with
    | mem x hx =>
      exact (Ideal.mem_torsionOf_iff x a).mp
        (hc x hx (Ideal.pow_le_pow_right (Finset.le_sup hx) ha))
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
    | smul b x _ hx => rw [smul_comm, hx, smul_zero]
  have hΛann : ∀ n, ∀ a ∈ I ^ c, ∀ x ∈ Λ n, a • x = 0 := by
    intro n a ha x hx
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hx
    rw [← map_smul, ← algebraMap_smul (AdicCompletion I R) a h,
      hc _ (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha) h hh, map_zero]
  -- the image of `H` consists of sections with support in `T`
  have hΛT : ∀ m, Λ m ≤ sectionsWithSupportIn R T (F.obj (op m)) := by
    intro m x hx
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hx
    rw [mem_sectionsWithSupportIn_iff]
    intro p hp
    have hIm : I ^ (m + 1) ≤ p.asIdeal := fun a ha => hp ((Ideal.mem_torsionOf_iff _ a).mpr (by
      rw [← map_smul]
      exact (LinearMap.mem_ker).mp (hρker m ▸ Submodule.smul_mem_smul ha Submodule.mem_top)))
    have hIp : I ≤ p.asIdeal := p.isPrime.le_of_pow_le hIm
    obtain ⟨𝔮, hI𝔮, hc𝔮⟩ := exists_primeSpectrum_adicCompletion_comap_eq I hIfg p hIp
    have hh' : h ∈ H := hh
    rw [mem_sectionsWithSupportIn_iff] at hh'
    have h𝔮 : 𝔮 ∈ T' := by
      apply hh'
      intro a ha
      obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_map_pow I hIfg a (m + 1)
      have hrp : r ∈ p.asIdeal := hp ((Ideal.mem_torsionOf_iff _ r).mpr (by
        rw [← hρsmul m a r hr h, (Ideal.mem_torsionOf_iff h a).mp ha, map_zero]))
      have hr𝔮 : algebraMap R (AdicCompletion I R) r ∈ 𝔮.asIdeal := by
        rw [← hc𝔮] at hrp; exact hrp
      exact (mem_iff_of_sub_mem _ (hI𝔮 (Ideal.pow_le_self (Nat.succ_ne_zero m) hr))).mpr hr𝔮
    rw [← hc𝔮]
    exact h𝔮.2
  -- the depth condition at each point of `T`
  have hdepth : ∀ q ∈ T, ∃ d, ∀ k (x : F.obj (op (k + d))),
      (∀ a ∈ q.asIdeal, ∃ t ∉ q.asIdeal, t • a • x ∈ Λ (k + d)) →
        ∃ t ∉ q.asIdeal, t • towerMap F (Nat.le_add_right k d) x ∈ Λ k := by
    intro q hq
    let A := AdicCompletion I R
    let Q : Ideal A := q.asIdeal.map (algebraMap R A)
    have hsat : ∀ z : Mh ⧸ H, (∀ a ∈ Q, a • z = 0) → z = 0 := by
      intro z hz
      by_contra hz0
      have htop : Ideal.torsionOf A (Mh ⧸ H) z ≠ ⊤ := fun h =>
        hz0 (by simpa using (Ideal.mem_torsionOf_iff z (1 : A)).mp (h ▸ Submodule.mem_top))
      obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_minimalPrimes htop
      have hPprime : P.IsPrime := hP.1.1
      have hQP : Q ≤ P := fun a ha => hP.1.2 ((Ideal.mem_torsionOf_iff z a).mpr (hz a ha))
      have hPT : (⟨P, hPprime⟩ : PrimeSpectrum A) ∈ T' := by
        refine ⟨(Ideal.map_mono (hTI q hq)).trans hQP, ?_⟩
        have hle : q ≤ PrimeSpectrum.comap (algebraMap R A) ⟨P, hPprime⟩ :=
          Ideal.map_le_iff_le_comap.mp hQP
        exact hT ((PrimeSpectrum.le_iff_specializes _ _).mp hle) hq
      exact notMem_associatedPrimes_quotient_sectionsWithSupportIn T' hT' hPT
        (mem_associatedPrimes_of_mem_minimalPrimes_torsionOf z hP)
    obtain ⟨d, hd⟩ := exists_mem_pow_smul_top_of_forall_smul_mem
      (I.map (algebraMap R A)) Q hsat
    refine ⟨d, fun k x hx => ?_⟩
    obtain ⟨g, hg⟩ := (IsNoetherian.noetherian q.asIdeal : q.asIdeal.FG)
    choose! t ht htx using fun a (ha : a ∈ g) => hx a (by rw [← hg]; exact Submodule.subset_span ha)
    let t₀ := ∏ a ∈ g, t a
    have ht₀ : t₀ ∉ q.asIdeal := q.asIdeal.primeCompl.prod_mem ht
    have ht₀x : ∀ a ∈ q.asIdeal, a • t₀ • x ∈ Λ (k + d) :=
      smul_mem_of_span_eq hg (Λ (k + d)) (t₀ • x) fun b hb => by
        rw [smul_comm, show t₀ = (∏ a ∈ g.erase b, t a) * t b from
          (Finset.prod_erase_mul g t hb).symm, mul_smul]
        exact Submodule.smul_mem _ _ (htx b hb)
    obtain ⟨y, hy⟩ := hρsurj (k + d) (t₀ • x)
    have hyH : ∀ a ∈ Q, a • H.mkQ y ∈
        (I.map (algebraMap R A)) ^ ((k + 1) + d) • (⊤ : Submodule A (Mh ⧸ H)) := by
      intro a ha
      have hgen : ∀ r ∈ q.asIdeal, algebraMap R A r • H.mkQ y ∈
          (I.map (algebraMap R A)) ^ ((k + 1) + d) • (⊤ : Submodule A (Mh ⧸ H)) := by
        intro r hr
        obtain ⟨h, hh, hhy⟩ := Submodule.mem_map.mp (show ρ (k + d) (r • y) ∈ Λ (k + d) by
          rw [map_smul, hy]; exact ht₀x r hr)
        have hker : r • y - h ∈ LinearMap.ker (ρ (k + d)) := by
          rw [LinearMap.mem_ker, map_sub, hhy, sub_self]
        rw [hρker, ← mem_pow_smul_top_iff_mem_map_pow_smul_top] at hker
        have := Submodule.mem_map_of_mem (f := H.mkQ) hker
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ, map_sub,
          Submodule.mkQ_apply H h, (Submodule.Quotient.mk_eq_zero H).mpr hh, sub_zero,
          ← algebraMap_smul A r y, map_smul] at this
        rwa [show k + 1 + d = k + d + 1 by omega]
      exact smul_mem_of_span_eq rfl _ _ (by rintro _ ⟨r, hr, rfl⟩; exact hgen r hr) a ha
    have hy' := hd (k + 1) _ hyH
    have hmem : ρ k y ∈ Λ k := by
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp (show H.mkQ y ∈ Submodule.map H.mkQ
          ((I.map (algebraMap R A)) ^ (k + 1) • (⊤ : Submodule A Mh)) from by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]; exact hy')
      have hz' := (mem_pow_smul_top_iff_mem_map_pow_smul_top I (k + 1) z).mp hz
      have hzy' := (Submodule.Quotient.eq H).mp hzy
      have hρz : ρ k z = 0 := by
        rw [← LinearMap.mem_ker, hρker]; exact hz'
      have : ρ k y = ρ k (-(z - y)) := by rw [map_neg, map_sub, hρz, zero_sub, neg_neg]
      rw [this]
      exact Submodule.mem_map_of_mem (neg_mem hzy')
    refine ⟨t₀, ht₀, ?_⟩
    rw [← map_smul, ← hy, hρtr]
    exact hmem
  -- the local hypothesis turns into the local pro-vanishing for the quotient system
  have hΛle : ∀ {m k : ℕ} (h : m ≤ k), Λ k ≤ (Λ m).comap (towerMap F h) := fun h =>
    Submodule.map_le_iff_le_comap.mp (hΛmap h).le
  let M'' : ℕ → Type u := fun n => F.obj (op n) ⧸ Λ n
  let tr'' : ∀ {k m : ℕ}, m ≤ k → M'' k →ₗ[R] M'' m := fun h =>
    Submodule.mapQ (Λ _) (Λ _) (towerMap F h) (hΛle h)
  have htr'' : ∀ {l k m : ℕ} (h₁ : m ≤ k) (h₂ : k ≤ l) (x : M'' l),
      tr'' h₁ (tr'' h₂ x) = tr'' (h₁.trans h₂) x := by
    intro l k m h₁ h₂ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (towerMap F h₁ (towerMap F h₂ x)) = Submodule.Quotient.mk _
    rw [towerMap_towerMap]
  have hlocZ : ∀ q ∈ T, LocalProZeroAt M'' tr'' q := by
    intro q hq m
    obtain ⟨m₂, h, hm₂⟩ := hloc q hq Λ (fun n => hΛmap (Nat.le_succ n)) ⟨c, hΛann⟩
      (hdepth q hq) m
    refine ⟨m₂, h, fun x hx => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hcol : (Λ m₂).colon {x} = Ideal.torsionOf R (M'' m₂) (Submodule.Quotient.mk x) := by
      ext a
      rw [Submodule.mem_colon_singleton, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero]
    obtain ⟨e, he⟩ := exists_pow_mul_mem_of_forall_isPrime _ q
      (fun p hp hle hpq => hx p hp (hcol ▸ hle) hpq)
    obtain ⟨t, ht, htx⟩ := hm₂ x ⟨e, fun a ha => by
      obtain ⟨t, ht, hta⟩ := he a ha
      exact ⟨t, ht, by rw [← mul_smul]; exact Submodule.mem_colon_singleton.mp hta⟩⟩
    refine ⟨t, ht, ?_⟩
    change t • Submodule.Quotient.mk (towerMap F h x) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact htx
  refine ⟨Λ, c, hΛann, fun n => ?_⟩
  obtain ⟨k, hnk, hk⟩ := exists_forall_sectionsWithSupportIn_map_eq_zero T M'' tr'' htr'' hlocZ n
  refine ⟨k, hnk, fun m h hkm => le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := map_mem_sectionsWithSupportIn T (towerMap F hkm) hx
    have h0 := hk _ (map_mem_sectionsWithSupportIn T (Λ k).mkQ hx')
    change Submodule.Quotient.mk (towerMap F hnk (towerMap F hkm x)) = 0 at h0
    rw [Submodule.Quotient.mk_eq_zero, towerMap_towerMap] at h0
    exact h0
  · rw [← hΛmap h]
    exact Submodule.map_mono (hΛT m)

end Tower

end Stacks.LocalCohomology

end
