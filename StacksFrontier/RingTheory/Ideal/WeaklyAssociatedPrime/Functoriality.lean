module

public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Weakly associated primes and finite ring maps

Throughout, all rings are commutative with unit, and `φ : R → S` is a ring homomorphism. We
regard an `S`-module `M` also as an `R`-module via restriction of scalars along `φ`, i.e.
`r • m = φ(r) • m`, encoded by `[IsScalarTower R S M]`.

For an `A`-module `M` and `m ∈ M`, the annihilator of `m` is
`Ann_A(m) = { a ∈ A | a • m = 0 }`, which is `(A ∙ m).annihilator`, and a prime ideal `p` of
`A` is *weakly associated* to `M` if there is `m ∈ M` with `p` minimal among the primes
containing `Ann_A(m)`; this is `IsWeaklyAssociatedPrime A M p`, i.e.
`∃ m, p ∈ (A ∙ m).annihilator.minimalPrimes`. The induced map on spectra
`f = Spec(φ) : Spec(S) → Spec(R)` sends a prime `q` of `S` to its contraction
`φ⁻¹(q) = Ideal.comap (algebraMap R S) q`. The map `φ` is *finite* if `S`, viewed as an
`R`-module via `φ`, is finitely generated, i.e. `Module.Finite R S`.

If `φ` is finite then `WeakAss_R(M) = f(WeakAss_S(M))`, an equality of subsets of `Spec(R)`.
Only the inclusion `f(WeakAss_S(M)) ⊆ WeakAss_R(M)` requires finiteness; the other inclusion holds
for an arbitrary ring map. No Noetherian assumption is made.

## Main results

* `weakAss_subset_comap_image_weakAss`: `WeakAss_R(M) ⊆ f(WeakAss_S(M))` for an arbitrary ring
  map.
* `comap_isWeaklyAssociatedPrime_of_finite`: `f(WeakAss_S(M)) ⊆ WeakAss_R(M)` for a finite ring
  map.
* `weakAss_eq_comap_image_of_finite`: `WeakAss_R(M) = f(WeakAss_S(M))` for a finite ring map.

## References

* [Stacks Project, Tag 05E1](https://stacks.math.columbia.edu/tag/05E1)
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type*} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- Under restriction of scalars along `g = algebraMap R S`, the `R`-annihilator of the
cyclic submodule `R ∙ m` is the contraction of the `S`-annihilator of `S ∙ m`:
`Ann_R(m) = g⁻¹(Ann_S(m))`. -/
theorem annihilator_comap (m : M) :
    (R ∙ m).annihilator = Ideal.comap (algebraMap R S) (S ∙ m).annihilator := by
  ext r
  rw [Submodule.mem_annihilator_span_singleton, Ideal.mem_comap,
    Submodule.mem_annihilator_span_singleton, IsScalarTower.algebraMap_smul]

/-- The inclusion `WeakAss_R(M) ⊆ f(WeakAss_S(M))`, for an arbitrary ring map: if `p` is weakly
associated to `M` as an `R`-module, then there is a prime `q` of `S`, weakly associated to `M` as
an `S`-module, with `g⁻¹(q) = p`. -/
theorem weakAss_subset_comap_image_weakAss
    (p : Ideal R) (h : IsWeaklyAssociatedPrime R M p) :
    ∃ q : Ideal S, IsWeaklyAssociatedPrime S M q
      ∧ Ideal.comap (algebraMap R S) q = p := by
  obtain ⟨m, hm⟩ := h
  rw [annihilator_comap (S := S) m] at hm
  obtain ⟨q, hq, hqcomap⟩ := Ideal.exists_minimalPrimes_comap_eq (algebraMap R S) p hm
  exact ⟨q, ⟨m, hq⟩, hqcomap⟩

/-! ### The inclusion `f(WeakAss_S(M)) ⊆ WeakAss_R(M)` for a finite ring map -/

/-- A prime `p` containing an ideal `I` is a *minimal* prime over `I` as soon as every `f ∈ p`
has, up to multiplication by some `s ∉ p`, a power lying in `I`
(`∃ s ∉ p, ∃ n, s * f ^ n ∈ I`), that is, as soon as `p Aₚ` is the radical of `I Aₚ`. -/
theorem minimalPrimes_of_radical_condition {A : Type*} [CommRing A] (I p : Ideal A)
    (hp : p.IsPrime) (hIp : I ≤ p)
    (h : ∀ f ∈ p, ∃ s ∉ p, ∃ n : ℕ, s * f ^ n ∈ I) : p ∈ I.minimalPrimes := by
  refine ⟨⟨hp, hIp⟩, ?_⟩
  rintro p' ⟨hp', hIp'⟩ hle
  intro f hf
  obtain ⟨s, hs, n, hsf⟩ := h f hf
  have hmem : s * f ^ n ∈ p' := hIp' hsf
  rcases hp'.mem_or_mem hmem with h1 | h2
  · exact absurd (hle h1) hs
  · exact hp'.mem_of_pow_mem n h2

/-- If `p` is a minimal prime over `I` and `x ∈ p`, then some power of `x` lies in `I` up to a
unit-at-`p` multiplier, `∃ y ∉ p, ∃ n, y * x ^ n ∈ I`. This is the statement that
`p Aₚ = rad(I Aₚ)` in elementary form. -/
theorem exists_mul_pow_mem_of_mem_minimalPrimes {A : Type*} [CommRing A] {I p : Ideal A}
    (hp : p ∈ I.minimalPrimes) {x : A} (hx : x ∈ p) : ∃ y ∉ p, ∃ n : ℕ, y * x ^ n ∈ I := by
  have : p.IsPrime := hp.left.left
  by_contra hcon
  push Not at hcon
  set T : Submonoid A := p.primeCompl ⊔ Submonoid.powers x with hT
  have hdisj : Disjoint (I : Set A) (T : Set A) := by
    rw [Set.disjoint_left]
    rintro z hzI hzT
    rw [SetLike.mem_coe, hT, Submonoid.mem_sup] at hzT
    obtain ⟨y, hy, w, hw, rfl⟩ := hzT
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff w x).mp hw
    exact hcon y hy n hzI
  obtain ⟨P, hP, hIP, hPdisj⟩ := Ideal.exists_le_prime_disjoint I T hdisj
  have hPle : P ≤ p := fun a ha => by
    by_contra hap
    exact Set.disjoint_left.mp hPdisj ha (by rw [hT]; exact Submonoid.mem_sup_left hap)
  have hxP : x ∉ P := fun hxP =>
    Set.disjoint_left.mp hPdisj hxP
      (by rw [hT]; exact Submonoid.mem_sup_right (Submonoid.mem_powers x))
  exact absurd (le_antisymm hPle (hp.right ⟨hP, hIP⟩ hPle))
    (ne_of_lt (lt_of_le_of_ne hPle (by rintro rfl; exact hxP hx)))

/-- `s` annihilates `c • m` exactly when `s * c` annihilates `m`. -/
private theorem mem_annihilator_smul_iff (m : M) (c s : S) :
    s ∈ (S ∙ c • m).annihilator ↔ s * c ∈ (S ∙ m).annihilator := by
  rw [Submodule.mem_annihilator_span_singleton, Submodule.mem_annihilator_span_singleton,
    smul_smul]

omit [Module R M] [IsScalarTower R S M] in
/-- Under a finite ring map, for `q ∈ WeakAss_S(M)` there are a witness `m' : M`, an element
`x : S` and an exponent `t : ℕ` such that

* `(S ∙ m').annihilator ≤ q`,
* `q ∈ (S ∙ m').annihilator.minimalPrimes`,
* `x ^ t • m' = 0`, and
* `x` avoids every prime `q' ≠ q` of `S` lying over `p = comap g q`. -/
theorem exists_separating_witness_of_finite (hfin : Module.Finite R S)
    (q : Ideal S) (hq : IsWeaklyAssociatedPrime S M q) :
    ∃ (m' : M) (x : S) (t : ℕ),
      (S ∙ m').annihilator ≤ q ∧
      q ∈ (S ∙ m').annihilator.minimalPrimes ∧
      x ^ t • m' = 0 ∧
      (∀ q' ∈ (Ideal.comap (algebraMap R S) q).primesOver S, q' ≠ q → x ∉ q') := by
  obtain ⟨m, hm⟩ := hq
  set p := Ideal.comap (algebraMap R S) q with hp
  have hqp : q.IsPrime := hm.left.left
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hFfin : (p.primesOver S).Finite := Algebra.QuasiFinite.finite_primesOver p
  have hqF : q ∈ p.primesOver S := ⟨hqp, ⟨rfl⟩⟩
  have hprime : ∀ q' ∈ p.primesOver S, q'.IsPrime := fun q' hq' => hq'.left
  have hincomp : ∀ q' ∈ p.primesOver S, q' ≠ q → ¬ q ≤ q' := by
    intro q' hq'F hne hle
    have : q'.LiesOver p := hq'F.right
    have hlt : q < q' := lt_of_le_of_ne hle (Ne.symm hne)
    have hcomaplt := Ideal.IsIntegral.under_lt_under (R := R) hlt
    have e2 : Ideal.under R q' = p := (Ideal.LiesOver.over (P := q') (p := p)).symm
    rw [e2] at hcomaplt
    exact lt_irrefl _ hcomaplt
  obtain ⟨x, hxq, hxsep⟩ : ∃ x ∈ q, ∀ q' ∈ p.primesOver S, q' ≠ q → x ∉ q' := by
    set s := (hFfin.toFinset).erase q with hs
    have hsmem : ∀ i ∈ s, i ∈ p.primesOver S ∧ i ≠ q := by
      intro i hi
      rw [hs, Finset.mem_erase] at hi
      exact ⟨(Set.Finite.mem_toFinset hFfin).mp hi.right, hi.left⟩
    have key : ((q : Set S) ⊆ ⋃ i ∈ (s : Set (Ideal S)), (id i : Set S)) ↔ ∃ i ∈ s, q ≤ id i :=
      Ideal.subset_union_prime (s := s) (f := id) q q
        (fun i hi _ _ => hprime i (hsmem i hi).left)
    have hnotsub : ¬ ((q : Set S) ⊆ ⋃ i ∈ (s : Set (Ideal S)), (id i : Set S)) := by
      rw [key]
      rintro ⟨i, hi, hle⟩
      exact hincomp i (hsmem i hi).left (hsmem i hi).right hle
    rw [Set.not_subset] at hnotsub
    obtain ⟨x, hxq, hxnu⟩ := hnotsub
    refine ⟨x, hxq, ?_⟩
    intro q' hq'F hq'ne hxq'
    apply hxnu
    simp only [Set.mem_iUnion, id, exists_prop]
    refine ⟨q', ?_, hxq'⟩
    rw [Finset.mem_coe, hs, Finset.mem_erase]
    exact ⟨hq'ne, (Set.Finite.mem_toFinset hFfin).mpr hq'F⟩
  obtain ⟨y, hy, t, hyt⟩ := exists_mul_pow_mem_of_mem_minimalPrimes hm hxq
  rw [Submodule.mem_annihilator_span_singleton] at hyt
  have hKp : (S ∙ y • m).annihilator ≤ q := fun s hs =>
    (hqp.mem_or_mem (hm.left.right ((mem_annihilator_smul_iff m y s).mp hs))).resolve_right hy
  refine ⟨y • m, x, t, hKp, ?_, ?_, hxsep⟩
  · have hJK : (S ∙ m).annihilator ≤ (S ∙ y • m).annihilator := by
      intro s hs
      exact (mem_annihilator_smul_iff m y s).mpr (Ideal.mul_mem_right y _ hs)
    refine ⟨⟨hqp, hKp⟩, ?_⟩
    rintro p' ⟨hp'prime, hKp'⟩ hp'le
    exact hm.right ⟨hp'prime, le_trans hJK hKp'⟩ hp'le
  · rw [smul_smul, mul_comm, ← hyt]

/-- Let `g = algebraMap R S` be finite, let `q` be minimal over the `S`-annihilator of `m' : M`,
and let `x : S` with `x ^ t • m' = 0` avoid every prime `q' ≠ q` of `S` lying over
`p = comap g q`. Then for every `f ∈ p` there are `s ∉ p` and `n` with
`s * f ^ n ∈ (R ∙ m').annihilator`. -/
theorem exists_radical_of_separating_witness (hfin : Module.Finite R S)
    (q : Ideal S) (m' : M) (x : S) (t : ℕ)
    (hmin : q ∈ (S ∙ m').annihilator.minimalPrimes)
    (hxt : x ^ t • m' = 0)
    (hsep : ∀ q' ∈ (Ideal.comap (algebraMap R S) q).primesOver S, q' ≠ q → x ∉ q') :
    ∀ f ∈ Ideal.comap (algebraMap R S) q, ∃ s ∉ Ideal.comap (algebraMap R S) q,
      ∃ n : ℕ, s * f ^ n ∈ (R ∙ m').annihilator := by
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hqp : q.IsPrime := hmin.left.left
  intro f hf
  set g := algebraMap R S with hg
  set b : S := g f with hb
  have hbq : b ∈ q := hf
  obtain ⟨y₀, hy₀, n₀, hy₀b⟩ := exists_mul_pow_mem_of_mem_minimalPrimes hmin hbq
  set m2 : M := b ^ n₀ • m' with hm2
  set Ann' : Ideal S := (S ∙ m2).annihilator with hAnn'
  have hy₀Ann : y₀ ∈ Ann' := (mem_annihilator_smul_iff m' _ y₀).mpr hy₀b
  have hxtAnn : x ^ t ∈ Ann' := (mem_annihilator_smul_iff m' _ _).mpr
    (Ideal.mul_mem_right _ _ ((Submodule.mem_annihilator_span_singleton _ _).mpr hxt))
  -- `comap g Ann' ⊄ p`: otherwise going-up gives a prime `Q ⊇ Ann'` of `S` lying over `p`;
  -- `y₀ ∈ Ann' ⊆ Q` but `y₀ ∉ q` forces `Q ≠ q`, so `hsep` gives `x ∉ Q`, contradicting
  -- `x^t ∈ Ann' ⊆ Q` (and `Q` prime).
  have hclaim : ¬ Ideal.comap g Ann' ≤ Ideal.comap g q := by
    intro hle
    obtain ⟨Q, hQge, hQp, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.comap g q) Ann' hle
    have : Q.IsPrime := hQp
    have hQF : Q ∈ (Ideal.comap g q).primesOver S :=
      ⟨hQp, ⟨hQcomap.symm⟩⟩
    have hQne : Q ≠ q := fun hQeq => hy₀ (hQeq ▸ hQge hy₀Ann)
    exact hsep Q hQF hQne (hQp.mem_of_pow_mem t (hQge hxtAnn))
  rw [IsConcreteLE.not_le_iff_exists] at hclaim
  obtain ⟨s', hs'Ann, hs'p⟩ := hclaim
  rw [Ideal.mem_comap] at hs'Ann hs'p
  refine ⟨s', hs'p, n₀, ?_⟩
  rw [annihilator_comap (S := S) m', Ideal.mem_comap]
  rw [hAnn', mem_annihilator_smul_iff] at hs'Ann
  rwa [map_mul, map_pow, ← hb]

/-- For a finite ring map and a prime `q` of `S` weakly associated to `M`, there is a witness
`m' : M` whose `R`-annihilator is contained in `p = comap g q` and satisfies the radical condition
at `p`. -/
theorem exists_witness_radical_of_finite (hfin : Module.Finite R S)
    (q : Ideal S) (hq : IsWeaklyAssociatedPrime S M q) :
    ∃ m' : M, (R ∙ m').annihilator ≤ Ideal.comap (algebraMap R S) q ∧
      ∀ f ∈ Ideal.comap (algebraMap R S) q, ∃ s ∉ Ideal.comap (algebraMap R S) q,
        ∃ n : ℕ, s * f ^ n ∈ (R ∙ m').annihilator := by
  obtain ⟨m', x, t, hannle, hmin, hxt, hsep⟩ :=
    exists_separating_witness_of_finite hfin q hq
  refine ⟨m', ?_, exists_radical_of_separating_witness hfin q m' x t hmin hxt hsep⟩
  rw [annihilator_comap (S := S) m']
  exact Ideal.comap_mono hannle

/-- The inclusion `f(WeakAss_S(M)) ⊆ WeakAss_R(M)` for a finite ring map: if `q` is a prime
of `S` weakly associated to `M` over `S`, then its contraction `g⁻¹(q)` is weakly associated
to `M` over `R`. -/
@[ega "IV 3.1.10.1" "Contraction inclusion"]
theorem comap_isWeaklyAssociatedPrime_of_finite (hfin : Module.Finite R S)
    (q : Ideal S) (hq : IsWeaklyAssociatedPrime S M q) :
    IsWeaklyAssociatedPrime R M (Ideal.comap (algebraMap R S) q) := by
  have := hq.isPrime
  have hp : (Ideal.comap (algebraMap R S) q).IsPrime := Ideal.IsPrime.comap _
  obtain ⟨m', hle, hrad⟩ := exists_witness_radical_of_finite hfin q hq
  exact ⟨m', minimalPrimes_of_radical_condition _ _ hp hle hrad⟩

/-- Membership characterization: a prime `p` of `R` is weakly associated to `M` as an
`R`-module if and only if there is a prime `q` of `S`, weakly associated to `M` as an
`S`-module, whose contraction `φ⁻¹(q)` equals `p`. -/
theorem mem_weakAss_iff_exists_comap_of_finite (hfin : Module.Finite R S)
    (p : Ideal R) :
    IsWeaklyAssociatedPrime R M p
      ↔ ∃ q : Ideal S, IsWeaklyAssociatedPrime S M q ∧ Ideal.comap (algebraMap R S) q = p :=
  ⟨weakAss_subset_comap_image_weakAss p, fun ⟨q, hq, hqp⟩ =>
    hqp ▸ comap_isWeaklyAssociatedPrime_of_finite hfin q hq⟩

/-- For a finite ring map `φ : R → S` and an `S`-module `M`, the weakly associated primes of `M`
over `R` are exactly the contractions along `f = Spec(φ)` of the weakly associated primes of `M`
over `S`, i.e. `WeakAss_R(M) = f(WeakAss_S(M))` as subsets of `Spec(R)`. -/
@[stacks 05E1]
theorem weakAss_eq_comap_image_of_finite (hfin : Module.Finite R S) :
    {p : Ideal R | IsWeaklyAssociatedPrime R M p}
      = (Ideal.comap (algebraMap R S)) '' {q : Ideal S | IsWeaklyAssociatedPrime S M q} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  rw [mem_weakAss_iff_exists_comap_of_finite hfin p]

end
