module

public import StacksFrontier.RingTheory.GeometricallyIrreducible.SeparableClosure.SeparableTensor
import StacksCore.Tactic.EgaSgaAttribute

/-! # Descent of irreducibility of spectra of tensor products

Fraction-field reduction, descent from an algebraic closure, purely inseparable base change,
and tensor products with the algebraic closure of a perfect base. -/

@[expose] public section

open scoped TensorProduct

-- (A-G) "Geometrically pure" descent: irreducibility from the relative separable
-- closure.  Proof (informal Steps 4a/4b): write `Ls := separableClosure F L`; then
-- `L / Ls` has trivial relative separable closure.  Split `Ls ⊆ Ls' ⊆ L` with `Ls'`
-- purely transcendental over `Ls` and `L/Ls'` purely inseparable.  Base change of
-- the domain `B := K ⊗[F] Ls` along the purely transcendental `Ls'/Ls` is a domain
-- (localized polynomial ring); base change along the purely inseparable `L/Ls'` is a
-- Spec universal homeomorphism (Stacks 05K7/0BR8 — the one genuinely-absent
-- primitive), preserving irreducibility.  `Algebra.TensorProduct.cancelBaseChange`
-- relates `K ⊗[F] L` to `B ⊗[Ls] L`.
-- ===========================================================================
-- (A-G) DECOMPOSITION, following Steps 4 and Assembly of the informal argument.
-- We isolate one acyclic stub sub-lemma:
--
--   (G1) `irreducibleSpace_tensor_of_relSepClosed_bot` — THE ANALYTIC KERNEL,
--        stated with an ABSTRACT intermediate field `Ls` (a genuine type variable,
--        NOT the subtype `↥(separableClosure F L)`).  This avoids the instance
--        diamond between `Algebra.TensorProduct.leftAlgebra`'s module and
--        `TensorProduct.leftModule` that arises when the double tensor
--        `(↥(separableClosure F L) ⊗[F] K) ⊗[↥(separableClosure F L)] L` is formed in
--        the elaboration context of `irreducibleSpace_tensor_of_algSep_domain`.
--
--        Statement: given a tower `F ⊆ Ls ⊆ L` of fields (`IsScalarTower F Ls L`) with
--        `K ⊗[F] Ls` a DOMAIN and `separableClosure Ls L = ⊥` (i.e. `L/Ls` has trivial
--        relative separable closure — the "geometrically pure" condition), the spectrum
--        `Spec(K ⊗[F] L)` is irreducible.
--
--        Honest content (informal Steps 4a/4b/Assembly): set `B := K ⊗[F] Ls`
--        (a domain).  Base-change associativity `K ⊗[F] L ≅ B ⊗[Ls] L`
--        (`Algebra.TensorProduct.cancelBaseChange`/`comm`).  Factor `Ls ⊆ Ls' ⊆ L`
--        with `Ls'/Ls` purely transcendental (so `B ⊗[Ls] Ls'` stays a domain —
--        localized polynomial ring, Lemma E, reuse `finite_separableClosure_kernel_aux_domain`)
--        and `L/Ls'` purely inseparable algebraic (so `Spec(B' ⊗[Ls'] L)` is irreducible
--        by the purely-inseparable Spec universal homeomorphism Stacks 05K7/0BR8,
--        Lemma F — the single genuinely-absent primitive).  Will need its own
--        sub-decomposition (transcendental-domain + purely-inseparable nilradical-prime).
--
-- Assembly (`irreducibleSpace_tensor_of_algSep_domain`): set `Ls := separableClosure F L`
-- (the subtype is a Field with `Algebra F Ls`, `Algebra Ls L`, `IsScalarTower F Ls L`);
-- `separableClosure Ls L = ⊥` (`separableClosure.separableClosure_eq_bot`); `K ⊗[F] Ls`
-- is a domain (hBdom); apply (G1).  Because (G1)'s CONCLUSION is `K ⊗[F] L` (no double
-- tensor in the statement), instantiating it at the subtype `Ls` elaborates cleanly.
-- ===========================================================================

-- (G1a) THE GENUINE ANALYTIC KERNEL, now stated over an ABSTRACT integral-domain base
-- `B` (an `Ls`-algebra).  Stacks 037K Steps 4a/4b: `L / Ls` has trivial relative
-- separable closure (`separableClosure Ls L = ⊥`), i.e. `L/Ls` is "geometrically pure"
-- = transcendental ⊕ purely inseparable.  Then base change of the domain `B` along
-- `Ls → L` keeps `Spec` irreducible.
--   Honest content (Lemmas E + F + assembly):
--   factor `Ls ⊆ Ls' ⊆ L` with `Ls'/Ls` purely transcendental and `L/Ls'` purely
--   inseparable algebraic.  (E) `B ⊗[Ls] Ls'` stays a domain (localized polynomial
--   ring — REUSE `finite_separableClosure_kernel_aux_domain`'s technique).  (F) the
--   purely-inseparable base change `B' ⊗[Ls'] L` is a Spec universal homeomorphism
--   (Stacks 05K7/0BR8 — the single genuinely-absent primitive): reduce to a single
--   generator `Ls'(y) ≅ Ls'[T]/(T^{p^e}-a)`, so `B' ⊗[Ls'] Ls'(y) ≅ B'[T]/(T^{p^e}-a)`;
--   in char p, `T^{p^e}-a = (T-u)^{p^e}` (`sub_pow_char`), the quotient mod a
--   nilpotent-generated ideal has prime nilradical
--   (`PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`), then directed colimit
--   over finite purely-inseparable subextensions.
-- STUB — to be decomposed further (transcendental-domain step + purely-inseparable
-- nilradical-prime kernel + colimit).
-- ===========================================================================
-- (G1a) DECOMPOSITION (CORRECTED — fraction-field reduction + field-theoretic core).
-- The previous "purely transcendental ⊕ purely inseparable factorization" route was DEAD:
-- `geomPure_factor_exists` is FALSE (elliptic-function-field counterexample, see
-- a counterexample).  The correct, true-statement decomposition is:
--   (SL-1) reduce the abstract domain `B` to its fraction field `E := Frac(B)`;
--   (SL-2) the field-theoretic geometric-irreducibility core (Stacks 037K/04KZ):
--          for fields `E/Ls`, `L/Ls` with `Ls` separably closed in `L`, `Spec(E⊗[Ls]L)`
--          is irreducible.
-- ===========================================================================

-- (SL-1) Fraction-field reduction.  `B` a domain `Ls`-algebra; `E := FractionRing B`.
-- `B → E` is a localization, base change commutes with localization, so
-- `E ⊗[Ls] L = S'⁻¹(B ⊗[Ls] L)`.  Because `L` is a free `Ls`-module, `B → B ⊗[Ls] L` is
-- faithfully flat, so every minimal prime of `B ⊗[Ls] L` contracts to `(0) ⊆ B`, i.e. is
-- disjoint from `S' = image of B∖{0}`; hence minimal primes of `B ⊗ L` correspond to those
-- of `E ⊗ L`, and irreducibility (= unique minimal prime) transfers.
-- Mathlib: `IsLocalization`/`Localization` Spec homeomorphism onto primes disjoint from S',
-- `Module.Free` of base change, `PrimeSpectrum.irreducibleSpace_iff`,
-- faithfully-flat going-down.  We only need the ⟸ direction (field case ⟹ domain case).
-- Helper: in a flat algebra `R` over a domain `B`, the image of a nonzerodivisor is a
-- nonzerodivisor (multiplication by a regular element stays injective after flat base change).
private theorem flat_algebraMap_mem_nonZeroDivisors
    (B : Type*) [CommRing B] [IsDomain B] (R : Type*) [CommRing R] [Algebra B R]
    [Module.Flat B R] (p : B) (hp : p ∈ nonZeroDivisors B) :
    (algebraMap B R) p ∈ nonZeroDivisors R := by
  have hBinj : Function.Injective (LinearMap.lsmul B B p) := by
    intro a b hab
    simp only [LinearMap.lsmul_apply, smul_eq_mul] at hab
    exact mul_left_cancel₀ (nonZeroDivisors.ne_zero hp) hab
  have hT := Module.Flat.lTensor_preserves_injective_linearMap (M := R)
    (LinearMap.lsmul B B p) hBinj
  have hcomm : (TensorProduct.rid B R).toLinearMap.comp
      (LinearMap.lTensor R (LinearMap.lsmul B B p))
      = (LinearMap.lsmul B R p).comp (TensorProduct.rid B R).toLinearMap := by
    ext r
    simp [LinearMap.lsmul_apply, TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]
  have hRinj : Function.Injective (LinearMap.lsmul B R p) := by
    have h1 : Function.Injective ((TensorProduct.rid B R).toLinearMap.comp
        (LinearMap.lTensor R (LinearMap.lsmul B B p))) :=
      (TensorProduct.rid B R).injective.comp hT
    rw [hcomm] at h1
    intro a b hab
    obtain ⟨a', rfl⟩ := (TensorProduct.rid B R).surjective a
    obtain ⟨b', rfl⟩ := (TensorProduct.rid B R).surjective b
    exact congrArg _ (h1 hab)
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · apply hRinj
    simp only [LinearMap.lsmul_apply, map_zero]
    rw [Algebra.smul_def]; exact hy
  · apply hRinj
    simp only [LinearMap.lsmul_apply, map_zero]
    rw [Algebra.smul_def, mul_comm]; exact hy

/-- The preimage of the nilradical under an injective ring homomorphism is the nilradical. -/
private theorem comap_nilradical_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) : (nilradical S).comap f = nilradical R := by
  rw [nilradical, Ideal.comap_radical, Ideal.zero_eq_bot, Ideal.comap_bot_of_injective f hf]
  rfl

/-- Irreducibility of `Spec (B ⊗[Ls] L)` descends from `Spec (Frac B ⊗[Ls] L)`, for a domain
`B` over the field `Ls`. -/
theorem tensor_irreducible_of_fractionRing
    (Ls : Type*) [Field Ls] (B : Type*) [CommRing B] [IsDomain B] [Algebra Ls B]
    (L : Type*) [Field L] [Algebra Ls L]
    (hE : IrreducibleSpace (PrimeSpectrum ((FractionRing B) ⊗[Ls] L))) :
    IrreducibleSpace (PrimeSpectrum (B ⊗[Ls] L)) := by
  -- SANITY CHECK: when B is already a field, FractionRing B ≃ B and this is vacuous.
  -- B domain ⟹ B → FractionRing B localization ⟹ Spec(E⊗L) is the (pro-)open of primes
  -- of B⊗L disjoint from B∖{0}, which contains all minimal primes (faithfully flat
  -- base change), so unique-minimal-prime transfers from E⊗L to B⊗L.
  set R := B ⊗[Ls] L with hR
  set E := FractionRing B with hEdef
  -- `E ⊗[Ls] L = TensorProduct B R E` is a localization of `R` at the image of
  -- the nonzerodivisors of `B`.
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors B))
      (TensorProduct B R E) := IsLocalization.tensor E (nonZeroDivisors B)
  -- `R` is free, hence flat, over `B`; therefore the image of every nonzerodivisor of the
  -- domain `B` is a nonzerodivisor of `R`.  Hence the localization submonoid is contained in
  -- the nonzerodivisors of `R`.
  have hsub : Algebra.algebraMapSubmonoid R (nonZeroDivisors B) ≤ nonZeroDivisors R := by
    rintro x ⟨p, hp, rfl⟩
    exact flat_algebraMap_mem_nonZeroDivisors B R p hp
  -- Hence the localization map `R → TensorProduct B R E` is injective.
  have hlocinj : Function.Injective (algebraMap R (TensorProduct B R E)) :=
    IsLocalization.injective (TensorProduct B R E) hsub
  -- Identify `TensorProduct B R E` with `E ⊗[Ls] L`.
  have eRE : TensorProduct B R E ≃ₐ[B] E ⊗[Ls] L :=
    (Algebra.TensorProduct.comm B R E).trans
      ((Algebra.TensorProduct.cancelBaseChange Ls B E E L).restrictScalars B)
  -- Transfer irreducibility ⟺ prime nilradical.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hE ⊢
  -- `hE : (nilradical (E ⊗[Ls] L)).IsPrime`.  Transfer along `eRE` to `TensorProduct B R E`.
  have hET : (nilradical (TensorProduct B R E)).IsPrime := by
    rw [← comap_nilradical_of_injective (eRE : TensorProduct B R E →+* E ⊗[Ls] L) eRE.injective]
    exact hE.comap (eRE : TensorProduct B R E →+* E ⊗[Ls] L)
  -- The injective localization map `R → TensorProduct B R E` reflects prime nilradical.
  rw [← comap_nilradical_of_injective _ hlocinj]
  exact hET.comap (algebraMap R (TensorProduct B R E))

-- (SL-2) THE FIELD-THEORETIC GEOMETRIC-IRREDUCIBILITY CORE (Stacks Tag 037K / 04KZ).
-- For field extensions `E/Ls` and `L/Ls`, if `Ls` is separably algebraically closed in `L`
-- (`separableClosure Ls L = ⊥`) then `E ⊗[Ls] L` has a UNIQUE minimal prime, i.e.
-- `Spec(E ⊗[Ls] L)` is irreducible.  This is exactly "`L` is geometrically irreducible over
-- `Ls` ⟺ `Ls` is separably closed in `L`".  In char p the reduced ring need NOT be a domain
-- (nilpotents may appear); only the spectrum is irreducible.  Genuinely ABSENT from Mathlib;
-- the honest content (idempotents/minimal primes of `E ⊗ L` controlled by separable-algebraic
-- data over `Ls`; triviality of the separable closure ⟹ a single component).  THE genuine
-- analytic kernel — DECOMPOSED (Angle A via
-- the perfect closure of Ls).  Two acyclic open-goal sub-lemmas + a verified assembly.
--
-- ════════════════════════════════════════════════════════════════════════════════════
-- (SL-2/R) E→Ē REDUCTION (informal Layer 0, R1+R2).  Reduce to E algebraically closed:
-- for any field extension `E ⊆ Ē` realized as an `Ls`-algebra map `E →ₐ[Ls] Ē`, the
-- induced base change `E ⊗[Ls] L → Ē ⊗[Ls] L` is faithfully flat (apply the faithfully
-- flat functor `Ē ⊗[E] (−)` to the E-algebra `E ⊗[Ls] L`), so `Spec` is surjective
-- (`PrimeSpectrum.comap_surjective_of_faithfullyFlat`), hence dense image; a surjective
-- (dense-image) continuous map from an irreducible space has all of the target irreducible
-- (`IsIrreducible.image`, `IsIrreducible.closure`).  So irreducibility descends Ē ⟹ E.
-- Stated for an arbitrary `Ls`-algebra field map; the caller supplies `Ē = AlgebraicClosure E`.
/-- Irreducibility of `Spec (E ⊗[Ls] L)` follows from irreducibility of
`Spec (Ebar ⊗[Ls] L)` for an extension `Ebar/E` over `Ls`. -/
@[ega "IV 4.4.1" "special case"]
theorem tensorField_irreducible_descent_of_algClosure
    (Ls : Type*) [Field Ls] (E : Type*) [Field E] [Algebra Ls E]
    (Ebar : Type*) [Field Ebar] [Algebra Ls Ebar] [Algebra E Ebar]
    [IsScalarTower Ls E Ebar]
    (L : Type*) [Field L] [Algebra Ls L]
    (hEbar : IrreducibleSpace (PrimeSpectrum (Ebar ⊗[Ls] L))) :
    IrreducibleSpace (PrimeSpectrum (E ⊗[Ls] L)) := by
  -- The ring map `E ⊗[Ls] L → Ebar ⊗[Ls] L` (= base change of `E ⊆ Ebar` along free `L`)
  -- is faithfully flat (Ebar/E is a field extension, faithfully flat; base change preserves
  -- it), so `PrimeSpectrum.comap` is surjective ⟹ dense image; descend irreducibility.
  -- We realize the map as `R0 → R0 ⊗[E] Ebar` for the E-algebra `R0 := E ⊗[Ls] L`, whose
  -- base change `R0 ⊗[E] Ebar` is faithfully flat over `R0`, and identify its spectrum with
  -- `Spec(Ebar ⊗[Ls] L)` via `comm` then `cancelBaseChange`.
  set R0 := E ⊗[Ls] L with hR0
  let eqv : (TensorProduct E R0 Ebar) ≃+* (Ebar ⊗[Ls] L) :=
    (Algebra.TensorProduct.comm E R0 Ebar).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange Ls E Ebar Ebar L).toRingEquiv
  have hT : IrreducibleSpace (PrimeSpectrum (TensorProduct E R0 Ebar)) := by
    let H : PrimeSpectrum (TensorProduct E R0 Ebar) ≃ₜ PrimeSpectrum (Ebar ⊗[Ls] L) :=
    { toFun := PrimeSpectrum.comap eqv.symm.toRingHom
      invFun := PrimeSpectrum.comap eqv.toRingHom
      left_inv := by intro x; simp [← PrimeSpectrum.comap_comp_apply]
      right_inv := by intro x; simp [← PrimeSpectrum.comap_comp_apply]
      continuous_toFun := PrimeSpectrum.continuous_comap _
      continuous_invFun := PrimeSpectrum.continuous_comap _ }
    exact H.irreducibleSpace_iff.mpr hEbar
  have hsurj := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := R0) (B := TensorProduct E R0 Ebar)
  exact Function.Surjective.irreducibleSpace
      (PrimeSpectrum.continuous_comap _) hsurj
--
-- ════════════════════════════════════════════════════════════════════════════════════
-- (K1) GLOBAL-FROBENIUS PURELY-INSEPARABLE Spec-IRREDUCIBILITY KERNEL.  For `B'` a domain
-- that is an `Ls'`-algebra and `L/Ls'` purely inseparable, `Spec(B' ⊗[Ls'] L)` is irreducible.
-- FULLY PROVED (global Frobenius: every element of `R := B' ⊗[Ls'] L` has a `q`-power, `q` the
-- exponential characteristic, inside the injective image of `B'`; the nilradical of `R` is
-- then prime since `B'` is a reduced domain).  This is the reusable kernel (Stacks 05K7/0BR8)
-- recovered from commit 6337715; it is consumed by A1 (the perfect-closure purely-inseparable
-- migration step) below.
/-- For a purely inseparable extension `L/Ls'` and a domain `B'` over `Ls'`, the space
`Spec (B' ⊗[Ls'] L)` is irreducible, base change along a purely inseparable extension being a
universal homeomorphism. -/
@[ega "IV 4.3.2" "special case", ega "IV 4.3.4" "purely inseparable L/k"]
theorem irreducibleSpace_baseChange_purelyInseparable
    (Ls' : Type*) [Field Ls'] (B' : Type*) [CommRing B'] [IsDomain B'] [Algebra Ls' B']
    (L : Type*) [Field L] [Algebra Ls' L] [IsPurelyInseparable Ls' L] :
    IrreducibleSpace (PrimeSpectrum (B' ⊗[Ls'] L)) := by
  -- is a universal homeomorphism ⟹ irreducible since Spec(B') is (B' a domain).)
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  set R := B' ⊗[Ls'] L with hR
  have : Nontrivial R := by infer_instance
  obtain ⟨q, hq⟩ := ExpChar.exists Ls'
  have hqne : q ≠ 0 := (expChar_pos Ls' q).ne'
  have hinjLs : Function.Injective (algebraMap Ls' R) := (algebraMap Ls' R).injective
  have : ExpChar R q := expChar_of_injective_ringHom hinjLs q
  set φ : B' →+* R := Algebra.TensorProduct.includeLeftRingHom with hφ
  have hφinj : Function.Injective φ := by
    have hL : Function.Injective (algebraMap Ls' L) := (algebraMap Ls' L).injective
    exact Algebra.TensorProduct.includeLeft_injective (S := Ls') hL
  have hext : ∀ (z : R) (m : ℕ), z ^ (q ^ m) ∈ φ.range →
      ∀ N, m ≤ N → z ^ (q ^ N) ∈ φ.range := by
    intro z m hm N hN
    have hzz : z ^ (q ^ N) = (z ^ (q ^ m)) ^ (q ^ (N - m)) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hN]
    rw [hzz]; exact Subring.pow_mem _ hm _
  have key : ∀ z : R, ∃ n : ℕ, z ^ (q ^ n) ∈ φ.range := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul b x =>
        obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem Ls' q x
        refine ⟨n, ?_⟩
        have hpt : (b ⊗ₜ[Ls'] x : R) ^ (q ^ n) = φ (c • b ^ (q ^ n)) := by
          rw [Algebra.TensorProduct.tmul_pow, ← hc, hφ]
          show _ = Algebra.TensorProduct.includeLeftRingHom (c • b ^ (q ^ n))
          rw [Algebra.TensorProduct.includeLeftRingHom_apply,
            Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
        rw [hpt]; exact ⟨_, rfl⟩
    | add z w hz hw =>
        obtain ⟨nz, hnz⟩ := hz
        obtain ⟨nw, hnw⟩ := hw
        refine ⟨max nz nw, ?_⟩
        have hadd : (z + w) ^ (q ^ (max nz nw))
            = z ^ (q ^ (max nz nw)) + w ^ (q ^ (max nz nw)) := by
          have := (iterateFrobenius R q (max nz nw)).map_add z w
          simpa [iterateFrobenius_def] using this
        rw [hadd]
        exact Subring.add_mem _ (hext z nz hnz _ (le_max_left _ _))
          (hext w nw hnw _ (le_max_right _ _))
  constructor
  · rw [Ideal.ne_top_iff_one, mem_nilradical]
    rintro ⟨k, hk⟩
    simp at hk
  · intro x y hxy
    rw [mem_nilradical] at hxy
    obtain ⟨nx, ax, hax⟩ := key x
    obtain ⟨ny, ay, hay⟩ := key y
    set N := max nx ny with hN
    have hxN : x ^ (q ^ N) ∈ φ.range := hext x nx ⟨ax, hax⟩ N (le_max_left _ _)
    have hyN : y ^ (q ^ N) ∈ φ.range := hext y ny ⟨ay, hay⟩ N (le_max_right _ _)
    obtain ⟨a, ha⟩ := hxN
    obtain ⟨b, hb⟩ := hyN
    have hqNne : q ^ N ≠ 0 := pow_ne_zero _ hqne
    have heq : (x * y) ^ (q ^ N) = φ (a * b) := by
      rw [mul_pow, ← ha, ← hb, map_mul]
    have hprodnil : IsNilpotent ((x * y) ^ (q ^ N)) := by
      obtain ⟨k, hk⟩ := hxy
      refine ⟨k, ?_⟩
      rw [← pow_mul, mul_comm (q ^ N) k, pow_mul, hk, zero_pow hqNne]
    rw [heq] at hprodnil
    have habnil : IsNilpotent (a * b) := by
      obtain ⟨k, hk⟩ := hprodnil
      exact ⟨k, hφinj (by rwa [map_pow, map_zero])⟩
    have hab0 : a * b = 0 := IsReduced.eq_zero _ habnil
    rcases mul_eq_zero.mp hab0 with h0 | h0
    · left
      rw [mem_nilradical]
      exact ⟨q ^ N, by rw [← ha, h0, map_zero]⟩
    · right
      rw [mem_nilradical]
      exact ⟨q ^ N, by rw [← hb, h0, map_zero]⟩
--
-- ════════════════════════════════════════════════════════════════════════════════════
-- (SL-2/AC-A2) THE PERFECT-BASE SEPARABLE DOMAIN CORE (informal A2).  THE genuine residual
-- analytic kernel of SL-2/AC.  Over a PERFECT field `P`, every field extension is separable;
-- a finitely generated separable extension `L'/P` with `separableClosure P L' = ⊥` admits a
-- separating transcendence basis (LEGITIMATE because `P` is perfect — the move forbidden over
-- the imperfect `Ls`), reducing `Ē ⊗[P] L'` along `P ⊆ P(t₁,…,t_r) ⊆ L'` to a localized
-- polynomial ring (a domain) tensored with a finite separable factor; the separable domain
-- core (K2 = `geomIrred_tensor_sep_isDomain` / `tensorSep_finite_isField`) makes the result a
-- DOMAIN.  Stated abstractly with a perfect base `P`; SL-2/AC instantiates `P := perfectClosure
-- Ls Ebar`.  (Needs its own decomposition: A2-transcendental + A2-finite-separable.)
-- (A2-Claim1) `Ω ⊗[P] L'` is a FIELD, where `Ω := ↥(algebraicClosure P Ebar)` is the algebraic
-- closure of `P` inside the algebraically closed `Ebar` (so `Ω` is itself algebraically closed,
-- and over the perfect `P` it is separable algebraic over `P`).  Stated with `Ω` ABSTRACT (an
-- algebraically-closed, separable-algebraic `P`-extension) to avoid a subtype diamond; A2
-- instantiates `Ω := ↥(algebraicClosure P Ebar)` at the call site.  Math (Claim 1):
-- `Ω/P` is separable algebraic (perfect base), so `Ω ⊗[P] L'` is a directed colimit of
-- the finite-separable stages `Ωᵢ ⊗[P] L'`, each a FIELD by `tensorSep_finite_isField` (uses
-- `separableClosure P L' = ⊥`); a directed colimit of fields along injective maps is a field.
set_option synthInstance.maxHeartbeats 40000 in
-- needed: instance search in `perfectBase_algClosure_tensor_isField` exceeds the default
-- instance-search budget
/-- Let `P` be a perfect field, `Ω` an algebraic closure of `P`, and `L'` an extension of `P`
whose separable closure over `P` is trivial. Then `Ω ⊗[P] L'` is a field. -/
@[ega "IV 4.3.6" "special case", ega "IV 6.7.4.1" "special case"]
theorem perfectBase_algClosure_tensor_isField
    (P : Type*) [Field P] [PerfectField P]
    (Ω : Type*) [Field Ω] [Algebra P Ω] [IsAlgClosed Ω]
    [Algebra.IsSeparable P Ω] [Algebra.IsAlgebraic P Ω]
    (L' : Type*) [Field L'] [Algebra P L']
    (hsc : separableClosure P L' = ⊥) :
    IsField (Ω ⊗[P] L') := by
  -- Ω = sep/alg closure of perfect P = ⋃ finite separable Ωᵢ; Ω⊗[P]L' = colim (Ωᵢ⊗[P]L'), each a
  -- FIELD by tensorSep_finite_isField (hsc essential: ℚ(√2)⊗ℚ(√2) splits without it); directed
  -- colimit of fields along injective maps is a field. TRUE.
  -- Ω is a separable closure of the perfect P (algebraically closed ⟹ separably closed,
  -- and separable algebraic over P), hence P-isomorphic to `SeparableClosure P`.
  have : IsSepClosure P Ω := ⟨IsSepClosed.of_isAlgClosed Ω, inferInstance⟩
  let eΩ : Ω ≃ₐ[P] (SeparableClosure P) := IsSepClosure.equiv P Ω (SeparableClosure P)
  -- Transport: Ω ⊗[P] L' ≃ₐ[P] (SeparableClosure P) ⊗[P] L' ≃ₐ[P] L' ⊗[P] SeparableClosure P.
  let e1 : (Ω ⊗[P] L') ≃ₐ[P] ((SeparableClosure P) ⊗[P] L') :=
    Algebra.TensorProduct.congr eΩ (AlgEquiv.refl)
  let e2 : ((SeparableClosure P) ⊗[P] L') ≃ₐ[P] (L' ⊗[P] (SeparableClosure P)) :=
    Algebra.TensorProduct.comm P (SeparableClosure P) L'
  let e : (Ω ⊗[P] L') ≃ₐ[P] (L' ⊗[P] (SeparableClosure P)) := e1.trans e2
  -- It suffices to show `L' ⊗[P] SeparableClosure P` is a field.
  suffices h : IsField (L' ⊗[P] (SeparableClosure P)) by
    exact MulEquiv.isField h e.toMulEquiv
  -- `L' ⊗[P] SeparableClosure P` is a directed colimit of the finite-separable stages
  -- `L' ⊗[P] Lᵢ` (each a field by `tensorSep_finite_isField`); it is a domain by
  -- `geomIrred_tensor_sep_isDomain`, and every nonzero element is invertible since it lies
  -- in some finite stage where it is a unit (whose inverse maps up through the field hom).
  set R := L' ⊗[P] (SeparableClosure P) with hR
  have : IsDomain R := geomIrred_tensor_sep_isDomain P L' hsc
  let φ : (L : IntermediateField P (SeparableClosure P)) → (L' ⊗[P] L →ₐ[L'] R) :=
    fun L => Algebra.TensorProduct.map (AlgHom.id L' L') L.val
  have hφinj : ∀ (L : IntermediateField P (SeparableClosure P)), Function.Injective (φ L) := by
    intro L
    have key : (φ L).toLinearMap = LinearMap.lTensor L' (L.val.toLinearMap) := by
      apply TensorProduct.ext'
      intro x y
      show (φ L) (x ⊗ₜ[P] y) = LinearMap.lTensor L' (L.val.toLinearMap) (x ⊗ₜ[P] y)
      rw [LinearMap.lTensor_tmul]
      show Algebra.TensorProduct.map (AlgHom.id L' L') L.val (x ⊗ₜ[P] y) = _
      rw [Algebra.TensorProduct.map_tmul]
      rfl
    rw [show ⇑(φ L) = ⇑(LinearMap.lTensor L' (L.val.toLinearMap)) from by rw [← key]; rfl]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ L.val.injective
  have hmono : ∀ (L₁ L₂ : IntermediateField P (SeparableClosure P)), L₁ ≤ L₂ →
      (φ L₁).range ≤ (φ L₂).range := by
    intro L₁ L₂ h
    have hfac : φ L₁ = (φ L₂).comp
        (Algebra.TensorProduct.map (AlgHom.id L' L') (IntermediateField.inclusion h)) := by
      show Algebra.TensorProduct.map (AlgHom.id L' L') (L₁.val) = _
      rw [← Algebra.TensorProduct.map_comp]; congr 1
    rw [hfac, AlgHom.range_comp]
    rintro x ⟨y, -, rfl⟩
    exact ⟨_, rfl⟩
  have hcov : ∀ x : R, ∃ L : IntermediateField P (SeparableClosure P),
      FiniteDimensional P L ∧ x ∈ (φ L).range := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨⊥, inferInstance, Subalgebra.zero_mem _⟩
    | tmul k s =>
        refine ⟨IntermediateField.adjoin P {s}, ?_, ?_⟩
        · exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
        · refine ⟨k ⊗ₜ[P] ⟨s, ?_⟩, ?_⟩
          · exact IntermediateField.subset_adjoin P {s} (Set.mem_singleton s)
          · show Algebra.TensorProduct.map (AlgHom.id L' L') _ _ = _
            rw [Algebra.TensorProduct.map_tmul]; rfl
    | add a b ha hb =>
        obtain ⟨L₁, hL₁, haL₁⟩ := ha
        obtain ⟨L₂, hL₂, hbL₂⟩ := hb
        refine ⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, ?_⟩
        exact Subalgebra.add_mem _ (hmono L₁ (L₁ ⊔ L₂) le_sup_left haL₁)
          (hmono L₂ (L₁ ⊔ L₂) le_sup_right hbL₂)
  refine ⟨exists_pair_ne R, fun x y => mul_comm x y, ?_⟩
  intro a ha
  obtain ⟨L, hL, haL⟩ := hcov a
  have : FiniteDimensional P L := hL
  have hfield : IsField (L' ⊗[P] L) := tensorSep_finite_isField P L' hsc L
  let : Field (L' ⊗[P] L) := hfield.toField
  have : IsDomain (L' ⊗[P] L) := Field.isDomain
  -- The range of `φ L` is a field, isomorphic to the field `L' ⊗[P] L`.
  let e : (L' ⊗[P] L) ≃ₐ[L'] (φ L).range := AlgEquiv.ofInjective (φ L) (hφinj L)
  have hrangeField : IsField ((φ L).range) := MulEquiv.isField hfield e.symm.toMulEquiv
  -- `a` sits in the range; as a nonzero element of that field it has an inverse there,
  -- whose image in `R` (via the subalgebra inclusion) is a right inverse of `a`.
  set a' : (φ L).range := ⟨a, haL⟩ with ha'
  have ha'0 : a' ≠ 0 := by
    intro h
    apply ha
    have : (a' : R) = 0 := by rw [h]; rfl
    simpa [ha'] using this
  obtain ⟨c, hc⟩ := hrangeField.mul_inv_cancel ha'0
  refine ⟨(c : R), ?_⟩
  have : ((a' * c : (φ L).range) : R) = ((1 : (φ L).range) : R) := by rw [hc]
  rw [Subalgebra.coe_mul, Subalgebra.coe_one] at this
  simpa [ha'] using this
--
-- (A2-core) GEOMETRIC IRREDUCIBILITY OVER AN ALGEBRAICALLY CLOSED BASE (the genuine residual
-- kernel of A2).  `Ω` algebraically closed (= alg. closure of `P` inside `Ebar`); `Ebar` an
-- algebraically closed `Ω`-algebra; `L'/P` finitely generated; and `Ω ⊗[P] L'` a FIELD
-- (hypothesis `hF`, supplied by A2-Claim1).  Then `Ebar ⊗[P] L'` is a domain.  Route
-- (Claim 2 + Step 2): base-change associativity `Ebar ⊗[P] L' ≅
-- Ebar ⊗[Ω] (Ω ⊗[P] L')` (`cancelBaseChange P Ω Ebar Ebar L'`); set `F' := Ω ⊗[P] L'`, a f.g.
-- field over the ALGEBRAICALLY CLOSED `Ω`, so `Ω` is algebraically closed in `F'` ⟹ a separating
-- transcendence basis gives `Ē ⊗[Ω] F'` a localized polynomial ring (domain) over `Ē`
-- (`finite_separableClosure_kernel_aux_domain` + `AlgebraicIndependent.aevalEquivField`).  This is
-- where alg-closedness of the base makes the geometric-irreducibility input automatic (no residual
-- separable-algebraic constants).  Takes `hF` so it is strictly an ASSEMBLY of Claim 1.
-- (A2-core-FG) f.g. bookkeeping: if `L'/P` is finitely generated as a field and `Ω ⊗[P] L'` is a
-- field `F'`, then `F'/Ω` is finitely generated as a field.  The images `1 ⊗ gᵢ` of the
-- generators `gᵢ` of `⊤ = IntermediateField.adjoin P S` (S finite) generate `⊤ : IntermediateField
-- Ω F'`, since `F' = Ω ⊗[P] L'` is generated over `Ω` by the pure tensors `1 ⊗ x` and `x ↦ 1 ⊗ x`
-- is a P-algebra map `L' → F'` whose image, adjoined to `Ω`, is everything (the `Ω ⊗ 1` part is
-- already in `Ω`).  Routine; no geometry.
/-- If `L'` is a finitely generated field extension of `P` and `Ω ⊗[P] L'` is a field, then it
is finitely generated as a field over `Ω`. -/
theorem algClosure_tensor_fg
    (P : Type*) [Field P]
    (Ω : Type*) [Field Ω] [Algebra P Ω]
    (L' : Type*) [Field L'] [Algebra P L']
    (hfg : (⊤ : IntermediateField P L').FG)
    (hF : IsField (Ω ⊗[P] L')) :
    letI : Field (Ω ⊗[P] L') := hF.toField
    (⊤ : IntermediateField Ω (Ω ⊗[P] L')).FG := by
  -- images 1 ⊗ gᵢ of a finite P-generating set {gᵢ} of L').
  let : Field (Ω ⊗[P] L') := hF.toField
  classical
  rw [IntermediateField.fg_def] at hfg
  obtain ⟨S, hSfin, hSadj⟩ := hfg
  refine ⟨hSfin.toFinset.image (Algebra.TensorProduct.includeRight : L' →ₐ[P] _), ?_⟩
  rw [Finset.coe_image, Set.Finite.coe_toFinset]
  set K : IntermediateField Ω (Ω ⊗[P] L') :=
    IntermediateField.adjoin Ω (Algebra.TensorProduct.includeRight '' S) with hK
  have hmem : ∀ b : L', (Algebra.TensorProduct.includeRight b : Ω ⊗[P] L') ∈ K := by
    have hsub : S ⊆ ((K.restrictScalars P).comap
        (Algebra.TensorProduct.includeRight)) := by
      intro s hs
      show Algebra.TensorProduct.includeRight s ∈ K
      exact IntermediateField.subset_adjoin _ _ ⟨s, hs, rfl⟩
    have hle : IntermediateField.adjoin P S ≤
        (K.restrictScalars P).comap (Algebra.TensorProduct.includeRight) :=
      IntermediateField.adjoin_le_iff.mpr hsub
    rw [hSadj] at hle
    intro b
    exact hle (by trivial)
  -- pure tensors lie in K
  have hpure : ∀ x : Ω ⊗[P] L', x ∈ {t | ∃ a b, a ⊗ₜ[P] b = t} →
      x ∈ (K.toSubalgebra.restrictScalars P) := by
    rintro x ⟨a, b, rfl⟩
    have hx : a ⊗ₜ[P] b
        = algebraMap Ω (Ω ⊗[P] L') a * Algebra.TensorProduct.includeRight b := by
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul]; simp
    show a ⊗ₜ[P] b ∈ K.toSubalgebra
    rw [hx]
    exact mul_mem (K.algebraMap_mem a) (hmem b)
  rw [eq_top_iff]
  rintro x -
  have hxsub : x ∈ K.toSubalgebra.restrictScalars P := by
    have htop : Algebra.adjoin P {t : Ω ⊗[P] L' | ∃ a b, a ⊗ₜ[P] b = t} = ⊤ :=
      Algebra.TensorProduct.adjoin_tmul_eq_top P Ω L'
    have hsub2 : Algebra.adjoin P {t : Ω ⊗[P] L' | ∃ a b, a ⊗ₜ[P] b = t}
        ≤ K.toSubalgebra.restrictScalars P :=
      Algebra.adjoin_le hpure
    have hx : x ∈ Algebra.adjoin P {t : Ω ⊗[P] L' | ∃ a b, a ⊗ₜ[P] b = t} := by
      rw [htop]; trivial
    exact hsub2 hx
  exact hxsub
--
-- (A2-core-KERNEL) GEOMETRIC INTEGRALITY OVER AN ALGEBRAICALLY CLOSED BASE — THE genuine residual
-- analytic kernel.  `Ω` algebraically closed; `Ebar` ANY field extension of `Ω`; `F'/Ω` a finitely
-- generated FIELD extension.  Then `Ebar ⊗[Ω] F'` is an integral domain (geometric integrality is
-- AUTOMATIC over an alg-closed base: no residual separable-algebraic / inseparable constants).
-- ROUTE (gap-free, non-circular — Galois-descent/transitivity):
--   • Ω alg-closed ⟹ perfect ⟹ separating transcendence basis `s` of `F'/Ω`; `K₀ := Ω(s)` purely
--     transcendental, `F'/K₀` finite separable, `F' = K₀(α)`, `f := minpoly_{K₀} α` separable
-- monic.
--   • `B := Ebar ⊗[Ω] K₀` is a domain (localized poly ring,
-- `finite_separableClosure_kernel_aux_domain`
--     + `AlgebraicIndependent.aevalEquivField`); `K := Frac B`; `Ebar ⊗[Ω] F' ≅ B[X]/(f)`.
--   • Step A: `f` irreducible over `K` ⟹ `K[X]/(f)` a field, and `B[X]/(f) ↪ K[X]/(f)` (f monic ⟹
--     B-free ⟹ torsion-free ⟹ injects into its localization), so `B[X]/(f)` is a domain.
--   • Step B (the engine): `f` stays irreducible over `Ebar(s) ⊇ K`, via Galois transitivity:
--     `G := Gal(L/Ω(s))` (L = Galois closure of F'/Ω(s)) acts transitively on the roots of `f`
--     (f irreducible over Ω(s)); `L ∩ Ebar(s) = Ω(s)` BECAUSE Ω is alg-closed (so Ω(s) is
--     alg-closed in Ebar(s)), giving `Gal(L·Ebar(s)/Ebar(s)) ↠ G` (restrictNormalHom iso onto
--     Gal(L/L∩Ebar(s))); hence transitivity persists ⟹ no proper stable root-subset ⟹ irreducible.
--   This route does NOT use "E⊗F domain" (avoids circularity) and does NOT use any downstream
--   geomPure_*/tensorAlgClosed_* lemma, so the decomposition is acyclic.
-- (A2-core-FIELD) Abstract finite-separable variant of `tensorSep_finite_isField` (PROVED, with
-- no open goals of its own).  For a field `K₀` separably closed in an extension `M`
-- (`separableClosure K₀ M = ⊥`) and
-- any FINITE SEPARABLE `K₀`-algebra field `F'`, the base change `M ⊗[K₀] F'` is a field.  Same
-- proof
-- as the in-file `tensorSep_finite_isField`, but for an abstract finite-separable extension `F'`
-- (a genuine field type, not an `IntermediateField _ (SeparableClosure _)`); used by the assembly
-- with `K₀ = Frac(MvPolynomial s Ω)` and `F'/K₀` the separable algebraic part of the f.g. ext.
-- ACYCLIC: only invokes `tensorSep_minpoly_irreducible` (a Part-1 sibling) + Mathlib; no
-- `geomPure_*`/`tensorAlgClosed_*` / `algClosedBase_*` lemma.
open Polynomial in
/-- If the separable closure of `K₀` in `M` is trivial and `F'/K₀` is finite separable, then
`M ⊗[K₀] F'` is a field. -/
@[ega "IV 4.3.2" "special case", ega "IV 4.3.7" "special case", ega "IV 6.7.4.1" "special case"]
theorem tensorSep_finite_isField'
    (K₀ : Type*) [Field K₀] (M : Type*) [Field M] [Algebra K₀ M]
    (hsc : separableClosure K₀ M = ⊥)
    (F' : Type*) [Field F'] [Algebra K₀ F'] [Algebra.IsSeparable K₀ F'] [FiniteDimensional K₀ F'] :
    IsField (M ⊗[K₀] F') := by
  set pb : PowerBasis K₀ F' := Field.powerBasisOfFiniteOfSeparable K₀ F' with hpb
  set p : K₀[X] := minpoly K₀ pb.gen with hp
  set pK : M[X] := p.map (algebraMap K₀ M) with hpK
  have hp0 : p ≠ 0 := minpoly.ne_zero (IsIntegral.of_finite K₀ pb.gen)
  have hirr : Irreducible pK :=
    tensorSep_minpoly_irreducible K₀ M hsc pb.gen (IsIntegral.of_finite K₀ pb.gen)
      (Algebra.IsSeparable.isSeparable K₀ pb.gen)
  have : Fact (Irreducible pK) := ⟨hirr⟩
  have hpKne : pK ≠ 0 := hirr.ne_zero
  have : FiniteDimensional M (AdjoinRoot pK) := (AdjoinRoot.powerBasis hpKne).finite
  have hroot : (aeval (AdjoinRoot.root pK) (minpoly K₀ pb.gen) : AdjoinRoot pK) = 0 := by
    rw [← hp, ← Polynomial.aeval_map_algebraMap M, ← hpK, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  set g : F' →ₐ[K₀] AdjoinRoot pK := pb.lift (AdjoinRoot.root pK) hroot with hg
  set φ := Algebra.TensorProduct.lift (Algebra.ofId M (AdjoinRoot pK)) g
    (fun x y => Commute.all _ _) with hφ
  have hφgen : φ ((1 : M) ⊗ₜ[K₀] pb.gen) = AdjoinRoot.root pK := by
    rw [hφ, Algebra.TensorProduct.lift_tmul]; simp [hg, PowerBasis.lift_gen]
  have hsurj : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top, Algebra.adjoin_le_iff]
    rintro x rfl
    exact ⟨(1 : M) ⊗ₜ[K₀] pb.gen, hφgen⟩
  have hdimL : Module.finrank K₀ F' = p.natDegree := by rw [pb.finrank, hp, pb.natDegree_minpoly]
  have hdimT : Module.finrank M (M ⊗[K₀] F') = p.natDegree := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul, hdimL]
  have hdimA : Module.finrank M (AdjoinRoot pK) = p.natDegree := by
    rw [(AdjoinRoot.powerBasis hpKne).finrank, AdjoinRoot.powerBasis_dim, hpK,
      Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective K₀ M)]
  have hdimeq : Module.finrank M (M ⊗[K₀] F') = Module.finrank M (AdjoinRoot pK) := by
    rw [hdimT, hdimA]
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimeq).mpr hsurj
  let ee : (M ⊗[K₀] F') ≃ₐ[M] AdjoinRoot pK := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  exact MulEquiv.isField (Field.toIsField (AdjoinRoot pK)) ee.toMulEquiv

-- (A2-core-KERNEL) THE genuine residual analytic kernel, stated diamond-free with a
-- PLAIN field type for the transcendental base.  `Ω` algebraically closed; `Ebar/Ω` ANY field
-- extension; `K₀` a purely transcendental Ω-extension presented abstractly as the fraction field
-- of a multivariate polynomial ring (the iso `e : Frac(MvPolynomial ι Ω) ≃ₐ[Ω] K₀`).  Then `K₀` is
-- separably (indeed algebraically) closed inside `M := Frac(Ebar ⊗[Ω] K₀) ≅ Ebar(s)`, i.e.
-- `separableClosure K₀ M = ⊥`.  This is EXACTLY the geometric-irreducibility content of the route:
-- "Ω alg-closed ⟹ Ω(s) is alg-closed in Ebar(s)" (Step B / B.3.1),
-- proved there by Galois-descent/transitivity (G = Gal(L/Ω(s)) acts transitively on the roots of
-- the minpoly; L ∩ Ebar(s) = Ω(s) since Ω is algebraically closed;
-- restrictNormalHom surjectivity).
-- The `Algebra K₀ (Ebar ⊗[Ω] K₀)` is taken as an EXPLICIT instance argument (the `rightAlgebra`),
-- so the `FractionRing` localization-algebra instance over `K₀` matches the call site.
-- ACYCLIC: the Galois-descent argument does NOT use "E ⊗ F domain" (no circularity) and does NOT
-- reference any downstream `geomPure_*`/`tensorAlgClosed_*` or this target.
--
-- DECOMPOSED (this step) into ONE genuine kernel + a trivial assembly, via the
-- LINEAR-DISJOINTNESS route (Galois-free).  Its engine is: `Ebar` and `K₀` are
-- Ω-linearly disjoint inside
-- `B = Ebar ⊗[Ω] K₀` (this is just the free-tensor coordinate structure, available NON-circularly
-- from the `IsDomain B` hypothesis, which gives the embedding `B ↪ M := Frac B`).  For `α ∈ M`
-- separable over `K₀` with monic minpoly `p` of degree `d`, the powers `1,α,…,α^{d-1}` stay
-- M-linearly independent (linear disjointness + minimality of `p`: any M-relation, cleared into
-- `B` and sliced against an Ω-basis of the finite Ebar-subspace appearing, yields K₀[X]-relations
-- `rᵢ(α)=0` of degree `<d`, forcing `rᵢ=0`).  Hence `[M(α):M] = d`; but `α ∈ M` so `M(α)=M` and
-- `d = 1`, i.e. `α ∈ K₀`.  THE SINGLE genuine kernel is the per-element degree fact.

-- (A2-core-KERNEL-LD) THE genuine linear-disjointness kernel.  For `α` in the
-- fraction field `M := Frac(Ebar ⊗[Ω] K₀)` that is separable-algebraic over `K₀`, the minimal
-- polynomial has degree one.  This is the heart: "`Ω` alg-closed ⟹ `K₀ = Ω(s)` is algebraically
-- closed in `Ebar(s) ≅ M`", proved Galois-FREE by linear disjointness of `Ebar` and `K₀` over `Ω`
-- inside the domain `B = Ebar ⊗[Ω] K₀` (the `IsDomain B` hypothesis gives `B ↪ M`).
-- ACYCLIC: a NEW statement (minpoly degree over a purely-transcendental base); does NOT use
-- "E ⊗ F domain" as a black box (only the GIVEN `IsDomain B`), and references no downstream
-- `geomPure_*`/`tensorAlgClosed_*`/`algClosedBase_*` lemma or this target.
-- (A2-core-KERNEL-MAIN) THE genuine geometric-irreducibility kernel:
-- `Ω` algebraically closed ⟹ `K₀ = Ω(s)` is ALGEBRAICALLY closed in `M = Frac(Ebar ⊗[Ω] K₀)`.
-- I.e. every element of `M` integral (algebraic) over `K₀` already lies in `K₀`.  This is the
-- substantive content of Stacks 037K/04KZ for an alg-closed constant field.
-- PROOF (gap-free), by the specialization argument, which repairs the false
-- "linear-disjointness slicing" of the earlier sketch:
--   For `β` integral over `K₀` with `β = u/v`, `u,v ∈ B₀ := Ebar ⊗[Ω] P` (`P := MvPolynomial ι Ω`,
--   after clearing both the B- and K₀=Frac(P)-denominators), and a primitive relation
--   `∑_{j≤d} a_j u^j v^{d-j} = 0` in `B₀` with `a_j ∈ P`, `a_d ≠ 0`: specialize the
--   transcendentals
--   `s ↦ λ ∈ Ω` via the Ebar-algebra map `Φ_λ := id_Ebar ⊗ MvPolynomial.eval λ : B₀ → Ebar`
--   (this RESPECTS the Ebar-grading — it only touches the `P` factor, dodging the old gap).
--   For `λ` in the nonempty Zariski-open `U = {a_d·v_{i*} ≠ 0}` (nonempty: Ω alg-closed
--   ⟹ infinite,
--   a nonzero MvPolynomial has a non-root), `β(λ) := Φ_λ(u)/Φ_λ(v) ∈ Ebar` satisfies a degree-`d`
--   relation with coefficients in `Ω`, so is ALGEBRAIC over Ω ⟹ (Ω alg-closed in Ebar) `β(λ) ∈ Ω`.
--   Slicing `Φ_λ(u) = β(λ)·Φ_λ(v)` against an Ω-basis `{φ_i}` of `Ebar` (legal: Φ_λ lands by
--   coordinates `u_i(λ)`) gives `u_i(λ) = β(λ)·v_i(λ)` ∀i, hence
--   `u_i·v_{i*} = u_{i*}·v_i` vanishes
--   on `U` ⟹ identically in `P` (infinite field). So `u = r·v` with `r := u_{i*}/v_{i*} ∈ K₀`,
--   whence `β = r ∈ K₀`.  Uses ONLY `IsDomain B` (for `B₀ ↪ M`) + `IsAlgClosed Ω`. NON-CIRCULAR.
-- ACYCLIC: concludes `β ∈ range(algebraMap K₀ M)` for `β` integral/K₀ — a NEW "constant field
-- algebraically closed" statement; does NOT use any downstream `geomPure_*`/`tensorAlgClosed_*`/
-- `algClosedBase_*` lemma or a black-box `E⊗F`-domain fact for `K₀(α)`.
