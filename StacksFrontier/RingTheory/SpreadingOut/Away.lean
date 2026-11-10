module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.TotallySplit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Isomorphism after localization away from an element

Let `R` be a commutative ring, `I ⊆ R` an ideal, `φ : S → S'` a homomorphism of
commutative `R`-algebras, and `q ⊂ S` a prime ideal with `IS ⊆ q`. Assume:

1. `φ : S → S'` is surjective;
2. the induced map `S_q / IS_q → S'_q / IS'_q` is an isomorphism;
3. `S` is of finite type over `R`;
4. `S'` is of finite presentation over `R`;
5. `S'_q` is flat over `R`.

Then there exists `g ∈ S` with `g ∉ q` such that the induced `R`-algebra map
`φ_g : S_g → S'_g` is an isomorphism.

## Conventions

- The prime `q` is a prime of `S`. The localization `S'_q` is the localization of
  `S'` viewed as an `S`-algebra (through `φ`) at the prime `q`, i.e. localization at
  the multiplicative set `φ(S \ q)`. We model this with the submonoid
  `q.primeCompl.map φ` of `S'`.
- `IS` is the extension ideal `I.map (algebraMap R S)`; `IS_q` is its further
  extension `(I.map (algebraMap R S)).map (algebraMap S S_q)`, and similarly `IS'_q`.
- `S_g = Localization.Away g` and `S'_g = Localization.Away (φ g)`. The induced map
  `φ_g` is `IsLocalization.Away.map`.
- "Isomorphism" of ring maps is expressed as `Function.Bijective`.
- Flatness of `S'_q` over `R` is `Module.Flat R S'q`, where the `R`-module structure
  on `S'q` comes from the scalar tower `R → S' → S'q`.
-/

@[expose] public section

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {S : Type*} [CommRing S] [Algebra R S]
variable {S' : Type*} [CommRing S'] [Algebra R S']
variable (φ : S →ₐ[R] S')
variable (q : Ideal S) [q.IsPrime]
variable (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q]
variable (S'q : Type*) [CommRing S'q] [Algebra S' S'q]
  [IsLocalization (q.primeCompl.map (φ : S →+* S')) S'q]
variable [Algebra R S'q] [IsScalarTower R S' S'q]

/-- The induced ring map `S_q → S'_q`. Since `S'_q` is the localization of `S'`
inverting `φ(S \ q)`, the composite `S → S' → S'_q` inverts `S \ q`, so it factors
through `S_q`. -/
@[ega "0 1.5.1" "special case", ega "0 7.6.7" "special case"]
noncomputable def phiq : Sq →+* S'q :=
  IsLocalization.lift (M := q.primeCompl) (g := (algebraMap S' S'q).comp (φ : S →+* S'))
    (fun s => IsLocalization.map_units S'q
      (⟨(φ : S →+* S') s, Submonoid.mem_map_of_mem _ s.property⟩ :
        q.primeCompl.map (φ : S →+* S')))

omit [Algebra R S'q] [IsScalarTower R S' S'q] in
/-- The map `φ_q : S_q → S'_q` agrees with `φ` on the image of `S`. -/
@[ega "0 1.5.1" "partial"]
theorem phiq_alg (x : S) :
    phiq φ q Sq S'q (algebraMap S Sq x) = algebraMap S' S'q (φ x) := by
  unfold phiq
  rw [IsLocalization.lift_eq]
  rfl

/-- The extension ideal `IS_q ⊆ S_q`. -/
noncomputable def ISq : Ideal Sq := (I.map (algebraMap R S)).map (algebraMap S Sq)

/-- The extension ideal `IS'_q ⊆ S'_q`. -/
noncomputable def IS'q : Ideal S'q := (I.map (algebraMap R S')).map (algebraMap S' S'q)

omit [Algebra R S'q] [IsScalarTower R S' S'q] in
/-- The map `φ_q` carries the extension ideal `IS_q ⊆ S_q` into `IS'_q ⊆ S'_q`. -/
theorem phiq_ISq_le :
    ISq I (S := S) Sq ≤ Ideal.comap (phiq φ q Sq S'q) (IS'q I (S' := S') S'q) := by
  unfold ISq IS'q
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  simp only [Ideal.mem_comap, phiq_alg]
  apply Ideal.mem_map_of_mem
  rw [← φ.comp_algebraMap, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hx

/-- The induced map on quotients `S_q / IS_q → S'_q / IS'_q`. -/
noncomputable def phiqBar :
    (Sq ⧸ ISq I (S := S) Sq) →+* (S'q ⧸ IS'q I (S' := S') S'q) :=
  Ideal.quotientMap (IS'q I (S' := S') S'q) (phiq φ q Sq S'q) (phiq_ISq_le I φ q Sq S'q)

/-- The induced `R`-algebra map `φ_g : S_g → S'_g` on localizations at an element
`g ∈ S` (with `S'_g = S'` localized at `φ g`). -/
@[ega "0 1.5.1" "special case"]
noncomputable def phig (g : S) :
    Localization.Away g →+* Localization.Away ((φ : S →+* S') g) :=
  IsLocalization.Away.map (Localization.Away g) (Localization.Away ((φ : S →+* S') g))
    (φ : S →+* S') g

omit [Algebra R S'q] [IsScalarTower R S' S'q] in
/-- `phig φ g` is surjective when `φ` is, being the localization of a surjection. -/
@[ega "0 1.5.1" "special case"]
theorem phig_surjective (g : S) (hsurj : Function.Surjective (φ : S → S')) :
    Function.Surjective (phig φ g) := by
  unfold phig
  intro y
  obtain ⟨⟨y0, ⟨_, n, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers ((φ:S→+*S') g)) y
  obtain ⟨x0, rfl⟩ := hsurj y0
  refine ⟨IsLocalization.mk' (Localization.Away g) x0
    (⟨g ^ n, n, rfl⟩ : Submonoid.powers g), ?_⟩
  rw [IsLocalization.Away.map, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simpa [map_pow] using hy.symm

omit [Algebra R S'q] [IsScalarTower R S' S'q] in
/-- If `g` annihilates the kernel of `φ`, then `phig φ g` is injective. -/
theorem phig_injective (g : S)
    (hann : ∀ x : S, (φ : S →+* S') x = 0 → g * x = 0) :
    Function.Injective (phig φ g) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  -- write z = x / g^n
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hzx⟩ := IsLocalization.surj (Submonoid.powers g) z
  unfold phig at hz
  obtain rfl : z = IsLocalization.mk' (Localization.Away g) x
      (⟨g ^ n, n, rfl⟩ : Submonoid.powers g) :=
    IsLocalization.eq_mk'_iff_mul_eq.2 hzx
  rw [IsLocalization.Away.map, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := hz
  simp only at hm
  have hker : (φ : S →+* S') (g ^ m * x) = 0 := by rwa [map_mul, map_pow]
  rw [IsLocalization.mk'_eq_zero_iff]
  refine ⟨(⟨g ^ (m + 1), m + 1, rfl⟩ : Submonoid.powers g), ?_⟩
  simp only
  linear_combination hann _ hker

/-- Abstract helper_087p: if `g : M →ₗ[R] N` has injective base change `– ⊗ R/I`, then any
`m : M` with `g m ∈ I·N` already lies in `I·M`. (Translation of flat-injectivity to a
concrete membership statement via `quotTensorEquivQuotSMul`.) -/
theorem lTensor_smul_mem {R : Type*} [CommRing R] (I : Ideal R) {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (hinj : Function.Injective (LinearMap.lTensor (R ⧸ I) g))
    (m : M) (hm : g m ∈ I • (⊤ : Submodule R N)) :
    m ∈ I • (⊤ : Submodule R M) := by
  have h1 : (1 : R ⧸ I) ⊗ₜ[R] (g m) = 0 := by
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk (M := N) I (g m),
      show (Submodule.Quotient.mk (g m) : N ⧸ (I • (⊤ : Submodule R N))) = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr hm, map_zero]
  have h3 : (1 : R ⧸ I) ⊗ₜ[R] m = 0 := hinj (by rw [LinearMap.lTensor_tmul, h1, map_zero])
  rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk (M := M) I m] at h3
  exact (Submodule.Quotient.mk_eq_zero _).mp ((LinearEquiv.map_eq_zero_iff _).mp h3)

/-- Abstract helper_087p: convert an `R`-level membership `m ∈ I·(⊤ : Submodule R Jq)` into the
`B`-level ideal membership `↑m ∈ K·Jq`, provided `K` contains `algebraMap R B '' I`. -/
theorem smul_top_to_ideal_smul {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) (K : Ideal B) (Jq : Ideal B)
    (hIK : ∀ r ∈ I, algebraMap R B r ∈ K)
    (m : (Jq.restrictScalars R)) (hm : m ∈ I • (⊤ : Submodule R (Jq.restrictScalars R))) :
    (m : B) ∈ K • Jq := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro r hr n _
    have hc : ((r • n : (Jq.restrictScalars R)) : B) = algebraMap R B r * (n : B) := by
      rw [Submodule.coe_smul, Algebra.smul_def]
    rw [hc]
    simpa [smul_eq_mul] using Submodule.smul_mem_smul (M := B) (hIK r hr) n.property
  · intro a b ha hb
    rw [Submodule.coe_add]
    exact Submodule.add_mem _ ha hb

omit [Algebra R S'q] [IsScalarTower R S' S'q] in
/-- `phiq` is surjective when `φ` is (localization of a surjection). -/
@[ega "0 1.3.2" "special case", ega "0 1.5.1" "special case"]
theorem phiq_surj (hsurj : Function.Surjective (φ : S → S')) :
    Function.Surjective (phiq φ q Sq S'q) := by
  intro y
  obtain ⟨⟨y0, m, hm⟩, hy⟩ := IsLocalization.surj (q.primeCompl.map (φ:S→+*S')) y
  obtain ⟨x0, rfl⟩ := hsurj y0
  obtain ⟨s, hs, rfl⟩ := hm
  refine ⟨IsLocalization.mk' Sq x0 ⟨s, hs⟩, ?_⟩
  simp only at hy
  have hunit : IsUnit (algebraMap S' S'q (φ s)) :=
    IsLocalization.map_units S'q
      (⟨(φ:S→+*S') s, Submonoid.mem_map_of_mem _ hs⟩ : q.primeCompl.map (φ:S→+*S'))
  apply hunit.mul_right_cancel
  have hL : phiq φ q Sq S'q (IsLocalization.mk' Sq x0 ⟨s, hs⟩) * algebraMap S' S'q (φ s)
      = algebraMap S' S'q (φ x0) := by
    rw [← phiq_alg φ q Sq S'q s, ← map_mul, mul_comm, IsLocalization.mk'_spec' Sq x0 ⟨s, hs⟩,
      phiq_alg]
  exact hL.trans hy.symm

omit [Algebra R S'q] [IsScalarTower R S' S'q] in
/-- The kernel of `phiq` is the extension of `ker φ` to `S_q` (exactness of localization
over `S`). -/
theorem phiq_ker :
    RingHom.ker (phiq φ q Sq S'q) = (RingHom.ker (φ:S→+*S')).map (algebraMap S Sq) := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨⟨x, s, hs⟩, hzx⟩ := IsLocalization.surj q.primeCompl z
    simp only at hzx
    have hax : algebraMap S' S'q (φ x) = 0 := by
      rw [← phiq_alg φ q Sq S'q x, ← hzx, map_mul, hz, zero_mul]
    rw [IsLocalization.map_eq_zero_iff (q.primeCompl.map (φ:S→+*S')) S'q] at hax
    obtain ⟨⟨m, s', hs', rfl⟩, hm⟩ := hax
    simp only at hm
    have hkerx : (s' * x) ∈ RingHom.ker (φ:S→+*S') := by
      rwa [RingHom.mem_ker, map_mul]
    have hmem : algebraMap S Sq (s' * x) ∈ (RingHom.ker (φ:S→+*S')).map (algebraMap S Sq) :=
      Ideal.mem_map_of_mem _ hkerx
    have hexpand : algebraMap S Sq (s' * x) = (algebraMap S Sq s' * algebraMap S Sq s) * z := by
      rw [map_mul, ← hzx]
      ring
    rwa [hexpand, Ideal.unit_mul_mem_iff_mem _
      ((IsLocalization.map_units Sq ⟨s', hs'⟩).mul (IsLocalization.map_units Sq ⟨s, hs⟩))] at hmem
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, phiq_alg, show φ x = (0:S') from hx, map_zero]

/-- **Flatness inclusion (the analytic heart of Stacks 087P).**

Let `J = ker(φ : S → S')`.  We claim the localized kernel `J·S_q` satisfies the
Nakayama-style inclusion `J·S_q ≤ (I·S_q) • (J·S_q)`.

**Informal argument.**
Write `Jq := J.map (algebraMap S Sq)` for the extension of `J` to `S_q`, and
`ISq` for `I·S_q`. We must show `Jq ≤ ISq • Jq`, i.e. that the `S_q`-module
`Jq / (ISq • Jq) = Jq ⊗_{S_q} (S_q / ISq)` vanishes.

Consider the short exact sequence of `S`-modules
`0 → J → S → S' → 0` (exact because `φ` is surjective with kernel `J`).
Localizing at `q` over `S` (an exact functor) gives the exact sequence of
`S_q`-modules
`0 → Jq → S_q → S'_q → 0`,            (★)
where `S'_q ≅ S'⊗_S S_q` is the localization of `S'` described in the statement
and `Jq` is the image of `J ⊗_S S_q → S_q` (which is injective since
localization is flat over `S`, so `Jq ≅ J ⊗_S S_q`).

Now tensor (★) with `R/I` over `R`. Because `S'_q` is **flat over `R`**
(hypothesis `hflat`), the functor `– ⊗_R (R/I)` is exact on the right end; more
precisely Stacks 00HL / `Module.Flat.lTensor_exact` applied to (★) and the
flat module `S'_q` shows that
`Tor_1^R(S'_q, R/I) = 0`, and the sequence stays exact after `⊗_R R/I`:
`0 → Jq/I·Jq → S_q/I·S_q → S'_q/I·S'_q → 0`.   (★★)
(The first map is `Jq ⊗_R R/I → S_q ⊗_R R/I`, identified with the natural
`Jq/(I·Jq) → S_q/(I·S_q)`; it is injective precisely because `Tor_1^R(S'_q,R/I)=0`,
the flatness input.)

By hypothesis (2) (`hiso`), the right-hand map of (★★),
`phiqBar : S_q/I·S_q → S'_q/I·S'_q`, is an **isomorphism**; equivalently it is
injective.  In the exact sequence (★★) injectivity of the right map forces the
image of the left map to be `0`, i.e. `Jq/(I·Jq) → S_q/(I·S_q)` is the zero map.
But that left map is injective (flatness), so its source `Jq/(I·Jq)` is `0`.
Hence `Jq = I·Jq = ISq • Jq`, in particular `Jq ≤ ISq • Jq`. ∎

This step is the only place flatness (hypothesis 5) and the iso-mod-`I`
hypothesis (2) are used; everything else is finiteness + Nakayama.

Flatness is load-bearing: for the degenerate non-flat `R = k[e]/(e²)` the conclusion fails
exactly when `hflat` does.  The hypothesis `hIq` is not needed here, only downstream.

The argument goes as follows.
  1. Build the SES `0 → J → S → S' → 0` of `S`-modules from `hsurj` and
     `J = ker φ` (`RingHom.ker`, `LinearMap.exact` / `Function.Exact`).
  2. Base-change/localize to get the `S_q`-exact `0 → Jq → S_q → S'_q → 0`
     (localization is flat over `S`); identify `Jq = J.map (algebraMap S Sq)`.
  3. Apply `Module.Flat.lTensor_exact` (Stacks 00HL) with the flat `R`-module
     `S'q` (`hflat`) to keep exactness after `– ⊗_R (R/I)`, yielding injectivity
     of `Jq/I·Jq → S_q/I·S_q` (equivalently `Tor₁^R(S'q, R/I)=0`).
  4. From `hiso` (Bijective ⇒ Injective on `phiqBar`), the right map of the
     `⊗_R R/I` sequence is injective, so the image of `Jq/I·Jq → S_q/I·S_q` is `0`;
     with step 3's injectivity this forces `Jq/I·Jq = 0`, i.e. `Jq ≤ I·Jq`.
  5. Convert `I·Jq`, the `R`-module extension, to `ISq • Jq` using
     `ISq = I.map (algebraMap R Sq)`. -/
@[sga "3 VIIA 7.4.3" "K ⊗ k = 0"]
theorem flatness_inclusion_087P
    (hsurj : Function.Surjective (φ : S → S'))
    (hiso : Function.Bijective (phiqBar I φ q Sq S'q))
    (hflat : Module.Flat R S'q) :
    (RingHom.ker (φ : S →+* S')).map (algebraMap S Sq) ≤
      (ISq I (S := S) Sq) •
        ((RingHom.ker (φ : S →+* S')).map (algebraMap S Sq)) := by
  let : Algebra R Sq := ((algebraMap S Sq).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S Sq := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set Jq : Ideal Sq := (RingHom.ker (φ:S→+*S')).map (algebraMap S Sq)
  -- Part A: Jq ≤ ISq (uses `hiso` injectivity; no flatness needed here).
  have hJqISq : Jq ≤ ISq I (S := S) Sq := by
    intro x hx
    have hbar : phiqBar I φ q Sq S'q (Ideal.Quotient.mk (ISq I (S := S) Sq) x) = 0 := by
      unfold phiqBar
      rw [Ideal.quotientMap_mk, RingHom.mem_ker.mp ((phiq_ker φ q Sq S'q).ge hx), map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hiso.injective (by rw [hbar, map_zero]))
  -- `ISq = I.map (algebraMap R Sq)` and `I • ⊤ = restrictScalars (ISq)`.
  have hISqmap : ISq I (S := S) Sq = I.map (algebraMap R Sq) := by
    unfold ISq
    rw [Ideal.map_map]
    congr 1
  have hsmultop : I • (⊤ : Submodule R Sq) = (ISq I (S := S) Sq).restrictScalars R := by
    rw [Ideal.smul_top_eq_map, hISqmap]
  have hIK : ∀ r ∈ I, algebraMap R Sq r ∈ ISq I (S := S) Sq := fun r hr => by
    rw [hISqmap]
    exact Ideal.mem_map_of_mem _ hr
  -- `phiq` is `R`-linear; package it as `fR`, with `gR` the inclusion of `Jq`.
  have hlin : ∀ (r : R) (z : Sq), phiq φ q Sq S'q (r • z) = r • phiq φ q Sq S'q z := by
    intro r z
    rw [Algebra.smul_def, Algebra.smul_def, map_mul,
        show (algebraMap R Sq) r = algebraMap S Sq (algebraMap R S r) from rfl, phiq_alg]
    congr 1
    rw [show φ (algebraMap R S r) = algebraMap R S' r from by rw [AlgHom.commutes],
        ← IsScalarTower.algebraMap_apply R S' S'q]
  let fR : Sq →ₗ[R] S'q :=
    { toFun := phiq φ q Sq S'q, map_add' := map_add _, map_smul' := hlin }
  let gR : (Jq.restrictScalars R) →ₗ[R] Sq := (Jq.restrictScalars R).subtype
  -- Exactness of `0 → Jq → Sq → S'q` (from `phiq_ker`).
  have hexact : Function.Exact gR fR := fun z =>
    ⟨fun hz => ⟨⟨z, (phiq_ker φ q Sq S'q).le hz⟩, rfl⟩, by
      rintro ⟨y, rfl⟩
      exact (phiq_ker φ q Sq S'q).ge y.property⟩
  -- Flatness of `S'q` ⟹ base change `– ⊗ R/I` keeps `gR` injective (Stacks 00HL).
  have htensor : Function.Injective (LinearMap.lTensor (R ⧸ I) gR) :=
    LinearMap.lTensor_injective_of_exact_of_flat fR (phiq_surj φ q Sq S'q hsurj) gR
      Subtype.coe_injective hexact (R ⧸ I)
  -- Conclude: every `x ∈ Jq` lies in `I • Jq ⊆ ISq • Jq`.
  intro x hx
  refine smul_top_to_ideal_smul I (ISq I (S := S) Sq) Jq hIK ⟨x, hx⟩
    (lTensor_smul_mem I gR htensor ⟨x, hx⟩ ?_)
  change x ∈ I • (⊤ : Submodule R Sq)
  rw [hsmultop]
  exact hJqISq hx

/-- **Stacks Tag 087P (Lemma 10.126.10).**
Under the stated hypotheses there is `g ∈ S`, `g ∉ q`, with `φ_g : S_g → S'_g` an
isomorphism (i.e. bijective). -/
@[stacks 087P]
theorem isomorphism_of_flat_surjective_087P
    (hIq : I.map (algebraMap R S) ≤ q)
    (hsurj : Function.Surjective (φ : S → S'))
    (hiso : Function.Bijective (phiqBar I φ q Sq S'q))
    (hft : (algebraMap R S).FiniteType)
    (hfp : (algebraMap R S').FinitePresentation)
    (hflat : Module.Flat R S'q) :
    ∃ g : S, g ∉ q ∧ Function.Bijective (phig φ g) := by
  -- It suffices to find g ∉ q annihilating ker φ; then `phig` is injective
  -- (phig_injective) and surjective (phig_surjective), hence bijective.
  suffices h : ∃ g : S, g ∉ q ∧ ∀ x : S, (φ : S →+* S') x = 0 → g * x = 0 by
    obtain ⟨g, hgq, hann⟩ := h
    exact ⟨g, hgq, phig_injective φ g hann, phig_surjective φ g hsurj⟩
  -- J = ker φ
  set J : Ideal S := RingHom.ker (φ : S →+* S') with hJ
  -- Step 2: J is finitely generated.
  -- φ is a surjective ring hom of finite presentation (S' f.p. over R, S f.t. over R,
  -- via `RingHom.FinitePresentation.of_comp_finiteType`), so its kernel is f.g.
  -- (`Algebra.FinitePresentation.ker_fG_of_surjective`).
  have hJfg : J.FG := by
    have hφfp : (φ : S →+* S').FinitePresentation :=
      RingHom.FinitePresentation.of_comp_finiteType (algebraMap R S)
        (by rwa [φ.comp_algebraMap]) hft
    let : Algebra S S' := (φ : S →+* S').toAlgebra
    have : Algebra.FinitePresentation S S' := hφfp
    have hker := Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId S S') hsurj
    have hkereq : RingHom.ker (Algebra.ofId S S').toRingHom = J := by
      rw [hJ]
      congr 1
    rwa [hkereq] at hker
  -- Step 3: JSq ≤ ISq • JSq  (flatness — see `flatness_inclusion_087P`).
  have hflateq : (J.map (algebraMap S Sq)) ≤
      (ISq I (S := S) Sq) • (J.map (algebraMap S Sq)) :=
    flatness_inclusion_087P I φ q Sq S'q hsurj hiso hflat
  -- Step 4: Nakayama gives JSq = ⊥.
  -- ISq lies in the Jacobson radical of Sq (= the maximal ideal of the local ring Sq,
  -- since ISq ≤ q·Sq = maximal ideal), and JSq is f.g., so JSq = ISq • JSq forces JSq = ⊥.
  have hISqJac : (ISq I (S := S) Sq) ≤ (⊥ : Ideal Sq).jacobson := by
    have : IsLocalRing Sq := IsLocalization.AtPrime.isLocalRing Sq q
    rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal Sq) bot_ne_top,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal (Rₚ := Sq) (p := q)]
    unfold ISq
    exact Ideal.map_mono hIq
  have hJSqbot : J.map (algebraMap S Sq) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (ISq I (S := S) Sq) (J.map (algebraMap S Sq)) (hJfg.map _) hflateq hISqJac
  -- Step 5: extract g ∉ q annihilating J.
  -- Each x ∈ J maps to 0 in Sq (since JSq = ⊥), hence is killed by some s ∉ q.
  -- Take g = product of killers over a finite generating set of J; g ∉ q (prime
  -- complement is multiplicative) and g annihilates all of J by span induction.
  have hkill : ∀ x : S, x ∈ J → ∃ s : q.primeCompl, (s : S) * x = 0 := by
    intro x hx
    have h0 : algebraMap S Sq x ∈ J.map (algebraMap S Sq) := Ideal.mem_map_of_mem _ hx
    rwa [hJSqbot, Ideal.mem_bot, IsLocalization.map_eq_zero_iff q.primeCompl (S := Sq)] at h0
  obtain ⟨t, ht⟩ := hJfg
  have htJ : ∀ j ∈ t, j ∈ J := by
    intro j hj
    rw [← ht]
    exact Ideal.subset_span hj
  classical
  choose kf hkf using fun (j : S) (hj : j ∈ t) => hkill j (htJ j hj)
  set kf' : S → S := fun j => if h : j ∈ t then (kf j h : S) else 1 with hkf'
  refine ⟨∏ j ∈ t, kf' j, ?_, ?_⟩
  · change (∏ j ∈ t, kf' j) ∈ q.primeCompl
    apply Submonoid.prod_mem
    intro j hj
    rw [hkf']
    simp only [hj, dite_eq_left]
    exact (kf j hj).property
  · intro x hxk
    have hxJ : x ∈ J := hxk
    rw [← ht] at hxJ
    refine Submodule.span_induction (p := fun x _ => (∏ j ∈ t, kf' j) * x = 0) ?_ ?_ ?_ ?_ hxJ
    · intro y hy
      have hyt : y ∈ t := hy
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem kf' hyt
      have hky : kf' y = (kf y hyt : S) := by
        rw [hkf']
        simp [hyt]
      rw [hc, mul_comm (kf' y) c, mul_assoc, hky, hkf y hyt, mul_zero]
    · simp
    · intro a b _ _ ha hb
      rw [mul_add, ha, hb, add_zero]
    · intro a b _ hb
      rw [mul_smul_comm, hb, smul_zero]
