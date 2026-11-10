module

public import Mathlib.RingTheory.Smooth.Quotient
public import StacksFrontier.RingTheory.Flat.AdicFiltration
public import StacksFrontier.RingTheory.Flat.LocalCriterionVariant
public import StacksFrontier.RingTheory.Smooth.SmoothAt

/-!
# A common smooth neighbourhood for all the adic stages of a ring map

Let `B → C` be a homomorphism of Noetherian rings, `b ⊆ B` an ideal and, for `n : ℕ`, let
`Bₙ = B/bⁿ⁺¹` and `Cₙ = C/bⁿ⁺¹C`. Let `q ⊆ C` be a prime containing `bC` such that every
`Bₙ → Cₙ` is of finite type and smooth at the prime `qₙ = q/bⁿ⁺¹C`. Then there is a single
`f ∉ q` such that, for every `n`, `Bₙ → Cₙ` is smooth at every prime of `Cₙ` not containing the
image of `f`. This is the key step of the proof of Stacks 0GI9.

## Main results

* `Algebra.flat_localization_atPrime_of_forall_smoothAt`: under the hypotheses above `C_q` is
  flat over `B`.
* `Algebra.exists_notMem_forall_smoothAt_quotient_pow`: the common smooth neighbourhood.

## Implementation notes

The source argues with the Rees algebras of `b` and of `bC`: the comparison map
`⊕ bⁿ/bⁿ⁺¹ ⊗_{B₁} C₁ → ⊕ bⁿC/bⁿ⁺¹C` of finite graded algebras is an isomorphism at `q`, hence on a
principal open, and the local criterion of flatness (Stacks 0AS8) then gives flatness of every
`Bₙ → Cₙ` there. Here the same finiteness enters through a single finite `C`-module instead, the
kernel `K` of `C ⊗_B b → C ⊗_B B`, which is the `Tor₁^B(C, B/b)` of the local criterion. Flatness
of every stage at `q` gives flatness of `C_q` over `B` by Stacks 0523, so `K_q = 0`, and since `K`
is finite some `s ∉ q` kills it. At every prime `Q ⊇ bC` with `s ∉ Q` the local criterion of
flatness in the form of Stacks 00ML then gives flatness of `C_Q` over `B`, as `C_Q/bC_Q` is flat
over `B/b` near `q`. Smoothness of the stages at `Q` follows from smoothness of the first stage by
Stacks 031L, one square-zero step at a time.

## References

* [Stacks Project, Tag 0GI9](https://stacks.math.columbia.edu/tag/0GI9)
* [Stacks Project, Tag 0523](https://stacks.math.columbia.edu/tag/0523)
* [Stacks Project, Tag 00ML](https://stacks.math.columbia.edu/tag/00ML)
* [Stacks Project, Tag 031L](https://stacks.math.columbia.edu/tag/031L)
* [Stacks Project, Tag 0AS8](https://stacks.math.columbia.edu/tag/0AS8)
-/

@[expose] public section

open TensorProduct

namespace Algebra

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra B C]

/-! ### Localizations of quotients -/

/-- The image of a prime `Q ⊇ J` in `C ⧸ J` is prime. -/
theorem isPrime_map_quotient {J Q : Ideal C} [Q.IsPrime] (hJQ : J ≤ Q) :
    (Q.map (Ideal.Quotient.mk J)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

/-- The image of the complement of a prime `Q ⊇ J` in `C ⧸ J` is the complement of `Q/J`. -/
theorem algebraMapSubmonoid_primeCompl_quotient {J Q : Ideal C} [Q.IsPrime] (hJQ : J ≤ Q) :
    haveI := isPrime_map_quotient hJQ
    Algebra.algebraMapSubmonoid (C ⧸ J) Q.primeCompl =
      (Q.map (Ideal.Quotient.mk J)).primeCompl := by
  have := isPrime_map_quotient hJQ
  ext x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · rintro ⟨c', hc', hcc'⟩
    change Ideal.Quotient.mk J c' = Ideal.Quotient.mk J c at hcc'
    exact fun h => hc' ((Ideal.mem_quotient_iff_mem hJQ).mp (hcc' ▸ h))
  · exact fun hc => ⟨c, fun h => hc ((Ideal.mem_quotient_iff_mem hJQ).mpr h), rfl⟩

/-- For a prime `Q ⊇ J` of `C`, the quotient `C_Q ⧸ J C_Q` is the localization of `C ⧸ J` at the
image of `Q`. -/
theorem isLocalization_atPrime_quotient {J Q : Ideal C} [Q.IsPrime] (hJQ : J ≤ Q) :
    haveI := isPrime_map_quotient hJQ
    IsLocalization.AtPrime
      (Localization.AtPrime Q ⧸ J.map (algebraMap C (Localization.AtPrime Q)))
      (Q.map (Ideal.Quotient.mk J)) := by
  have := isPrime_map_quotient hJQ
  change IsLocalization (Q.map (Ideal.Quotient.mk J)).primeCompl _
  rw [← algebraMapSubmonoid_primeCompl_quotient hJQ]
  infer_instance

/-- For a prime `Q ⊇ IC` of `C`, the module `C_Q ⧸ I C_Q` over `B ⧸ I` is the local ring of
`C ⧸ IC` at the image of `Q`. -/
noncomputable def quotientSMulTopAtPrimeEquiv (I : Ideal B) {Q : Ideal C} [Q.IsPrime]
    (hIQ : I.map (algebraMap B C) ≤ Q) :
    haveI := isPrime_map_quotient hIQ
    (Localization.AtPrime Q ⧸ (I • ⊤ : Submodule B (Localization.AtPrime Q))) ≃ₗ[B ⧸ I]
      Localization.AtPrime (Q.map (Ideal.Quotient.mk (I.map (algebraMap B C)))) := by
  haveI := isPrime_map_quotient hIQ
  haveI := isLocalization_atPrime_quotient hIQ
  have hJ : (I • ⊤ : Submodule B (Localization.AtPrime Q)) =
      ((I.map (algebraMap B C)).map (algebraMap C (Localization.AtPrime Q))).restrictScalars B := by
    rw [Ideal.smul_top_eq_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  haveI : IsScalarTower B (C ⧸ I.map (algebraMap B C))
      (Localization.AtPrime Q ⧸
        (I.map (algebraMap B C)).map (algebraMap C (Localization.AtPrime Q))) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [← Ideal.Quotient.mk_algebraMap,
        IsScalarTower.algebraMap_apply B C (Localization.AtPrime Q),
        IsScalarTower.algebraMap_apply B C (C ⧸ I.map (algebraMap B C)),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_quotient_map_quotient]
  let e3 : (Localization.AtPrime Q ⧸
        (I.map (algebraMap B C)).map (algebraMap C (Localization.AtPrime Q)))
      ≃ₐ[C ⧸ I.map (algebraMap B C)]
      Localization.AtPrime (Q.map (Ideal.Quotient.mk (I.map (algebraMap B C)))) :=
    IsLocalization.algEquiv (Q.map (Ideal.Quotient.mk (I.map (algebraMap B C)))).primeCompl _ _
  let e : (Localization.AtPrime Q ⧸ (I • ⊤ : Submodule B (Localization.AtPrime Q))) ≃ₗ[B]
      Localization.AtPrime (Q.map (Ideal.Quotient.mk (I.map (algebraMap B C)))) :=
    (Submodule.quotEquivOfEq _ _ hJ) ≪≫ₗ (Submodule.Quotient.restrictScalarsEquiv B _) ≪≫ₗ
      (e3.toLinearEquiv.restrictScalars B)
  exact e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- A ring map smooth at a prime `q` of the target is flat at `q`. -/
theorem flat_localization_atPrime_of_smoothAt {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] {q : Ideal S} [q.IsPrime] (h : Algebra.SmoothAt R S q) :
    Module.Flat R (Localization.AtPrime q) := by
  obtain ⟨g, hgq, hgs⟩ := h
  let : Algebra (Localization.Away g) (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers g) q.primeCompl
      (Submonoid.powers_le.mpr hgq)
  have : IsScalarTower S (Localization.Away g) (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsScalarTower R (Localization.Away g) (Localization.AtPrime q) := .to₁₃₄ _ S _ _
  have : IsLocalization (q.primeCompl.map (algebraMap S (Localization.Away g)))
      (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away g)
      (Localization.AtPrime q) (Submonoid.powers g) q.primeCompl (Submonoid.powers_le.mpr hgq)
  have : Module.Flat (Localization.Away g) (Localization.AtPrime q) :=
    IsLocalization.flat _ (q.primeCompl.map (algebraMap S (Localization.Away g)))
  have : Module.Flat R (Localization.Away g) := Algebra.Smooth.flat_of_isNoetherianRing _ _
  exact Module.Flat.trans R (Localization.Away g) (Localization.AtPrime q)

/-- The ideal `bⁿ⁺¹C` lies in every prime containing `bC`. -/
theorem map_pow_succ_le {b : Ideal B} {Q : Ideal C} (hQ : b.map (algebraMap B C) ≤ Q) (n : ℕ) :
    (b ^ (n + 1)).map (algebraMap B C) ≤ Q := by
  rw [Ideal.map_pow]
  exact (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans hQ

variable [IsNoetherianRing B] [IsNoetherianRing C]

/-- **Flatness at `q` from flatness of the stages.** If `Bₙ → Cₙ` is smooth at `qₙ` for every
`n`, then `C_q` is flat over `B`: each `C_q/bⁿ⁺¹C_q` is the local ring of `Cₙ` at `qₙ`, flat over
`Bₙ`, so Stacks 0523 applies. -/
theorem flat_localization_atPrime_of_forall_smoothAt (b : Ideal B) (q : Ideal C) [q.IsPrime]
    (hq : b.map (algebraMap B C) ≤ q)
    (hsm : ∀ n : ℕ, haveI := isPrime_map_quotient (map_pow_succ_le hq n)
      Algebra.SmoothAt (B ⧸ b ^ (n + 1)) (C ⧸ (b ^ (n + 1)).map (algebraMap B C))
        (q.map (Ideal.Quotient.mk ((b ^ (n + 1)).map (algebraMap B C))))) :
    Module.Flat B (Localization.AtPrime q) := by
  have hflat : ∀ n : ℕ, Module.Flat (B ⧸ b ^ (n + 1))
      (Localization.AtPrime q ⧸ (b ^ (n + 1) • ⊤ : Submodule B (Localization.AtPrime q))) := by
    intro n
    have := isPrime_map_quotient (map_pow_succ_le hq n)
    have := flat_localization_atPrime_of_smoothAt (hsm n)
    exact Module.Flat.of_linearEquiv (quotientSMulTopAtPrimeEquiv (b ^ (n + 1))
      (map_pow_succ_le hq n))
  have hmax : b.map (algebraMap B (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply B C (Localization.AtPrime q),
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q]
    exact hq (Ideal.mem_map_of_mem _ hx)
  have : IsLocalization (IsLocalRing.maximalIdeal (Localization.AtPrime q)).primeCompl
      (Localization.AtPrime q) :=
    IsLocalization.of_le_isUnit fun x hx => by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using! hx
  have : IsLocalizedModule.AtPrime (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (LinearMap.id : Localization.AtPrime q →ₗ[Localization.AtPrime q] _) :=
    isLocalizedModule_id _ _ (Localization.AtPrime q)
  exact Module.Flat.of_flat_quotient_pow b (Localization.AtPrime q) hflat
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)) hmax (Localization.AtPrime q)
    LinearMap.id

/-- **The `Tor₁` of the local criterion is killed near `q`.** If `C_q` is flat over `B`, some
`s ∉ q` kills the kernel of `C ⊗_B b → C ⊗_B B`: that kernel is a finite `C`-module whose
localization at `q` is the kernel of the injective map `C_q ⊗_B b → C_q ⊗_B B`. -/
theorem exists_notMem_smul_ker_lTensor_eq_zero (b : Ideal B) (q : Ideal C) [q.IsPrime]
    (hflat : Module.Flat B (Localization.AtPrime q)) :
    ∃ s ∉ q, ∀ x ∈ LinearMap.ker (AlgebraTensorModule.lTensor C C b.subtype), s • x = 0 := by
  let K := LinearMap.ker (AlgebraTensorModule.lTensor C C b.subtype)
  let Cq := Localization.AtPrime q
  let g : C →ₗ[C] Cq := Algebra.linearMap C Cq
  have : IsNoetherian C (C ⊗[B] b) := isNoetherian_of_isNoetherianRing_of_finite C _
  have : Module.Finite C K := Module.IsNoetherian.finite C K
  have hinj : Function.Injective (AlgebraTensorModule.lTensor C Cq b.subtype) := by
    rw [AlgebraTensorModule.coe_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hloc : ∀ x : K, ∃ r ∉ q, r • x = 0 := by
    intro x
    have h0 : AlgebraTensorModule.rTensor B b g x.1 = 0 := by
      apply hinj
      rw [map_zero, ← IsLocalizedModule.map_lTensor (S := q.primeCompl) (g := g) (f := b.subtype),
        IsLocalizedModule.map_apply, x.2, map_zero]
    obtain ⟨r, hr⟩ := (IsLocalizedModule.eq_zero_iff q.primeCompl
      (AlgebraTensorModule.rTensor B b g)).mp h0
    exact ⟨r.1, r.2, Subtype.ext hr⟩
  have hsupp : (⟨q, inferInstance⟩ : PrimeSpectrum C) ∉ Module.support C K :=
    Module.notMem_support_iff'.mpr hloc
  rw [Module.mem_support_iff_of_finite, IsConcreteLE.not_le_iff_exists] at hsupp
  obtain ⟨s, hs, hsq⟩ := hsupp
  exact ⟨s, hsq, fun x hx => congrArg Subtype.val (Module.mem_annihilator.mp hs ⟨x, hx⟩)⟩

/-- **The local criterion of flatness at a prime `Q ⊇ bC`.** Suppose some `s ∉ Q` kills the
kernel of `C ⊗_B b → C ⊗_B B`, and the local ring of `C/bC` at `Q` is flat over `B/b`. Then
`C_Q` is flat over `B`. This is Stacks 00ML for the local homomorphism `B_p → C_Q`,
`p = Q ∩ B`, and the ideal `bB_p`: the vanishing of `Tor₁` is the injectivity of
`C_Q ⊗_B b → C_Q ⊗_B B`, the localization of the given kernel at `Q`. -/
theorem flat_localization_atPrime_of_smul_ker_eq_zero (b : Ideal B) {s : C}
    (hs : ∀ x ∈ LinearMap.ker (AlgebraTensorModule.lTensor C C b.subtype), s • x = 0)
    (Q : Ideal C) [Q.IsPrime] (hbQ : b.map (algebraMap B C) ≤ Q) (hsQ : s ∉ Q)
    (hflat : haveI := isPrime_map_quotient hbQ
      Module.Flat (B ⧸ b)
        (Localization.AtPrime (Q.map (Ideal.Quotient.mk (b.map (algebraMap B C)))))) :
    Module.Flat B (Localization.AtPrime Q) := by
  let CQ := Localization.AtPrime Q
  let gQ : C →ₗ[C] CQ := Algebra.linearMap C CQ
  -- `C_Q ⊗_B b → C_Q ⊗_B B` is injective
  have hinjl : Function.Injective (AlgebraTensorModule.lTensor C CQ b.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨x, u⟩, hxu⟩ :=
      IsLocalizedModule.surj Q.primeCompl (AlgebraTensorModule.rTensor B b gQ) y
    simp only [Submonoid.smul_def] at hxu
    have h1 :
        AlgebraTensorModule.rTensor B B gQ (AlgebraTensorModule.lTensor C C b.subtype x) = 0 := by
      rw [← IsLocalizedModule.map_apply Q.primeCompl (AlgebraTensorModule.rTensor B b gQ),
        IsLocalizedModule.map_lTensor (S := Q.primeCompl) (g := gQ) (f := b.subtype), ← hxu,
        map_smul, hy, smul_zero]
    obtain ⟨u', hu'⟩ := (IsLocalizedModule.eq_zero_iff Q.primeCompl
      (AlgebraTensorModule.rTensor B B gQ)).mp h1
    have h2 : s • u'.1 • x = 0 := hs _ (by rw [LinearMap.mem_ker, map_smul]; exact hu')
    apply IsLocalizedModule.smul_injective (AlgebraTensorModule.rTensor B b gQ)
      (⟨s, hsQ⟩ * u' * u)
    change (s * u'.1 * u.1) • y = (s * u'.1 * u.1) • 0
    rw [smul_zero, mul_smul, mul_smul, hxu, ← map_smul, ← map_smul, h2, map_zero]
  have hinjr : Function.Injective (b.subtype.rTensor CQ) := by
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj, ← AlgebraTensorModule.coe_lTensor (A := C)]
    exact hinjl
  -- the local homomorphism `B_p → C_Q`
  let p := Q.comap (algebraMap B C)
  let Bp := Localization.AtPrime p
  let : Algebra Bp CQ := (Localization.localRingHom p Q (algebraMap B C) rfl).toAlgebra
  have : IsScalarTower B Bp CQ := IsScalarTower.of_algebraMap_eq fun x =>
    (Localization.localRingHom_to_map p Q (algebraMap B C) rfl x).symm
  have : IsLocalHom (algebraMap Bp CQ) :=
    Localization.isLocalHom_localRingHom p Q (algebraMap B C) rfl
  let I := b.map (algebraMap B Bp)
  have hbp : b ≤ p := fun x hx => hbQ (Ideal.mem_map_of_mem _ hx)
  have hI : I ≠ ⊤ := by
    refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal Bp).ne_top ?_
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalization.AtPrime.to_map_mem_maximal_iff Bp p]
    exact hbp hx
  have hTor : Function.Injective (I.subtype.rTensor CQ) :=
    Ideal.rTensor_subtype_map_injective Bp b CQ hinjr
  -- flatness of `C_Q / I C_Q` over `B_p / I`
  have hrestr : (I • ⊤ : Submodule Bp CQ).restrictScalars B = b • ⊤ := by
    rw [Ideal.smul_top_eq_map, Ideal.smul_top_eq_map, Submodule.restrictScalars_restrictScalars,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let : Module (B ⧸ b) (CQ ⧸ (I • ⊤ : Submodule Bp CQ)) :=
    Module.compHom _ (algebraMap (B ⧸ b) (Bp ⧸ I))
  have : IsScalarTower (B ⧸ b) (Bp ⧸ I) (CQ ⧸ (I • ⊤ : Submodule Bp CQ)) :=
    IsScalarTower.of_compHom _ _ _
  have : IsScalarTower B (B ⧸ b) (CQ ⧸ (I • ⊤ : Submodule Bp CQ)) := by
    refine IsScalarTower.of_algebraMap_smul fun x y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have h1 :
        (algebraMap B (B ⧸ b) x) • (Submodule.Quotient.mk y : CQ ⧸ (I • ⊤ : Submodule Bp CQ)) =
        (algebraMap B Bp x) • Submodule.Quotient.mk y := rfl
    rw [h1, algebraMap_smul]
  have := isPrime_map_quotient hbQ
  let e : (CQ ⧸ (I • ⊤ : Submodule Bp CQ)) ≃ₗ[B ⧸ b]
      Localization.AtPrime (Q.map (Ideal.Quotient.mk (b.map (algebraMap B C)))) :=
    (((Submodule.Quotient.restrictScalarsEquiv B (I • ⊤ : Submodule Bp CQ)).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hrestr).extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective) ≪≫ₗ quotientSMulTopAtPrimeEquiv b hbQ
  have : Module.Flat (B ⧸ b) (CQ ⧸ (I • ⊤ : Submodule Bp CQ)) := Module.Flat.of_linearEquiv e
  have hflatI : Module.Flat (Bp ⧸ I) (CQ ⧸ (I • ⊤ : Submodule Bp CQ)) :=
    (Module.flat_iff_of_isLocalization (Bp ⧸ I)
      (Algebra.algebraMapSubmonoid (B ⧸ b) p.primeCompl) _).mpr inferInstance
  have : Module.Flat Bp CQ :=
    Module.Flat.of_rTensor_subtype_injective_of_flat_quotient CQ CQ I hI hTor hflatI
  exact Module.Flat.trans B Bp CQ

/-- For a prime `Q ⊇ IC` of `C`, the ring `C_Q ⧸ I C_Q` over `B ⧸ I` is the local ring of
`C ⧸ IC` at the image of `Q`. -/
noncomputable def quotientMapAtPrimeAlgEquiv (I : Ideal B) {Q : Ideal C} [Q.IsPrime]
    (hIQ : I.map (algebraMap B C) ≤ Q) :
    haveI := isPrime_map_quotient hIQ
    (Localization.AtPrime Q ⧸ I.map (algebraMap B (Localization.AtPrime Q))) ≃ₐ[B ⧸ I]
      Localization.AtPrime (Q.map (Ideal.Quotient.mk (I.map (algebraMap B C)))) := by
  haveI := isPrime_map_quotient hIQ
  haveI := isLocalization_atPrime_quotient hIQ
  have hJ : I.map (algebraMap B (Localization.AtPrime Q)) =
      (I.map (algebraMap B C)).map (algebraMap C (Localization.AtPrime Q)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let e3 := IsLocalization.algEquiv (Q.map (Ideal.Quotient.mk (I.map (algebraMap B C)))).primeCompl
      (Localization.AtPrime Q ⧸
        (I.map (algebraMap B C)).map (algebraMap C (Localization.AtPrime Q)))
      (Localization.AtPrime (Q.map (Ideal.Quotient.mk (I.map (algebraMap B C)))))
  refine AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq hJ).trans e3.toRingEquiv) fun x => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change e3 (Ideal.quotEquivOfEq hJ (Ideal.Quotient.mk _ (algebraMap B _ x))) = _
  rw [Ideal.quotEquivOfEq_mk, IsScalarTower.algebraMap_apply B C (Localization.AtPrime Q),
    ← Ideal.Quotient.algebraMap_quotient_map_quotient, AlgEquiv.commutes,
    IsScalarTower.algebraMap_apply (B ⧸ I) (C ⧸ I.map (algebraMap B C)),
    Ideal.Quotient.algebraMap_quotient_map_quotient]

omit [IsNoetherianRing B] in
/-- Flatness passes to the quotients `D/ID` over `B/I`, `D/ID` being `(B/I) ⊗_B D`. -/
theorem flat_quotient_map_of_flat (I : Ideal B) (D : Type*) [CommRing D] [Algebra B D]
    [Module.Flat B D] : Module.Flat (B ⧸ I) (D ⧸ I.map (algebraMap B D)) := by
  let e : ((B ⧸ I) ⊗[B] D) ≃ₗ[B] D ⧸ I.map (algebraMap B D) :=
    TensorProduct.quotTensorEquivQuotSMul D I ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I) ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv B _
  exact Module.Flat.of_linearEquiv (e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective).symm

omit [IsNoetherianRing B] in
/-- **Stacks 031L, iterated.** For `D` flat over `B`, formal smoothness of `B/b → D/bD` passes to
every `B/bⁿ⁺¹ → D/bⁿ⁺¹D`: each step is a square-zero thickening. -/
theorem formallySmooth_quotient_pow_of_flat (b : Ideal B) (D : Type*) [CommRing D] [Algebra B D]
    [Module.Flat B D]
    (h0 : Algebra.FormallySmooth (B ⧸ b ^ (0 + 1)) (D ⧸ (b ^ (0 + 1)).map (algebraMap B D)))
    (n : ℕ) :
    Algebra.FormallySmooth (B ⧸ b ^ (n + 1)) (D ⧸ (b ^ (n + 1)).map (algebraMap B D)) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    have hle : b ^ (n + 1 + 1) ≤ b ^ (n + 1) := Ideal.pow_le_pow_right n.succ.le_succ
    have hleD : (b ^ (n + 1 + 1)).map (algebraMap B D) ≤ (b ^ (n + 1)).map (algebraMap B D) :=
      Ideal.map_mono hle
    let f := algebraMap (B ⧸ b ^ (n + 1 + 1)) (D ⧸ (b ^ (n + 1 + 1)).map (algebraMap B D))
    let qR := Ideal.Quotient.factor hle
    let qS := Ideal.Quotient.factor hleD
    let g := algebraMap (B ⧸ b ^ (n + 1)) (D ⧸ (b ^ (n + 1)).map (algebraMap B D))
    have hfmk : f.comp (Ideal.Quotient.mk _) =
        (Ideal.Quotient.mk _).comp (algebraMap B D) := RingHom.ext fun _ => rfl
    have hflat : f.Flat := RingHom.flat_algebraMap_iff.mpr (flat_quotient_map_of_flat _ D)
    have hcomm : qS.comp f = g.comp qR := Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    have hsq : RingHom.ker qR ^ 2 = ⊥ := by
      rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker,
        Ideal.mk_ker, ← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    have heq : RingHom.ker qS = (RingHom.ker qR).map f := by
      rw [Ideal.Quotient.factor_ker, Ideal.Quotient.factor_ker, Ideal.map_map, Ideal.map_map,
        hfmk]
    exact RingHom.formallySmooth_algebraMap.mp
      (RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero f hflat qR qS g
        (Ideal.Quotient.factor_surjective hle) (Ideal.Quotient.factor_surjective hleD) hcomm hsq
        heq (RingHom.formallySmooth_algebraMap.mpr ih))

omit [IsNoetherianRing C] in
/-- **Smoothness of every stage at a prime where `C_Q` is flat.** If `C_Q` is flat over `B` and
`B/b → C/bC` is smooth at `Q`, then every `Bₙ → Cₙ` of finite type is smooth at `Qₙ`. -/
theorem smoothAt_quotient_pow_of_flat (b : Ideal B) (Q : Ideal C) [Q.IsPrime]
    (hbQ : b.map (algebraMap B C) ≤ Q) (hflat : Module.Flat B (Localization.AtPrime Q))
    (h0 : haveI := isPrime_map_quotient (map_pow_succ_le hbQ 0)
      Algebra.SmoothAt (B ⧸ b ^ (0 + 1)) (C ⧸ (b ^ (0 + 1)).map (algebraMap B C))
        (Q.map (Ideal.Quotient.mk ((b ^ (0 + 1)).map (algebraMap B C)))))
    (n : ℕ) (hft : Algebra.FiniteType (B ⧸ b ^ (n + 1)) (C ⧸ (b ^ (n + 1)).map (algebraMap B C))) :
    haveI := isPrime_map_quotient (map_pow_succ_le hbQ n)
    Algebra.SmoothAt (B ⧸ b ^ (n + 1)) (C ⧸ (b ^ (n + 1)).map (algebraMap B C))
      (Q.map (Ideal.Quotient.mk ((b ^ (n + 1)).map (algebraMap B C)))) := by
  have := isPrime_map_quotient (map_pow_succ_le hbQ n)
  have := isPrime_map_quotient (map_pow_succ_le hbQ 0)
  have hfs0 : Algebra.FormallySmooth (B ⧸ b ^ (0 + 1))
      (Localization.AtPrime Q ⧸ (b ^ (0 + 1)).map (algebraMap B (Localization.AtPrime Q))) := by
    have := Algebra.isSmoothAt_of_smoothAt _ _ h0
    exact Algebra.FormallySmooth.of_equiv
      (quotientMapAtPrimeAlgEquiv (b ^ (0 + 1)) (map_pow_succ_le hbQ 0)).symm
  have hfs := formallySmooth_quotient_pow_of_flat b (Localization.AtPrime Q) hfs0 n
  have := Algebra.FormallySmooth.of_equiv
    (quotientMapAtPrimeAlgEquiv (b ^ (n + 1)) (map_pow_succ_le hbQ n))
  have : Algebra.FinitePresentation (B ⧸ b ^ (n + 1)) (C ⧸ (b ^ (n + 1)).map (algebraMap B C)) :=
    Algebra.FinitePresentation.of_finiteType.mp hft
  exact (Algebra.smoothAt_iff_isSmoothAt _ _ _).mpr inferInstance

/-- **A common smooth neighbourhood of all the adic stages (the key step of Stacks 0GI9).** Let
`B → C` be a homomorphism of Noetherian rings, `b ⊆ B` an ideal and `q ⊇ bC` a prime of `C`. If
every stage `B/bⁿ⁺¹ → C/bⁿ⁺¹C` is of finite type and smooth at the image of `q`, there is one
`f ∉ q` such that every stage is smooth at the image of every prime `Q ⊇ bC` with `f ∉ Q`. -/
theorem exists_notMem_forall_smoothAt_quotient_pow (b : Ideal B) (q : Ideal C) [q.IsPrime]
    (hq : b.map (algebraMap B C) ≤ q)
    (hft : ∀ n : ℕ,
      Algebra.FiniteType (B ⧸ b ^ (n + 1)) (C ⧸ (b ^ (n + 1)).map (algebraMap B C)))
    (hsm : ∀ n : ℕ, haveI := isPrime_map_quotient (map_pow_succ_le hq n)
      Algebra.SmoothAt (B ⧸ b ^ (n + 1)) (C ⧸ (b ^ (n + 1)).map (algebraMap B C))
        (q.map (Ideal.Quotient.mk ((b ^ (n + 1)).map (algebraMap B C))))) :
    ∃ f ∉ q, ∀ (n : ℕ) (Q : Ideal C) [Q.IsPrime] (hQ : b.map (algebraMap B C) ≤ Q), f ∉ Q →
      haveI := isPrime_map_quotient (map_pow_succ_le hQ n)
      Algebra.SmoothAt (B ⧸ b ^ (n + 1)) (C ⧸ (b ^ (n + 1)).map (algebraMap B C))
        (Q.map (Ideal.Quotient.mk ((b ^ (n + 1)).map (algebraMap B C)))) := by
  have hflatq := flat_localization_atPrime_of_forall_smoothAt b q hq hsm
  obtain ⟨s, hsq, hs⟩ := exists_notMem_smul_ker_lTensor_eq_zero (b ^ (0 + 1)) q hflatq
  have := isPrime_map_quotient (map_pow_succ_le hq 0)
  obtain ⟨g, hgq, hg⟩ := hsm 0
  obtain ⟨f₂, rfl⟩ := Ideal.Quotient.mk_surjective g
  have hf₂ : f₂ ∉ q := fun h => hgq (Ideal.mem_map_of_mem _ h)
  refine ⟨s * f₂, fun h => (‹q.IsPrime›.mem_or_mem h).elim hsq hf₂, ?_⟩
  intro n Q _ hQ hfQ
  have hsQ : s ∉ Q := fun h => hfQ (Q.mul_mem_right _ h)
  have hf₂Q : f₂ ∉ Q := fun h => hfQ (Q.mul_mem_left _ h)
  have := isPrime_map_quotient (map_pow_succ_le hQ 0)
  have h0 : Algebra.SmoothAt (B ⧸ b ^ (0 + 1)) (C ⧸ (b ^ (0 + 1)).map (algebraMap B C))
      (Q.map (Ideal.Quotient.mk ((b ^ (0 + 1)).map (algebraMap B C)))) := by
    refine ⟨Ideal.Quotient.mk _ f₂, fun h => hf₂Q ?_, hg⟩
    rwa [Ideal.mem_quotient_iff_mem (map_pow_succ_le hQ 0)] at h
  have hflatQ := flat_localization_atPrime_of_smul_ker_eq_zero (b ^ (0 + 1)) hs Q
    (map_pow_succ_le hQ 0) hsQ (flat_localization_atPrime_of_smoothAt h0)
  exact smoothAt_quotient_pow_of_flat b Q hQ hflatQ h0 n (hft n)

end Algebra
