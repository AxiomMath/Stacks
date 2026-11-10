module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.Algebra.Module.TwoTermComplex.Noetherian
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.AlgebraicGeometry.Flatness.EssentialFinitePresentation
public import StacksFrontier.RingTheory.Flat.LocalCriterionNonNoetherian

/-!
# Complexes whose derived fibres are concentrated in one degree

Let `φ : R → A` be a flat ring map of finite presentation and let `K ∈ D(A)` be pseudo-coherent.
If for every prime `p` of `R` the derived fibre `K ⊗^L_R κ(p)` has cohomology only in degree `n`,
then `K` has cohomology only in degree `n` and `H^n(K)` is flat over `R`.

Represent `K` by a bounded above complex `P` of finite projective `A`-modules. At a maximal ideal
`q` of `A` over `p ⊂ R` the local rings `R_p → A_q` form a local homomorphism essentially of
finite presentation, and exactness of `κ(p) ⊗_R P` in degree `i` says that the localized
differential `coker(d^{i-1})_q → P^{i+1}_q` is injective modulo the maximal ideal of `R_p`. The
local criterion of flatness without Noetherian hypotheses (Stacks 046Y) then gives exactness of
`P` in degree `i` together with flatness over `R` of the cokernels of the differentials; the
flatness of `H^n(P)` follows from the short exact sequences around degree `n`.

## Main results

* `PseudoCoherence.ker_eq_range_and_flat_quotient_of_exact_mod_maximalIdeal`: the local step.
* `PseudoCoherence.ker_eq_range_and_flat_quotient_of_exact_mod_primes`: its globalisation over
  the maximal ideals of `A`.
* `PseudoCoherence.exactAt_and_flat_homology_of_exactAt_fibres`: the statement for a complex of
  finite projective modules.
* `PseudoCoherence.isZero_homology_and_flat_of_isZero_homology_derivedFibre`: the statement for a
  pseudo-coherent object of `D(A)`.

## References

* [Stacks Project, Tag 046Y](https://stacks.math.columbia.edu/tag/046Y)
-/

@[expose] public section

open IsLocalRing

universe u

namespace PseudoCoherence

section LocalStep

/-- **The local step.** Let `R → S` be a local homomorphism of local rings with `S` essentially
of finite presentation over `R`, and let `P → Q → N` be a complex of `S`-modules with `P` finite,
`Q` and `N` of finite presentation over `S` and `N` flat over `R`. If the complex is exact in the
middle modulo the maximal ideal `𝔪` of `R`, then it is exact in the middle and `N/e(Q)` is flat
over `R`. -/
theorem ker_eq_range_and_flat_quotient_of_exact_mod_maximalIdeal
    {R S P Q N : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    [AddCommGroup P] [Module S P]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S P] [Module.FinitePresentation S Q] [Module.FinitePresentation S N]
    [Module.Flat R N]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (d : P →ₗ[S] Q) (e : Q →ₗ[S] N)
    (hde : e ∘ₗ d = 0)
    (h : ∀ y : Q, e y ∈ maximalIdeal R • (⊤ : Submodule R N) →
      ∃ x : P, y - d x ∈ maximalIdeal R • (⊤ : Submodule R Q)) :
    LinearMap.ker e = LinearMap.range d ∧ Module.Flat R (N ⧸ LinearMap.range e) := by
  have hle : LinearMap.range d ≤ LinearMap.ker e := LinearMap.range_le_ker_iff.2 hde
  have : (LinearMap.range d).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map d
  have : Module.FinitePresentation S (Q ⧸ LinearMap.range d) :=
    Module.finitePresentation_of_surjective _ (LinearMap.range d).mkQ_surjective
      (by rw [Submodule.ker_mkQ]; assumption)
  let u : (Q ⧸ LinearMap.range d) →ₗ[S] N := (LinearMap.range d).liftQ e hle
  have hu : Function.Injective
      (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R (Q ⧸ LinearMap.range d)))
        (maximalIdeal R • (⊤ : Submodule R N)) (u.restrictScalars R)
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) (u.restrictScalars R))) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨x, hx⟩ := h y hz
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have : (LinearMap.range d).mkQ y = (LinearMap.range d).mkQ (y - d x) := by
      rw [map_sub, Submodule.mkQ_apply (LinearMap.range d) (d x),
        (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self d x), sub_zero]
    rw [this]
    exact Submodule.smul_top_le_comap_smul_top (maximalIdeal R)
        (((LinearMap.range d).mkQ).restrictScalars R) hx
  obtain ⟨hinj, hflat⟩ :=
    Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal hS u hu
  refine ⟨le_antisymm (fun y hy => ?_) hle, ?_⟩
  · have : u ((LinearMap.range d).mkQ y) = 0 := hy
    have h0 := hinj (this.trans (map_zero u).symm)
    exact (Submodule.Quotient.mk_eq_zero _).1 h0
  · have hr : LinearMap.range u = LinearMap.range e := Submodule.range_liftQ _ _ _
    rw [hr] at hflat
    exact hflat

end LocalStep


section Global

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- `p • M` is stable under the action of `A`, for an ideal `p` of `R` and an `A`-module `M`. -/
theorem smul_mem_smul_top_of_mem {M : Type*} [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] (p : Ideal R) (a : A) {w : M} (hw : w ∈ p • (⊤ : Submodule R M)) :
    a • w ∈ p • (⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on hw (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · rw [smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [smul_add]
    exact Submodule.add_mem _ hx hy


/-- **The global step.** Let `R → A` be flat and of finite presentation and let `P → Q → N` be a
complex of `A`-modules with `P` finite, `Q` and `N` of finite presentation, and `N` flat over `A`.
Suppose that for every prime `p` of `R` the complex is exact in the middle modulo `p` up to a
scalar outside `p`: if `e(y) ∈ pN` then `b • y - d(x) ∈ pQ` for some `x` and some `b ∉ p`. Then the
complex is exact in the middle and `N/e(Q)` is flat over `R`. -/
theorem ker_eq_range_and_flat_quotient_of_exact_mod_primes
    (hfl : (algebraMap R A).Flat) (hfp : (algebraMap R A).FinitePresentation)
    {P Q N : Type u} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module R Q] [Module A Q] [IsScalarTower R A Q]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite A P] [Module.FinitePresentation A Q] [Module.FinitePresentation A N]
    [Module.Flat A N]
    (d : P →ₗ[A] Q) (e : Q →ₗ[A] N) (hde : e ∘ₗ d = 0)
    (h : ∀ (p : Ideal R) [p.IsPrime] (y : Q), e y ∈ p • (⊤ : Submodule R N) →
      ∃ (x : P) (b : R), b ∉ p ∧ b • y - d x ∈ p • (⊤ : Submodule R Q)) :
    LinearMap.ker e = LinearMap.range d ∧ Module.Flat R (N ⧸ LinearMap.range e) := by
  have hloc : ∀ (q : Ideal A) [q.IsMaximal],
      LinearMap.ker (LocalizedModule.map q.primeCompl e) =
          LinearMap.range (LocalizedModule.map q.primeCompl d) ∧
        Module.Flat R (LocalizedModule q.primeCompl N ⧸
          (LinearMap.range e).localized q.primeCompl) := by
    intro q _
    let p : Ideal R := q.comap (algebraMap R A)
    let Rp := Localization.AtPrime p
    let Aq := Localization.AtPrime q
    let φq : Rp →+* Aq := Localization.localRingHom p q (algebraMap R A) rfl
    let : Algebra Rp Aq := φq.toAlgebra
    have : IsLocalHom (algebraMap Rp Aq) := Localization.isLocalHom_localRingHom _ _ _ rfl
    have hess : (algebraMap Rp Aq).EssentiallyOfFinitePresentation :=
      RingHom.EssentiallyOfFinitePresentation.localRingHom_of_finitePresentation _ hfp q
    have : Module.Flat Rp Aq := RingHom.Flat.localRingHom hfl q p rfl
    -- the scalar action of `R` through `R_p`, on fractions
    have hact : ∀ {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
        (r : R) (m : M) (s : q.primeCompl),
        (algebraMap Rp Aq (algebraMap R Rp r)) • LocalizedModule.mk m s =
          LocalizedModule.mk (r • m) s := by
      intro M _ _ _ _ r m s
      have h1 : algebraMap Rp Aq (algebraMap R Rp r) =
          algebraMap A Aq (algebraMap R A r) :=
        Localization.localRingHom_to_map p q (algebraMap R A) rfl r
      rw [h1, algebraMap_smul (R := A) (A := Localization q.primeCompl),
        LocalizedModule.smul'_mk, algebraMap_smul]
    -- the `R_p`-module structures of the localized modules
    let : Module Rp (LocalizedModule q.primeCompl Q) := Module.compHom _ (algebraMap Rp Aq)
    have : IsScalarTower Rp Aq (LocalizedModule q.primeCompl Q) :=
      ⟨fun r a m => mul_smul (algebraMap Rp Aq r) a m⟩
    let : Module Rp (LocalizedModule q.primeCompl N) := Module.compHom _ (algebraMap Rp Aq)
    have : IsScalarTower Rp Aq (LocalizedModule q.primeCompl N) :=
      ⟨fun r a m => mul_smul (algebraMap Rp Aq r) a m⟩
    -- fractions with numerator in `p • ⊤` lie in `𝔪 • ⊤`
    have hnum : ∀ {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
        [Module Rp (LocalizedModule q.primeCompl M)]
        [IsScalarTower Rp Aq (LocalizedModule q.primeCompl M)]
        (w : M), w ∈ p • (⊤ : Submodule R M) → ∀ u : q.primeCompl,
        LocalizedModule.mk w u ∈
          maximalIdeal Rp • (⊤ : Submodule Rp (LocalizedModule q.primeCompl M)) := by
      intro M _ _ _ _ _ _ w hw u
      refine Submodule.smul_induction_on hw (fun r hr m _ => ?_) (fun x y hx hy => ?_)
      · rw [← hact r m u, algebraMap_smul Aq (algebraMap R Rp r) (LocalizedModule.mk m u)]
        exact Submodule.smul_mem_smul
          ((IsLocalization.AtPrime.to_map_mem_maximal_iff Rp p r).2 hr) Submodule.mem_top
      · have : LocalizedModule.mk (x + y) u =
            LocalizedModule.mk x u + LocalizedModule.mk y u := by
          rw [LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]
        rw [this]
        exact Submodule.add_mem _ hx hy
    -- conversely, a fraction in `𝔪 • ⊤` has a numerator in `p • ⊤` up to a unit
    have hden : ∀ {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
        [Module Rp (LocalizedModule q.primeCompl M)]
        [IsScalarTower Rp Aq (LocalizedModule q.primeCompl M)]
        (z : M) (s : q.primeCompl), LocalizedModule.mk z s ∈
          maximalIdeal Rp • (⊤ : Submodule Rp (LocalizedModule q.primeCompl M)) →
        ∃ t : q.primeCompl, (t : A) • z ∈ p • (⊤ : Submodule R M) := by
      intro M _ _ _ _ _ _ z s hz
      -- the action of a fraction of `R_p` on a fraction
      have hsmul : ∀ (a : R) (σ : p.primeCompl) (m : M) (v : q.primeCompl),
          IsLocalization.mk' Rp a σ • LocalizedModule.mk m v =
            LocalizedModule.mk (algebraMap R A a • m) (⟨algebraMap R A σ, σ.2⟩ * v) := by
        intro a σ m v
        rw [← algebraMap_smul Aq (IsLocalization.mk' Rp a σ) (LocalizedModule.mk m v)]
        change φq (IsLocalization.mk' Rp a σ) • LocalizedModule.mk m v = _
        rw [Localization.localRingHom_mk', ← Localization.mk_eq_mk', LocalizedModule.mk_smul_mk]
      let T : Submodule Rp (LocalizedModule q.primeCompl M) :=
        { carrier := {w | ∃ z' ∈ p • (⊤ : Submodule R M), ∃ u : q.primeCompl,
            w = LocalizedModule.mk z' u}
          add_mem' := by
            rintro _ _ ⟨z₁, hz₁, u₁, rfl⟩ ⟨z₂, hz₂, u₂, rfl⟩
            exact ⟨_, Submodule.add_mem _ (smul_mem_smul_top_of_mem p _ hz₁)
              (smul_mem_smul_top_of_mem p _ hz₂), _, LocalizedModule.mk_add_mk⟩
          zero_mem' := ⟨0, Submodule.zero_mem _, 1, (LocalizedModule.zero_mk 1).symm⟩
          smul_mem' := by
            rintro c _ ⟨z', hz', u, rfl⟩
            obtain ⟨⟨a, σ⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Rp) p.primeCompl c
            exact ⟨algebraMap R A a • z', smul_mem_smul_top_of_mem p _ hz',
              ⟨algebraMap R A σ, σ.2⟩ * u, hsmul a σ z' u⟩ }
      have hle : maximalIdeal Rp • (⊤ : Submodule Rp (LocalizedModule q.primeCompl M)) ≤ T := by
        rw [Submodule.smul_le]
        intro r hr w _
        obtain ⟨⟨a, σ⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Rp) p.primeCompl r
        have ha : a ∈ p := (IsLocalization.AtPrime.mk'_mem_maximal_iff Rp p a σ).1 hr
        induction w using LocalizedModule.induction_on with
        | h m v =>
          refine ⟨algebraMap R A a • m, ?_, ⟨algebraMap R A σ, σ.2⟩ * v, ?_⟩
          · rw [algebraMap_smul]
            exact Submodule.smul_mem_smul ha Submodule.mem_top
          · exact hsmul a σ m v
      obtain ⟨z', hz', u, heq⟩ := hle hz
      obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.1 heq
      refine ⟨t * u, ?_⟩
      have : ((t * u : q.primeCompl) : A) • z = ((t * s : q.primeCompl) : A) • z' := by
        simpa [mul_smul, Submonoid.smul_def] using ht
      rw [this]
      exact smul_mem_smul_top_of_mem p _ hz'
    -- the localized complex is exact modulo `𝔪`
    let dq := LocalizedModule.map q.primeCompl d
    let eq := LocalizedModule.map q.primeCompl e
    have hdeq : eq ∘ₗ dq = 0 := by
      refine LinearMap.ext fun z => ?_
      induction z using LocalizedModule.induction_on with
      | h m s =>
        change LocalizedModule.map _ e (LocalizedModule.map _ d (LocalizedModule.mk m s)) = 0
        rw [LocalizedModule.map_mk, LocalizedModule.map_mk,
          show e (d m) = 0 from LinearMap.congr_fun hde m, LocalizedModule.zero_mk]
    have hsub : ∀ (a c : Q) (u : q.primeCompl), LocalizedModule.mk a u - LocalizedModule.mk c u =
        LocalizedModule.mk (a - c) u := by
      intro a c u
      rw [sub_eq_iff_eq_add, LocalizedModule.mk_add_mk, ← smul_add,
        LocalizedModule.mk_cancel_common_left, sub_add_cancel]
    have hex : ∀ y : LocalizedModule q.primeCompl Q,
        eq y ∈ maximalIdeal Rp • (⊤ : Submodule Rp (LocalizedModule q.primeCompl N)) →
        ∃ x, y - dq x ∈ maximalIdeal Rp • (⊤ : Submodule Rp (LocalizedModule q.primeCompl Q)) := by
      intro y hy
      induction y using LocalizedModule.induction_on with
      | h y₀ s =>
        change LocalizedModule.map _ e (LocalizedModule.mk y₀ s) ∈ _ at hy
        rw [LocalizedModule.map_mk] at hy
        obtain ⟨t, ht⟩ := hden (e y₀) s hy
        rw [← LinearMap.map_smul] at ht
        obtain ⟨x, b, hb, hbx⟩ := h p ((t : A) • y₀) ht
        let b' : q.primeCompl := ⟨algebraMap R A b, hb⟩
        refine ⟨LocalizedModule.mk x (b' * t * s), ?_⟩
        change _ - LocalizedModule.map _ d (LocalizedModule.mk x (b' * t * s)) ∈ _
        rw [LocalizedModule.map_mk,
          ← LocalizedModule.mk_cancel_common_left (b' * t) s y₀, hsub]
        have hnum' : (b' * t : q.primeCompl) • y₀ = b • ((t : A) • y₀) := by
          rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul, ← algebraMap_smul (A := A) b]
        rw [hnum']
        exact hnum _ hbx _
    have : Module.Finite Aq (LocalizedModule q.primeCompl P) :=
      Module.Finite.of_isLocalizedModule q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl P)
    have : Module.Flat Rp (LocalizedModule q.primeCompl N) := Module.Flat.trans Rp Aq _
    obtain ⟨hker, hflat⟩ :=
      ker_eq_range_and_flat_quotient_of_exact_mod_maximalIdeal hess dq eq hdeq hex
    refine ⟨hker, ?_⟩
    have hrange : LinearMap.range eq = (LinearMap.range e).localized q.primeCompl := by
      rw [Submodule.localized, Submodule.localized'_eq_span]
      refine le_antisymm ?_ (Submodule.span_le.2 ?_)
      · rintro _ ⟨z, rfl⟩
        induction z using LocalizedModule.induction_on with
        | h y s =>
          change LocalizedModule.map _ e (LocalizedModule.mk y s) ∈ _
          rw [LocalizedModule.map_mk]
          have : LocalizedModule.mk (e y) s =
              Localization.mk (1 : A) s • LocalizedModule.mk (e y) (1 : q.primeCompl) := by
            rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e y, ⟨y, rfl⟩, rfl⟩)
      · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨LocalizedModule.mk y 1, LocalizedModule.map_mk _ _ _ _⟩
    let : Module Rp (LocalizedModule q.primeCompl N ⧸
        (LinearMap.range e).localized q.primeCompl) := inferInstance
    have hflat' : Module.Flat Rp (LocalizedModule q.primeCompl N ⧸
        (LinearMap.range e).localized q.primeCompl) :=
      (Module.Flat.equiv_iff ((Submodule.quotEquivOfEq _ _ hrange).restrictScalars Rp)).1 hflat
    have : IsScalarTower R Rp (LocalizedModule q.primeCompl N ⧸
        (LinearMap.range e).localized q.primeCompl) := by
      refine ⟨fun r c x => ?_⟩
      have h1 : algebraMap Rp Aq (algebraMap R Rp r) = algebraMap R Aq r := by
        change φq (algebraMap R Rp r) = _
        rw [Localization.localRingHom_to_map p q (algebraMap R A) rfl r,
          ← IsScalarTower.algebraMap_apply R A Aq]
      rw [Algebra.smul_def, ← smul_smul, ← algebraMap_smul Aq (algebraMap R Rp r), h1,
        algebraMap_smul]
    exact Module.Flat.trans R Rp _
  -- exactness, from the local exactness at the maximal ideals
  refine ⟨le_antisymm (fun y hy => ?_) (LinearMap.range_le_ker_iff.2 hde), ?_⟩
  · let I : Ideal A := (LinearMap.range d).comap (LinearMap.toSpanSingleton A Q y)
    by_contra hy'
    have hI : I ≠ ⊤ := by
      intro htop
      have : (1 : A) ∈ I := htop ▸ Submodule.mem_top
      apply hy'
      simpa [I] using this
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hI
    have hmem : LocalizedModule.mk y (1 : q.primeCompl) ∈
        LinearMap.ker (LocalizedModule.map q.primeCompl e) := by
      rw [LinearMap.mem_ker, LocalizedModule.map_mk, show e y = 0 from hy,
        LocalizedModule.zero_mk]
    rw [(hloc q).1] at hmem
    obtain ⟨z, hz⟩ := hmem
    induction z using LocalizedModule.induction_on with
    | h x s =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hz
      obtain ⟨t, ht⟩ := hz
      have hts : ((t * s : q.primeCompl) : A) ∈ I := by
        change LinearMap.toSpanSingleton A Q y ((t * s : q.primeCompl) : A) ∈ LinearMap.range d
        rw [LinearMap.toSpanSingleton_apply]
        refine ⟨(t : A) • x, ?_⟩
        rw [map_smul]
        simpa [mul_smul, Submonoid.smul_def] using ht
      exact (t * s).2 (hIq hts)
  · exact Module.flat_of_isLocalized_maximal A (N ⧸ LinearMap.range e)
      (fun P _ => LocalizedModule P.primeCompl N ⧸ (LinearMap.range e).localized P.primeCompl)
      (fun P _ => (LinearMap.range e).toLocalizedQuotient P.primeCompl) (fun P _ => (hloc P).2)

end Global


/-! ### Elements of the fibre `κ(p) ⊗_R M` -/

section ResidueField

variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
  {M : Type u} [AddCommGroup M] [Module R M]

open TensorProduct in
/-- An element `m` of `M` vanishing in the fibre `κ(p) ⊗_R M` lies in `p • M` after multiplication
by a scalar outside `p`. -/
theorem exists_smul_mem_smul_top_of_one_tmul_eq_zero {m : M}
    (hm : (1 : p.ResidueField) ⊗ₜ[R] m = 0) :
    ∃ b : R, b ∉ p ∧ b • m ∈ p • (⊤ : Submodule R M) := by
  let Mbar := M ⧸ p • (⊤ : Submodule R M)
  let X := TensorProduct (R ⧸ p) p.ResidueField Mbar
  let g₀ : Mbar →ₗ[R ⧸ p] X := TensorProduct.mk (R ⧸ p) p.ResidueField Mbar 1
  let g : M →ₗ[R] X := (g₀.restrictScalars R).comp (p • (⊤ : Submodule R M)).mkQ
  have hg : g m = 0 := by
    have := congrArg (g.liftBaseChange p.ResidueField) hm
    rwa [LinearMap.liftBaseChange_tmul, one_smul, map_zero] at this
  have : IsLocalizedModule (nonZeroDivisors (R ⧸ p)) g₀ :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (R ⧸ p)) p.ResidueField g₀).2
      (TensorProduct.isBaseChange (R ⧸ p) Mbar p.ResidueField)
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (R ⧸ p)) g₀).1 hg
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (c : R ⧸ p)
  refine ⟨b, fun hbp => ?_, ?_⟩
  · exact nonZeroDivisors.coe_ne_zero c (hb ▸ Ideal.Quotient.eq_zero_iff_mem.2 hbp)
  · rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    change (Ideal.Quotient.mk p b) • (Submodule.Quotient.mk m : Mbar) = 0
    rwa [hb]

open TensorProduct in
/-- Every element of the fibre `κ(p) ⊗_R M` is of the form `1 ⊗ m` after multiplication by a
scalar outside `p`. -/
theorem exists_smul_eq_one_tmul (z : p.ResidueField ⊗[R] M) :
    ∃ b : R, b ∉ p ∧ ∃ m : M, algebraMap R p.ResidueField b • z = (1 : p.ResidueField) ⊗ₜ[R] m := by
  suffices h : ∃ b : R, b ∉ p ∧ ∃ m : M, b • z = (1 : p.ResidueField) ⊗ₜ[R] m by
    obtain ⟨b, hb, m, hm⟩ := h
    exact ⟨b, hb, m, by rwa [algebraMap_smul]⟩
  induction z using TensorProduct.inductionOn with
  | tmul c m =>
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (R ⧸ p)) c
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (s : R ⧸ p)
    refine ⟨b, fun hbp => nonZeroDivisors.coe_ne_zero s ?_, a' • m, ?_⟩
    · exact hb ▸ Ideal.Quotient.eq_zero_iff_mem.2 hbp
    · have hc : b • IsLocalization.mk' p.ResidueField (Ideal.Quotient.mk p a') s =
          a' • (1 : p.ResidueField) := by
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R (R ⧸ p) p.ResidueField b]
        change algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p b) * _ = _
        rw [hb, IsLocalization.mk'_spec' (M := nonZeroDivisors (R ⧸ p))]
        change algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p a') = _
        rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
          Algebra.algebraMap_eq_smul_one]
      rw [TensorProduct.smul_tmul', hc, TensorProduct.smul_tmul]
  | add z w hz hw =>
    obtain ⟨b₁, hb₁, m₁, h₁⟩ := hz
    obtain ⟨b₂, hb₂, m₂, h₂⟩ := hw
    refine ⟨b₁ * b₂, p.primeCompl.mul_mem hb₁ hb₂, b₂ • m₁ + b₁ • m₂, ?_⟩
    rw [smul_add, mul_comm, mul_smul, h₁, mul_comm, mul_smul, h₂, tmul_add,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]

open TensorProduct in
/-- Elements of `p • M` vanish in the fibre `κ(p) ⊗_R M`. -/
theorem one_tmul_eq_zero_of_mem_smul_top {m : M} (hm : m ∈ p • (⊤ : Submodule R M)) :
    (1 : p.ResidueField) ⊗ₜ[R] m = 0 := by
  refine Submodule.smul_induction_on hm (fun r hr n _ => ?_) (fun x y hx hy => ?_)
  · rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
      (Ideal.algebraMap_residueField_eq_zero (I := p)).2 hr, TensorProduct.zero_tmul]
  · rw [tmul_add, hx, hy, add_zero]

open TensorProduct in
/-- **Exactness of the fibre, read on `M` itself.** If `κ(p) ⊗_R P → κ(p) ⊗_R Q → κ(p) ⊗_R N` is
exact and `e(y) ∈ pN`, then `b • y - d(x) ∈ pQ` for some `x ∈ P` and some `b ∉ p`. -/
theorem exists_smul_sub_mem_smul_top_of_exact_lTensor {P Q N : Type u} [AddCommGroup P]
    [Module R P] [AddCommGroup Q] [Module R Q] [AddCommGroup N] [Module R N]
    (d : P →ₗ[R] Q) (e : Q →ₗ[R] N)
    (hex : Function.Exact (d.lTensor p.ResidueField) (e.lTensor p.ResidueField))
    (y : Q) (hy : e y ∈ p • (⊤ : Submodule R N)) :
    ∃ (x : P) (b : R), b ∉ p ∧ b • y - d x ∈ p • (⊤ : Submodule R Q) := by
  have h0 : e.lTensor p.ResidueField ((1 : p.ResidueField) ⊗ₜ[R] y) = 0 := by
    rw [LinearMap.lTensor_tmul]
    exact one_tmul_eq_zero_of_mem_smul_top p hy
  obtain ⟨z, hz⟩ := (hex _).1 h0
  obtain ⟨b, hb, x₀, hx₀⟩ := exists_smul_eq_one_tmul p z
  have h1 : (1 : p.ResidueField) ⊗ₜ[R] (b • y - d x₀) = 0 := by
    have := congrArg (d.lTensor p.ResidueField) hx₀
    rw [algebraMap_smul, map_smul, hz, LinearMap.lTensor_tmul, ← TensorProduct.tmul_smul] at this
    rw [tmul_sub, this, sub_self]
  obtain ⟨b', hb', hmem⟩ := exists_smul_mem_smul_top_of_one_tmul_eq_zero p h1
  refine ⟨b' • x₀, b' * b, p.primeCompl.mul_mem hb' hb, ?_⟩
  rwa [map_smul, mul_smul, ← smul_sub]

end ResidueField



section FlatPieces

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {P Q N : Type u} [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
  [AddCommGroup Q] [Module R Q] [Module A Q] [IsScalarTower R A Q]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

omit [Module R Q] [IsScalarTower R A Q] in
/-- The image of a map into a flat module with flat cokernel is flat. -/
theorem flat_range_of_flat_quotient [Module.Flat R N] (e : Q →ₗ[A] N)
    [Module.Flat R (N ⧸ LinearMap.range e)] : Module.Flat R (LinearMap.range e) := by
  have : Module.Flat R (N ⧸ (LinearMap.range e).restrictScalars R) :=
    (Module.Flat.equiv_iff (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range e))).2
      inferInstance
  have h := Stacks.TwoTermComplex.flat_ker_of_surjective
    ((LinearMap.range e).restrictScalars R).mkQ (Submodule.mkQ_surjective _)
  rwa [Submodule.ker_mkQ] at h

omit [Module R P] [IsScalarTower R A P] in
/-- In an exact sequence `P → Q → N` with `N` and `N/e(Q)` flat, the cokernel `Q/d(P)` is flat. -/
theorem flat_quotient_range_of_ker_eq [Module.Flat R N] (d : P →ₗ[A] Q) (e : Q →ₗ[A] N)
    (hker : LinearMap.ker e = LinearMap.range d) [Module.Flat R (N ⧸ LinearMap.range e)] :
    Module.Flat R (Q ⧸ LinearMap.range d) := by
  have := flat_range_of_flat_quotient (R := R) e
  exact (Module.Flat.equiv_iff (((Submodule.quotEquivOfEq _ _ hker.symm).trans
    e.quotKerEquivRange).restrictScalars R)).2 inferInstance

omit [Module R P] [IsScalarTower R A P] in
/-- **The homology of a complex `P → Q → N` with flat pieces.** If `e ∘ d = 0`, `Q/d(P)` is flat
and `e(Q)` is flat, then `ker e / d(P)` is flat; here `t : P → ker e` is the corestriction of
`d`. -/
theorem flat_ker_quotient_of_flat (d : P →ₗ[A] Q) (e : Q →ₗ[A] N)
    (t : P →ₗ[A] LinearMap.ker e) (ht : ∀ x, (t x : Q) = d x)
    [Module.Flat R (Q ⧸ LinearMap.range d)] [Module.Flat R (LinearMap.range e)] :
    Module.Flat R (LinearMap.ker e ⧸ LinearMap.range t) := by
  have hle : LinearMap.range d ≤ LinearMap.ker e.rangeRestrict := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_ker.2 <| Subtype.ext <|
      (congrArg e (ht x)).symm.trans (LinearMap.mem_ker.1 (t x).2)
  let g : (Q ⧸ LinearMap.range d) →ₗ[A] LinearMap.range e := (LinearMap.range d).liftQ _ hle
  have hg : Function.Surjective g := fun ⟨_, y, hy⟩ => ⟨Submodule.Quotient.mk y, Subtype.ext hy⟩
  have hflatker : Module.Flat R (LinearMap.ker (g.restrictScalars R)) :=
    Stacks.TwoTermComplex.flat_ker_of_surjective (g.restrictScalars R) hg
  have hle' :
      LinearMap.range t ≤ LinearMap.ker ((LinearMap.range d).mkQ ∘ₗ (LinearMap.ker e).subtype) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ht,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self d x
  let f : (LinearMap.ker e ⧸ LinearMap.range t) →ₗ[A] Q ⧸ LinearMap.range d :=
    (LinearMap.range t).liftQ _ hle'
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    rw [LinearMap.mem_ker] at hz
    change (LinearMap.range d).mkQ (z : Q) = 0 at hz
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).1 hz
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, Subtype.ext ((ht x).trans hx)⟩
  have hrange : LinearMap.range (f.restrictScalars R) = LinearMap.ker (g.restrictScalars R) := by
    ext w
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    refine ⟨?_, fun hy => ⟨Submodule.Quotient.mk ⟨y, congrArg Subtype.val hy⟩, rfl⟩⟩
    rintro ⟨z, hz⟩
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    rw [← hz, LinearMap.mem_ker]
    exact Subtype.ext z.2
  exact (Module.Flat.equiv_iff (((LinearEquiv.ofInjective (f.restrictScalars R) hf).trans
    (LinearEquiv.ofEq _ _ hrange)))).2 hflatker

end FlatPieces

/-! ### Complexes of finite projective modules -/

section Complex

open CategoryTheory TensorProduct

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Exactness of `S ⊗_R -` on a pair of maps, read through `ModuleCat.extendScalars` or through
`LinearMap.lTensor`: the two differ only in the spelling of the `R`-module structure of `S`. -/
theorem exact_lTensor_of_exact_extendScalars {S : Type u} [CommRing S] [Algebra R S]
    {M₁ M₂ M₃ : ModuleCat.{u} R} (g₁ : M₁ ⟶ M₂) (g₂ : M₂ ⟶ M₃)
    (hex : Function.Exact ((ModuleCat.extendScalars (algebraMap R S)).map g₁).hom
      ((ModuleCat.extendScalars (algebraMap R S)).map g₂).hom) :
    Function.Exact (g₁.hom.lTensor S) (g₂.hom.lTensor S) := by
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let e₀ : S' ≃ₗ[R] S :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => (Algebra.smul_def r (show S from x)).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E : ∀ M : ModuleCat.{u} R, TensorProduct R S' M ≃ₗ[R] S ⊗[R] M := fun M =>
    TensorProduct.congr e₀ (LinearEquiv.refl R M)
  have hcomm : ∀ {M M' : ModuleCat.{u} R} (g : M ⟶ M') (z : TensorProduct R S' M),
      E M' (TensorProduct.map LinearMap.id g.hom z) = g.hom.lTensor S (E M z) := by
    intro M M' g z
    induction z using TensorProduct.inductionOn with
    | tmul c m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmap : ∀ {M M' : ModuleCat.{u} R} (g : M ⟶ M') (z : TensorProduct R S' M),
      ((ModuleCat.extendScalars (algebraMap R S)).map g).hom z =
        TensorProduct.map LinearMap.id g.hom z := fun _ _ => rfl
  intro y
  obtain ⟨y', rfl⟩ := (E M₂).surjective y
  rw [← hcomm, LinearEquiv.map_eq_zero_iff (E M₃), ← hmap]
  refine (hex y').trans ⟨fun ⟨z, hz⟩ => ⟨E M₁ z, ?_⟩, fun ⟨z, hz⟩ => ?_⟩
  · have h1 := hcomm g₁ (show TensorProduct R S' M₁ from z)
    rw [← hmap g₁ z] at h1
    rw [← h1, hz]
  · obtain ⟨z', rfl⟩ := (E M₁).surjective z
    refine ⟨z', (E M₂).injective ?_⟩
    rw [hmap g₁ z', hcomm]
    exact hz


/-- Exactness of a short complex of modules, as exactness of its two underlying maps. -/
theorem function_exact_of_shortComplex_exact {B : Type u} [CommRing B]
    {S : ShortComplex (ModuleCat.{u} B)} (h : S.Exact) : Function.Exact S.f.hom S.g.hom :=
  LinearMap.exact_iff.2 h.moduleCat_range_eq_ker.symm

/-- **The complex form.** Let `φ : R → A` be flat and of finite presentation and let `P` be a
complex of finite projective `A`-modules. If for every prime `p` of `R` the fibre
`κ(p) ⊗_R P` is exact in every degree `i ≠ n`, then so is `P`, and `H^n(P)` is flat over `R`. -/
theorem exactAt_and_flat_homology_of_exactAt_fibres (φ : R →+* A) (hfl : φ.Flat)
    (hfp : φ.FinitePresentation) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ i, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i)) (n : ℤ)
    (hfib : ∀ (p : Ideal R) [p.IsPrime] (i : ℤ), i ≠ n →
      (((ModuleCat.extendScalars (algebraMap R p.ResidueField)).mapHomologicalComplex _).obj
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj P)).ExactAt i) :
    (∀ i, i ≠ n → P.ExactAt i) ∧
      Module.Flat R ((ModuleCat.restrictScalars φ).obj (P.homology n)) := by
  let := φ.toAlgebra
  let instR : ∀ i, Module R (P.X i) := fun i => Module.compHom _ φ
  have : ∀ i, IsScalarTower R A (P.X i) := fun i =>
    ⟨fun r a m => mul_smul (φ r) a m⟩
  have : ∀ i, Module.FinitePresentation A (P.X i) := fun i =>
    have := (hP i).1; have := (hP i).2; Module.finitePresentation_of_projective A (P.X i)
  have : ∀ i, Module.Flat A (P.X i) := fun i =>
    have := (hP i).2; inferInstance
  have : ∀ i, Module.Finite A (P.X i) := fun i => (hP i).1
  -- the local criterion at each degree `j ≠ n`
  have hstep : ∀ i j k, j = i + 1 → k = j + 1 → j ≠ n →
      LinearMap.ker (P.d j k).hom = LinearMap.range (P.d i j).hom ∧
        Module.Flat R (P.X k ⧸ LinearMap.range (P.d j k).hom) := by
    intro i j k hij hjk hj
    refine ker_eq_range_and_flat_quotient_of_exact_mod_primes hfl hfp _ _ ?_ ?_
    · ext x
      exact congrArg (fun f => f.hom x) (P.d_comp_d i j k)
    · intro p _ y hy
      have hC := hfib p j hj
      rw [HomologicalComplex.exactAt_iff' _ i j k (by simp; omega) (by simp; omega)] at hC
      have hex := exact_lTensor_of_exact_extendScalars _ _ (function_exact_of_shortComplex_exact hC)
      exact exists_smul_sub_mem_smul_top_of_exact_lTensor p _ _ hex y hy
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    have : x ∈ LinearMap.ker (P.d i (i + 1)).hom := hx
    rwa [(hstep (i - 1) i (i + 1) (by omega) rfl hi).1] at this
  · have : Module.Flat R A := hfl
    have : ∀ i, Module.Flat R (P.X i) := fun i => Module.Flat.trans R A (P.X i)
    let d₀ := (P.d (n - 1) n).hom
    let d₁ := (P.d n (n + 1)).hom
    let d₂ := (P.d (n + 1) (n + 2)).hom
    obtain ⟨hker₂, hflat₂⟩ := hstep n (n + 1) (n + 2) rfl (by omega) (by omega)
    have : Module.Flat R (P.X (n + 2) ⧸ LinearMap.range d₂) := hflat₂
    have : Module.Flat R (P.X n ⧸ LinearMap.range d₀) :=
      (hstep (n - 2) (n - 1) n (by omega) (by omega) (by omega)).2
    -- the pieces of the complex around degree `n` are flat
    have : Module.Flat R (P.X (n + 1) ⧸ LinearMap.range d₁) :=
      flat_quotient_range_of_ker_eq d₁ d₂ hker₂
    have : Module.Flat R (LinearMap.range d₁) := flat_range_of_flat_quotient (R := R) d₁
    let S := P.sc' (n - 1) n (n + 1)
    let t : P.X (n - 1) →ₗ[A] LinearMap.ker d₁ := S.moduleCatToCycles
    have hH : Module.Flat R (LinearMap.ker d₁ ⧸ LinearMap.range t) :=
      flat_ker_quotient_of_flat d₀ d₁ t (fun _ => rfl)
    -- `H^n(P)` is that quotient
    let E : P.homology n ≅ S.moduleCatLeftHomologyData.H :=
      P.homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp) ≪≫ S.moduleCatHomologyIso
    let E' : (ModuleCat.restrictScalars φ).obj (P.homology n) ≃ₗ[R]
        (LinearMap.ker d₁ ⧸ LinearMap.range t) :=
      { E.toLinearEquiv.toAddEquiv with
        map_smul' := fun r x => E.toLinearEquiv.map_smul (φ r) x }
    exact (Module.Flat.equiv_iff E').2 hH

end Complex


/-! ### The derived form -/

section Derived

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

variable {R A : Type u} [CommRing R] [CommRing A]

/-- **Pseudo-coherent complexes whose derived fibres are concentrated in one degree.** Let
`φ : R → A` be flat and of finite presentation and let `K ∈ D(A)` be pseudo-coherent. If for every
prime `p` of `R` the derived fibre `K ⊗^L_R κ(p)` has cohomology only in degree `n`, then `K` has
cohomology only in degree `n`, and `H^n(K)` is flat over `R`. -/
theorem isZero_homology_and_flat_of_isZero_homology_derivedFibre (φ : R →+* A) (hfl : φ.Flat)
    (hfp : φ.FinitePresentation) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (n : ℤ)
    (hfib : ∀ (p : PrimeSpectrum R) (i : ℤ), i ≠ n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} p.asIdeal.ResidueField) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R p.asIdeal.ResidueField)).functor.obj
          ((ModuleCat.restrictScalars φ).mapDerivedCategory.obj K)))) :
    (∀ i, i ≠ n → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ∧
      Module.Flat R ((ModuleCat.restrictScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K)) := by
  obtain ⟨P, ⟨b, hb⟩, hP, ⟨e⟩⟩ :=
    StacksDraft.PseudoCoherence.finiteProjectiveRepresentative_of_pseudoCoherent hK
  -- the homology of `K` is that of `P`
  have hH : ∀ i, (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K ≅ P.homology i :=
    fun i => (DerivedCategory.homologyFunctor _ i).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P
  -- the fibres of `P` are exact away from `n`
  have hPfib : ∀ (p : Ideal R) [p.IsPrime] (i : ℤ), i ≠ n →
      (((ModuleCat.extendScalars (algebraMap R p.ResidueField)).mapHomologicalComplex _).obj
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj P)).ExactAt i := by
    intro p _ i hi
    let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R p.ResidueField)
    let P' : CochainComplex (ModuleCat.{u} R) ℤ :=
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj P
    have : P'.IsStrictlyLE b := by
      rw [CochainComplex.isStrictlyLE_iff] at hb ⊢
      intro j hj
      exact (ModuleCat.restrictScalars φ).map_isZero (hb j hj)
    let := φ.toAlgebra
    have : Module.Flat R A := hfl
    have : ∀ j, Module.Flat R (P'.X j) := fun j => by
      have := (hP j).2
      let : Module R (P.X j) := Module.compHom _ φ
      have : IsScalarTower R A (P.X j) := ⟨fun r a m => mul_smul (φ r) a m⟩
      exact Module.Flat.trans R A (P.X j)
    have : IsIso (T.comparison.app P') :=
      T.comparison_isIso_of_kFlat P' (CochainComplex.KFlat.kFlat_of_flat P' b)
    have h0 := hfib ⟨p, inferInstance⟩ i hi
    have e₁ : (ModuleCat.restrictScalars φ).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P' :=
      (ModuleCat.restrictScalars φ).mapDerivedCategory.mapIso e.symm ≪≫
        (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.app P
    have e₂ := (DerivedCategory.homologyFunctor _ i).mapIso
      (T.functor.mapIso e₁ ≪≫ asIso (T.comparison.app P'))
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (h0.of_iso e₂.symm).of_iso
      ((DerivedCategory.homologyFunctorFactors _ i).app _).symm
  obtain ⟨hex, hflat⟩ := exactAt_and_flat_homology_of_exactAt_fibres φ hfl hfp P hP n hPfib
  refine ⟨fun i hi => ?_, ?_⟩
  · exact ((P.exactAt_iff_isZero_homology i).1 (hex i hi)).of_iso (hH i)
  · exact (Module.Flat.equiv_iff ((ModuleCat.restrictScalars φ).mapIso (hH n)).toLinearEquiv).2
      hflat

end Derived

end PseudoCoherence
