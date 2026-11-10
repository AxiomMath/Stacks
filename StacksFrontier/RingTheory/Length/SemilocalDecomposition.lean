module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import StacksCore.Tactic.StacksAttribute

/-!
# Length of an Artinian module over a semilocal ring, through its localizations

Let `B` be a commutative ring with finitely many maximal ideals and let `M` be an Artinian
`B`-module. Then `M` is the finite product of its localizations at the maximal ideals of `B`,
because the localization of `M_𝔮` at a second maximal ideal `𝔮'` vanishes.

If moreover `B` is a finite algebra over a local ring `A`, the `A`-length of a module over the
localization `B_𝔮` is the residue degree `[κ(𝔮) : κ(𝔪)]` times its `B_𝔮`-length, so the two
statements combine into

`length_A(M) = ∑_𝔮 [κ(𝔮) : κ(𝔪)] length_{B_𝔮}(M_𝔮)`,

which is the length half of Stacks 02M0 and the computation the norm compatibility of tame
symbols (Stacks 0EAT) rests on.

## Main results

* `Stacks.Length.subsingleton_localizedModule_localizedModule` — the localization at a maximal
  ideal of the localization of an Artinian module at a different maximal ideal vanishes.
* `Stacks.Length.nonempty_linearEquiv_pi_localizedModule` — an Artinian module over a semilocal
  ring is the product of its localizations.
* `Stacks.Length.isLocalHom_algebraMap_localization`, `Stacks.Length.finite_maximalSpectrum` —
  a finite algebra over a local ring is semilocal, and local at each of its maximal ideals.
* `Stacks.Length.length_restrictScalars_eq_finrank_mul` — the residue-degree change of rings
  for length.
* `Stacks.Length.length_eq_sum_length_localizedModule`,
  `Stacks.Length.length_eq_sum_finrank_mul_length_localizedModule` — the length formulas.

## Implementation notes

**Stacks 02M0 is already in the library, and is not reused here.**
`StacksFrontier.RingTheory.Length.SemiLocal` proves
`length_eq_sum_residue_degree_mul_localized_length`, carrying `@[stacks 02M0]`, which is this
file's `Stacks.Length.length_eq_sum_finrank_mul_length_localizedModule` at the same generality.
Two spellings separate them, and both bear on the consumer. It indexes the maximal ideals of `B`
by a family `Fin n → Ideal B` with hypotheses saying that family is exactly the maximal ideals,
where this file indexes by `MaximalSpectrum B`; that part is a reindexing. The one that is not is
the base field: its residue degree is `Module.finrank (IsLocalRing.maximalIdeal A).ResidueField`,
the residue field of the *localization* `A_𝔪`, with the `Algebra` instance its own
`residueFieldAlgebra`, where the tame symbol of Stacks 0EAT takes the norm
`Algebra.norm (IsLocalRing.ResidueField A)` over the residue field of `A` itself, with Mathlib's
instance from `[IsLocalHom (algebraMap A B_𝔮)]`. Those two base fields are isomorphic and not
equal, and the two `Algebra` structures on `κ(𝔮)` are distinct terms, so transporting that
statement to the one the symbol needs is a two-instance bridge rather than a rewrite.

`StacksFrontier.RingTheory.OrderOfVanishing.Norm` proves these three statements for `M = B ⧸ bB`
with `A` and `B` integral domains, `A` of Krull dimension at most one and `b ≠ 0`, which is the
generality Stacks 02MJ needs. None of the proofs uses those hypotheses: the first two use only
that `M` is Artinian over `B`, and the third only that `B` is finite over the local ring `A`.
Stacks 0EAT is stated for a one-dimensional Noetherian local ring that need not be a domain, so
the statements are reproved here at the generality their proofs have. The off-diagonal vanishing
is obtained from `IsArtinian.exists_pow_succ_smul_dvd` applied to a cyclic submodule rather than
from a descending chain of submodules in the order dual, which is what the version in
`StacksFrontier/RingTheory/OrderOfVanishing/Norm.lean` needs a
`backward.isDefEq.respectTransparency`
escape for. The residue degree is spelled `Module.finrank (ResidueField A) (ResidueField B_𝔮)`
rather than `Ideal.inertiaDeg'`, which is deprecated and whose uses in that file are behind a
`linter.deprecated` option; the two agree, and the `finrank` spelling is the one the norm of an
element of `κ(𝔪)` is computed with.

## References

* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
* [Stacks Project, Tag 02MJ](https://stacks.math.columbia.edu/tag/02MJ)
-/

@[expose] public section

universe u v w

namespace Stacks.Length

section OffDiagonal

variable {B : Type v} [CommRing B] (M : Type w) [AddCommGroup M] [Module B M] [IsArtinian B M]

/-- **An Artinian module localized at one maximal ideal dies at any other.** An element of
`M_𝔮` is `m / u`; choosing `s ∈ 𝔮` with `s ∉ 𝔮'` and stabilizing the descending chain of
cyclic submodules generated by `s ^ n • m` produces `β` with `s ^ n • m = β s ^ (n + 1) • m`,
so `1 - β s`, which is outside `𝔮`, annihilates `s ^ n • m`; hence `s ^ n` kills `m / u` in
`M_𝔮`, and `s ^ n` is outside `𝔮'`. -/
theorem subsingleton_localizedModule_localizedModule
    {v w : MaximalSpectrum B} (hvw : v ≠ w) :
    Subsingleton (LocalizedModule w.asIdeal.primeCompl
      (LocalizedModule v.asIdeal.primeCompl M)) := by
  classical
  -- choose `s ∈ 𝔮` with `s ∉ 𝔮'`: distinct maximal ideals are incomparable
  obtain ⟨s, hsv, hsw⟩ : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := by
    have hne : v.asIdeal ≠ w.asIdeal := fun h => hvw (MaximalSpectrum.ext h)
    have hnle : ¬ v.asIdeal ≤ w.asIdeal := fun hle =>
      hne (v.isMaximal.eq_of_le w.isMaximal.ne_top hle)
    rw [IsConcreteLE.not_le_iff_exists] at hnle
    obtain ⟨s, hsv, hsw⟩ := hnle
    exact ⟨s, hsv, hsw⟩
  rw [LocalizedModule.subsingleton_iff]
  intro n
  induction n using LocalizedModule.induction_on with
  | _ c u =>
    -- Artinian stabilization inside the cyclic submodule generated by `c`
    obtain ⟨k, β, hβ⟩ : ∃ (k : ℕ) (β : B), s ^ k • c = β • (s ^ (k + 1) • c) := by
      obtain ⟨k, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (M := (Submodule.span B {c}))
        s ⟨c, Submodule.mem_span_singleton_self c⟩
      obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp y.2
      refine ⟨k, β, ?_⟩
      have hy' : s ^ (k + 1) • (y : M) = s ^ k • c := congrArg Subtype.val hy
      rw [← hy', ← hβ, smul_comm]
    refine ⟨s ^ k, fun hpow => hsw (w.isMaximal.isPrime.mem_of_pow_mem k hpow), ?_⟩
    rw [LocalizedModule.smul'_mk]
    have hkill : (1 - β * s) • (s ^ k • c) = 0 := by
      rw [sub_smul, one_smul, mul_smul, show s • (s ^ k • c) = s ^ (k + 1) • c by
        rw [← mul_smul, ← pow_succ'], ← hβ, sub_self]
    have hv : (1 - β * s) ∈ v.asIdeal.primeCompl := by
      intro hmem
      have hone : (1 : B) ∈ v.asIdeal := by
        simpa using Ideal.add_mem _ hmem (Ideal.mul_mem_left v.asIdeal β hsv)
      exact v.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)
    rw [show (0 : LocalizedModule v.asIdeal.primeCompl M) =
      LocalizedModule.mk 0 u from (LocalizedModule.zero_mk u).symm, LocalizedModule.mk_eq]
    refine ⟨⟨1 - β * s, hv⟩, ?_⟩
    simp only [Submonoid.mk_smul, smul_zero]
    rw [smul_comm, hkill, smul_zero]

variable [Finite (MaximalSpectrum B)]

/-- **An Artinian module over a semilocal ring is the product of its localizations.** The
canonical map to the product is a localization at each maximal ideal `𝔮'`: the factor at `𝔮'`
is `M_{𝔮'}` localized again at `𝔮'`, which is `M_{𝔮'}`, and every other factor vanishes by
`Stacks.Length.subsingleton_localizedModule_localizedModule`. -/
@[sga "3 VIIB 0.1.1" "partial"]
theorem nonempty_linearEquiv_pi_localizedModule :
    Nonempty (M ≃ₗ[B] (∀ v : MaximalSpectrum B, LocalizedModule v.asIdeal.primeCompl M)) := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum B)
  refine ⟨LinearEquiv.ofBijective
    (LinearMap.pi (fun v => LocalizedModule.mkLinearMap v.asIdeal.primeCompl M)) ?_⟩
  apply bijective_of_isLocalized_maximal (R := B)
    (fun P _ => LocalizedModule P.primeCompl M)
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M)
    (fun P _ => ∀ v : MaximalSpectrum B,
      LocalizedModule P.primeCompl (LocalizedModule v.asIdeal.primeCompl M))
    (fun P _ => LinearMap.pi (fun v =>
      (LocalizedModule.mkLinearMap P.primeCompl _).comp (LinearMap.proj v)))
    _
  intro P hP
  set f := LocalizedModule.mkLinearMap P.primeCompl M
  set g := LinearMap.pi (fun v : MaximalSpectrum B =>
    (LocalizedModule.mkLinearMap P.primeCompl
      (LocalizedModule v.asIdeal.primeCompl M)).comp (LinearMap.proj v))
  set F := LinearMap.pi (fun v : MaximalSpectrum B =>
    LocalizedModule.mkLinearMap v.asIdeal.primeCompl M)
  -- the composite `M → ∏_𝔮 (M_𝔮)_P` is itself a localization of `M` at `P`
  have hcomp : IsLocalizedModule P.primeCompl (g.comp F) := by
    set w : MaximalSpectrum B := ⟨P, hP⟩ with hw
    let mkw := LocalizedModule.mkLinearMap w.asIdeal.primeCompl M
    let mkP := LocalizedModule.mkLinearMap P.primeCompl (LocalizedModule w.asIdeal.primeCompl M)
    have hmkP_bij : Function.Bijective mkP := by
      have hid : IsLocalizedModule P.primeCompl
          (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) :=
        isLocalizedModule_id P.primeCompl (LocalizedModule w.asIdeal.primeCompl M)
          (Localization P.primeCompl)
      have hcoe : ⇑mkP = ⇑(IsLocalizedModule.linearEquiv P.primeCompl
          (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) mkP) := by
        funext x
        have h2 := IsLocalizedModule.linearEquiv_apply P.primeCompl
          (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) mkP x
        simp only [LinearMap.id_coe, id_eq] at h2
        exact h2.symm
      rw [hcoe]
      exact (IsLocalizedModule.linearEquiv P.primeCompl
        (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) mkP).bijective
    let mkPe : LocalizedModule w.asIdeal.primeCompl M ≃ₗ[B]
        LocalizedModule P.primeCompl (LocalizedModule w.asIdeal.primeCompl M) :=
      LinearEquiv.ofBijective mkP hmkP_bij
    have hsub : ∀ v : MaximalSpectrum B, v ≠ w →
        Subsingleton (LocalizedModule P.primeCompl (LocalizedModule v.asIdeal.primeCompl M)) :=
      fun v hv => subsingleton_localizedModule_localizedModule M hv
    let pr : (∀ v : MaximalSpectrum B,
        LocalizedModule P.primeCompl (LocalizedModule v.asIdeal.primeCompl M))
      →ₗ[B] LocalizedModule P.primeCompl (LocalizedModule w.asIdeal.primeCompl M) :=
      LinearMap.proj w
    have hproj : Function.Bijective pr := by
      refine ⟨fun y₁ y₂ hyy => funext fun v => ?_, fun z => ⟨Pi.single w z, by simp [pr]⟩⟩
      by_cases hv : v = w
      · subst hv; exact hyy
      · have := hsub v hv; exact Subsingleton.elim _ _
    let pe := LinearEquiv.ofBijective pr hproj
    have hkey : g.comp F = pe.symm.toLinearMap.comp (mkPe.toLinearMap.comp mkw) := by
      refine LinearMap.ext fun m => ?_
      apply pe.injective
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      change (g (F m)) w = _
      simp only [g, F, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply]
      rfl
    rw [hkey]
    exact IsLocalizedModule.of_linearEquiv P.primeCompl (mkPe.toLinearMap.comp mkw) pe.symm
  have key : IsLocalizedModule.map P.primeCompl f g F =
      (IsLocalizedModule.iso P.primeCompl (g.comp F)).toLinearMap.comp
        (IsLocalizedModule.iso P.primeCompl f).symm.toLinearMap := by
    apply IsLocalizedModule.ext P.primeCompl f
      (fun x => IsLocalizedModule.map_units (g.comp F) x)
    rw [IsLocalizedModule.map_comp]
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [show (IsLocalizedModule.iso P.primeCompl f).symm (f m) = LocalizedModule.mk m 1 from ?_]
    · rw [IsLocalizedModule.iso_apply_mk]
      simp
    · rw [IsLocalizedModule.iso_symm_apply' P.primeCompl f (f m) m 1 (by simp)]
  rw [key, LinearMap.coe_comp]
  exact (IsLocalizedModule.iso P.primeCompl (g.comp F)).bijective.comp
    (IsLocalizedModule.iso P.primeCompl f).symm.bijective

end OffDiagonal

section ResidueDegree

open IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B]
  [Algebra A B] [Module.Finite A B]

/-- A maximal ideal of a finite algebra over a local ring contracts to the maximal ideal. -/
@[ega "0 10.3.1.2" "partial"]
theorem comap_asIdeal_eq_maximalIdeal (q : MaximalSpectrum B) :
    q.asIdeal.comap (algebraMap A B) = maximalIdeal A :=
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) q.asIdeal)

include A in
/-- A finite algebra over a local ring has finitely many maximal ideals: each of them lies over
the maximal ideal of the base, and there are finitely many such. -/
@[ega "0 10.3.1.2" "partial"]
theorem finite_maximalSpectrum : Finite (MaximalSpectrum B) := by
  have := (Algebra.QuasiFinite.finite_primesOver (S := B) (maximalIdeal A)).fintype
  exact Finite.of_injective
    (fun q : MaximalSpectrum B => (⟨q.asIdeal, q.isMaximal.isPrime,
      ⟨(comap_asIdeal_eq_maximalIdeal (A := A) q).symm⟩⟩ : (maximalIdeal A).primesOver B))
    (fun x y h => MaximalSpectrum.ext (congrArg Subtype.val h))

/-- **Localizing a finite algebra at a maximal ideal is local over the base.** The maximal ideal
of `B_𝔮` contracts to `𝔮` in `B` and `𝔮` contracts to `𝔪` in `A`. -/
theorem isLocalHom_algebraMap_localization (q : MaximalSpectrum B) :
    IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := by
  apply ((local_hom_TFAE (algebraMap A (Localization.AtPrime q.asIdeal))).out 5 1).mp
  rw [IsScalarTower.algebraMap_eq A B (Localization.AtPrime q.asIdeal), ← Ideal.comap_comap,
    show Ideal.comap (algebraMap B (Localization.AtPrime q.asIdeal))
      (maximalIdeal (Localization.AtPrime q.asIdeal)) = q.asIdeal from
      IsLocalization.AtPrime.under_maximalIdeal _ _, comap_asIdeal_eq_maximalIdeal q]

/-- **The residue degree at a maximal ideal of a finite algebra over a local ring**, that is
`[κ(𝔮) : κ(𝔪)]`. The residue field of `B_𝔮` is a finite extension of the residue field of `A`
because it is a quotient of `B`, which is finite over `A`. -/
theorem finite_residueField (A : Type u) [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B]
    [Algebra A B] [Module.Finite A B] (q : MaximalSpectrum B)
    [IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))] :
    Module.Finite (ResidueField A) (ResidueField (Localization.AtPrime q.asIdeal)) := by
  have : Module.Finite A (ResidueField (Localization.AtPrime q.asIdeal)) :=
    Module.Finite.trans B _
  exact Module.Finite.of_restrictScalars_finite A _ _

/-- The `A`-length of a module and its length over the quotient of `A` by the maximal ideal
agree, because the two submodule lattices coincide. -/
private theorem length_eq_length_residueField (N : Type w) [AddCommGroup N]
    [Module (ResidueField A) N] [Module A N] [IsScalarTower A (ResidueField A) N] :
    Module.length A N = Module.length (ResidueField A) N := by
  let toK : Submodule A N → Submodule (ResidueField A) N := fun P =>
    { carrier := P
      add_mem' := P.add_mem
      zero_mem' := P.zero_mem
      smul_mem' := fun k m hm => by
        obtain ⟨a, rfl⟩ := residue_surjective k
        rw [show residue A a = algebraMap A (ResidueField A) a from rfl, algebraMap_smul]
        exact P.smul_mem a hm }
  let e : Submodule (ResidueField A) N ≃o Submodule A N :=
    { toFun := fun P => P.restrictScalars A
      invFun := toK
      left_inv := fun P => by ext x; simp [toK]
      right_inv := fun P => by ext x; simp [toK]
      map_rel_iff' := Iff.rfl }
  unfold Module.length
  congr 1
  exact (Order.krullDim_eq_of_orderIso e).symm

/-- Length is additive along a submodule and its quotient, over any base ring acting compatibly. -/
private theorem length_eq_add_length_quotient {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (P : Submodule S M) : Module.length R M = Module.length R P + Module.length R (M ⧸ P) :=
  Module.length_eq_add_of_exact (P.subtype.restrictScalars R) (P.mkQ.restrictScalars R)
    P.subtype_injective P.mkQ_surjective (LinearMap.exact_subtype_mkQ P)

/-- **The residue-degree change of rings for length.** A module over the localization `B_𝔮` has
`A`-length `[κ(𝔮) : κ(𝔪)]` times its `B_𝔮`-length: a Jordan–Hölder induction on a
`B_𝔮`-composition series, whose simple factors are all `κ(𝔮)`, and `κ(𝔮)` has `A`-length equal
to its dimension over `κ(𝔪)` because `𝔪` annihilates it. -/
theorem length_restrictScalars_eq_finrank_mul (q : MaximalSpectrum B)
    [IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    (N : Type w) [AddCommGroup N]
    [Module (Localization.AtPrime q.asIdeal) N] [Module A N]
    [IsScalarTower A (Localization.AtPrime q.asIdeal) N]
    (hN : Module.length (Localization.AtPrime q.asIdeal) N ≠ ⊤) :
    Module.length A N =
      (Module.finrank (ResidueField A) (ResidueField (Localization.AtPrime q.asIdeal)) : ℕ∞) *
        Module.length (Localization.AtPrime q.asIdeal) N := by
  set Bq := Localization.AtPrime q.asIdeal
  -- the constant: the `A`-length of the residue field of `B_𝔮`
  have hconst : Module.length A (ResidueField Bq) =
      (Module.finrank (ResidueField A) (ResidueField Bq) : ℕ∞) := by
    have := finite_residueField A q
    rw [length_eq_length_residueField (A := A) (ResidueField Bq)]
    exact Module.length_eq_finrank (ResidueField A) (ResidueField Bq)
  have simpleA : ∀ (Q : Type w) [AddCommGroup Q] [Module Bq Q] [Module A Q]
      [IsScalarTower A Bq Q], IsSimpleModule Bq Q →
      Module.length A Q = Module.length A (ResidueField Bq) := by
    intro Q _ _ _ _ hQ
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hQ
    obtain rfl : I = maximalIdeal Bq := eq_maximalIdeal hI
    exact (e.restrictScalars A).length_eq
  have key : ∀ (M : Type w) [AddCommGroup M] [Module Bq M] (_ : IsFiniteLength Bq M)
      [Module A M] [IsScalarTower A Bq M],
      Module.length A M = Module.length A (ResidueField Bq) * Module.length Bq M := by
    intro M _ _ h
    induction h with
    | @of_subsingleton M _ _ _ =>
        intro _ _
        have h1 : Module.length A M = 0 := Module.length_eq_zero_iff.mpr ‹_›
        have h2 : Module.length Bq M = 0 := Module.length_eq_zero_iff.mpr ‹_›
        rw [h1, h2, mul_zero]
    | @of_simple_quotient M _ _ P hsimp _ ih =>
        intro _ _
        rw [length_eq_add_length_quotient (R := A) P, ih, simpleA (M ⧸ P) hsimp,
          length_eq_add_length_quotient (R := Bq) P,
          Module.length_eq_one_iff.mpr hsimp, mul_add, mul_one]
  rw [key N (Module.length_ne_top_iff.mp hN), hconst]

end ResidueDegree

section Formula

open IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B]
  [Algebra A B] [Module.Finite A B] [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]

omit [IsLocalRing A] [Module.Finite A B]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))] in
/-- **An Artinian module over a semilocal ring has length the sum of the lengths of its
localizations**, over any base ring acting compatibly. -/
theorem length_eq_sum_length_localizedModule
    (M : Type w) [AddCommGroup M] [Module B M] [IsArtinian B M] [Module A M]
    [IsScalarTower A B M] :
    Module.length A M =
      ∑ q : MaximalSpectrum B, Module.length A (LocalizedModule q.asIdeal.primeCompl M) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_pi_localizedModule (B := B) M
  rw [(e.restrictScalars A).length_eq, Module.length_pi_of_fintype]

/-- **Stacks 02M0, the length half.** For an Artinian module `M` over a finite algebra `B` over
a local ring `A`, the `A`-length of `M` is the sum over the maximal ideals of `B` of the residue
degree times the `B_𝔮`-length of `M_𝔮`: decompose `M` into its localizations and apply the
residue-degree change of rings to each factor. -/
theorem length_eq_sum_finrank_mul_length_localizedModule
    (M : Type w) [AddCommGroup M] [Module B M] [IsArtinian B M] [Module A M]
    [IsScalarTower A B M]
    (hfin : ∀ q : MaximalSpectrum B, Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) ≠ ⊤) :
    Module.length A M =
      ∑ q : MaximalSpectrum B,
        (Module.finrank (ResidueField A)
            (ResidueField (Localization.AtPrime q.asIdeal)) : ℕ∞) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M) := by
  rw [length_eq_sum_length_localizedModule (B := B) M]
  exact Finset.sum_congr rfl fun q _ =>
    length_restrictScalars_eq_finrank_mul q (LocalizedModule q.asIdeal.primeCompl M) (hfin q)

end Formula

end Stacks.Length

end
