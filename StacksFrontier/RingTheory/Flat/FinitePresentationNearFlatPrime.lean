module

public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.FlatLocusFiniteModule
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.Flat.OpenFlatLocusNoetherian
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Basic
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatFibre
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatTensorProduct

/-!
# Finite presentation near a prime of relative flatness

Let `R → S` be a ring map of finite presentation, let `M` be a *finite* `S`-module and let `q` be
a prime of `S` at which `M` is flat over `R`. If `R` has only finitely many weakly associated
primes then `M` becomes finitely presented, and flat over `R`, on a basic open around `q`. That
statement is `Stacks.Flatness.ExistsAwayFlatFinitePresentationOfFlatAtPrime`, the affine content
of Stacks 05IK, and this file proves it.

One input is isolated as a named `Prop`-valued hypothesis, in the same style as the conclusion
itself, because it is the one result of the source that the argument does not already have:
`Stacks.Flatness.FinitePresentationLocalizedModuleAtPrimeOfFlat`, the algebra form of
Stacks 05I7 — the localization of a finite module at a prime of relative flatness is finitely
presented over the localized ring.

The other input of the source, Stacks 05IJ combined with Stacks 05AF, is a *theorem* here:
`Stacks.Flatness.finiteWeaklyAssociatedPrimesOfFlatFinitePresentation`. It is stated at finite
presentation rather than finite type, for the reason set out on the `def` below, and it is
discharged inside the main proof.

## Main definitions

* `Stacks.Flatness.FinitePresentationLocalizedModuleAtPrimeOfFlat`, the algebra form of
  Stacks 05I7.
* `Stacks.Flatness.FiniteWeaklyAssociatedPrimesOfFlatFinitePresentation`, the algebra form of
  Stacks 05IJ together with Stacks 05AF.

## Main results

* `Stacks.Flatness.existsAwayFlatFinitePresentationOfFlatAtPrime_of_finitePresentation_atPrime`
  proves `Stacks.Flatness.ExistsAwayFlatFinitePresentationOfFlatAtPrime` from that one
  hypothesis and results in the library.
* `Stacks.Flatness.finiteWeaklyAssociatedPrimesOfFlatFinitePresentation` discharges the
  Stacks 05IJ/05AF input outright.

## Implementation notes

The proof is the one in the source. Let `q` be a prime with `M_q` flat over `R`. By Stacks 05I7
the localization `M_q` is finitely presented over `S_q`, so Stacks 05GJ
(`Module.exists_finite_isLocalizedModule_comp_atPrime`) produces a finitely presented `S`-module
`M'` and a map `φ : M' → M` inducing an isomorphism `M'_q ≅ M_q`. In particular `M'` is flat
over `R` at `q`, so by Stacks 00RC (`Module.isOpen_setOf_flat_localizedModule_atPrime`) there is
`g₁ ∉ q` with `D(g₁)` inside the relative flat locus of `M'`.

Since `M` is finite and `φ_q` is onto, finitely many denominators clear at once and there is
`g₃ ∉ q` with `g₃ · M ⊆ im φ`; this is the algebraic form of the shrinking that the source takes
from Stacks 01B8 (Nakayama, Stacks 00DV, is the alternative the source offers).

By Stacks 05IJ and Stacks 05AF the weakly associated primes of `M'_{g₁}` are finitely many, so by
Stacks 05C9 (`weakAss_inter_image_eq_weakAss_localizedModule`) those of `M'` meeting `D(g₁)` are
finitely many too. For each of them not contained in `q` pick an element of it outside `q`; the
product `g₂` of those elements is outside `q`, and `D(g₂)` misses every such prime. This is the
prime avoidance of Stacks 00DS, in the form in which only a product of witnesses is needed.

Put `g = g₁g₂g₃` and let `K = ker φ`. By Stacks 0548
(`Module.weaklyAssociatedPrimes_subset_of_injective`) one has `WeakAss(K) ⊆ WeakAss(M')`, while
every prime weakly associated to `K` and inside `q` would have an element of `q.primeCompl` in
its annihilator ideal, because `φ_q` is injective. Hence no prime weakly associated to `K` meets
`D(g)`, so `K_g = 0` by Stacks 0588 (`weakAss_empty_iff_zero`), and `M_g` is the localization of
`M'` at the powers of `g`. Finite presentation and flatness over `R` of `M_g` then transport
from `M'`.

## References

* [Stacks Project, Tag 05IK](https://stacks.math.columbia.edu/tag/05IK)
* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 05IJ](https://stacks.math.columbia.edu/tag/05IJ)
-/

@[expose] public section

universe u v w

namespace Stacks.Flatness

/-- **The algebra form of Stacks 05I7.** For every ring map `R → S` of finite presentation, every
finite `S`-module `M` and every prime `q` of `S` at which `M` is flat over `R`, the localization
`M_q` is a finitely presented `S_q`-module.

This is Stacks 05I7 for the sheaf associated to a module: the stalk of a finite type
quasi-coherent module at a point of relative flatness of a morphism locally of finite
presentation is a module of finite presentation over the local ring there. -/
def FinitePresentationLocalizedModuleAtPrimeOfFlat : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
      [Algebra.FinitePresentation R S] (M : Type w) [AddCommGroup M] [Module S M] [Module R M]
      [IsScalarTower R S M] [Module.Finite S M] (q : PrimeSpectrum S),
    Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) →
      Module.FinitePresentation (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal M)

/-- **The algebra form of Stacks 05IJ together with Stacks 05AF.** For every ring map `R → S` of
finite presentation and every finitely presented `S`-module `N` which is flat over `R`, if `R`
has only finitely many weakly associated primes then so does `N`.

Stacks 05IJ computes `WeakAss_X(F ⊗ f^*G)` as the union, over the weakly associated points `s` of
`G`, of the associated points of `F_s` on the fibre `X_s`; Stacks 05AF says each of those unions
is finite, the fibre being of finite type over a field. Taking `G = O_S`, so that
`F ⊗ f^*G = F`, and using that `WeakAss(S)` is finite, the union is finite — which is exactly how
the proof of Stacks 05IK uses the two lemmas, and all that it uses them for.

## Why finite presentation and not finite type

Stacks 05IJ is stated for a morphism locally of finite type, that is, with
`Algebra.FiniteType R S` and `Module.Finite S N`. **At those
hypotheses this `def` is not provable here**, and the obstruction is not a gap in the formalization.
The fibre clause it rests on,
`isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct`,
needs `Module.FinitePresentation S N`, because its engine is Stacks 05DF, whose proof is a limit
argument. And the missing hypothesis cannot be manufactured: this library contains the
counterexample, `Module.not_forall_finitePresentation_of_finite_of_flat` in
`StacksFrontier/RingTheory/Flat/FiniteFlatNotFinitePresentation.lean`, showing that a finite module
flat over the base need not be finitely presented. The source bridges the gap in the second
paragraph of the proof of Stacks 05IH, through Proposition 05I5 and étale descent of weakly
associated primes — a genuinely separate piece of work.

Nothing is weakened by stating it this way, because this `def` is an interior abstraction rather
than a statement of 05IJ: its only consumer,
`existsAwayFlatFinitePresentationOfFlatAtPrime_of_finitePresentation_atPrime`, applies it to
`Localization.Away g₁` over `R` and to `LocalizedModule.Away g₁ M'`, and already establishes
`Algebra.FinitePresentation R (Localization.Away g₁)` and
`Module.FinitePresentation S M'` before doing so. The statement of
`ExistsAwayFlatFinitePresentationOfFlatAtPrime` is unchanged, and so is every tag downstream
of it. -/
def FiniteWeaklyAssociatedPrimesOfFlatFinitePresentation : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
      [Algebra.FinitePresentation R S]
      (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
      [Module.FinitePresentation S N] [Module.Flat R N],
    (weaklyAssociatedPrimes R R).Finite → (weaklyAssociatedPrimes S N).Finite

/-- **Stacks 05IJ and Stacks 05AF, in the form Stacks 05IK consumes.** The abstraction above is a
theorem, proved in
`StacksFrontier/RingTheory/Ideal/WeaklyAssociatedPrime/FlatFibre.lean`. -/
theorem finiteWeaklyAssociatedPrimesOfFlatFinitePresentation :
    FiniteWeaklyAssociatedPrimesOfFlatFinitePresentation.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hR =>
    Stacks.WeaklyAssociatedPrimes.finite_weaklyAssociatedPrimes_of_flat_of_finitePresentation hR

/-- **The affine content of Stacks 05IK.** Let `R → S` be of finite presentation, let `M` be a
finite `S`-module and let `q` be a prime of `S` at which `M` is flat over `R`. If `R` has only
finitely many weakly associated primes then there is `g ∉ q` such that `M_g` is a finitely
presented `S_g`-module and is flat over `R`.

The one hypothesis is the algebra form of Stacks 05I7; the algebra form of Stacks 05IJ together
with Stacks 05AF is a theorem, `finiteWeaklyAssociatedPrimesOfFlatFinitePresentation`, and is
discharged internally. Everything else the proof uses is proved. See the implementation notes of
this file for the argument. -/
theorem existsAwayFlatFinitePresentationOfFlatAtPrime_of_finitePresentation_atPrime
    (h7 : FinitePresentationLocalizedModuleAtPrimeOfFlat.{u, v, w}) :
    ExistsAwayFlatFinitePresentationOfFlatAtPrime.{u, v, w} := by
  classical
  have hJ : FiniteWeaklyAssociatedPrimesOfFlatFinitePresentation.{u, v, v} :=
    finiteWeaklyAssociatedPrimesOfFlatFinitePresentation
  intro R _ S _ _ _ M _ _ _ _ _ hR q hq
  have hqp : q.asIdeal.IsPrime := q.isPrime
  have := hq
  -- Stacks 05I7: the stalk of `M` at `q` is finitely presented
  have hfpq : Module.FinitePresentation (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal M) := h7 R S M q hq
  -- Stacks 05GJ: a finitely presented approximation `φ : M' → M` of `M` near `q`
  obtain ⟨M', iAdd, iMod, φ, hM'fin, hloc, hM'fp⟩ :=
    Module.exists_finite_isLocalizedModule_comp_atPrime (R := S) q.asIdeal
      (Localization.AtPrime q.asIdeal) (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
  let : AddCommGroup M' := iAdd
  let : Module S M' := iMod
  let : Module R M' := Module.compHom M' (algebraMap R S)
  have : IsScalarTower R S M' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite S M' := hM'fin
  have : IsLocalizedModule q.asIdeal.primeCompl
      ((LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) ∘ₗ φ) := hloc
  have : Module.FinitePresentation S M' := hM'fp hfpq
  -- `M'` is flat over `R` at `q`, because `φ_q` is an isomorphism
  have : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M') :=
    Module.Flat.of_linearEquiv ((IsLocalizedModule.linearEquiv q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M')
      ((LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) ∘ₗ φ)).restrictScalars R)
  -- Stacks 00RC: a basic open around `q` inside the relative flat locus of `M'`
  have hqmem : q ∈ {q' : PrimeSpectrum S |
      Module.Flat R (LocalizedModule.AtPrime q'.asIdeal M')} := ‹_›
  rw [PrimeSpectrum.eq_biUnion_of_isOpen
    (Module.isOpen_setOf_flat_localizedModule_atPrime (R := R) (S := S) (M := M'))] at hqmem
  obtain ⟨g₁, hg₁sub, hg₁mem⟩ := Set.mem_iUnion₂.mp hqmem
  have hg₁q : g₁ ∉ q.asIdeal := (PrimeSpectrum.mem_basicOpen g₁ q).mp hg₁mem
  have : Module.Flat R (LocalizedModule.Away g₁ M') :=
    OpenFlatLocus.flat_localizedModule_away_of_forall_flat_atPrime g₁ fun _ hq' => hg₁sub hq'
  -- Stacks 05IJ and Stacks 05AF: finitely many weakly associated primes on `D(g₁)`
  have : Algebra.FinitePresentation S (Localization.Away g₁) :=
    IsLocalization.Away.finitePresentation g₁
  have : Algebra.FinitePresentation R (Localization.Away g₁) :=
    Algebra.FinitePresentation.trans R S (Localization.Away g₁)
  have hFfin : {p ∈ weakAss S M' |
      p ∈ Set.range (localizationComap (Submonoid.powers g₁))}.Finite := by
    rw [weakAss_inter_image_eq_weakAss_localizedModule (Submonoid.powers g₁),
      weakAss_localizedModule_eq_image (Submonoid.powers g₁)]
    exact Set.Finite.image _ (Stacks.WeaklyAssociatedPrimes.finite_weakAss_iff.mpr
      (hJ R (Localization.Away g₁) (LocalizedModule.Away g₁ M') hR))
  -- Stacks 00DS: a single element of `q.primeCompl` avoiding all the bad primes
  have hBfin : {p ∈ {p ∈ weakAss S M' |
      p ∈ Set.range (localizationComap (Submonoid.powers g₁))} |
      ¬ p.asIdeal ≤ q.asIdeal}.Finite := hFfin.subset fun _ hp => hp.1
  choose! x hx1 hx2 using fun (p : PrimeSpectrum S) (hp : p ∈ {p ∈ {p ∈ weakAss S M' |
      p ∈ Set.range (localizationComap (Submonoid.powers g₁))} | ¬ p.asIdeal ≤ q.asIdeal}) =>
    IsConcreteLE.not_le_iff_exists.mp hp.2
  set g₂ : S := ∏ p ∈ hBfin.toFinset, x p with hg₂def
  have hg₂q : g₂ ∉ q.asIdeal :=
    q.asIdeal.primeCompl.prod_mem fun p hp => hx2 p (hBfin.mem_toFinset.mp hp)
  -- `M` is finite, so finitely many denominators clear the surjectivity of `φ` at once
  obtain ⟨T, hT⟩ : (⊤ : Submodule S M).FG := Module.Finite.fg_top
  have hwit : ∀ m : M, ∃ s : q.asIdeal.primeCompl, (s : S) • m ∈ LinearMap.range φ := by
    intro m
    obtain ⟨⟨m', s⟩, hms⟩ := IsLocalizedModule.surj q.asIdeal.primeCompl
      ((LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) ∘ₗ φ)
      ((LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) m)
    have hms' : (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) ((s : S) • m)
        = (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) (φ m') := by
      rw [map_smul]; exact hms
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq
      (S := q.asIdeal.primeCompl)
      (f := LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) hms'
    have ht' : (t : S) • ((s : S) • m) = (t : S) • φ m' := by
      simpa only [Submonoid.smul_def] using ht
    refine ⟨t * s, ⟨(t : S) • m', ?_⟩⟩
    rw [map_smul, ← ht', Submonoid.coe_mul, mul_smul]
  choose u hu using hwit
  set g₃ : S := ∏ m ∈ T, (u m : S) with hg₃def
  have hg₃q : g₃ ∉ q.asIdeal := q.asIdeal.primeCompl.prod_mem fun m _ => (u m).2
  have hg₃surj : ∀ m : M, g₃ • m ∈ LinearMap.range φ := by
    have hsub : (T : Set M) ⊆
        ((LinearMap.range φ).comap (LinearMap.lsmul S M g₃) : Submodule S M) := by
      intro m hm
      obtain ⟨c, hc⟩ : (u m : S) ∣ g₃ :=
        hg₃def ▸ Finset.dvd_prod_of_mem (fun m : M => (u m : S)) hm
      have hmem : g₃ • m ∈ LinearMap.range φ := by
        rw [hc, mul_comm, mul_smul]
        exact Submodule.smul_mem _ c (hu m)
      exact hmem
    have hle : (⊤ : Submodule S M) ≤ (LinearMap.range φ).comap (LinearMap.lsmul S M g₃) := by
      rw [← hT]; exact Submodule.span_le.mpr hsub
    exact fun m => hle Submodule.mem_top
  -- the element around which everything works
  set g : S := g₁ * g₂ * g₃ with hgdef
  have hg₁dvd : g₁ ∣ g := ⟨g₂ * g₃, by rw [hgdef, mul_assoc]⟩
  have hg₂dvd : g₂ ∣ g := ⟨g₁ * g₃, by rw [hgdef]; ring⟩
  have hgq : g ∉ q.asIdeal :=
    q.asIdeal.primeCompl.mul_mem (q.asIdeal.primeCompl.mul_mem hg₁q hg₂q) hg₃q
  -- the kernel of `φ` dies on `D(g)`: no prime weakly associated to it meets `D(g)`
  have hkerq : ∀ k : M', φ k = 0 → ∃ s : q.asIdeal.primeCompl, (s : S) • k = 0 := fun k hk =>
    (IsLocalizedModule.eq_zero_iff q.asIdeal.primeCompl
      ((LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) ∘ₗ φ)).mp (by simp [hk])
  have hKweak : ∀ p : PrimeSpectrum S,
      p ∈ weakAss S (LinearMap.ker φ) → g ∉ p.asIdeal → False := by
    intro p hp hgp
    obtain ⟨k, hk⟩ := hp
    have hpM' : p ∈ weakAss S M' :=
      Module.weaklyAssociatedPrimes_subset_of_injective
        (f := (LinearMap.ker φ).subtype) (LinearMap.ker φ).injective_subtype ⟨k, hk⟩
    have hg₁p : g₁ ∉ p.asIdeal := fun h => hgp (p.asIdeal.mem_of_dvd hg₁dvd h)
    have hrange : p ∈ Set.range (localizationComap (Submonoid.powers g₁)) := by
      rw [PrimeSpectrum.localization_comap_range (Localization (Submonoid.powers g₁))
        (Submonoid.powers g₁)]
      refine Set.disjoint_left.mpr ?_
      rintro a ⟨n, rfl⟩ hap
      exact hg₁p (p.isPrime.mem_of_pow_mem n hap)
    by_cases hple : p.asIdeal ≤ q.asIdeal
    · obtain ⟨s, hs⟩ := hkerq (k : M') k.2
      have hsann : (s : S) ∈ (Submodule.span S {k}).annihilator :=
        (Submodule.mem_annihilator_span_singleton k (s : S)).mpr (Subtype.ext hs)
      exact s.2 (hple (hk.left.right hsann))
    · have hpB : p ∈ {p ∈ {p ∈ weakAss S M' |
          p ∈ Set.range (localizationComap (Submonoid.powers g₁))} |
          ¬ p.asIdeal ≤ q.asIdeal} := ⟨⟨hpM', hrange⟩, hple⟩
      exact hgp (p.asIdeal.mem_of_dvd hg₂dvd (p.asIdeal.mem_of_dvd
        (hg₂def ▸ Finset.dvd_prod_of_mem x (hBfin.mem_toFinset.mpr hpB)) (hx1 p hpB)))
  -- Stacks 0588: a module with no weakly associated primes is zero
  have hKzero : ∀ k : M', φ k = 0 → ∃ i : ℕ, g ^ i • k = 0 := by
    intro k hk
    have hNzero : ∀ y : LocalizedModule.Away g ↥(LinearMap.ker φ), y = 0 := by
      rw [weakAss_empty_iff_zero (R := S)]
      refine Set.eq_empty_of_forall_notMem fun I hI => ?_
      have hIp : I.IsPrime := hI.isPrime S _
      have hmemw : (⟨I, hIp⟩ : PrimeSpectrum S) ∈
          weakAss S (LocalizedModule.Away g ↥(LinearMap.ker φ)) := hI
      rw [← weakAss_inter_image_eq_weakAss_localizedModule (Submonoid.powers g)] at hmemw
      obtain ⟨hw, hr⟩ := hmemw
      rw [PrimeSpectrum.localization_comap_range (Localization (Submonoid.powers g))
        (Submonoid.powers g)] at hr
      exact hKweak ⟨I, hIp⟩ hw fun hgI =>
        Set.disjoint_left.mp hr (Submonoid.mem_powers g) hgI
    obtain ⟨⟨_, i, rfl⟩, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) ↥(LinearMap.ker φ))).mp
        (hNzero ((LocalizedModule.mkLinearMap (Submonoid.powers g) ↥(LinearMap.ker φ))
          ⟨k, hk⟩))
    exact ⟨i, congrArg Subtype.val hs⟩
  -- `M_g` is the localization of `M'` at the powers of `g`
  have hψ : IsLocalizedModule (Submonoid.powers g)
      ((LocalizedModule.mkLinearMap (Submonoid.powers g) M) ∘ₗ φ) := by
    refine IsLocalizedModule.Away.mk_of_addCommGroup (r := g) ?_ ?_ ?_
    · exact IsLocalizedModule.Away.isUnit_algebraMap
        (LocalizedModule.mkLinearMap (Submonoid.powers g) M) g
    · intro y
      obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj
        (LocalizedModule.mkLinearMap (Submonoid.powers g) M) g y
      obtain ⟨m', hm'⟩ := hg₃surj m
      refine ⟨n + 1, (g₁ * g₂) • m', ?_⟩
      calc g ^ (n + 1) • y = g • (g ^ n • y) := by rw [pow_succ, mul_comm, mul_smul]
        _ = g • (LocalizedModule.mkLinearMap (Submonoid.powers g) M) m := by rw [hm]
        _ = (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (g • m) :=
            (map_smul _ _ _).symm
        _ = ((LocalizedModule.mkLinearMap (Submonoid.powers g) M) ∘ₗ φ) ((g₁ * g₂) • m') := by
            rw [LinearMap.comp_apply, map_smul φ, hm', hgdef, mul_smul]
    · intro k hk
      obtain ⟨⟨_, j, rfl⟩, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g)
        (LocalizedModule.mkLinearMap (Submonoid.powers g) M)).mp hk
      obtain ⟨i, hi⟩ := hKzero (g ^ j • k) (by rw [map_smul]; exact hs)
      exact ⟨i + j, by rw [pow_add, mul_smul]; exact hi⟩
  refine ⟨g, hgq, ?_, ?_⟩
  · exact FinitePresentation.of_isBaseChange
      ((LocalizedModule.mkLinearMap (Submonoid.powers g) M) ∘ₗ φ)
      ((isLocalizedModule_iff_isBaseChange (Submonoid.powers g) (Localization.Away g) _).mp hψ)
  · have : Module.Flat R (LocalizedModule.Away g M') :=
      OpenFlatLocus.flat_localizedModule_away_of_forall_flat_atPrime g fun q' hq' =>
        hg₁sub ((PrimeSpectrum.mem_basicOpen g₁ q').mpr fun h =>
          (PrimeSpectrum.mem_basicOpen g q').mp hq' (q'.asIdeal.mem_of_dvd hg₁dvd h))
    exact Module.Flat.of_linearEquiv ((IsLocalizedModule.linearEquiv (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M')
      ((LocalizedModule.mkLinearMap (Submonoid.powers g) M) ∘ₗ φ)).restrictScalars R).symm

end Stacks.Flatness

end
