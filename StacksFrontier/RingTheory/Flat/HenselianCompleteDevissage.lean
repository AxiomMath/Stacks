module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraExistence
public import StacksFrontier.RingTheory.Flat.CompleteDevissageSpecTransport
public import StacksFrontier.RingTheory.Flat.DevissagePointedLocalizeAway
public import StacksFrontier.RingTheory.Flat.ElementaryEtaleLocalizationHenselian

/-!
# The henselian collapse of Stacks Tag 05I1
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v w x

namespace Algebra

/-- away form of the retraction -/
theorem exists_isLocalization_away_of_etale_retraction {A : Type u} {R' : Type v} [CommRing A]
    [IsLocalRing A] [CommRing R'] [Algebra A R'] [Algebra.Etale A R'] {p' : Ideal R'}
    [p'.IsPrime] (σ : R' →ₐ[A] A) (hσ : (maximalIdeal A).comap σ.toRingHom = p') :
    ∃ a : R', a ∈ p'.primeCompl ∧ σ a = 1 ∧
      (∀ y : R', a * y = a * algebraMap A R' (σ y)) ∧
      letI : Algebra R' A := σ.toRingHom.toAlgebra
      IsLocalization (Submonoid.powers a) A := by
  let : Algebra R' A := σ.toRingHom.toAlgebra
  have hmap : ∀ r : R', algebraMap R' A r = σ r := fun _ ↦ rfl
  have hsurj : Function.Surjective σ := fun z ↦ ⟨algebraMap A R' z, σ.commutes z⟩
  obtain ⟨e₀, he₀, hker⟩ := Algebra.exists_isIdempotentElem_ker_of_etale_retraction σ
  have he₀ker : σ e₀ = 0 :=
    RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self e₀)
  have he₀p : e₀ ∈ p' := by
    rw [← hσ, Ideal.mem_comap]
    change σ e₀ ∈ maximalIdeal A
    rw [he₀ker]
    exact Submodule.zero_mem _
  have hone : (1 - e₀) ∈ p'.primeCompl := by
    intro h
    have h1 : (1 : R') ∈ p' := by simpa using Ideal.add_mem p' h he₀p
    exact ‹p'.IsPrime›.ne_top ((Ideal.eq_top_iff_one p').mpr h1)
  have hσa : σ (1 - e₀) = 1 := by rw [map_sub, map_one, he₀ker, sub_zero]
  have hidem : e₀ * e₀ = e₀ := he₀
  have hkill : ∀ y : R', (1 - e₀) * y = (1 - e₀) * algebraMap A R' (σ y) := by
    intro y
    have hsub : y - algebraMap A R' (σ y) ∈ RingHom.ker σ.toRingHom := by
      rw [RingHom.mem_ker]
      change σ (y - algebraMap A R' (σ y)) = 0
      rw [map_sub, σ.commutes]
      simp
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hker ▸ hsub)
    have hzero : (1 - e₀) * (y - algebraMap A R' (σ y)) = 0 := by
      rw [← hc]
      linear_combination (-c) * hidem
    linear_combination hzero
  refine ⟨1 - e₀, hone, hσa, hkill, ?_⟩
  refine (_root_.isLocalization_iff (M := Submonoid.powers (1 - e₀)) (S := A)).mpr
    ⟨fun y ↦ ?_, fun z ↦ ?_, fun {y z} h ↦ ⟨⟨1 - e₀, Submonoid.mem_powers _⟩, ?_⟩⟩
  · obtain ⟨n, hn⟩ := y.2
    rw [hmap, ← hn, map_pow, hσa, one_pow]
    exact isUnit_one
  · obtain ⟨r, hr⟩ := hsurj z
    exact ⟨⟨r, 1⟩, by rw [hmap, hmap, hr]; simp⟩
  · have hyz : algebraMap A R' (σ y) = algebraMap A R' (σ z) := by
      rw [← hmap, ← hmap, h]
    change (1 - e₀) * y = (1 - e₀) * z
    rw [hkill y, hkill z, hyz]

namespace ElementaryEtaleLocalization

/-- away form over a henselian base -/
theorem exists_isLocalization_away_of_henselian {A : Type u} {S : Type v} [CommRing A]
    [CommRing S] [Algebra A S] [IsLocalRing A] [HenselianLocalRing A] {p : Ideal A} [p.IsPrime]
    {q : Ideal S} [q.IsPrime] [q.LiesOver p] (hp : p = maximalIdeal A)
    (E : ElementaryEtaleLocalization.{u, v, w, x} A S p q) :
    ∃ (σ : E.R' →ₐ[A] A) (a : E.R'), a ∈ E.p'.primeCompl ∧ σ a = 1 ∧
      (∀ y : E.R', a * y = a * algebraMap A E.R' (σ y)) ∧
      letI : Algebra E.R' A := σ.toRingHom.toAlgebra
      IsLocalization (Submonoid.powers a) A := by
  subst hp
  obtain ⟨σ, hσ⟩ := E.exists_retraction_of_henselian
  exact ⟨σ, Algebra.exists_isLocalization_away_of_etale_retraction σ hσ⟩

end ElementaryEtaleLocalization

end Algebra

namespace Algebra

/-- the two localization carriers induce the same map -/
theorem algebraMap_algEquiv_away {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    {a : R} [Algebra R A] [IsLocalization (Submonoid.powers a) A] [Algebra R S]
    [Algebra (Localization.Away a) S] [Algebra A S] [IsScalarTower R (Localization.Away a) S]
    [IsScalarTower R A S] (z : Localization.Away a) :
    algebraMap A S (IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) A z)
      = algebraMap (Localization.Away a) S z := by
  have h1 : (algebraMap A S).comp
      (IsLocalization.algEquiv (Submonoid.powers a)
        (Localization.Away a) A).toAlgHom.toRingHom
      = algebraMap (Localization.Away a) S := by
    refine IsLocalization.ringHom_ext (Submonoid.powers a) ?_
    ext r
    simp [← IsScalarTower.algebraMap_apply]
  exact congrArg (fun f : Localization.Away a →+* S => f z) h1

/-- finite type transfers between localization carriers of the base -/
theorem finiteType_of_isLocalization_base {R A S : Type u} [CommRing R] [CommRing A]
    [CommRing S] {a : R} [Algebra R A] [IsLocalization (Submonoid.powers a) A] [Algebra R S]
    [Algebra (Localization.Away a) S] [Algebra A S] [IsScalarTower R (Localization.Away a) S]
    [IsScalarTower R A S] [Algebra.FiniteType (Localization.Away a) S] :
    Algebra.FiniteType A S := by
  let : Algebra (Localization.Away a) A :=
    (IsLocalization.algEquiv (Submonoid.powers a)
      (Localization.Away a) A).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower (Localization.Away a) A S :=
    IsScalarTower.of_algebraMap_eq fun z => (algebraMap_algEquiv_away z).symm
  exact Algebra.FiniteType.of_restrictScalars_finiteType (Localization.Away a) A S

end Algebra

namespace Stacks.Flatness

/-- powers of an element outside a prime miss the prime -/
theorem disjoint_powers_of_mem_primeCompl {R : Type u} [CommRing R] {p : Ideal R} [p.IsPrime]
    {a : R} (ha : a ∈ p.primeCompl) :
    Disjoint ((Submonoid.powers a : Submonoid R) : Set R) ((p : Ideal R) : Set R) := by
  rw [Set.disjoint_left]
  rintro y ⟨n, rfl⟩ hy
  exact ha (‹p.IsPrime›.mem_of_pow_mem n hy)

/-- the image of the powers misses the prime upstairs -/
theorem disjoint_algebraMapSubmonoid_powers {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] {Q : Ideal S} [Q.IsPrime] {a : R} (ha : a ∈ (Q.under R).primeCompl) :
    Disjoint ((Algebra.algebraMapSubmonoid S (Submonoid.powers a) : Submonoid S) : Set S)
      ((Q : Ideal S) : Set S) := by
  rw [Set.disjoint_left]
  rintro y ⟨z, hz, rfl⟩ hy
  exact Set.disjoint_left.mp (disjoint_powers_of_mem_primeCompl ha) hz
    (Ideal.mem_comap.mpr hy)

/-- the extension of a prime to a localization that misses it is prime -/
theorem isPrime_map_of_mem_primeCompl {R : Type u} [CommRing R] {p : Ideal R} [p.IsPrime]
    {a : R} (ha : a ∈ p.primeCompl) (R' : Type v) [CommRing R'] [Algebra R R']
    [IsLocalization (Submonoid.powers a) R'] :
    (Ideal.map (algebraMap R R') p).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) R' p inferInstance
    (disjoint_powers_of_mem_primeCompl ha)

/-- the extension of `Q` to the localization of `S` away from `a` is prime -/
theorem isPrime_map_algebraMapSubmonoid_powers {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] {Q : Ideal S} [Q.IsPrime] {a : R}
    (ha : a ∈ (Q.under R).primeCompl) (S' : Type w) [CommRing S'] [Algebra S S']
    [IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) S'] :
    (Ideal.map (algebraMap S S') Q).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) S' Q inferInstance
    (disjoint_algebraMapSubmonoid_powers ha)

/-- the extension of `Q` to the localization contracts back to `Q` -/
theorem under_map_algebraMapSubmonoid_powers {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] {Q : Ideal S} [Q.IsPrime] {a : R}
    (ha : a ∈ (Q.under R).primeCompl) (S' : Type w) [CommRing S'] [Algebra S S']
    [IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) S'] :
    (Ideal.map (algebraMap S S') Q).comap (algebraMap S S') = Q :=
  IsLocalization.under_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) S' inferInstance
    (disjoint_algebraMapSubmonoid_powers ha)

end Stacks.Flatness

namespace Module

/-- a localized module of a zero module is zero -/
theorem subsingleton_localizedModule {S N : Type u} [CommRing S] [AddCommGroup N] [Module S N]
    (P : Submonoid S) [Subsingleton N] : Subsingleton (LocalizedModule P N) := by
  have h0 : ∀ z : LocalizedModule P N, z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | _ n s =>
      rw [Subsingleton.elim n (0 : N)]
      exact LocalizedModule.zero_mk s
  exact ⟨fun z y => (h0 z).trans (h0 y).symm⟩

/-- pointed away localization at the `CompleteDevissageAt` level -/
theorem nonempty_completeDevissageAt_localizeAway {R S N : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    {Q : Ideal S} [Q.IsPrime] (a : R) (ha : a ∈ (Q.under R).primeCompl)
    [(Ideal.map (algebraMap R (Localization.Away a)) (Q.under R)).IsPrime]
    [(Ideal.map (algebraMap S
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))) Q).IsPrime]
    [Module.Finite (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))
      (LocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N)]
    (h : Nonempty (CompleteDevissageAt R S N Q)) :
    Nonempty (CompleteDevissageAt (Localization.Away a)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))
      (LocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N)
      (Ideal.map (algebraMap S
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))) Q)) := by
  obtain ⟨D⟩ := h
  cases D with
  | empty hz =>
    have := hz
    exact ⟨.empty (subsingleton_localizedModule _)⟩
  | nonempty data =>
    exact ⟨.nonempty (data.localizeAway a ha _ _
      (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) N))⟩

/-- changing the localization carrier of the base of a dévissage at a prime -/
theorem nonempty_completeDevissageAt_of_isLocalization_base {R A S N : Type u} [CommRing R]
    [CommRing A] [CommRing S] [AddCommGroup N] {a : R} [Algebra R A]
    [IsLocalization (Submonoid.powers a) A] [Algebra R S] [Algebra (Localization.Away a) S]
    [Algebra A S] [IsScalarTower R (Localization.Away a) S] [IsScalarTower R A S]
    [Algebra.FiniteType (Localization.Away a) S] [Algebra.FiniteType A S] [Module S N]
    [Module.Finite S N] {Q : Ideal S} [Q.IsPrime]
    (h : Nonempty (CompleteDevissageAt (Localization.Away a) S N Q)) :
    Nonempty (CompleteDevissageAt A S N Q) :=
  nonempty_completeDevissageAt_ofRingEquiv
    (IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) A).toRingEquiv
    (RingEquiv.refl S) (AddEquiv.refl N) (fun z => Algebra.algebraMap_algEquiv_away z)
    (fun s n => rfl) (by simp) h

end Module

namespace Algebra.ElementaryEtaleLocalization

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {p : Ideal A} [p.IsPrime]
  {q : Ideal C} [q.IsPrime] [q.LiesOver p]
  (E : ElementaryEtaleLocalization.{u, u, u, u} A C p q) (a : E.R')

/-- `E.S'` localized at the image of the powers of `a` -/
abbrev locAway : Type u := Localization (Algebra.algebraMapSubmonoid E.S' (Submonoid.powers a))

/-- the localized base changed module -/
abbrev locAwayModule (M : Type u) [AddCommGroup M] [Module C M] : Type u :=
  LocalizedModule (Algebra.algebraMapSubmonoid E.S' (Submonoid.powers a))
    (TensorProduct C E.S' M)

/-- the prime of `E.locAway a` over `E.q'` -/
abbrev locAwayPrime : Ideal (E.locAway a) := Ideal.map (algebraMap E.S' (E.locAway a)) E.q'

/-- the `A`-algebra structure on `E.locAway a` -/
@[instance_reducible] noncomputable def locAwayAlgebra : Algebra A (E.locAway a) :=
  ((algebraMap E.R' (E.locAway a)).comp (algebraMap A E.R')).toAlgebra

end Algebra.ElementaryEtaleLocalization

namespace Module

/-- main theorem -/
theorem exists_locAway_completeDevissageAt_of_henselian (A C M : Type u) [CommRing A]
    [IsLocalRing A] [HenselianLocalRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    [AddCommGroup M] [Module C M] [Module.Finite C M] (q : Ideal C) [q.IsPrime]
    [q.LiesOver (maximalIdeal A)] :
    ∃ (E : Algebra.ElementaryEtaleLocalization.{u, u, u, u} A C (q.under A) q) (a : E.R'),
      a ∈ E.p'.primeCompl ∧
      ∃ hFiniteType : Algebra.FiniteType E.R' E.S',
        letI := hFiniteType
        letI : Algebra A (E.locAway a) := E.locAwayAlgebra a
        haveI : Module.Finite E.S' (TensorProduct C E.S' M) :=
          Module.Finite.base_change C E.S' M
        haveI : Module.Finite (E.locAway a) (E.locAwayModule a M) :=
          Module.Finite.of_isLocalizedModule
            (Algebra.algebraMapSubmonoid E.S' (Submonoid.powers a))
            (LocalizedModule.mkLinearMap _ _)
        ∃ hPrime : (E.locAwayPrime a).IsPrime,
          letI := hPrime
          ∃ _hFT : Algebra.FiniteType A (E.locAway a),
            IsScalarTower A C (E.locAway a) ∧ (E.locAwayPrime a).LiesOver q ∧
              Nonempty (CompleteDevissageAt A (E.locAway a) (E.locAwayModule a M)
                (E.locAwayPrime a)) := by
  obtain ⟨E, hFT, hD⟩ := Module.exists_elementaryEtaleLocalization_completeDevissageAt A C M q
  let := hFT
  have : Module.Finite E.S' (TensorProduct C E.S' M) := Module.Finite.base_change C E.S' M
  obtain ⟨σ, a, ha, hσa, hkill, hloc⟩ :=
    E.exists_isLocalization_away_of_henselian (‹q.LiesOver (maximalIdeal A)›.over).symm
  let : Algebra E.R' A := σ.toRingHom.toAlgebra
  let := hloc
  have hq'p' : E.q'.under E.R' = E.p' := E.q'_liesOver_p'.symm
  have ha' : a ∈ (E.q'.under E.R').primeCompl := fun hmem => ha (hq'p' ▸ hmem)
  let : Algebra A (E.locAway a) := E.locAwayAlgebra a
  have : Module.Finite (E.locAway a) (E.locAwayModule a M) :=
    Module.Finite.of_isLocalizedModule
    (Algebra.algebraMapSubmonoid E.S' (Submonoid.powers a)) (LocalizedModule.mkLinearMap _ _)
  have hPrime : (E.locAwayPrime a).IsPrime :=
    Stacks.Flatness.isPrime_map_algebraMapSubmonoid_powers ha' (E.locAway a)
  have : (Ideal.map (algebraMap E.R' (Localization.Away a)) (E.q'.under E.R')).IsPrime :=
    Stacks.Flatness.isPrime_map_of_mem_primeCompl ha' (Localization.Away a)
  have hunit : IsUnit (algebraMap E.R' (E.locAway a) a) := by
    rw [IsScalarTower.algebraMap_apply E.R' E.S' (E.locAway a)]
    exact IsLocalization.map_units
      (M := Algebra.algebraMapSubmonoid E.S' (Submonoid.powers a)) (E.locAway a)
      ⟨algebraMap E.R' E.S' a, ⟨a, Submonoid.mem_powers a, rfl⟩⟩
  have htower : IsScalarTower E.R' A (E.locAway a) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    refine hunit.mul_left_cancel ?_
    change algebraMap E.R' (E.locAway a) a * algebraMap E.R' (E.locAway a) x
      = algebraMap E.R' (E.locAway a) a *
        algebraMap E.R' (E.locAway a) (algebraMap A E.R' (σ x))
    rw [← map_mul, ← map_mul, hkill x]
  have hFTA : Algebra.FiniteType A (E.locAway a) :=
    Algebra.finiteType_of_isLocalization_base (a := a)
  refine ⟨E, a, ha, hFT, hPrime, hFTA, ?_, ?_, ?_⟩
  · refine IsScalarTower.of_algebraMap_eq fun y => ?_
    have hA : algebraMap A (E.locAway a) y
        = algebraMap E.R' (E.locAway a) (algebraMap A E.R' y) := rfl
    rw [hA, IsScalarTower.algebraMap_apply E.R' E.S' (E.locAway a),
      IsScalarTower.algebraMap_apply C E.S' (E.locAway a)]
    exact congrArg (algebraMap E.S' (E.locAway a))
      (congrFun (congrArg (fun f : A →+* E.S' => (f : A → E.S')) E.commutes) y).symm
  · refine ⟨?_⟩
    change q = Ideal.comap (algebraMap C (E.locAway a)) (E.locAwayPrime a)
    rw [IsScalarTower.algebraMap_eq C E.S' (E.locAway a), ← Ideal.comap_comap,
      Stacks.Flatness.under_map_algebraMapSubmonoid_powers ha' (E.locAway a)]
    exact E.q'_liesOver_q
  · exact Module.nonempty_completeDevissageAt_of_isLocalization_base (a := a)
      (Module.nonempty_completeDevissageAt_localizeAway a ha' hD)

end Module

end
