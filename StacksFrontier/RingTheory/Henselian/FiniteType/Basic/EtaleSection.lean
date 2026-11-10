module

import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.RingTheory.Artinian.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Henselian étale sections and the quasi-finite locus over the closed point

Preliminaries for the decomposition of a finite type algebra over a henselian local ring:
transport of non-quasi-finiteness along algebra isomorphisms, the product decomposition attached
to an idempotent, finiteness of the quasi-finite primes over the maximal ideal, and sections of
étale algebras over a henselian local ring at a residue point.
-/

@[expose] public section

universe u v

/-- The "not quasi-finite at any prime over `𝔪`" condition transports along an `R`-algebra
isomorphism: if `e : C ≃ₐ[R] B` and `C` has no quasi-finite prime over the maximal ideal of the
local ring `R`, then neither does `B`.

Since `Algebra.QuasiFiniteAt R 𝔮` unfolds to `Algebra.QuasiFinite R (Localization.AtPrime 𝔮)`,
a prime `𝔮` of `B` is compared with `𝔮' := 𝔮.comap e`: the algebra isomorphism `e` induces an
`R`-algebra isomorphism `Localization.AtPrime 𝔮' ≃ₐ[R] Localization.AtPrime 𝔮`, whence
`QuasiFiniteAt R 𝔮 ↔ QuasiFiniteAt R 𝔮'`. Lying over `maximalIdeal R` is preserved because
`algebraMap R B = e.toRingHom ∘ algebraMap R C`, so that
`𝔮'.comap (algebraMap R C) = 𝔮.comap (algebraMap R B)`. -/
lemma not_qf_over_maximal_of_algEquiv (R : Type u) [CommRing R] [IsLocalRing R] {B C : Type*}
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] (e : C ≃ₐ[R] B)
    (hC : ∀ (𝔮 : Ideal C) [𝔮.IsPrime], 𝔮.LiesOver (IsLocalRing.maximalIdeal R) →
        ¬ Algebra.QuasiFiniteAt R 𝔮) :
    ∀ (𝔮 : Ideal B) [𝔮.IsPrime], 𝔮.LiesOver (IsLocalRing.maximalIdeal R) →
        ¬ Algebra.QuasiFiniteAt R 𝔮 := by
  intro 𝔮 h𝔮prime h𝔮 Hqf
  set 𝔮' : Ideal C := 𝔮.comap e.toRingHom with h𝔮'def
  have : 𝔮'.IsPrime := Ideal.comap_isPrime e.toRingHom 𝔮
  have : 𝔮'.LiesOver (IsLocalRing.maximalIdeal R) := Ideal.comap_liesOver _ _ e
  -- submonoid map
  have hmap : Submonoid.map (e : C →+* B) (𝔮'.primeCompl) = 𝔮.primeCompl := by
    have hc : 𝔮'.primeCompl = Submonoid.comap (e : C →+* B) (𝔮.primeCompl) := by
      ext x
      simp [Ideal.primeCompl, h𝔮'def]
    rw [hc]
    exact Submonoid.map_comap_eq_of_surjective e.surjective _
  -- transport quasi-finiteness
  have eLoc : Localization.AtPrime 𝔮' ≃ₐ[R] Localization.AtPrime 𝔮 :=
    IsLocalization.algEquivOfAlgEquiv (Localization.AtPrime 𝔮') (Localization.AtPrime 𝔮) e hmap
  have Hqf' : Algebra.QuasiFiniteAt R 𝔮' := by
    rw [Algebra.QuasiFiniteAt, Algebra.QuasiFinite.iff_of_algEquiv eLoc]
    exact Hqf
  exact hC 𝔮' inferInstance Hqf'

/-- **Idempotent splitting (general algebra).** A commutative `R`-algebra `S` with an
idempotent `e` decomposes, as an `R`-algebra, into the product of the two quotient algebras
`S ⧸ span{1-e}` (the `e`-part, `≅ Sₑ`) and `S ⧸ span{e}` (the `(1-e)`-part, `≅ S_{1-e}`).

For an idempotent `e`, the ideals `span{e}` and `span{1-e}` are comaximal (`e + (1-e) = 1`, so
`IsCoprime`) and their intersection is `0` (`e(1-e) = 0`, and the spans are themselves the
annihilators). The Chinese remainder `R`-algebra map
`S → (S ⧸ span{1-e}) × (S ⧸ span{e})` is therefore bijective. -/
@[sga "3 VIIB 1.6" "partial"]
lemma idem_algEquiv_prod (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (e : S) (he : IsIdempotentElem e) :
    Nonempty (S ≃ₐ[R] (S ⧸ Ideal.span {1 - e}) × (S ⧸ Ideal.span {e})) := by
  classical
  -- `algebraMap R (S ⧸ I)` factors compatibly through `Ideal.Quotient.factor`
  have hfactor_alg : ∀ {I J : Ideal S} (h : I ≤ J) (r : R),
      (Ideal.Quotient.factor h) (algebraMap R (S ⧸ I) r) = algebraMap R (S ⧸ J) r :=
    fun h r => (Ideal.Quotient.factorₐ R h).commutes r
  have hee : e * e = e := he
  -- coprimality: span{1-e} ⊔ span{e} = ⊤ since (1-e) + e = 1
  have hcop : IsCoprime (Ideal.span {1 - e}) (Ideal.span {e}) := by
    rw [Ideal.isCoprime_iff_add, Ideal.one_eq_top, Ideal.eq_top_iff_one]
    have h1 : (1 - e) ∈ Ideal.span {1 - e} := Ideal.mem_span_singleton_self _
    have h2 : e ∈ Ideal.span {e} := Ideal.mem_span_singleton_self _
    simpa using Submodule.add_mem_sup h1 h2
  -- intersection is ⊥: span{1-e} ⊓ span{e} = span{(1-e)*e} = span{0} = ⊥
  have hinf : Ideal.span {1 - e} ⊓ Ideal.span {e} = (⊥ : Ideal S) := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxu, hxv⟩ := hx
    rw [Ideal.mem_span_singleton] at hxu hxv
    obtain ⟨c, hc⟩ := hxu
    obtain ⟨d, hd⟩ := hxv
    have hex : e * x = x := by rw [hd]; linear_combination d * hee
    have hxzero : x = 0 := by rw [← hex, hc]; linear_combination (-c) * hee
    rw [Ideal.mem_bot]; exact hxzero
  -- CRT ring equiv on the trivial intersection
  let cre : (S ⧸ (Ideal.span {1 - e} ⊓ Ideal.span {e})) ≃+*
      ((S ⧸ Ideal.span {1 - e}) × (S ⧸ Ideal.span {e})) :=
    Ideal.quotientInfEquivQuotientProd _ _ hcop
  -- R-compatibility of cre, packaging it as an R-algebra equiv
  have hcre : ∀ (r : R), cre (algebraMap R _ r) = algebraMap R _ r := by
    intro r
    rw [Prod.algebraMap_apply]
    apply Prod.ext
    · rw [Ideal.quotientInfEquivQuotientProd_fst]; exact hfactor_alg _ r
    · rw [Ideal.quotientInfEquivQuotientProd_snd]; exact hfactor_alg _ r
  let crea : (S ⧸ (Ideal.span {1 - e} ⊓ Ideal.span {e})) ≃ₐ[R]
      ((S ⧸ Ideal.span {1 - e}) × (S ⧸ Ideal.span {e})) :=
    AlgEquiv.ofRingEquiv hcre
  -- identify S ⧸ (inf) with S ⧸ ⊥, then with S
  let eq1 : S ≃ₐ[R] (S ⧸ (⊥ : Ideal S)) := (AlgEquiv.quotientBot R S).symm
  let eq2 : (S ⧸ (⊥ : Ideal S)) ≃ₐ[R] (S ⧸ (Ideal.span {1 - e} ⊓ Ideal.span {e})) :=
    Ideal.quotientEquivAlgOfEq R hinf.symm
  exact ⟨eq1.trans (eq2.trans crea)⟩

/-- A prime lying over the maximal ideal of `R` contains the extension of that ideal to `S`. -/
private theorem map_maximalIdeal_le_of_liesOver {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] (𝔮 : Ideal S) [𝔮.LiesOver (IsLocalRing.maximalIdeal R)] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ 𝔮 :=
  Ideal.map_le_iff_le_comap.2 Ideal.LiesOver.over.le

/-- The localization of the closed fibre at a quasi-finite point is Artinian: if `R → S` is
quasi-finite at a prime `𝔮` of `S` lying over the maximal ideal `𝔪` of the local ring `R`, then
the localization of the closed fibre `S/𝔪S` at the image `𝔮̄` of `𝔮` is an Artinian ring.

By `Algebra.quasiFinite_iff` (tag 00PM) applied to the prime `𝔪` of `R`, quasi-finiteness of
`R → Localization.AtPrime 𝔮` at the closed point says the fibre
`κ ⊗_R (Localization.AtPrime 𝔮)` is module-finite over the residue field `κ = ResidueField R`.
That fibre is canonically isomorphic to `Localization.AtPrime 𝔮̄` with `𝔮̄ = 𝔮.map (mk 𝔪S)`,
because localization commutes with the base change `κ ⊗_R -` and `κ ⊗_R S ≅ S/𝔪S`; and a ring
module-finite over a field is Artinian. -/
@[ega "0 7.4.4" "(i)"]
lemma closedFibre_localization_isArtinian
    (R : Type u) [CommRing R] [IsLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (𝔮 : Ideal S) [h𝔮 : 𝔮.IsPrime]
    [𝔮.LiesOver (IsLocalRing.maximalIdeal R)]
    (hqf : Algebra.QuasiFiniteAt R 𝔮)
    (q : Ideal (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)))
    [q.IsPrime]
    (hq : q = 𝔮.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S)))) :
    IsArtinianRing (Localization.AtPrime q) := by
  classical
  set π : S →+* (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) with hπ
  have hsub := map_maximalIdeal_le_of_liesOver (R := R) 𝔮
  have hπsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hcomap : 𝔮 = Ideal.comap π q := by
    rw [hq, Ideal.comap_map_of_surjective π hπsurj, ← RingHom.ker_eq_comap_bot, hπ, Ideal.mk_ker]
    exact (sup_eq_left.mpr hsub).symm
  -- g : S_𝔮 →ₐ[R] T_q, the localization of the quotient map π
  set g0 : Localization.AtPrime 𝔮 →+* Localization.AtPrime q :=
    Localization.localRingHom 𝔮 q π hcomap with hg0
  have hg0R : ∀ r : R, g0 ((algebraMap R (Localization.AtPrime 𝔮)) r)
      = (algebraMap R (Localization.AtPrime q)) r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime 𝔮)]
    rw [hg0, Localization.localRingHom_to_map]
    rw [IsScalarTower.algebraMap_apply R (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (Localization.AtPrime q)]
    congr 1
  have hg0surj : Function.Surjective g0 := by
    intro y
    obtain ⟨⟨x, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
    obtain ⟨a, rfl⟩ := hπsurj x
    obtain ⟨b, rfl⟩ := hπsurj s
    have hbcompl : b ∈ 𝔮.primeCompl := by
      intro hb; apply hs
      have hb' : b ∈ Ideal.comap π q := hcomap ▸ hb
      rwa [Ideal.mem_comap] at hb'
    refine ⟨IsLocalization.mk' (Localization.AtPrime 𝔮) a (⟨b, hbcompl⟩ : 𝔮.primeCompl), ?_⟩
    rw [hg0, Localization.localRingHom_mk']
  let g : Localization.AtPrime 𝔮 →ₐ[R] Localization.AtPrime q :=
    { g0 with commutes' := hg0R }
  -- f0 : κ' →+* T_q, lifting `algebraMap R T_q` across the residue field of 𝔪
  have h1 : IsLocalRing.maximalIdeal R ≤ RingHom.ker (algebraMap R (Localization.AtPrime q)) := by
    intro m hm
    rw [RingHom.mem_ker,
      IsScalarTower.algebraMap_apply R (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
          (Localization.AtPrime q)]
    have hz : (algebraMap S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))) (algebraMap R
        S m) = 0 := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hm
    rw [IsScalarTower.algebraMap_apply R S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)),
        hz, map_zero]
  have h2 : (IsLocalRing.maximalIdeal R).primeCompl ≤
      Submonoid.comap (algebraMap R (Localization.AtPrime q)) (IsUnit.submonoid
          (Localization.AtPrime q)) := by
    intro m hm
    rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact (IsLocalRing.notMem_maximalIdeal.mp hm).map _
  set f0 : (IsLocalRing.maximalIdeal R).ResidueField →+* (Localization.AtPrime q) :=
    Ideal.ResidueField.lift (IsLocalRing.maximalIdeal R) (algebraMap R (Localization.AtPrime q)) h1
        h2 with hf0
  -- equip the closed-fibre localization with the κ'-algebra structure coming from f0
  let algκTq : Algebra (IsLocalRing.maximalIdeal R).ResidueField (Localization.AtPrime q) :=
    f0.toAlgebra
  have towerκ : IsScalarTower R (IsLocalRing.maximalIdeal R).ResidueField (Localization.AtPrime
      q) := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change (algebraMap R (Localization.AtPrime q)) r = f0 (algebraMap R (IsLocalRing.maximalIdeal
        R).ResidueField r)
    rw [hf0, Ideal.ResidueField.lift_algebraMap]
  -- Ψ : (the fibre κ' ⊗_R S_𝔮) →ₐ[κ'] T_q, surjective onto T_q
  set Ψ : (IsLocalRing.maximalIdeal R).Fiber (Localization.AtPrime 𝔮) →ₐ[(IsLocalRing.maximalIdeal
      R).ResidueField]
      (Localization.AtPrime q) :=
    Algebra.TensorProduct.productLeftAlgHom
      (Algebra.ofId (IsLocalRing.maximalIdeal R).ResidueField (Localization.AtPrime q)) g with hΨ
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    obtain ⟨z, rfl⟩ := hg0surj y
    refine ⟨1 ⊗ₜ[R] z, ?_⟩
    rw [hΨ]
    simp only [Algebra.TensorProduct.productLeftAlgHom]
    rw [Algebra.TensorProduct.lift_tmul]
    simp only [map_one, one_mul]
    rfl
  -- the fibre is module-finite over κ' by quasi-finiteness (tag 00PM)
  have hFfin : Module.Finite (IsLocalRing.maximalIdeal R).ResidueField
      ((IsLocalRing.maximalIdeal R).Fiber (Localization.AtPrime 𝔮)) :=
    (Algebra.quasiFinite_iff R (Localization.AtPrime 𝔮)).mp hqf (IsLocalRing.maximalIdeal R)
  -- transfer module-finiteness across the surjection, then a finite algebra over a field is
  -- Artinian
  have hTqfin : Module.Finite (IsLocalRing.maximalIdeal R).ResidueField (Localization.AtPrime q) :=
    Module.Finite.of_surjective Ψ.toLinearMap hΨsurj
  exact finite_dimensional_algebra_is_artinian (IsLocalRing.maximalIdeal R).ResidueField
      (Localization.AtPrime q)

/-- Finiteness of the quasi-finite locus over `𝔪`: for a finite type algebra `S` over a local
ring `R`, the set of primes `𝔮` of `S` lying over the maximal ideal `𝔪` at which `R → S` is
quasi-finite is finite.

By `Algebra.quasiFinite_iff` and `Algebra.QuasiFinite.iff_finite_primesOver` (tag 00PM),
quasi-finiteness at `𝔮` over `𝔪` is equivalent to `𝔮` being an *isolated* point of the closed
fibre `Spec(S ⊗_R κ) = Spec(S/𝔪S)`, that is, both minimal and maximal in the fibre. The closed
fibre is a finite type `κ`-algebra for `κ` the residue field, hence Noetherian, so it has only
finitely many minimal primes; the isolated points are among the minimal primes that are also
maximal, hence finite in number. -/
@[ega "IV 5.7.9" "special case"]
lemma qf_primesOver_maximal_finite (R : Type u) [CommRing R] [IsLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    {𝔮 : Ideal S | ∃ _ : 𝔮.IsPrime, 𝔮.LiesOver (IsLocalRing.maximalIdeal R) ∧
        Algebra.QuasiFiniteAt R 𝔮}.Finite := by
  -- The closed fibre `T = S/𝔪S` is finite type over `κ = ResidueField R`, hence Noetherian, so
  -- it has finitely many minimal primes. The map `𝔮 ↦ 𝔮.map π` (π : S → T = S/𝔪S) is an
  -- injection from the quasi-finite locus over `𝔪` into `minimalPrimes T`: for a quasi-finite
  -- prime `𝔮` over `𝔪`, its image `𝔮̄` in `T` is a minimal prime because the local ring
  -- `T_𝔮̄ = (S/𝔪S)_𝔮̄` is Artinian — it is the closed fibre `κ ⊗_R S_𝔮` of the localization,
  -- which is finite over `κ` exactly because `R → S` is quasi-finite at `𝔮`
  -- (`Algebra.quasiFinite_iff`, tag 00PM). In an Artinian local ring every prime is maximal, so
  -- `𝔮̄` has no prime strictly below it, i.e. it is minimal. Finiteness of the locus follows by
  -- transporting the finiteness of `minimalPrimes T` back along the injection.
  classical
  set 𝔪 := IsLocalRing.maximalIdeal R with h𝔪
  set 𝔪S : Ideal S := 𝔪.map (algebraMap R S) with h𝔪S
  set π : S →+* (S ⧸ 𝔪S) := Ideal.Quotient.mk 𝔪S with hπ
  set T := S ⧸ 𝔪S with hT
  -- the closed fibre `T = S/𝔪S` is a finite-type `κ`-algebra, hence Noetherian
  have hle : 𝔪 ≤ Ideal.comap (algebraMap R S) 𝔪S := fun x hx => Ideal.mem_map_of_mem _ hx
  let algκT : Algebra (IsLocalRing.ResidueField R) T :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  have tower : IsScalarTower R (IsLocalRing.ResidueField R) T :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have ftRT : Algebra.FiniteType R T :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R 𝔪S) Ideal.Quotient.mk_surjective
  have ftκT : Algebra.FiniteType (IsLocalRing.ResidueField R) T :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (IsLocalRing.ResidueField R) T
  have noethT : IsNoetherianRing T :=
    Algebra.FiniteType.isNoetherianRing (IsLocalRing.ResidueField R) T
  have hπsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hcomapbot : Ideal.comap π (⊥ : Ideal T) ≤ 𝔪S := by
    rw [← RingHom.ker_eq_comap_bot, hπ, Ideal.mk_ker]
  have hsub_of_over : ∀ (𝔮 : Ideal S), 𝔮.LiesOver 𝔪 → 𝔪S ≤ 𝔮 := fun 𝔮 _ =>
    map_maximalIdeal_le_of_liesOver 𝔮
  -- A prime of `T` whose localization is Artinian is a minimal prime (Artinian ⇒ dim 0, local
  -- ⇒ unique prime, so nothing lies strictly below it).
  have hmin_of_artinian : ∀ (q : Ideal T) [q.IsPrime],
      IsArtinianRing (Localization.AtPrime q) → q ∈ minimalPrimes T := by
    intro q hq hart
    constructor
    · exact ⟨hq, bot_le⟩
    · intro Q hQ hQq
      obtain ⟨hQp, -⟩ := hQ
      set e := IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime q) q with he
      have hQmem : Q.IsPrime ∧ Q ≤ q := ⟨hQp, hQq⟩
      have hqmem : q.IsPrime ∧ q ≤ q := ⟨hq, le_refl q⟩
      set PQ := e.symm ⟨Q, hQmem⟩ with hPQ
      set Pq := e.symm ⟨q, hqmem⟩ with hPq
      have : PQ.val.IsPrime := PQ.property
      have : Pq.val.IsPrime := Pq.property
      have hPQmax : PQ.val.IsMaximal := IsArtinianRing.isMaximal_of_isPrime PQ.val
      have hle_sub : (⟨Q, hQmem⟩ : {p : Ideal T // p.IsPrime ∧ p ≤ q}) ≤ ⟨q, hqmem⟩ := hQq
      have hmono : PQ ≤ Pq := e.symm.monotone hle_sub
      have hlocal : PQ.val = Pq.val := hPQmax.eq_of_le Pq.property.ne_top hmono
      have heq : (⟨Q, hQmem⟩ : {p : Ideal T // p.IsPrime ∧ p ≤ q}) = ⟨q, hqmem⟩ := by
        apply e.symm.injective; exact Subtype.ext hlocal
      have hQq' : Q = q := congrArg Subtype.val heq
      exact le_of_eq hQq'.symm
  -- The quasi-finite locus injects into `minimalPrimes T` via `𝔮 ↦ 𝔮.map π`.
  have hmin : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], 𝔮.LiesOver 𝔪 → Algebra.QuasiFiniteAt R 𝔮 →
      𝔮.map π ∈ minimalPrimes T := by
    intro 𝔮 hp hover hqf
    have hqbar_prime : (𝔮.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hπsurj <| by
        rw [hπ, Ideal.mk_ker]
        exact hsub_of_over 𝔮 hover
    apply hmin_of_artinian (𝔮.map π)
    -- By tag 00PM (`Algebra.quasiFinite_iff`), quasi-finiteness of `R → S` at `𝔮` over `𝔪` says
    -- the closed fibre `κ ⊗_R S_𝔮` of the localization is module-finite over the residue field
    -- `κ`. That closed fibre is `(S/𝔪S)_𝔮̄ = Localization.AtPrime (𝔮.map π)`, since localization
    -- commutes with the base change `κ ⊗_R -`, and a finite algebra over the field `κ` is an
    -- Artinian ring; this is `closedFibre_localization_isArtinian`.
    have : 𝔮.LiesOver 𝔪 := hover
    exact closedFibre_localization_isArtinian R S 𝔮 hqf (𝔮.map π) rfl
  -- Assemble: transport finiteness of `minimalPrimes T` back along the injection.
  apply Set.Finite.of_finite_image (f := fun 𝔮 => Ideal.map π 𝔮)
  · apply (minimalPrimes.finite_of_isNoetherianRing T).subset
    rintro x ⟨𝔮, ⟨hp, hover, hqf⟩, rfl⟩
    exact hmin 𝔮 hover hqf
  · rintro 𝔮₁ ⟨hp1, hover1, _⟩ 𝔮₂ ⟨hp2, hover2, _⟩ heq
    simp only at heq
    have hcm : ∀ 𝔮 : Ideal S, 𝔮.LiesOver 𝔪 → Ideal.comap π (Ideal.map π 𝔮) = 𝔮 := by
      intro 𝔮 h
      rw [Ideal.comap_map_of_surjective π hπsurj]
      exact sup_eq_left.mpr (le_trans hcomapbot (hsub_of_over 𝔮 h))
    rw [← hcm 𝔮₁ hover1, ← hcm 𝔮₂ hover2, heq]

/-- A ring map compatible with the structure maps commutes with evaluation of polynomials. -/
private theorem map_aeval_of_algebraMap_comm {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (f : A →+* B)
    (hf : ∀ r : R, f (algebraMap R A r) = algebraMap R B r) (x : A) (p : Polynomial R) :
    f (Polynomial.aeval x p) = Polynomial.aeval (f x) p :=
  (Polynomial.aeval_algHom_apply ({ f with commutes' := hf } : A →ₐ[R] B) x p).symm

/-- The lift of the structure map of a localization away from `c` is compatible with the
`R`-algebra structures. -/
private theorem away_lift_algebraMap {R R' K : Type*} [CommRing R] [CommRing R'] [CommRing K]
    [Algebra R R'] [Algebra R K] [Algebra R' K] [IsScalarTower R R' K] (c : R')
    (hcunit : IsUnit (algebraMap R' K c)) (r : R) :
    IsLocalization.Away.lift c hcunit (algebraMap R (Localization.Away c) r) =
      algebraMap R K r := by
  rw [IsScalarTower.algebraMap_apply R R' (Localization.Away c) r, IsLocalization.Away.lift_eq,
    ← IsScalarTower.algebraMap_apply R R' K r]

/-- A henselian root of a standard-étale chart. Let `R` be henselian local, let `R'` be an étale
`R`-algebra with a `κ`-rational point `P` over `𝔪` (residue bijectivity `hres`), and let
`Localization.Away c` be a standard-étale chart at `P` (`c ∉ P`) with presentation
`pres : StandardEtalePresentation R (Localization.Away c)`, given by a monic `f`, an element `g`
and the condition `cond`. Then there is an `a : R` with `pres.HasMap a`, that is,
`aeval a pres.f = 0` and `IsUnit (aeval a pres.g)`, whose image in the residue field of `P` is
the prescribed point `pres.x`.

The argument runs as follows.
* The residue bijectivity `κ ≅ R'/P` of `hres` forces the induced `κ`-algebra map on the closed
  fibre `(κ[x]/(f̄))_ḡ = (Localization.Away c) ⊗_R κ` to land in `κ` itself, producing
  `ā := ψ(x̄) ∈ κ` with `f̄(ā) = 0`, with `f̄'(ā) ≠ 0` because `pres.f'` is a unit in the chart,
  and with `ḡ(ā) ≠ 0` because `pres.g` is a unit in the chart.
* As `f` is monic and `ā` is a simple root of `f̄`, `HenselianLocalRing.TFAE` yields an `a : R`
  with `f.IsRoot a`, hence `aeval a pres.f = 0`, and with `residue R a = ā`.
* From `ḡ(ā) ≠ 0` and `a ≡ ā mod 𝔪` we get `g(a) ∉ 𝔪`, hence `IsUnit (aeval a pres.g)` since
  `R` is local. Together these say `pres.HasMap a`. -/
@[sga "3 X 4.5" "special case", sga "3 XI 1.11" "special case"]
lemma henselian_etale_standardChart_hasMap
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (R' : Type v) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (P : Ideal R') [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hres : Function.Bijective
      ⇑(Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P (Algebra.ofId R R')
          Ideal.LiesOver.over))
    (c : R')
    (hcunit : IsUnit ((algebraMap R' P.ResidueField) c))
    (pres : StandardEtalePresentation R (Localization.Away c)) :
    ∃ a : R, pres.HasMap a ∧
      algebraMap R P.ResidueField a
        = IsLocalization.Away.lift c hcunit pres.x := by
  classical
  set K := P.ResidueField with hK
  set φ : R →+* K := algebraMap R K with hφ
  set ψ : Localization.Away c →+* K := IsLocalization.Away.lift c hcunit with hψ
  have hcomm : ∀ p : Polynomial R, ψ (Polynomial.aeval pres.x p) = Polynomial.aeval (ψ
      pres.x) p := map_aeval_of_algebraMap_comm ψ (away_lift_algebraMap c hcunit) _
  set ā : K := ψ pres.x with hā
  -- φ is surjective
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨z, hz⟩ := hres.surjective y
    obtain ⟨w, hw⟩ := Ideal.algebraMap_residueField_surjective (IsLocalRing.maximalIdeal R) z
    refine ⟨w, ?_⟩
    rw [hφ]
    have := AlgHom.commutes
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P (Algebra.ofId R R')
          Ideal.LiesOver.over) w
    rw [← this, hw, hz]
  -- φ is a local hom
  have hlocal : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have hker : φ a = 0 := by
      have : a ∈ RingHom.ker φ := by
        rw [IsLocalRing.ker_eq_maximalIdeal φ hφsurj]; exact hmem
      simpa [RingHom.mem_ker] using this
    rw [hker] at ha
    exact (not_isUnit_zero) ha
  -- the lift g : ResidueField R →+* K
  set g : IsLocalRing.ResidueField R →+* K := IsLocalRing.ResidueField.lift φ with hg
  have hg_residue : g.comp (IsLocalRing.residue R) = φ := by
    rw [hg]
    exact IsLocalRing.ResidueField.lift_comp_residue φ
  have hginj : Function.Injective g := (RingHom.injective g)
  -- g commutes with aeval
  have hgcomm : ∀ (b : IsLocalRing.ResidueField R) (p : Polynomial R),
      g (Polynomial.aeval b p) = Polynomial.aeval (g b) p := fun b p =>
    map_aeval_of_algebraMap_comm (R := R) g (RingHom.congr_fun hg_residue) b p
  -- the facts about pres.x
  have hfx : Polynomial.aeval pres.x pres.f = 0 := pres.hasMap.left
  have hgx : IsUnit (Polynomial.aeval pres.x pres.g) := pres.hasMap.right
  -- evals at ā
  have hāf : Polynomial.aeval ā pres.f = 0 := by
    rw [← hcomm, hfx, map_zero]
  have hāg_ne : Polynomial.aeval ā pres.g ≠ 0 := by
    rw [← hcomm]
    exact (hgx.map ψ).ne_zero
  -- derivative ≠ 0 at ā, using pres.cond
  have hādf : Polynomial.aeval ā (Polynomial.derivative pres.f) ≠ 0 := by
    obtain ⟨p₁, p₂, n, hcond⟩ := pres.cond
    have happ := congrArg (Polynomial.aeval ā) hcond
    simp only [map_add, map_mul, map_pow, hāf, zero_mul, add_zero] at happ
    intro hzero
    rw [hzero, zero_mul] at happ
    exact (pow_ne_zero n hāg_ne) happ.symm
  -- choose b : ResidueField R with g b = ā
  obtain ⟨r, hr⟩ := hφsurj ā
  set b : IsLocalRing.ResidueField R := IsLocalRing.residue R r with hb
  have hgb : g b = ā := by
    rw [hb, ← RingHom.comp_apply, hg_residue, hr]
  -- transfer the three facts to b
  have hb_zero : ∀ p : Polynomial R, Polynomial.aeval b p = 0 ↔ Polynomial.aeval ā p = 0 :=
    fun p => by rw [← map_eq_zero_iff g hginj, hgcomm, hgb]
  have hbf : Polynomial.aeval b pres.f = 0 := (hb_zero _).2 hāf
  have hbdf : Polynomial.aeval b (Polynomial.derivative pres.f) ≠ 0 := mt (hb_zero _).1 hādf
  have hbg : Polynomial.aeval b pres.g ≠ 0 := mt (hb_zero _).1 hāg_ne
  -- Hensel lift via TFAE item [1]
  have hH : HenselianLocalRing R := ‹_›
  have hiff := (HenselianLocalRing.TFAE R).out 1 2
  obtain ⟨a, hroot, hres_a⟩ :=
    hiff.mp hH pres.f pres.monic_f b hbf hbdf
  -- assemble pres.HasMap a ∧ pinning equation
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · -- aeval a pres.f = 0
    have : Polynomial.eval a pres.f = 0 := hroot
    rwa [Polynomial.coe_aeval_eq_eval]
  · -- IsUnit (aeval a pres.g)
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    apply hbg
    have hres_g : IsLocalRing.residue R (Polynomial.aeval a pres.g)
        = Polynomial.aeval b pres.g := by
      rw [← hres_a]
      exact map_aeval_of_algebraMap_comm (IsLocalRing.residue R) (fun _ => rfl) _ _
    rw [← hres_g]
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hmem
  · -- pinning: algebraMap R K a = ψ pres.x = ā
    -- φ a = g (residue R a) = g b = ā
    change φ a = ā
    have hφa : φ a = g b := by
      rw [← hg_residue, RingHom.comp_apply, hres_a]
    rw [hφa, hgb]

/-- Residue compatibility of the standard-étale section. Given a standard-étale chart
`Localization.Away c` at `P` (`c ∉ P`) with presentation `pres`, and a henselian root `a : R`
with `pres.HasMap a` pinned to `P` by `hpin`, the section
`σ = (pres.lift a ha) ∘ pres.equivRing ∘ ℓ : R' →ₐ[R] R` is residue-compatible at `P`, that is,
`∀ r' : R', r' - algebraMap R R' (σ r') ∈ P`.

Both `q ∘ σ` and the residue map `ρ = φ⁻¹ ∘ r` — where `r : R' → R'/P` and `φ : κ ≅ R'/P` comes
from the residue bijectivity — are `R`-algebra maps `R' → R'/P`. They agree on the image of `R`
and on the standard-étale generator, since `σ` sends it to the henselian root `a`, which reduces
mod `𝔪` to the root `ā` defining `P`. As the chart is `R`-generated by that variable, the two
maps coincide, giving `r (r' - algebraMap R R' (σ r')) = 0`, i.e. membership in `P = ker r`.

This is not automatic for an arbitrary section: it is exactly the compatibility of the henselian
root with the chosen point. -/
lemma henselian_etale_section_residue_compat
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (P : Ideal R') [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (c : R')
    (hcunit : IsUnit ((algebraMap R' P.ResidueField) c))
    (pres : StandardEtalePresentation R (Localization.Away c))
    (a : R) (ha : pres.HasMap a)
    (hpin : algebraMap R P.ResidueField a
        = IsLocalization.Away.lift c hcunit pres.x) :
    ∀ r' : R', r' - algebraMap R R'
      (((pres.lift a ha).comp
        (pres.equivRing.toAlgHom.comp
          (IsScalarTower.toAlgHom R R' (Localization.Away c)))) r') ∈ P := by
  -- `hpin` pins the henselian root `a` to the prescribed point `P`, namely
  -- `algebraMap R P.ResidueField a = ψ pres.x` with `ψ = IsLocalization.Away.lift c hcunit`.
  -- Without it the statement is false: for `R = ℚ`, `R' = ℚ × ℚ` and `f = X(X-1)` the two roots
  -- `{0, 1}` both satisfy `pres.HasMap a`, and the root selecting `Q ≠ P` gives the second
  -- projection, which is residue-incompatible at `P`.  At the call site in
  -- `henselian_etale_residue_point_section`, `hpin` comes for free from
  -- `henselian_etale_standardChart_hasMap`, since the henselian root reduces mod `𝔪` to the root
  -- `ā = ψ pres.x` defining `P`.
  classical
  set K := P.ResidueField with hK
  set L := Localization.Away c with hL
  -- scalar tower instances (hold by rfl)
  have towerK : IsScalarTower R R' K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have towerL : IsScalarTower R R' L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- ψ : L →+* K, the away lift
  set ψ : L →+* K := IsLocalization.Away.lift c hcunit with hψ
  -- ψ is R-linear
  have hψR : ∀ r : R, ψ (algebraMap R L r) = algebraMap R K r := away_lift_algebraMap c hcunit
  -- ψ on R'
  have hψR' : ∀ r' : R', ψ (algebraMap R' L r') = algebraMap R' K r' :=
    fun r' => IsLocalization.Away.lift_eq c hcunit r'
  -- ψ as an R-algebra hom L →ₐ[R] K
  let ψA : L →ₐ[R] K := { ψ with commutes' := hψR }
  -- Φ_res : pres.Ring →ₐ[R] K
  let Φ_res : pres.Ring →ₐ[R] K := ψA.comp pres.equivRing.symm.toAlgHom
  -- Φ_lift : pres.Ring →ₐ[R] K
  let Φ_lift : pres.Ring →ₐ[R] K := (Algebra.ofId R K).comp (pres.lift a ha)
  -- they agree on X
  have hagreeX : Φ_res pres.X = Φ_lift pres.X := by
    change ψA (pres.equivRing.symm pres.X) = (Algebra.ofId R K) ((pres.lift a ha) pres.X)
    rw [pres.lift_X]
    have hsymm : pres.equivRing.symm pres.X = pres.x := by
      rw [← pres.equivRing_x]; exact pres.equivRing.symm_apply_apply pres.x
    rw [hsymm]
    change ψ pres.x = algebraMap R K a
    rw [← hpin]
  -- so Φ_res = Φ_lift
  have hΦ : Φ_res = Φ_lift := StandardEtalePair.hom_ext hagreeX
  -- now conclude
  intro r'
  rw [← Ideal.algebraMap_residueField_eq_zero]
  set σ := ((pres.lift a ha).comp (pres.equivRing.toAlgHom.comp
    (IsScalarTower.toAlgHom R R' L))) with hσ
  rw [map_sub, sub_eq_zero]
  rw [← IsScalarTower.algebraMap_apply R R' K (σ r')]
  rw [← hψR' r']
  have hℓ : algebraMap R' L r' = (IsScalarTower.toAlgHom R R' L) r' := rfl
  rw [hℓ]
  have hσval : σ r' = (pres.lift a ha) (pres.equivRing ((IsScalarTower.toAlgHom R R' L) r')) := rfl
  rw [hσval]
  set y := pres.equivRing ((IsScalarTower.toAlgHom R R' L) r') with hy
  have hback : pres.equivRing.symm y = (IsScalarTower.toAlgHom R R' L) r' := by
    rw [hy]; exact pres.equivRing.symm_apply_apply _
  have e1 : ψ ((IsScalarTower.toAlgHom R R' L) r') = Φ_res y := by
    change ψ ((IsScalarTower.toAlgHom R R' L) r') = ψA (pres.equivRing.symm y)
    rw [hback]; rfl
  rw [e1, hΦ]
  change Φ_lift y = algebraMap R K ((pres.lift a ha) y)
  rfl

/-- Henselian splitting of a residue-rational étale point — the ring-theoretic content of Stacks
04GG part 11, and the fact that EGA IV 18.5.11 invokes.

Let `R` be henselian local with maximal ideal `𝔪` and residue field `κ = R/𝔪`, let `R'` be an
étale `R`-algebra, and let `P` be a prime of `R'` lying over `𝔪` whose induced residue extension
`κ → R'/P` is an isomorphism, i.e. `P` is a `κ`-rational point of the closed fibre (encoded as
bijectivity of `Ideal.ResidueField.mapₐ … (Algebra.ofId R R')`). Then there is an `R`-algebra
retraction `σ : R' →ₐ[R] R` of the structure map `R → R'`, residue-compatible at `P`, hence
splitting off a direct factor `≅ R`.

Equivalently, over a henselian local ring the functor from finite étale `R`-algebras to finite
étale `κ`-algebras is an equivalence on the connected component carrying the `κ`-point. Note that
polynomial Hensel lifting alone (`HenselianLocalRing.TFAE`) gives idempotent lifting for
*module-finite* algebras, not a section over a residue-rational point of a merely quasi-finite
étale algebra. The proof instead passes to a standard-étale chart at `P`, produces a henselian
root of its presentation with `henselian_etale_standardChart_hasMap`, and reads off the section;
residue compatibility is `henselian_etale_section_residue_compat`. -/
@[ega "IV 18.5.11" "special case",
  ega "IV 18.5.17" "affine étale morphisms",
  ega "IV 18.8.1" "(a)⇒(c), special case",
  sga "1 III 3.3" "special case",
  sga "3 VIB 5.6.1" "special case",
  sga "3 X 4.5" "special case",
  sga "4 XII 6.13" "partial"]
lemma henselian_etale_residue_point_section
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (P : Ideal R') [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hres : Function.Bijective
      ⇑(Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P (Algebra.ofId R R')
          Ideal.LiesOver.over)) :
    ∃ σ : R' →ₐ[R] R, ∀ r' : R', r' - algebraMap R R' (σ r') ∈ P := by
  -- A κ-rational point of the closed fibre of an étale R-algebra lifts to a section R' →ₐ[R] R,
  -- and any R-algebra hom R' →ₐ[R] R is automatically a retraction.  Concretely:
  --  * `Algebra.IsEtaleAt.exists_isStandardEtale` gives a standard-étale chart
  --    `Localization.Away c` with `c ∉ P`, and
  --    `IsStandardEtale.nonempty_standardEtalePresentation` gives its presentation `pres`.
  --  * `ℓ := IsScalarTower.toAlgHom R R' (Localization.Away c)` is the localization R-algebra map.
  --  * `φ := pres.equivRing : Localization.Away c ≃ₐ[R] pres.Ring`.
  --  * `henselian_etale_standardChart_hasMap` produces `a : R` with `pres.HasMap a`; then
  --    `τ := pres.lift a ha : pres.Ring →ₐ[R] R`. Compose: `σ := τ ∘ φ ∘ ℓ`.
  obtain ⟨c, hcP, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (S := R') P
  obtain ⟨pres⟩ := hstd.nonempty_standardEtalePresentation
  let ℓ : R' →ₐ[R] Localization.Away c := IsScalarTower.toAlgHom R R' (Localization.Away c)
  let φ : Localization.Away c ≃ₐ[R] pres.Ring := pres.equivRing
  have hcunit : IsUnit ((algebraMap R' P.ResidueField) c) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]; exact hcP
  obtain ⟨a, ha, hpin⟩ := henselian_etale_standardChart_hasMap R R' P hres c hcunit pres
  let τ : pres.Ring →ₐ[R] R := pres.lift a ha
  refine ⟨τ.comp (φ.toAlgHom.comp ℓ), ?_⟩
  -- Residue compatibility of the constructed section: σ realizes the residue isomorphism
  -- R'/P ≅ κ, i.e. q ∘ σ = ρ, the residue map. Both are R-algebra maps R' → R'/P agreeing on the
  -- standard-étale generator — σ sends it to the henselian root a, which reduces mod 𝔪 to the
  -- root ā defining P — hence they agree on all of R'.
  exact henselian_etale_section_residue_compat R R' P c hcunit pres a ha hpin

end
