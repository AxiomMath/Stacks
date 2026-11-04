module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion.ScalarExtension

@[expose] public section

/-!
# The covering `R → R' ⊕ R_f` of a Beauville--Laszlo glueing pair

Let `R` be a commutative ring, let `f : R`, and let `R → R'` be a ring map inducing
isomorphisms `R/fⁿR → R'/fⁿR'` for every `n > 0` — the standing hypothesis of the
Beauville--Laszlo theorem, satisfied in particular by the `(f)`-adic completion
`R^∧ = lim R/fⁿR`. This file collects the elementary descent properties of the pair of maps
`R → R'` and `R → R_f`, which together behave like a cover of `Spec(R)` even though `R → R'`
is usually not flat.

## Main results

* `quotient_pow_equiv_adicCompletion` (Stacks 0BNJ): the canonical map
  `R/fⁿR → R^∧/fⁿR^∧` is an isomorphism, so `(R → R^∧, f)` satisfies the standing hypothesis.
* `tensorProduct_prod_away_nontrivial_of_quotientMap_bijective` (Stacks 0BNL): the
  `R`-module `R' ⊕ R_f` is faithful, i.e. `M ⊗[R] (R' ⊕ R_f) ≠ 0` for every nonzero `M`.
* `primeSpectrum_cover_of_quotientMap_bijective` (Stacks 0BNM):
  `Spec(R') ⨿ Spec(R_f) → Spec(R)` is surjective.
* `finite_iff_tensorProduct_prod_away_of_quotientMap_bijective` (Stacks 0BNN): `M` is a
  finitely generated `R`-module if and only if `M ⊗[R] (R' ⊕ R_f)` is finitely generated
  over `R' ⊕ R_f`.

## Implementation notes

The standing hypothesis on `R → R'` is carried as bijectivity of the induced ring maps
`R/fⁿR → R'/fⁿR'`, written out as `Ideal.quotientMap` of the ideal power. The `(f)`-adic
completion is `AdicCompletion (Ideal.span {f}) R` and `R_f` is `Localization.Away f`, so the
statement about `R^∧` is obtained from the general one by `quotient_pow_equiv_adicCompletion`.
Faithfulness is phrased as `Nontrivial (M ⊗[R] (R' × R_f))` rather than as an inequality of
submodules, and the two summands are handled separately: if `M ⊗[R] R_f` is already nonzero we
are done, and otherwise `M` is `f`-power torsion and `M ⊗[R] R' ≅ M` (Stacks 0BNK).

## References

* [Beauville--Laszlo]
* [Stacks Project, Tag 0BNJ](https://stacks.math.columbia.edu/tag/0BNJ)
* [Stacks Project, Tag 0BNL](https://stacks.math.columbia.edu/tag/0BNL)
* [Stacks Project, Tag 0BNM](https://stacks.math.columbia.edu/tag/0BNM)
* [Stacks Project, Tag 0BNN](https://stacks.math.columbia.edu/tag/0BNN)
-/

namespace BeauvilleLaszlo
section

/-- A ring map `R → S` induces an isomorphism `R/I ≅ S/J` if `J` is the kernel of a map
`S → R/I` compatible with `R → S`. -/
private theorem bijective_quotientMap_of_ker_eq {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (φ : R →+* S) (π : S →+* R ⧸ I)
    (hker : RingHom.ker π = J) (hφ : ∀ r, π (φ r) = Ideal.Quotient.mk I r)
    (h : I ≤ J.comap φ) : Function.Bijective (Ideal.quotientMap J φ h) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, ← hker, RingHom.mem_ker, hφ] at hx
    exact hx
  · intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (π s)
    refine ⟨Ideal.Quotient.mk I r, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, ← hker, RingHom.mem_ker, map_sub, hφ, hr,
      sub_self]

/-- The canonical map `R / f^n R → R^∧ / f^n R^∧` is an isomorphism,
where `R^∧` is the `(f)`-adic completion. -/
@[stacks 0BNJ]
public theorem quotient_pow_equiv_adicCompletion {R : Type*} [CommRing R]
    (f : R) (n : ℕ) :
    ∃ e : (R ⧸ (Ideal.span {f}) ^ n) ≃+*
        (AdicCompletion (Ideal.span {f}) R ⧸
          (Ideal.span {(algebraMap R (AdicCompletion (Ideal.span {f}) R)) f}) ^ n),
      ∀ r : R,
        e (Ideal.Quotient.mk _ r) =
          Ideal.Quotient.mk _ ((algebraMap R (AdicCompletion (Ideal.span {f}) R)) r) := by
  let I : Ideal R := Ideal.span {f}
  let J : Ideal (AdicCompletion I R) :=
    Ideal.span {(algebraMap R (AdicCompletion I R)) f}
  have hker : J ^ n = RingHom.ker (AdicCompletion.evalₐ I n).toRingHom := by
    dsimp only [J]
    calc
      Ideal.span {(algebraMap R (AdicCompletion I R)) f} ^ n =
          (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
        rw [Ideal.map_pow]
        congr 1
        rw [Ideal.map_span]
        simp [I]
      _ = RingHom.ker (AdicCompletion.evalₐ I n).toRingHom := by
        ext x
        show x ∈ ((I ^ n).map (algebraMap R (AdicCompletion I R))).restrictScalars R ↔
          AdicCompletion.evalₐ I n x = 0
        rw [← Ideal.smul_top_eq_map,
          AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton f)]
        simp only [LinearMap.mem_ker]
        have hEq : (I ^ n • ⊤ : Ideal R) = I ^ n := by
          ext
          simp
        show AdicCompletion.eval I R n x = 0 ↔
          Ideal.quotientEquivAlgOfEq R hEq (AdicCompletion.eval I R n x) = 0
        exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R hEq).injective).symm
  have hle : I ^ n ≤ (J ^ n).comap (algebraMap R (AdicCompletion I R)) := by
    rw [hker]
    exact fun x hx => (AdicCompletion.evalₐ_of I n x).trans (Ideal.Quotient.eq_zero_iff_mem.2 hx)
  refine ⟨RingEquiv.ofBijective _ (bijective_quotientMap_of_ker_eq (I ^ n) (J ^ n)
    (algebraMap R (AdicCompletion I R)) (AdicCompletion.evalₐ I n).toRingHom
    hker.symm (AdicCompletion.evalₐ_of I n) hle),
    fun r => rfl⟩

end

section

universe u v w x

private theorem tensorProduct_nontrivial_of_retract
    {R : Type*} [CommRing R] {M A C : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]
    (F : A →ₗ[R] C) (G : C →ₗ[R] A) (h : G ∘ₗ F = LinearMap.id)
    [Nontrivial (TensorProduct R M A)] : Nontrivial (TensorProduct R M C) :=
  Function.Injective.nontrivial (f := TensorProduct.map (LinearMap.id (R := R) (M := M)) F)
    (Function.LeftInverse.injective (g := TensorProduct.map LinearMap.id G) fun x => by
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, h]
      simp)

private theorem tensorProduct_prod_away_nontrivial
    (R : Type u) [CommRing R] (f : R)
    (A : Type x) [CommRing A] [Algebra R A]
    (M : Type w) [AddCommGroup M] [Module R M] [Nontrivial M]
    (hbase : (∀ m : M, ∃ n : ℕ, ∀ r ∈ (Ideal.span {f}) ^ n, r • m = 0) →
      Function.Bijective (fun m : M => TensorProduct.mk R M A m 1)) :
    Nontrivial (TensorProduct R M (A × Localization.Away f)) := by
  by_cases hL : Nontrivial (TensorProduct R M (Localization.Away f))
  · let := hL
    exact tensorProduct_nontrivial_of_retract (LinearMap.inr R A (Localization.Away f))
      (LinearMap.snd R A (Localization.Away f)) (LinearMap.snd_comp_inr R A _)
  · have : Subsingleton (TensorProduct R M (Localization.Away f)) :=
      not_nontrivial_iff_subsingleton.mp hL
    have hM : ∀ m : M, ∃ n : ℕ, ∀ r ∈ (Ideal.span {f}) ^ n, r • m = 0 := by
      intro m
      have hzero : m ⊗ₜ[R] (1 : Localization.Away f) = 0 := Subsingleton.elim _ _
      have heq : (TensorProduct.mk R (Localization.Away f) M 1) m =
          (TensorProduct.mk R (Localization.Away f) M 1) 0 := by
        simpa using congrArg (TensorProduct.comm R M (Localization.Away f)) hzero
      obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq
        (S := Submonoid.powers f)
        (f := TensorProduct.mk R (Localization.Away f) M 1) heq
      obtain ⟨n, hn : f ^ n = s⟩ := s.property
      change (s : R) • m = (s : R) • (0 : M) at hs
      refine ⟨n, fun r hr => ?_⟩
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hr
      obtain ⟨a, rfl⟩ := hr
      rw [mul_comm, mul_smul, hn, hs, smul_zero, smul_zero]
    let : Nontrivial (TensorProduct R M A) := Function.Injective.nontrivial (hbase hM).1
    exact tensorProduct_nontrivial_of_retract (LinearMap.inl R A (Localization.Away f))
      (LinearMap.fst R A (Localization.Away f)) (LinearMap.fst_comp_inl R A _)

/-- If `R → S` induces isomorphisms modulo every positive power of `(f)`, then tensoring
with `S ⊕ R_f` detects nonzero modules. In particular, tensoring with `R^∧ ⊕ R_f`, where
`R^∧` is the `(f)`-adic completion, detects nonzero modules. -/
@[stacks 0BNL]
public theorem tensorProduct_prod_away_nontrivial_of_quotientMap_bijective
    (R : Type u) [CommRing R] (f : R) :
    (∀ (S : Type v) [CommRing S] [Algebra R S],
      (∀ n : ℕ, 0 < n →
        Function.Bijective
          (Ideal.quotientMap
            (Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n))
            (algebraMap R S) Ideal.le_comap_map)) →
      ∀ (M : Type w) [AddCommGroup M] [Module R M] [Nontrivial M],
        Nontrivial (TensorProduct R M (S × Localization.Away f))) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module R M] [Nontrivial M],
      Nontrivial
        (TensorProduct R M
          (AdicCompletion (Ideal.span {f}) R × Localization.Away f))) := by
  constructor
  · intro S _ _ hS M _ _ _
    exact tensorProduct_prod_away_nontrivial R f S M fun hM =>
      (_root_.tensorProduct_mk_bijective_of_ideal_power_torsion
        R (Ideal.span {f}) M hM).1 S hS
  · intro M _ _ _
    exact tensorProduct_prod_away_nontrivial R f (AdicCompletion (Ideal.span {f}) R) M fun hM => by
      have hK := _root_.tensorProduct_mk_bijective_of_ideal_power_torsion
        R (Ideal.span {f}) M hM
      have _hfix := hK.1 R
      exact hK.2 (Submodule.fg_span_singleton f)

end

section

private theorem primeSpectrumCoverOfQuotientMapBijective
    {R S : Type*} [CommRing R] (f : R) [CommRing S] (φ : R →+* S)
    (h : Function.Bijective
      (Ideal.quotientMap (Ideal.map φ (Ideal.span {f})) φ Ideal.le_comap_map)) :
    Function.Surjective
      (Sum.elim (PrimeSpectrum.comap φ)
        (PrimeSpectrum.comap (algebraMap R (Localization.Away f)))) := by
  intro p
  by_cases hp : f ∈ p.asIdeal
  · let I : Ideal R := Ideal.span {f}
    let J : Ideal S := Ideal.map φ I
    let qmap : (R ⧸ I) →+* (S ⧸ J) :=
      Ideal.quotientMap J φ Ideal.le_comap_map
    have hI : I ≤ p.asIdeal := Ideal.span_le.2 (Set.singleton_subset_iff.2 hp)
    let pbar : PrimeSpectrum (R ⧸ I) :=
      ⟨p.asIdeal.map (Ideal.Quotient.mk I),
        p.asIdeal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
          (by simpa only [Ideal.mk_ker] using hI)⟩
    let e : (R ⧸ I) ≃+* (S ⧸ J) := RingEquiv.ofBijective qmap h
    have := pbar.isPrime
    let qbar : PrimeSpectrum (S ⧸ J) :=
      ⟨pbar.asIdeal.map e.toRingHom,
        pbar.asIdeal.map_isPrime_of_surjective e.surjective
          (((RingHom.injective_iff_ker_eq_bot _).mp e.injective).trans_le bot_le)⟩
    let q : PrimeSpectrum S := PrimeSpectrum.comap (Ideal.Quotient.mk J) qbar
    refine ⟨Sum.inl q, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap φ (Ideal.comap (Ideal.Quotient.mk J) qbar.asIdeal) = p.asIdeal
    show Ideal.comap ((Ideal.Quotient.mk J).comp φ) qbar.asIdeal = p.asIdeal
    rw [← Ideal.quotientMap_comp_mk (f := φ) Ideal.le_comap_map]
    show Ideal.comap (qmap.comp (Ideal.Quotient.mk I)) qbar.asIdeal = p.asIdeal
    rw [← Ideal.comap_comap]
    show Ideal.comap (Ideal.Quotient.mk I) (Ideal.comap qmap qbar.asIdeal) = p.asIdeal
    have he : Ideal.comap qmap qbar.asIdeal = pbar.asIdeal := by
      show Ideal.comap e.toRingHom (Ideal.map e.toRingHom pbar.asIdeal) = pbar.asIdeal
      simpa only [RingEquiv.toRingHom_eq_coe] using
        congrArg (Ideal.comap (e : (R ⧸ I) →+* (S ⧸ J)))
          (Ideal.map_comap_of_equiv e (I := pbar.asIdeal)) |>.trans
            (Ideal.comap_of_equiv e)
    rw [he]
    show Ideal.comap (Ideal.Quotient.mk I)
      (Ideal.map (Ideal.Quotient.mk I) p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    exact sup_eq_left.2 (by rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker])
  · have hp' : p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      simpa [PrimeSpectrum.mem_basicOpen] using hp
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f] at hp'
    obtain ⟨q, hq⟩ := hp'
    exact ⟨Sum.inr q, hq⟩

private theorem adicQuotientMapBijective {R : Type*} [CommRing R] (f : R) :
    Function.Bijective
      (Ideal.quotientMap
        (Ideal.map (algebraMap R (AdicCompletion (Ideal.span {f}) R))
          (Ideal.span {f}))
        (algebraMap R (AdicCompletion (Ideal.span {f}) R)) Ideal.le_comap_map) := by
  let I : Ideal R := Ideal.span {f}
  exact bijective_quotientMap_of_ker_eq I _ (algebraMap R (AdicCompletion I R))
    (AdicCompletion.evalOneₐ I).toRingHom
    (AdicCompletion.ker_evalOneₐ_eq_map I (Submodule.fg_span_singleton f))
    (AdicCompletion.evalOneₐ_of I) Ideal.le_comap_map

/-- If `R → S` is an isomorphism modulo `f`, then `Spec(S)` and `Spec(R_f)`
jointly cover `Spec(R)`. The same cover holds with the `(f)`-adic completion in
place of `S`. -/
@[stacks 0BNM]
public theorem primeSpectrum_cover_of_quotientMap_bijective {R : Type*} [CommRing R] (f : R) :
    (∀ {S : Type*} [CommRing S] (φ : R →+* S),
      Function.Bijective
          (Ideal.quotientMap (Ideal.map φ (Ideal.span {f})) φ Ideal.le_comap_map) →
        Function.Surjective
          (Sum.elim (PrimeSpectrum.comap φ)
            (PrimeSpectrum.comap (algebraMap R (Localization.Away f))))) ∧
      Function.Surjective
        (Sum.elim
          (PrimeSpectrum.comap
            (algebraMap R (AdicCompletion (Ideal.span {f}) R)))
          (PrimeSpectrum.comap (algebraMap R (Localization.Away f)))) := by
  refine ⟨fun φ h ↦ primeSpectrumCoverOfQuotientMapBijective f φ h, ?_⟩
  exact primeSpectrumCoverOfQuotientMapBijective f
    (algebraMap R (AdicCompletion (Ideal.span {f}) R)) (adicQuotientMapBijective f)

end

section

open scoped TensorProduct


universe u v w

private theorem finite_of_finite_tensorProduct_of_nontrivial
    (R : Type u) (A : Type v) (M : Type w) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    (detect : ∀ (Q : Type w) [AddCommGroup Q] [Module R Q] [Nontrivial Q],
      Nontrivial (TensorProduct R Q A))
    (h : Module.Finite A (TensorProduct R A M)) : Module.Finite R M := by
  classical
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp h.fg_top
  obtain ⟨N, hNfin, hsub⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite s hsfin
  have hbase : N.baseChange A = ⊤ := by
    apply le_antisymm le_top
    rw [← hs]
    exact Submodule.span_le.2 hsub
  have hN : N = ⊤ := by
    by_contra hn
    let Q := M ⧸ N
    let : Nontrivial Q := Submodule.Quotient.nontrivial_iff.mpr hn
    have : Nontrivial (TensorProduct R Q A) := detect Q
    have hrange :
        LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[R] A) N.subtype) =
          (N.baseChange A).restrictScalars R := rfl
    have : Subsingleton ((TensorProduct R A M) ⧸
        LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[R] A) N.subtype)) := by
      rw [hrange, hbase, Submodule.restrictScalars_top]
      infer_instance
    have : Subsingleton (TensorProduct R A Q) :=
      Equiv.subsingleton (TensorProduct.tensorQuotientEquiv A N).toEquiv
    have : Subsingleton (TensorProduct R Q A) :=
      Equiv.subsingleton (TensorProduct.comm R Q A).toEquiv
    exact (not_nontrivial (TensorProduct R Q A)) inferInstance
  exact Module.Finite.of_surjective N.subtype fun x ↦
    ⟨⟨x, by simp [hN]⟩, rfl⟩

/-- Finite generation of a module is detected after extension of scalars to the product of
an algebra inducing isomorphisms modulo every positive power of `(f)` and the localization
away from `f`. In particular, it is detected by the product of the `(f)`-adic completion and
that localization. -/
@[stacks 0BNN]
public theorem finite_iff_tensorProduct_prod_away_of_quotientMap_bijective
    (R : Type u) [CommRing R] (f : R) :
    (∀ (S : Type v) [CommRing S] [Algebra R S],
      (∀ n : ℕ, 0 < n →
        Function.Bijective
          (Ideal.quotientMap
            (Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n))
            (algebraMap R S) Ideal.le_comap_map)) →
      ∀ (M : Type w) [AddCommGroup M] [Module R M],
        Module.Finite R M ↔
          Module.Finite (S × Localization.Away f)
            (TensorProduct R (S × Localization.Away f) M)) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module R M],
      Module.Finite
          (AdicCompletion (Ideal.span {f}) R × Localization.Away f)
          (TensorProduct R
            (AdicCompletion (Ideal.span {f}) R × Localization.Away f) M) →
        Module.Finite R M) := by
  constructor
  · intro S _ _ hquot M _ _
    refine ⟨fun _ => inferInstance, finite_of_finite_tensorProduct_of_nontrivial R _ M ?_⟩
    intro Q _ _ _
    exact (tensorProduct_prod_away_nontrivial_of_quotientMap_bijective R f).1 S hquot Q
  · intro M _ _
    apply finite_of_finite_tensorProduct_of_nontrivial R _ M
    intro Q _ _ _
    exact tensorProduct_prod_away_nontrivial_of_quotientMap_bijective.{u, v, w} R f |>.2 Q

end

end BeauvilleLaszlo

end
