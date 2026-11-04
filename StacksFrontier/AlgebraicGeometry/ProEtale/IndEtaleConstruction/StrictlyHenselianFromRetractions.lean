module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.StrictHenselizationColimit
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Flat.Prod
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.RingTheory.Spectrum.Prime.Specialization

/-!
# Strict henselianity from sections of étale covers

If every faithfully flat étale algebra over a ring `A` admits a retraction, then the
localization of `A` at each maximal ideal is strictly henselian.

The argument is local at a maximal ideal `m`. For an étale algebra `A → B` and a prime
`q ⊆ B` over `m`, étaleness is quasi-finite, so `q` can be isolated from the other primes of
the fibre by a single element `g ∉ q`; the image of `Spec (B_g) → Spec A` is open and contains
`m`, so one further principal open `D(f)` with `f ∈ m` completes it to a cover of `Spec A`.
The resulting `A → B_g × A_f` is faithfully flat and étale, so by hypothesis it retracts, and
the retraction is again étale, hence flat. Localizing at `m` turns the retraction into a flat
local section of `A_m → B_q`, and a flat local homomorphism of local rings with a flat local
section is an isomorphism. The strict henselization of `A_m` is a filtered colimit of such
localizations, so `A_m` is already strictly henselian.

## Main results

* `localizationAtPrime_strictlyHenselian_of_etale_faithfullyFlat_retracts`: the localizations
  of `A` at its maximal ideals are strictly henselian when every faithfully flat étale
  `A`-algebra admits a retraction.

## Implementation notes

A retraction of the structure map `A → B` is expressed as an `A`-algebra homomorphism
`B →ₐ[A] A`. Maximality is supplied as a typeclass so that the standard local-ring structure
on `Localization.AtPrime m` is available directly.

## References

* [Stacks Project, Tag 097V](https://stacks.math.columbia.edu/tag/097V)
-/

open CategoryTheory CategoryTheory.Limits IsLocalRing

@[expose] public section

universe u

namespace AlgebraicGeometry.ProEtale

/-- A retraction of an étale algebra is flat. -/
private theorem flat_of_etale_retraction {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] (σ : B →ₐ[A] A) :
    letI : Algebra B A := σ.toRingHom.toAlgebra
    Module.Flat B A := by
  let hf : (algebraMap A B).Etale :=
    RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A B)
  have hσ : σ.toRingHom.Etale := by
    apply RingHom.Etale.of_comp (RingHom.Etale.formallyUnramified _ hf)
      (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType A B))
    have hid : ((σ : B →+* A).comp (algebraMap A B)) = RingHom.id A := by
      ext x; exact σ.commutes x
    show ((σ : B →+* A).comp (algebraMap A B)).Etale
    rw [hid]; exact RingHom.Etale.of_bijective Function.bijective_id
  let : Algebra B A := σ.toRingHom.toAlgebra
  let : Algebra.Etale B A := hσ.toAlgebra
  infer_instance

/-- In a quasi-finite fibre, one can choose a principal open containing exactly a prescribed
prime of the fibre. -/
private theorem isolate_prime_in_quasiFinite_fiber {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.QuasiFinite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    ∃ g : S, g ∉ q ∧
      ∀ (q' : Ideal S) [q'.IsPrime] [q'.LiesOver p], q' ≠ q → g ∈ q' := by
  classical
  let : Fintype (p.primesOver S) := (Algebra.QuasiFinite.finite_primesOver (S := S) p).fintype
  let q₀ : p.primesOver S := Ideal.primesOver.mk p q
  have hsel (t : p.primesOver S) (ht : t ≠ q₀) :
      ∃ x : S, x ∈ (t : Ideal S) ∧ x ∉ q := by
    have hnot : ¬(t : Ideal S) ≤ q := fun hle ↦
      ht (Subtype.ext (Algebra.QuasiFiniteAt.eq_of_le_of_under_eq (R := R) hle
        ((t.1.over_def p).symm.trans (q.over_def p))))
    exact SetLike.not_le_iff_exists.mp hnot
  let f (t : p.primesOver S) : S :=
    if ht : t = q₀ then 1 else Classical.choose (hsel t ht)
  let s := (Finset.univ : Finset (p.primesOver S)).erase q₀
  let g := ∏ t ∈ s, f t
  refine ⟨g, ?_, ?_⟩
  · show g ∈ q.primeCompl
    apply q.primeCompl.prod_mem
    intro t ht
    have hne : t ≠ q₀ := (Finset.mem_erase.mp ht).1
    simp only [f, dite_eq_right hne]
    exact (Classical.choose_spec (hsel t hne)).2
  · intro q' _ _ hne
    let t : p.primesOver S := Ideal.primesOver.mk p q'
    have ht : t ≠ q₀ := fun heq ↦ hne (congrArg Subtype.val heq)
    have htmem : t ∈ s := Finset.mem_erase.mpr ⟨ht, Finset.mem_univ _⟩
    have hft : f t ∈ q' := by
      simp only [f, dite_eq_right ht]
      exact (Classical.choose_spec (hsel t ht)).1
    exact Ideal.mem_of_dvd q' (Finset.dvd_prod_of_mem f htmem) hft

/-- If an open subset of an affine spectrum contains a closed point, one principal open
complements it to a cover while avoiding that closed point. -/
private theorem exists_basicOpen_compl_cover_of_isOpen_at_maximal {A : Type*}
    [CommRing A] (m : Ideal A) [m.IsMaximal]
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U)
    (hm : (⟨m, inferInstance⟩ : PrimeSpectrum A) ∈ U) :
    ∃ f : A, f ∈ m ∧ ∀ x : PrimeSpectrum A, x ∈ U ∨ x ∈ PrimeSpectrum.basicOpen f := by
  obtain ⟨V, ⟨i, rfl⟩, hiV, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hm hU
  have hi : i ∉ m := (PrimeSpectrum.mem_basicOpen i _).mp hiV
  have hone : (1 : A) ∈ m ⊔ Ideal.span {i} :=
    (Ideal.isMaximal_iff.mp (inferInstance : m.IsMaximal)).2 _ i le_sup_left hi
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton i)))
  obtain ⟨f, hf, j, hj, hsum⟩ := Submodule.mem_sup.mp hone
  refine ⟨f, hf, fun x => ?_⟩
  by_cases hx : x ∈ U
  · exact Or.inl hx
  · right
    rw [PrimeSpectrum.mem_basicOpen]
    intro hfx
    have hix : i ∈ x.asIdeal := by
      by_contra hix
      exact hx (hsub ((PrimeSpectrum.mem_basicOpen i x).mpr hix))
    have hjx : j ∈ x.asIdeal := Ideal.span_le.mpr (by simpa using hix) hj
    have h1x : (1 : A) ∈ x.asIdeal := hsum ▸ x.asIdeal.add_mem hfx hjx
    exact x.isPrime.ne_top (x.asIdeal.eq_top_iff_one.mpr h1x)

/-- A binary product of étale algebras is étale. -/
private theorem etale_prod {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra A C] [Algebra.Etale A B] [Algebra.Etale A C] :
    Algebra.Etale A (B × C) := by
  let F : Fin 2 → Type u := Fin.cases B (fun _ => C)
  let : ∀ i, CommRing (F i) := by
    intro i
    cases i using Fin.cases with
    | zero => change CommRing B; infer_instance
    | succ j => change CommRing C; infer_instance
  let : ∀ i, Algebra A (F i) := by
    intro i
    cases i using Fin.cases with
    | zero => change Algebra A B; infer_instance
    | succ j => change Algebra A C; infer_instance
  let : ∀ i, Algebra.Etale A (F i) := by
    intro i
    cases i using Fin.cases with
    | zero => change Algebra.Etale A B; infer_instance
    | succ j => change Algebra.Etale A C; infer_instance
  let : Algebra.Etale A (∀ i, F i) := inferInstance
  let e : (∀ i, F i) ≃ₐ[A] (B × C) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo F) (by intro a; apply Prod.ext <;> rfl)
  exact Algebra.Etale.of_equiv e

/-- A pair of flat algebras whose spectra cover the base forms a faithfully flat algebra. -/
private theorem faithfullyFlat_prod_of_range_cover {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.Flat A B] [Module.Flat A C]
    (hcover : ∀ p : PrimeSpectrum A,
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) ∨
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap A C))) :
    Module.FaithfullyFlat A (B × C) := by
  apply RingHom.faithfullyFlat_algebraMap_iff.mp
  apply RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
  refine ⟨RingHom.flat_algebraMap_iff.mpr Module.Flat.prod, fun p => ?_⟩
  rcases hcover p with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · exact ⟨PrimeSpectrum.comap (RingHom.fst B C) q, rfl⟩
  · exact ⟨PrimeSpectrum.comap (RingHom.snd B C) q, rfl⟩

/-- A chosen point of an étale fibre can be isolated in a faithfully flat étale cover whose
second component avoids the chosen maximal ideal. -/
private theorem exists_etale_cover_retraction {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B]
    (h : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra.Etale A T]
      [Module.FaithfullyFlat A T], Nonempty (T →ₐ[A] A))
    (m : Ideal A) [m.IsMaximal] (q : Ideal B) [q.IsPrime] [q.LiesOver m] :
    ∃ g : B, g ∉ q ∧
      (∀ (q' : Ideal B) [q'.IsPrime] [q'.LiesOver m], q' ≠ q → g ∈ q') ∧
      ∃ f : A, f ∈ m ∧
        Nonempty ((Localization.Away g × Localization.Away f) →ₐ[A] A) := by
  have : Algebra.QuasiFinite A B := RingHom.quasiFinite_algebraMap.mp
    (RingHom.Etale.quasiFinite (algebraMap A B)
      (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A B)))
  obtain ⟨g, hg, hgone⟩ := isolate_prime_in_quasiFinite_fiber m q
  let C := Localization.Away g
  let U : Set (PrimeSpectrum A) := Set.range (PrimeSpectrum.comap (algebraMap A C))
  have hU : IsOpen U := by
    have hopen := PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := A) (S := C)
    simpa [U] using hopen _ isOpen_univ
  have hmU : (⟨m, inferInstance⟩ : PrimeSpectrum A) ∈ U := by
    have hqrange : (⟨q, inferInstance⟩ : PrimeSpectrum B) ∈
        Set.range (PrimeSpectrum.comap (algebraMap B C)) := by
      rw [PrimeSpectrum.localization_away_comap_range C g]
      exact (PrimeSpectrum.mem_basicOpen g _).mpr hg
    obtain ⟨r, hr⟩ := hqrange
    refine ⟨r, ?_⟩
    calc
      PrimeSpectrum.comap (algebraMap A C) r =
          PrimeSpectrum.comap (algebraMap A B)
            (PrimeSpectrum.comap (algebraMap B C) r) := rfl
      _ = PrimeSpectrum.comap (algebraMap A B) (⟨q, inferInstance⟩ : PrimeSpectrum B) :=
        congrArg _ hr
      _ = (⟨m, inferInstance⟩ : PrimeSpectrum A) := by
        apply PrimeSpectrum.ext
        exact (q.over_def m).symm
  obtain ⟨f, hf, hcover⟩ := exists_basicOpen_compl_cover_of_isOpen_at_maximal m U hU hmU
  let D := Localization.Away f
  have hcover' : ∀ p : PrimeSpectrum A,
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap A C)) ∨
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap A D)) := fun p ↦
    (hcover p).imp id fun hd ↦ by rwa [PrimeSpectrum.localization_away_comap_range D f]
  let : Algebra.Etale A (C × D) := etale_prod
  let : Module.FaithfullyFlat A (C × D) :=
    faithfullyFlat_prod_of_range_cover hcover'
  exact ⟨g, hg, hgone, f, hf, h (C × D)⟩

/-- In a retraction from `C × A_f` to `A`, the idempotent of the second component lies in any
ideal containing `f`. -/
private theorem prod_retraction_second_idempotent_mem {A C : Type*}
    [CommRing A] [CommRing C] [Algebra A C]
    (m : Ideal A) (f : A) (hf : f ∈ m)
    (σ : (C × Localization.Away f) →ₐ[A] A) : σ (0, 1) ∈ m := by
  let D := Localization.Away f
  let hfunit : IsUnit (algebraMap A D f) := IsLocalization.Away.algebraMap_isUnit f
  obtain ⟨u, hu⟩ := hfunit.exists_right_inv
  have heq : σ (0, 1) = f * σ (0, u) := by
    calc
      σ (0, 1) = σ ((algebraMap A (C × D) f) * (0, u)) := by
        congr 1
        ext <;> simp [Prod.algebraMap_apply, hu]
      _ = σ (algebraMap A (C × D) f) * σ (0, u) := σ.map_mul _ _
      _ = f * σ (0, u) := by
        rw [σ.commutes, Algebra.algebraMap_self_apply]
  rw [heq]
  exact m.mul_mem_right _ hf

/-- The complementary idempotent of the first component becomes one after localization at
the chosen maximal ideal. -/
private theorem prod_retraction_first_idempotent_map_eq_one {A C : Type*}
    [CommRing A] [CommRing C] [Algebra A C]
    (m : Ideal A) [m.IsPrime] (f : A) (hf : f ∈ m)
    (σ : (C × Localization.Away f) →ₐ[A] A) :
    (algebraMap A (Localization.AtPrime m)) (σ (1, 0)) = 1 := by
  have he₂ : σ (0, 1) ∈ m := prod_retraction_second_idempotent_mem m f hf σ
  have hsum : σ (1, 0) + σ (0, 1) = 1 := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk_one_one, map_one]
  have he₁ : σ (1, 0) ∉ m := by
    intro he
    have h1 : (1 : A) ∈ m := hsum ▸ m.add_mem he he₂
    exact (inferInstance : m.IsPrime).ne_top (m.eq_top_iff_one.mpr h1)
  let R := Localization.AtPrime m
  have hunit : IsUnit ((algebraMap A R) (σ (1, 0))) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff R m (σ (1, 0))).mpr he₁
  have hidem : IsIdempotentElem ((algebraMap A R) (σ (1, 0))) := by
    have he : IsIdempotentElem ((1, 0) : C × Localization.Away f) := by
      show ((1, 0) : C × Localization.Away f) * (1, 0) = (1, 0)
      ext <;> simp
    exact (he.map σ).map (algebraMap A R)
  exact (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp hidem

/-- A retraction of `C × A_f` induces a section from the first component after localizing
at a maximal ideal containing `f`. -/
private theorem exists_first_localAlgHom_of_prod_retraction {A C : Type*}
    [CommRing A] [CommRing C] [Algebra A C]
    (m : Ideal A) [m.IsPrime] (f : A) (hf : f ∈ m)
    (σ : (C × Localization.Away f) →ₐ[A] A) :
    ∃ τ : C →ₐ[A] Localization.AtPrime m,
      τ.toRingHom.comp (RingHom.fst C (Localization.Away f)) =
        (algebraMap A (Localization.AtPrime m)).comp σ.toRingHom := by
  let R := Localization.AtPrime m
  let T := C × Localization.Away f
  let : Algebra T C := (RingHom.fst C (Localization.Away f)).toAlgebra
  let : IsScalarTower A T C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let θ : T →ₐ[A] R := (IsScalarTower.toAlgHom A A R).comp σ
  have he : θ ((1, 0) : T) = 1 := prod_retraction_first_idempotent_map_eq_one m f hf σ
  have hu : IsUnit (θ ((1, 0) : T)) := he ▸ isUnit_one
  let τ : C →ₐ[A] R := IsLocalization.Away.liftAlgHom ((1, 0) : T) hu
  exact ⟨τ, IsLocalization.Away.lift_comp (S := C) (g := θ.toRingHom) ((1, 0) : T) hu⟩

/-- The induced map from the first component to the local ring is flat when the original
retraction is flat. -/
private theorem first_localAlgHom_flat_of_prod_retraction {A C : Type*}
    [CommRing A] [CommRing C] [Algebra A C]
    (m : Ideal A) [m.IsPrime] (f : A) (hf : f ∈ m)
    (σ : (C × Localization.Away f) →ₐ[A] A)
    (hσflat : σ.toRingHom.Flat) :
    ∃ τ : C →ₐ[A] Localization.AtPrime m,
      (τ : C →+* Localization.AtPrime m).Flat := by
  obtain ⟨τ, hcomp⟩ := exists_first_localAlgHom_of_prod_retraction m f hf σ
  let R := Localization.AtPrime m
  let D := Localization.Away f
  let T := C × D
  let ρ : A →+* R := algebraMap A R
  let : Algebra T C := (RingHom.fst C D).toAlgebra
  let : Algebra C R := τ.toRingHom.toAlgebra
  let : Algebra T R := (ρ.comp σ.toRingHom).toAlgebra
  have : IsScalarTower T C R := IsScalarTower.of_algebraMap_eq fun t =>
    congrArg (fun v : T →+* R => v t) hcomp.symm
  have hTR : Module.Flat T R :=
    RingHom.flat_algebraMap_iff.mp
      (hσflat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance))
  have hCR : Module.Flat C R :=
    (Module.flat_iff_of_isLocalization C (Submonoid.powers ((1, 0) : T)) R).mpr hTR
  exact ⟨τ, RingHom.flat_algebraMap_iff.mpr hCR⟩

/-- An isolated point of the fibre selects a flat local map from its local ring to the
localization of the base. -/
private theorem localAlgHom_of_isolated_prime {A B : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) [m.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver m]
    (g : B)
    (hgone : ∀ (q' : Ideal B) [q'.IsPrime] [q'.LiesOver m], q' ≠ q → g ∈ q')
    (τ : Localization.Away g →ₐ[A] Localization.AtPrime m)
    (hτflat : τ.toRingHom.Flat) :
    ∃ φ : Localization.AtPrime q →ₐ[A] Localization.AtPrime m,
      φ.toRingHom.Flat ∧ IsLocalHom φ.toRingHom := by
  let C := Localization.Away g
  let R := Localization.AtPrime m
  let Bq := Localization.AtPrime q
  let j : B →ₐ[A] C := IsScalarTower.toAlgHom A B C
  let θ : B →ₐ[A] R := τ.comp j
  have hjflat : j.toRingHom.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hθflat : θ.toRingHom.Flat := hjflat.comp hτflat
  let Q : Ideal B := (IsLocalRing.maximalIdeal R).comap θ.toRingHom
  have : Q.LiesOver m := ⟨by
    show m = ((IsLocalRing.maximalIdeal R).comap θ.toRingHom).comap (algebraMap A B)
    rw [Ideal.comap_comap]
    have hc : θ.toRingHom.comp (algebraMap A B) = algebraMap A R := by
      ext a
      exact θ.commutes a
    rw [hc]
    exact (Localization.AtPrime.under_maximalIdeal (I := m)).symm⟩
  have hgQ : g ∉ Q := by
    have hu : IsUnit (θ g) := by
      show IsUnit (τ ((algebraMap B C) g))
      exact (IsLocalization.Away.algebraMap_isUnit g).map τ
    intro hmem
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)) hu
  have hQ : Q = q := by_contra fun hne ↦ hgQ (hgone Q hne)
  have hunits : ∀ s : q.primeCompl, IsUnit (θ s.1) := fun s ↦ by_contra fun hnu ↦
    (show s.1 ∉ Q from hQ.symm ▸ s.2)
      ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
  let φ : Bq →ₐ[A] R := IsLocalization.liftAlgHom (M := q.primeCompl) (f := θ) hunits
  let : Algebra B R := θ.toRingHom.toAlgebra
  let : Algebra Bq R := φ.toRingHom.toAlgebra
  have : IsScalarTower B Bq R := IsScalarTower.of_algebraMap_eq fun b => by
    show θ b = φ ((algebraMap B Bq) b)
    exact (IsLocalization.lift_eq hunits b).symm
  have hBR : Module.Flat B R := RingHom.flat_algebraMap_iff.mp hθflat
  have hBqR : Module.Flat Bq R :=
    (Module.flat_iff_of_isLocalization Bq q.primeCompl R).mpr hBR
  have hφlocal : IsLocalHom φ.toRingHom := IsLocalHom.mk fun x hx => by
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    have heq : φ (IsLocalization.mk' Bq b s) =
        θ b * φ (IsLocalization.mk' Bq 1 s) := by
      rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul]
      exact congrArg (· * φ (IsLocalization.mk' Bq 1 s))
        (IsLocalization.lift_eq hunits b)
    change IsUnit (φ (IsLocalization.mk' Bq b s)) at hx
    rw [heq] at hx
    have hbunit : IsUnit (θ b) := isUnit_of_mul_isUnit_left hx
    intro hbq
    have hbm : θ b ∈ IsLocalRing.maximalIdeal R := show b ∈ Q from hQ ▸ hbq
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hbm)) hbunit
  exact ⟨φ, RingHom.flat_algebraMap_iff.mpr hBqR, hφlocal⟩

/-- Two `A`-algebra maps out of a localization of `A` at a prime are equal. -/
private theorem algHom_atPrime_ext {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    {m : Ideal A} [m.IsPrime] (f g : Localization.AtPrime m →ₐ[A] S) : f = g :=
  haveI := IsLocalization.algHom_subsingleton (S := Localization.AtPrime m) m.primeCompl
    (P := S)
  Subsingleton.elim _ _

/-- A flat local section of a localization forces the localization map to be an isomorphism. -/
private theorem localAlgEquiv_of_flat_local_section {A B : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) [m.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver m]
    (φ : Localization.AtPrime q →ₐ[A] Localization.AtPrime m)
    (hφflat : φ.toRingHom.Flat) (hφlocal : IsLocalHom φ.toRingHom) :
    Nonempty (Localization.AtPrime m ≃ₐ[A] Localization.AtPrime q) := by
  let R := Localization.AtPrime m
  let Bq := Localization.AtPrime q
  let α : R →ₐ[A] Bq :=
    Localization.localAlgHom m q (Algebra.ofId A B) (q.over_def m)
  have hcomp : φ.comp α = AlgHom.id A R := algHom_atPrime_ext _ _
  let : Algebra Bq R := φ.toRingHom.toAlgebra
  let : Module.Flat Bq R := RingHom.flat_algebraMap_iff.mp hφflat
  let : IsLocalHom (algebraMap Bq R) := hφlocal
  let : Module.FaithfullyFlat Bq R := .of_flat_of_isLocalHom
  have hφinj : Function.Injective φ := FaithfulSMul.algebraMap_injective Bq R
  have hαsurj : Function.Surjective α := fun b ↦
    ⟨φ b, hφinj (DFunLike.congr_fun hcomp (φ b))⟩
  have hαinj : Function.Injective α := by
    intro x y hxy
    simpa only [← AlgHom.comp_apply, hcomp, AlgHom.id_apply] using congrArg φ hxy
  exact ⟨AlgEquiv.ofBijective α ⟨hαinj, hαsurj⟩⟩

/-- Under the section hypothesis, every point of an étale fibre over a maximal ideal has
the same local ring as the base. -/
private theorem etale_localization_algEquiv_of_sections {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (h : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra.Etale A T]
      [Module.FaithfullyFlat A T], Nonempty (T →ₐ[A] A))
    (m : Ideal A) [m.IsMaximal] (q : Ideal B) [q.IsPrime] [q.LiesOver m] :
    Nonempty (Localization.AtPrime m ≃ₐ[A] Localization.AtPrime q) := by
  obtain ⟨g, hg, hgone, f, hf, ⟨σ⟩⟩ := exists_etale_cover_retraction h m q
  let : Algebra.Etale A (Localization.Away g × Localization.Away f) := etale_prod
  let : Algebra (Localization.Away g × Localization.Away f) A := σ.toRingHom.toAlgebra
  obtain ⟨τ, hτflat⟩ := first_localAlgHom_flat_of_prod_retraction m f hf σ
    (RingHom.flat_algebraMap_iff.mpr (flat_of_etale_retraction σ))
  obtain ⟨φ, hφflat, hφlocal⟩ :=
    localAlgHom_of_isolated_prime m q g hgone τ hτflat
  exact localAlgEquiv_of_flat_local_section m q φ hφflat hφlocal

/-- If every faithfully flat étale algebra over `A` has a retraction, then the localization
of `A` at any maximal ideal is strictly henselian. -/
@[stacks 097V]
theorem localizationAtPrime_strictlyHenselian_of_etale_faithfullyFlat_retracts
    (A : Type u) [CommRing A]
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
      [Module.FaithfullyFlat A B], Nonempty (B →ₐ[A] A))
    (m : Ideal A) [m.IsMaximal] :
    StrictlyHenselianLocalRing (Localization.AtPrime m) := by
  let R := Localization.AtPrime m
  let L := SeparableClosure (ResidueField R)
  let : Algebra A L :=
    ((algebraMap (ResidueField R) L).comp (algebraMap A (ResidueField R))).toAlgebra
  obtain ⟨Rh, hRhRing, hRhAlg, hRhLocal, hRhMapLocal, _, hRhInd, -, hRhRes⟩ :=
    IsLocalRing.exists_henselization R
  let : CommRing Rh := hRhRing
  let : Algebra R Rh := hRhAlg
  let : IsLocalRing Rh := hRhLocal
  let : IsLocalHom (algebraMap R Rh) := hRhMapLocal
  obtain ⟨Rsh, hRshRing, hRshLocal, hRRshAlg, _, _, _, hRshHens,
      hRshSep, hRshInd, _, eRsh, heRsh⟩ :=
    IsLocalRing.exists_strictHenselization R Rh hRhInd hRhRes.2 L
  let : CommRing Rsh := hRshRing
  let : IsLocalRing Rsh := hRshLocal
  let : Algebra R Rsh := hRRshAlg
  let : IsLocalRing.IsHenselization R L Rsh :=
    IsLocalRing.IsHenselization.of_ind_etale hRshHens hRshInd ⟨eRsh, heRsh⟩
  let : Algebra A Rsh :=
    ((algebraMap R Rsh).comp (algebraMap A R)).toAlgebra
  let : IsScalarTower A R Rsh := IsScalarTower.of_algebraMap_eq' rfl
  have he (a : A) : eRsh (algebraMap A L a) =
      algebraMap A (ResidueField Rsh) a := heRsh (algebraMap A R a)
  obtain ⟨hfilt, _, _, _, ⟨_⟩, ιLoc, _, ⟨hcLoc⟩⟩ :=
    IsLocalRing.IsHenselization.isFiltered_augmentedEtale_and_isColimit m Rsh eRsh he
  have hprime (X : CommAlgCat.AugmentedEtale A L) : X.prime.LiesOver m := by
    refine ⟨?_⟩
    apply Eq.symm; ext a
    show X.hom.hom (algebraMap A (X.left.obj : Type u) a) = 0 ↔ a ∈ m
    have hcomm : X.hom.hom (algebraMap A (X.left.obj : Type u) a) =
        (algebraMap A L) a := X.hom.hom.commutes a
    rw [hcomm]
    show (algebraMap (ResidueField R) L) ((algebraMap A (ResidueField R)) a) = 0 ↔ a ∈ m
    rw [← map_zero (algebraMap (ResidueField R) L),
      (RingHom.injective (algebraMap (ResidueField R) L)).eq_iff]
    exact Ideal.algebraMap_residueField_eq_zero
  let α (X : CommAlgCat.AugmentedEtale A L) :
      R →ₐ[A] Localization.AtPrime X.prime := by
    have : X.prime.LiesOver m := hprime X
    exact Localization.localAlgHom m X.prime
      (Algebra.ofId A (X.left.obj : Type u)) (X.prime.over_def m)
  let η : (Functor.const _).obj (CommAlgCat.of A R) ⟶
      CommAlgCat.AugmentedEtale.localization A L :=
    { app X := CommAlgCat.ofHom (α X)
      naturality X Y f := by
        show CommAlgCat.ofHom (α Y) =
          CommAlgCat.ofHom (α X) ≫ (CommAlgCat.AugmentedEtale.localization A L).map f
        exact CommAlgCat.hom_ext (algHom_atPrime_ext _ _)
    }
  have hpoint (X : CommAlgCat.AugmentedEtale A L) : IsIso (η.app X) := by
    let : X.prime.LiesOver m := hprime X
    obtain ⟨e⟩ := etale_localization_algEquiv_of_sections h m X.prime
    have heq : η.app X = (CommAlgCat.isoMk e).hom := by
      show CommAlgCat.ofHom (α X) = (CommAlgCat.isoMk e).hom
      exact CommAlgCat.hom_ext (algHom_atPrime_ext _ _)
    rw [heq]; infer_instance
  let ε : (Functor.const _).obj (CommAlgCat.of A R) ≅
      CommAlgCat.AugmentedEtale.localization A L :=
    NatIso.ofComponents (fun X => by
      have := hpoint X
      exact asIso (η.app X)) fun f ↦ η.naturality f
  let : IsFiltered (CommAlgCat.AugmentedEtale A L) := hfilt
  let : IsConnected (CommAlgCat.AugmentedEtale A L) :=
    IsFiltered.isConnected (CommAlgCat.AugmentedEtale A L)
  let c : Cocone (CommAlgCat.AugmentedEtale.localization A L) := Cocone.mk _ ιLoc
  let c' : Cocone ((Functor.const _).obj (CommAlgCat.of A R)) :=
    (Cocone.precompose ε.hom).obj c
  have hc' : IsColimit c' := (IsColimit.precomposeHomEquiv ε c).symm hcLoc
  let e : R ≃ₐ[A] Rsh := CommAlgCat.algEquivOfIso
    ((isColimitConstCocone (CommAlgCat.AugmentedEtale A L)
      (CommAlgCat.of A R)).coconePointUniqueUpToIso hc')
  let : HenselianLocalRing Rsh := hRshHens
  let : IsSepClosed (ResidueField Rsh) := hRshSep
  have : HenselianLocalRing R := HenselianLocalRing.of_ringEquiv e.symm.toRingEquiv
  have : IsSepClosed (ResidueField R) :=
    IsSepClosed.of_ringEquiv (ResidueField.mapEquiv e.toRingEquiv)
  exact ⟨⟩

end AlgebraicGeometry.ProEtale

end
