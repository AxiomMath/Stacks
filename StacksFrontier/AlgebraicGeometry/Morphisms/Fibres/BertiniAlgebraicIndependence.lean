module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimension
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension

/-!
# Algebraic independence from a codimension-two intersection

Let `A` be a domain of finite type over a field `k`, let `n ≥ 2` and let `g₁, …, gₙ ∈ A` be
elements such that `V(g₁, g₂)` has an irreducible component of dimension `dim A - 2`. Then there
are `c₁, …, cₙ ∈ k` for which the `n + 2` elements `x₁, …, xₙ`, `∑ gᵢxᵢ` and `∑ cᵢgᵢ` are
algebraically independent over `k`.

The irreducible component is a minimal prime `p` of the ideal `(g₁, g₂)` with
`dim(A/p) + 2 = dim A`, and the algebraic independence is stated in the polynomial ring
`A[x₁, …, xₙ]`.

## Main results

* `Algebra.exists_algebraicIndependent_linearCombinations`: there are coefficients `c₁, …, cₙ`
  for which `x₁, …, xₙ`, `∑ gᵢxᵢ` and `∑ cᵢgᵢ` are algebraically independent over `k`.

## References

* [Stacks Project, Tag 0G4E](https://stacks.math.columbia.edu/tag/0G4E)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace Algebra

/-- The local dimension of `Spec R` at a minimal prime `p` is the dimension of `R ⧸ p`. -/
private theorem localKrullDim_eq_quotient_of_minimalPrime
    (k : Type u) [Field k] {R : Type v} [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (p : Ideal R) [p.IsPrime]
    (hp : p ∈ minimalPrimes R) :
    TopologicalSpace.localKrullDim (PrimeSpectrum R) ⟨p, ‹p.IsPrime›⟩ =
      ringKrullDim (R ⧸ p) := by
  let x : PrimeSpectrum R := ⟨p, ‹p.IsPrime›⟩
  rw [(PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k x).1]
  let Z₀ := PrimeSpectrum.zeroLocus (p : Set R)
  have hZ₀ : Z₀ ∈ irreducibleComponents (PrimeSpectrum R) := by
    rwa [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents, (‹p.IsPrime›).radical]
  have hxZ₀ : x ∈ Z₀ := (PrimeSpectrum.mem_zeroLocus x _).2 le_rfl
  have hdim₀ : topologicalKrullDim Z₀ = ringKrullDim (R ⧸ p) :=
    topologicalKrullDim_zeroLocus p
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun Z ⟨hZcomp, hxZ⟩ ↦ ?_
    have hZclosed : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZcomp
    have hminZ : PrimeSpectrum.vanishingIdeal Z ∈ minimalPrimes R := by
      apply (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes).2
      rwa [hZclosed.closure_eq]
    have hZV : PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z : Set R) = Z := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZclosed.closure_eq]
    have hle : PrimeSpectrum.vanishingIdeal Z ≤ p := by
      apply (PrimeSpectrum.mem_zeroLocus x _).mp
      rwa [hZV]
    have hEq : PrimeSpectrum.vanishingIdeal Z = p := le_antisymm hle (hp.2 ⟨hminZ.1.1, bot_le⟩ hle)
    have hZeq : Z = Z₀ := by rw [← hZV, hEq]
    rw [hZeq]; exact hdim₀.le
  · exact le_iSup_of_le Z₀ (le_iSup_of_le ⟨hZ₀, hxZ₀⟩ hdim₀.symm.le)

/-- Contracting an ideal along a surjection does not change the dimension of the quotient. -/
private lemma ringKrullDim_quotient_comap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (q : Ideal S) :
    ringKrullDim (R ⧸ q.comap f) = ringKrullDim (S ⧸ q) := by
  have hsurj := Ideal.Quotient.mk_surjective (I := q) |>.comp hf
  have hker : RingHom.ker ((Ideal.Quotient.mk q).comp f) = q.comap f := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  rw [← hker]
  exact ringKrullDim_eq_of_ringEquiv
    (((Ideal.Quotient.mk q).comp f).quotientKerEquivOfSurjective hsurj)

/-- The local dimension of the zero locus `V(I)` at a minimal prime `p` of `I` is the dimension
of `R ⧸ p`. -/
private lemma topologicalKrullDimAt_zeroLocus_minimalPrime
    (k : Type u) [Field k] {R : Type v} [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ I.minimalPrimes) :
    topologicalKrullDimAt (PrimeSpectrum.zeroLocus (I : Set R)) ⟨p, hp.1.2⟩ =
      ringKrullDim (R ⧸ p.asIdeal) := by
  obtain ⟨q, hq, hqp⟩ := Ideal.minimalPrimes_eq_comap (I := I) ▸ hp
  have : q.IsPrime := hq.1.1
  let x : PrimeSpectrum (R ⧸ I) := ⟨q, ‹q.IsPrime›⟩
  have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  let e := (PrimeSpectrum.isEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective).toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hex : e x = ⟨p, hp.1.2⟩ := Subtype.ext (PrimeSpectrum.ext hqp)
  rw [← hex, ← topologicalKrullDimAt_eq_of_homeomorph,
    topologicalKrullDimAt_eq_localKrullDim,
    localKrullDim_eq_quotient_of_minimalPrime k q hq, ← hqp]
  exact (ringKrullDim_quotient_comap _ Ideal.Quotient.mk_surjective q).symm

/-- The lower bound for fibre dimensions, read on spectra: for a `k`-algebra map `f : A →ₐ[k] B`
between finite-type `k`-algebras with `B` a domain, the dimension of `B` is at most the local
dimension of the fibre of `Spec f` through a point plus the dimension of the image of `Spec f`.
-/
private lemma ringKrullDim_le_fiber_add_quotient
    (k A B : Type u) [Field k] [CommRing A] [CommRing B] [IsDomain B]
    [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    (f : A →ₐ[k] B) (x : PrimeSpectrum B) :
    ringKrullDim B ≤
      topologicalKrullDimAt (PrimeSpectrum.comap f.toRingHom ⁻¹'
        {PrimeSpectrum.comap f.toRingHom x}) ⟨x, rfl⟩ +
      ringKrullDim (A ⧸ RingHom.ker f) := by
  let X := AlgebraicGeometry.Spec (.of B)
  let Y := AlgebraicGeometry.Spec (.of A)
  let φ : X ⟶ Y := Spec.map (CommRingCat.ofHom f.toRingHom)
  let pX : X ⟶ AlgebraicGeometry.Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k B))
  let pY : Y ⟶ AlgebraicGeometry.Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k A))
  have hcomp : φ ≫ pY = pX := by
    rw [← Spec.map_comp]; congr 1; ext a; exact f.commutes a
  have : LocallyOfFiniteType pX := HasRingHomProperty.Spec_iff.mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : LocallyOfFiniteType pY := HasRingHomProperty.Spec_iff.mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hx : φ.fiberHomeo (φ x) (φ.asFiber x) = ⟨x, rfl⟩ :=
    (φ.fiberHomeo (φ x)).apply_symm_apply _
  let I := Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure (Set.range (fun x : X => φ x)))
  have hI : topologicalKrullDim I.subscheme = ringKrullDim (A ⧸ RingHom.ker f) := by
    have hrange : Set.range I.subschemeι = PrimeSpectrum.zeroLocus (RingHom.ker f : Set A) := by
      rw [I.range_subschemeι]
      show closure (Set.range (PrimeSpectrum.comap f.toRingHom)) = _
      exact PrimeSpectrum.closure_range_comap _
    exact ((I.subschemeι.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)).isHomeomorph.topologicalKrullDim_eq _).trans
        (topologicalKrullDim_zeroLocus _)
  have h := AlgebraicGeometry.topologicalKrullDim_le_fiber_add_imageClosure k pX pY φ hcomp x
  rw [topologicalKrullDimAt_eq_of_homeomorph (φ.fiberHomeo (φ x)), hx, hI] at h
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).symm.trans_le h

/-- A prime contracts to the kernel of an evaluation map exactly when it contains the
corresponding differences of a variable and a constant. -/
private lemma comap_aeval_eq_ker_eval_iff
    {σ k B : Type*} [Field k] [CommRing B] [Algebra k B]
    (f : MvPolynomial σ k →ₐ[k] B) (q : Ideal B) [q.IsPrime] (a : σ → k) :
    q.comap f = RingHom.ker (MvPolynomial.eval a) ↔
      ∀ i, f (MvPolynomial.X i) - algebraMap k B (a i) ∈ q := by
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · simpa using (show MvPolynomial.X i - MvPolynomial.C (a i) ∈ q.comap f by rw [h]; simp)
  · have hcomp : (Ideal.Quotient.mk q).comp f.toRingHom =
        (algebraMap k (B ⧸ q)).comp (MvPolynomial.eval a) :=
      MvPolynomial.ringHom_ext (fun r ↦ by simp) fun i ↦ by
        simpa [Ideal.Quotient.eq, sub_eq_zero] using Ideal.Quotient.eq_zero_iff_mem.mpr (h i)
    show q.comap f.toRingHom = _
    rw [← Ideal.mk_ker (I := q), RingHom.comap_ker, hcomp,
      RingHom.ker_comp_of_injective _ (algebraMap k (B ⧸ q)).injective]

/-- An ideal of a polynomial ring containing the differences of the variables and a point is
recovered from its contraction along the constants. -/
private lemma comap_eval_comap_C {σ R : Type*} [CommRing R]
    (q : Ideal (MvPolynomial σ R)) (a : σ → R)
    (h : ∀ i, MvPolynomial.X i - MvPolynomial.C (a i) ∈ q) :
    (q.comap MvPolynomial.C).comap (MvPolynomial.eval a) = q := by
  have hcomp : ((Ideal.Quotient.mk q).comp MvPolynomial.C).comp
      (MvPolynomial.eval a) = Ideal.Quotient.mk q :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp) fun i ↦ by
      simpa only [RingHom.comp_apply, MvPolynomial.eval_X] using (Ideal.Quotient.eq.mpr (h i)).symm
  rw [← Ideal.mk_ker (I := q), RingHom.comap_ker, RingHom.comap_ker, hcomp]

/-- The `k`-algebra map sending the variables to themselves, `y` to the generic linear
combination `∑ gᵢxᵢ` and `z` to the single coefficient `gⱼ`. -/
private noncomputable abbrev genericLinearMap
    (k : Type u) {A : Type v} [Field k] [CommRing A] [Algebra k A]
    {n : ℕ} (g : Fin n → A) (j : Fin n) :
    MvPolynomial (Fin n ⊕ Fin 2) k →ₐ[k] MvPolynomial (Fin n) A :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X
    (fun b : Fin 2 ↦ if b = 0 then
      ∑ i, MvPolynomial.C (g i) * MvPolynomial.X i else MvPolynomial.C (g j)))

/-- The fibre of `Spec` of the generic linear map over the point obtained by setting the
variables to the `i`-th unit vector and both linear combinations to zero is the image of the zero
locus of `(gᵢ, gⱼ)`. -/
private lemma genericLinearMap_fiber
    (k : Type u) {A : Type v} [Field k] [CommRing A] [Algebra k A]
    {n : ℕ} (g : Fin n → A) (i j : Fin n) :
    let f := genericLinearMap k g j
    let a : Fin n → A := Pi.single i 1
    let s : Fin n ⊕ Fin 2 → k := Sum.elim (Pi.single i 1) (fun _ => 0)
    let y := PrimeSpectrum.comap (MvPolynomial.eval s) (⊥ : PrimeSpectrum k)
    PrimeSpectrum.comap f.toRingHom ⁻¹' {y} =
      PrimeSpectrum.comap (MvPolynomial.eval a) ''
        PrimeSpectrum.zeroLocus (Ideal.span {g i, g j} : Set A) := by
  classical
  dsimp only
  let f := genericLinearMap k g j
  let a : Fin n → A := Pi.single i 1
  let s : Fin n ⊕ Fin 2 → k := Sum.elim (Pi.single i 1) (fun _ ↦ 0)
  have ha (l : Fin n) : algebraMap k A ((Pi.single i 1 : Fin n → k) l) = a l := by
    by_cases h : l = i <;> simp [a, h]
  have hev : MvPolynomial.eval a (∑ l, MvPolynomial.C (g l) * MvPolynomial.X l) = g i := by
    simp [a, map_sum, Pi.single_apply, Finset.sum_ite_eq', mul_ite]
  ext q
  show PrimeSpectrum.comap f.toRingHom q =
    PrimeSpectrum.comap (MvPolynomial.eval s) ⊥ ↔ _
  rw [PrimeSpectrum.ext_iff]
  show q.asIdeal.comap f = RingHom.ker (MvPolynomial.eval s) ↔ _
  rw [comap_aeval_eq_ker_eval_iff]
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hX (l : Fin n) : MvPolynomial.X l - MvPolynomial.C (a l) ∈ q.asIdeal := by
      simpa [f, genericLinearMap, s, ← ha l, MvPolynomial.algebraMap_eq] using h (.inl l)
    have hq := comap_eval_comap_C q.asIdeal a hX
    let p := PrimeSpectrum.comap MvPolynomial.C q
    have hpq : PrimeSpectrum.comap (MvPolynomial.eval a) p = q := PrimeSpectrum.ext hq
    refine ⟨p, ?_, hpq⟩
    show Ideal.span {g i, g j} ≤ p.asIdeal
    rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · have hm : (∑ l, MvPolynomial.C (g l) * MvPolynomial.X l) ∈ q.asIdeal := by
        simpa [f, genericLinearMap, s] using h (.inr 0)
      rw [← hq] at hm
      show MvPolynomial.C (g i) ∈ q.asIdeal
      simpa only [Ideal.mem_comap, hev] using hm
    · exact (by simpa [f, genericLinearMap, s] using h (.inr 1) : MvPolynomial.C (g j) ∈ q.asIdeal)
  · rintro ⟨p, hp, rfl⟩ b
    show MvPolynomial.eval a (f (MvPolynomial.X b) - algebraMap k _ (s b)) ∈ p.asIdeal
    cases b with
    | inl l => simp [f, genericLinearMap, s, ha]
    | inr b =>
      have hgi : g i ∈ p.asIdeal := hp (Ideal.subset_span (by simp))
      have hgj : g j ∈ p.asIdeal := hp (Ideal.subset_span (by simp))
      by_cases hb : b = 0 <;> simp [f, genericLinearMap, s, hb, hev, hgi, hgj]

/-- A nontrivial algebra of finite type over a field has finite Krull dimension. -/
private lemma exists_ringKrullDim_eq_nat
    (k : Type u) [Field k] (R : Type v) [CommRing R] [Nontrivial R]
    [Algebra k R] [Algebra.FiniteType k R] :
    ∃ d : ℕ, ringKrullDim R = d := by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp
    (inferInstance : Algebra.FiniteType k R)
  have h := ringKrullDim_le_of_surjective f.toRingHom hf
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, zero_add] at h
  have htop : ringKrullDim R ≠ ⊤ :=
    ne_top_of_le_ne_top (fun he ↦ ENat.natCast_ne_top _ (WithBot.coe_eq_coe.mp he)) h
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp fun hbot ↦
    not_subsingleton R (ringKrullDim_eq_bot_iff_subsingleton.mp hbot)
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp fun (hd' : d = ⊤) ↦ htop (by rw [← hd, hd']; rfl)
  exact ⟨e, by rw [← hd, ← he]; rfl⟩

/-- The generic linear map is injective when the zero locus of `(gᵢ, gⱼ)` has a component of
codimension two. -/
private lemma genericLinearMap_injective
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] {n : ℕ} (g : Fin n → A) (i j : Fin n)
    (p : PrimeSpectrum A)
    (hp : p.asIdeal ∈ (Ideal.span {g i, g j}).minimalPrimes)
    (hcodim : ringKrullDim (A ⧸ p.asIdeal) + 2 = ringKrullDim A) :
    Function.Injective (genericLinearMap k g j) := by
  classical
  let B := MvPolynomial (Fin n) A
  let R := MvPolynomial (Fin n ⊕ Fin 2) k
  let f := genericLinearMap k g j
  let a : Fin n → A := Pi.single i 1
  let E : B →+* A := MvPolynomial.eval a
  have hE : Function.Surjective E := fun z ↦ ⟨MvPolynomial.C z, MvPolynomial.eval_C z⟩
  let I := Ideal.span {g i, g j}
  let x := PrimeSpectrum.comap E p
  let s : Fin n ⊕ Fin 2 → k := Sum.elim (Pi.single i 1) (fun _ ↦ 0)
  let y := PrimeSpectrum.comap (MvPolynomial.eval s) (⊥ : PrimeSpectrum k)
  have hfiber : PrimeSpectrum.comap f.toRingHom ⁻¹' {y} =
      PrimeSpectrum.comap E '' PrimeSpectrum.zeroLocus (I : Set A) :=
    genericLinearMap_fiber k g i j
  have hxy : PrimeSpectrum.comap f.toRingHom x = y := by
    show x ∈ PrimeSpectrum.comap f.toRingHom ⁻¹' {y}
    exact hfiber ▸ ⟨p, hp.1.2, rfl⟩
  have hemb := PrimeSpectrum.isEmbedding_comap_of_surjective _ _ hE
  have hfiber' : PrimeSpectrum.comap f.toRingHom ⁻¹'
      {PrimeSpectrum.comap f.toRingHom x} =
      PrimeSpectrum.comap E '' PrimeSpectrum.zeroLocus (I : Set A) := by
    rwa [hxy]
  let e := (hemb.homeomorphImage (PrimeSpectrum.zeroLocus (I : Set A))).trans
    (Homeomorph.setCongr hfiber'.symm)
  have hlocal : topologicalKrullDimAt (PrimeSpectrum.comap f.toRingHom ⁻¹'
      {PrimeSpectrum.comap f.toRingHom x}) ⟨x, rfl⟩ = ringKrullDim (A ⧸ p.asIdeal) := by
    have h := topologicalKrullDimAt_eq_of_homeomorph e ⟨p, hp.1.2⟩
    rw [topologicalKrullDimAt_zeroLocus_minimalPrime k I p hp] at h
    exact h.symm
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hB : ringKrullDim B = ringKrullDim A + n := by
    simp [B, MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hR : ringKrullDim R = (n + 2 : ℕ) := by
    simp [R, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card]
  have hdim := ringKrullDim_le_fiber_add_quotient k R B f x
  rw [hlocal, hB] at hdim
  apply (RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr
  by_contra hker
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f.toRingHom
  have hh : (1 : ℕ∞) ≤ (RingHom.ker f).height := by
    rwa [Order.one_le_iff_ne_zero, ne_eq, Ideal.height_eq_zero_iff_eq_bot]
  have hbound : ringKrullDim (R ⧸ RingHom.ker f) + 1 ≤ ringKrullDim R := by
    rw [Stacks.Spectrum.LocalDimensionFormula.ringKrullDim_eq_height_add_ringKrullDim_quotient
      k R (RingHom.ker f), add_comm]
    exact add_le_add_left (WithBot.coe_le_coe.mpr hh) _
  rw [hR] at hbound
  obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_nat k A
  obtain ⟨d₀, hd₀⟩ := exists_ringKrullDim_eq_nat k (A ⧸ p.asIdeal)
  obtain ⟨d₁, hd₁⟩ := exists_ringKrullDim_eq_nat k (R ⧸ RingHom.ker f)
  rw [hd, hd₀, hd₁] at hdim
  rw [hd₀, hd] at hcodim
  rw [hd₁] at hbound
  have hdim' : d + n ≤ d₀ + d₁ := by exact_mod_cast hdim
  have hcodim' : d₀ + 2 = d := by exact_mod_cast hcodim
  have hbound' : d₁ + 1 ≤ n + 2 := by exact_mod_cast hbound
  omega

/-- Let `A` be a domain of finite type over a field `k`, let
`n ≥ 2` and let `g : Fin n → A`. If the common zero locus of `g 0` and `g 1` has an irreducible
component of dimension `dim A - 2`, then there are `c : Fin n → k` for which the variables
`x₁, …, xₙ`, the linear combination `∑ gᵢxᵢ` and the constant `∑ cᵢgᵢ` are algebraically
independent over `k`. -/
@[stacks 0G4E]
public theorem exists_algebraicIndependent_linearCombinations
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] {n : ℕ} (hn : 2 ≤ n) (g : Fin n → A)
    (hcodim : ∃ p : Ideal A,
      p ∈ (Ideal.span {g ⟨0, by omega⟩, g ⟨1, by omega⟩}).minimalPrimes ∧
        ringKrullDim (A ⧸ p) + 2 = ringKrullDim A) :
    ∃ c : Fin n → k,
      AlgebraicIndependent k
        (Sum.elim (MvPolynomial.X : Fin n → MvPolynomial (Fin n) A)
          (fun j : Fin 2 =>
            if j = 0 then
              ∑ i : Fin n, MvPolynomial.C (g i) * MvPolynomial.X i
            else
              MvPolynomial.C (∑ i : Fin n, algebraMap k A (c i) * g i))) := by
  classical
  obtain ⟨p, hp, hdim⟩ := hcodim
  have : p.IsPrime := hp.1.1
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have : Small.{u} A := Algebra.FiniteType.small (R := k)
  let A' := Shrink.{u} A
  let e : A' ≃ₐ[k] A := Shrink.algEquiv k A
  have : Algebra.FiniteType k A' := Algebra.FiniteType.of_surjective
    e.symm.toAlgHom e.symm.surjective
  let g' : Fin n → A' := fun l ↦ e.symm (g l)
  let p' := PrimeSpectrum.comap e.toRingHom ⟨p, ‹p.IsPrime›⟩
  have hI : (Ideal.span {g i, g j}).comap e.toRingHom =
      Ideal.span {g' i, g' j} := by
    show (Ideal.span {g i, g j}).comap e.toRingEquiv = _
    rw [← Ideal.map_symm e.toRingEquiv, Ideal.map_span]
    simp only [Set.image_pair]; rfl
  have hp' : p'.asIdeal ∈ (Ideal.span {g' i, g' j}).minimalPrimes :=
    hI ▸ Ideal.minimalPrimes_comap_of_surjective e.surjective hp
  have hdim' : ringKrullDim (A' ⧸ p'.asIdeal) + 2 = ringKrullDim A' := by
    show ringKrullDim (A' ⧸ p.comap e.toRingHom) + 2 = ringKrullDim A'
    rwa [ringKrullDim_quotient_comap e.toRingHom e.surjective p,
      ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  have hinj' := genericLinearMap_injective k A' g' i j p' hp' hdim'
  have hmap : (MvPolynomial.mapAlgHom e.symm.toAlgHom).comp (genericLinearMap k g j) =
      genericLinearMap k g' j := by
    ext b
    cases b with
    | inl l => simp [genericLinearMap, MvPolynomial.mapAlgHom_apply]
    | inr b =>
      by_cases hb : b = 0 <;>
        simp [genericLinearMap, hb, g', MvPolynomial.mapAlgHom_apply, map_sum]
  have hinj : Function.Injective (genericLinearMap k g j) := fun r t hrt ↦ hinj' <|
    (DFunLike.congr_fun hmap r).symm.trans
      ((congrArg (MvPolynomial.mapAlgHom e.symm.toAlgHom) hrt).trans (DFunLike.congr_fun hmap t))
  refine ⟨Pi.single j 1, ?_⟩
  have hc : (∑ l : Fin n, algebraMap k A ((Pi.single j 1 : Fin n → k) l) * g l) =
      g j := by simp [Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq']
  rwa [hc, algebraicIndependent_iff_injective_aeval]

end Algebra

end
