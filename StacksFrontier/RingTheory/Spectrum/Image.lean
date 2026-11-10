module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

/-
# Problem Description

Stacks Tag 0532 (Lemma 15.21.4).

Let `R` be a commutative ring with unit and `n ≥ 0` a natural number. Work with the
polynomial ring `R[T_1, …, T_n]`, formalized as `MvPolynomial (Fin n) R`.

Given:
* An ideal `J ⊆ R[T_1, …, T_n]`, with quotient `S = R[T_1, …, T_n] / J`.
* For each `i`, a positive integer `d_i ≥ 1` and elements `α_{ij} ∈ R`
  (`j ∈ {1, …, d_i}`) such that the one-variable polynomial
  `P_i(T_i) = ∏_{j=1}^{d_i} (T_i - α_{ij})`, regarded as an element of
  `R[T_1, …, T_n]`, belongs to `J`.
* The index set of multi-indices `K = { (k_1, …, k_n) : 1 ≤ k_i ≤ d_i }`
  (here formalized as the dependent product `(i : Fin n) → Fin (d i)`).
* For each `k ∈ K` the evaluation `R`-algebra map
  `Φ_k : R[T_1, …, T_n] → R`, `T_i ↦ α_{i k_i}`.
* The image ideals `J_k = Φ_k(J) ⊆ R`.
* For an ideal `I ⊆ R`, the vanishing locus `V(I) = { p ∈ Spec(R) : I ⊆ p }`.
* The structure map `R → S` and the induced map `Spec(S) → Spec(R)`.

# Main Statement

The image of `Spec(S) → Spec(R)` equals `V( ⋂_{k ∈ K} J_k )`. Equivalently, a prime
`p ∈ Spec(R)` lies in the image iff `⋂_{k ∈ K} J_k ⊆ p`.

The proof hint: `V(⋂ J_k) = ⋃ V(J_k)`, and the image is exactly `⋃_k V(J_k)`.
The hypothesis `P_i(T_i) ∈ J` (with `d_i ≥ 1`) is what forces the image into the union.
-/

/-- The zero locus of a finite infimum of ideals is the union of their zero loci:
a prime contains `⨅ i, I i` if and only if it contains some `I i`. -/
theorem PrimeSpectrum.zeroLocus_iInf {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (I : ι → Ideal R) :
    PrimeSpectrum.zeroLocus ((⨅ i, I i : Ideal R) : Set R) =
      ⋃ i, PrimeSpectrum.zeroLocus ((I i : Ideal R) : Set R) := by
  have : Fintype ι := Fintype.ofFinite _
  ext p
  simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_iUnion, SetLike.coe_subset_coe]
  refine ⟨fun h => ?_, fun ⟨i, hi⟩ => (iInf_le _ i).trans hi⟩
  have hprodle : Finset.univ.prod I ≤ p.asIdeal :=
    Ideal.prod_le_inf.trans (by rwa [Finset.inf_univ_eq_iInf])
  obtain ⟨i, -, hi⟩ := p.isPrime.prod_le.mp hprodle
  exact ⟨i, hi⟩

open MvPolynomial

namespace Stacks.Spectrum.PolynomialQuotientImage

variable {R : Type*} [CommRing R] {n : ℕ} (d : Fin n → ℕ)
  (α : (i : Fin n) → Fin (d i) → R)

/-- The (finite, nonempty when each `d_i ≥ 1`) index set of multi-indices
`K = { (k_1, …, k_n) : 1 ≤ k_i ≤ d_i }`, formalized as the dependent product. -/
abbrev MultiIndex := (i : Fin n) → Fin (d i)

/-- The one-variable polynomial `P_i(T_i) = ∏_{j} (T_i - α_{ij})`, regarded as an
element of `R[T_1, …, T_n]` depending only on the variable `T_i`. -/
noncomputable def factoredPoly (i : Fin n) : MvPolynomial (Fin n) R :=
  ∏ j : Fin (d i), (X i - C (α i j))

/-- Definitional unfolding of `factoredPoly`. -/
theorem factoredPoly_def (i : Fin n) :
    factoredPoly d α i = ∏ j : Fin (d i), (X i - C (α i j)) := rfl

/-- The evaluation `R`-algebra homomorphism `Φ_k : R[T_1, …, T_n] → R`,
`T_i ↦ α_{i k_i}`. -/
noncomputable def evalHom (k : MultiIndex d) : MvPolynomial (Fin n) R →ₐ[R] R :=
  aeval (fun i => α i (k i))

/-- `Φ_k` maps the constant polynomial `C r` to `r`. -/
@[simp] theorem evalHom_C (k : MultiIndex d) (r : R) : evalHom d α k (C r) = r := by
  simp [evalHom]

/-- `Φ_k` maps the variable `T_i` to `α_{i k_i}`. -/
@[simp] theorem evalHom_X (k : MultiIndex d) (i : Fin n) : evalHom d α k (X i) = α i (k i) := by
  simp [evalHom]

/-- The image ideal `J_k = Φ_k(J) ⊆ R`. Since `Φ_k` is surjective this is an ideal of `R`. -/
noncomputable def imageIdeal (k : MultiIndex d) (J : Ideal (MvPolynomial (Fin n) R)) : Ideal R :=
  Ideal.map (evalHom d α k) J

/-- Definitional unfolding of `imageIdeal`. -/
theorem imageIdeal_def (k : MultiIndex d) (J : Ideal (MvPolynomial (Fin n) R)) :
    imageIdeal d α k J = Ideal.map (evalHom d α k) J := rfl

/-- The canonical structure map `R → S = R[T_1, …, T_n] / J`, namely the algebra map
of the quotient algebra. -/
noncomputable abbrev structMap (J : Ideal (MvPolynomial (Fin n) R)) :
    R →+* (MvPolynomial (Fin n) R ⧸ J) :=
  algebraMap R (MvPolynomial (Fin n) R ⧸ J)

/-- The structure map sends `r ∈ R` to the class of the constant polynomial `C r` in
`R[T_1, …, T_n] / J`. -/
@[simp] theorem structMap_apply (J : Ideal (MvPolynomial (Fin n) R)) (r : R) :
    structMap J r = Ideal.Quotient.mk J (C r) := by
  rw [← Ideal.Quotient.mk_algebraMap, algebraMap_eq]

-- ===========================================================================
-- Sub-lemmas of the decomposition (one level below the two main theorems).
--
-- Overall strategy (Stacks: "this lemma proves itself"):
--   image(Spec S → Spec R) = ⋃_k V(J_k)   and   V(⋂_k J_k) = ⋃_k V(J_k).
-- The first equality splits into the two inclusions (Lemma B: ⊇, Lemma C: ⊆);
-- the second is the finite-intersection/zeroLocus identity
-- (`PrimeSpectrum.zeroLocus_iInf`). The
-- hypothesis `P_i(T_i) ∈ J` is used only in Lemma C.
-- ===========================================================================

/-- Every prime containing the image ideal `J_k` lies in the image of
`Spec(S) → Spec(R)`, that is, `V(J_k) ⊆ range (comap (structMap J))`. -/
theorem zeroLocus_imageIdeal_subset_range (J : Ideal (MvPolynomial (Fin n) R))
    (k : MultiIndex d) :
    PrimeSpectrum.zeroLocus ((imageIdeal d α k J) : Ideal R) ⊆
      Set.range (PrimeSpectrum.comap (structMap J)) := by
  -- Φ_k = evalHom sends J into J_k = map Φ_k J, so it descends to a ring hom
  -- ψ : S = R[T]/J → R/J_k with ψ ∘ (structMap J) = mk J_k. By functoriality of
  -- comap, range(comap (mk J_k)) = range(comap (structMap J) ∘ comap ψ) ⊆
  -- range(comap (structMap J)); and range(comap (mk J_k)) = zeroLocus J_k since
  -- mk J_k is surjective with kernel J_k (`range_comap_of_surjective`, `Ideal.mk_ker`).
  set Jk : Ideal R := imageIdeal d α k J with hJk
  set Φ : MvPolynomial (Fin n) R →+* R := (evalHom d α k).toRingHom with hΦ
  have hJle : J ≤ Ideal.comap Φ Jk := by
    rw [hJk, imageIdeal_def]
    exact Ideal.le_comap_map
  set ψ : (MvPolynomial (Fin n) R ⧸ J) →+* (R ⧸ Jk) :=
    Ideal.quotientMap Jk Φ hJle with hψ
  have hcomp : ψ.comp (structMap J) = Ideal.Quotient.mk Jk := by
    ext r
    change ψ (structMap J r) = Ideal.Quotient.mk Jk r
    rw [structMap_apply, hψ, Ideal.quotientMap_mk]
    change Ideal.Quotient.mk Jk (Φ (C r)) = Ideal.Quotient.mk Jk r
    congr 1
    rw [hΦ]
    simp
  have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk Jk))
      = PrimeSpectrum.zeroLocus ((RingHom.ker (Ideal.Quotient.mk Jk)) : Set R) :=
    range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hrange
  rw [← hrange, ← hcomp, PrimeSpectrum.comap_comp]
  rw [Set.range_comp]
  exact Set.image_subset_range _ _

/-- A ring map to a domain that kills `P_i(T_i) = ∏_j (T_i - α_{ij})` must send `T_i`
to the image of one of the roots `α_{ij}`. -/
theorem exists_eq_of_factoredPoly_eq_zero {A : Type*} [CommRing A] [IsDomain A]
    (φ : MvPolynomial (Fin n) R →+* A) (hφ : ∀ i, φ (factoredPoly d α i) = 0) (i : Fin n) :
    ∃ j : Fin (d i), φ (C (α i j)) = φ (X i) := by
  have hp : ∏ j : Fin (d i), (φ (X i) - φ (C (α i j))) = 0 := by
    have := hφ i
    rw [factoredPoly_def, map_prod] at this
    simpa only [map_sub] using this
  obtain ⟨j, -, hj⟩ := (Finset.prod_eq_zero_iff
    (s := (Finset.univ : Finset (Fin (d i))))
    (f := fun j => φ (X i) - φ (C (α i j)))).mp hp
  exact ⟨j, (eq_of_sub_eq_zero hj).symm⟩

/-- The image of `Spec(S) → Spec(R)` is contained in `⋃_k V(J_k)`, whenever each
polynomial `P_i(T_i) = ∏_j (T_i - α_{ij})` belongs to `J`. -/
theorem range_subset_iUnion_zeroLocus_imageIdeal (J : Ideal (MvPolynomial (Fin n) R))
    (hJ : ∀ i, factoredPoly d α i ∈ J) :
    Set.range (PrimeSpectrum.comap (structMap J)) ⊆
      ⋃ k : MultiIndex d, PrimeSpectrum.zeroLocus ((imageIdeal d α k J) : Ideal R) := by
  rintro p ⟨q, rfl⟩
  rw [Set.mem_iUnion]
  set S := MvPolynomial (Fin n) R ⧸ J
  have hqp : q.asIdeal.IsPrime := q.isPrime
  have hdom : IsDomain (S ⧸ q.asIdeal) := Ideal.Quotient.isDomain q.asIdeal
  set φ : MvPolynomial (Fin n) R →+* (S ⧸ q.asIdeal) :=
    (Ideal.Quotient.mk q.asIdeal).comp (Ideal.Quotient.mk J) with hφ
  -- Each factored polynomial is killed by `φ` since it lies in `J`.
  have hkill : ∀ i, φ (factoredPoly d α i) = 0 := by
    intro i
    have hz : Ideal.Quotient.mk J (factoredPoly d α i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hJ i)
    rw [hφ, RingHom.comp_apply, hz, map_zero]
  -- In the integral domain `S ⧸ q` one factor of each `P_i` vanishes; collect the
  -- resulting roots into a multi-index `k`.
  choose k hk using exists_eq_of_factoredPoly_eq_zero (A := S ⧸ q.asIdeal) d α φ hkill
  refine ⟨k, ?_⟩
  rw [PrimeSpectrum.mem_zeroLocus]
  change (imageIdeal d α k J : Ideal R) ≤ (PrimeSpectrum.comap (structMap J) q).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, imageIdeal_def, Ideal.map_le_iff_le_comap]
  -- The two ring maps `mk q ∘ structMap J ∘ Φ_k` and `φ` agree on generators, hence
  -- are equal; so for any `g`, `mk q (structMap J (Φ_k g)) = φ g`.
  have hkey : ∀ g : MvPolynomial (Fin n) R,
      Ideal.Quotient.mk q.asIdeal (structMap J ((evalHom d α k) g)) = φ g := by
    have hcomp : ((Ideal.Quotient.mk q.asIdeal).comp ((structMap J).comp (evalHom d α k).toRingHom))
        = φ := by
      apply ringHom_ext
      · intro r
        simp [hφ]
      · intro i
        simpa [hφ] using hk i
    intro g
    simpa using RingHom.congr_fun hcomp g
  intro f hf
  refine Ideal.mem_comap.mpr ?_
  refine (Ideal.Quotient.eq_zero_iff_mem (I := q.asIdeal)).mp ?_
  rw [hkey f, hφ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

-- Main Statement(s)

/-- **Stacks Tag 0532.** The image of the map `Spec(S) → Spec(R)` induced by the
structure map `R → S = R[T_1, …, T_n] / J` equals the closed set `V(⋂_{k ∈ K} J_k)`
cut out by the intersection of the image ideals. -/
@[stacks 0532]
theorem range_comap_eq_zeroLocus_iInf_imageIdeal
    (J : Ideal (MvPolynomial (Fin n) R))
    (hJ : ∀ i, factoredPoly d α i ∈ J) :
    Set.range (PrimeSpectrum.comap (structMap J)) =
      PrimeSpectrum.zeroLocus (R := R)
        ((⨅ k : (i : Fin n) → Fin (d i), imageIdeal d α k J) : Ideal R) := by
  rw [PrimeSpectrum.zeroLocus_iInf]
  exact (range_subset_iUnion_zeroLocus_imageIdeal d α J hJ).antisymm
    (Set.iUnion_subset (zeroLocus_imageIdeal_subset_range d α J))

/-- Explicit form of Stacks Tag 0532: a prime `p ∈ Spec(R)` lies in the image of
`Spec(S) → Spec(R)` iff `⋂_{k ∈ K} J_k ⊆ p`. -/
theorem mem_range_comap_iff (J : Ideal (MvPolynomial (Fin n) R))
    (hJ : ∀ i, factoredPoly d α i ∈ J) (p : PrimeSpectrum R) :
    p ∈ Set.range (PrimeSpectrum.comap (structMap J)) ↔
      (⨅ k : MultiIndex d, imageIdeal d α k J) ≤ p.asIdeal := by
  rw [range_comap_eq_zeroLocus_iInf_imageIdeal d α J hJ, PrimeSpectrum.mem_zeroLocus]
  -- `s ⊆ ↑p.asIdeal` for the ideal-as-set is defeq to `(⨅ k, …) ≤ p.asIdeal`.
  exact Iff.rfl

end Stacks.Spectrum.PolynomialQuotientImage

-- ===== merged from StacksDraft.Sec9.Tag07M3 =====



/-
# Problem Description

Stacks Tag 07M3 (lemma-separate-image-closed-from-closed).

Let `φ : R → S` be a homomorphism of commutative rings. Let `I ⊆ R` be an ideal of
`R` and let `J ⊆ S` be an ideal of `S`. Suppose that the closure (in `Spec R`) of the
image of `V(J) ⊆ Spec S` under `Spec(φ) : Spec S → Spec R` is disjoint from `V(I)`:

  closure (Spec(φ) (V(J))) ∩ V(I) = ∅.

Then there exists an element `f ∈ R` such that
1. `f` maps to `1` in `R/I` (equivalently, `f - 1 ∈ I`), and
2. `φ(f) ∈ J`.
-/

-- Background and context (as comments)
--
-- * Prime spectrum. `Spec R = PrimeSpectrum R` is the set of prime ideals of `R`,
--   equipped with the Zariski topology, whose closed sets are the zero loci
--   `V(a) = {p : a ⊆ p} = PrimeSpectrum.zeroLocus a`.
--
-- * Induced map on spectra. The ring map `φ : R → S` induces the continuous map
--   `Spec(φ) = PrimeSpectrum.comap φ : Spec S → Spec R`, sending a prime ideal
--   `q ⊆ S` to its contraction `φ⁻¹(q) = Ideal.comap φ q`.
--
-- * "f maps to 1 in R/I" means `Ideal.Quotient.mk I f = 1`, equivalently `f - 1 ∈ I`.
--
-- Notes (for orientation, not part of the statement):
-- A standard fact (Stacks 00ES / 00FK) is that
--   closure (Spec(φ) (V(J))) = V(φ⁻¹(J)).
-- With it, the hypothesis becomes `V(φ⁻¹(J)) ∩ V(I) = ∅`, equivalently
-- `V(φ⁻¹(J) + I) = ∅`, equivalently `φ⁻¹(J) + I = R`, i.e. `1 = a + b` with
-- `a ∈ φ⁻¹(J)` and `b ∈ I`; then `f = a` works.

open PrimeSpectrum

-- Main Statement(s)

/-- **Stacks Tag 07M3.** If the closure of the image of `V(J)` under `Spec(φ)` is
disjoint from `V(I)`, then there is `f ∈ R` mapping to `1` in `R/I` with `φ(f) ∈ J`. -/
@[stacks 07M3]
theorem exists_quotient_eq_one_and_map_mem {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal R) (J : Ideal S)
    (h : closure ((PrimeSpectrum.comap φ) '' (PrimeSpectrum.zeroLocus (J : Set S)))
        ∩ PrimeSpectrum.zeroLocus (I : Set R) = ∅) :
    ∃ f : R, (Ideal.Quotient.mk I) f = 1 ∧ φ f ∈ J := by
  -- Closure of the image of V(J) under Spec(φ) equals V(φ⁻¹(J)) = V(comap φ J).
  rw [closure_image_comap_zeroLocus] at h
  -- Intersection V(comap φ J) ∩ V(I) = V(comap φ J ⊔ I).
  rw [← zeroLocus_sup] at h
  -- Empty zero locus ⟺ the ideal is the whole ring: comap φ J ⊔ I = ⊤.
  have htop : (Ideal.comap φ J ⊔ I) = ⊤ := PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp h
  -- Hence 1 ∈ comap φ J ⊔ I, so 1 = x + y with x ∈ comap φ J (i.e. φ x ∈ J) and y ∈ I.
  have hmem : (1 : R) ∈ Ideal.comap φ J ⊔ I := by rw [htop]; trivial
  rw [Submodule.mem_sup] at hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := hmem
  -- Take f = x. Since x = 1 - y with y ∈ I, mk I x = 1; and φ x ∈ J since x ∈ comap φ J.
  refine ⟨x, ?_, ?_⟩
  · have : x = 1 - y := by linear_combination hxy
    rw [this]
    rw [map_sub, map_one, (Ideal.Quotient.eq_zero_iff_mem).mpr hy, sub_zero]
  · exact (Ideal.mem_comap).mp hx
