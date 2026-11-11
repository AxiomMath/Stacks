module

public import StacksCore.Tactic.EgaSgaAttribute
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Spectrum.Prime.Polynomial
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

@[expose] public section

open PrimeSpectrum

/-- The preimage of a basic open under `PrimeSpectrum.comap φ` is the basic
open at the image: `(comap φ)⁻¹(D(f)) = D(φ f)`. -/
@[ega "I 1.2.2" "more general", ega "I 1.6.1" "more general", ega "I 10.2.1" "special case"]
private lemma preimage_comap_basicOpen
    {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (f : R) :
    (PrimeSpectrum.comap φ) ⁻¹' (basicOpen f : Set (PrimeSpectrum R)) =
      (basicOpen (φ f) : Set (PrimeSpectrum S)) := by
  ext; simp

/-- Every quasi-compact open subset of `Spec(R)` is a finite union of basic
opens. -/
private lemma exists_finset_eq_biUnion_basicOpen
    {R : Type*} [CommSemiring R] (V : Set (PrimeSpectrum R))
    (hV : IsOpen V) (hVc : IsCompact V) :
    ∃ s : Finset R, V = ⋃ f ∈ s, (basicOpen f : Set (PrimeSpectrum R)) := by
  classical
  obtain ⟨s, hs, rfl⟩ := (isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis _
    isTopologicalBasis_basic_opens isCompact_basicOpen V).1 ⟨hVc, hV⟩
  exact ⟨hs.toFinset, by simp⟩

/--
Stacks 00F7 (first assertion): for a ring map `φ : R → S`, the induced
continuous map `Spec(S) → Spec(R)` is quasi-compact, i.e. the preimage of
every quasi-compact open of `Spec(R)` is quasi-compact in `Spec(S)`.
-/
@[stacks 00F7 "(1)"]
theorem PrimeSpectrum.isCompact_preimage_comap_of_isOpen
    {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (V : Set (PrimeSpectrum R)) (hV : IsOpen V) (hVc : IsCompact V) :
    IsCompact ((PrimeSpectrum.comap φ) ⁻¹' V) := by
  obtain ⟨s, rfl⟩ := exists_finset_eq_biUnion_basicOpen V hV hVc
  simp_rw [Set.preimage_iUnion, preimage_comap_basicOpen]
  exact s.finite_toSet.isCompact_biUnion
    fun f _ => PrimeSpectrum.isCompact_basicOpen (φ f)

/--
Stacks 00F7 (second assertion): for a ring map `φ : R → S` and any
constructible subset `E ⊆ Spec(R)`, the preimage `(comap φ)⁻¹(E)` is
constructible in `Spec(S)`.
-/
@[stacks 00F7 "(2)"]
theorem PrimeSpectrum.isConstructible_preimage_comap
    {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    Topology.IsConstructible ((PrimeSpectrum.comap φ) ⁻¹' E) :=
  hE.preimage (PrimeSpectrum.continuous_comap φ)
    (fun V hV hVr =>
      ((isCompact_preimage_comap_of_isOpen φ V hV hVr.isCompact).isRetrocompact
        ((PrimeSpectrum.continuous_comap φ).isOpen_preimage V hV)))

-- The former @[stacks 00F9] declaration is now the Mathlib theorems: `Spec S → Spec R` for a
-- localization away from `f` is an open embedding with retrocompact (basic open) range, and
-- constructibility transports along such an embedding.
add_to_stacks 00F9 "`Spec R_f → Spec R` is an open embedding"
  PrimeSpectrum.localization_away_isOpenEmbedding
add_to_stacks 00F9 "constructibility transports along an open embedding with retrocompact range"
  Topology.IsConstructible.image_of_isOpenEmbedding
add_to_sga "3 VIB 3.7" "partial" Topology.IsConstructible.image_of_isOpenEmbedding
add_to_stacks 00F9 "the range of `Spec R_f → Spec R` is `D(f)`"
  PrimeSpectrum.localization_away_comap_range
add_to_ega "I 1.2.6" "special case" PrimeSpectrum.localization_away_comap_range
add_to_ega "I 1.6.2" "special case" PrimeSpectrum.localization_away_comap_range
add_to_stacks 00F9 "`D(f)` is retrocompact" PrimeSpectrum.isRetrocompact_basicOpen

-- The former @[stacks 00FA] declaration is now the Mathlib theorems: `Spec (R/I) → Spec R` is a
-- closed embedding, its range is `V(I)` whose complement is retrocompact when `I` is finitely
-- generated, and constructibility transports along such an embedding.
add_to_stacks 00FA "`Spec (R/I) → Spec R` is a closed embedding"
  PrimeSpectrum.isClosedEmbedding_comap_of_surjective
add_to_stacks 00FA "the complement of `V(I)` is retrocompact for a finitely generated `I`"
  PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg
add_to_stacks 00FA "constructibility transports along a closed embedding with retrocompact range"
  Topology.IsConstructible.image_of_isClosedEmbedding
add_to_stacks 00FA "the range of `Spec (R/I) → Spec R` is `V(I)`" range_comap_of_surjective

open Polynomial TensorProduct

/-- The characteristic polynomial of an `R`-linear endomorphism `φ : A →ₗ[R] A`,
computed using the witness that `A ≃ₗ[R] Fin n → R`. -/
@[ega "II 6.4.1", sga "3 V 4.1" "special case", sga "3 X 7.3"]
noncomputable def charPolyOfEquiv {R A : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] {n : ℕ} (e : A ≃ₗ[R] (Fin n → R))
    (φ : A →ₗ[R] A) : Polynomial R :=
  letI : Module.Free R A := Module.Free.of_equiv e.symm
  letI : Module.Finite R A := Module.Finite.equiv e.symm
  φ.charpoly

/-- A monic polynomial of degree `n` reduces to `X ^ n` over the residue field at a prime `I`
if and only if its first `n` coefficients lie in `I`. -/
lemma Polynomial.map_residueField_eq_X_pow_iff {R : Type*} [CommRing R] {n : ℕ} {P : R[X]}
    (hP : P.Monic) (hdeg : P.natDegree = n) (I : Ideal R) [I.IsPrime] :
    P.map (algebraMap R I.ResidueField) = X ^ n ↔ ∀ i : Fin n, P.coeff i ∈ I := by
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · have key := congr(($h).coeff (i : ℕ))
    simp only [coeff_map, coeff_X_pow, ite_eq_right i.isLt.ne] at key
    rwa [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] at key
  · ext i
    rcases lt_trichotomy i n with hi | rfl | hi
    · simp only [coeff_map, coeff_X_pow, ite_eq_right hi.ne]
      rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
      exact h ⟨i, hi⟩
    · simp [coeff_map, ← hdeg, hP.coeff_natDegree]
    · simp [coeff_map, coeff_X_pow, hi.ne', coeff_eq_zero_of_natDegree_lt (hdeg ▸ hi)]

/-- For `A` free of rank `n` over `R` and `f : A`, multiplication by `f` is nilpotent after
base change to the residue field at a prime `p` if and only if the first `n` coefficients of
its characteristic polynomial lie in `p`. -/
lemma isNilpotent_baseChange_mulLeft_iff_coeffs_mem
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) (e : A ≃ₗ[R] (Fin n → R))
    (f : A) (p : PrimeSpectrum R) :
    IsNilpotent
        (LinearMap.baseChange p.asIdeal.ResidueField (LinearMap.mulLeft R f)) ↔
      ∀ i : Fin n, (charPolyOfEquiv e (LinearMap.mulLeft R f)).coeff (i : ℕ) ∈ p.asIdeal := by
  let : Module.Free R A := Module.Free.of_equiv e.symm
  let : Module.Finite R A := Module.Finite.equiv e.symm
  have := p.nontrivial
  have hrank : Module.finrank R A = n := by
    rw [LinearEquiv.finrank_eq e, Module.finrank_fin_fun]
  have hrank' : Module.finrank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] A) = n := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul, hrank]
  rw [LinearMap.isNilpotent_iff_charpoly, LinearMap.charpoly_baseChange, hrank',
    charPolyOfEquiv]
  exact Polynomial.map_residueField_eq_X_pow_iff (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree, hrank]) _

/-- A prime `p` lies in the zero locus of the first `n` coefficients of `P` exactly when each
of those coefficients belongs to `p`. -/
lemma mem_zeroLocus_image_coeffs_iff
    {R : Type*} [CommRing R] {n : ℕ} (P : Polynomial R) (p : PrimeSpectrum R) :
    p ∈ PrimeSpectrum.zeroLocus
        ((fun i : Fin n => P.coeff (i : ℕ)) '' Set.univ) ↔
      ∀ i : Fin n, P.coeff (i : ℕ) ∈ p.asIdeal := by
  simp [PrimeSpectrum.mem_zeroLocus, Set.subset_def]

/-- For `A` free of rank `n` over `R` and `f : A`, the set of primes `p` at which
multiplication by `f` becomes nilpotent over the residue field is the zero locus of the first
`n` coefficients of the characteristic polynomial of multiplication by `f`. -/
@[stacks 00FC]
theorem PrimeSpectrum.isNilpotent_baseChange_mulLeft_iff_mem_zeroLocus
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) (e : A ≃ₗ[R] (Fin n → R))
    (f : A) (p : PrimeSpectrum R) :
    IsNilpotent
        (LinearMap.baseChange p.asIdeal.ResidueField
          (LinearMap.mulLeft R f)) ↔
      p ∈ PrimeSpectrum.zeroLocus
        ((fun i : Fin n =>
            (charPolyOfEquiv e (LinearMap.mulLeft R f)).coeff i) '' Set.univ) := by
  rw [isNilpotent_baseChange_mulLeft_iff_coeffs_mem n e f p,
      mem_zeroLocus_image_coeffs_iff (charPolyOfEquiv e (LinearMap.mulLeft R f)) p]

/--
**Stacks Tag 00FD.** Let `R` be a ring and `f, g ∈ R[x]` polynomials whose
leading coefficient of `g` is a unit of `R`. Then the image of `D(f) ∩ V(g)`
under the structure map `Spec(R[x]) → Spec(R)` is a finite union of standard
opens: there exist `r_1, …, r_n ∈ R` with image `= ⋃ᵢ D(rᵢ)`.

Since the leading coefficient of `g` is a unit, `g` is associate to the monic
polynomial `g' = (leadingCoeff g)⁻¹ • g`, so `V(g) = V(g')`. For monic `g'`,
`R[x]/(g')` is finite free over `R`, and Mathlib's
`Polynomial.exists_image_comap_of_monic` produces a finite set `t ⊆ R` with
image `= (V(t))ᶜ = ⋃_{r ∈ t} D(r)`, which we reindex by `Fin n`.
-/
@[stacks 00FD]
theorem image_comap_C_basicOpen_inter_zeroLocus
    {R : Type*} [CommRing R] (f g : R[X]) (hg : IsUnit g.leadingCoeff) :
    ∃ (n : ℕ) (r : Fin n → R),
      comap (C : R →+* R[X]) ''
          ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus {g}) =
        ⋃ i, (basicOpen (r i) : Set (PrimeSpectrum R)) := by
  -- Replace `g` by the associated monic polynomial `g' = (leadingCoeff g)⁻¹ • g`.
  set g' : R[X] := hg.unit⁻¹ • g with hg'def
  have hmonic : g'.Monic := monic_of_isUnit_leadingCoeff_inv_smul hg
  -- `V(g) = V(g')`, since `g'` and `g` differ by the unit `C (leadingCoeff g)⁻¹`.
  have hzl : (zeroLocus {g} : Set (PrimeSpectrum R[X])) = zeroLocus {g'} := by
    have hmul : g' = C (↑hg.unit⁻¹ : R) * g := by
      rw [hg'def, Units.smul_def, smul_eq_C_mul]
    ext p
    simp only [mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
    rw [hmul]
    exact (Ideal.unit_mul_mem_iff_mem _ (isUnit_C.mpr (Units.isUnit _))).symm
  -- Rewrite `D(f) ∩ V(g)` as `V(g') \ V(f)` to match the Mathlib lemma.
  have hset : (basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus {g}
      = zeroLocus {g'} \ zeroLocus {f} := by
    rw [basicOpen_eq_zeroLocus_compl, hzl, Set.sdiff_eq, Set.inter_comm]
  -- Mathlib: the image is `(V(t))ᶜ` for a finite set `t ⊆ R`.
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g' hmonic
  -- `(V(t))ᶜ = ⋃_{x ∈ t} D(x)`, indexed over the subtype `{x // x ∈ t}`.
  have hunion : (zeroLocus (↑t : Set R))ᶜ
      = ⋃ x : {x // x ∈ t}, (basicOpen x.val : Set (PrimeSpectrum R)) := by
    ext p
    simp [Set.not_subset]
  -- Reindex the union over `Fin n` via `{x // x ∈ t} ≃ Fin (card …)`.
  refine ⟨Fintype.card {x // x ∈ t},
    fun i => ((Fintype.equivFin {x // x ∈ t}).symm i).val, ?_⟩
  rw [hset, ht, hunion]
  exact ((Fintype.equivFin {x // x ∈ t}).symm.surjective.iUnion_comp _).symm

-- The former @[stacks 00FE] declaration is now the Mathlib theorem.
add_to_stacks 00FE "Chevalley's theorem" PrimeSpectrum.isConstructible_comap_image
add_to_sga "3 VIB 3.7" "special case" PrimeSpectrum.isConstructible_comap_image
add_to_sga "3 VIB 4.2" "special case" PrimeSpectrum.isConstructible_comap_image
add_to_ega "IV 1.8.4.1" "affine source" PrimeSpectrum.isConstructible_comap_image
add_to_ega "IV 1.9.5" "(viii), special case" PrimeSpectrum.isConstructible_comap_image
-- `add_to_ega` / `add_to_sga` take the declaration on the SAME line as the reference and
-- comment; on a continuation line the command terminates first and the identifier is read as
-- a fresh command.
add_to_ega "IV 1.8.4" "affine case" PrimeSpectrum.isConstructible_comap_image
add_to_ega "IV 1.8.5" "affine case" PrimeSpectrum.isConstructible_comap_image
add_to_ega "IV 9.5.1" "affine case" PrimeSpectrum.isConstructible_comap_image
add_to_sga "1 IV 6.2" "affine case" PrimeSpectrum.isConstructible_comap_image

/-- For a finite-type map out of a Noetherian ring, the image of a constructible set is
constructible: Chevalley's theorem, since a finite-type algebra over a Noetherian ring is of
finite presentation. This is the left vertical arrow of the square of Stacks 00GE, see
`PrimeSpectrum.exists_commSq_constructible_restrictToClosedPoints`. -/
@[sga "1 IV 6.2" "affine source and target"]
theorem PrimeSpectrum.isConstructible_comap_image_of_finiteType
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (φ : R →+* S) (hφ : φ.FiniteType)
    {E : Set (PrimeSpectrum S)} (hE : Topology.IsConstructible E) :
    Topology.IsConstructible (PrimeSpectrum.comap φ '' E) :=
  PrimeSpectrum.isConstructible_comap_image
    (RingHom.FinitePresentation.of_finiteType.mp hφ) hE
