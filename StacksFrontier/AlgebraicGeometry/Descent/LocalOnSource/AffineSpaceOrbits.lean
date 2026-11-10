module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.FieldTheory.PrimeField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Artinian.FiniteType

/-!
# Orbits of elementary transformations of affine space

An elementary transformation of affine space replaces one coordinate by that coordinate plus a
power of another. An open subset of affine space invariant under all of them is either the
whole of affine space, or has very small complement: finitely many closed points, whose
coordinates are algebraic over the prime field, and only in positive characteristic.

## Main definitions

* `MvPolynomial.coordinateShear` is the automorphism of the coordinate ring induced by an
  elementary transformation.

## Main results

* `MvPolynomial.eq_univ_or_finite_compl_of_invariant_coordinateShear` describes invariant
  nonempty open subsets of affine space.

## Implementation notes

Affine space is represented by the prime spectrum of its multivariate polynomial coordinate
ring. An open subscheme is represented by its open carrier, and invariance is expressed using
inverse image under the induced spectrum automorphism. A closed point is a maximal prime
ideal, and its coordinates are the images of the variables in its residue field. Being
algebraic over the prime field is expressed by integrality over `ZMod (ringChar k)`.

## References

* [Stacks Project, Tag 0CF0](https://stacks.math.columbia.edu/tag/0CF0)
-/

@[expose] public section

namespace MvPolynomial

/-- The pullback on the coordinate ring of the transformation which replaces
the `i`-th coordinate by that coordinate plus the `d`-th power of the `j`-th
coordinate. Its inverse subtracts the same power. -/
noncomputable def coordinateShear {R : Type*} [CommRing R] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (d : ℕ) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun l => if l = i then MvPolynomial.X i + MvPolynomial.X j ^ d
      else MvPolynomial.X l)
    (MvPolynomial.aeval fun l => if l = i then MvPolynomial.X i - MvPolynomial.X j ^ d
      else MvPolynomial.X l)
    (MvPolynomial.algHom_ext fun l ↦ by by_cases hli : l = i <;> simp [hli, Ne.symm hij])
    (MvPolynomial.algHom_ext fun l ↦ by by_cases hli : l = i <;> simp [hli, Ne.symm hij])

@[sga "6 V 2.6" "partial"]
private lemma eq_zero_of_eval_zero_on_infinite_product
    {R : Type*} [CommRing R] [IsDomain R] {σ : Type*} [Finite σ]
    (P : MvPolynomial σ R) (T : σ → Set R)
    (hT : ∀ i, (T i).Infinite)
    (hP : ∀ x : σ → R, (∀ i, x i ∈ T i) → MvPolynomial.eval x P = 0) :
    P = 0 := by
  classical
  let S : σ → Finset R := fun i =>
    Classical.choose ((hT i).exists_subset_card_eq (P.degreeOf i + 1))
  have hS (i : σ) : (↑(S i) : Set R) ⊆ T i ∧ (S i).card = P.degreeOf i + 1 :=
    Classical.choose_spec ((hT i).exists_subset_card_eq (P.degreeOf i + 1))
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P S
  · intro i; rw [(hS i).2]; omega
  · intro x hx; exact hP x (fun i => (hS i).1 (hx i))

/-- A polynomial vanishing on infinitely many values of one variable vanishes for all of them. -/
private lemma aeval_update_eq_zero_of_infinite
    {k K : Type*} [Field k] [Field K] [Algebra k K] {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ k) (x : σ → K) (i : σ) (S : Set K)
    (hS : S.Infinite)
    (h : ∀ t ∈ S, MvPolynomial.aeval (Function.update x i t) P = 0) :
    ∀ t : K, MvPolynomial.aeval (Function.update x i t) P = 0 := by
  simp only [MvPolynomial.aeval_def, ← MvPolynomial.eval_map] at h ⊢
  generalize P.map (algebraMap k K) = P' at h ⊢
  let Q : Polynomial K := MvPolynomial.aeval
    (fun j => if j = i then Polynomial.X else Polynomial.C (x j)) P'
  have hQ (t : K) : Q.eval t = MvPolynomial.eval (Function.update x i t) P' := by
    let e : MvPolynomial σ K →+* K :=
      (Polynomial.evalRingHom t).comp
        (MvPolynomial.aeval (fun j => if j = i then Polynomial.X else Polynomial.C (x j))).toRingHom
    have he : e = MvPolynomial.eval₂Hom (RingHom.id K) (Function.update x i t) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [e]
      · intro j; by_cases hji : j = i <;> simp [e, hji, Function.update]
    exact congrArg (fun f : MvPolynomial σ K →+* K => f P') he
  have hroot : {t : K | Q.IsRoot t}.Infinite := by
    apply hS.mono
    intro t ht
    change Q.eval t = 0
    simpa [hQ] using h t ht
  have hzero := Polynomial.eq_zero_of_infinite_isRoot Q hroot
  intro t; rw [← hQ, hzero, Polynomial.eval_zero]

/-- A property of points that holds at `x` and is preserved by changing coordinates in `q`
holds at every point which differs from `x` only in coordinates satisfying `q`. -/
private lemma holds_of_update_steps {ι K : Type*} [DecidableEq ι] (x : ι → K)
    (p : (ι → K) → Prop) (q : ι → Prop) (hx : p x)
    (step : ∀ z i, q i → p z → ∀ t, p (Function.update z i t))
    (s : Finset ι) (hs : ∀ l ∈ s, q l) : ∀ y, (∀ l ∉ s, y l = x l) → p y := by
  induction s using Finset.induction_on with
  | empty =>
    intro y hy
    obtain rfl : y = x := funext (by simpa using hy)
    exact hx
  | @insert i s his ih =>
    intro y hy
    have hzy : Function.update (Function.update y i (x i)) i (y i) = y := by simp
    rw [← hzy]
    refine step _ i (hs i (Finset.mem_insert_self i s))
      (ih (fun l hl => hs l (Finset.mem_insert_of_mem hl)) _ fun l hl => ?_) _
    by_cases hli : l = i
    · subst hli; simp
    · simpa [hli] using hy l (by simp [hli, hl])

private lemma vanishingIdeal_shear_mem
    {k : Type*} [Field k] {n : ℕ}
    (W : Set (PrimeSpectrum (MvPolynomial (Fin n) k)))
    (hWinv : ∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ),
      PrimeSpectrum.comap (coordinateShear (R := k) i j hij d).toRingHom ⁻¹' W = W)
    (i j : Fin n) (hij : i ≠ j) (d : ℕ)
    (P : MvPolynomial (Fin n) k)
    (hP : P ∈ PrimeSpectrum.vanishingIdeal Wᶜ) :
    coordinateShear i j hij d P ∈ PrimeSpectrum.vanishingIdeal Wᶜ := by
  refine (PrimeSpectrum.mem_vanishingIdeal Wᶜ _).mpr fun q hq ↦ ?_
  exact (PrimeSpectrum.mem_vanishingIdeal Wᶜ P).mp hP _
    fun hw ↦ hq ((Set.ext_iff.mp (hWinv i j hij d) q).mp hw)

private lemma aeval_coordinateShear
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (d : ℕ)
    (x : Fin n → K) (P : MvPolynomial (Fin n) k) :
    MvPolynomial.aeval x (coordinateShear i j hij d P) =
      MvPolynomial.aeval (Function.update x i (x i + x j ^ d)) P := by
  have he : (MvPolynomial.aeval x : MvPolynomial (Fin n) k →ₐ[k] K).comp
      (coordinateShear i j hij d).toAlgHom =
      (MvPolynomial.aeval (Function.update x i (x i + x j ^ d)) :
        MvPolynomial (Fin n) k →ₐ[k] K) := by
    apply MvPolynomial.algHom_ext
    intro l
    by_cases hli : l = i
    · subst l
      simp [coordinateShear, Function.update]
    · simp [coordinateShear, Function.update, hli]
  exact congrArg (fun f : MvPolynomial (Fin n) k →ₐ[k] K => f P) he

private lemma aeval_update_zero_of_infinite
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ)
      (P : MvPolynomial (Fin n) k), P ∈ I → coordinateShear i j hij d P ∈ I)
    (x : Fin n → K) (hx : ∀ P ∈ I, MvPolynomial.aeval x P = 0)
    (i j : Fin n) (hij : i ≠ j)
    (hinf : (Set.range fun d : ℕ => x j ^ d).Infinite) :
    ∀ t : K, ∀ P ∈ I, MvPolynomial.aeval (Function.update x i t) P = 0 := by
  intro t P hP
  let S : Set K := (fun z => x i + z) '' Set.range (fun d : ℕ => x j ^ d)
  have hS : S.Infinite := hinf.image (fun _ _ _ _ h => add_left_cancel h)
  refine aeval_update_eq_zero_of_infinite P x i S hS ?_ t
  rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
  rw [← aeval_coordinateShear i j hij d]
  exact hx _ (hI i j hij d P hP)

private lemma aeval_free_except
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ)
      (P : MvPolynomial (Fin n) k), P ∈ I → coordinateShear i j hij d P ∈ I)
    (x : Fin n → K) (hx : ∀ P ∈ I, MvPolynomial.aeval x P = 0)
    (j : Fin n) (hinf : (Set.range fun d : ℕ => x j ^ d).Infinite) :
    ∀ y : Fin n → K, y j = x j → ∀ P ∈ I, MvPolynomial.aeval y P = 0 := by
  classical
  intro y hy
  refine (holds_of_update_steps x (fun z => z j = x j ∧ ∀ P ∈ I, MvPolynomial.aeval z P = 0)
    (· ≠ j) ⟨rfl, hx⟩ (fun z i hij hz t => ⟨?_, ?_⟩) (Finset.univ.erase j) (by simp) y
    fun l hl => ?_).2
  · simpa [Function.update_of_ne hij.symm] using hz.1
  · exact aeval_update_zero_of_infinite I hI z hz.2 i j hij (by simpa [hz.1] using hinf) t
  · simpa [(by simpa using hl : l = j)] using hy

private lemma aeval_everywhere_of_infinite_power_sources
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ)
      (P : MvPolynomial (Fin n) k), P ∈ I → coordinateShear i j hij d P ∈ I)
    (x : Fin n → K) (hx : ∀ P ∈ I, MvPolynomial.aeval x P = 0)
    (i j : Fin n) (hij : i ≠ j)
    (hinf : (Set.range fun d : ℕ => x j ^ d).Infinite)
    (A : Set K) (hA : A.Infinite)
    (hApow : ∀ a ∈ A, (Set.range fun d : ℕ => a ^ d).Infinite) :
    ∀ y : Fin n → K, ∀ P ∈ I, MvPolynomial.aeval y P = 0 := by
  have hfree := aeval_free_except I hI x hx j hinf
  intro y P hP
  have hzero (a : K) (ha : a ∈ A) :
      MvPolynomial.aeval (Function.update y i a) P = 0 := by
    let z := Function.update (Function.update y i a) j (x j)
    have hzj : z j = x j := by simp [z]
    have hz := hfree z hzj
    have hzi : z i = a := by simp [z, hij]
    have hzinfinite : (Set.range fun d : ℕ => z i ^ d).Infinite := by
      simpa [hzi] using hApow a ha
    have h := aeval_update_zero_of_infinite I hI z hz j i (Ne.symm hij)
      hzinfinite (y j) P hP
    have hupdate : Function.update z j (y j) = Function.update y i a := by
      funext l
      by_cases hlj : l = j
      · subst l; simp [Function.update, Ne.symm hij]
      · simp [z, hlj, Function.update]
    simpa [hupdate] using h
  simpa using aeval_update_eq_zero_of_infinite P y i A hA hzero (y i)

private lemma infinite_powers_of_transcendental
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (a : K) (ha : Transcendental F a) :
    (Set.range fun d : ℕ => a ^ d).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n hmn
  have he : (Polynomial.X : Polynomial F) ^ m = (Polynomial.X : Polynomial F) ^ n :=
    (transcendental_iff_injective.mp ha) (by simpa using hmn)
  simpa using congrArg Polynomial.natDegree he

private lemma aeval_update_zero_of_charZero
    {k K : Type*} [Field k] [Field K] [CharZero K] [Algebra k K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ)
      (P : MvPolynomial (Fin n) k), P ∈ I → coordinateShear i j hij d P ∈ I)
    (x : Fin n → K) (hx : ∀ P ∈ I, MvPolynomial.aeval x P = 0)
    (i j : Fin n) (hij : i ≠ j) :
    ∀ t : K, ∀ P ∈ I, MvPolynomial.aeval (Function.update x i t) P = 0 := by
  have horbit : ∀ m : ℕ, ∀ P ∈ I,
      MvPolynomial.aeval (Function.update x i (x i + (m : K))) P = 0 := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      intro P hP
      have h := ih (coordinateShear i j hij 0 P) (hI i j hij 0 P hP)
      rw [aeval_coordinateShear] at h
      convert h using 1
      simp [Function.update, pow_zero, Nat.cast_succ, add_assoc]
  have hS : (Set.range fun m : ℕ => x i + (m : K)).Infinite :=
    Set.infinite_range_of_injective fun _ _ hab ↦ Nat.cast_injective (add_left_cancel hab)
  intro t P hP
  exact aeval_update_eq_zero_of_infinite P x i _ hS (by rintro _ ⟨m, rfl⟩; exact horbit m P hP) t

private lemma ideal_eq_bot_of_aeval_zero
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (hinf : (Set.univ : Set K).Infinite)
    (h : ∀ y : Fin n → K, ∀ P ∈ I, MvPolynomial.aeval y P = 0) : I = ⊥ := by
  apply le_antisymm _ bot_le
  intro P hP
  have hzero : P.map (algebraMap k K) = 0 := by
    refine eq_zero_of_eval_zero_on_infinite_product _ (fun _ => Set.univ) (fun _ ↦ hinf) ?_
    intro y _; simpa [MvPolynomial.aeval_def, MvPolynomial.eval_map] using h y P hP
  have hPzero : P = 0 :=
    (MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective k K)) (by simpa using hzero)
  simp [hPzero]

private lemma ideal_eq_bot_of_charZero
    {k K : Type*} [Field k] [Field K] [CharZero K] [Algebra k K] {n : ℕ}
    (hn : 2 ≤ n)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ)
      (P : MvPolynomial (Fin n) k), P ∈ I → coordinateShear i j hij d P ∈ I)
    (x : Fin n → K) (hx : ∀ P ∈ I, MvPolynomial.aeval x P = 0) : I = ⊥ := by
  classical
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hfree := holds_of_update_steps x (fun z => ∀ P ∈ I, MvPolynomial.aeval z P = 0)
    (fun _ => True) hx (fun z i _ hz t => ?_) Finset.univ (by simp)
  · exact ideal_eq_bot_of_aeval_zero I Set.infinite_univ fun y ↦ hfree y (by simp)
  · obtain ⟨j, hij⟩ := exists_ne i
    exact aeval_update_zero_of_charZero I hI z hz i j (Ne.symm hij) t

private lemma aeval_everywhere_of_transcendental_coordinate
    {F k K : Type*} [Field F] [Field k] [Field K]
    [Algebra F K] [Algebra k K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ)
      (P : MvPolynomial (Fin n) k), P ∈ I → coordinateShear i j hij d P ∈ I)
    (x : Fin n → K) (hx : ∀ P ∈ I, MvPolynomial.aeval x P = 0)
    (i j : Fin n) (hij : i ≠ j)
    (ht : Transcendental F (x j)) :
    ∀ y : Fin n → K, ∀ P ∈ I, MvPolynomial.aeval y P = 0 := by
  let A : Set K := Set.range (fun d : ℕ => x j ^ (d + 1))
  have hinf := infinite_powers_of_transcendental (x j) ht
  have hxj : x j ≠ 0 := by
    intro he; rw [he] at ht; exact ht isAlgebraic_zero
  have hA : A.Infinite := by
    have := hinf.image (fun _ _ _ _ h => mul_right_cancel₀ hxj h)
    convert this using 1
    ext a
    simp only [A, Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨d, rfl⟩; exact ⟨x j ^ d, ⟨d, rfl⟩, by simp [pow_succ]⟩
    · rintro ⟨_, ⟨d, rfl⟩, rfl⟩; exact ⟨d, by simp [pow_succ]⟩
  have hApow : ∀ a ∈ A, (Set.range fun d : ℕ => a ^ d).Infinite := by
    rintro a ⟨d, rfl⟩; exact infinite_powers_of_transcendental _ (ht.pow (Nat.succ_pos d))
  exact aeval_everywhere_of_infinite_power_sources I hI x hx i j hij hinf A hA hApow

/-- A closed subset of the prime spectrum is the zero locus of its vanishing ideal. -/
private lemma zeroLocus_vanishingIdeal_of_isClosed {R : Type*} [CommRing R]
    {C : Set (PrimeSpectrum R)} (hC : IsClosed C) :
    PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal C : Set R) = C := by
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hC.closure_eq]

private lemma vanishingIdeal_compl_ne_bot_of_open_nonempty
    {R : Type*} [CommRing R] (W : Set (PrimeSpectrum R))
    (hWopen : IsOpen W) (hWnonempty : W.Nonempty) :
    PrimeSpectrum.vanishingIdeal Wᶜ ≠ ⊥ := by
  intro hI
  have hzero := (zeroLocus_vanishingIdeal_of_isClosed hWopen.isClosed_compl).symm
  rw [hI, PrimeSpectrum.zeroLocus_bot] at hzero
  obtain ⟨q, hq⟩ := hWnonempty
  have : q ∈ Wᶜ := by rw [hzero]; trivial
  exact this hq

private lemma aeval_eq_ringHom
    {k K : Type*} [CommRing k] [CommRing K] [Algebra k K] {n : ℕ}
    (f : MvPolynomial (Fin n) k →+* K)
    (hf : algebraMap k K = f.comp MvPolynomial.C)
    (P : MvPolynomial (Fin n) k) :
    MvPolynomial.aeval (fun i => f (MvPolynomial.X i)) P = f P := by
  have he : (MvPolynomial.aeval (fun i => f (MvPolynomial.X i)) :
      MvPolynomial (Fin n) k →ₐ[k] K).toRingHom = f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa only [MvPolynomial.aeval_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        RingHom.comp_apply] using congrArg (fun g : k →+* K => g c) hf
    · intro i; simp
  exact congrArg (fun g : MvPolynomial (Fin n) k →+* K => g P) he

private lemma isMaximal_of_integral_residue_coordinates
    {k : Type*} [Field k] {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) k))
    (h : ∀ i : Fin n, IsIntegral k
      (algebraMap (MvPolynomial (Fin n) k) q.asIdeal.ResidueField (MvPolynomial.X i))) :
    q.asIdeal.IsMaximal := by
  classical
  let K := q.asIdeal.ResidueField
  let f : MvPolynomial (Fin n) k →+* K := algebraMap _ _
  let : Algebra k K := (f.comp MvPolynomial.C).toAlgebra
  let x : Fin n → K := fun i => f (MvPolynomial.X i)
  let B : Subalgebra k K := Algebra.adjoin k (Set.range x)
  have : Algebra.IsIntegral k B := Algebra.IsIntegral.adjoin (by rintro z ⟨i, rfl⟩; exact h i)
  have hfield : IsField B := isField_of_isIntegral_of_isField' (Field.toIsField k)
  let : Field B := hfield.toField
  let xB : Fin n → B := fun i => ⟨x i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  let g : MvPolynomial (Fin n) k →+* B := (MvPolynomial.aeval xB).toRingHom
  have he : B.val.comp (MvPolynomial.aeval xB) =
      (MvPolynomial.aeval x : MvPolynomial (Fin n) k →ₐ[k] K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [xB, x]
  have hg (P : MvPolynomial (Fin n) k) : (g P : K) = f P := by
    rw [show (g P : K) = MvPolynomial.aeval x P from
      congrArg (fun e : MvPolynomial (Fin n) k →ₐ[k] K => e P) he]
    exact aeval_eq_ringHom f rfl P
  have hsurj : Function.Surjective g := by
    intro b
    have hb : (b : K) ∈
        (MvPolynomial.aeval x : MvPolynomial (Fin n) k →ₐ[k] K).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact b.property
    obtain ⟨P, hP⟩ := hb
    refine ⟨P, Subtype.ext ?_⟩
    change MvPolynomial.aeval x P = (b : K) at hP
    rw [aeval_eq_ringHom f rfl P] at hP
    simpa only [hg] using hP
  have hker : RingHom.ker g = q.asIdeal := by
    ext P
    change g P = 0 ↔ P ∈ q.asIdeal
    constructor
    · intro hP
      apply Ideal.algebraMap_residueField_eq_zero.mp
      change f P = 0
      rw [← hg P, hP]
      rfl
    · intro hP
      apply Subtype.ext
      rw [hg P, Ideal.algebraMap_residueField_eq_zero.mpr hP]
      rfl
  exact hker ▸ RingHom.ker_isMaximal_of_surjective g hsurj

/-- A nonempty open subset of affine `n`-space, for `n ≥ 2`, invariant under
every elementary coordinate shear, is either all of affine space or has finite
complement consisting of closed points whose coordinates are algebraic over
the prime field (and in the latter case the field has positive characteristic). -/
@[stacks 0CF0]
lemma eq_univ_or_finite_compl_of_invariant_coordinateShear
    {k : Type*} [Field k] {n : ℕ} (hn : 2 ≤ n)
    (W : Set (PrimeSpectrum (MvPolynomial (Fin n) k)))
    (hWopen : IsOpen W) (hWnonempty : W.Nonempty)
    (hWinv : ∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ),
      PrimeSpectrum.comap (coordinateShear (R := k) i j hij d).toRingHom ⁻¹' W = W) :
    W = Set.univ ∨
      (0 < ringChar k ∧ Wᶜ.Finite ∧ ∀ q ∈ Wᶜ, q.asIdeal.IsMaximal ∧
        ∃ ι : ZMod (ringChar k) →+* q.asIdeal.ResidueField,
          ∀ i : Fin n, @IsIntegral (ZMod (ringChar k)) q.asIdeal.ResidueField _ _ ι.toAlgebra
            (algebraMap (MvPolynomial (Fin n) k) q.asIdeal.ResidueField
            (MvPolynomial.X i))) := by
  classical
  let I : Ideal (MvPolynomial (Fin n) k) := PrimeSpectrum.vanishingIdeal Wᶜ
  have hIne : I ≠ ⊥ := vanishingIdeal_compl_ne_bot_of_open_nonempty W hWopen hWnonempty
  have hIinv : ∀ (i j : Fin n) (hij : i ≠ j) (d : ℕ)
      (P : MvPolynomial (Fin n) k), P ∈ I → coordinateShear i j hij d P ∈ I :=
    vanishingIdeal_shear_mem W hWinv
  by_cases hW : W = Set.univ
  · exact Or.inl hW
  right
  have hchar : 0 < ringChar k := by
    by_contra h
    have hchar0 : ringChar k = 0 := Nat.eq_zero_of_not_pos h
    have : CharZero k := (CharP.ringChar_zero_iff_CharZero (R := k)).mp hchar0
    obtain ⟨q, hq⟩ := Set.ne_univ_iff_exists_notMem W |>.mp hW
    let K := q.asIdeal.ResidueField
    let f : MvPolynomial (Fin n) k →+* K := algebraMap _ _
    let : Algebra k K := (f.comp MvPolynomial.C).toAlgebra
    have : CharZero K :=
      charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k K)
    let x : Fin n → K := fun i => f (MvPolynomial.X i)
    have hx : ∀ P ∈ I, MvPolynomial.aeval x P = 0 := by
      intro P hP
      rw [show MvPolynomial.aeval x P = f P from aeval_eq_ringHom f rfl P]
      exact Ideal.algebraMap_residueField_eq_zero.mpr
        ((PrimeSpectrum.mem_vanishingIdeal Wᶜ P).mp hP q hq)
    exact hIne (ideal_eq_bot_of_charZero hn I hIinv x hx)
  have hIntegral : ∀ q ∈ Wᶜ,
      ∃ ι : ZMod (ringChar k) →+* q.asIdeal.ResidueField,
        ∀ i : Fin n, @IsIntegral (ZMod (ringChar k)) q.asIdeal.ResidueField _ _
          ι.toAlgebra (algebraMap (MvPolynomial (Fin n) k) q.asIdeal.ResidueField
            (MvPolynomial.X i)) := by
    intro q hq
    let K := q.asIdeal.ResidueField
    let f : MvPolynomial (Fin n) k →+* K := algebraMap _ _
    let : Algebra k K := (f.comp MvPolynomial.C).toAlgebra
    let x : Fin n → K := fun i => f (MvPolynomial.X i)
    have hx : ∀ P ∈ I, MvPolynomial.aeval x P = 0 := by
      intro P hP
      rw [show MvPolynomial.aeval x P = f P from aeval_eq_ringHom f rfl P]
      exact Ideal.algebraMap_residueField_eq_zero.mpr
        ((PrimeSpectrum.mem_vanishingIdeal Wᶜ P).mp hP q hq)
    have : Fact (Nat.Prime (ringChar k)) :=
      ⟨(CharP.char_is_prime_or_zero k (ringChar k)).resolve_right (Nat.ne_of_gt hchar)⟩
    let ι : ZMod (ringChar k) →+* K :=
      ZMod.castHom (show ringChar K ∣ ringChar k by rw [Algebra.ringChar_eq k K]) K
    let : Algebra (ZMod (ringChar k)) K := ι.toAlgebra
    refine ⟨ι, ?_⟩
    intro i
    apply isAlgebraic_iff_isIntegral.mp
    by_contra ht
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    obtain ⟨j, hji⟩ := exists_ne i
    exact hIne (ideal_eq_bot_of_aeval_zero I
      ((infinite_powers_of_transcendental (x i) ht).mono (Set.subset_univ _))
      (aeval_everywhere_of_transcendental_coordinate I hIinv x hx j i hji ht))
  have hmax : ∀ q ∈ Wᶜ, q.asIdeal.IsMaximal := by
    intro q hq
    obtain ⟨ι, hι⟩ := hIntegral q hq
    let K := q.asIdeal.ResidueField
    let ιk : ZMod (ringChar k) →+* k := ZMod.castHom (dvd_refl _) k
    let : Algebra (ZMod (ringChar k)) k := ιk.toAlgebra
    let : Algebra (ZMod (ringChar k)) K := ι.toAlgebra
    let : IsScalarTower (ZMod (ringChar k)) k K :=
      IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact isMaximal_of_integral_residue_coordinates q fun i ↦ IsIntegral.tower_top (hι i)
  refine ⟨hchar, ?_, ?_⟩
  · have hzero : Wᶜ = PrimeSpectrum.zeroLocus I :=
      (zeroLocus_vanishingIdeal_of_isClosed hWopen.isClosed_compl).symm
    let Q := MvPolynomial (Fin n) k ⧸ I
    have hdim : Ring.KrullDimLE 0 Q := by
      apply Ring.krullDimLE_zero_iff.mpr
      intro J hJ
      let q : PrimeSpectrum (MvPolynomial (Fin n) k) :=
        PrimeSpectrum.comap (Ideal.Quotient.mk I) ⟨J, hJ⟩
      have hq : q ∈ Wᶜ := by
        rw [hzero]
        change I ≤ J.comap (Ideal.Quotient.mk I)
        intro P hP
        change (Ideal.Quotient.mk I) P ∈ J
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hP]
        exact J.zero_mem
      have hqmax := hmax q hq
      exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
        (Ideal.Quotient.mk I)
        ((Ideal.Quotient.mk I).isIntegral_of_surjective Ideal.Quotient.mk_surjective)
        J hqmax
    have : Finite (PrimeSpectrum Q) :=
      ((Algebra.FiniteType.krullDimLE_zero_tfae k Q).out 1 2).mp hdim
    have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = Wᶜ := by
      rw [hzero]
      simpa [Ideal.mk_ker] using
        (range_comap_of_surjective _ (Ideal.Quotient.mk I)
          Ideal.Quotient.mk_surjective)
    rw [← hrange]
    exact Set.finite_range _
  · exact fun q hq ↦ ⟨hmax q hq, hIntegral q hq⟩

end MvPolynomial

end
