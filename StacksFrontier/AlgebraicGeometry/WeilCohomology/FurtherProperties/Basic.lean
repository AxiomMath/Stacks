module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Trace.Defs
public import StacksFrontier.RingTheory.Artinian.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Relations between traces of algebra homomorphisms

Over a field of characteristic zero, consider two surjective maps from a finite algebra to the
same finite separable algebra, the difference of whose trace maps is divisible by an integer
greater than one in a relation involving traces to other finite separable algebras. Then the
two maps differ by an automorphism of their target: they have the same kernel and the same
trace map, and each is the other composed with an automorphism. If moreover the two maps have
a common section they are themselves equal.

The proof splits each separable algebra into a product of fields, expands the trace of a map
into such a product as a sum over the embeddings of the factors into an algebraic closure, and
compares the two sides coefficientwise. Surjectivity makes every coefficient of the two trace
maps `0` or `1`, and two such coefficients congruent modulo an integer greater than one are
equal; the two maps therefore meet the same characters of the source, so they have the same
kernel, and the first isomorphism theorem turns that into the automorphism. A common section
then forces the automorphism to be the identity.

## Main results

* `AlgHom.exists_algEquiv_comp_eq_of_trace_sub_trace_eq_zsmul` produces the automorphism `θ`
  of the target with `σ' = θ ∘ σ`, together with the equality of the two trace maps and of the
  two kernels.
* `AlgHom.trace_comp_eq_trace_comp_of_trace_sub_trace_eq_zsmul` records the equality of the two
  trace maps on its own.
* `AlgHom.eq_of_trace_sub_trace_eq_zsmul` proves that the two algebra homomorphisms are equal
  when they have a common section.

## Implementation notes

The relation in the source is expressed directly as an equality of linear maps. The algebras
indexed there by the integers from `1` to `r` are indexed here by `Fin r`.

Tag 0FHT states the equality of the two algebra homomorphisms from surjectivity alone. That
statement is false, and `Stacks.WeilCohomology.not_traceRelationStatement`, in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.TraceRelationCounterexample`,
refutes it: the identity and complex conjugation are distinct surjective `ℝ`-algebra maps
`ℂ → ℂ` with equal trace maps. The corrected statement, recorded as a Stacks erratum,
replaces the conclusion by the automorphism relation; that is the registered statement here.
The version with a common section is what the chapter has available at the one place it uses
Tag 0FHT, namely Tag 0FHU.

## References

* [Stacks Project, Tag 0FHT](https://stacks.math.columbia.edu/tag/0FHT)
-/

@[expose] public section

universe u v w x

open Polynomial

/-- The trace of a product of algebras is the sum of the traces of the factors. -/
private theorem trace_pi_sum
    {K : Type u} [Field K] {ι : Type v} [Fintype ι] (E : ι → Type x)
    [∀ i, CommRing (E i)] [∀ i, Algebra K (E i)]
    [∀ i, Module.Free K (E i)] [∀ i, Module.Finite K (E i)]
    (x : ∀ i, E i) :
    Algebra.trace K (∀ i, E i) x = ∑ i, Algebra.trace K (E i) (x i) := by
  classical
  let b : Module.Basis (Σ i, Fin (Module.finrank K (E i))) K (∀ i, E i) :=
    Pi.basis fun i => Module.finBasis K (E i)
  rw [Algebra.trace_eq_matrix_trace b]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_apply,
    LinearMap.toMatrix_apply]
  dsimp [b]
  simp only [Pi.basis_apply, Pi.single_eq_same]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (Module.finBasis K (E i)) (x i)]
  simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul]

/-- For a map into an algebra presented as a finite product of finite separable fields, the
image of the trace in an algebraically closed field is the sum, over the factors and over the
embeddings of each factor, of the composites with the projection. -/
private theorem trace_comp_sum_embeddings
    (F : Type u) (A : Type w) (R : Type v) [Field F] [CommRing A] [Algebra F A]
    [CommRing R] [Algebra F R] (I : Type v) [Fintype I] (E : I → Type v)
    [∀ i, Field (E i)] [∀ i, Algebra F (E i)] [∀ i, Module.Finite F (E i)]
    [∀ i, Algebra.IsSeparable F (E i)] (e : R ≃ₐ[F] ∀ i, E i)
    (f : A →ₐ[F] R) (Ω : Type x) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (a : A) :
    algebraMap F Ω (Algebra.trace F R (f a)) =
      ∑ i, ∑ ψ : E i →ₐ[F] Ω, ψ ((Pi.evalAlgHom F E i).comp (e.toAlgHom.comp f) a) := by
  classical
  calc
    algebraMap F Ω (Algebra.trace F R (f a)) =
        algebraMap F Ω (Algebra.trace F (∀ i, E i) (e (f a))) :=
      congrArg (algebraMap F Ω) (Algebra.trace_eq_of_algEquiv e (f a)).symm
    _ = algebraMap F Ω (∑ i, Algebra.trace F (E i)
          ((Pi.evalAlgHom F E i).comp (e.toAlgHom.comp f) a)) := by
      congr 1
      simpa using trace_pi_sum (K := F) E (e (f a))
    _ = ∑ i, ∑ ψ : E i →ₐ[F] Ω,
          ψ ((Pi.evalAlgHom F E i).comp (e.toAlgHom.comp f) a) := by
      simp only [map_sum]
      exact Finset.sum_congr rfl fun i _ => trace_eq_sum_embeddings (E := Ω)

/-- A separable algebra over a field is formally unramified: two lifts to a square-zero
extension agree, because the derivative of a minimal polynomial is a unit at its root. -/
@[ega "0 20.4.13" "base domain a field"]
private theorem formallyUnramified_of_isSeparable_commRing
    (K : Type u) (A : Type x) [Field K] [CommRing A] [Algebra K A]
    [Algebra.IsSeparable K A] : Algebra.FormallyUnramified K A := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f₁ f₂ e
  ext x
  have hx : f₁ x - f₂ x ∈ I := by
    simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using AlgHom.congr_fun e x
  have hsq : (f₁ x - f₂ x) ^ 2 ∈ (⊥ : Ideal B) := hI ▸ Ideal.pow_mem_pow hx 2
  have heval := Polynomial.eval_add_of_sq_eq_zero
    ((minpoly K x).map (algebraMap K B)) (f₂ x) (f₁ x - f₂ x) hsq
  simp only [add_sub_cancel, eval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero,
    derivative_map, zero_add] at heval
  have hder : IsUnit ((aeval x) (derivative (minpoly K x))) := by
    obtain ⟨a, b, hab⟩ :=
      (Polynomial.separable_def' (minpoly K x)).mp (Algebra.IsSeparable.isSeparable K x)
    refine IsUnit.of_mul_eq_one ((aeval x) b) ?_
    rw [← map_mul, show derivative (minpoly K x) * b = 1 - a * minpoly K x by
      linear_combination hab]
    simp [minpoly.aeval]
  rwa [eq_comm, (hder.map f₂).mul_right_eq_zero, sub_eq_zero] at heval

/-- A finite separable algebra over a field of characteristic zero is a finite product of
finite separable field extensions: it is Artinian and reduced, so it splits along its maximal
spectrum. -/
private theorem exists_finite_separable_product
    (K : Type u) (A : Type x) [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [CharZero K] :
    ∃ (I : Type x) (_ : Finite I) (E : I → Type x)
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra K (E i))
      (_e : A ≃ₐ[K] ∀ i, E i),
      ∀ i, Module.Finite K (E i) ∧ Algebra.IsSeparable K (E i) := by
  classical
  have : Algebra.FormallyUnramified K A := formallyUnramified_of_isSeparable_commRing K A
  have : IsArtinianRing A := finite_dimensional_algebra_is_artinian K A
  have : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  have : Finite (MaximalSpectrum A) := inferInstance
  let (i : MaximalSpectrum A) : Field (A ⧸ i.asIdeal) := Ideal.Quotient.field i.asIdeal
  have (i : MaximalSpectrum A) : Module.Finite K (A ⧸ i.asIdeal) := inferInstance
  have (i : MaximalSpectrum A) : Algebra.IsSeparable K (A ⧸ i.asIdeal) := inferInstance
  exact ⟨MaximalSpectrum A, inferInstance, fun i => A ⧸ i.asIdeal, inferInstance,
    inferInstance, (IsArtinianRing.equivPi A).restrictScalars K,
    fun i => ⟨inferInstance, inferInstance⟩⟩

/-- The formal sum of a finite family of algebra homomorphisms into a field, recorded as a
finitely supported function on the set of all such homomorphisms. -/
private noncomputable def characterWeight {K : Type u} {A : Type w} {Ω : Type x}
    [Field K] [CommRing A] [Algebra K A] [Field Ω] [Algebra K Ω]
    (ι : Type v) [Fintype ι] (χ : ι → A →ₐ[K] Ω) : (A →ₐ[K] Ω) →₀ Ω :=
  ∑ i, Finsupp.single (χ i) (1 : Ω)

/-- The number of indices at which a finite family of algebra homomorphisms takes a given
value. -/
private noncomputable def characterMultiplicity {K : Type u} {A : Type w} {Ω : Type x}
    [Field K] [CommRing A] [Algebra K A] [Field Ω] [Algebra K Ω]
    (ι : Type v) [Fintype ι] (χ : ι → A →ₐ[K] Ω) (φ : A →ₐ[K] Ω) : ℤ := by
  classical
  exact ∑ i, if χ i = φ then 1 else 0

/-- The coefficient of `φ` in the formal sum of a family is the number of indices mapping to
`φ`. -/
private theorem characterWeight_apply {K : Type u} {A : Type w} {Ω : Type x}
    [Field K] [CommRing A] [Algebra K A] [Field Ω] [Algebra K Ω]
    (ι : Type v) [Fintype ι] (χ : ι → A →ₐ[K] Ω) (φ : A →ₐ[K] Ω) :
    characterWeight ι χ φ = (characterMultiplicity ι χ φ : Ω) := by
  classical
  unfold characterWeight characterMultiplicity
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply, Int.cast_sum, Int.cast_ite, Int.cast_one,
    Int.cast_zero]

/-- Multiplicities are nonnegative. -/
private theorem characterMultiplicity_nonneg {K : Type u} {A : Type w} {Ω : Type x}
    [Field K] [CommRing A] [Algebra K A] [Field Ω] [Algebra K Ω]
    (ι : Type v) [Fintype ι] (χ : ι → A →ₐ[K] Ω) (φ : A →ₐ[K] Ω) :
    0 ≤ characterMultiplicity ι χ φ := by
  unfold characterMultiplicity
  refine Finset.sum_nonneg fun i _ => ?_
  split <;> norm_num

/-- An injective family of algebra homomorphisms takes each value at most once, so all its
multiplicities are `0` or `1`. -/
private theorem characterMultiplicity_le_one {K : Type u} {A : Type w} {Ω : Type x}
    [Field K] [CommRing A] [Algebra K A] [Field Ω] [Algebra K Ω]
    (ι : Type v) [Fintype ι] {χ : ι → A →ₐ[K] Ω} (hχ : Function.Injective χ)
    (φ : A →ₐ[K] Ω) : characterMultiplicity ι χ φ ≤ 1 := by
  classical
  unfold characterMultiplicity
  by_cases h : ∃ i₀, χ i₀ = φ
  · obtain ⟨i₀, hi₀⟩ := h
    have key : ∀ i, (if χ i = φ then (1 : ℤ) else 0) = if i = i₀ then 1 else 0 := by
      intro i
      by_cases hi : i = i₀
      · subst hi
        simp [hi₀]
      · rw [ite_eq_right hi, ite_eq_right]
        exact fun hh => hi (hχ (hh.trans hi₀.symm))
    rw [Finset.sum_congr rfl fun i _ => key i]
    simp
  · have key : ∀ i, (if χ i = φ then (1 : ℤ) else 0) = 0 :=
      fun i => ite_eq_right fun hh => h ⟨i, hh⟩
    rw [Finset.sum_congr rfl fun i _ => key i]
    simp

/-- A homomorphism occurs in a finite family exactly when its multiplicity is positive. -/
private theorem characterMultiplicity_pos_iff {K : Type u} {A : Type w} {Ω : Type x}
    [Field K] [CommRing A] [Algebra K A] [Field Ω] [Algebra K Ω]
    (ι : Type v) [Fintype ι] (χ : ι → A →ₐ[K] Ω) (φ : A →ₐ[K] Ω) :
    0 < characterMultiplicity ι χ φ ↔ ∃ i, χ i = φ := by
  classical
  unfold characterMultiplicity
  constructor
  · intro h
    by_contra hno
    have key : ∀ i, (if χ i = φ then (1 : ℤ) else 0) = 0 :=
      fun i => ite_eq_right fun hh => hno ⟨i, hh⟩
    rw [Finset.sum_congr rfl fun i _ => key i] at h
    simp at h
  · rintro ⟨i, hi⟩
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · split <;> norm_num
    · simp [hi]

/-- The linear combination attached to the formal sum of a family is the sum of the underlying
linear maps. -/
private theorem linearCombination_characterWeight {K : Type u} {A : Type w} {Ω : Type x}
    [Field K] [CommRing A] [Algebra K A] [Field Ω] [Algebra K Ω]
    (ι : Type v) [Fintype ι] (χ : ι → A →ₐ[K] Ω) :
    Finsupp.linearCombination Ω AlgHom.toLinearMap (characterWeight ι χ) =
      ∑ i, (χ i).toLinearMap := by
  classical
  simp [characterWeight, map_sum]

/-- The linear combination attached to the formal sum of the characters
`ψ ∘ pr_j ∘ e ∘ f` is `Tr ∘ f` pushed into an algebraically closed field. -/
private theorem linearCombination_characterWeight_embeddings
    (F : Type u) (A : Type w) (R : Type v) [Field F] [CommRing A] [Algebra F A]
    [CommRing R] [Algebra F R] (I : Type v) [Fintype I] (E : I → Type v)
    [∀ i, Field (E i)] [∀ i, Algebra F (E i)] [∀ i, Module.Finite F (E i)]
    [∀ i, Algebra.IsSeparable F (E i)] (e : R ≃ₐ[F] ∀ i, E i)
    (f : A →ₐ[F] R) (Ω : Type x) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] :
    Finsupp.linearCombination Ω AlgHom.toLinearMap
      (characterWeight (Σ j : I, E j →ₐ[F] Ω)
        (fun q => q.2.comp ((Pi.evalAlgHom F E q.1).comp (e.toAlgHom.comp f)))) =
      (Algebra.linearMap F Ω).comp ((Algebra.trace F R).comp f.toLinearMap) := by
  classical
  rw [linearCombination_characterWeight, Fintype.sum_sigma]
  ext a
  simpa using (trace_comp_sum_embeddings F A R I E e f Ω a).symm

/-- Two surjections onto a finite separable algebra whose trace forms differ by `n > 1` times
an integral combination of trace forms of maps to finite separable algebras have the same
kernel.

Each character of `A` appears with multiplicity `0` or `1` in the trace form of a surjection,
the two multiplicities are congruent modulo `n`, and `n > 1`, so they agree; the two
surjections therefore meet the same characters of `A`, and an element of `A` dies under a
surjection exactly when every character met by it kills that element. -/
private theorem ker_eq_ker_of_trace_sub_trace_eq_zsmul
    (F : Type u) [Field F] [CharZero F]
    (F' : Type v) [CommRing F'] [Algebra F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F']
    (A : Type w) [CommRing A] [Algebra F A] [FiniteDimensional F A]
    {r : ℕ} (F_i : Fin r → Type x)
    [∀ i, CommRing (F_i i)] [∀ i, Algebra F (F_i i)]
    [∀ i, FiniteDimensional F (F_i i)] [∀ i, Algebra.IsSeparable F (F_i i)]
    (σ σ' : A →ₐ[F] F') (σ_i : ∀ i, A →ₐ[F] F_i i)
    (hσ : Function.Surjective σ) (hσ' : Function.Surjective σ')
    (n : ℤ) (hn : 1 < n) (m : Fin r → ℤ)
    (hrel :
      (Algebra.trace F F').comp σ.toLinearMap -
          (Algebra.trace F F').comp σ'.toLinearMap =
        n • ∑ i, m i • (Algebra.trace F (F_i i)).comp (σ_i i).toLinearMap) :
    RingHom.ker σ.toRingHom = RingHom.ker σ'.toRingHom := by
  classical
  obtain ⟨I, hI, E, hEf, hEa, e, hEprops⟩ := exists_finite_separable_product F F'
  let : _root_.Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let (j : I) : Field (E j) := hEf j
  let (j : I) : Algebra F (E j) := hEa j
  let (j : I) : Module.Finite F (E j) := (hEprops j).1
  let (j : I) : Algebra.IsSeparable F (E j) := (hEprops j).2
  let (j : I) : FiniteDimensional F (E j) := inferInstance
  have hFi : ∀ i, ∃ (J : Type x) (_ : _root_.Finite J) (G : J → Type x)
      (_ : ∀ j, Field (G j)) (_ : ∀ j, Algebra F (G j))
      (eᵢ : F_i i ≃ₐ[F] ∀ j, G j),
      ∀ j, Module.Finite F (G j) ∧ Algebra.IsSeparable F (G j) :=
    fun i => exists_finite_separable_product F (F_i i)
  choose J hJ G hGf hGa eᵢ hGprops using hFi
  let (i : Fin r) : _root_.Finite (J i) := hJ i
  let (i : Fin r) : Fintype (J i) := Fintype.ofFinite (J i)
  let (i : Fin r) (j : J i) : Field (G i j) := hGf i j
  let (i : Fin r) (j : J i) : Algebra F (G i j) := hGa i j
  let (i : Fin r) (j : J i) : Module.Finite F (G i j) := (hGprops i j).1
  let (i : Fin r) (j : J i) : Algebra.IsSeparable F (G i j) := (hGprops i j).2
  let (i : Fin r) (j : J i) : FiniteDimensional F (G i j) := inferInstance
  let Ω := AlgebraicClosure F
  let : Field Ω := inferInstance
  let : Algebra F Ω := inferInstance
  let : IsAlgClosed Ω := inferInstance
  let (j : I) : Fintype (E j →ₐ[F] Ω) := minpoly.AlgHom.fintype F (E j) Ω
  let (i : Fin r) (j : J i) : Fintype (G i j →ₐ[F] Ω) := minpoly.AlgHom.fintype F (G i j) Ω
  let P := Σ j : I, E j →ₐ[F] Ω
  let chr : (A →ₐ[F] F') → P → (A →ₐ[F] Ω) := fun f p =>
    p.2.comp ((Pi.evalAlgHom F E p.1).comp (e.toAlgHom.comp f))
  let CR (i : Fin r) := characterWeight (Σ j : J i, G i j →ₐ[F] Ω)
    (fun q => q.2.comp ((Pi.evalAlgHom F (G i) q.1).comp
      ((eᵢ i).toAlgHom.comp (σ_i i))))
  let W : (A →ₐ[F] Ω) →₀ Ω :=
    characterWeight P (chr σ) - characterWeight P (chr σ') - (n : Ω) • ∑ i, (m i : Ω) • CR i
  have hformula (f : A →ₐ[F] F') :
      Finsupp.linearCombination Ω AlgHom.toLinearMap (characterWeight P (chr f)) =
        (Algebra.linearMap F Ω).comp ((Algebra.trace F F').comp f.toLinearMap) :=
    linearCombination_characterWeight_embeddings F A F' I E e f Ω
  have hRformula (i : Fin r) :
      Finsupp.linearCombination Ω AlgHom.toLinearMap (CR i) =
        (Algebra.linearMap F Ω).comp
          ((Algebra.trace F (F_i i)).comp (σ_i i).toLinearMap) :=
    linearCombination_characterWeight_embeddings F A (F_i i) (J i) (G i) (eᵢ i) (σ_i i) Ω
  have hcombo : Finsupp.linearCombination Ω AlgHom.toLinearMap W = 0 := by
    have hrelΩ (a : A) :
        algebraMap F Ω ((Algebra.trace F F') (σ a) - (Algebra.trace F F') (σ' a)) =
          (n : Ω) * ∑ i, (m i : Ω) *
            algebraMap F Ω ((Algebra.trace F (F_i i)) (σ_i i a)) := by
      have hh := congrArg (fun f : A →ₗ[F] F => algebraMap F Ω (f a)) hrel
      simpa [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
        map_sub, map_sum, map_zsmul] using hh
    calc
      Finsupp.linearCombination Ω AlgHom.toLinearMap W =
          Finsupp.linearCombination Ω AlgHom.toLinearMap (characterWeight P (chr σ)) -
            Finsupp.linearCombination Ω AlgHom.toLinearMap (characterWeight P (chr σ')) -
            (n : Ω) • ∑ i, (m i : Ω) •
              Finsupp.linearCombination Ω AlgHom.toLinearMap (CR i) := by
          simp [W, map_sub, map_sum, map_smul]
    _ = 0 := by
          rw [hformula σ, hformula σ']
          simp_rw [hRformula]
          ext a
          simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
            LinearMap.sum_apply, LinearMap.zero_apply, Algebra.linearMap_apply,
            AlgHom.toLinearMap_apply, smul_eq_mul]
          have hrel' := hrelΩ a
          rw [map_sub] at hrel'
          linear_combination hrel'
  have hW : W = 0 :=
    (linearIndependent_iff.mp (linearIndependent_algHom_toLinearMap F A Ω)) W hcombo
  -- a surjection meets each character of `A` at most once
  have hinj (f : A →ₐ[F] F') (hf : Function.Surjective f) : Function.Injective (chr f) := by
    rintro ⟨k, η⟩ ⟨k', η'⟩ hpq
    have hval : ∀ y : F', η ((Pi.evalAlgHom F E k) (e y)) =
        η' ((Pi.evalAlgHom F E k') (e y)) := by
      intro y
      obtain ⟨a, rfl⟩ := hf y
      simpa [chr] using AlgHom.congr_fun hpq a
    have hk : k = k' := by
      by_contra hkk
      have hv := hval (e.symm (Pi.single k (1 : E k)))
      simp only [AlgEquiv.apply_symm_apply, Pi.evalAlgHom_apply, Pi.single_eq_same, map_one,
        ne_eq, Ne.symm hkk, not_false_eq_true, Pi.single_eq_of_ne, map_zero] at hv
      exact one_ne_zero hv
    subst hk
    have hη : η = η' := by
      ext z
      have hv := hval (e.symm (Pi.single k z))
      simpa using hv
    subst hη
    rfl
  -- the two multiplicities are congruent modulo `n`, and both lie in `{0, 1}`
  have hmulteq : ∀ φ : A →ₐ[F] Ω,
      characterMultiplicity P (chr σ) φ = characterMultiplicity P (chr σ') φ := by
    intro φ
    have hcoeff : W φ = 0 := by simp [hW]
    have hInt : characterMultiplicity P (chr σ) φ - characterMultiplicity P (chr σ') φ =
        n * ∑ i, m i * characterMultiplicity (Σ j : J i, G i j →ₐ[F] Ω)
          (fun q => q.2.comp ((Pi.evalAlgHom F (G i) q.1).comp
            ((eᵢ i).toAlgHom.comp (σ_i i)))) φ := by
      apply Int.cast_injective (α := Ω)
      have hc := hcoeff
      simp [W, CR, characterWeight_apply] at hc
      push_cast
      linear_combination hc
    have h1 := characterMultiplicity_nonneg P (chr σ) φ
    have h2 := characterMultiplicity_le_one P (hinj σ hσ) φ
    have h3 := characterMultiplicity_nonneg P (chr σ') φ
    have h4 := characterMultiplicity_le_one P (hinj σ' hσ') φ
    have habs : |characterMultiplicity P (chr σ) φ -
        characterMultiplicity P (chr σ') φ| < n := by
      rw [abs_lt]
      omega
    have hzero := Int.eq_zero_of_abs_lt_dvd ⟨_, hInt⟩ habs
    omega
  -- the characters of `A` met by `σ` are exactly those met by `σ'`
  have hrange : ∀ φ : A →ₐ[F] Ω, (∃ p : P, chr σ p = φ) ↔ ∃ p : P, chr σ' p = φ := by
    intro φ
    rw [← characterMultiplicity_pos_iff P (chr σ) φ,
      ← characterMultiplicity_pos_iff P (chr σ') φ, hmulteq φ]
  -- an element dies under a surjection exactly when every character met by it kills it
  have hmem (f : A →ₐ[F] F') (a : A) : f a = 0 ↔ ∀ p : P, chr f p a = 0 := by
    refine ⟨fun h p => by simp [chr, h], fun h => ?_⟩
    apply e.injective
    rw [map_zero]
    refine funext fun j => ?_
    change (e (f a)) j = 0
    obtain ⟨ψ⟩ := IntermediateField.nonempty_algHom_of_splits
      (F := F) (E := E j) (K := Ω) (fun y =>
        ⟨Algebra.IsIntegral.isIntegral y, IsAlgClosed.splits _⟩)
    have hv := h ⟨j, ψ⟩
    simp only [chr, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
      Pi.evalAlgHom_apply, map_eq_zero] at hv
    exact hv
  ext a
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [hmem σ a, hmem σ' a]
  constructor
  · intro h p
    obtain ⟨q, hq⟩ := (hrange (chr σ' p)).mpr ⟨p, rfl⟩
    rw [← hq]
    exact h q
  · intro h p
    obtain ⟨q, hq⟩ := (hrange (chr σ p)).mp ⟨p, rfl⟩
    rw [← hq]
    exact h q

/-- **Stacks Project, Tag 0FHT**, in the corrected form recorded as a Stacks erratum.

Over a field `F` of characteristic zero, let `σ, σ' : A → F'` be surjections from a finite
`F`-algebra onto a finite separable `F`-algebra, and let `σ i : A → F i` be `F`-algebra maps to
finite separable `F`-algebras. If

```
Tr_{F'/F} ∘ σ - Tr_{F'/F} ∘ σ' = n (∑ m i * Tr_{F i/F} ∘ σ i)
```

with `n > 1` and the `m i` integers, then `σ' = θ ∘ σ` for an `F`-algebra automorphism `θ` of
`F'`; equivalently `Tr_{F'/F} ∘ σ = Tr_{F'/F} ∘ σ'` and `ker σ = ker σ'`.

As printed, the tag concludes `σ = σ'`. That conclusion is refuted by
`Stacks.WeilCohomology.not_traceRelationStatement`, which takes `F = ℝ`, `F' = A = ℂ`,
`σ = id` and `σ' = ` complex conjugation. An automorphism of `F'` is invisible to the trace
relation, and the displayed conclusion is exactly what the relation does see. -/
@[stacks 0FHT "as printed the tag concludes σ = σ' from surjectivity of σ and σ' alone; \
  `Stacks.WeilCohomology.not_traceRelationStatement` refutes that with F = ℝ, F' = A = ℂ, \
  σ = id and σ' = complex conjugation. This declaration is the corrected statement, \
  under the source's own hypotheses: σ' = θ ∘ σ for an \
  F-algebra automorphism θ of F', equivalently Tr ∘ σ = Tr ∘ σ' together with ker σ = ker σ'"]
theorem AlgHom.exists_algEquiv_comp_eq_of_trace_sub_trace_eq_zsmul
    (F : Type u) [Field F] [CharZero F]
    (F' : Type v) [CommRing F'] [Algebra F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F']
    (A : Type w) [CommRing A] [Algebra F A] [FiniteDimensional F A]
    {r : ℕ} (F_i : Fin r → Type x)
    [∀ i, CommRing (F_i i)] [∀ i, Algebra F (F_i i)]
    [∀ i, FiniteDimensional F (F_i i)] [∀ i, Algebra.IsSeparable F (F_i i)]
    (σ σ' : A →ₐ[F] F') (σ_i : ∀ i, A →ₐ[F] F_i i)
    (hσ : Function.Surjective σ) (hσ' : Function.Surjective σ')
    (n : ℤ) (hn : 1 < n) (m : Fin r → ℤ)
    (hrel :
      (Algebra.trace F F').comp σ.toLinearMap -
          (Algebra.trace F F').comp σ'.toLinearMap =
        n • ∑ i, m i • (Algebra.trace F (F_i i)).comp (σ_i i).toLinearMap) :
    (∃ θ : F' ≃ₐ[F] F', σ' = (θ : F' →ₐ[F] F').comp σ) ∧
      (Algebra.trace F F').comp σ.toLinearMap =
        (Algebra.trace F F').comp σ'.toLinearMap ∧
      RingHom.ker σ.toRingHom = RingHom.ker σ'.toRingHom := by
  have hker :=
    ker_eq_ker_of_trace_sub_trace_eq_zsmul F F' A F_i σ σ' σ_i hσ hσ' n hn m hrel
  set g := AlgHom.liftOfSurjective σ hσ σ' hker.le
  set g' := AlgHom.liftOfSurjective σ' hσ' σ hker.ge
  have hgσ : ∀ a : A, g (σ a) = σ' a := fun a => AlgHom.liftOfSurjective_apply _ _ _ _ a
  have hg'σ' : ∀ a : A, g' (σ' a) = σ a := fun a => AlgHom.liftOfSurjective_apply _ _ _ _ a
  have h₁ : g.comp g' = AlgHom.id F F' := by
    ext y
    obtain ⟨a, rfl⟩ := hσ' y
    simp [hg'σ' a, hgσ a]
  have h₂ : g'.comp g = AlgHom.id F F' := by
    ext y
    obtain ⟨a, rfl⟩ := hσ y
    simp [hgσ a, hg'σ' a]
  have hθ : σ' = ((AlgEquiv.ofAlgHom g g' h₁ h₂ : F' ≃ₐ[F] F') : F' →ₐ[F] F').comp σ := by
    ext a
    rw [AlgEquiv.toAlgHom_ofAlgHom]
    exact (hgσ a).symm
  refine ⟨⟨AlgEquiv.ofAlgHom g g' h₁ h₂, hθ⟩, ?_, hker⟩
  ext a
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  conv_rhs => rw [hθ]
  rw [AlgHom.comp_apply, AlgEquiv.toAlgHom_ofAlgHom]
  exact (Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom g g' h₁ h₂) (σ a)).symm

/-- The trace maps of two surjections related as in Tag 0FHT agree. -/
theorem AlgHom.trace_comp_eq_trace_comp_of_trace_sub_trace_eq_zsmul
    (F : Type u) [Field F] [CharZero F]
    (F' : Type v) [CommRing F'] [Algebra F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F']
    (A : Type w) [CommRing A] [Algebra F A] [FiniteDimensional F A]
    {r : ℕ} (F_i : Fin r → Type x)
    [∀ i, CommRing (F_i i)] [∀ i, Algebra F (F_i i)]
    [∀ i, FiniteDimensional F (F_i i)] [∀ i, Algebra.IsSeparable F (F_i i)]
    (σ σ' : A →ₐ[F] F') (σ_i : ∀ i, A →ₐ[F] F_i i)
    (hσ : Function.Surjective σ) (hσ' : Function.Surjective σ')
    (n : ℤ) (hn : 1 < n) (m : Fin r → ℤ)
    (hrel :
      (Algebra.trace F F').comp σ.toLinearMap -
          (Algebra.trace F F').comp σ'.toLinearMap =
        n • ∑ i, m i • (Algebra.trace F (F_i i)).comp (σ_i i).toLinearMap) :
    (Algebra.trace F F').comp σ.toLinearMap =
      (Algebra.trace F F').comp σ'.toLinearMap :=
  (AlgHom.exists_algEquiv_comp_eq_of_trace_sub_trace_eq_zsmul
    F F' A F_i σ σ' σ_i hσ hσ' n hn m hrel).2.1

/-- Two surjections onto a finite separable algebra that are related as in Tag 0FHT and have a
common section are equal: the automorphism of
`AlgHom.exists_algEquiv_comp_eq_of_trace_sub_trace_eq_zsmul` fixes every element of the target.

This is the form the chapter uses at Tag 0FHU, where the section is the pullback along
`H^0(Spec k') → H^0(X)`. -/
theorem AlgHom.eq_of_trace_sub_trace_eq_zsmul
    (F : Type u) [Field F] [CharZero F]
    (F' : Type v) [CommRing F'] [Algebra F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F']
    (A : Type w) [CommRing A] [Algebra F A] [FiniteDimensional F A]
    {r : ℕ} (F_i : Fin r → Type x)
    [∀ i, CommRing (F_i i)] [∀ i, Algebra F (F_i i)]
    [∀ i, FiniteDimensional F (F_i i)] [∀ i, Algebra.IsSeparable F (F_i i)]
    (σ σ' : A →ₐ[F] F') (σ_i : ∀ i, A →ₐ[F] F_i i)
    (hσ : Function.Surjective σ) (hσ' : Function.Surjective σ')
    (τ : F' →ₐ[F] A) (hτ : σ.comp τ = AlgHom.id F F')
    (hτ' : σ'.comp τ = AlgHom.id F F')
    (n : ℤ) (hn : 1 < n) (m : Fin r → ℤ)
    (hrel :
      (Algebra.trace F F').comp σ.toLinearMap -
          (Algebra.trace F F').comp σ'.toLinearMap =
        n • ∑ i, m i • (Algebra.trace F (F_i i)).comp (σ_i i).toLinearMap) :
    σ = σ' := by
  obtain ⟨⟨θ, hθ⟩, -, -⟩ :=
    AlgHom.exists_algEquiv_comp_eq_of_trace_sub_trace_eq_zsmul
      F F' A F_i σ σ' σ_i hσ hσ' n hn m hrel
  have hfix : ∀ y : F', θ y = y := by
    intro y
    have h1 : σ (τ y) = y := by simpa using AlgHom.congr_fun hτ y
    have h2 : σ' (τ y) = y := by simpa using AlgHom.congr_fun hτ' y
    have h3 := AlgHom.congr_fun hθ (τ y)
    rw [h2, AlgHom.comp_apply, h1] at h3
    exact h3.symm
  ext a
  have h4 := AlgHom.congr_fun hθ a
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hfix (σ a)] at h4
  exact h4.symm
