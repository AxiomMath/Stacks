module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.FinitePresentation

/-!
# Smoothness of a quotient from a Jacobian retraction modulo a nil ideal

Let `P` be a formally smooth `R`-algebra and `f₁, …, fᵣ ∈ P`, and put `S = P / (f₁, …, fᵣ)`.
If some `S`-linear map `ψ : S ⊗_P Ω_{P/R} → Sʳ` sends `1 ⊗ d fᵢ` to the `i`-th basis vector
modulo an ideal of `S` contained in the nilradical, then `S` is formally smooth over `R`.
-/

@[expose] public section

open TensorProduct KaehlerDifferential

namespace Algebra.FormallySmooth

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]

/-- The kernel of the quotient map `P → P / I` is `I`. -/
private theorem ker_algebraMap_quotient {I : Ideal P} :
    RingHom.ker (algebraMap P (P ⧸ I)) = I :=
  Ideal.mk_ker

/-- A ring homomorphism preserves the entries of a standard basis vector. -/
private theorem map_pi_single_one_apply {A B : Type*} [Semiring A] [Semiring B] (g : A →+* B)
    {r : ℕ} (i j : Fin r) : g ((Pi.single i 1 : Fin r → A) j) = (Pi.single i 1 : Fin r → B) j := by
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp [Pi.single_eq_of_ne' h]

/-- The generators `fᵢ` of the ideal they span lie in the kernel of the quotient map. -/
theorem mem_ker_quotient_span {r : ℕ} (f : Fin r → P) (i : Fin r) :
    f i ∈ RingHom.ker (algebraMap P (P ⧸ Ideal.span (Set.range f))) := by
  rw [ker_algebraMap_quotient]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- **The basis map to the conormal module.** For `S = P / (f₁, …, fᵣ)`, the `P`-linear map
`Sʳ → I/I²`, `I = (f₁, …, fᵣ)`, sending the `i`-th basis vector to the class of `fᵢ`. -/
noncomputable def cotangentBasisMap {r : ℕ} (f : Fin r → P) :
    (Fin r → P ⧸ Ideal.span (Set.range f)) →ₗ[P]
      (RingHom.ker (algebraMap P (P ⧸ Ideal.span (Set.range f)))).Cotangent :=
  ∑ i, ((Ideal.span (Set.range f)).liftQ (LinearMap.toSpanSingleton P _
      ((RingHom.ker (algebraMap P (P ⧸ Ideal.span (Set.range f)))).toCotangent
        ⟨f i, mem_ker_quotient_span f i⟩)) (by
      intro p hp
      simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      refine Ideal.Cotangent.smul_eq_zero_of_mem ?_ _
      rw [show RingHom.ker (algebraMap P (P ⧸ Ideal.span (Set.range f))) =
        Ideal.span (Set.range f) from Ideal.mk_ker]
      exact hp)).comp (LinearMap.proj i)

/-- `cotangentBasisMap f` sends the `i`-th basis vector to the class of `fᵢ` in `I/I²`. -/
theorem cotangentBasisMap_single {r : ℕ} (f : Fin r → P) (i : Fin r) :
    cotangentBasisMap f (Pi.single i 1) =
      (RingHom.ker (algebraMap P (P ⧸ Ideal.span (Set.range f)))).toCotangent
        ⟨f i, mem_ker_quotient_span f i⟩ := by
  unfold cotangentBasisMap
  rw [LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
    change (Ideal.span (Set.range f)).liftQ _ _ (Submodule.Quotient.mk 1) = _
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

/-- The classes of the generators span the conormal module. -/
theorem span_range_toCotangent_eq_top {r : ℕ} (f : Fin r → P) :
    Submodule.span P (Set.range fun i =>
      (RingHom.ker (algebraMap P (P ⧸ Ideal.span (Set.range f)))).toCotangent
        ⟨f i, mem_ker_quotient_span f i⟩) = ⊤ := by
  set I := RingHom.ker (algebraMap P (P ⧸ Ideal.span (Set.range f)))
  refine (Submodule.eq_top_iff').2 fun x => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := I.toCotangent_surjective x
  have hy' : y ∈ Ideal.span (Set.range f) := ker_algebraMap_quotient.le hy
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun P).1 hy'
  have : (⟨y, hy⟩ : I) = ∑ i, a i • ⟨f i, mem_ker_quotient_span f i⟩ := by
    ext1
    simp [← ha]
  rw [this, map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The map `cotangentBasisMap f : Sʳ → I/I²` is surjective. -/
theorem cotangentBasisMap_surjective {r : ℕ} (f : Fin r → P) :
    Function.Surjective (cotangentBasisMap f) := by
  rw [← LinearMap.range_eq_top]
  refine top_le_iff.1 ?_
  rw [← span_range_toCotangent_eq_top f, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨Pi.single i 1, cotangentBasisMap_single f i⟩

/-- Let `P` be formally smooth over `R` and `S = P / (f₁, …, fᵣ)`. If some `S`-linear map
`l : S ⊗_P Ω_{P/R} → Sʳ` sends each `1 ⊗ d fᵢ` to the `i`-th basis vector, then `S` is formally
smooth over `R`. -/
theorem quotient_span_of_retraction [FormallySmooth R P] {r : ℕ} (f : Fin r → P)
    (l : (P ⧸ Ideal.span (Set.range f)) ⊗[P] Ω[P⁄R] →ₗ[P ⧸ Ideal.span (Set.range f)]
      (Fin r → P ⧸ Ideal.span (Set.range f)))
    (hl : ∀ i, l (1 ⊗ₜ D R P (f i)) = Pi.single i 1) :
    FormallySmooth R (P ⧸ Ideal.span (Set.range f)) := by
  rw [FormallySmooth.iff_split_injection (P := P) (A := P ⧸ Ideal.span (Set.range f))
    Ideal.Quotient.mk_surjective]
  refine ⟨cotangentBasisMap f ∘ₗ l.restrictScalars P, ?_⟩
  refine LinearMap.ext_on_range (span_range_toCotangent_eq_top f) fun i => ?_
  change cotangentBasisMap f (l (1 ⊗ₜ D R P (f i))) = _
  rw [hl i, cotangentBasisMap_single]
  rfl

/-- Let `P` be formally smooth over `R`, `S = P / (f₁, …, fᵣ)` and `K ⊆ S` an ideal inside the
nilradical. If some `S`-linear map `ψ : S ⊗_P Ω_{P/R} → Sʳ` sends each `1 ⊗ d fᵢ` to the `i`-th
basis vector modulo `K`, then `S` is formally smooth over `R`. -/
theorem quotient_span_of_retraction_mod_nil [FormallySmooth R P] {r : ℕ} (f : Fin r → P)
    (K : Ideal (P ⧸ Ideal.span (Set.range f))) (hK : K ≤ nilradical _)
    (ψ : (P ⧸ Ideal.span (Set.range f)) ⊗[P] Ω[P⁄R] →ₗ[P ⧸ Ideal.span (Set.range f)]
      (Fin r → P ⧸ Ideal.span (Set.range f)))
    (hψ : ∀ i j, ψ (1 ⊗ₜ D R P (f i)) j -
      (Pi.single i 1 : Fin r → P ⧸ Ideal.span (Set.range f)) j ∈ K) :
    FormallySmooth R (P ⧸ Ideal.span (Set.range f)) := by
  set S := P ⧸ Ideal.span (Set.range f)
  let M : Matrix (Fin r) (Fin r) S := Matrix.of fun i j => ψ (1 ⊗ₜ D R P (f i)) j
  have hdet : M.det - 1 ∈ K := by
    rw [← Ideal.Quotient.eq, map_one, RingHom.map_det]
    have : (Ideal.Quotient.mk K).mapMatrix M = 1 := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply]
      rw [Matrix.one_apply, Ideal.Quotient.eq.2 (hψ i j), map_pi_single_one_apply,
        Pi.single_apply]
      exact if_congr eq_comm rfl rfl
    rw [this, Matrix.det_one]
  have hunit : IsUnit M.det := by
    simpa using (mem_nilradical.1 (hK hdet)).isUnit_one_add
  refine quotient_span_of_retraction f ((Matrix.vecMulLinear M⁻¹) ∘ₗ ψ) fun i => ?_
  ext k
  have := congrFun (congrFun (Matrix.mul_nonsing_inv M hunit) i) k
  simp only [Matrix.mul_apply, M, Matrix.of_apply] at this
  simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct]
  rw [this, Matrix.one_apply, Pi.single_apply]
  simp [eq_comm]

/-- **Formal smoothness of `P / (f₁, …, fᵣ)` from a derivation modulo a nil ideal.** Let `P` be
formally smooth over `R`, `S = P / (f₁, …, fᵣ)` and `K ⊆ S` an ideal inside the nilradical. If
some `R`-derivation `δ : P → (S / K)ʳ` sends each `fᵢ` to the `i`-th basis vector, then `S` is
formally smooth over `R`. -/
theorem quotient_span_of_derivation_mod_nil [FormallySmooth R P] {r : ℕ} (f : Fin r → P)
    (K : Ideal (P ⧸ Ideal.span (Set.range f))) (hK : K ≤ nilradical _)
    (δ : Derivation R P (Fin r → (P ⧸ Ideal.span (Set.range f)) ⧸ K))
    (hδ : ∀ i, δ (f i) = Pi.single i 1) :
    FormallySmooth R (P ⧸ Ideal.span (Set.range f)) := by
  set S := P ⧸ Ideal.span (Set.range f)
  let G : S ⊗[P] Ω[P⁄R] →ₗ[S] (Fin r → S ⧸ K) := δ.liftKaehlerDifferential.liftBaseChange S
  let q : (Fin r → S) →ₗ[S] (Fin r → S ⧸ K) :=
    LinearMap.pi fun i => (Ideal.Quotient.mkₐ S K).toLinearMap ∘ₗ LinearMap.proj i
  have hq : Function.Surjective q := by
    intro v
    refine ⟨fun i => Function.surjInv Ideal.Quotient.mk_surjective (v i), ?_⟩
    ext i
    simp [q, Function.surjInv_eq]
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property q G hq
  refine quotient_span_of_retraction_mod_nil f K hK ψ fun i j => ?_
  rw [← Ideal.Quotient.eq]
  have h1 := congrFun (LinearMap.congr_fun hψ (1 ⊗ₜ D R P (f i))) j
  simp only [LinearMap.comp_apply, q, LinearMap.pi_apply, LinearMap.proj_apply,
    AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, G, LinearMap.liftBaseChange_tmul, one_smul,
    Derivation.liftKaehlerDifferential_comp_D, hδ i] at h1
  rw [h1]
  exact (map_pi_single_one_apply (Ideal.Quotient.mk K) i j).symm

/-- **The derivation at the reduced level.** Let `P₀` be formally smooth over `R₀`, let
`f₁, …, fᵣ ∈ P₀` and `S₀ = P₀ / (f₁, …, fᵣ)`. If `S₀` is formally smooth over `R₀` and the
classes of the `fᵢ` are `S₀`-linearly independent in the conormal module, then some
`R₀`-derivation `P₀ → S₀ʳ` sends each `fᵢ` to the `i`-th basis vector. -/
theorem exists_derivation_of_quotient_span {R₀ P₀ : Type*} [CommRing R₀] [CommRing P₀]
    [Algebra R₀ P₀] [FormallySmooth R₀ P₀] {r : ℕ} (f : Fin r → P₀)
    [FormallySmooth R₀ (P₀ ⧸ Ideal.span (Set.range f))]
    (hinj : Function.Injective (cotangentBasisMap f)) :
    ∃ δ : Derivation R₀ P₀ (Fin r → P₀ ⧸ Ideal.span (Set.range f)),
      ∀ i, δ (f i) = Pi.single i 1 := by
  set S₀ := P₀ ⧸ Ideal.span (Set.range f)
  obtain ⟨L, hL⟩ := (FormallySmooth.iff_split_injection (R := R₀) (P := P₀) (A := S₀)
    Ideal.Quotient.mk_surjective).1 inferInstance
  let e := LinearEquiv.ofBijective (cotangentBasisMap f) ⟨hinj, cotangentBasisMap_surjective f⟩
  let l : Ω[P₀⁄R₀] →ₗ[P₀] (Fin r → S₀) :=
    (e.symm.toLinearMap ∘ₗ L) ∘ₗ (TensorProduct.mk P₀ S₀ Ω[P₀⁄R₀] 1)
  refine ⟨l.compDer (D R₀ P₀), fun i => ?_⟩
  have h1 : L (1 ⊗ₜ D R₀ P₀ (f i)) =
      (RingHom.ker (algebraMap P₀ S₀)).toCotangent ⟨f i, mem_ker_quotient_span f i⟩ :=
    LinearMap.congr_fun hL
      ((RingHom.ker (algebraMap P₀ S₀)).toCotangent ⟨f i, mem_ker_quotient_span f i⟩)
  change e.symm (L (1 ⊗ₜ D R₀ P₀ (f i))) = _
  rw [h1, LinearEquiv.symm_apply_eq]
  exact (cotangentBasisMap_single f i).symm

/-- **Formal smoothness of `P / (f₁, …, fᵣ)` from a derivation on the reduction.** Let `P` be
formally smooth over `R`, let `J ⊆ R` be an ideal inside the nilradical, and write
`P₀ = P / JP`. If some `R`-derivation `P₀ → (P₀ / (f̄₁, …, f̄ᵣ))ʳ` sends each `f̄ᵢ` to the
`i`-th basis vector, then `P / (f₁, …, fᵣ)` is formally smooth over `R`. -/
theorem quotient_span_of_derivation_reduction [FormallySmooth R P] (J : Ideal R)
    (hJ : J ≤ nilradical R) {r : ℕ} (f : Fin r → P)
    (δ₀ : Derivation R (P ⧸ J.map (algebraMap R P))
      (Fin r → (P ⧸ J.map (algebraMap R P)) ⧸
        Ideal.span (Set.range (Ideal.Quotient.mk (J.map (algebraMap R P)) ∘ f))))
    (hδ₀ : ∀ i, δ₀ (Ideal.Quotient.mk _ (f i)) = Pi.single i 1) :
    FormallySmooth R (P ⧸ Ideal.span (Set.range f)) := by
  set S := P ⧸ Ideal.span (Set.range f)
  set K : Ideal S := J.map (algebraMap R S)
  let J' := J.map (algebraMap R P)
  let I₀ := Ideal.span (Set.range (Ideal.Quotient.mk J' ∘ f))
  let ψ : P →+* S ⧸ K := (Ideal.Quotient.mk K).comp (Ideal.Quotient.mk (Ideal.span (Set.range f)))
  have h1 : J' ≤ RingHom.ker ψ := Ideal.map_le_iff_le_comap.2 fun x hx => by
    simp only [Ideal.mem_comap, RingHom.mem_ker, ψ, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem (algebraMap R S) hx
  let φ₁ : P ⧸ J' →+* S ⧸ K := Ideal.Quotient.lift J' ψ fun a ha => RingHom.mem_ker.1 (h1 ha)
  have h2 : I₀ ≤ RingHom.ker φ₁ := Ideal.span_le.2 <| by
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, Function.comp_apply, φ₁,
      Ideal.Quotient.lift_mk, ψ, RingHom.comp_apply]
    rw [(Ideal.Quotient.eq_zero_iff_mem (I := Ideal.span (Set.range f))).2
      (Ideal.subset_span (Set.mem_range_self i)), map_zero]
  let φ : (P ⧸ J') ⧸ I₀ →+* S ⧸ K := Ideal.Quotient.lift I₀ φ₁ fun a ha => RingHom.mem_ker.1 (h2 ha)
  have hφR : ∀ c : R, φ (algebraMap R ((P ⧸ J') ⧸ I₀) c) = algebraMap R (S ⧸ K) c := fun _ => rfl
  let Dl : P →ₗ[R] (Fin r → S ⧸ K) :=
    { toFun := fun p j => φ (δ₀ (Ideal.Quotient.mk J' p) j)
      map_add' := by
        intro a b
        ext j
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro c a
        ext j
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [show Ideal.Quotient.mk J' (c • a) = c • Ideal.Quotient.mk J' a from rfl,
          δ₀.map_smul, Pi.smul_apply, Algebra.smul_def, map_mul, hφR, ← Algebra.smul_def] }
  let δ : Derivation R P (Fin r → S ⧸ K) := Derivation.mk' Dl (by
    intro a b
    ext j
    simp only [Dl, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Derivation.leibniz, Pi.add_apply,
      Pi.smul_apply, map_add]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, Algebra.smul_def,
      Algebra.smul_def]
    rfl)
  refine quotient_span_of_derivation_mod_nil f K ?_ δ fun i => ?_
  · exact Ideal.map_le_iff_le_comap.2 fun x hx =>
      mem_nilradical.2 ((mem_nilradical.1 (hJ hx)).map (algebraMap R S))
  · ext j
    change φ (δ₀ (Ideal.Quotient.mk (J.map (algebraMap R P)) (f i)) j) = _
    rw [hδ₀ i]
    exact map_pi_single_one_apply φ i j

end Algebra.FormallySmooth
