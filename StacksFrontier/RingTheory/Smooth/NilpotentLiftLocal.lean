module

public import StacksFrontier.RingTheory.Smooth.NilpotentLiftQuotient
public import StacksFrontier.RingTheory.Smooth.LocalLeftInverse
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The Jacobian derivation at a local ring, and flat transfer of minimality

Let `P₀` be a local ring formally smooth over `R₀` and `f₁, …, fᵣ ∈ 𝔪` with `P₀ / (f)` formally
smooth over `R₀`. If the `fᵢ` are minimal generators of `(f)` (no relation `∑ aᵢ fᵢ ∈ 𝔪 (f)`
with some `aᵢ ∉ 𝔪`), then some `R₀`-derivation `P₀ → (P₀ / (f))ʳ` sends `fᵢ` to the `i`-th
basis vector.

Minimality is transported along flat local maps by the equational criterion for flatness: if
every relation among the `fᵢ` in `Q` has coefficients in a prime `𝔮₀`, then the images of the
`fᵢ` are minimal generators in any flat local `Q`-algebra whose maximal ideal lies over `𝔮₀`.
-/

@[expose] public section

open TensorProduct KaehlerDifferential IsLocalRing

namespace Algebra.FormallySmooth

/-- An element of an ideal `I ≤ 𝔪` whose class in `I/I²` lies in `𝔪 · I/I²` lies in `𝔪 I`. -/
theorem mem_mul_of_toCotangent_mem_smul {P₀ : Type*} [CommRing P₀] {m I : Ideal P₀}
    (hI : I ≤ m) {y : P₀} (hy : y ∈ I)
    (h : I.toCotangent ⟨y, hy⟩ ∈ m • (⊤ : Submodule P₀ I.Cotangent)) : y ∈ m * I := by
  have htop : (⊤ : Submodule P₀ I.Cotangent) = (⊤ : Submodule P₀ I).map I.toCotangent := by
    rw [Submodule.map_top, LinearMap.range_eq_top.2 I.toCotangent_surjective]
  rw [htop, ← Submodule.map_smul''] at h
  obtain ⟨y', hy', heq⟩ := h
  have hsub : (y' : P₀) ∈ m * I := by
    have : (m • (⊤ : Submodule P₀ I)).map I.subtype = m * I := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, Ideal.smul_eq_mul]
    rw [← this]
    exact ⟨y', hy', rfl⟩
  have h2 : (y : P₀) - y' ∈ I ^ 2 := by
    have := (Ideal.toCotangent_eq I).1 heq.symm
    simpa using this
  have h3 : I ^ 2 ≤ m * I := by
    rw [pow_two]
    exact Ideal.mul_mono_left hI
  have := Ideal.add_mem _ hsub (h3 h2)
  simpa using this

/-- If `I ≤ 𝔪` then `P ⧸ I` sends `𝔪` into its maximal ideal. -/
private theorem mk_mem_maximalIdeal {P : Type*} [CommRing P] [IsLocalRing P] {I : Ideal P}
    [IsLocalRing (P ⧸ I)] (hI : I ≤ maximalIdeal P) {x : P} (hx : x ∈ maximalIdeal P) :
    Ideal.Quotient.mk I x ∈ maximalIdeal (P ⧸ I) := by
  refine (mem_maximalIdeal _).2 fun hu => ?_
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hc
  have : (1 : P) ∈ maximalIdeal P := by
    have := Ideal.sub_mem _ (Ideal.mul_mem_right c' _ hx) (hI hc)
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal P).ne_top ((Ideal.eq_top_iff_one _).2 this)

/-- **The Jacobian derivation at a local ring.** -/
theorem exists_derivation_of_isLocalRing {R₀ P₀ : Type*} [CommRing R₀] [CommRing P₀]
    [Algebra R₀ P₀] [IsLocalRing P₀] [FormallySmooth R₀ P₀] {r : ℕ} (f : Fin r → P₀)
    (hfm : Ideal.span (Set.range f) ≤ maximalIdeal P₀)
    [FormallySmooth R₀ (P₀ ⧸ Ideal.span (Set.range f))]
    (hmin : ∀ a : Fin r → P₀, ∑ i, a i * f i ∈ maximalIdeal P₀ * Ideal.span (Set.range f) →
      ∀ i, a i ∈ maximalIdeal P₀) :
    ∃ δ : Derivation R₀ P₀ (Fin r → P₀ ⧸ Ideal.span (Set.range f)),
      ∀ i, δ (f i) = Pi.single i 1 := by
  classical
  set I := Ideal.span (Set.range f)
  set A := P₀ ⧸ I
  have hItop : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal P₀).ne_top (top_le_iff.1 (h ▸ hfm))
  have : Nontrivial A := Ideal.Quotient.nontrivial_iff.2 hItop
  have : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  obtain ⟨L, hL⟩ := (FormallySmooth.iff_split_injection (R := R₀) (P := P₀) (A := A)
    Ideal.Quotient.mk_surjective).1 inferInstance
  set N := A ⊗[P₀] Ω[P₀⁄R₀]
  let φ : (Fin r → A) →ₗ[A] N := (Pi.basisFun A (Fin r)).constr A fun i => 1 ⊗ₜ D R₀ P₀ (f i)
  have hφe : ∀ i, φ (Pi.single i 1) = 1 ⊗ₜ D R₀ P₀ (f i) := by
    intro i
    rw [← Pi.basisFun_apply A (Fin r) i, (Pi.basisFun A (Fin r)).constr_basis]
  -- the class of `∑ bᵢ fᵢ` in `I/I²` maps to `φ (b̄)`
  have hφkct : ∀ b : Fin r → P₀, φ (fun i => Ideal.Quotient.mk I (b i)) =
      kerCotangentToTensor R₀ P₀ A
        ((RingHom.ker (algebraMap P₀ A)).toCotangent
          ⟨∑ i, b i * f i, Ideal.sum_mem _ fun i _ =>
            Ideal.mul_mem_left _ _ (mem_ker_quotient_span f i)⟩) := by
    intro b
    rw [kerCotangentToTensor_toCotangent]
    have hR : (1 : A) ⊗ₜ[P₀] D R₀ P₀ (∑ i, b i * f i) = ∑ i, b i • ((1 : A) ⊗ₜ D R₀ P₀ (f i)) := by
      rw [map_sum, tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Derivation.leibniz, tmul_add]
      have h0 : (1 : A) ⊗ₜ[P₀] (f i • D R₀ P₀ (b i)) = 0 := by
        rw [← smul_tmul, Algebra.smul_def, mul_one]
        have : algebraMap P₀ A (f i) = 0 := mem_ker_quotient_span f i
        rw [this, zero_tmul]
      rw [h0, add_zero, tmul_smul]
    rw [hR, Module.Basis.constr_apply_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.basisFun_equivFun, LinearEquiv.refl_apply, ← algebraMap_smul A (b i)]
    rfl
  have hφ : ∀ a, φ a ∈ (maximalIdeal A) • (⊤ : Submodule A N) → ∀ i, a i ∈ maximalIdeal A := by
    intro a ha
    set b : Fin r → P₀ := fun i => Function.surjInv Ideal.Quotient.mk_surjective (a i)
    have hab : (fun i => Ideal.Quotient.mk I (b i)) = a := by
      ext i; exact Function.surjInv_eq _ _
    rw [← hab, hφkct b] at ha
    -- push the membership through the retraction
    have hmA : ∀ x ∈ maximalIdeal A, ∃ y ∈ maximalIdeal P₀, Ideal.Quotient.mk I y = x := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨y, ?_, rfl⟩
      by_contra hy
      have hu : IsUnit y := by
        by_contra h'; exact hy ((mem_maximalIdeal _).2 h')
      exact (mem_maximalIdeal _).1 hx (hu.map _)
    have hle : ∀ n ∈ (maximalIdeal A) • (⊤ : Submodule A N),
        n ∈ ((maximalIdeal P₀) • (⊤ : Submodule P₀ N)) := by
      intro n hn
      refine Submodule.smul_induction_on hn (fun x hx n _ => ?_) (fun _ _ h1 h2 => ?_)
      · obtain ⟨y, hy, rfl⟩ := hmA x hx
        rw [show (Ideal.Quotient.mk I y) • n = y • n from (algebraMap_smul A y n).symm]
        exact Submodule.smul_mem_smul hy trivial
      · exact Submodule.add_mem _ h1 h2
    have h1 := hle _ ha
    have h2 : L (kerCotangentToTensor R₀ P₀ A ((RingHom.ker (algebraMap P₀ A)).toCotangent
        ⟨∑ i, b i * f i, Ideal.sum_mem _ fun i _ =>
          Ideal.mul_mem_left _ _ (mem_ker_quotient_span f i)⟩)) ∈
        (maximalIdeal P₀) • (⊤ : Submodule P₀ (RingHom.ker (algebraMap P₀ A)).Cotangent) := by
      have hmap := Submodule.mem_map_of_mem (f := L) h1
      rw [Submodule.map_smul''] at hmap
      exact SetLike.le_def.1 (smul_mono_right _ le_top) hmap
    rw [show L (kerCotangentToTensor R₀ P₀ A _) = _ from LinearMap.congr_fun hL _] at h2
    have hIker : RingHom.ker (algebraMap P₀ A) = I := Ideal.mk_ker
    have hm : RingHom.ker (algebraMap P₀ A) ≤ maximalIdeal P₀ := by rw [hIker]; exact hfm
    have h3 := mem_mul_of_toCotangent_mem_smul hm _ h2
    rw [hIker] at h3
    intro i
    rw [← hab]
    exact mk_mem_maximalIdeal hfm (hmin b h3 i)
  obtain ⟨l, hl⟩ := Module.exists_leftInverse_of_isLocalRing φ hφ
  refine ⟨((l.restrictScalars P₀) ∘ₗ (TensorProduct.mk P₀ A Ω[P₀⁄R₀] 1)).compDer (D R₀ P₀),
    fun i => ?_⟩
  show l (1 ⊗ₜ D R₀ P₀ (f i)) = _
  rw [← hφe i]
  exact LinearMap.congr_fun hl _

/-- **Flat transfer of minimality.** -/
theorem minimal_of_flat {Q L : Type*} [CommRing Q] [CommRing L] [IsLocalRing L] [Algebra Q L]
    [Module.Flat Q L] {r : ℕ} (f₀ : Fin r → Q) (q₀ : Ideal Q)
    (hq₀ : q₀ ≤ (maximalIdeal L).comap (algebraMap Q L))
    (hrel : ∀ a : Fin r → Q, ∑ i, a i * f₀ i = 0 → ∀ i, a i ∈ q₀) :
    ∀ b : Fin r → L, ∑ i, b i * algebraMap Q L (f₀ i) ∈
      maximalIdeal L * Ideal.span (Set.range (algebraMap Q L ∘ f₀)) →
      ∀ i, b i ∈ maximalIdeal L := by
  classical
  intro b hb
  set g : Fin r → L := algebraMap Q L ∘ f₀ with hg
  rw [← Ideal.smul_eq_mul, ← Ideal.submodule_span_eq,
    Submodule.mem_ideal_smul_span_iff_exists_sum] at hb
  obtain ⟨c, hc, hcs⟩ := hb
  rw [Finsupp.sum_fintype _ _ (by simp)] at hcs
  set b' : Fin r → L := fun i => b i - c i with hb'
  have hrel' : ∑ i, f₀ i • b' i = 0 := by
    have e1 : ∑ i, f₀ i • b' i = ∑ i, b i * g i - ∑ i, c i • g i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hb', hg, Function.comp_apply, Algebra.smul_def,
        Algebra.algebraMap_self, RingHom.id_apply]
      ring
    rw [e1, hcs]
    simp [hg]
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel'
  have hacol : ∀ i j, a i j ∈ q₀ := fun i j =>
    hrel (fun i => a i j) (by simpa [mul_comm] using ha j) i
  intro i
  have hbi : b i = b' i + c i := by simp [hb']
  rw [hbi]
  refine Ideal.add_mem _ ?_ (hc i)
  rw [hy i]
  exact Ideal.sum_mem _ fun j _ => by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (hq₀ (hacol i j))

/-- **Formal smoothness of `P / (f)` at a local ring from its reduction.** Let `P` be a local
ring formally smooth over `R`, `J ⊆ R` an ideal inside the nilradical and `f₁, …, fᵣ` in the
maximal ideal. Write `P₀ = P / JP` and `f̄ᵢ` for the images. If `P₀ / (f̄)` is formally smooth
over `R / J` and the `f̄ᵢ` are minimal generators of `(f̄)`, then `P / (f)` is formally smooth
over `R`. -/
theorem quotient_span_of_isLocalRing_of_reduction {R P : Type*} [CommRing R] [CommRing P]
    [Algebra R P] [IsLocalRing P] [FormallySmooth R P] (J : Ideal R) (hJ : J ≤ nilradical R)
    {r : ℕ} (f : Fin r → P) (hfm : Ideal.span (Set.range f) ≤ maximalIdeal P)
    [IsLocalRing (P ⧸ J.map (algebraMap R P))]
    [FormallySmooth (R ⧸ J) ((P ⧸ J.map (algebraMap R P)) ⧸
      Ideal.span (Set.range (Ideal.Quotient.mk (J.map (algebraMap R P)) ∘ f)))]
    (hmin : ∀ a : Fin r → P ⧸ J.map (algebraMap R P),
      ∑ i, a i * Ideal.Quotient.mk (J.map (algebraMap R P)) (f i) ∈
        maximalIdeal (P ⧸ J.map (algebraMap R P)) *
          Ideal.span (Set.range (Ideal.Quotient.mk (J.map (algebraMap R P)) ∘ f)) →
      ∀ i, a i ∈ maximalIdeal (P ⧸ J.map (algebraMap R P))) :
    FormallySmooth R (P ⧸ Ideal.span (Set.range f)) := by
  have hJP : J.map (algebraMap R P) ≤ maximalIdeal P := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hn : IsNilpotent (algebraMap R P x) := (mem_nilradical.1 (hJ hx)).map _
    exact (mem_maximalIdeal _).2 hn.not_isUnit
  have : FormallySmooth (R ⧸ J) (P ⧸ J.map (algebraMap R P)) :=
    FormallySmooth.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor P J).symm
  have hfm₀ : Ideal.span (Set.range (Ideal.Quotient.mk (J.map (algebraMap R P)) ∘ f)) ≤
      maximalIdeal (P ⧸ J.map (algebraMap R P)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact mk_mem_maximalIdeal hJP (hfm (Ideal.subset_span ⟨i, rfl⟩))
  obtain ⟨δ₀, hδ₀⟩ := exists_derivation_of_isLocalRing (R₀ := R ⧸ J)
    (Ideal.Quotient.mk (J.map (algebraMap R P)) ∘ f) hfm₀ hmin
  exact quotient_span_of_derivation_reduction J hJ f (δ₀.restrictScalars R) fun i => hδ₀ i

end Algebra.FormallySmooth
