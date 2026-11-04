module

public import StacksFrontier.RingTheory.Smooth.NilpotentLiftLocal
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.Localization

/-!
# Smoothness at a point of `P / (f)` from its reduction along a nil ideal

Let `P` be formally smooth over `R`, `J ⊆ R` inside the nilradical and `f₁, …, fᵣ ∈ P`. Let
`𝔷` be a prime of `S = P / (f)`. Suppose that `P₀ / (f̄)` is formally smooth over `R / J`, where
`P₀ = P / JP`, and that `P₀` is flat over a ring `Q` containing elements `f⁰ᵢ` mapping to the
`f̄ᵢ`, all of whose relations have coefficients in a prime lying under `𝔷`. Then `S` is smooth
over `R` at `𝔷`.
-/

@[expose] public section

open IsLocalRing

namespace Algebra

/-- Let `P` be formally smooth over `R`, let `J ≤ nilradical R`, let `f : Fin r → P`, and let `𝔷`
be a prime of `P ⧸ (f)`. Suppose that `(P ⧸ JP) ⧸ (f̄)` is formally smooth over `R ⧸ J`, and that
`φ : Q →+* P ⧸ JP` is flat with `φ (f₀ i) = f̄ i`, where every relation `∑ aᵢ f₀ᵢ = 0` has all its
coefficients in an ideal `q₀` contained in the preimage under `φ` of the image in `P ⧸ JP` of the
preimage of `𝔷` in `P`. Then `P ⧸ (f)` is smooth over `R` at `𝔷`. -/
theorem isSmoothAt_quotient_span_of_reduction {R P : Type*} [CommRing R] [CommRing P]
    [Algebra R P] [FormallySmooth R P] (J : Ideal R) (hJ : J ≤ nilradical R) {r : ℕ}
    (f : Fin r → P)
    [FormallySmooth (R ⧸ J) ((P ⧸ J.map (algebraMap R P)) ⧸
      Ideal.span (Set.range (Ideal.Quotient.mk (J.map (algebraMap R P)) ∘ f)))]
    {Q : Type*} [CommRing Q] (φ : Q →+* P ⧸ J.map (algebraMap R P)) (hφ : φ.Flat)
    (f₀ : Fin r → Q) (hf₀ : ∀ i, φ (f₀ i) = Ideal.Quotient.mk _ (f i)) (q₀ : Ideal Q)
    (hrel : ∀ a : Fin r → Q, ∑ i, a i * f₀ i = 0 → ∀ i, a i ∈ q₀)
    (𝔷 : Ideal (P ⧸ Ideal.span (Set.range f))) [𝔷.IsPrime]
    (hq₀ : q₀ ≤ ((𝔷.comap (algebraMap P (P ⧸ Ideal.span (Set.range f)))).map
      (Ideal.Quotient.mk (J.map (algebraMap R P)))).comap φ) :
    IsSmoothAt R 𝔷 := by
  classical
  let S := P ⧸ Ideal.span (Set.range f)
  let 𝔭 : Ideal P := 𝔷.comap (algebraMap P S)
  have : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  let L := Localization.AtPrime 𝔭
  let fL : Fin r → L := algebraMap P L ∘ f
  have hf𝔭 : ∀ i, f i ∈ 𝔭 := by
    intro i
    simp only [𝔭, Ideal.mem_comap]
    rw [show algebraMap P S (f i) = 0 from FormallySmooth.mem_ker_quotient_span f i]
    exact 𝔷.zero_mem
  -- the reduction of `L`, presented as a localization of `P₀`
  let JP := J.map (algebraMap R P)
  let JL' := JP.map (algebraMap P L)
  have hJL : J.map (algebraMap R L) = JL' := by
    show _ = Ideal.map (algebraMap P L) (Ideal.map (algebraMap R P) J)
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hJLm : JL' ≤ maximalIdeal L := by
    rw [← hJL, Ideal.map_le_iff_le_comap]
    intro x hx
    exact (mem_maximalIdeal _).2 ((mem_nilradical.1 (hJ hx)).map _).not_isUnit
  have hJLtop : JL' ≠ ⊤ := fun h => (maximalIdeal.isMaximal L).ne_top (top_le_iff.1 (h ▸ hJLm))
  have : Nontrivial (L ⧸ JL') := Ideal.Quotient.nontrivial_iff.2 hJLtop
  have hloc : IsLocalRing (L ⧸ JL') :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  -- membership of the maximal ideal of `L ⧸ JL'`
  have hmaxL : ∀ p : P, p ∈ 𝔭 →
      Ideal.Quotient.mk JL' (algebraMap P L p) ∈ maximalIdeal (L ⧸ JL') := by
    intro p hp
    have hpm : algebraMap P L p ∈ maximalIdeal L :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L 𝔭 p).2 hp
    refine (mem_maximalIdeal _).2 fun hu => ?_
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at hc
    have h1 : algebraMap P L p * c' ∈ maximalIdeal L := Ideal.mul_mem_right _ _ hpm
    have h := Ideal.sub_mem _ h1 (hJLm hc)
    rw [sub_sub_cancel] at h
    exact (maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).2 h)
  -- the flat map `Q ⟶ L ⧸ JL'`
  let ψ : P ⧸ JP →+* L ⧸ JL' := algebraMap (P ⧸ JP) (L ⧸ JL')
  have hψflat : ψ.Flat := RingHom.flat_algebraMap_iff.2
    (IsLocalization.flat (L ⧸ JL') (Algebra.algebraMapSubmonoid (P ⧸ JP) 𝔭.primeCompl))
  let : Algebra Q (L ⧸ JL') := (ψ.comp φ).toAlgebra
  have : Module.Flat Q (L ⧸ JL') := RingHom.Flat.comp hφ hψflat
  have hψmk : ∀ p : P, ψ (Ideal.Quotient.mk JP p) = Ideal.Quotient.mk JL' (algebraMap P L p) :=
    fun _ => rfl
  have hq₀' : q₀ ≤ (maximalIdeal (L ⧸ JL')).comap (algebraMap Q (L ⧸ JL')) := by
    intro a ha
    have h1 := hq₀ ha
    rw [Ideal.mem_comap] at h1 ⊢
    obtain ⟨p, hp, hpa⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h1
    show ψ (φ a) ∈ _
    rw [← hpa, hψmk]
    exact hmaxL p hp
  have hmin := FormallySmooth.minimal_of_flat f₀ q₀ hq₀' hrel
  have hfL0 : algebraMap Q (L ⧸ JL') ∘ f₀ = Ideal.Quotient.mk JL' ∘ fL := by
    funext i
    show ψ (φ (f₀ i)) = _
    rw [hf₀, hψmk]
    rfl
  rw [hfL0] at hmin
  have hmin' : ∀ b : Fin r → L ⧸ JL', ∑ i, b i * Ideal.Quotient.mk JL' (fL i) ∈
      maximalIdeal (L ⧸ JL') * Ideal.span (Set.range (Ideal.Quotient.mk JL' ∘ fL)) →
      ∀ i, b i ∈ maximalIdeal (L ⧸ JL') := by
    intro b hb
    have e : ∀ i, algebraMap Q (L ⧸ JL') (f₀ i) = Ideal.Quotient.mk JL' (fL i) :=
      fun i => congrFun hfL0 i
    exact hmin b (by simpa only [e] using hb)
  -- the `R ⧸ J`-algebra structure on `L ⧸ JL'`, compatible with `P ⧸ JP`
  have hle : J ≤ JL'.comap (algebraMap R L) := by
    rw [← hJL]; exact Ideal.le_comap_map
  let : Algebra (R ⧸ J) (L ⧸ JL') := (Ideal.quotientMap JL' (algebraMap R L) hle).toAlgebra
  have : IsScalarTower R (R ⧸ J) (L ⧸ JL') := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (R ⧸ J) (P ⧸ JP) (L ⧸ JL') := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk JL' (algebraMap R L x) =
      Ideal.Quotient.mk JL' (algebraMap P L (algebraMap R P x))
    rw [← IsScalarTower.algebraMap_apply]
  have : FormallySmooth (R ⧸ J) (P ⧸ JP) :=
    FormallySmooth.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor P J).symm
  have : FormallySmooth (P ⧸ JP) (L ⧸ JL') :=
    FormallySmooth.of_isLocalization (Algebra.algebraMapSubmonoid (P ⧸ JP) 𝔭.primeCompl)
  have : FormallySmooth (R ⧸ J) (L ⧸ JL') := FormallySmooth.comp (R ⧸ J) (P ⧸ JP) _
  -- the reduced quotient, as a localization of the global one
  let I₀ : Ideal (P ⧸ JP) := Ideal.span (Set.range (Ideal.Quotient.mk JP ∘ f))
  have hI₀ : I₀.map (algebraMap (P ⧸ JP) (L ⧸ JL')) =
      Ideal.span (Set.range (Ideal.Quotient.mk JL' ∘ fL)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have : FormallySmooth ((P ⧸ JP) ⧸ I₀) ((L ⧸ JL') ⧸ I₀.map (algebraMap (P ⧸ JP) (L ⧸ JL'))) :=
    FormallySmooth.of_isLocalization (Algebra.algebraMapSubmonoid ((P ⧸ JP) ⧸ I₀)
      (Algebra.algebraMapSubmonoid (P ⧸ JP) 𝔭.primeCompl))
  have : IsScalarTower (R ⧸ J) ((P ⧸ JP) ⧸ I₀)
      ((L ⧸ JL') ⧸ I₀.map (algebraMap (P ⧸ JP) (L ⧸ JL'))) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      show Ideal.Quotient.mk _ (Ideal.Quotient.mk JL' (algebraMap R L x)) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk JL' (algebraMap P L (algebraMap R P x)))
      rw [← IsScalarTower.algebraMap_apply]
  have : FormallySmooth (R ⧸ J)
      ((L ⧸ JL') ⧸ Ideal.span (Set.range (Ideal.Quotient.mk JL' ∘ fL))) := by
    rw [← hI₀]
    exact FormallySmooth.comp (R ⧸ J) ((P ⧸ JP) ⧸ I₀) _
  have hfm0 : Ideal.span (Set.range (Ideal.Quotient.mk JL' ∘ fL)) ≤ maximalIdeal (L ⧸ JL') := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmaxL (f i) (hf𝔭 i)
  obtain ⟨δ, hδ⟩ := FormallySmooth.exists_derivation_of_isLocalRing (R₀ := R ⧸ J)
    (Ideal.Quotient.mk JL' ∘ fL) hfm0 hmin'
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : Derivation R (L ⧸ J.map (algebraMap R L))
      (Fin r → (L ⧸ J.map (algebraMap R L)) ⧸
        Ideal.span (Set.range (Ideal.Quotient.mk (J.map (algebraMap R L)) ∘ fL))),
      ∀ i, δ₀ (Ideal.Quotient.mk _ (fL i)) = Pi.single i 1 := by
    rw [hJL]
    exact ⟨δ.restrictScalars R, hδ⟩
  have hFS : FormallySmooth R (L ⧸ Ideal.span (Set.range fL)) :=
    FormallySmooth.quotient_span_of_derivation_reduction J hJ fL δ₀ hδ₀
  -- transport to the localization of `S` at `𝔷`
  let I := Ideal.span (Set.range f)
  have hIL : I.map (algebraMap P L) = Ideal.span (Set.range fL) := by
    rw [Ideal.map_span, ← Set.range_comp]
  rw [← hIL] at hFS
  have hsub : Algebra.algebraMapSubmonoid S 𝔭.primeCompl = 𝔷.primeCompl := by
    ext x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨?_, fun hp => ⟨p, hp, rfl⟩⟩
    rintro ⟨p', hp', hpp'⟩
    change Ideal.Quotient.mk I p' = _ at hpp'
    show Ideal.Quotient.mk I p ∉ 𝔷
    rw [← hpp']
    exact hp'
  have : IsLocalization 𝔷.primeCompl (L ⧸ I.map (algebraMap P L)) := by
    rw [← hsub]; infer_instance
  have : IsScalarTower R S (L ⧸ I.map (algebraMap P L)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show Ideal.Quotient.mk _ (algebraMap R L x) =
        Ideal.Quotient.mk _ (algebraMap P L (algebraMap R P x))
      rw [← IsScalarTower.algebraMap_apply]
  let e := (IsLocalization.algEquiv 𝔷.primeCompl (Localization.AtPrime 𝔷)
    (L ⧸ I.map (algebraMap P L))).restrictScalars R
  exact FormallySmooth.of_equiv e.symm

end Algebra
