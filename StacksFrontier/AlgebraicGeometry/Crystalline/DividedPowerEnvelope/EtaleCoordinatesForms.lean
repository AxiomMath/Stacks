module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.RingHom.Etale
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Envelope

/-!
# Differential forms of the divided power envelope of an algebra with étale coordinates

Let `A` be a ring and `B` an `A`-algebra with *étale coordinates* `t₁, …, t_d ∈ B`: the map
`A[T₁, …, T_d] → B`, `Tᵢ ↦ tᵢ`, is étale.  Then `Ω_{B/A}` is spanned by `dt₁, …, dt_d`, and for
a divided power ring `(A, I, γ)` and an ideal `J ⊇ IB` of `B` the divided power differentials of
the divided power envelope `D = D_{B,γ}(J)` are spanned by the images of `dt₁, …, dt_d`
([Stacks, Tag 07HW]: `Ω_{D/A,δ} = D ⊗_B Ω_{B/A}`).  Consequently the exterior powers
`Ω^n_{D/A,δ}` vanish for `n > d`.

## Main results

* `Crystalline.exteriorPower_subsingleton_of_span` — the `n`-th exterior power of a module
  spanned by `d < n` elements is zero.
* `Crystalline.span_range_kaehlerD_of_etale` — `Ω_{B/A}` is spanned by the `dtᵢ`.
* `Crystalline.span_range_envelopeDifferential_of_etale` — `Ω_{D/A,δ}` is spanned by the `dtᵢ`.
* `Crystalline.subsingleton_envelopeForms_of_etale` — `Ω^n_{D/A,δ} = 0` for `n > d`.

## References

* [Stacks Project, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Crystalline

/-- **The `n`-th exterior power of a module spanned by fewer than `n` elements is zero**: it is
spanned by the wedges of `n`-tuples of the spanning elements, each of which repeats one. -/
theorem exteriorPower_subsingleton_of_span {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {d : ℕ} (v : Fin d → M) (hv : Submodule.span R (Set.range v) = ⊤) {n : ℕ}
    (hn : d < n) : Subsingleton (⋀[R]^n M) := by
  have hzero : exteriorPower.ιMulti R n '' {a | Set.range a ⊆ Set.range v} ⊆ {0} := by
    rintro _ ⟨a, ha, rfl⟩
    choose c hc using fun i ↦ ha (Set.mem_range_self i)
    have hac : a = v ∘ c := funext fun i ↦ (hc i).symm
    have hc' : ¬Function.Injective c := fun hinj ↦ by
      have := Fintype.card_le_of_injective c hinj
      simp only [Fintype.card_fin] at this
      omega
    refine Set.mem_singleton_iff.2 ((exteriorPower.ιMulti R n).map_eq_zero_of_not_injective a ?_)
    rw [hac]
    exact fun hinj ↦ hc' (Function.Injective.of_comp hinj)
  have hbot : (⊤ : Submodule R (⋀[R]^n M)) = ⊥ := by
    rw [← exteriorPower.ιMulti_span_of_span R n M hv, eq_bot_iff, Submodule.span_le]
    exact hzero.trans (by simp)
  exact subsingleton_of_forall_eq 0 fun x ↦ (Submodule.mem_bot R).1 (hbot ▸ Submodule.mem_top)

/-- If `s` spans the `R`-module `M`, then the images of `1 ⊗ m`, `m ∈ s`, under a surjective
`S`-linear map out of `S ⊗[R] M` span the target. -/
private theorem span_image_one_tmul_eq_top {R S M N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (s : Set M)
    (hs : Submodule.span R s = ⊤) (f : S ⊗[R] M →ₗ[S] N) (hf : Function.Surjective f) :
    Submodule.span S ((fun m ↦ f (1 ⊗ₜ m)) '' s) = ⊤ := by
  have h := Submodule.baseChange_span (R := R) S s
  rw [hs, Submodule.baseChange_top] at h
  rw [show (fun m ↦ f (1 ⊗ₜ m)) '' s = f '' (TensorProduct.mk R S M 1 '' s) by
    rw [Set.image_image]; rfl, ← Submodule.map_span, ← h, Submodule.map_top,
    LinearMap.range_eq_top.2 hf]

section Etale

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {d : ℕ} (t : Fin d → B)

/-- **The differentials of étale coordinates span the Kähler differentials**: for
`A[T₁, …, T_d] → B`, `Tᵢ ↦ tᵢ`, étale, `Ω_{B/A}` is spanned by `dt₁, …, dt_d`.  The relative
differentials `Ω_{B/A[T]}` vanish, so `B ⊗ Ω_{A[T]/A} → Ω_{B/A}` is onto, and `Ω_{A[T]/A}` is
spanned by the `dTᵢ`. -/
theorem span_range_kaehlerD_of_etale (ht : (MvPolynomial.aeval (R := A) t).toRingHom.Etale) :
    Submodule.span B (Set.range fun i ↦ KaehlerDifferential.D A B (t i)) = ⊤ := by
  let Q := MvPolynomial (Fin d) A
  let : Algebra Q B := (MvPolynomial.aeval (R := A) t).toRingHom.toAlgebra
  have : IsScalarTower A Q B := .of_algebraMap_eq fun a ↦ (MvPolynomial.aeval_C t a).symm
  have : Algebra.Etale Q B := RingHom.etale_algebraMap.1 ht
  have hb : Submodule.span Q (Set.range fun i ↦ KaehlerDifferential.D A Q (MvPolynomial.X i)) =
      ⊤ := by
    rw [← (KaehlerDifferential.mvPolynomialBasis A (Fin d)).span_eq]
    congr 2
    funext i
    rw [← Module.Basis.repr_symm_single_one,
      KaehlerDifferential.mvPolynomialBasis_repr_symm_single, one_smul]
  have := span_image_one_tmul_eq_top _ hb (KaehlerDifferential.mapBaseChange A Q B)
    fun ω ↦ (KaehlerDifferential.exact_mapBaseChange_map A Q B ω).1 (Subsingleton.elim _ _)
  have key (i : Fin d) : algebraMap Q B (MvPolynomial.X i) = t i := MvPolynomial.aeval_X t i
  rw [← Set.range_comp] at this
  simpa [Function.comp_def, KaehlerDifferential.map_D, key] using this

end Etale

end Crystalline

namespace Crystalline

section Envelope

variable (A : DividedPowerRing.{u}) {B : Type u} [CommRing B] (f : (A : Type u) →+* B)
  (J : Ideal B) (hJ : A.ideal.map f ≤ J) (E : DividedPowerEnvelope A f J hJ) {d : ℕ}
  (t : Fin d → B)

/-- **The divided power differentials of the envelope of an algebra with étale coordinates are
spanned by the differentials of the coordinates** ([Stacks, Tag 07HW]: `Ω_{D/A,δ} = D ⊗_B Ω_{B/A}`,
and `Ω_{B/A}` is spanned by the `dtᵢ`). -/
theorem span_range_envelopeDifferential_of_etale
    (ht : letI : Algebra (A : Type u) B := f.toAlgebra
      (MvPolynomial.aeval (R := (A : Type u)) t).toRingHom.Etale) :
    letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
    Submodule.span E.object (Set.range fun i ↦ dividedPowerDifferential (A := (A : Type u))
      E.object.dividedPowers (E.algebraMap.toRingHom (t i))) = ⊤ := by
  let : Algebra (A : Type u) B := f.toAlgebra
  let : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
  let : Algebra B E.object := E.algebraMap.toRingHom.toAlgebra
  obtain ⟨e, he⟩ := dividedPowerEnvelopeDifferentialsEquiv A f J hJ E
  have hs : Submodule.span B (Set.range fun i ↦ KaehlerDifferential.D (A : Type u) B (t i)) =
      ⊤ := span_range_kaehlerD_of_etale (A := (A : Type u)) (B := B) t ht
  have := span_image_one_tmul_eq_top _ hs e.symm.toLinearMap e.symm.surjective
  rw [← Set.range_comp] at this
  simpa [Function.comp_def, ← he] using this

/-- **The divided power forms of degree `n > d` of the envelope of an algebra with `d` étale
coordinates vanish.** -/
theorem subsingleton_envelopeForms_of_etale
    (ht : letI : Algebra (A : Type u) B := f.toAlgebra
      (MvPolynomial.aeval (R := (A : Type u)) t).toRingHom.Etale) {n : ℕ} (hn : d < n) :
    letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
    Subsingleton (dividedPowerDifferentialForms (A := (A : Type u)) E.object.dividedPowers n) :=
  let : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
  exteriorPower_subsingleton_of_span _
    (span_range_envelopeDifferential_of_etale A f J hJ E t ht) hn

end Envelope

end Crystalline
