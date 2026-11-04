module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.RingTheory.ApproximationProperty.Defs
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.Pair.Lifting.Algebra
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing
public import StacksFrontier.RingTheory.Henselian.Pair.Operations
public import StacksFrontier.RingTheory.Smoothing.IndSmooth

/-!
# Approximating a solution in a complete local ring by solutions coming from a local ring

This file contains the approximation step of Rotthaus' proof that a Noetherian local ring with
the approximation property has geometrically regular formal fibres. Let `B` be a Noetherian local
ring with completion `B^∧`, let `R` be a complete local ring with a surjection `ρ : R → B^∧`, and
let `R₀` be a ring mapping compatibly to `R` and to `B`, such that `R` is a filtered colimit of
smooth `R₀`-algebras. Given a finitely presented `R₀`-algebra `𝓔` and an `R₀`-algebra map
`τ : 𝓔 → R`, the approximation property of `B` produces, for every `n`, another `R₀`-algebra map
`φ : 𝓔 → R` which agrees with `τ` modulo `𝔪_R ^ n`, whose values become elements of `B` in
`B^∧`, and which keeps finitely many prescribed values of `ρ ∘ τ` lying in `B`.

## Main results

* `Stacks.ApproximationProperty.henselianPair_of_le_maximalIdeal`: an ideal inside the maximal
  ideal of a complete local ring forms a henselian pair with it.
* `Stacks.ApproximationProperty.exists_lift_of_smooth_of_sup`: two maps from a smooth algebra
  agreeing modulo `I ⊔ J` are simultaneously approximated, modulo `I` and modulo `J`, by a single
  map, when `(R, I ⊓ J)` is a henselian pair.
* `Stacks.ApproximationProperty.exists_algHom_approx`: the approximation step described above.

## References

* [C. Rotthaus, *Rings with approximation property*, Math. Ann. 287 (1990), 455–466][Rotthaus]
* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
* [Stacks Project, Tag 0H74](https://stacks.math.columbia.edu/tag/0H74)
* [Stacks Project, Tag 0DYD](https://stacks.math.columbia.edu/tag/0DYD)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u

namespace Stacks.ApproximationProperty

/-- An ideal contained in the maximal ideal of a complete local ring forms a henselian pair
with it. -/
theorem henselianPair_of_le_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    HenselianPair R I := by
  have : HenselianLocalRing R := henselianLocalRing_of_isAdicComplete_maximalIdeal R
  exact ((henselianPair_iff_of_le hI).mpr (henselianPair_maximalIdeal R)).1

/-- Two `R₀`-algebra maps `f₁ f₂ : D → R` from a smooth `R₀`-algebra which agree modulo `I ⊔ J`
are approximated by a single map `f`, with `f ≡ f₁` modulo `I` and `f ≡ f₂` modulo `J`, as soon
as `(R, I ⊓ J)` is a henselian pair. -/
theorem exists_lift_of_smooth_of_sup {R₀ D R : Type u} [CommRing R₀] [CommRing D] [CommRing R]
    [Algebra R₀ D] [Algebra R₀ R] [Algebra.Smooth R₀ D] (I J : Ideal R)
    (hIJ : HenselianPair R (I ⊓ J)) (f₁ f₂ : D →ₐ[R₀] R) (h : ∀ d, f₁ d - f₂ d ∈ I ⊔ J) :
    ∃ f : D →ₐ[R₀] R, (∀ d, f d - f₁ d ∈ I) ∧ ∀ d, f d - f₂ d ∈ J := by
  classical
  let χ : R →+* (R ⧸ I) × (R ⧸ J) := (Ideal.Quotient.mk I).prod (Ideal.Quotient.mk J)
  have hker : RingHom.ker χ = I ⊓ J := by
    ext x
    simp [χ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  let γ₀ : D →+* (R ⧸ I) × (R ⧸ J) :=
    ((Ideal.Quotient.mk I).comp f₁.toRingHom).prod ((Ideal.Quotient.mk J).comp f₂.toRingHom)
  have hpre : ∀ d, ∃ r : R, r - f₁ d ∈ I ∧ r - f₂ d ∈ J := by
    intro d
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 (h d)
    refine ⟨f₁ d - i, by simpa using I.neg_mem hi, ?_⟩
    rwa [show f₁ d - i - f₂ d = j by linear_combination -1 * hij]
  have hχ : ∀ d (r : R), r - f₁ d ∈ I → r - f₂ d ∈ J → χ r = γ₀ d := by
    intro d r h₁ h₂
    simp only [χ, γ₀, RingHom.prod_apply, RingHom.coe_comp, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Prod.mk.injEq]
    exact ⟨Ideal.Quotient.eq.2 h₁, Ideal.Quotient.eq.2 h₂⟩
  have hrange : ∀ d, γ₀ d ∈ χ.range := by
    intro d
    obtain ⟨r, h₁, h₂⟩ := hpre d
    exact ⟨r, hχ d r h₁ h₂⟩
  let e : R ⧸ RingHom.ker χ ≃+* χ.range := RingHom.quotientKerEquivRange χ
  let g₀ : D →+* R ⧸ (I ⊓ J) :=
    (Ideal.quotEquivOfEq hker).toRingHom.comp (e.symm.toRingHom.comp (γ₀.codRestrict _ hrange))
  have hg₀ : ∀ d (r : R), r - f₁ d ∈ I → r - f₂ d ∈ J → g₀ d = Ideal.Quotient.mk _ r := by
    intro d r h₁ h₂
    have he : e (Ideal.Quotient.mk _ r) = γ₀.codRestrict _ hrange d :=
      Subtype.ext (hχ d r h₁ h₂)
    simp only [g₀, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, ← he, RingEquiv.symm_apply_apply]
    rfl
  let g : D →ₐ[R₀] R ⧸ (I ⊓ J) :=
    { g₀ with
      commutes' := fun c => by
        change g₀ (algebraMap R₀ D c) = algebraMap R₀ (R ⧸ (I ⊓ J)) c
        rw [hg₀ (algebraMap R₀ D c) (algebraMap R₀ R c) (by simp) (by simp)]
        rfl }
  obtain ⟨f, hf⟩ := exists_lift_of_smooth_of_henselianPair (I ⊓ J) hIJ g
  have key : ∀ d, f d - f₁ d ∈ I ∧ f d - f₂ d ∈ J := by
    intro d
    obtain ⟨r, h₁, h₂⟩ := hpre d
    have : Ideal.Quotient.mk (I ⊓ J) (f d) = Ideal.Quotient.mk (I ⊓ J) r := by
      rw [← hg₀ d r h₁ h₂]
      exact congrArg (fun φ : D →ₐ[R₀] R ⧸ (I ⊓ J) => φ d) hf
    have h := Ideal.Quotient.eq.1 this
    exact ⟨by simpa only [sub_add_sub_cancel] using I.add_mem h.1 h₁,
      by simpa only [sub_add_sub_cancel] using J.add_mem h.2 h₂⟩
  exact ⟨f, fun d => (key d).1, fun d => (key d).2⟩

variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

/-- **The approximation step** (Rotthaus (3.6)–(3.9)). Let `B` be a Noetherian local ring
satisfying the approximation statement `hB` for finite type `B`-algebras (approximation of
finitely many values modulo powers of `𝔪_B`), let `R` be a complete local ring which is a
filtered colimit of smooth `R₀`-algebras, and let `ρ : R → B^∧` be a surjection compatible with
`R₀ → B`. For a finitely presented `R₀`-algebra `𝓔`, an `R₀`-algebra map `τ : 𝓔 → R`, finitely
many elements `e i` of `𝓔` with `ρ (τ (e i))` coming from elements `b i` of `B`, and any `n`,
there is an `R₀`-algebra map `φ : 𝓔 → R` congruent to `τ` modulo `𝔪_R ^ n`, all of whose values
are mapped by `ρ` into the image of `B`, and with `ρ (φ (e i)) = b i`. -/
theorem exists_algHom_approx
    (hB : ∀ (E : Type u) [CommRing E] [Algebra B E] [Algebra.FiniteType B E]
      (f : E →ₐ[B] AdicCompletion (maximalIdeal B) B) {k : ℕ} (x : Fin k → E) (N : ℕ),
      ∃ g : E →ₐ[B] B, ∀ i, algebraMap B (AdicCompletion (maximalIdeal B) B) (g (x i)) - f (x i) ∈
        (maximalIdeal B ^ N).map (algebraMap B (AdicCompletion (maximalIdeal B) B)))
    {R₀ R : Type u} [CommRing R₀] [CommRing R] [IsLocalRing R] [Algebra R₀ R] [Algebra R₀ B]
    [IsAdicComplete (maximalIdeal R) R] (hind : Stacks.Smoothing.IndSmooth R₀ R)
    (ρ : R →+* AdicCompletion (maximalIdeal B) B) (hρ : Function.Surjective ρ)
    (hcompat : ρ.comp (algebraMap R₀ R) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp (algebraMap R₀ B))
    {𝓔 : Type u} [CommRing 𝓔] [Algebra R₀ 𝓔] [Algebra.FinitePresentation R₀ 𝓔]
    (τ : 𝓔 →ₐ[R₀] R) {p : ℕ} (e : Fin p → 𝓔) (b : Fin p → B)
    (hb : ∀ i, ρ (τ (e i)) = algebraMap B (AdicCompletion (maximalIdeal B) B) (b i)) (n : ℕ) :
    ∃ φ : 𝓔 →ₐ[R₀] R, (∀ x, φ x - τ x ∈ maximalIdeal R ^ n) ∧
      (∀ x, ∃ b' : B, ρ (φ x) = algebraMap B (AdicCompletion (maximalIdeal B) B) b') ∧
      ∀ i, ρ (φ (e i)) = algebraMap B (AdicCompletion (maximalIdeal B) B) (b i) := by
  classical
  set Bh := AdicCompletion (maximalIdeal B) B
  set ι := algebraMap B Bh
  have hι : ∀ r : R₀, algebraMap R₀ Bh r = ι (algebraMap R₀ B r) := fun _ => rfl
  have : IsScalarTower R₀ B Bh := IsScalarTower.of_algebraMap_eq hι
  let ρₐ : R →ₐ[R₀] Bh :=
    { ρ with
      commutes' := fun r => by
        change ρ (algebraMap R₀ R r) = algebraMap R₀ Bh r
        rw [hι]
        exact congrArg (fun φ : R₀ →+* Bh => φ r) hcompat }
  obtain ⟨D, _, algD, hDsm, α, β, hαβ⟩ :=
    (Stacks.Smoothing.indSmooth_iff_exists_factorization R₀ R).1 hind 𝓔 inferInstance
      inferInstance inferInstance τ
  let := algD
  let := hDsm
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R₀) (A := D)
  let k := s.card
  let d : Fin k → D := fun i => (s.equivFin.symm i : D)
  have hd : Algebra.adjoin R₀ (Set.range d) = ⊤ := by
    rw [show Set.range d = (s : Set D) from
      (EquivLike.range_comp Subtype.val s.equivFin.symm).trans Subtype.range_coe_subtype, hs]
  let E₀ := B ⊗[R₀] D
  let ιD : D →ₐ[R₀] E₀ := Algebra.TensorProduct.includeRight
  let ρβ : D →ₐ[R₀] Bh := (ρₐ.comp β)
  let v₀ : E₀ →ₐ[B] Bh :=
    Algebra.TensorProduct.lift (Algebra.ofId B Bh) ρβ (fun _ _ => Commute.all _ _)
  have hv₀D : ∀ y, v₀ (ιD y) = ρ (β y) := by
    intro y
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one,
      one_mul]
    rfl
  let J : Ideal E₀ := Ideal.span (Set.range fun i => ιD (α (e i)) - algebraMap B E₀ (b i))
  have hJ : ∀ x ∈ J, v₀ x = 0 := fun x hx => by
    refine (Ideal.span_le (I := RingHom.ker v₀)).2 ?_ hx
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hv₀D, AlgHom.commutes, ← hb i,
      show β (α (e i)) = τ (e i) from DFunLike.congr_fun hαβ (e i), sub_self]
  let E := E₀ ⧸ J
  let v : E →ₐ[B] Bh := Ideal.Quotient.liftₐ J v₀ hJ
  have : Algebra.FiniteType B E₀ := inferInstance
  have : Algebra.FiniteType B E :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B J) Ideal.Quotient.mk_surjective
  let x : Fin k → E := fun i => Ideal.Quotient.mk J (ιD (d i))
  obtain ⟨w, hw⟩ := hB E v x n
  let ψ : D →ₐ[R₀] Bh :=
    ((Algebra.ofId B Bh).restrictScalars R₀).comp
      ((w.restrictScalars R₀).comp ((Ideal.Quotient.mkₐ R₀ J).comp ιD))
  have hψ : ∀ y, ψ y = ι (w (Ideal.Quotient.mk J (ιD y))) := fun _ => rfl
  set K : Ideal Bh := (maximalIdeal B ^ n).map ι
  have hK : ∀ y, ψ y - ρ (β y) ∈ K := by
    let π : Bh →ₐ[R₀] Bh ⧸ K := Ideal.Quotient.mkₐ R₀ K
    have heq : π.comp ψ = π.comp ρβ := by
      apply AlgHom.ext_of_adjoin_eq_top hd
      rintro _ ⟨i, rfl⟩
      simp only [AlgHom.comp_apply, π, Ideal.Quotient.mkₐ_eq_mk]
      apply Ideal.Quotient.eq.2
      have h := hw i
      rw [show v (x i) = ρ (β (d i)) from hv₀D (d i)] at h
      simpa [ψ, ρβ, ρₐ] using h
    exact fun y => Ideal.Quotient.eq.1 (DFunLike.congr_fun heq y)
  have hKρ : K = (maximalIdeal R ^ n).map ρ := by
    have hmax : (maximalIdeal R).map ρ = maximalIdeal Bh :=
      IsLocalRing.map_maximalIdeal_of_surjective ρ hρ
    rw [Ideal.map_pow, hmax, AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  have hkerle : RingHom.ker ρ ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ρ)
  let eρ : (R ⧸ RingHom.ker ρₐ) ≃ₐ[R₀] Bh := Ideal.quotientKerAlgEquivOfSurjective hρ
  obtain ⟨φ₁, hφ₁⟩ := exists_lift_of_smooth_of_henselianPair (RingHom.ker ρₐ)
    (henselianPair_of_le_maximalIdeal _ hkerle) (eρ.symm.toAlgHom.comp ψ)
  have hρφ₁ : ∀ y, ρ (φ₁ y) = ψ y := by
    intro y
    have h1 : Ideal.Quotient.mk (RingHom.ker ρₐ) (φ₁ y) = eρ.symm (ψ y) :=
      DFunLike.congr_fun hφ₁ y
    have h2 : eρ (Ideal.Quotient.mk (RingHom.ker ρₐ) (φ₁ y)) = ρ (φ₁ y) := rfl
    rw [← h2, h1, AlgEquiv.apply_symm_apply]
  have hsup : ∀ y, φ₁ y - β y ∈ RingHom.ker ρ ⊔ maximalIdeal R ^ n := by
    intro y
    have hmem : ρ (φ₁ y - β y) ∈ (maximalIdeal R ^ n).map ρ := by
      rw [map_sub, hρφ₁, ← hKρ]
      exact hK y
    obtain ⟨m, hm, hρm⟩ := (Ideal.mem_map_iff_of_surjective ρ hρ).1 hmem
    have hk : φ₁ y - β y - m ∈ RingHom.ker ρ := by
      rw [RingHom.mem_ker, map_sub, hρm, sub_self]
    have := Submodule.add_mem_sup hk hm
    rwa [sub_add_cancel] at this
  obtain ⟨φD, hφD₁, hφD₂⟩ := exists_lift_of_smooth_of_sup (RingHom.ker ρ) (maximalIdeal R ^ n)
    (henselianPair_of_le_maximalIdeal _ (le_trans inf_le_left hkerle)) φ₁ β hsup
  have hρφD : ∀ y, ρ (φD y) = ψ y := by
    intro y
    have := hφD₁ y
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    rw [this, hρφ₁]
  refine ⟨φD.comp α, fun z => ?_, fun z => ⟨w (Ideal.Quotient.mk J (ιD (α z))), ?_⟩, fun i => ?_⟩
  · rw [show τ z = β (α z) from (DFunLike.congr_fun hαβ z).symm]
    exact hφD₂ (α z)
  · rw [AlgHom.comp_apply, hρφD, hψ]
  · rw [AlgHom.comp_apply, hρφD, hψ]
    congr 1
    have : Ideal.Quotient.mk J (ιD (α (e i))) = Ideal.Quotient.mk J (algebraMap B E₀ (b i)) :=
      Ideal.Quotient.eq.2 (Ideal.subset_span ⟨i, rfl⟩)
    rw [this]
    exact w.commutes (b i)

end Stacks.ApproximationProperty

end
