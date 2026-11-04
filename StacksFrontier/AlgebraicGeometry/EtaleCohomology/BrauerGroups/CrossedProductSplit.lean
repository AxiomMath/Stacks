module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import StacksCore.Algebra.BrauerGroup.BaseChange
public import StacksCore.Algebra.Split.Finrank
public import StacksCore.RingTheory.SkolemNoether
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.CrossedProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.TwoCocycleInflation

/-!
# Splitting of crossed products, and degree-two vanishing from the relative Brauer group

For `L/K` finite Galois and `c` a `2`-cocycle `Gal(L/K) × Gal(L/K) → Lˣ`, the crossed product
`CrossedProduct c` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.CrossedProduct` is a finite central
simple `K`-algebra of dimension `[L : K]²` containing `L`. This file proves that `c` is a
coboundary exactly when that algebra is split, and deduces that every `2`-cocycle is a
coboundary as soon as the relative Brauer group `Br(L/K)` vanishes.

## Main results

* `Stacks.GaloisCohomology.CrossedProduct.isMulCoboundary₂_iff_isSplit`: a `2`-cocycle is a
  coboundary if and only if its crossed product is a matrix algebra over `K`.
* `Stacks.GaloisCohomology.CrossedProduct.coboundaryAlgEquiv`: the splitting isomorphism
  produced by a trivialising `1`-cochain.
* `Stacks.GaloisCohomology.CrossedProduct.isMulCoboundary₂_of_algEquiv_end`: a `2`-cocycle whose
  crossed product is isomorphic to `End_K L` is a coboundary.
* `Stacks.GaloisCohomology.isMulCoboundary₂_of_brauer` and
  `Stacks.GaloisCohomology.isMulCoboundary₂_of_ker_baseChange_eq_bot`: for `L/K` finite Galois,
  every `2`-cocycle `Gal(L/K) × Gal(L/K) → Lˣ` is a coboundary when `Br(L/K) = 0`, the relative
  Brauer group being the kernel of `BrauerGroup.baseChange K L`.
* `Stacks.GaloisCohomology.isMulCoboundary₂_separableClosure_of_forall_brauer`: if
  `Br(L/K) = 0` for every finite Galois subextension `L/K` of `Kˢᵉᵖ` then every locally constant
  `2`-cocycle on `Gal(Kˢᵉᵖ/K)` with values in `(Kˢᵉᵖ)ˣ` is a coboundary.

## References

* [Stacks Project, Tag 03R7](https://stacks.math.columbia.edu/tag/03R7)
* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
* [Stacks Project, Tag 074Q](https://stacks.math.columbia.edu/tag/074Q), Skolem–Noether.
-/

@[expose] public noncomputable section

open Module groupCohomology

namespace Stacks.GaloisCohomology

universe u

namespace CrossedProduct

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  {c : Gal(L/K) × Gal(L/K) → Lˣ} [Fact (IsMulCocycle₂ c)]

/-- A representation of the crossed product on `L` itself which restricts to multiplication on
the copy of `L` exhibits the cocycle as a coboundary. -/
theorem isMulCoboundary₂_of_rep (Φ : CrossedProduct c → Module.End K L)
    (hone : Φ 1 = 1) (hmul : ∀ y z : CrossedProduct c, Φ (y * z) = Φ y * Φ z)
    (hincl : ∀ a : L, Φ (incl a) = Algebra.lmul K L a) : IsMulCoboundary₂ c := by
  obtain ⟨b, hbdef⟩ : ∃ b : Gal(L/K) → L, ∀ σ, b σ = Φ (single σ 1) 1 := ⟨_, fun _ ↦ rfl⟩
  have hsemi : ∀ (σ : Gal(L/K)) (t : L), Φ (single σ 1) t = σ t * b σ := by
    intro σ t
    have h1 := hmul (single σ 1) (incl t)
    have h2 := hmul (incl (σ t)) (single σ 1)
    rw [single_one_mul_incl, hincl] at h1
    rw [incl_mul_single_one, hincl] at h2
    have h3 := LinearMap.congr_fun (h1.symm.trans h2) (1 : L)
    simp only [Module.End.mul_apply] at h3
    rw [hbdef]
    simpa using h3
  have hbne : ∀ σ : Gal(L/K), b σ ≠ 0 := by
    intro σ hσ
    obtain ⟨w, hw⟩ := exists_mul_single_eq_one (c := c) σ (one_ne_zero (α := L))
    have h0 : Φ (single σ 1) = 0 :=
      LinearMap.ext fun t ↦ by rw [hsemi, hσ, mul_zero]; rfl
    have hz : (1 : Module.End K L) = 0 := by rw [← hone, ← hw, hmul, h0, zero_mul]
    simpa using LinearMap.congr_fun hz (1 : L)
  have hrel : ∀ σ τ : Gal(L/K), σ (b τ) * b σ = ((c (σ, τ) : Lˣ) : L) * b (σ * τ) := by
    intro σ τ
    have h := hmul (single σ 1) (single τ 1)
    rw [single_one_mul_single_one, hmul, hincl] at h
    have h3 := LinearMap.congr_fun h (1 : L)
    simp only [Module.End.mul_apply] at h3
    rw [← hbdef (σ * τ), ← hbdef τ, hsemi σ (b τ)] at h3
    simpa using h3.symm
  refine ⟨fun σ ↦ Units.mk0 (b σ) (hbne σ), fun σ τ ↦ ?_⟩
  rw [div_mul_eq_mul_div, div_eq_iff_eq_mul]
  refine Units.ext ?_
  simpa only [Units.val_mul, val_units_smul, Units.val_mk0] using hrel σ τ

/-- If the crossed product is isomorphic to the algebra of `K`-linear endomorphisms of `L`,
then the cocycle is a coboundary. -/
theorem isMulCoboundary₂_of_algEquiv_end [IsGalois K L]
    (θ : CrossedProduct c ≃ₐ[K] Module.End K L) : IsMulCoboundary₂ c := by
  obtain ⟨x, hx⟩ := skolemNoether K (CrossedProduct c) L (inclAlgHom (c := c))
    (θ.symm.toAlgHom.comp (Algebra.lmul K L))
  refine isMulCoboundary₂_of_rep
    (fun y ↦ θ ((x : CrossedProduct c) * y * ((x⁻¹ : (CrossedProduct c)ˣ) : CrossedProduct c)))
    (by simp) (fun y z ↦ by simp only [← map_mul, mul_assoc, Units.inv_mul_cancel_left])
    fun a ↦ ?_
  have h := hx a
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom, inclAlgHom_apply] at h
  rw [← h, θ.apply_symm_apply]

/-- If `K` itself splits the crossed product, the cocycle is a coboundary. -/
theorem isMulCoboundary₂_of_isSplit [IsGalois K L]
    (h : Algebra.IsSplit K (CrossedProduct c) K) : IsMulCoboundary₂ c := by
  classical
  obtain ⟨m, hm, ⟨e⟩⟩ := h
  have e' : CrossedProduct c ≃ₐ[K] Matrix (Fin m) (Fin m) K :=
    (Algebra.TensorProduct.lid K (CrossedProduct c)).symm.trans e
  have hdim : m ^ 2 = finrank K L ^ 2 := by
    rw [← finrank_eq (c := c), e'.toLinearEquiv.finrank_eq, Module.finrank_matrix,
      Fintype.card_fin, pow_two, finrank_self, mul_one]
  have hm' : m = finrank K L := Nat.pow_left_injective (by norm_num) hdim
  subst hm'
  exact isMulCoboundary₂_of_algEquiv_end (e'.trans (algEquivMatrix (Module.finBasis K L)).symm)

section Coboundary

variable {b : Gal(L/K) → Lˣ}

omit [FiniteDimensional K L] [Fact (IsMulCocycle₂ c)] in
/-- The `2`-coboundary condition, with the values coerced into `L` and cleared of division. -/
theorem val_isMulCoboundary₂ (hb : ∀ g h : Gal(L/K), g • b h / b (g * h) * b g = c (g, h))
    (σ τ : Gal(L/K)) :
    ((b σ : Lˣ) : L) * σ ((b τ : Lˣ) : L)
      = ((c (σ, τ) : Lˣ) : L) * ((b (σ * τ) : Lˣ) : L) := by
  have h := hb σ τ
  rw [div_mul_eq_mul_div, div_eq_iff_eq_mul] at h
  simpa only [Units.val_mul, val_units_smul, mul_comm] using congrArg Units.val h

omit [FiniteDimensional K L] [Fact (IsMulCocycle₂ c)] in
/-- A trivialising `1`-cochain has `b 1 = c (1, 1)`. -/
theorem map_one_of_isMulCoboundary₂
    (hb : ∀ g h : Gal(L/K), g • b h / b (g * h) * b g = c (g, h)) : b 1 = c (1, 1) := by
  simpa using hb 1 1

/-- The `K`-linear endomorphism of `L` by which an element of the crossed product acts, once a
`1`-cochain `b` trivialising the cocycle has been chosen: `a * u σ` acts as
`t ↦ a * b σ * σ t`. -/
def coboundaryRep (b : Gal(L/K) → Lˣ) (x : CrossedProduct c) : L →ₗ[K] L where
  toFun t := ∑ σ : Gal(L/K), x σ * ((b σ : Lˣ) : L) * σ t
  map_add' t u := by
    simp only [map_add, mul_add]
    rw [← Finset.sum_add_distrib]
  map_smul' k t := by
    simp only [RingHom.id_apply, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ ↦ mul_smul_comm k _ _

omit [Fact (IsMulCocycle₂ c)] in
/-- The defining formula for `coboundaryRep`. -/
theorem coboundaryRep_apply (b : Gal(L/K) → Lˣ) (x : CrossedProduct c) (t : L) :
    coboundaryRep b x t = ∑ σ : Gal(L/K), x σ * ((b σ : Lˣ) : L) * σ t := rfl

/-- **A coboundary splits the crossed product.** If the cocycle `c` is the coboundary of `b`,
then the crossed product acts on `L` as the full algebra of `K`-linear endomorphisms. -/
def coboundaryAlgHom (b : Gal(L/K) → Lˣ)
    (hb : ∀ g h : Gal(L/K), g • b h / b (g * h) * b g = c (g, h)) :
    CrossedProduct c →ₐ[K] Module.End K L where
  toFun := coboundaryRep b
  map_one' := by
    refine LinearMap.ext fun t ↦ ?_
    rw [coboundaryRep_apply, Finset.sum_eq_single 1 (fun g _ hg ↦ by
      rw [one_def, single_apply_of_ne _ hg, zero_mul, zero_mul])
      (fun h ↦ absurd (Finset.mem_univ _) h), one_def, single_apply_self, AlgEquiv.one_apply,
      map_one_of_isMulCoboundary₂ hb, Module.End.one_apply]
    linear_combination t * Units.inv_mul (c (1, 1))
  map_mul' x y := by
    refine LinearMap.ext fun t ↦ ?_
    rw [Module.End.mul_apply]
    have hR : coboundaryRep b x (coboundaryRep b y t)
        = ∑ σ : Gal(L/K), ∑ τ : Gal(L/K),
          x σ * ((b σ : Lˣ) : L) * (σ (y τ) * σ ((b τ : Lˣ) : L) * (σ * τ) t) := by
      rw [coboundaryRep_apply]
      refine Finset.sum_congr rfl fun σ _ ↦ ?_
      rw [coboundaryRep_apply, map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ ↦ by rw [map_mul, map_mul, AlgEquiv.mul_apply]
    have hL : coboundaryRep b (x * y) t
        = ∑ σ : Gal(L/K), ∑ τ : Gal(L/K),
          x σ * ((b σ : Lˣ) : L) * (σ (y τ) * σ ((b τ : Lˣ) : L) * (σ * τ) t) := by
      rw [coboundaryRep_apply]
      have e₁ : ∀ ρ : Gal(L/K), (x * y) ρ * ((b ρ : Lˣ) : L) * ρ t
          = ∑ σ : Gal(L/K), x σ * σ (y (σ⁻¹ * ρ)) * ((c (σ, σ⁻¹ * ρ) : Lˣ) : L)
            * ((b ρ : Lˣ) : L) * ρ t := fun ρ ↦ by
        rw [mul_apply, Finset.sum_mul, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun ρ (_ : ρ ∈ Finset.univ) ↦ e₁ ρ, Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ ↦ ?_
      refine Eq.trans (Equiv.sum_comp (Equiv.mulLeft σ) _).symm
        (Finset.sum_congr rfl fun τ _ ↦ ?_)
      simp only [Equiv.coe_mulLeft]
      rw [show σ⁻¹ * (σ * τ) = τ by group]
      linear_combination (-(x σ * σ (y τ) * (σ * τ) t)) * val_isMulCoboundary₂ hb σ τ
    rw [hL, hR]
  map_zero' := by
    refine LinearMap.ext fun t ↦ ?_
    simp [coboundaryRep_apply]
  map_add' x y := by
    refine LinearMap.ext fun t ↦ ?_
    rw [LinearMap.add_apply, coboundaryRep_apply, coboundaryRep_apply, coboundaryRep_apply,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ ↦ by rw [add_apply]; ring
  commutes' k := by
    refine LinearMap.ext fun t ↦ ?_
    rw [coboundaryRep_apply, Finset.sum_eq_single 1 (fun g _ hg ↦ by
      rw [algebraMap_apply, incl_def, single_apply_of_ne _ hg, zero_mul, zero_mul])
      (fun h ↦ absurd (Finset.mem_univ _) h), algebraMap_apply, incl_def, single_apply_self,
      AlgEquiv.one_apply, map_one_of_isMulCoboundary₂ hb, Module.algebraMap_end_apply,
      Algebra.smul_def]
    linear_combination (algebraMap K L k * t) * Units.inv_mul (c (1, 1))

/-- **A coboundary splits the crossed product**: the induced action on `L` is an isomorphism
onto `End_K L`. -/
def coboundaryAlgEquiv [IsGalois K L] (b : Gal(L/K) → Lˣ)
    (hb : ∀ g h : Gal(L/K), g • b h / b (g * h) * b g = c (g, h)) :
    CrossedProduct c ≃ₐ[K] Module.End K L := by
  have hinj : Function.Injective (coboundaryAlgHom b hb) :=
    (coboundaryAlgHom b hb).toRingHom.injective
  have hrank : finrank K (CrossedProduct c) = finrank K (Module.End K L) := by
    rw [finrank_eq (c := c), Module.finrank_linearMap, pow_two]
  exact AlgEquiv.ofBijective (coboundaryAlgHom b hb) ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
      (f := (coboundaryAlgHom b hb).toLinearMap)).1 hinj⟩

end Coboundary

/-- **A cocycle is a coboundary exactly when its crossed product is split**, i.e. when the
crossed product is a matrix algebra over `K`. -/
theorem isMulCoboundary₂_iff_isSplit [IsGalois K L] :
    IsMulCoboundary₂ c ↔ Algebra.IsSplit K (CrossedProduct c) K := by
  classical
  refine ⟨fun ⟨b, hb⟩ ↦ ⟨finrank K L, ?_, ⟨?_⟩⟩, isMulCoboundary₂_of_isSplit⟩
  · exact Module.finrank_pos.ne'
  · exact (Algebra.TensorProduct.lid K (CrossedProduct c)).trans
      ((coboundaryAlgEquiv b hb).trans (algEquivMatrix (Module.finBasis K L)))

end CrossedProduct

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Every `2`-cocycle of a finite Galois group is a coboundary once the relative Brauer group
vanishes.** -/
theorem isMulCoboundary₂_of_brauer
    (hBr : ∀ y : BrauerGroup K, BrauerGroup.baseChange K L y = 1 → y = 1)
    (c : Gal(L/K) × Gal(L/K) → Lˣ) (hc : IsMulCocycle₂ c) : IsMulCoboundary₂ c := by
  have : Fact (IsMulCocycle₂ c) := ⟨hc⟩
  have hsplitL : Algebra.IsSplit K (CrossedProduct c) L :=
    Algebra.IsCentralSimple.split_of_finrank (CrossedProduct.inclAlgHom (c := c))
      (by rw [CrossedProduct.finrank_eq, pow_two])
  refine CrossedProduct.isMulCoboundary₂_of_isSplit
    ((Algebra.isSplit_iff_baseChange_eq_one K (CrossedProduct c) K).2 ?_)
  rw [hBr _ ((Algebra.isSplit_iff_baseChange_eq_one K (CrossedProduct c) L).1 hsplitL), map_one]

/-- **Every `2`-cocycle of a finite Galois group is a coboundary once the relative Brauer group
vanishes**, with the hypothesis written as the triviality of the kernel of base change, which is
the relative Brauer group `Br(L/K)`. -/
theorem isMulCoboundary₂_of_ker_baseChange_eq_bot
    (hBr : (BrauerGroup.baseChange K L).ker = ⊥)
    (c : Gal(L/K) × Gal(L/K) → Lˣ) (hc : IsMulCocycle₂ c) : IsMulCoboundary₂ c :=
  isMulCoboundary₂_of_brauer
    (fun _ hy ↦ Subgroup.mem_bot.1 (hBr ▸ MonoidHom.mem_ker.2 hy)) c hc

-- `SeparableClosure K` unfolds to `separableClosure K (AlgebraicClosure K)`, and unfolding it
-- is needed to find the action of `Gal(M/K)` on `Mˣ` for `M` a subextension of it.
/-- **Degree-two vanishing for the absolute Galois group from the relative Brauer groups.**
If `Br(L/K) = 0` for every finite Galois subextension `L/K` of `Kˢᵉᵖ`, then every locally
constant `2`-cocycle on `Gal(Kˢᵉᵖ/K)` with values in `(Kˢᵉᵖ)ˣ` is a coboundary. -/
theorem isMulCoboundary₂_separableClosure_of_forall_brauer (K : Type u) [Field K]
    (hBr : ∀ (M : FiniteGaloisIntermediateField K (SeparableClosure K)) (y : BrauerGroup K),
      BrauerGroup.baseChange K ↥M y = 1 → y = 1)
    (f : Gal(SeparableClosure K/K) × Gal(SeparableClosure K/K) → (SeparableClosure K)ˣ)
    (hloc : IsLocallyConstant f) (hf : IsMulCocycle₂ f) : IsMulCoboundary₂ f :=
  isMulCoboundary₂_separableClosure_of_forall_finiteGalois K
    (fun M F hF ↦ isMulCoboundary₂_of_brauer (hBr M) F hF) f hloc hf

end Stacks.GaloisCohomology

end
