module

public import StacksFrontier.RingTheory.NoetherNormalization.FiniteInjectiveDimension
public import StacksFrontier.RingTheory.KrullDimension.GoingUpGoingDown
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.WeakRelativeNoetherNormalization

/-!
# A projection with fibres of dimension at most one

Let `A` be a finitely generated algebra over a field `k` with `dim A ≤ n + 1`. A Noether
normalization `k[x₁, …, xₛ] ⟶ A` (finite and injective, with `s ≤ dim A ≤ n + 1`) gives, through
its first `n` coordinates (padded by zero when `s ≤ n`), a morphism `Spec A ⟶ 𝔸ⁿ_k` all of whose
fibres have dimension at most one: `A` is finite over `k[x₁, …, xₙ][t]`, so every fibre of
`Spec A ⟶ Spec k[x₁, …, xₙ]` is quasi-finite over a fibre of the affine line, and has dimension at
most one (`AlgebraicGeometry.forall_topologicalKrullDim_fiber_le_of_quasiFinite_mvPolynomial`).
When `dim A = n + 1`, the Noether normalization has exactly `n + 1` variables and the map
`k[x₁, …, xₙ] ⟶ A` is injective.

This is the geometric input of the reduction of the trace formula of [Stacks, Tag 03V3] in
dimension `d` to dimension `d - 1` (the source's "general case follows easily from that case
together with the proper base change theorem"), and of the reduction of [Stacks, Tag 03VH] to
curves: an affine scheme of finite type of dimension `d` fibres over `𝔸^{d-1}` in curves.

## Main results

* `Stacks.NoetherNormalization.exists_algHom_mvPolynomial_topologicalKrullDim_fibre_le_one_of_le`:
  `dim A ≤ n + 1` gives `k[x₁, …, xₙ] ⟶ A` with fibres of dimension at most one.
* `Stacks.NoetherNormalization.exists_algHom_mvPolynomial_topologicalKrullDim_fibre_le_one`:
  `dim A = n + 1` gives such a map which is moreover injective.

## References

* [Stacks Project, Tag 00OW](https://stacks.math.columbia.edu/tag/00OW)
* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry MvPolynomial

universe u

namespace Stacks.NoetherNormalization

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A] {n : ℕ}

/-- The identification of the variables `Fin 1 ⊕ Fin n` with `Fin (n + 1)`, the extra variable
being the last one. -/
def lastSumEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  (Equiv.sumComm _ _).trans finSumFinEquiv

/-- The first `n` coordinates of a map out of `k[x₁, …, xₙ₊₁]`. -/
def firstCoordinates (φ : MvPolynomial (Fin (n + 1)) k →ₐ[k] A) :
    MvPolynomial (Fin n) k →ₐ[k] A :=
  φ.comp ((renameEquiv k (lastSumEquiv n)).toAlgHom.comp (rename Sum.inr))

/-- **The fibres of the first `n` coordinates of a finite map have dimension at most one.**  If
`φ : k[x₁, …, xₙ₊₁] ⟶ A` is finite, then every fibre of
`Spec A ⟶ Spec k[x₁, …, xₙ]`, along the first `n` coordinates, has dimension at most one: over
`C = k[x₁, …, xₙ]`, `A` is finite over `C[t]`. -/
theorem topologicalKrullDim_fibre_firstCoordinates_le_one
    (φ : MvPolynomial (Fin (n + 1)) k →ₐ[k] A) (hφ : φ.toRingHom.Finite)
    (y : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    topologicalKrullDim
      ↥(PrimeSpectrum.comap (firstCoordinates φ).toRingHom ⁻¹' {y}) ≤ 1 := by
  let C := MvPolynomial (Fin n) k
  let g := firstCoordinates φ
  let : Algebra C A := g.toRingHom.toAlgebra
  let ψ₀ : MvPolynomial (Fin 1) C →ₐ[k] A :=
    (φ.comp (renameEquiv k (lastSumEquiv n)).toAlgHom).comp
      (sumAlgEquiv k (Fin 1) (Fin n)).symm.toAlgHom
  have hψ₀C : ∀ c : C, ψ₀ (MvPolynomial.C c) = g c := by
    intro c
    have h := congrArg (fun F => F c)
      (sumAlgEquiv_comp_rename_inr k (S₁ := Fin 1) (S₂ := Fin n))
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_algHom,
      IsScalarTower.coe_toAlgHom'] at h
    simp only [ψ₀, g, firstCoordinates, AlgHom.coe_comp, Function.comp_apply,
      AlgEquiv.coe_algHom]
    congr 2
    apply (sumAlgEquiv k (Fin 1) (Fin n)).injective
    rw [AlgEquiv.apply_symm_apply, h]
    rfl
  let ψ : MvPolynomial (Fin 1) C →ₐ[C] A :=
    { ψ₀.toRingHom with
      commutes' := hψ₀C }
  have hfin : ψ.toRingHom.Finite := by
    show (ψ₀.toRingHom).Finite
    exact (hφ.comp (.of_surjective _ (renameEquiv k (lastSumEquiv n)).surjective)).comp
      (.of_surjective _ (sumAlgEquiv k (Fin 1) (Fin n)).symm.surjective)
  have h := forall_topologicalKrullDim_fiber_le_of_quasiFinite_mvPolynomial (R := C) (S := A) 1 ψ
    (RingHom.QuasiFinite.of_finite hfin) y
  let f := Spec.map (CommRingCat.ofHom (algebraMap C A))
  rw [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph] at h
  exact_mod_cast h

/-- **A projection to `𝔸ⁿ` with fibres of dimension at most one.**  For a finitely generated
algebra `A` over a field `k` with `dim A ≤ n + 1` there is a `k`-algebra map
`g : k[x₁, …, xₙ] ⟶ A` such that every fibre of `Spec A ⟶ 𝔸ⁿ_k` has dimension at most one. -/
theorem exists_algHom_mvPolynomial_topologicalKrullDim_fibre_le_one_of_le (k A : Type u)
    [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ)
    (h : ringKrullDim A ≤ n + 1) :
    ∃ g : MvPolynomial (Fin n) k →ₐ[k] A, ∀ y : PrimeSpectrum (MvPolynomial (Fin n) k),
      topologicalKrullDim ↥(PrimeSpectrum.comap g.toRingHom ⁻¹' {y}) ≤ 1 := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · refine ⟨aeval 0, fun y => ?_⟩
    refine (topologicalKrullDim_subspace_le _ _).trans ?_
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  obtain ⟨s, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hs : s ≤ n + 1 := by
    exact_mod_cast (natCast_le_ringKrullDim_of_finite_of_injective k φ hinj hfin).trans h
  -- `ν : k[x₁, …, xₙ₊₁] ⟶ k[x₁, …, xₛ]`, the identity on the first `s` variables and zero after
  let ν : MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin s) k :=
    aeval fun i => if hi : (i : ℕ) < s then X ⟨i, hi⟩ else 0
  have hν : Function.Surjective ν := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← MvPolynomial.adjoin_range_X, Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    refine ⟨X ⟨j, by omega⟩, ?_⟩
    simp [ν, j.isLt]
  exact ⟨firstCoordinates (φ.comp ν), topologicalKrullDim_fibre_firstCoordinates_le_one (φ.comp ν)
    (hfin.comp (.of_surjective _ hν))⟩

/-- **A dominant projection to `𝔸ⁿ` with fibres of dimension at most one.**  For a finitely
generated algebra `A` over a field `k` with `dim A = n + 1` there is an injective `k`-algebra map
`g : k[x₁, …, xₙ] ⟶ A` such that every fibre of `Spec A ⟶ 𝔸ⁿ_k` has dimension at most one: the
first `n` coordinates of a Noether normalization, which has exactly `n + 1` variables. -/
theorem exists_algHom_mvPolynomial_topologicalKrullDim_fibre_le_one (k A : Type u)
    [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ)
    (h : ringKrullDim A = n + 1) :
    ∃ g : MvPolynomial (Fin n) k →ₐ[k] A, Function.Injective g ∧
      ∀ y : PrimeSpectrum (MvPolynomial (Fin n) k),
        topologicalKrullDim ↥(PrimeSpectrum.comap g.toRingHom ⁻¹' {y}) ≤ 1 := by
  have : Nontrivial A := by
    by_contra hA
    rw [not_nontrivial_iff_subsingleton, ← ringKrullDim_eq_bot_iff_subsingleton, h] at hA
    exact WithBot.coe_ne_bot hA
  obtain ⟨s, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hs₁ : (s : WithBot ℕ∞) ≤ n + 1 :=
    (natCast_le_ringKrullDim_of_finite_of_injective k φ hinj hfin).trans h.le
  have hs₂ : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ s := by
    have hdim : ringKrullDim (MvPolynomial (Fin s) k) = s := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
        ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have := (integral_dim_up φ.toRingHom hfin.to_isIntegral).1
    rw [h, hdim] at this
    exact_mod_cast this
  obtain rfl : s = n + 1 := le_antisymm (by exact_mod_cast hs₁) (by exact_mod_cast hs₂)
  refine ⟨firstCoordinates φ, ?_, topologicalKrullDim_fibre_firstCoordinates_le_one φ hfin⟩
  simp only [firstCoordinates, AlgHom.coe_comp, AlgEquiv.coe_algHom]
  exact hinj.comp ((renameEquiv k (lastSumEquiv n)).injective.comp
    (rename_injective _ Sum.inr_injective))

end Stacks.NoetherNormalization
