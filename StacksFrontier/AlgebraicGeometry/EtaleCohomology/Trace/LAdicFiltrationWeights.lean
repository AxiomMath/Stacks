module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicLimitWeights

/-!
# Weights along a filtration of towers

The Leray spectral sequence of `Rg_!` enters the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3) through the
truncation triangles `τ_{≤ q-1} Rg_! K → τ_{≤ q} Rg_! K → R^q g_! K[-q]`: in a fixed degree `i`
they give towers `A_q` (the `i`-th cohomology of `RΓ_c` of the truncations) and exact sequences
`A_q → A_{q+1} → E_{q+1}` with `E_{q+1}` the tower of `H^{i-q-1}_c(R^{q+1} g_! K)`. This file
propagates a bound on the absolute values of the Frobenius characteristic roots along such a
chain of towers of `ℤ_ℓ`-modules, levelwise exact with finite terms, to the rational limits.

## Main results

* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_rationalLim_of_filtration`.
* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_rationalLim_of_surjective`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] [HasLimitsOfShape ℕᵒᵖ (ModuleCat.{v} ℤ_[ℓ])]

/-- **Weights along a filtration of towers.** Let `A q` and `E q` be towers of `ℤ_ℓ`-modules with
endomorphisms `φA q`, `φE q`, and maps `A q → A (q+1) → E (q+1)` exact at every level,
equivariant, with every `A q` levelwise finite. If the rational limits are finite dimensional and
the characteristic roots on the rational limits of `A 0` and of every `E (q+1)` have absolute
values `q' ^ (w / 2)` with `w ≤ b`, then so do those on the rational limit of every `A q`. -/
theorem isCharpolyNormMixedOfWeightLE_rationalLim_of_filtration
    (A E : ℕ → (ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ])) (α : ∀ q, A q ⟶ A (q + 1))
    (β : ∀ q, A (q + 1) ⟶ E (q + 1))
    (hex : ∀ q n, Function.Exact ((α q).app n) ((β q).app n))
    (hfin : ∀ q n, Finite ((A q).obj n))
    (φA : ∀ q, A q ⟶ A q) (φE : ∀ q, E q ⟶ E q)
    (hα : ∀ q, φA q ≫ α q = α q ≫ φA (q + 1)) (hβ : ∀ q, φA (q + 1) ≫ β q = β q ≫ φE (q + 1))
    (hFDA : ∀ q, FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj (A q)))
    (hFDE : ∀ q, FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj (E q)))
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}
    (h0 : IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map (φA 0)).hom)
    (hE : ∀ q, IsCharpolyNormMixedOfWeightLE q' ι b
      ((rationalLim (ℓ := ℓ)).map (φE (q + 1))).hom) (q : ℕ) :
    IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map (φA q)).hom := by
  induction q with
  | zero => exact h0
  | succ q ih =>
    have := hFDA q
    have := hFDA (q + 1)
    have := hFDE (q + 1)
    exact isCharpolyNormMixedOfWeightLE_rationalLimMap_of_exact (α q) (β q) (hex q) (hfin q)
      (φA q) (φA (q + 1)) (φE (q + 1)) (hα q) (hβ q) ih (hE q)

/-- **Weights pass to a levelwise surjective image of a levelwise finite tower.** -/
theorem isCharpolyNormMixedOfWeightLE_rationalLim_of_surjective {A B : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]}
    (π : A ⟶ B) (hπ : ∀ n, Function.Surjective (π.app n)) (hfin : ∀ n, Finite (A.obj n))
    (φA : A ⟶ A) (φB : B ⟶ B) (hφ : φA ≫ π = π ≫ φB)
    [FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A)]
    [FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj B)]
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}
    (hA : IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map φA).hom) :
    IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map φB).hom := by
  have hex := exact_rationalLimMap_of_finite (ℓ := ℓ) π (0 : B ⟶ B)
    (fun n => by
      rw [Function.Exact]
      intro y
      simp only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply, true_iff]
      exact (hπ n) y) hfin
  refine hA.of_surjective (p := ((rationalLim (ℓ := ℓ)).map π).hom) (fun a => ?_) (fun y => ?_)
  · have h := congrArg (fun t => (ModuleCat.Hom.hom ((rationalLim (ℓ := ℓ)).map t)) a) hφ
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  · refine (hex y).1 ?_
    have h0 : (rationalLim (ℓ := ℓ)).map (0 : B ⟶ B) = 0 := by
      show (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map (limMap 0) = 0
      rw [show (limMap (0 : B ⟶ B)) = 0 from limit.hom_ext (fun j => by simp), Functor.map_zero]
    rw [h0]
    rfl

end Stacks.EtaleCohomology
