module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyRootsExact

/-!
# Characteristic roots of the restriction of scalars of a linear endomorphism

Let `E/F` be a finite extension of fields, `V` a finite-dimensional `E`-vector space and
`f : V → V` an `E`-linear endomorphism.  The characteristic polynomial of `f` viewed as an
`F`-linear map is the norm of the characteristic polynomial of `f`: at `t ∈ F`,
`det_F(t - f) = N_{E/F}(det_E(t - f))` (`LinearMap.det_restrictScalars`).  Along an embedding
`ι : F → ℂ`, the norm is the product over the embeddings `ι' : E → ℂ` extending `ι`
(`Algebra.norm_eq_prod_embeddings`), so the complex roots of the `F`-characteristic polynomial
along `ι` are the roots of the `E`-characteristic polynomial along the various `ι'`.

This is the bridge between Laumon's theorem for the restriction of scalars `Res_{E/ℚ_ℓ} σ` of a
representation with coefficients in `E` (`Stacks.EtaleCohomology.LaumonOpenAffineLineInput`),
where the hypothesis is purity along every embedding `ι'` of `E` over `ι`, and its `E`-linear
form, where `π_U^*` acts `E`-linearly on `H¹_c` and is pure along each `ι'` separately.

## Main results

* `Stacks.EtaleCohomology.eval_charpoly_restrictScalars`:
  `χ_F(f)(t) = N_{E/F}(χ_E(f)(t))`.
* `Stacks.EtaleCohomology.isRoot_charpoly_restrictScalars_map_iff`: the roots along `ι` of
  `χ_F(f)` are the roots along the embeddings `ι'` of `E` over `ι` of `χ_E(f)`.
* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_restrictScalars_iff`: the weight bound
  along `ι` for `f` over `F` is the weight bound along every `ι'` over `ι` for `f` over `E`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.EtaleCohomology

variable {F E V : Type*} [Field F] [Field E] [Algebra F E] [AddCommGroup V] [Module E V]
  [Module F V] [IsScalarTower F E V] [FiniteDimensional E V] [FiniteDimensional F V]

/-- **The characteristic polynomial of the restriction of scalars, evaluated**: for an
`E`-linear endomorphism `f` and `t ∈ F`, `χ_F(f)(t) = N_{E/F}(χ_E(f)(t))`. -/
public theorem eval_charpoly_restrictScalars (f : V →ₗ[E] V) (t : F) :
    (f.restrictScalars F).charpoly.eval t =
      Algebra.norm F (f.charpoly.eval (algebraMap F E t)) := by
  rw [LinearMap.eval_charpoly, LinearMap.eval_charpoly, ← LinearMap.det_restrictScalars]
  congr 1
  ext v
  simp [Module.algebraMap_end_apply, algebraMap_smul]

/-- **Roots of the characteristic polynomial of the restriction of scalars**: for `E/F` finite
and an embedding `ι : F → ℂ`, a complex number is a root of `χ_F(f)` along `ι` if and only if it
is a root of `χ_E(f)` along some embedding `ι' : E → ℂ` extending `ι`. -/
public theorem isRoot_charpoly_restrictScalars_map_iff [FiniteDimensional F E] (f : V →ₗ[E] V)
    (ι : F →+* ℂ) (z : ℂ) :
    ((f.restrictScalars F).charpoly.map ι).IsRoot z ↔
      ∃ ι' : E →+* ℂ, (∀ c, ι' (algebraMap F E c) = ι c) ∧ (f.charpoly.map ι').IsRoot z := by
  classical
  let : Algebra F ℂ := ι.toAlgebra
  have : CharZero F := ι.charZero
  have hprod : (f.restrictScalars F).charpoly.map ι =
      ∏ σ : E →ₐ[F] ℂ, f.charpoly.map (σ : E →+* ℂ) := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono (s := Set.range ι) ?_ (Set.infinite_range_of_injective ι.injective)
    rintro _ ⟨t, rfl⟩
    simp only [Set.mem_setOf_eq, eval_map_apply, eval_prod, eval_charpoly_restrictScalars]
    rw [show ι (Algebra.norm F (f.charpoly.eval (algebraMap F E t))) =
        algebraMap F ℂ (Algebra.norm F (f.charpoly.eval (algebraMap F E t))) from rfl,
      Algebra.norm_eq_prod_embeddings]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [show ι t = (σ : E →+* ℂ) (algebraMap F E t) from (σ.commutes t).symm, eval_map_apply]
    rfl
  rw [hprod, IsRoot, eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨σ, -, hσ⟩
    exact ⟨σ, fun c => σ.commutes c, hσ⟩
  · rintro ⟨ι', hι', hz⟩
    exact ⟨{ ι' with commutes' := hι' }, Finset.mem_univ _, hz⟩

/-- **Weights of the restriction of scalars**: the absolute values of the roots of `χ_F(f)` along
`ι` are of the form `q ^ (w / 2)` with integers `w ≤ i` if and only if the same holds for the
roots of `χ_E(f)` along every embedding `ι'` of `E` extending `ι`. -/
public theorem isCharpolyNormMixedOfWeightLE_restrictScalars_iff [FiniteDimensional F E]
    (f : V →ₗ[E] V) (q : ℕ) (ι : F →+* ℂ) (i : ℤ) :
    IsCharpolyNormMixedOfWeightLE q ι i (f.restrictScalars F) ↔
      ∀ ι' : E →+* ℂ, (∀ c, ι' (algebraMap F E c) = ι c) →
        IsCharpolyNormMixedOfWeightLE q ι' i f := by
  constructor
  · intro h ι' hι' z hz
    exact h z ((isRoot_charpoly_restrictScalars_map_iff f ι z).2 ⟨ι', hι', hz⟩)
  · intro h z hz
    obtain ⟨ι', hι', hz'⟩ := (isRoot_charpoly_restrictScalars_map_iff f ι z).1 hz
    exact h ι' hι' z hz'

end Stacks.EtaleCohomology

end
