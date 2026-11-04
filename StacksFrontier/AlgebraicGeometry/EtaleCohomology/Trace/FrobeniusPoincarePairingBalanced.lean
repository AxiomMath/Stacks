module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPoincarePairing
public import Mathlib.RingTheory.Trace.Basic

/-!
# Complex eigenvalues under a balanced perfect pairing over a subfield

Let `E/K` be a finite separable field extension, `V`, `W` finite-dimensional `E`-vector spaces and
`B₀ : V × W → K` a perfect `K`-bilinear pairing which is `E`-balanced:
`B₀(e v, w) = B₀(v, e w)`. Composition with the trace `Tr_{E/K}` identifies `E`-linear forms on
`W` with `K`-linear forms (`Stacks.EtaleCohomology.bijective_traceDualMap`: injective by the
nondegeneracy of the trace form, and both sides have `K`-dimension `dim_K W`), so `B₀ = Tr ∘ B`
for a unique `E`-bilinear `B`, which is perfect. For `E`-linear `f`, `g` with
`B₀(f v, g w) = c B₀(v, w)`, `c ∈ K` nonzero, the same holds for `B`, so the complex roots `z` of
the `E`-linear characteristic polynomial of `f` along an embedding `ι : E → ℂ` are nonzero and
`ι c / z` is a root of that of `g` (`Stacks.EtaleCohomology.isRoot_div_charpoly_of_isPerfPair`)
— `Stacks.EtaleCohomology.isRoot_div_charpoly_of_isPerfPair_balanced`.

This is how Poincaré duality, a perfect pairing of `ℚ_ℓ`-vector spaces balanced for the action of
the coefficient field `E`, constrains the `E`-linear Frobenius characteristic polynomials, in the
purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.traceDualMap`: composition of `E`-linear forms with `Tr_{E/K}`.

## Main results

* `Stacks.EtaleCohomology.bijective_traceDualMap`: composition with the trace is bijective.
* `Stacks.EtaleCohomology.isRoot_div_charpoly_of_isPerfPair_balanced`: the eigenvalue relation
  for a balanced perfect pairing over a subfield.
-/

@[expose] public noncomputable section

open Module Polynomial

namespace Stacks.EtaleCohomology

variable (K E : Type*) [Field K] [Field E] [Algebra K E]
  (W : Type*) [AddCommGroup W] [Module E W] [Module K W] [IsScalarTower K E W]

/-- **Composition with the trace**: an `E`-linear form `λ` on `W` gives the `K`-linear form
`Tr_{E/K} ∘ λ`. -/
def traceDualMap : Dual E W →ₗ[K] Dual K W where
  toFun l := (Algebra.trace K E).comp (l.restrictScalars K)
  map_add' l l' := by
    ext w
    simp
  map_smul' a l := by
    ext w
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      LinearMap.smul_apply, RingHom.id_apply]
    rw [← LinearMap.map_smul (Algebra.trace K E)]

/-- `traceDualMap K E W l` sends `w` to `Tr_{E/K}(l w)`. -/
@[simp]
theorem traceDualMap_apply (l : Dual E W) (w : W) :
    traceDualMap K E W l w = Algebra.trace K E (l w) :=
  rfl

/-- **Composition with the trace is injective** for a finite separable extension `E/K`. -/
theorem injective_traceDualMap [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    Function.Injective (traceDualMap K E W) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro l hl
  ext w
  have h : ∀ e : E, Algebra.traceForm K E (l w) e = 0 := fun e => by
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← l.map_smul]
    exact (LinearMap.congr_fun hl (e • w)).trans (LinearMap.zero_apply _)
  exact (traceForm_nondegenerate K E).1 _ h

/-- **Composition with the trace is bijective** for a finite separable extension `E/K` and `W`
finite-dimensional over `E`. -/
theorem bijective_traceDualMap [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [FiniteDimensional E W] : Function.Bijective (traceDualMap K E W) := by
  have : FiniteDimensional K W := Module.Finite.trans E W
  refine ⟨injective_traceDualMap K E W, ?_⟩
  have : FiniteDimensional K (Dual E W) := Module.Finite.trans E (Dual E W)
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [LinearMap.finrank_range_of_inj (injective_traceDualMap K E W),
    Subspace.dual_finrank_eq, ← Module.finrank_mul_finrank K E W,
    ← Module.finrank_mul_finrank K E (Dual E W), Subspace.dual_finrank_eq]

variable {K E} {V : Type*} [AddCommGroup V] [Module E V] [Module K V] [IsScalarTower K E V]
  {W}

omit [IsScalarTower K E V] in
/-- **Complex eigenvalues under a balanced twisted-equivariant perfect pairing over a subfield.**
Let `E/K` be finite separable, `B₀ : V × W → K` a perfect `K`-bilinear pairing of
finite-dimensional `E`-vector spaces with `B₀(e v, w) = B₀(v, e w)`, and `f`, `g` `E`-linear with
`B₀(f v, g w) = c B₀(v, w)`, `c ∈ K` nonzero. Then for every embedding `ι : E →+* ℂ`, every complex
root `z` of the `E`-linear characteristic polynomial of `f` along `ι` is nonzero and `ι c / z` is
a root of that of `g`. -/
theorem isRoot_div_charpoly_of_isPerfPair_balanced [FiniteDimensional K E]
    [Algebra.IsSeparable K E] [FiniteDimensional E V] [FiniteDimensional E W]
    (B₀ : V →ₗ[K] W →ₗ[K] K) [B₀.IsPerfPair]
    (hbal : ∀ (e : E) (v : V) (w : W), B₀ (e • v) w = B₀ v (e • w))
    {f : Module.End E V} {g : Module.End E W} {c : K}
    (hfg : ∀ v w, B₀ (f v) (g w) = c * B₀ v w) (hc : c ≠ 0) (ι : E →+* ℂ) {z : ℂ}
    (hz : (f.charpoly.map ι).IsRoot z) :
    z ≠ 0 ∧ (g.charpoly.map ι).IsRoot (ι (algebraMap K E c) / z) := by
  let τ := LinearEquiv.ofBijective (traceDualMap K E W) (bijective_traceDualMap K E W)
  have hτ : ∀ l w, τ l w = Algebra.trace K E (l w) := fun _ _ => rfl
  have hτs : ∀ v w, Algebra.trace K E (τ.symm (B₀ v) w) = B₀ v w := fun v w => by
    rw [← hτ, LinearEquiv.apply_symm_apply]
  let B : V →ₗ[E] W →ₗ[E] E :=
    { toFun := fun v => τ.symm (B₀ v)
      map_add' := fun v v' => by rw [map_add, map_add]
      map_smul' := fun e v => by
        refine τ.injective (LinearMap.ext fun w => ?_)
        rw [LinearEquiv.apply_symm_apply, RingHom.id_apply, hτ, LinearMap.smul_apply,
          ← LinearMap.map_smul, hτs, hbal] }
  have hB : ∀ v w, Algebra.trace K E (B v w) = B₀ v w := hτs
  have hBf : ∀ v w, B (f v) (g w) = algebraMap K E c * B v w := fun v w => by
    have h := congrArg (fun l : Dual E W => l w)
      (τ.injective (show τ ((B (f v)).comp g) = τ (algebraMap K E c • B v) from
        LinearMap.ext fun w' => by
          rw [hτ, hτ, LinearMap.comp_apply, hB, hfg, LinearMap.smul_apply, smul_eq_mul,
            ← Algebra.smul_def, LinearMap.map_smul, hB, smul_eq_mul]))
    simpa [Algebra.smul_def] using h
  have hB' : ∀ {v w v' w'}, B v w = B v' w' → B₀ v w = B₀ v' w' := fun h => by
    rw [← hB, ← hB, h]
  have : B.IsPerfPair :=
    LinearMap.IsPerfPair.of_injective
      (fun v v' h => (LinearMap.IsPerfPair.bijective_left B₀).1
        (LinearMap.ext fun w => hB' (LinearMap.congr_fun h w)))
      (fun w w' h => (LinearMap.IsPerfPair.bijective_right B₀).1
        (LinearMap.ext fun v => hB' (LinearMap.congr_fun h v)))
  exact isRoot_div_charpoly_of_isPerfPair (B := B) hBf
    ((map_ne_zero_iff _ (algebraMap K E).injective).2 hc) ι hz

end Stacks.EtaleCohomology

end
