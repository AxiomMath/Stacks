module

public import StacksFrontier.RingTheory.Koszul.Defs

/-!
# Additivity and base change for the Koszul differential

The Koszul differential `Koszul.d φ n : ⋀^(n+1) E →ₗ[R] ⋀ⁿ E` depends linearly on the
functional `φ`, and it moves along a base change `R → S`.

## Main results

* `Koszul.d_ιMulti`: the value of `Koszul.d φ n` on a wedge of `n + 1` vectors, computed
  inside the exterior power `⋀ⁿ E` rather than in the ambient exterior algebra.
* `Koszul.d_add`: additivity of `Koszul.d φ n` in `φ`.
* `Koszul.d_mem_smul_top`: if `φ` takes values in an ideal `J`, then `Koszul.d φ n` has
  image in `J • ⊤`.
* `Koszul.baseChangeMap`: the map `⋀[R]^n E →ₗ[R] ⋀[S]^n F` induced by an `R`-linear map
  `f : E →ₗ[R] F` into a module over an `R`-algebra `S`, with `Koszul.baseChangeMap_ιMulti`
  its value on a wedge of vectors.
* `Koszul.baseChangeMap_d`: `Koszul.baseChangeMap` is a map of Koszul complexes, provided the
  two functionals are compatible.
-/

@[expose] public section

open scoped ExteriorAlgebra

namespace Koszul

universe u v w

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- The Koszul differential of a wedge of `n + 1` vectors, computed in `⋀ⁿ E`: it is the
alternating sum of the wedges with one factor removed, weighted by the value of the functional
at the removed factor. This is `Koszul.contraction_ιMulti` transported to the exterior power. -/
theorem d_ιMulti (φ : Module.Dual R E) (n : ℕ) (v : Fin (n + 1) → E) :
    d φ n (exteriorPower.ιMulti R (n + 1) v) =
      ∑ k : Fin (n + 1), ((-1 : R) ^ k.val * φ (v k)) •
        exteriorPower.ιMulti R n (v ∘ k.succAbove) := by
  refine Subtype.ext ?_
  rw [d_apply_coe, exteriorPower.ιMulti_apply_coe, contraction_ιMulti, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- The Koszul differential is additive in the functional. -/
theorem d_add (φ ψ : Module.Dual R E) (n : ℕ) :
    Koszul.d (φ + ψ) n = Koszul.d φ n + Koszul.d ψ n := by
  have h : (contraction (φ + ψ) : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E)
      = contraction φ + contraction ψ := map_add _ _ _
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp only [LinearMap.add_apply, Submodule.coe_add, d_apply_coe]
  exact LinearMap.congr_fun h (x : ExteriorAlgebra R E)

/-- A submodule of the exterior power containing all wedges of vectors is everything. -/
private theorem mem_of_forall_ιMulti_mem {m : ℕ} (p : Submodule R (⋀[R]^m E))
    (h : ∀ v : Fin m → E, exteriorPower.ιMulti R m v ∈ p) (x : ⋀[R]^m E) : x ∈ p :=
  Submodule.span_le.2 (Set.range_subset_iff.2 h) (by rw [exteriorPower.ιMulti_span]; trivial)

/-- If the functional takes values in an ideal `J`, the Koszul differential has image in
`J • ⊤`. -/
theorem d_mem_smul_top (J : Ideal R) (φ : Module.Dual R E) (hφ : ∀ e : E, φ e ∈ J) (n : ℕ)
    (x : ⋀[R]^(n + 1) E) :
    Koszul.d φ n x ∈ J • (⊤ : Submodule R (⋀[R]^n E)) := by
  refine mem_of_forall_ιMulti_mem ((J • (⊤ : Submodule R (⋀[R]^n E))).comap (d φ n))
    (fun v => ?_) x
  rw [Submodule.mem_comap, d_ιMulti]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem_smul (J.mul_mem_left _ (hφ (v k))) Submodule.mem_top

section BaseChange

variable {S : Type w} [CommRing S] [Algebra R S]
  {F : Type*} [AddCommGroup F] [Module S F] [Module R F] [IsScalarTower R S F]

/-- The canonical alternating map `(Fin n → F) → ⋀[S]^n F`, viewed as an `R`-alternating map
through the scalar tower `R → S → F`. -/
noncomputable def ιMultiRestrictScalars (n : ℕ) : F [⋀^Fin n]→ₗ[R] (⋀[S]^n F) where
  toMultilinearMap := (exteriorPower.ιMulti S n).toMultilinearMap.restrictScalars R
  map_eq_zero_of_eq' v _i _j hv hij := (exteriorPower.ιMulti S n).map_eq_zero_of_eq v hv hij

/-- `Koszul.ιMultiRestrictScalars n` sends a family `v` to the wedge
`exteriorPower.ιMulti S n v`. -/
@[simp]
theorem ιMultiRestrictScalars_apply (n : ℕ) (v : Fin n → F) :
    ιMultiRestrictScalars (R := R) n v = exteriorPower.ιMulti S n v := rfl

/-- The map on exterior powers induced by a linear map into a module over a larger ring. -/
noncomputable def baseChangeMap (f : E →ₗ[R] F) (n : ℕ) : (⋀[R]^n E) →ₗ[R] (⋀[S]^n F) :=
  exteriorPower.alternatingMapLinearEquiv
    ((ιMultiRestrictScalars (R := R) (S := S) n).compLinearMap f)

/-- `Koszul.baseChangeMap` sends the wedge of a family of vectors to the wedge of their
images. Note that `exteriorPower.ιMulti R n v` is the element `⟨ExteriorAlgebra.ιMulti R n v, _⟩`
of `⋀[R]^n E`. -/
@[simp]
theorem baseChangeMap_ιMulti (f : E →ₗ[R] F) (n : ℕ) (v : Fin n → E) :
    baseChangeMap (S := S) f n (exteriorPower.ιMulti R n v)
      = exteriorPower.ιMulti S n (f ∘ v) := by
  rw [baseChangeMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply, ιMultiRestrictScalars_apply]
  rfl

/-- The underlying element of `Koszul.baseChangeMap` applied to a wedge of vectors. -/
theorem baseChangeMap_mk (f : E →ₗ[R] F) (n : ℕ) (v : Fin n → E)
    (h : ExteriorAlgebra.ιMulti R n v ∈ ⋀[R]^n E) :
    baseChangeMap (S := S) f n ⟨ExteriorAlgebra.ιMulti R n v, h⟩
      = ⟨ExteriorAlgebra.ιMulti S n (f ∘ v), ιMulti_mem n _⟩ :=
  baseChangeMap_ιMulti f n v

/-- `baseChangeMap` is compatible with the Koszul differentials, where the functional on the
target side is the `S`-linear functional whose composition with `f` is `algebraMap R S ∘ φ`. -/
theorem baseChangeMap_d (f : E →ₗ[R] F) (φ : Module.Dual R E) (ψ : Module.Dual S F)
    (hcompat : ∀ e : E, ψ (f e) = algebraMap R S (φ e)) (n : ℕ)
    (x : ⋀[R]^(n + 1) E) :
    baseChangeMap f n (Koszul.d φ n x) = Koszul.d ψ n (baseChangeMap f (n + 1) x) := by
  refine mem_of_forall_ιMulti_mem (LinearMap.eqLocus
    (baseChangeMap f n ∘ₗ d φ n) ((d ψ n).restrictScalars R ∘ₗ baseChangeMap f (n + 1)))
    (fun v => ?_) x
  rw [LinearMap.mem_eqLocus]
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [d_ιMulti, map_sum, baseChangeMap_ιMulti, d_ιMulti]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, baseChangeMap_ιMulti,
    ← IsScalarTower.algebraMap_smul S ((-1 : R) ^ k.val * φ (v k))]
  have hc : algebraMap R S ((-1 : R) ^ k.val * φ (v k))
      = (-1 : S) ^ k.val * ψ ((f ∘ v) k) := by
    rw [map_mul, map_pow, map_neg, map_one, Function.comp_apply, hcompat]
  rw [hc]
  rfl

end BaseChange

end Koszul

end
