module

public import StacksFrontier.LinearAlgebra.ExteriorPower.Koszul
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The exterior powers of a module with a free rank-one submodule

Let `R` be a commutative ring and `0 → P → M → Q → 0` an exact sequence of `R`-modules with `P`
free of rank one, spanned by `p₀`, and `Q` projective. Write `e` for the image of `p₀` in `M`.
Wedging with `e` identifies `⋀ᵏ⁺¹ Q` with the kernel of `⋀ᵏ⁺² M → ⋀ᵏ⁺² Q`, so that

  `0 → P ⊗ ⋀ᵏ⁺¹ Q → ⋀ᵏ⁺² M → ⋀ᵏ⁺² Q → 0`

is exact, the first map sending `p ⊗ ⋀ᵏ⁺¹(g)(y)` to `a(p) ∧ y`.

The proof splits the sequence: a section of `M → Q` and the coordinate along `e` identify `M`
with `Q × R`, carrying `e` to `(0, 1)`, and `exteriorPower.prodRightEquiv` decomposes
`⋀ᵏ⁺²(Q × R)` as `⋀ᵏ⁺² Q × ⋀ᵏ⁺¹ Q`. Under that decomposition `⋀ᵏ⁺²(g)` is the first projection
and wedging with `e` is the inclusion of the second factor.

## Main results

* `exteriorPower.map_wedgeLeft`: functoriality carries wedging with `e` to wedging with the image
  of `e`.
* `exteriorPower.prodRightEquiv_wedgeLeft`: under `prodRightEquiv`, wedging with `(0, 1)` is the
  inclusion of the second factor.
* `exteriorPower.injective_and_range_eq_ker_of_wedgeLeft`: **the exactness statement**, for any
  linear map out of `P ⊗ ⋀ᵏ⁺¹ Q` satisfying the wedge-and-lift formula.
-/

@[expose] public section

open TensorProduct

namespace exteriorPower

variable {R : Type*} [CommRing R]

section Naturality

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Functoriality commutes with wedging**: `⋀ⁿ⁺¹(h)(e ∧ y) = h(e) ∧ ⋀ⁿ(h)(y)`. -/
theorem map_wedgeLeft (h : M →ₗ[R] N) (e : M) (n : ℕ) (y : ⋀[R]^n M) :
    map (n + 1) h (wedgeLeft e n y) = wedgeLeft (h e) n (map n h y) := by
  have key : map (n + 1) h ∘ₗ wedgeLeft e n = wedgeLeft (h e) n ∘ₗ map n h := by
    refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      wedgeLeft_ιMulti, map_apply_ιMulti]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  exact DFunLike.congr_fun key y

end Naturality

section Prod

variable (M : Type*) [AddCommGroup M] [Module R M]

/-- **Under `prodRightEquiv`, wedging with the generator `(0, 1)` is the inclusion of the second
factor**, read through the first projection `M × R → M`. -/
theorem prodRightEquiv_wedgeLeft (n : ℕ) (z : ⋀[R]^(n + 1) (M × R)) :
    prodRightEquiv R M (n + 1) (wedgeLeft ((0, 1) : M × R) (n + 1) z) =
      (0, map (n + 1) (LinearMap.fst R M R) z) := by
  rw [prodRightEquiv_apply]
  refine Prod.ext ?_ ?_
  · show map (n + 2) (LinearMap.fst R M R) (wedgeLeft ((0, 1) : M × R) (n + 1) z) = 0
    rw [← LinearMap.comp_apply, map_comp_wedgeLeft (LinearMap.fst R M R) _ rfl (n + 1),
      LinearMap.zero_apply]
  · show map (n + 1) (LinearMap.fst R M R)
      (contraction (LinearMap.snd R M R) (n + 1) (wedgeLeft ((0, 1) : M × R) (n + 1) z)) =
        map (n + 1) (LinearMap.fst R M R) z
    have hk := DFunLike.congr_fun
      (contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction (LinearMap.snd R M R)
        ((0, 1) : M × R) n) z
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.id_coe, id_eq, LinearMap.snd_apply, one_smul] at hk
    rw [eq_sub_of_add_eq hk, map_sub, ← LinearMap.comp_apply (map (n + 1) (LinearMap.fst R M R)),
      map_comp_wedgeLeft (LinearMap.fst R M R) _ rfl n, LinearMap.zero_apply, sub_zero]

end Prod

section Line

variable {P M Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]

/-- If `range a = ker g`, then `g ∘ a = 0`. -/
private theorem map_eq_zero_of_range_eq_ker {a : P →ₗ[R] M} {g : M →ₗ[R] Q}
    (hex : LinearMap.range a = LinearMap.ker g) (p : P) : g (a p) = 0 :=
  LinearMap.mem_ker.1 (hex ▸ LinearMap.mem_range_self a p)

/-- Every element of a module with a basis indexed by `Fin 1` is a multiple of the basis vector. -/
private theorem eq_coord_smul (b : Module.Basis (Fin 1) R P) (p : P) : p = b.coord 0 p • b 0 := by
  simpa using (b.sum_repr p).symm

/-- **The splitting of a short exact sequence with a free rank-one kernel**: a section `σ` of
`g` and a coordinate functional `φ` with `φ ∘ a = b.coord 0` and `φ ∘ σ = 0`, so that every
vector is `σ (g v) + φ v • a (b 0)`. -/
theorem exists_section_coord (a : P →ₗ[R] M) (g : M →ₗ[R] Q) (ha : Function.Injective a)
    (hg : Function.Surjective g) (hex : LinearMap.range a = LinearMap.ker g)
    (b : Module.Basis (Fin 1) R P) [Module.Projective R Q] :
    ∃ (σ : Q →ₗ[R] M) (φ : M →ₗ[R] R), g ∘ₗ σ = LinearMap.id ∧ φ (a (b 0)) = 1 ∧
      φ ∘ₗ σ = 0 ∧ ∀ v, v = σ (g v) + φ v • a (b 0) := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property g LinearMap.id hg
  have hd : ∀ v, v - σ (g v) ∈ LinearMap.range a := by
    intro v
    rw [hex, LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply g σ, hσ, LinearMap.id_apply,
      sub_self]
  let d : M →ₗ[R] LinearMap.range a :=
    LinearMap.codRestrict (LinearMap.range a) (LinearMap.id - σ ∘ₗ g) fun v ↦ hd v
  let φ : M →ₗ[R] R := b.coord 0 ∘ₗ (LinearEquiv.ofInjective a ha).symm.toLinearMap ∘ₗ d
  have hga := map_eq_zero_of_range_eq_ker hex
  have hpre : ∀ v, a ((LinearEquiv.ofInjective a ha).symm (d v)) = v - σ (g v) :=
    fun v ↦ congrArg Subtype.val ((LinearEquiv.ofInjective a ha).apply_symm_apply (d v))
  have hrepr := eq_coord_smul b
  refine ⟨σ, φ, hσ, ?_, ?_, fun v ↦ ?_⟩
  · have hdv : (LinearEquiv.ofInjective a ha).symm (d (a (b 0))) = b 0 := by
      refine ha ?_
      rw [hpre, hga, σ.map_zero, sub_zero]
    show b.coord 0 ((LinearEquiv.ofInjective a ha).symm (d (a (b 0)))) = 1
    rw [hdv, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  · refine LinearMap.ext fun q ↦ ?_
    have hdq : (LinearEquiv.ofInjective a ha).symm (d (σ q)) = 0 := by
      refine ha ?_
      rw [hpre, map_zero, ← LinearMap.comp_apply g σ, hσ, LinearMap.id_apply, sub_self]
    show b.coord 0 ((LinearEquiv.ofInjective a ha).symm (d (σ q))) = 0
    rw [hdq, map_zero]
  · have h := congrArg a (hrepr ((LinearEquiv.ofInjective a ha).symm (d v)))
    rw [hpre, map_smul] at h
    show v = σ (g v) + b.coord 0 ((LinearEquiv.ofInjective a ha).symm (d v)) • a (b 0)
    rw [← h, add_sub_cancel]

/-- **The exterior powers of a module with a free rank-one submodule.** Let
`0 → P → M → Q → 0` be exact with `P` free of rank one and `Q` projective, and let
`L : P ⊗ ⋀ᵏ⁺¹ Q → ⋀ᵏ⁺² M` satisfy the wedge-and-lift formula
`L (p ⊗ ⋀ᵏ⁺¹(g)(y)) = a(p) ∧ y`. Then `L` is injective with image the kernel of
`⋀ᵏ⁺²(g)`. -/
theorem injective_and_range_eq_ker_of_wedgeLeft (a : P →ₗ[R] M) (g : M →ₗ[R] Q)
    (ha : Function.Injective a) (hg : Function.Surjective g)
    (hex : LinearMap.range a = LinearMap.ker g) (b : Module.Basis (Fin 1) R P)
    [Module.Projective R Q] (k : ℕ) (L : P ⊗[R] ⋀[R]^(k + 1) Q →ₗ[R] ⋀[R]^(k + 2) M)
    (hL : ∀ p y, L (p ⊗ₜ map (k + 1) g y) = wedgeLeft (a p) (k + 1) y) :
    Function.Injective L ∧ LinearMap.range L = LinearMap.ker (map (k + 2) g) := by
  obtain ⟨σ, φ, hσ, hφe, hφσ, hv⟩ := exists_section_coord a g ha hg hex b
  set e := a (b 0) with he
  have hga := map_eq_zero_of_range_eq_ker hex
  -- the splitting `M ≃ Q × R`
  let Ψ : M ≃ₗ[R] Q × R :=
    LinearEquiv.ofLinear (g.prod φ) ((σ.coprod (LinearMap.toSpanSingleton R M e)))
      (by
        refine LinearMap.prod_ext (LinearMap.ext fun q ↦ ?_) (LinearMap.ext fun c ↦ ?_)
        · refine Prod.ext ?_ ?_
          · show g (σ q + (0 : R) • e) = q
            rw [zero_smul, add_zero, ← LinearMap.comp_apply, hσ, LinearMap.id_apply]
          · show φ (σ q + (0 : R) • e) = 0
            rw [zero_smul, add_zero, ← LinearMap.comp_apply, hφσ, LinearMap.zero_apply]
        · refine Prod.ext ?_ ?_
          · show g (σ 0 + c • e) = 0
            rw [map_zero, zero_add, map_smul, he, hga, smul_zero]
          · show φ (σ 0 + c • e) = c
            rw [map_zero, zero_add, map_smul, hφe, smul_eq_mul, mul_one])
      (LinearMap.ext fun v ↦ (hv v).symm)
  have hΨ1 : (LinearMap.fst R Q R).comp Ψ.toLinearMap = g := rfl
  have hΨe : Ψ e = (0, 1) := by
    refine Prod.ext ?_ ?_
    · exact hga (b 0)
    · exact hφe
  -- the decomposition of `⋀ᵏ⁺² M`
  let mΨ : ⋀[R]^(k + 2) M ≃ₗ[R] ⋀[R]^(k + 2) (Q × R) :=
    LinearEquiv.ofLinear (map (k + 2) Ψ.toLinearMap) (map (k + 2) Ψ.symm.toLinearMap)
      (by rw [← map_comp, show Ψ.toLinearMap ∘ₗ Ψ.symm.toLinearMap = LinearMap.id from
        LinearMap.ext Ψ.apply_symm_apply, map_id])
      (by rw [← map_comp, show Ψ.symm.toLinearMap ∘ₗ Ψ.toLinearMap = LinearMap.id from
        LinearMap.ext Ψ.symm_apply_apply, map_id])
  let Θ : ⋀[R]^(k + 2) M ≃ₗ[R] ⋀[R]^(k + 2) Q × ⋀[R]^(k + 1) Q :=
    mΨ.trans (prodRightEquiv R Q (k + 1))
  have hΘ1 : ∀ w, (Θ w).1 = map (k + 2) g w := by
    intro w
    show map (k + 2) (LinearMap.fst R Q R) (map (k + 2) Ψ.toLinearMap w) = _
    rw [← LinearMap.comp_apply, ← map_comp, hΨ1]
  have hΘwedge : ∀ y, Θ (wedgeLeft e (k + 1) y) = (0, map (k + 1) g y) := by
    intro y
    show prodRightEquiv R Q (k + 1) (map (k + 2) Ψ.toLinearMap (wedgeLeft e (k + 1) y)) = _
    rw [map_wedgeLeft, LinearEquiv.coe_coe, hΨe, prodRightEquiv_wedgeLeft,
      ← LinearMap.comp_apply, ← map_comp, hΨ1]
  -- `P ⊗ ⋀ᵏ⁺¹ Q` is `⋀ᵏ⁺¹ Q`, through `b 0`
  have hgσ : ∀ z : ⋀[R]^(k + 1) Q, map (k + 1) g (map (k + 1) σ z) = z := by
    intro z
    rw [← LinearMap.comp_apply, ← map_comp, hσ, map_id, LinearMap.id_apply]
  have hτ : ∀ z : ⋀[R]^(k + 1) Q, Θ (L (b 0 ⊗ₜ z)) = (0, z) := by
    intro z
    have h := hL (b 0) (map (k + 1) σ z)
    rw [hgσ] at h
    rw [h, ← he, hΘwedge, hgσ]
  have hrepr := eq_coord_smul b
  have hsurjτ : ∀ t : P ⊗[R] ⋀[R]^(k + 1) Q, ∃ z, t = b 0 ⊗ₜ z := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, (tmul_zero _ _).symm⟩
    | tmul p y =>
        refine ⟨b.coord 0 p • y, ?_⟩
        conv_lhs => rw [hrepr p]
        rw [smul_tmul]
    | add t t' ht ht' =>
        obtain ⟨z, rfl⟩ := ht
        obtain ⟨z', rfl⟩ := ht'
        exact ⟨z + z', (tmul_add _ _ _).symm⟩
  refine ⟨fun t t' htt' ↦ ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨z, rfl⟩ := hsurjτ t
    obtain ⟨z', rfl⟩ := hsurjτ t'
    have h := congrArg Θ htt'
    rw [hτ, hτ] at h
    rw [show z = z' from (Prod.ext_iff.1 h).2]
  · rintro _ ⟨t, rfl⟩
    obtain ⟨z, rfl⟩ := hsurjτ t
    rw [LinearMap.mem_ker, ← hΘ1, hτ]
  · intro w hw
    refine ⟨b 0 ⊗ₜ (Θ w).2, Θ.injective ?_⟩
    rw [hτ]
    refine Prod.ext ?_ rfl
    rw [hΘ1]
    exact (LinearMap.mem_ker.1 hw).symm

end Line

end exteriorPower
