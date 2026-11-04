module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.PowerFunctors

/-!
# The zeroth homology of a degreewise exterior power

Let `B` be a commutative ring and let `X` be a simplicial `B`-module. The zeroth homology of
the Moore complex (`AlgebraicTopology.alternatingFaceMapComplex`) of the degreewise `k`-th
exterior power of `X` is the `k`-th exterior power of the zeroth homology of `X`:

`H₀(⋀ᵏ X) ≅ ⋀ᵏ (H₀ X)`.

## Main results

* `nonempty_linearEquiv_homologyZero_extPowFunctor`: the displayed isomorphism, as the
  nonemptiness of a type of linear equivalences.

## Implementation notes

The zeroth homology of a Moore complex is the cokernel of `δ₀ - δ₁ : X_1 → X_0`: this is
`Stacks.SimplicialPower.exists_homologyZero_presentation`, which presents it through the
identification of `H₀` of a chain complex with the opcycles in degree `0`, i.e. with that
cokernel.

Right-exactness of the exterior power (`exterior_power_presentation`, Tag 00DO) identifies the
kernel of `⋀ᵏ(π) : ⋀ᵏ(X_0) → ⋀ᵏ(H₀ X)` with the image of the presentation map
`β : X_1 ⊗ ⋀^{k-1}(X_0) → ⋀ᵏ(X_0)`, `β (m ⊗ y) = (δ₀ - δ₁)(m) ∧ y`. The degeneracy `σ₀` is a
common section of `δ₀` and `δ₁`, and `β (m ⊗ y) = (⋀ᵏδ₀ - ⋀ᵏδ₁)(m ∧ ⋀^{k-1}(σ₀)(y))`, so that
image coincides with the image of `⋀ᵏδ₀ - ⋀ᵏδ₁`, which is exactly what the Moore complex of
`⋀ᵏ X` divides by in degree `0`. In degree `k = 0` both sides are the base ring and the two
images are zero, so the same final step applies.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

open scoped Simplicial TensorProduct

universe u

namespace Stacks.SimplicialPower

/-! ### The zeroth exterior power -/

/-- Naturality of the identification `⋀⁰(M) ≃ R`, in applied form. -/
public lemma exteriorPower_zeroEquiv_map {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (x : ⋀[R]^0 M) :
    exteriorPower.zeroEquiv R N (exteriorPower.map 0 f x) = exteriorPower.zeroEquiv R M x :=
  LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality f) x

/-- The zeroth exterior power is functorially constant: `⋀⁰(f)` does not depend on `f`. -/
public lemma exteriorPower_map_zero_eq {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f g : M →ₗ[R] N) :
    exteriorPower.map 0 f = exteriorPower.map 0 g :=
  LinearMap.ext fun x => (exteriorPower.zeroEquiv R N).injective
    ((exteriorPower_zeroEquiv_map f x).trans (exteriorPower_zeroEquiv_map g x).symm)

/-- The zeroth exterior power of any linear map is injective. -/
public lemma exteriorPower_map_zero_injective {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Function.Injective (exteriorPower.map 0 f) := fun x y hxy =>
  (exteriorPower.zeroEquiv R M).injective
    ((exteriorPower_zeroEquiv_map f x).symm.trans
      ((congrArg (exteriorPower.zeroEquiv R N) hxy).trans (exteriorPower_zeroEquiv_map f y)))

/-! ### The presentation map `β` of the exterior power -/

/-- The presentation map `β` built on `g` is the wedge product with the image of `g`. -/
public lemma beta_eq_beta_id {R M₁ M₂ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (g : M₂ →ₗ[R] M₁) (j : ℕ) (m : M₂) (y : ⋀[R]^j M₁) :
    ExtPow.beta j g (m ⊗ₜ[R] y) =
      ExtPow.beta j (LinearMap.id : M₁ →ₗ[R] M₁) (g m ⊗ₜ[R] y) :=
  Subtype.ext rfl

/-- Naturality of the wedge product `m ⊗ w ↦ m ∧ w` in the module. -/
public lemma map_beta_id {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (j : ℕ) (m : M) (w : ⋀[R]^j M) :
    exteriorPower.map (j + 1) f (ExtPow.beta j (LinearMap.id : M →ₗ[R] M) (m ⊗ₜ[R] w)) =
      ExtPow.beta j (LinearMap.id : N →ₗ[R] N)
        (f m ⊗ₜ[R] exteriorPower.map j f w) := by
  apply Subtype.ext
  rw [ExtPow.map_coe, ExtPow.beta_tmul, ExtPow.beta_tmul, map_mul,
    ExteriorAlgebra.map_apply_ι, ← ExtPow.map_coe]
  rfl

/-- If `f₀` and `f₁` have a common section, the image of the presentation map `β` built on
`f₀ - f₁` is contained in the image of `⋀^{j+1}(f₀) - ⋀^{j+1}(f₁)`: a decomposable element
`(f₀ - f₁)(m) ∧ y` is the value of that difference at `m ∧ ⋀^j(s)(y)`. -/
public lemma range_beta_le_range_sub {R M₁ M₂ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (f₀ f₁ : M₂ →ₗ[R] M₁) (s : M₁ →ₗ[R] M₂)
    (h₀ : f₀.comp s = LinearMap.id) (h₁ : f₁.comp s = LinearMap.id) (j : ℕ) :
    LinearMap.range (ExtPow.beta j (f₀ - f₁)) ≤
      LinearMap.range (exteriorPower.map (j + 1) f₀ - exteriorPower.map (j + 1) f₁) := by
  have hcomp : ExtPow.beta j (f₀ - f₁) =
      (exteriorPower.map (j + 1) f₀ - exteriorPower.map (j + 1) f₁).comp
        ((ExtPow.beta j (LinearMap.id : M₂ →ₗ[R] M₂)).comp
          (TensorProduct.map (LinearMap.id : M₂ →ₗ[R] M₂)
            (exteriorPower.map j s))) := by
    refine TensorProduct.ext' fun m y => ?_
    have hs : ∀ f : M₂ →ₗ[R] M₁, f.comp s = LinearMap.id →
        exteriorPower.map j f (exteriorPower.map j s y) = y := fun f h => by
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, h, exteriorPower.map_id,
        LinearMap.id_apply]
    rw [beta_eq_beta_id (f₀ - f₁) j m y]
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.sub_apply, map_beta_id, hs f₀ h₀, hs f₁ h₁]
    rw [TensorProduct.sub_tmul, map_sub]
  rw [hcomp]
  exact LinearMap.range_comp_le_range _ _

/-- For two maps `f₀, f₁ : M₂ → M₁` with a common section whose difference presents
`π : M₁ → M`, the kernel of `⋀ᵏ(π)` is the image of `⋀ᵏ(f₀) - ⋀ᵏ(f₁)`. -/
public lemma ker_map_eq_range_sub {R M M₁ M₂ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    (f₀ f₁ : M₂ →ₗ[R] M₁) (s : M₁ →ₗ[R] M₂)
    (h₀ : f₀.comp s = LinearMap.id) (h₁ : f₁.comp s = LinearMap.id)
    (π : M₁ →ₗ[R] M) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π = LinearMap.range (f₀ - f₁)) (k : ℕ) :
    LinearMap.ker (exteriorPower.map k π) =
      LinearMap.range (exteriorPower.map k f₀ - exteriorPower.map k f₁) := by
  have hπf : π.comp f₀ = π.comp f₁ := by
    refine LinearMap.ext fun m => ?_
    have hm : (f₀ - f₁) m ∈ LinearMap.ker π := by
      rw [hker]
      exact LinearMap.mem_range_self _ m
    rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, sub_eq_zero] at hm
    simpa only [LinearMap.comp_apply] using hm
  have hle : LinearMap.range (exteriorPower.map k f₀ - exteriorPower.map k f₁) ≤
      LinearMap.ker (exteriorPower.map k π) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, ← LinearMap.comp_apply,
      ← LinearMap.comp_apply, ← exteriorPower.map_comp, ← exteriorPower.map_comp, hπf,
      sub_self]
  obtain _ | j := k
  · rw [exteriorPower_map_zero_eq f₀ f₁, sub_self, LinearMap.range_zero,
      LinearMap.ker_eq_bot.mpr (exteriorPower_map_zero_injective π)]
  · refine le_antisymm ?_ hle
    rw [← (exterior_power_presentation (f₀ - f₁) π hπ hker.symm j).2]
    exact range_beta_le_range_sub f₀ f₁ s h₀ h₁ j

/-! ### The zeroth homology of a Moore complex -/

variable {B : Type u} [CommRing B]

/-- The degree-one differential of the Moore complex of a simplicial module is `δ₀ - δ₁`. -/
public lemma hom_d_one_zero (Y : SimplicialObject (ModuleCat.{u} B)) :
    (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj Y).d 1 0).hom =
      (Y.δ (0 : Fin 2)).hom - (Y.δ (1 : Fin 2)).hom := by
  show ((AlternatingFaceMapComplex.obj Y).d 1 0).hom = _
  rw [AlternatingFaceMapComplex.obj_d_eq Y 0]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- The zeroth homology of a chain complex of modules indexed by `ℕ` is the cokernel of the
differential `d₁ : K₁ → K₀`: there is a surjection from `K₀` onto it whose kernel is the image
of that differential. -/
public lemma exists_homologyZero_cokernel (K : ChainComplex (ModuleCat.{u} B) ℕ) :
    ∃ π : (K.X 0 : ModuleCat.{u} B) →ₗ[B] (K.homology 0 : ModuleCat.{u} B),
      Function.Surjective π ∧ LinearMap.ker π = LinearMap.range (K.d 1 0).hom := by
  let e : (K.homology 0 : ModuleCat.{u} B) ≃ₗ[B] (K.opcycles 0 : ModuleCat.{u} B) :=
    (ChainComplex.isoHomologyι₀ K).toLinearEquiv
  have hp : Function.Surjective (K.pOpcycles 0).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hex : (ShortComplex.mk (K.d 1 0) (K.pOpcycles 0) (K.d_pOpcycles 1 0)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.opcyclesIsCokernel 1 0 (by simp))
  refine ⟨e.symm.toLinearMap.comp (K.pOpcycles 0).hom, ?_, ?_⟩
  · intro z
    obtain ⟨x, hx⟩ := hp (e z)
    exact ⟨x, by simp [hx]⟩
  · rw [hex.moduleCat_range_eq_ker]
    ext x
    simp [LinearMap.mem_ker]

/-- The zeroth homology of the Moore complex of a simplicial module `Y` is the cokernel of
`δ₀ - δ₁ : Y_1 → Y_0`: there is a surjection from `Y_0` onto it with that image as kernel. -/
public lemma exists_homologyZero_presentation (Y : SimplicialObject (ModuleCat.{u} B)) :
    ∃ π : (Y _⦋0⦌ : ModuleCat.{u} B) →ₗ[B]
        (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj Y).homology 0 : ModuleCat.{u} B),
      Function.Surjective π ∧
        LinearMap.ker π =
          LinearMap.range ((Y.δ (0 : Fin 2)).hom - (Y.δ (1 : Fin 2)).hom) := by
  obtain ⟨π, hπ, hk⟩ :=
    exists_homologyZero_cokernel ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj Y)
  exact ⟨π, hπ, by rw [hk, hom_d_one_zero]⟩

/-! ### The main comparison -/

/-- The faces of the degreewise exterior power are the exterior powers of the faces. -/
public lemma comp_extPowFunctor_δ (X : SimplicialObject (ModuleCat.{u} B)) (k : ℕ)
    (i : Fin 2) :
    (SimplicialObject.δ (X ⋙ Stacks.ModuleCat.extPowFunctor B k) i).hom =
      exteriorPower.map k ((X.δ i).hom) := rfl

end Stacks.SimplicialPower

/-- The zeroth homology of the degreewise exterior power is the exterior power of the
zeroth homology. -/
public lemma nonempty_linearEquiv_homologyZero_extPowFunctor
    (B : Type u) [CommRing B] (X : SimplicialObject (ModuleCat.{u} B)) (k : ℕ) :
    Nonempty (
      (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} B)).obj
          (X ⋙ Stacks.ModuleCat.extPowFunctor B k)).homology 0 : ModuleCat.{u} B) ≃ₗ[B]
      ⋀[B]^k (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} B)).obj
          X).homology 0 : ModuleCat.{u} B)) := by
  obtain ⟨π, hπ, hkerπ⟩ := Stacks.SimplicialPower.exists_homologyZero_presentation X
  obtain ⟨π', hπ', hkerπ'⟩ := Stacks.SimplicialPower.exists_homologyZero_presentation
    (X ⋙ Stacks.ModuleCat.extPowFunctor B k)
  have hσ₀ : ((X.δ (0 : Fin 2)).hom).comp ((X.σ (0 : Fin 1)).hom) = LinearMap.id :=
    congrArg ModuleCat.Hom.hom (X.δ_comp_σ_self (i := (0 : Fin 1)))
  have hσ₁ : ((X.δ (1 : Fin 2)).hom).comp ((X.σ (0 : Fin 1)).hom) = LinearMap.id :=
    congrArg ModuleCat.Hom.hom (X.δ_comp_σ_succ (i := (0 : Fin 1)))
  have hkey := Stacks.SimplicialPower.ker_map_eq_range_sub ((X.δ (0 : Fin 2)).hom)
    ((X.δ (1 : Fin 2)).hom) ((X.σ (0 : Fin 1)).hom) hσ₀ hσ₁ π hπ hkerπ k
  let π₂ : (⋀[B]^k (X _⦋0⦌ : ModuleCat.{u} B)) →ₗ[B]
      (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (X ⋙ Stacks.ModuleCat.extPowFunctor B k)).homology 0 : ModuleCat.{u} B) := π'
  have hπ₂ : Function.Surjective π₂ := hπ'
  have hker₂ : LinearMap.ker π₂ =
      LinearMap.range (exteriorPower.map k ((X.δ (0 : Fin 2)).hom) -
        exteriorPower.map k ((X.δ (1 : Fin 2)).hom)) := hkerπ'
  exact ⟨(LinearMap.quotKerEquivOfSurjective π₂ hπ₂).symm.trans
    ((Submodule.quotEquivOfEq _ _ (hker₂.trans hkey.symm)).trans
      (LinearMap.quotKerEquivOfSurjective (exteriorPower.map k π)
        (exteriorPower.map_surjective (n := k) hπ)))⟩

end
