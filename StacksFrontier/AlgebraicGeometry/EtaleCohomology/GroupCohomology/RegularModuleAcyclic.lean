module

public import Mathlib.FieldTheory.Galois.NormalBasis
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteCochains

/-!
# The regular module is acyclic, and the additive group of a finite Galois extension

Let `Γ` be a group and `B` an abelian group. The *regular* `Γ`-module on `B` is the group of all
functions `Γ → B` with `Γ` acting by right translation of the argument. This file shows that it
has no cohomology in degrees one and two: every `1`-cocycle is `dZero` of a `0`-cochain and every
`2`-cocycle is `dOne` of a `1`-cochain, with explicit formulas.

The application is to a finite Galois extension `L'/L`. The normal basis theorem says that `L'`
is free of rank one over the group algebra of `Gal(L'/L)`, which is exactly the statement that
the additive group of `L'` is the regular `Gal(L'/L)`-module on `L`. Consequently `H ¹` and `H ²`
of `Gal(L'/L)` acting on the additive group of `L'` vanish — the additive analogue of Hilbert 90
and its degree-two companion.

## Main definitions

* `Stacks.GroupCohomology.normalBasisAddEquiv`: the normal basis theorem read as an additive
  isomorphism `L' ≃+ (Gal(L'/L) → L)`, sending `x` to its coordinate function `t ↦ c^{t⁻¹}(x)`
  in Mathlib's `IsGalois.normalBasis`.

## Main results

* `Stacks.GroupCohomology.exists_dZero_eq_of_regular` and
  `Stacks.GroupCohomology.exists_dOne_eq_of_regular`: **a module isomorphic to the regular
  module has vanishing cohomology in degrees one and two.**
* `Stacks.GroupCohomology.normalBasisAddEquiv_smul`: the normal basis isomorphism turns the
  Galois action into right translation, so the additive group of a finite Galois extension is a
  regular module.
* `Stacks.GroupCohomology.exists_dZero_eq_finiteGalois` and
  `Stacks.GroupCohomology.exists_dOne_eq_finiteGalois`: **the additive group of a finite Galois
  extension has vanishing `H ¹` and `H ²`.**

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
-/

@[expose] public noncomputable section

open groupCohomology

namespace Stacks.GroupCohomology

/-! ### Acyclicity of the regular module -/

section Regular

variable {Γ : Type*} [Group Γ] {B : Type*} [AddCommGroup B]
  {M : Type*} [AddCommGroup M] [DistribMulAction Γ M]

/-- **A module isomorphic to the regular module has vanishing `H ¹`.** The hypothesis is an
additive isomorphism `e : M ≃+ (Γ → B)` carrying the action of `Γ` on `M` to right translation
of the argument. -/
theorem exists_dZero_eq_of_regular (e : M ≃+ (Γ → B))
    (he : ∀ (γ : Γ) (m : M) (t : Γ), e (γ • m) t = e m (t * γ))
    (c : Γ → M) (hc : IsCocycle₁ c) : ∃ x : M, dZero x = c := by
  have key : ∀ g₁ g₂ t : Γ, e (c (g₁ * g₂)) t = e (c g₂) (t * g₁) + e (c g₁) t :=
    fun g₁ g₂ t ↦ by simpa only [map_add, Pi.add_apply, he] using congrArg (e · t) (hc g₁ g₂)
  refine ⟨e.symm fun s ↦ e (c s) 1, funext fun g ↦ e.injective (funext fun t ↦ ?_)⟩
  rw [dZero_apply, map_sub, Pi.sub_apply, he]
  simp only [AddEquiv.apply_symm_apply]
  rw [key t g 1, one_mul, add_sub_cancel_right]

/-- **A module isomorphic to the regular module has vanishing `H ²`.** The hypothesis is an
additive isomorphism `e : M ≃+ (Γ → B)` carrying the action of `Γ` on `M` to right translation
of the argument. -/
theorem exists_dOne_eq_of_regular (e : M ≃+ (Γ → B))
    (he : ∀ (γ : Γ) (m : M) (t : Γ), e (γ • m) t = e m (t * γ))
    (F : Γ × Γ → M) (hF : IsCocycle₂ F) : ∃ x : Γ → M, dOne x = F := by
  have key : ∀ g₁ g₂ g₃ t : Γ, e (F (g₁ * g₂, g₃)) t + e (F (g₁, g₂)) t
      = e (F (g₂, g₃)) (t * g₁) + e (F (g₁, g₂ * g₃)) t := fun g₁ g₂ g₃ t ↦ by
    simpa only [map_add, Pi.add_apply, he] using congrArg (e · t) (hF g₁ g₂ g₃)
  refine ⟨fun γ ↦ e.symm fun s ↦ e (F (s, γ)) 1,
    funext fun ⟨γ₁, γ₂⟩ ↦ e.injective (funext fun t ↦ ?_)⟩
  rw [dOne_apply, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he]
  simp only [AddEquiv.apply_symm_apply]
  rw [sub_add_eq_add_sub, key t γ₁ γ₂ 1, one_mul, add_sub_cancel_right]

end Regular

/-! ### The normal basis isomorphism -/

section NormalBasis

variable (L L' : Type*) [Field L] [Field L'] [Algebra L L']
  [FiniteDimensional L L'] [IsGalois L L']

/-- **The normal basis theorem as an additive isomorphism onto the regular module.** The
coordinates of `x : L'` in `IsGalois.normalBasis L L'`, read along the index `t⁻¹`. -/
def normalBasisAddEquiv : L' ≃+ (Gal(L'/L) → L) :=
  ((IsGalois.normalBasis L L').repr.trans
    ((Finsupp.linearEquivFunOnFinite L L Gal(L'/L)).trans
      (LinearEquiv.funCongrLeft L L (Equiv.inv Gal(L'/L))))).toAddEquiv

/-- The value of `normalBasisAddEquiv L L' x` at `t` is the coordinate of `x` at `t⁻¹` in the
normal basis. -/
@[simp] lemma normalBasisAddEquiv_apply (x : L') (t : Gal(L'/L)) :
    normalBasisAddEquiv L L' x t = (IsGalois.normalBasis L L').repr x t⁻¹ :=
  rfl

variable {L L'}

/-- The coordinate of `σ • x` at `f` in the normal basis is the coordinate of `x` at
`σ⁻¹ * f`. -/
theorem normalBasis_repr_smul (σ : Gal(L'/L)) (x : L') (f : Gal(L'/L)) :
    (IsGalois.normalBasis L L').repr (σ • x) f
      = (IsGalois.normalBasis L L').repr x (σ⁻¹ * f) := by
  classical
  have hmap : ∀ i : Gal(L'/L), σ (IsGalois.normalBasis L L' i)
      = IsGalois.normalBasis L L' (σ * i) := fun i ↦ by
    rw [IsGalois.normalBasis_apply i, IsGalois.normalBasis_apply (σ * i), AlgEquiv.mul_apply]
  have key : (Finsupp.lapply f).comp
        (((IsGalois.normalBasis L L').repr : L' →ₗ[L] (Gal(L'/L) →₀ L)).comp
          (σ.toLinearEquiv : L' →ₗ[L] L'))
      = (Finsupp.lapply (σ⁻¹ * f)).comp
          ((IsGalois.normalBasis L L').repr : L' →ₗ[L] (Gal(L'/L) →₀ L)) :=
    (IsGalois.normalBasis L L').ext fun i ↦ by
      simp [hmap, Finsupp.single_apply, eq_inv_mul_iff_mul_eq]
  exact LinearMap.congr_fun key x

/-- **The additive group of a finite Galois extension is the regular module.** Under the normal
basis isomorphism the Galois action becomes right translation of the argument. -/
theorem normalBasisAddEquiv_smul (σ : Gal(L'/L)) (x : L') (t : Gal(L'/L)) :
    normalBasisAddEquiv L L' (σ • x) t = normalBasisAddEquiv L L' x (t * σ) := by
  rw [normalBasisAddEquiv_apply, normalBasisAddEquiv_apply, normalBasis_repr_smul, mul_inv_rev]

end NormalBasis

/-! ### Additive Hilbert 90 and its degree-two companion -/

section FiniteGalois

/-- **Additive Hilbert 90.** Every `1`-cocycle of the Galois group of a finite Galois extension
with values in the additive group of the extension is a coboundary, i.e.
`H ¹(Gal(L'/L), L') = 0` for the additive group of `L'`. -/
theorem exists_dZero_eq_finiteGalois (L L' : Type*) [Field L] [Field L'] [Algebra L L']
    [FiniteDimensional L L'] [IsGalois L L'] (c : Gal(L'/L) → L') (hc : IsCocycle₁ c) :
    ∃ x : L', dZero x = c :=
  exists_dZero_eq_of_regular (normalBasisAddEquiv L L') normalBasisAddEquiv_smul c hc

/-- **The degree-two companion of additive Hilbert 90.** Every `2`-cocycle of the Galois group of
a finite Galois extension with values in the additive group of the extension is a coboundary,
i.e. `H ²(Gal(L'/L), L') = 0` for the additive group of `L'`. -/
theorem exists_dOne_eq_finiteGalois (L L' : Type*) [Field L] [Field L'] [Algebra L L']
    [FiniteDimensional L L'] [IsGalois L L'] (F : Gal(L'/L) × Gal(L'/L) → L')
    (hF : IsCocycle₂ F) : ∃ x : Gal(L'/L) → L', dOne x = F :=
  exists_dOne_eq_of_regular (normalBasisAddEquiv L L') normalBasisAddEquiv_smul F hF

end FiniteGalois

end Stacks.GroupCohomology

end
