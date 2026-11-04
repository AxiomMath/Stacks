module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Data
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.ProjectiveBundleAxiomDegreewise

/-!
# The class `c₁^{Hodge}(𝒪_P(1))` in the coordinates of axiom (A3)

Axiom (A3) of Weil cohomology theories is reduced in
`Stacks.WeilDeRham.projectiveBundleAxiom_of_degreewise` to the bijectivity, in every degree, of
`(a_i) ↦ ∑ ξ^i φ(a_i)` with `ξ = κ(c₁^H(𝒪_P(1)))`, where `κ` reads the twist `H^*(P)(1)` through
the chosen coordinate `Stacks.WeilCohomology.FirstChernClassData.coord` of the Tate line. For
Hodge cohomology the Tate line is `k` itself and `c₁^{Hodge}` is read through the identity
coordinate `tateTwistCoordinates (LinearEquiv.refl k k)`; the two coordinates differ by a nonzero
scalar `λ`, so `ξ = λ • ξ₀` with `ξ₀ = c₁^{Hodge}(𝒪_P(1)) ∈ H^1(P, Ω^1)`. Scaling `ξ` by a unit
does not change the bijectivity of the projective bundle map, since
`∑ (λ ξ₀)^i φ(a_i) = ∑ ξ₀^i φ(λ^i a_i)`.

## Main results

* `Stacks.HodgeWeil.bijective_degreewiseMap_smul_iff`: bijectivity of the degreewise projective
  bundle map is unchanged under scaling `ξ` by a unit.
* `Stacks.HodgeWeil.hodge_κ_one`: `κ = λ • tateTwistCoordinates (LinearEquiv.refl k k)` in
  twist `1`, for a nonzero `λ`.

## References

* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
-/

@[expose] public noncomputable section

open DirectSum

universe u

namespace Stacks.HodgeWeil

section Graded

variable {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
  {𝒜 : ℤ → Submodule F A} [_root_.GradedAlgebra 𝒜] {ℬ : ℤ → Submodule F B}
  [_root_.GradedAlgebra ℬ]

/-- The degreewise projective bundle map with `u • ξ` is that with `ξ` precomposed with
`(a_i) ↦ (u^i • a_i)`. -/
theorem degreewiseMap_smul {φ : A →ₐ[F] B} (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n) {ξ : B}
    (hξ : ξ ∈ ℬ 2) (u : F) (huξ : u • ξ ∈ ℬ 2) (r : ℕ) (n : ℤ)
    (a : ∀ i : Fin r, 𝒜 (n - 2 * ((i : ℕ) : ℤ))) :
    Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ huξ r n a =
      Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ hξ r n (fun i => u ^ (i : ℕ) • a i) := by
  apply Subtype.ext
  rw [Stacks.WeilDeRham.coe_degreewiseMap, Stacks.WeilDeRham.coe_degreewiseMap]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_pow, smul_mul_assoc, Submodule.coe_smul, map_smul, mul_smul_comm]

/-- **Scaling `ξ` by a unit does not change the bijectivity of the degreewise projective bundle
map**: `(a_i) ↦ (u^i • a_i)` is a bijection of `∏_i A^{n - 2i}`. -/
theorem bijective_degreewiseMap_smul_iff {φ : A →ₐ[F] B} (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n)
    {ξ : B} (hξ : ξ ∈ ℬ 2) (u : F) (hu : u ≠ 0) (huξ : u • ξ ∈ ℬ 2) (r : ℕ) (n : ℤ) :
    Function.Bijective (Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ huξ r n) ↔
      Function.Bijective (Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ hξ r n) := by
  have h : Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ huξ r n =
      Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ hξ r n ∘
        Equiv.piCongrRight fun i : Fin r => MulAction.toPerm (Units.mk0 u hu ^ (i : ℕ)) :=
    funext fun a => degreewiseMap_smul hφ hξ u huξ r n a
  rw [h]
  exact Function.Bijective.of_comp_iff _ (Equiv.bijective _)

end Graded

section Coordinate

open Stacks.WeilCohomology

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]

/-- Two coordinates on a line differ by the scalar `φ(ψ⁻¹ 1)`. -/
theorem linearEquiv_apply_eq_mul (φ ψ : M ≃ₗ[F] F) (x : M) : φ x = ψ x * φ (ψ.symm 1) := by
  have hx : x = ψ x • ψ.symm 1 := by
    apply ψ.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  conv_lhs => rw [hx]
  rw [map_smul, smul_eq_mul]

variable (k : Type u) [Field k]

/-- The scalar by which the coordinate of the Tate line of Hodge cohomology differs from the
identity coordinate, in twist `1`. -/
def hodgeTateScalar : k :=
  tateLineCoordinates (hodgeFirstChernClassData k).coord 1
    ((tateLineCoordinates (LinearEquiv.refl k k) 1).symm 1)

/-- The scalar `hodgeTateScalar k` is nonzero. -/
theorem hodgeTateScalar_ne_zero : hodgeTateScalar k ≠ 0 :=
  (tateLineCoordinates (hodgeFirstChernClassData k).coord 1).map_ne_zero_iff.2 <|
    (tateLineCoordinates (LinearEquiv.refl k k) 1).symm.map_ne_zero_iff.2 one_ne_zero

variable {k}

/-- **The coordinate of axiom (A3) is a nonzero multiple of the identity coordinate** on the
twist `H^*_{Hodge}(X/k)(1)`. -/
theorem hodge_κ_one (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : tateTwist k k (hodgeAlgebraOf X) 1) :
    (hodgeFirstChernClassData k).κ X 1 x =
      hodgeTateScalar k • tateTwistCoordinates (LinearEquiv.refl k k) 1 x := by
  induction x using TensorProduct.induction_on with
  | zero =>
    exact ((hodgeFirstChernClassData k).κ X 1).map_zero.trans
      (((congrArg (hodgeTateScalar k • ·)
        (tateTwistCoordinates (V := hodgeAlgebraOf X) (LinearEquiv.refl k k) 1).map_zero).trans
          (smul_zero _)).symm)
  | tmul v l =>
    show tateTwistCoordinates (hodgeFirstChernClassData k).coord 1 (v ⊗ₜ l) =
      hodgeTateScalar k • tateTwistCoordinates (LinearEquiv.refl k k) 1 (v ⊗ₜ l)
    refine (tateTwistCoordinates_tmul _ _ v l).trans ?_
    refine Eq.trans ?_ (congrArg (hodgeTateScalar k • ·) (tateTwistCoordinates_tmul _ _ v l)).symm
    refine Eq.trans ?_ (smul_smul _ _ v).symm
    exact congrArg (· • v) ((linearEquiv_apply_eq_mul
      (tateLineCoordinates (hodgeFirstChernClassData k).coord 1)
      (tateLineCoordinates (LinearEquiv.refl k k) 1) l).trans (mul_comm _ _))
  | add x y hx hy =>
    exact (((hodgeFirstChernClassData k).κ X 1).map_add x y).trans
      ((congrArg₂ (· + ·) hx hy).trans (((congrArg (hodgeTateScalar k • ·)
        ((tateTwistCoordinates (V := hodgeAlgebraOf X) (LinearEquiv.refl k k) 1).map_add x y)).trans
          (smul_add _ _ _)).symm))

end Coordinate

end Stacks.HodgeWeil

end
