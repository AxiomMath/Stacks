module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Functor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassData

/-!
# The comparison data of Tag 0FVT

Data (D0), (D1), (D2') `𝔇` for `(k, F)` and `𝔇'` for `(k', F')`, an isomorphism
`F(1) ⊗_F F' ≅ F'(1)`, and functorial isomorphisms of graded `F'`-algebras
`H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})` compatible with the first Chern classes.

## Main definitions

* `Stacks.WeilCohomology.twistOneBaseChange`: the `F'`-linear map `F' ⊗_F V(1) → V'(1)` induced by
  `ψ : F' ⊗_F V → V'` and `F' ⊗_F F(1) ≅ F'(1)`.
* `Stacks.WeilCohomology.FieldExtensionComparison`: the comparison data of Tag 0FVT between `𝔇`
  and `𝔇'`.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

section TwistOne

variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
  {L : Type*} [AddCommGroup L] [Module F L] {L' : Type*} [AddCommGroup L'] [Module F' L']
  {V : Type*} [AddCommGroup V] [Module F V] {V' : Type*} [AddCommGroup V'] [Module F' V']

/-- The comparison `F' ⊗_F F(1)^{⊗ 1} ≅ F'(1)^{⊗ 1}` of first tensor powers induced by
`F' ⊗_F F(1) ≅ F'(1)`. -/
def tensorPowerOneBaseChange (τ : F' ⊗[F] L ≃ₗ[F'] L') :
    F' ⊗[F] TensorPower F 1 L ≃ₗ[F'] TensorPower F' 1 L' :=
  ((LinearEquiv.baseChange F F' _ _ (PiTensorProduct.subsingletonEquiv (R := F)
      (s := fun _ : Fin 1 => L) 0)).trans τ).trans
    (PiTensorProduct.subsingletonEquiv (R := F') (s := fun _ : Fin 1 => L') 0).symm

/-- **The right vertical arrow `H^2(X)(1) → (H')^2(X_{k'})(1)` of Tag 0FVT**, extended
`F'`-linearly: `F' ⊗_F V(1) → V'(1)`, `a ⊗ (v ⊗ t) ↦ ψ(a ⊗ v) ⊗ τ(1 ⊗ t)`, for an `F'`-linear map
`ψ : F' ⊗_F V → V'` and `τ : F' ⊗_F F(1) ≅ F'(1)`. -/
def twistOneBaseChange (τ : F' ⊗[F] L ≃ₗ[F'] L') (ψ : F' ⊗[F] V →ₗ[F'] V') :
    F' ⊗[F] tateTwist F L V 1 →ₗ[F'] tateTwist F' L' V' 1 :=
  (TensorProduct.map ψ (tensorPowerOneBaseChange τ).toLinearMap).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange F F' V (TensorPower F 1 L)).toLinearMap

end TwistOne

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']

/-- **The comparison data of Tag 0FVT.** For data (D0), (D1), (D2') `𝔇` for `(k, F)` and `𝔇'` for
`(k', F')`: an isomorphism `F(1) ⊗_F F' ≅ F'(1)`, isomorphisms of graded `F'`-algebras
`H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})`, functorial in the smooth projective scheme `X` over `k`, such
that the squares `Pic(X) → H^2(X)(1)`, `Pic(X_{k'}) → (H')^2(X_{k'})(1)` commute. -/
structure FieldExtensionComparison (𝔇 : FirstChernClassData k F)
    (𝔇' : FirstChernClassData k' F') where
  /-- The isomorphism `F(1) ⊗_F F' ≅ F'(1)`. -/
  tateEquiv : F' ⊗[F] 𝔇.tate ≃ₗ[F'] 𝔇'.tate
  /-- The isomorphisms `H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})`, of `F'`-algebras. -/
  iso : ∀ X, F' ⊗[F] 𝔇.H X ≃ₐ[F'] 𝔇'.H ((baseChange k k').obj X)
  /-- They are graded. -/
  iso_grade : ∀ X (n : ℤ) (a : 𝔇.H X), a ∈ 𝔇.grade X n →
    iso X (1 ⊗ₜ a) ∈ 𝔇'.grade ((baseChange k k').obj X) n
  /-- They are functorial. -/
  iso_natural : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (a : 𝔇.H Y),
    iso X (1 ⊗ₜ 𝔇.pull f a) = 𝔇'.pull ((baseChange k k').map f) (iso Y (1 ⊗ₜ a))
  /-- The squares with the first Chern classes commute: for an invertible `𝒪_X`-module `ℒ`, the
  image of `c₁^H(ℒ)` is `c₁^{H'}` of the pullback of `ℒ` to `X_{k'}`. Every class of `Pic(X)` is
  the class of such an `ℒ`. -/
  c₁_comm : ∀ X (L : ((toScheme k).obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
      ((toScheme k).obj X).ringCatSheaf.2 L),
    twistOneBaseChange tateEquiv (iso X).toLinearMap (1 ⊗ₜ 𝔇.c₁ X (picardClassOf _ L hL)) =
      𝔇'.c₁ ((baseChange k k').obj X)
        (picardClassOf _ ((Scheme.Modules.pullback (baseChangeProj X)).obj L)
          (isInvertible_pullback_obj _ L hL))

end Stacks.WeilCohomology
