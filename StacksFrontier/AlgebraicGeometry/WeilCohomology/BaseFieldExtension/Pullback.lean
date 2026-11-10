module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Coproduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SourceChernSetup

/-!
# Axiom (A2) descends along a field extension

Given a comparison `Φ` between first Chern class data `𝔇` over `k` with coefficients in `F` and
`𝔇'` over `k'` with coefficients in `F'`, compatibility of `c₁^{H'}` with pullbacks implies
compatibility of `c₁^H` with pullbacks.

## Main definitions

* `FieldExtensionComparison.twistOne`: The comparison map `H^*(X)(1) → (H')^*(X_{k'})(1)`.
* `FieldExtensionComparison.pullbackBaseChangeIso`: The isomorphism identifying the two ways of
  pulling a module on `Y` back to `X_{k'}`.

## Main results

* `FieldExtensionComparison.twistOne_injective`: The comparison of first twists is injective.
* `FieldExtensionComparison.twistOne_pullTw`: The comparison of first twists commutes with
  pullbacks.
* `FieldExtensionComparison.pullbackAxiom`: Axiom (A2) for `𝔇'` implies axiom (A2) for `𝔇`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Function

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

section TwistOne

variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
  {L : Type*} [AddCommGroup L] [Module F L] {L' : Type*} [AddCommGroup L'] [Module F' L']
  {V : Type*} [AddCommGroup V] [Module F V] {V' : Type*} [AddCommGroup V'] [Module F' V']

/-- The value of `twistOneBaseChange τ ψ` on a pure tensor `a ⊗ (v ⊗ t)`. -/
@[simp]
theorem twistOneBaseChange_tmul (τ : F' ⊗[F] L ≃ₗ[F'] L') (ψ : F' ⊗[F] V →ₗ[F'] V') (a : F')
    (v : V) (t : tateLine F L 1) :
    twistOneBaseChange τ ψ (a ⊗ₜ (v ⊗ₜ t)) =
      ψ (a ⊗ₜ v) ⊗ₜ tensorPowerOneBaseChange τ (1 ⊗ₜ[F] (t : TensorPower F 1 L)) := rfl

/-- The comparison of first twists is injective on `V(1)` when `ψ` is an isomorphism. -/
theorem injective_twistOneBaseChange (τ : F' ⊗[F] L ≃ₗ[F'] L') (ψ : F' ⊗[F] V ≃ₗ[F'] V') :
    Injective fun x : tateTwist F L V 1 => twistOneBaseChange τ ψ.toLinearMap (1 ⊗ₜ x) := by
  have : Injective (twistOneBaseChange τ ψ.toLinearMap) :=
    ((TensorProduct.congr ψ (tensorPowerOneBaseChange τ)).injective.comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange F F' V (TensorPower F 1 L)).injective :)
  exact this.comp (injective_one_tmul (F := F) (V := tateTwist F L V 1) F')

end TwistOne

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

/-- The comparison of first twists of `H^*(X)`, as a map `H^*(X)(1) → (H')^*(X_{k'})(1)`. -/
def twistOne (X : (SmoothProjectiveScheme k).FullSubcategory) (x : tateTwist F 𝔇.tate (𝔇.H X) 1) :
    tateTwist F' 𝔇'.tate (𝔇'.H ((baseChange k k').obj X)) 1 :=
  twistOneBaseChange Φ.tateEquiv (Φ.iso X).toLinearMap (1 ⊗ₜ x)

/-- The comparison of first twists `H^*(X)(1) → (H')^*(X_{k'})(1)` is injective. -/
theorem twistOne_injective (X : (SmoothProjectiveScheme k).FullSubcategory) :
    Injective (Φ.twistOne X) :=
  injective_twistOneBaseChange Φ.tateEquiv (Φ.iso X).toLinearEquiv

/-- The comparison of first twists commutes with pullbacks. -/
theorem twistOne_pullTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (x : tateTwist F 𝔇.tate (𝔇.H Y) 1) :
    Φ.twistOne X (𝔇.pullTw f 1 x) = 𝔇'.pullTw ((baseChange k k').map f) 1 (Φ.twistOne Y x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v t =>
    simp only [twistOne, FirstChernClassData.pullTw, tateTwistMap, TensorProduct.map_tmul,
      LinearMap.id_coe, id_eq, AlgHom.toLinearMap_apply]
    rw [twistOneBaseChange_tmul, twistOneBaseChange_tmul, TensorProduct.map_tmul]
    simp only [AlgEquiv.toLinearMap_apply, Φ.iso_natural, AlgHom.toLinearMap_apply,
      LinearMap.id_coe, id_eq]
  | add x y hx hy =>
    simp only [twistOne, map_add, TensorProduct.tmul_add] at hx hy ⊢
    rw [hx, hy]

/-- Pulling back to `X_{k'}` commutes with pulling back along `f`, up to isomorphism. -/
def pullbackBaseChangeIso {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (L : ((toScheme k).obj Y).Modules) :
    (Scheme.Modules.pullback ((toScheme k').map ((baseChange k k').map f))).obj
        ((Scheme.Modules.pullback (baseChangeProj Y)).obj L) ≅
      (Scheme.Modules.pullback (baseChangeProj X)).obj
        ((Scheme.Modules.pullback ((toScheme k).map f)).obj L) :=
  (Scheme.Modules.pullbackComp ((toScheme k').map ((baseChange k k').map f))
      (baseChangeProj Y)).app L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeProj_naturality f)).app L ≪≫
      ((Scheme.Modules.pullbackComp (baseChangeProj X) ((toScheme k).map f)).app L).symm

include Φ in
/-- **Axiom (A2) descends**: if `c₁^{H'}` is compatible with pullbacks, so is `c₁^H`. -/
theorem pullbackAxiom (h : 𝔇'.PullbackAxiom) : 𝔇.PullbackAxiom := by
  intro X Y f L hL
  apply Φ.twistOne_injective X
  rw [Φ.twistOne_pullTw]
  change 𝔇'.pullTw _ 1 (twistOneBaseChange _ _ _) = twistOneBaseChange _ _ _
  rw [Φ.c₁_comm, Φ.c₁_comm, h]
  exact congrArg (𝔇'.c₁ _) (picardClassOf_eq_of_iso _ _ _ _ _ (pullbackBaseChangeIso f L))

end FieldExtensionComparison

end Stacks.WeilCohomology
