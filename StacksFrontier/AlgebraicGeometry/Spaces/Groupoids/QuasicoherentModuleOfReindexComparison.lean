module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModuleOfReindex

/-!
# Comparing a module on a groupoid built from a transition with a module on the base

Let `(U, R, s, t, c)` be a groupoid with `φ : U ⟶ X`, `t ≫ φ = s ≫ φ`, and let
`(ρ^*ℳ, τ^*α)` be the quasi-coherent module on the groupoid of
`AlgebraicGeometry.Space.quasicoherentModuleOfReindex`. A morphism of modules on the groupoid
from it to the module `(φ^*𝒩, can)` attached to an `𝒪_X`-module `𝒩` (Stacks 03M3) is a morphism
`ρ^*ℳ ⟶ φ^*𝒩` whose two inverse images to `R` intertwine `τ^*α` with the canonical
identification.

## Main results

* `AlgebraicGeometry.Space.reindexHomSpaceBase_comm`: a morphism of modules on the groupoid from
  `(ρ^*ℳ, τ^*α)` to `(φ^*𝒩, can)`, read on the underlying modules, intertwines the two
  transition morphisms.
* `AlgebraicGeometry.Space.modulePullbackReindex_eq_descentTransport_of_iso`: if the two modules
  on the groupoid are isomorphic, then `α` reindexed along `τ` is the descent datum of `𝒩` along
  `φ` transported to `ℳ`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Comparison

variable {A : AlgebraicSpaces B S hS} (Γ : GroupoidInAlgebraicSpaces B S hS A)
  {X Z V : AlgebraicSpaces B S hS} (φ : Γ.objects ⟶ X)
  (hφ : Γ.target ≫ φ = Γ.source ≫ φ) (N : Modules.{u, u} B S hS X.1 X.2)
  (hN : N.IsQuasicoherentOnSite) (ρ : Γ.objects ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2)
  (hM : M.IsQuasicoherentOnSite) {a b : V ⟶ Z}
  (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M)
  (τ : Γ.arrows ⟶ V) (ha : Γ.target ≫ ρ = τ ≫ a) (hb : τ ≫ b = Γ.source ≫ ρ)
  (hcoc : TransitionCocycle B S hS M α (firstArrow Γ ≫ τ) (secondArrow Γ ≫ τ) (Γ.comp ≫ τ))
  (hunit : TransitionUnit B S hS M α (identityArrow Γ ≫ τ))

/-- The transition of the module built from `α` is `transitionOfReindex`. -/
theorem quasicoherentModuleOfReindex_alpha :
    (quasicoherentModuleOfReindex Γ ρ M α τ ha hb hM hcoc hunit).alpha =
      transitionOfReindex Γ ρ M α τ ha hb :=
  rfl

/-- A morphism from the module built from a transition to the module attached to an
`𝒪_X`-module, read on the underlying modules. -/
def reindexHomSpaceBase
    (θ : quasicoherentModuleOfReindex Γ ρ M α τ ha hb hM hcoc hunit ⟶
      quasicoherentModuleOfSpaceBase B S hS Γ φ hφ N hN) :
    (modulePullback B S hS ρ).obj M ⟶ (modulePullback B S hS φ).obj N :=
  θ.hom

/-- A morphism of modules on the groupoid from the module built from `α` to the module attached to
`𝒩`, read on the underlying modules, intertwines the two transition morphisms. -/
theorem reindexHomSpaceBase_comm
    (θ : quasicoherentModuleOfReindex Γ ρ M α τ ha hb hM hcoc hunit ⟶
      quasicoherentModuleOfSpaceBase B S hS Γ φ hφ N hN) :
    transitionOfReindex Γ ρ M α τ ha hb ≫
        (modulePullback B S hS Γ.source).map
          (reindexHomSpaceBase Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit θ) =
      (modulePullback B S hS Γ.target).map
          (reindexHomSpaceBase Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit θ) ≫
        spaceBaseDescent B S hS Γ φ hφ N := by
  have h := θ.comm
  rwa [quasicoherentModuleOfReindex_alpha, quasicoherentModuleOfSpaceBase_alpha] at h

/-- A morphism from the module attached to an `𝒪_X`-module to the module built from a
transition, read on the underlying modules. -/
def spaceBaseHomReindex
    (θ : quasicoherentModuleOfSpaceBase B S hS Γ φ hφ N hN ⟶
      quasicoherentModuleOfReindex Γ ρ M α τ ha hb hM hcoc hunit) :
    (modulePullback B S hS φ).obj N ⟶ (modulePullback B S hS ρ).obj M :=
  θ.hom

/-- A morphism of modules on the groupoid from the module attached to `𝒩` to the module built from
`α`, read on the underlying modules, intertwines the two transition morphisms. -/
theorem spaceBaseHomReindex_comm
    (θ : quasicoherentModuleOfSpaceBase B S hS Γ φ hφ N hN ⟶
      quasicoherentModuleOfReindex Γ ρ M α τ ha hb hM hcoc hunit) :
    spaceBaseDescent B S hS Γ φ hφ N ≫
        (modulePullback B S hS Γ.source).map
          (spaceBaseHomReindex Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit θ) =
      (modulePullback B S hS Γ.target).map
          (spaceBaseHomReindex Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit θ) ≫
        transitionOfReindex Γ ρ M α τ ha hb := by
  have h := θ.comm
  rwa [quasicoherentModuleOfReindex_alpha, quasicoherentModuleOfSpaceBase_alpha] at h

/-- Solving a commuting square for its fourth side. -/
theorem eq_comp_of_comp_eq {C : Type*} [Category C] {X Y Z W : C} {i : X ⟶ Y} {i' : Y ⟶ X}
    (hi : i ≫ i' = 𝟙 X) {d : Y ⟶ Z} {c : Z ⟶ W} {T : X ⟶ W} (h : d ≫ c = i' ≫ T) :
    T = i ≫ d ≫ c := by
  rw [h, ← Category.assoc, hi, Category.id_comp]

/-- Flattening a conjugate of an unflattening. -/
theorem modulePullbackFlatten_map_comp_unflatten_comp_map {P Q : AlgebraicSpaces B S hS}
    {a b : P ⟶ Q} {ρ' : Q ⟶ Z} {φ' : Q ⟶ X} {M' : Modules.{u, u} B S hS Z.1 Z.2}
    {N' : Modules.{u, u} B S hS X.1 X.2}
    (ι : (modulePullback B S hS ρ').obj M' ≅ (modulePullback B S hS φ').obj N')
    (x : (modulePullback B S hS (a ≫ φ')).obj N' ⟶ (modulePullback B S hS (b ≫ φ')).obj N') :
    modulePullbackFlatten ρ' ((modulePullback B S hS a).map ι.hom ≫
        modulePullbackUnflatten φ' x ≫ (modulePullback B S hS b).map ι.inv) =
      modulePullbackReindexHom a ι.hom ≫ x ≫ modulePullbackReindexHom b ι.inv := by
  rw [modulePullbackReindexHom_def, modulePullbackReindexHom_def, modulePullbackUnflatten_eq]
  simp only [modulePullbackFlatten, Category.assoc]

/-- **The transition of a module on the groupoid built from `α`, compared with the module
attached to `𝒩` (Stacks 03M3)**: reindexed along `τ`, `α` is the descent datum of `𝒩` along `φ`,
transported through `ι : ρ^*ℳ ≅ φ^*𝒩`, for any morphism of modules on the groupoid whose
underlying morphism is `ι⁻¹`. -/
theorem modulePullbackReindex_eq_descentTransport_of_hom
    (θ : quasicoherentModuleOfSpaceBase B S hS Γ φ hφ N hN ⟶
      quasicoherentModuleOfReindex Γ ρ M α τ ha hb hM hcoc hunit)
    (ι : (modulePullback B S hS ρ).obj M ≅ (modulePullback B S hS φ).obj N)
    (hι : ι.inv = spaceBaseHomReindex Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit θ)
    (hb' : Γ.source ≫ ρ = τ ≫ b) :
    modulePullbackReindex τ α = descentTransport ρ φ ι ha hb' hφ := by
  have hT := eq_comp_of_comp_eq (ι.map_hom_inv_id (F := modulePullback B S hS Γ.target))
    (hι ▸ spaceBaseHomReindex_comm Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit θ)
  have hF := (modulePullbackFlatten_transitionOfReindex Γ ρ M α τ ha hb).symm.trans
    ((congrArg (fun z => modulePullbackFlatten ρ z) hT).trans
      ((modulePullbackFlatten_map_comp_unflatten_comp_map ι
        (pullbackTransport N hφ)).trans (descentTransportCore_eq ι hφ).symm))
  refine (Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback.sandwich_cancel
    (pullbackTransport_comp_self M ha.symm ha)
    (pullbackTransport_comp_self M hb hb') _).symm.trans ?_
  exact (congrArg (fun z => pullbackTransport M ha.symm ≫ z ≫ pullbackTransport M hb') hF).trans
    (descentTransport_eq ι ha hb' hφ).symm

/-- An isomorphism of modules on the groupoid between the module attached to `𝒩` and the module
built from `α`, read on the underlying modules as `ρ^*ℳ ≅ φ^*𝒩`. -/
def reindexSpaceBaseIso
    (e : quasicoherentModuleOfSpaceBase B S hS Γ φ hφ N hN ≅
      quasicoherentModuleOfReindex Γ ρ M α τ ha hb hM hcoc hunit) :
    (modulePullback B S hS ρ).obj M ≅ (modulePullback B S hS φ).obj N where
  hom := reindexHomSpaceBase Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit e.inv
  inv := spaceBaseHomReindex Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit e.hom
  hom_inv_id := congrArg QuasicoherentModule.Hom.hom e.inv_hom_id
  inv_hom_id := congrArg QuasicoherentModule.Hom.hom e.hom_inv_id

/-- The inverse of `reindexSpaceBaseIso e` is the underlying morphism of `e.hom`. -/
theorem reindexSpaceBaseIso_inv
    (e : quasicoherentModuleOfSpaceBase B S hS Γ φ hφ N hN ≅
      quasicoherentModuleOfReindex Γ ρ M α τ ha hb hM hcoc hunit) :
    (reindexSpaceBaseIso Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit e).inv =
      spaceBaseHomReindex Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit e.hom :=
  rfl

/-- **The transition of a module on the groupoid built from `α`, isomorphic to the module
attached to `𝒩` (Stacks 03M3)**: reindexed along `τ`, `α` is the descent datum of `𝒩` along `φ`
transported to `ℳ`. -/
theorem modulePullbackReindex_eq_descentTransport_of_iso
    (e : quasicoherentModuleOfSpaceBase B S hS Γ φ hφ N hN ≅
      quasicoherentModuleOfReindex Γ ρ M α τ ha hb hM hcoc hunit)
    (hb' : Γ.source ≫ ρ = τ ≫ b) :
    modulePullbackReindex τ α = descentTransport ρ φ
      (reindexSpaceBaseIso Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit e) ha hb' hφ :=
  modulePullbackReindex_eq_descentTransport_of_hom Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit
    e.hom _ (reindexSpaceBaseIso_inv Γ φ hφ N hN ρ M hM α τ ha hb hcoc hunit e) hb'

end Comparison

end AlgebraicGeometry.Space

end
