module

public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.PullbackComp
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Transfers of tensor powers along `pullHom`

For morphisms `a b : T ⟶ X` of schemes and an invertible `𝒪_X`-module `M`, an isomorphism
`κ : a^* M ≅ b^* M` has a transfer `a^* (M ^⊗ n) ≅ b^* (M ^⊗ n)` to the tensor powers
(`AlgebraicGeometry.Scheme.Modules.tensorPowerTransfer`). This file reads the restriction
`pullHom` of the pseudofunctor of sheaves of modules on the transfer: restricting the transfer of
`κ` along `g` is the transfer of the restriction of `κ`. As a consequence the transfer of a
`κ` satisfying the cocycle condition of a descent datum, written with `pullHom`, satisfies it
too.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullHomIso`: the restriction of an isomorphism `κ` along
  `g`, as an isomorphism, whose underlying morphism is `pullHom κ.hom g`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullHom_tensorPowerTransfer`: `pullHom` of a transfer is the
  transfer of `pullHomIso`.
* `AlgebraicGeometry.Scheme.Modules.pullHom_tensorPowerTransfer_cocycle`: the transfer of an
  isomorphism satisfying the cocycle condition satisfies the cocycle condition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Invertible
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat (pullHom)
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X T T' : Scheme.{u}} {M : X.Modules}

/-- **The restriction of an isomorphism of pullbacks along a morphism, as an isomorphism.** For
`κ : a^* M ≅ b^* M` and `g : T' ⟶ T` with `g ≫ a = ga` and `g ≫ b = gb`, the isomorphism
`ga^* M ≅ gb^* M` obtained by pulling `κ` back along `g`; its underlying morphism is
`pullHom κ.hom g ga gb` (`AlgebraicGeometry.Scheme.Modules.pullHomIso_hom`). -/
def pullHomIso {a b : T ⟶ X} (κ : (pullback a).obj M ≅ (pullback b).obj M) (g : T' ⟶ T)
    (ga gb : T' ⟶ X) (ha : g ≫ a = ga) (hb : g ≫ b = gb) :
    (pullback ga).obj M ≅ (pullback gb).obj M := by
  subst ha hb
  exact (pullbackComp g a).symm.app M ≪≫ (pullback g).mapIso κ ≪≫ (pullbackComp g b).app M

/-- The underlying morphism of `pullHomIso κ g ga gb ha hb` is `pullHom κ.hom g ga gb ha hb`. -/
theorem pullHomIso_hom {a b : T ⟶ X} (κ : (pullback a).obj M ≅ (pullback b).obj M)
    (g : T' ⟶ T) (ga gb : T' ⟶ X) (ha : g ≫ a = ga) (hb : g ≫ b = gb) :
    (pullHomIso κ g ga gb ha hb).hom =
      pullHom (F := modulePullbackPseudofunctor) κ.hom g ga gb ha hb := by
  subst ha hb
  rfl

variable [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
  (structureSheafRing X.toRingedSpace).property M]

/-- **`pullHom` of a transfer is the transfer of the restriction.** -/
theorem pullHom_tensorPowerTransfer {a b : T ⟶ X}
    (κ : (pullback a).obj M ≅ (pullback b).obj M) (g : T' ⟶ T) (ga gb : T' ⟶ X)
    (ha : g ≫ a = ga) (hb : g ≫ b = gb) (n : ℕ) :
    pullHom (F := modulePullbackPseudofunctor) (tensorPowerTransfer a b M κ n).hom g ga gb ha hb =
      (tensorPowerTransfer ga gb M (pullHomIso κ g ga gb ha hb) n).hom := by
  subst ha hb
  exact tensorPowerTransfer_pullback a b M g κ n

/-- **The transfer of a cocycle is a cocycle.** If `κ : a^* M ≅ b^* M` satisfies the cocycle
condition along `σ₁₂ σ₂₃ σ₁₃ : T₃ ⟶ T`, written with `pullHom`, then so does its transfer to
every tensor power. -/
theorem pullHom_tensorPowerTransfer_cocycle {a b : T ⟶ X}
    (κ : (pullback a).obj M ≅ (pullback b).obj M) {T₃ : Scheme.{u}}
    (σ₁₂ σ₂₃ σ₁₃ : T₃ ⟶ T) (t₁ t₂ t₃ : T₃ ⟶ X) (h₁₂₁ : σ₁₂ ≫ a = t₁) (h₁₂₂ : σ₁₂ ≫ b = t₂)
    (h₂₃₁ : σ₂₃ ≫ a = t₂) (h₂₃₂ : σ₂₃ ≫ b = t₃) (h₁₃₁ : σ₁₃ ≫ a = t₁) (h₁₃₂ : σ₁₃ ≫ b = t₃)
    (hcoc : pullHom (F := modulePullbackPseudofunctor) κ.hom σ₁₂ t₁ t₂ h₁₂₁ h₁₂₂ ≫
        pullHom (F := modulePullbackPseudofunctor) κ.hom σ₂₃ t₂ t₃ h₂₃₁ h₂₃₂ =
      pullHom (F := modulePullbackPseudofunctor) κ.hom σ₁₃ t₁ t₃ h₁₃₁ h₁₃₂) (n : ℕ) :
    pullHom (F := modulePullbackPseudofunctor) (tensorPowerTransfer a b M κ n).hom
        σ₁₂ t₁ t₂ h₁₂₁ h₁₂₂ ≫
      pullHom (F := modulePullbackPseudofunctor) (tensorPowerTransfer a b M κ n).hom
        σ₂₃ t₂ t₃ h₂₃₁ h₂₃₂ =
    pullHom (F := modulePullbackPseudofunctor) (tensorPowerTransfer a b M κ n).hom
      σ₁₃ t₁ t₃ h₁₃₁ h₁₃₂ := by
  have h : pullHomIso κ σ₁₂ t₁ t₂ h₁₂₁ h₁₂₂ ≪≫ pullHomIso κ σ₂₃ t₂ t₃ h₂₃₁ h₂₃₂ =
      pullHomIso κ σ₁₃ t₁ t₃ h₁₃₁ h₁₃₂ :=
    Iso.ext (by rw [Iso.trans_hom, pullHomIso_hom, pullHomIso_hom, pullHomIso_hom]; exact hcoc)
  rw [pullHom_tensorPowerTransfer, pullHom_tensorPowerTransfer, pullHom_tensorPowerTransfer, ← h,
    ← tensorPowerTransfer_trans]
  rfl

end AlgebraicGeometry.Scheme.Modules

end
