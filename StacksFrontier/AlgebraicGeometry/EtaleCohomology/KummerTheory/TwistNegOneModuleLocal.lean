module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModuleLocallyConstant

/-!
# The Tate twist `𝓗om(μ_N, G)` over an étale scheme carrying a primitive `N`-th root of unity

Let `W` be an étale `X`-scheme with a ring map `κ : k → Γ(W, 𝒪)` from a field `k` and a primitive
`N`-th root of unity `ζ ∈ k`. Then `μ_N|_W` is the constant sheaf `ℤ/N` on the generator `ζ`
(`Stacks.Kummer.sliceRootSheafIso`). So a section of `G(-1) = 𝓗om(μ_N, G)` over `W`, which is a
morphism `μ_N|_W ⟶ G|_W`, is determined by its value at `ζ`, and any value can occur. The
evaluation map `G(-1)(W) → G(W)` at `ζ` is a bijection
(`Stacks.Kummer.bijective_twistNegOneModuleEvalRoot`).

## Main definitions

* `Stacks.Kummer.twistNegOneModuleEvalRoot`: evaluation of a section of `𝓗om(μ_N, G)` at `ζ`.

## Main results

* `Stacks.Kummer.bijective_twistNegOneModuleEvalRoot`: it is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.Kummer

variable {X : Scheme.{u}} (W : X.Etale) {k : Type u} [Field k] (κ : k →+* Γ(W.left, ⊤))
  {N : ℕ} [NeZero N] {ζ : k} (hζ : IsPrimitiveRoot ζ N)
  (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod N)))

/-- **Evaluation at `ζ`**: a section of `𝓗om(μ_N, G)` over `W`, a morphism `μ_N|_W ⟶ G|_W`, read
at the root of unity `ζ`, a section of `μ_N` over `W`. -/
def twistNegOneModuleEvalRoot :
    ToType ((twistNegOneModule.{u, v} X N G).obj.obj (op W)) →ₗ[ZMod N]
      ToType (G.obj.obj (op W)) where
  toFun α := α.hom.app (op (Over.mk (𝟙 W))) (sliceRootSection.{u, v} W κ hζ (Over.mk (𝟙 W)) 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation at `ζ` is the component at `𝟙 W` applied to the section `ζ`. -/
theorem twistNegOneModuleEvalRoot_apply
    (α : ToType ((twistNegOneModule.{u, v} X N G).obj.obj (op W))) :
    twistNegOneModuleEvalRoot W κ hζ G α =
      α.hom.app (op (Over.mk (𝟙 W))) (sliceRootSection.{u, v} W κ hζ (Over.mk (𝟙 W)) 1) :=
  rfl

/-- **Evaluation at `ζ` is bijective**: a morphism `μ_N|_W ⟶ G|_W` is determined by its value at
`ζ`, and any value occurs. -/
theorem bijective_twistNegOneModuleEvalRoot :
    Function.Bijective (twistNegOneModuleEvalRoot W κ hζ G) := by
  have := Stacks.ConstantSheaf.hasSheafify_over_moduleCat_of_univLE.{u + 1, u, 0, max (u + 1) v}
    X.smallEtaleTopology (ZMod N) W
  let A := ModuleCat.{max (u + 1) v} (ZMod N)
  let M : A := ModuleCat.of (ZMod N) (ULift.{max (u + 1) v} (ZMod N))
  let S := (X.smallEtaleTopology.overPullback A W).obj G
  let c := sliceRootSheafIso.{u, v} W κ hζ
  let e1 : ((X.smallEtaleTopology.overPullback A W).obj (rootsOfUnityModule.{u, v} X N) ⟶ S) ≃
      ((constantSheaf (X.smallEtaleTopology.over W) A).obj M ⟶ S) :=
    c.symm.homCongr (Iso.refl S)
  let e2 := (CategoryTheory.constantSheafAdj (X.smallEtaleTopology.over W) A
    Over.mkIdTerminal).homEquiv M S
  let e3 : (M ⟶ S.obj.obj (op (Over.mk (𝟙 W)))) ≃ ToType (G.obj.obj (op W)) :=
    { toFun := fun f => f.hom ⟨1⟩
      invFun := fun s => ModuleCat.ofHom
        ((LinearMap.toSpanSingleton (ZMod N) _ s).comp ULift.moduleEquiv.toLinearMap)
      left_inv := fun f => ModuleCat.hom_ext <| LinearMap.ext fun ⟨a⟩ => by
        change a • f.hom ⟨1⟩ = f.hom ⟨a⟩
        rw [← map_smul]
        exact congrArg f.hom (ULift.ext (mul_one a))
      right_inv := fun s => one_smul _ s }
  have h' : ∀ (t : ToType ((sliceConstantPresheaf W N).obj (op (Over.mk (𝟙 W))))),
      (sliceRootSheafHom.{u, v} W κ hζ).hom.app (op (Over.mk (𝟙 W)))
        ((toSheafify (X.smallEtaleTopology.over W) (sliceConstantPresheaf W N)).app
          (op (Over.mk (𝟙 W))) t) =
        (sliceRootPresheafHom.{u, v} W κ hζ).app (op (Over.mk (𝟙 W))) t :=
    fun t => ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_sliceRootSheafHom.{u, v} W κ hζ) (op (Over.mk (𝟙 W)))) t
  have he2 : ∀ φ, e2 φ = (toSheafify (X.smallEtaleTopology.over W) (sliceConstantPresheaf W N)).app
      (op (Over.mk (𝟙 W))) ≫ φ.hom.app (op (Over.mk (𝟙 W))) := fun φ =>
    Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply (X.smallEtaleTopology.over W) A
      Over.mkIdTerminal M S φ
  have key : ∀ α, twistNegOneModuleEvalRoot W κ hζ G α = e3 (e2 (e1 α)) := fun α => by
    change α.hom.app _ ((sliceRootPresheafHom.{u, v} W κ hζ).app (op (Over.mk (𝟙 W))) ⟨1⟩) = _
    rw [← h', he2]
    rfl
  rw [show ⇑(twistNegOneModuleEvalRoot W κ hζ G) = ⇑(e1.trans (e2.trans e3)) from funext key]
  exact Equiv.bijective _

end Stacks.Kummer

end
