module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneModuleLocal

/-!
# The evaluation pairing `𝓗om(μ_N, G) ⊗ μ_N ⟶ G` on sections

A section of `𝓗om(μ_N, G)` over an étale `U ⟶ X` is a morphism `α : μ_N|_U ⟶ G|_U`, and a section
`s` of `μ_N` over `U` can be fed to it: `⟨α, s⟩ = α_U(s)`, its component at the terminal object
`𝟙 U` of the slice. This is bilinear and natural in `U`
(`Stacks.Kummer.twistNegOneModulePairing_naturality`).

## Main definitions

* `Stacks.Kummer.twistNegOneModulePairing`: the pairing on sections over `U`.

## Main results

* `Stacks.Kummer.twistNegOneModulePairing_naturality`: the pairing is natural in `U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.Kummer

variable (X : Scheme.{u}) (N : ℕ) [NeZero N]
  (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod N)))

/-- **The evaluation pairing on sections over `U`**: `⟨α, s⟩ = α_U(s)`. -/
def twistNegOneModulePairing (U : X.Etale) :
    ToType ((twistNegOneModule.{u, v} X N G).obj.obj (op U)) →ₗ[ZMod N]
      ToType ((rootsOfUnityModule.{u, v} X N).obj.obj (op U)) →ₗ[ZMod N]
        ToType (G.obj.obj (op U)) :=
  LinearMap.mk₂ (ZMod N) (fun α s => α.hom.app (op (Over.mk (𝟙 U))) s)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun α _ _ => map_add (α.hom.app (op (Over.mk (𝟙 U)))).hom _ _)
    (fun c α s => map_smul (α.hom.app (op (Over.mk (𝟙 U)))).hom c s)

/-- **The pairing is natural**: restricting a section of `𝓗om(μ_N, G)` and a section of `μ_N`
along `g : V ⟶ U` and pairing them restricts the pairing. -/
theorem twistNegOneModulePairing_naturality {U V : X.Etale} (g : V ⟶ U)
    (α : ToType ((twistNegOneModule.{u, v} X N G).obj.obj (op U)))
    (s : ToType ((rootsOfUnityModule.{u, v} X N).obj.obj (op U))) :
    twistNegOneModulePairing X N G V ((twistNegOneModule.{u, v} X N G).obj.map g.op α)
        ((rootsOfUnityModule.{u, v} X N).obj.map g.op s) =
      G.obj.map g.op (twistNegOneModulePairing X N G U α s) :=
  (ConcreteCategory.congr_hom (presheafHom_map_app (𝟙 V) g g (Category.id_comp _) α.hom) _).trans
    (ConcreteCategory.congr_hom (α.hom.naturality (Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 U)).op) s)

end Stacks.Kummer

end
