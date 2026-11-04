module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Hull
public import StacksFrontier.Topology.Sheaves.PresheafOfModules.StalkMap
public import StacksCore.Tactic.StacksAttribute

/-!
# The reflexive powers of a module and the system `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} → ⋯`

[Stacks, Tag 0EBN] attaches to an `𝒪_X`-module `ℱ` its *reflexive powers*

`ℱ^{[1]} = ℱ`,   `ℱ^{[n + 1]} = (ℱ ⊗_{𝒪_X} ℱ^{[n]})^{**}`,

and, to a global section `s ∈ Γ(X, ℱ)`, the `ℕ`-indexed system

`𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ℱ^{[3]} →ˢ ⋯`

whose transition maps are multiplication by `s`. This file builds both, together with the
stalk of the system at a point of `X`. The index `0` carries the first term `𝒪_X` of the system,
so `ℱ^{[1]} = ℱ` and the recursion is imposed from `n = 1` on.

## Main definitions

* `mulSectionHom`: the map `𝒢 ⟶ ℱ ⊗ 𝒢`, `a ↦ s ⊗ a`, attached to `s : 𝒪_X ⟶ ℱ`.
* `reflexivePower ℱ n`: the `n`-th term `ℱ^{[n]}` of the system, with `ℱ^{[0]} = 𝒪_X`.
* `reflexivePowerTransition ℱ s n`: the transition `ℱ^{[n]} ⟶ ℱ^{[n + 1]}`, multiplication
  by `s` followed by the canonical map to the reflexive hull.
* `reflexivePowerStalk`, `reflexivePowerStalkMap`, `reflexivePowerUnit`: the stalk `ℱ^{[n]}_x`
  as an `𝒪_{X, x}`-module, the stalk of the transition as an `𝒪_{X, x}`-linear map, and the
  germ of `1 ∈ Γ(X, 𝒪_X)` in `ℱ^{[0]}_x`.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules (reflexiveHull toDoubleDual)
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules.OnSpace (tensorObjTmul unitSection)

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

/-! ### Multiplication by a global section -/

/-- Multiplication by a global section: the map `𝒢 ⟶ ℱ ⊗ 𝒢` attached to a morphism
`σ : 𝒪_X ⟶ ℱ`, obtained by inserting the unit and whiskering. -/
noncomputable def mulSectionHom (Y : RingedSpace.{u, u})
    {F G : SheafOfModules.{u} (structureSheafRing Y)}
    (σ : 𝟙_ (SheafOfModules.{u} (structureSheafRing Y)) ⟶ F) :
    G ⟶ F ⊗ G :=
  (λ_ G).inv ≫ (σ ▷ G)

/-- `mulSectionHom` is multiplication by the section: on a local section `a` of `𝒢` it takes
the value `σ(1) ⊗ a`. -/
theorem mulSectionHom_app (Y : RingedSpace.{u, u})
    {F G : SheafOfModules.{u} (structureSheafRing Y)}
    (σ : 𝟙_ (SheafOfModules.{u} (structureSheafRing Y)) ⟶ F)
    (U : (Opens Y.carrier)ᵒᵖ) (a : G.val.obj U) :
    ((mulSectionHom Y σ).val.app U).hom a =
      tensorObjTmul Y F G U ((σ.val.app U).hom (unitSection Y U 1)) a := by
  rw [mulSectionHom, Stacks.SheafOfModules.OnSpace.sheaf_comp_app_apply,
    Stacks.SheafOfModules.OnSpace.leftUnitor_inv_apply,
    Stacks.SheafOfModules.OnSpace.whiskerRight_tmul]

/-! ### The reflexive powers -/

variable {X : Scheme.{u}}

/-- The reflexive powers of `ℱ`: `ℱ^{[1]} = ℱ` and `ℱ^{[n + 1]} = (ℱ ⊗_{𝒪_X} ℱ^{[n]})^{**}`; the
value at `0` is `𝒪_X`, the first term of the system `𝒪_X → ℱ → ℱ^{[2]} → ⋯`. -/
@[stacks 0EBN "the reflexive powers ℱ^[1] = ℱ, ℱ^[n+1] = (ℱ ⊗ ℱ^[n])^{**}"]
noncomputable def reflexivePower (F : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | 1 => F
  | n + 2 => reflexiveHull ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
        ((reflexivePower F (n + 1)))))

/-- The zeroth term of the system is the structure sheaf. -/
@[simp]
theorem reflexivePower_zero (F : X.Modules) :
    reflexivePower F 0 = SheafOfModules.unit X.ringCatSheaf := rfl

/-- The first reflexive power is `ℱ` itself. -/
@[simp]
theorem reflexivePower_one (F : X.Modules) : reflexivePower F 1 = F := rfl

/-- The recursion `ℱ^{[n + 2]} = (ℱ ⊗_{𝒪_X} ℱ^{[n + 1]})^{**}`. -/
theorem reflexivePower_succ_succ (F : X.Modules) (n : ℕ) :
    reflexivePower F (n + 2) =
      reflexiveHull ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
          ((reflexivePower F (n + 1))))) := rfl

/-- The transition maps `ℱ^{[n]} ⟶ ℱ^{[n + 1]}` of the system of [Stacks, Tag 0EBN]:
multiplication by `s` followed by the canonical map to the reflexive hull in degrees `≥ 1`, and
the morphism `𝒪_X ⟶ ℱ` determined by `s` in degree `0`. -/
noncomputable def reflexivePowerTransition (F : X.Modules) (s : F.sections) :
    (n : ℕ) → (reflexivePower F n ⟶ reflexivePower F (n + 1))
  | 0 => F.unitHomEquiv.symm s
  | n + 1 =>
      mulSectionHom X.toRingedSpace (F.unitHomEquiv.symm s) ≫
        toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
            ((reflexivePower F (n + 1)))))

/-- The transition out of degree `0` is the morphism `𝒪_X ⟶ ℱ` determined by `s`. -/
theorem reflexivePowerTransition_zero (F : X.Modules) (s : F.sections) :
    reflexivePowerTransition F s 0 = F.unitHomEquiv.symm s := rfl

/-- The transition out of degree `n + 1` is multiplication by `s` into the hull. -/
theorem reflexivePowerTransition_succ (F : X.Modules) (s : F.sections) (n : ℕ) :
    reflexivePowerTransition F s (n + 1) =
      mulSectionHom X.toRingedSpace (F.unitHomEquiv.symm s) ≫
        toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
            ((reflexivePower F (n + 1))))) := rfl

/-! ### The system at a point -/

/-- `ℱ^{[n]}_x`, the stalk of the `n`-th reflexive power, an `𝒪_{X, x}`-module by
`AlgebraicGeometry.Scheme.Modules.moduleStalk`. -/
abbrev reflexivePowerStalk (F : X.Modules) (x : X) (n : ℕ) : Type u :=
  ↑(TopCat.Presheaf.stalk (reflexivePower F n).val.presheaf x)

/-- The stalk of the transition map, as an `𝒪_{X, x}`-linear map `ℱ^{[n]}_x ⟶ ℱ^{[n + 1]}_x`.
This is the multiplication by `s` of [Stacks, Tag 0EBR]. -/
noncomputable def reflexivePowerStalkMap (F : X.Modules) (s : F.sections) (x : X) (n : ℕ) :
    reflexivePowerStalk F x n →ₗ[↑(X.presheaf.stalk x)] reflexivePowerStalk F x (n + 1) :=
  AlgebraicGeometry.stalkMapLinear (R := X.presheaf) _ _ (reflexivePowerTransition F s n).val x

/-- The germ at `x` of the unit section `1 ∈ Γ(X, 𝒪_X)`, an element of `ℱ^{[0]}_x = 𝒪_{X, x}`.
Pushing it along the transitions gives the powers `sⁿ ∈ ℱ^{[n]}_x`. -/
noncomputable def reflexivePowerUnit (F : X.Modules) (x : X) : reflexivePowerStalk F x 0 :=
  (TopCat.Presheaf.germ (reflexivePower F 0).val.presheaf ⊤ x trivial).hom
    (1 : Γ(X, (⊤ : X.Opens)))

end Stacks.AlgebraicGeometry.ReflexivePowers

end
