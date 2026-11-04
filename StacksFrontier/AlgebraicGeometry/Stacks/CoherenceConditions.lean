module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# The conditions characterizing coherence on a locally Noetherian stack

Let `𝒳` be a locally Noetherian algebraic stack and `ℱ` an `𝒪_𝒳`-module. The following four
conditions on `ℱ` are equivalent:

1. `ℱ` is a quasi-coherent, finite type `𝒪_𝒳`-module;
2. `ℱ` is an `𝒪_𝒳`-module of finite presentation;
3. `ℱ` is quasi-coherent and for every morphism `f : U ⟶ 𝒳` with `U` a locally Noetherian
   algebraic space the pullback `f^*ℱ|_{U_étale}` is coherent;
4. `ℱ` is quasi-coherent and there are an algebraic space `U` and a morphism `f : U ⟶ 𝒳` which
   is locally of finite type, flat and surjective such that `f^*ℱ|_{U_étale}` is coherent.

Conditions (1) and (2) are conditions on the big fppf site of `𝒳` alone, and are
`AlgebraicGeometry.Stack.IsQuasicoherentFiniteTypeModule` and
`SheafOfModules.IsFinitePresentationOnSite`. This module proves the implication (2) ⟹ (1).

## Main definitions

* `AlgebraicGeometry.Stack.IsQuasicoherentFiniteTypeModule`: condition (1), that a module on the
  big fppf site of an algebraic stack be quasi-coherent and of finite type.

## Main results

* `AlgebraicGeometry.Stack.isQuasicoherentFiniteTypeModule_of_isFinitePresentationOnSite`: the
  implication (2) ⟹ (1).

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u m t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A module on the big fppf site of an algebraic stack `𝒳` is quasi-coherent and of finite
type. -/
abbrev IsQuasicoherentFiniteTypeModule (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) : Prop :=
  M.IsQuasicoherentOnSite ∧ M.IsFiniteTypeOnSite

/-- On a locally Noetherian algebraic stack a module of finite presentation on the big fppf site is
quasi-coherent and of finite type. -/
@[stacks 0GR5 "condition (2) implies condition (1)"]
theorem isQuasicoherentFiniteTypeModule_of_isFinitePresentationOnSite
    (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : M.IsFinitePresentationOnSite) :
    IsQuasicoherentFiniteTypeModule B S hS 𝒳 M :=
  have := hM
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Stack

end
