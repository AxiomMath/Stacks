module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.Topology.Sheaves.RingedSpace.ThickeningTrivialization
import StacksCore.Tactic.StacksAttribute

/-!
# Strict morphisms of thickenings and cartesian squares (Stacks 08L2)

Let

    X  ⟶  X'
    ↓f    ↓f'
    S  ⟶  S'

be a morphism of thickenings of ringed spaces in the sense of **Stacks 08KZ**. Tag 08L2 says
that `(f, f')` is a *strict* morphism of thickenings — the canonical map `(f')^* J ⟶ I` of
**Stacks 08L1** is surjective — exactly when the displayed square is cartesian in the category
of ringed spaces. This file proves the forward implication.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings.isPullback_of_isStrict`:
  **Stacks 08L2**, a strict morphism of thickenings has a cartesian square.

## Implementation notes

Both thickenings are monomorphisms of ringed spaces
(`AlgebraicGeometry.RingedSpaceThickening.mono_of_isThickening`), so the square has at most one
lift of any test pair and only existence has content. For a test pair `(g, h)` with
`g ≫ f' = h ≫ t`, the composite `(f')^* J ⟶ I ⟶ 𝒪_{X'} ⟶ g_* 𝒪_Z` vanishes: transposed across
`(f')^* ⊣ (f')_*` it becomes `J ⟶ 𝒪_{S'} ⟶ (g ≫ f')_* 𝒪_Z`, which is the comorphism of
`h ≫ t` and so kills `J`. Strictness turns that into the vanishing of `I ⟶ 𝒪_{X'} ⟶ g_* 𝒪_Z`,
and `exists_factorization_of_comp_idealι_eq_zero` then factors `g` through `i`.

## References

* [Stacks Project, Tag 08L2](https://stacks.math.columbia.edu/tag/08L2)
* [Stacks Project, Tag 08L1](https://stacks.math.columbia.edu/tag/08L1)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local implicit_reducible] RingedSpaceModuleAdjunction.modulePushforward
  RingedSpaceModuleAdjunction.modulePullback

namespace MorphismOfThickenings

/-- The ambient ideal map `(f')^* J ⟶ 𝒪_{X'}` of **Stacks 08KZ** is killed by the comorphism of
any `g : Z ⟶ X'` that fits into the square, that is, any `g` with `g ≫ f' = h ≫ t` for some
`h : Z ⟶ S`. Transposed across `(f')^* ⊣ (f')_*` the composite becomes the inclusion
`J ⟶ 𝒪_{S'}` followed by the comorphism of `g ≫ f' = h ≫ t`, which kills `J` because the
comorphism of `t` does. -/
private theorem ambientIdealMap_comp_comorphism_eq_zero
    (D : MorphismOfThickenings.{u}) {Z : RingedSpace.{u, u}}
    (g : Z ⟶ D.X') (h : Z ⟶ D.S) (hw : g ≫ D.f' = h ≫ D.t) :
    D.ambientIdealMap ≫
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g) = 0 := by
  have hamb : D.ambientIdealMap =
      (modulePullback D.f').map (kernel.ι
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.t))) ≫
        pullbackUnitToUnit D.f' := rfl
  have h1 : kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.t)) ≫
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.t) ≫
        (modulePushforward D.t).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom h)) = 0 := by
    rw [kernel.condition_assoc, zero_comp]
  have h2 := (comp_unitToPushforwardObjUnit_eq_zero_iff h D.t
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.t)))).1 h1
  rw [← hw] at h2
  have h3 := (comp_unitToPushforwardObjUnit_eq_zero_iff g D.f'
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.t)))).2 h2
  apply ((modulePullbackPushforwardAdjunction D.f').homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, hamb, homEquiv_map_comp_pullbackUnitToUnit,
    Category.assoc, h3, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]

/-- **Stacks Project, Tag 08L2.** A strict morphism of thickenings has a cartesian square: both
thickenings are monomorphisms, so uniqueness of a lift is automatic, and existence is the
factorization of a test morphism through `i` supplied by
`exists_factorization_of_comp_idealι_eq_zero`. -/
@[stacks 08L2 "a strict morphism has a cartesian square"]
theorem isPullback_of_isStrict (D : MorphismOfThickenings.{u}) (hs : D.IsStrict) :
    IsPullback D.i D.f D.f' D.t := by
  have hmi : Mono D.i := mono_of_isThickening D.i D.i_isThickening
  have hmt : Mono D.t := mono_of_isThickening D.t D.t_isThickening
  have hepi : Epi D.idealMap.1 := hs
  refine IsPullback.mk' D.comm (fun _ _ _ hi _ => (cancel_mono D.i).mp hi) fun Z g h hw => ?_
  have hk : kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.i)) ≫
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g) = 0 := by
    rw [← cancel_epi D.idealMap.1, comp_zero, ← Category.assoc, D.idealMap.2]
    exact ambientIdealMap_comp_comorphism_eq_zero D g h hw
  obtain ⟨l, hl⟩ :=
    exists_factorization_of_comp_idealι_eq_zero D.i g D.i_isThickening hk
  refine ⟨l, hl, (cancel_mono D.t).mp ?_⟩
  rw [Category.assoc, ← D.comm, ← Category.assoc, hl, hw]

end MorphismOfThickenings

end AlgebraicGeometry.RingedSpaceThickening

end
