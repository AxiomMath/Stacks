module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.Topology.Sheaves.Modules.Differentials
public import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of relative differentials of a morphism of schemes

For a morphism of schemes `f : X ⟶ S`, the sheaf of relative differentials is the module
representing derivations of the structure sheaf of `X` relative to the inverse image of the
structure sheaf of `S`, together with its universal derivation.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` is the sheaf of relative differentials
  of a morphism of schemes.
* `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation` is its universal relative
  derivation.

## Implementation notes

The structural map of a morphism of schemes is `AlgebraicGeometry.inverseImageStructureMap`,
and the representing module and its universal derivation are the sheaf-theoretic
constructions for that map. So these are definitions rather than constructions: all the
content is in the representability of the derivations functor.

## References

* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The sheaf of relative differentials of a morphism of schemes, formed over the inverse
image of the structure sheaf of the base. -/
noncomputable def relativeDifferentials {X S : Scheme.{u}} (f : X ⟶ S) : X.Modules :=
  SheafOfModules.moduleOfDifferentials (inverseImageStructureMap f)

/-- The universal relative derivation of the structure sheaf of the source of a morphism of
schemes into its sheaf of relative differentials. -/
@[ega "IV 16.5.3"]
noncomputable def universalRelativeDerivation {X S : Scheme.{u}} (f : X ⟶ S) :
    SheafOfModules.SheafDerivation (inverseImageStructureMap f) (relativeDifferentials f) :=
  SheafOfModules.universalDerivation (inverseImageStructureMap f)

/-- **The comorphism of `f` factors through the structural map `f⁻¹𝒪_S ⟶ 𝒪_X`.** On sections
over an open `W` of `S`, `f^♯` is the unit of `f⁻¹ ⊣ f_*` at `𝒪_S` followed by
`AlgebraicGeometry.inverseImageStructureMap`.

This is the definition of `AlgebraicGeometry.inverseImageStructureMap` as the adjunct of `f.c`,
read on sections. -/
theorem app_eq_inverseImageStructureMap {X S : Scheme.{u}} (f : X ⟶ S) (W : S.Opens)
    (r : Γ(S, W)) :
    (f.app W).hom r =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app S.sheaf ≫
          (TopCat.Sheaf.pushforward CommRingCat f.base).map
            (inverseImageStructureMap f)).hom.app (Opposite.op W)).hom r := by
  have h2 := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv
    S.sheaf X.sheaf).apply_symm_apply (⟨f.c⟩ :
      S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf)
  rw [Adjunction.homEquiv_unit] at h2
  exact (congrArg (fun ψ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf ↦
    (ψ.hom.app (Opposite.op W)).hom r) h2).symm

/-- **The universal relative derivation kills the sections coming from the base.** For a section
`r` of `𝒪_S` over an open `W` of `S`, `d_{X/S} (f^♯ r) = 0`.

The vanishing of a relative derivation on the image of the structural map `f⁻¹𝒪_S ⟶ 𝒪_X` is one
of the defining conditions of `AlgebraicGeometry.SheafOfModules.SheafDerivation`; this is that
condition read through `AlgebraicGeometry.Scheme.Hom.app_eq_inverseImageStructureMap`. -/
theorem universalRelativeDerivation_d_app_eq_zero {X S : Scheme.{u}} (f : X ⟶ S) (W : S.Opens)
    (r : Γ(S, W)) : (universalRelativeDerivation f).d ((f.app W).hom r) = 0 :=
  (congrArg (fun y : Γ(X, f ⁻¹ᵁ W) ↦ (universalRelativeDerivation f).d y)
    (app_eq_inverseImageStructureMap f W r)).trans
      ((universalRelativeDerivation f).d_app
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app
          S.sheaf).hom.app (Opposite.op W)).hom r))

end AlgebraicGeometry.Scheme.Hom
