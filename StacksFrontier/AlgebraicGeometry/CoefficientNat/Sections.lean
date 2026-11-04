module

public import StacksFrontier.AlgebraicGeometry.CoefficientNat.Basic
public import StacksFrontier.AlgebraicGeometry.CoefficientIso.Basic

/-!
# The restriction maps of [Stacks, Tag 01XL]'s coefficient system, on sections

`Stacks.Tag01XLCoefficientIso.absoluteCechOpensPresheafEvalIso` compares the coefficient presheaf
of [Stacks, Tag 01XL] with the Čech diagram of [Stacks, Tag 02FU] at each open set and naturally
in the module, and what it does not do is the naturality **in the open set**.  That square
compares `Stacks.CechTotalComplex.CoveringResolution.infPushforwardRestriction` with
`Stacks.AlgebraicGeometry.RelativeCech.relativeUnit`, and the obstruction recorded in
`StacksFrontier/AlgebraicGeometry/CoefficientIso/Basic.lean` was that no declaration in either tree
concluded a value for
`relativeUnit` **on sections**.

This file supplies that value, for an open immersion, and the two values on the other side of the
square.  The three together reduce the naturality in the open set to the transport of a
`CategoryTheory.eqToHom` along the factorisation `X.homOfLE h ≫ W.ι = V.ι`.

## Main results

* `Stacks.Tag01XLCoefficientNat.restrictUnitStep_app_app`: the restriction map of the coefficient
  system in the `restrictFunctor` spelling is, on sections over `U`, the single presheaf
  restriction map `ℱ(b ''ᵁ b ⁻¹ᵁ U) ⟶ ℱ((u ≫ b) ''ᵁ (u ≫ b) ⁻¹ᵁ U)`.
* `Stacks.Tag01XLCoefficientNat.relativeUnit_app_comp_app` and
  `Stacks.Tag01XLCoefficientNat.relativeUnit_app_app`: **the value of
  `RelativeCech.relativeUnit` on sections**, for an open immersion:  conjugated by
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` it is that presheaf restriction
  map.  This is the declaration whose absence was recorded.
* `Stacks.Tag01XLCoefficientNat.restrictPushforwardInfIso_hom_app_app` and
  `Stacks.Tag01XLCoefficientNat.infPushforwardRestriction_app_up`: the two values on the
  [Stacks, Tag 02FU] side of the square — the coefficient comparison is a presheaf restriction
  along `U ⊓ V = V.ι ''ᵁ (V.ι ⁻¹ᵁ U)`, and the restriction map of the Čech diagram is the
  `ULift` of a presheaf restriction.  Both hold by `rfl`.

## Implementation notes

The first two are the two halves of `thin_map_comp₂`:  every factor is an `ℱ.presheaf.map`, and
any two morphisms of `X.Opens` with the same source and target are equal.  `rw` is never used to
cancel two such factors; the identity is always applied as a term.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.Tag01XLCoefficientNat

/-! ### The [Stacks, Tag 01XL] side -/

variable {X : Scheme.{u}}

/-- Equal morphisms of module sheaves have equal values on sections.  Stated as a lemma rather
than used as a `congrArg` inline:  with the function written out, its domain is elaborated from
the equation, and no spelling of the source or target functor has to be guessed. -/
theorem hom_congr_app {M N : X.Modules} {φ ψ : M ⟶ N} (h : φ = ψ) (U : X.Opens) :
    φ.app U = ψ.app U :=
  congrArg (fun k : M ⟶ N => k.app U) h

variable {Y Z : Scheme.{u}} (u : Y ⟶ Z) (b : Z ⟶ X) [IsOpenImmersion u] [IsOpenImmersion b]

/-- The image of the preimage along a composite is inside the image of the preimage along the
second factor:  `(u ≫ b) ''ᵁ ((u ≫ b) ⁻¹ᵁ U) = b ''ᵁ (u ''ᵁ (u ⁻¹ᵁ (b ⁻¹ᵁ U)))`. -/
theorem image_preimage_comp_le (U : X.Opens) :
    (u ≫ b) ''ᵁ ((u ≫ b) ⁻¹ᵁ U) ≤ b ''ᵁ (b ⁻¹ᵁ U) := by
  rw [Scheme.Hom.comp_image, Scheme.Hom.comp_preimage]
  exact Scheme.Hom.image_mono b (u.image_preimage_le _)

/-- **The restriction map of the coefficient system, on sections.**  In the `restrictFunctor`
spelling it is a single presheaf restriction map: the sections over `U` of
`restrictFunctor b ⋙ pushforward b` are `ℱ(b ''ᵁ b ⁻¹ᵁ U)`, those of the composite are
`ℱ((u ≫ b) ''ᵁ (u ≫ b) ⁻¹ᵁ U)`, and the map is the restriction between them. -/
theorem restrictUnitStep_app_app (M : X.Modules) (U : X.Opens) :
    ((restrictUnitStep u b).app M).app U =
      M.presheaf.map (homOfLE (image_preimage_comp_le u b U)).op := by
  have key : ((restrictAdjunction u).unit.app ((restrictFunctor b).obj M) ≫
        (pushforward u).map ((restrictFunctorComp u b).inv.app M)).app (b ⁻¹ᵁ U) =
      M.presheaf.map (homOfLE (image_preimage_comp_le u b U)).op := by
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
      Scheme.Modules.restrictAdjunction_unit_app_app,
      Scheme.Modules.restrictFunctorComp_inv_app_app, Scheme.Modules.restrict_map]
    exact thin_map_comp₂ M.presheaf _ _ _
  exact (hom_congr_app (restrictUnitStep_app u b M) U).trans key

/-- **The value of `Stacks.AlgebraicGeometry.RelativeCech.relativeUnit` on sections**, for open
immersions `u` and `b`:  conjugated by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` it is the presheaf restriction map
`ℱ(b ''ᵁ b ⁻¹ᵁ U) ⟶ ℱ((u ≫ b) ''ᵁ (u ≫ b) ⁻¹ᵁ U)`.

Neither the unit of `pullbackPushforwardAdjunction` nor `pullbackComp` — the two ingredients of
`relativeUnit` — has a description on sections; this is the identification that supplies one. -/
theorem relativeUnit_app_comp_app (M : X.Modules) (U : X.Opens) :
    ((pushforward b).map ((restrictFunctorIsoPullback b).hom.app M)).app U ≫
        ((Stacks.AlgebraicGeometry.RelativeCech.relativeUnit u b).app M).app U =
      ((restrictUnitStep u b).app M).app U ≫
        ((pushforward b).map ((pushforward u).map
          ((restrictFunctorIsoPullback (u ≫ b)).hom.app M))).app U :=
  hom_congr_app (map_restrictFunctorIsoPullback_comp_relativeUnit u b M) U

/-- **The value of `Stacks.AlgebraicGeometry.RelativeCech.relativeUnit` on sections**, for open
immersions `u` and `b`:  conjugated by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` it is the presheaf restriction map
`ℱ(b ''ᵁ b ⁻¹ᵁ U) ⟶ ℱ((u ≫ b) ''ᵁ (u ≫ b) ⁻¹ᵁ U)`.

Neither the unit of `pullbackPushforwardAdjunction` nor `pullbackComp` — the two ingredients of
`relativeUnit` — has a description on sections; this is the identification that supplies one. -/
theorem relativeUnit_app_app (M : X.Modules) (U : X.Opens) :
    ((pushforward b).map ((restrictFunctorIsoPullback b).hom.app M)).app U ≫
        ((Stacks.AlgebraicGeometry.RelativeCech.relativeUnit u b).app M).app U =
      M.presheaf.map (homOfLE (image_preimage_comp_le u b U)).op ≫
        ((pushforward b).map ((pushforward u).map
          ((restrictFunctorIsoPullback (u ≫ b)).hom.app M))).app U :=
  by rw [← restrictUnitStep_app_app]; exact relativeUnit_app_comp_app u b M U

/-! ### The [Stacks, Tag 02FU] side -/

/-- **The coefficient comparison of
`Stacks.Tag01XLCoefficientIso.restrictPushforwardInfIso`, on sections:** the restriction along
`V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U ⊓ V`.  Every factor of that isomorphism —
`SheafOfModules.pushforwardComp`, `SheafOfModules.pushforwardNatIso` and
`SheafOfModules.pushforwardCongr` — is either an identity or a presheaf restriction map on
sections, so this holds by `rfl`. -/
theorem restrictPushforwardInfIso_hom_app_app (X : Scheme.{u}) (V : X.Opens) (F : X.Modules)
    (U : X.Opens) :
    ((Stacks.Tag01XLCoefficientIso.restrictPushforwardInfIso X V).hom.app F).app U =
      F.presheaf.map (eqToHom (Stacks.Tag01XLCoefficientIso.image_preimage_ι X V U).symm).op :=
  rfl

/-- **The restriction map of the Čech diagram of [Stacks, Tag 02FU], on sections:** the `ULift`
of the presheaf restriction `ℱ(U ⊓ W) ⟶ ℱ(U ⊓ V)`.  This holds by `rfl`. -/
theorem infPushforwardRestriction_app_up (X : Scheme.{u}) {V W : X.Opens} (h : V ≤ W)
    (F : X.Modules) (U : X.Opens) (x : Γ(F, U ⊓ W)) :
    (Stacks.CechTotalComplex.CoveringResolution.infPushforwardRestriction.{u, u, u, u} X.carrier
      X.ringCatSheaf F h).app
        (op U) (ULift.up x) =
      ULift.up (F.presheaf.map (homOfLE (inf_le_inf_left U h)).op x) :=
  rfl

end Stacks.Tag01XLCoefficientNat

end
