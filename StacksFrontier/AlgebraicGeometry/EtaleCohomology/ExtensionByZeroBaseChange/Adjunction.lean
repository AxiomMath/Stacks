module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero on small étale sites

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`.
Restriction of sheaves along `j` is the direct image of the continuous site functor
`AlgebraicGeometry.smallEtalePostcompose`, that is, precomposition with "an étale scheme over
`U` is an étale scheme over `X`". Its left adjoint is *extension by zero*: on presheaves it
is the left Kan extension `V ↦ ⨁_{V → U} F(V → U)`, and `j_!F` is the sheafification of
that. This file constructs restriction and extension by zero for abelian sheaves and for
sheaves of modules over a fixed ring, each with its defining adjunction.

Only parts (2) and (3) of Stacks 03S3 are constructed here — abelian sheaves and sheaves of
modules. Part (1), for sheaves of sets, is not present.

## Main definitions

* `AlgebraicGeometry.abelianRestriction` and `AlgebraicGeometry.abelianExtensionByZero` —
  `j^{-1}` and `j_!` on abelian sheaves, with
  `AlgebraicGeometry.abelianPresheafExtensionByZero` the presheaf `j_{p!}` whose
  sheafification `j_!` is, as recorded by
  `AlgebraicGeometry.abelianExtensionByZero_eq`.
* `AlgebraicGeometry.moduleRestriction` and `AlgebraicGeometry.moduleExtensionByZero` — the
  same for sheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.abelianExtensionByZeroAdjunction` and
  `AlgebraicGeometry.moduleExtensionByZeroAdjunction` — the defining adjunctions
  `j_! ⊣ j^{-1}`.

## Implementation notes

The adjunction is the general sheaf-pullback construction of a continuous functor of sites,
so extension by zero is `Functor.sheafPullbackConstruction.sheafPullback` rather than a
hand-built colimit; the characterising property is the adjunction, which is what every
consumer uses.

Sheafification of `ModuleCat Λ`-valued presheaves on the small étale site is available
because that site is essentially small at the universe `max (u + 1) v`, and the forgetful
functor of `ModuleCat Λ` preserves filtered colimits; this is
`AlgebraicGeometry.moduleSheaf_hasWeakSheafify`. The module universe is therefore tied to the
scheme universe, as it is for the coproducts defining the presheaf extension.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- Restriction of abelian étale sheaves along the étale morphism `U ⟶ X`. -/
public abbrev abelianRestriction :
    Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        AddCommGrpCat.{u + 1} :=
  (smallEtalePostcompose B X hX U).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1}
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- The *presheaf* extension by zero `j_{p!}` of an abelian étale sheaf along the étale
morphism `U ⟶ X`: the left Kan extension `V ↦ ⨁_{φ : V → U} F(V →^φ U)` of the underlying
presheaf along the site functor `AlgebraicGeometry.smallEtalePostcompose`, before
sheafification. -/
public abbrev abelianPresheafExtensionByZero :
    Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        AddCommGrpCat.{u + 1} ⥤
      ((SmallEtale B X hX)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  sheafToPresheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1} ⋙
    (smallEtalePostcompose B X hX U).op.lan

/-- **Stacks 03S3, part (2).** Extension by zero of abelian étale sheaves along the étale
morphism `U ⟶ X`: the sheafification of `V ↦ ⨁_{V → U} F(V → U)`, realised as the sheaf
pullback of the continuous site functor `AlgebraicGeometry.smallEtalePostcompose`. -/
@[stacks 03S3 "abelian_extension_by_zero"]
public def abelianExtensionByZero :
    Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtalePostcompose B X hX U)
    AddCommGrpCat.{u + 1}
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- **Stacks 03S3, part (2).** Extension by zero is left adjoint to restriction, which is
the property characterising it. -/
@[stacks 03S3 "abelian_extension_by_zero",
  sga "4 XVII 6.2.11" "f_! ⊣ f^* (abelian)",
  sga "4 IV 11.3.1" "étale site, Ab"]
public def abelianExtensionByZeroAdjunction :
    abelianExtensionByZero B X hX U ⊣ abelianRestriction B X hX U :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtalePostcompose B X hX U)
    AddCommGrpCat.{u + 1}
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- Extension by zero is the sheafification of the presheaf extension by zero: `j_!F` is
`(j_{p!}F)^#`. -/
public theorem abelianExtensionByZero_eq :
    abelianExtensionByZero B X hX U =
      abelianPresheafExtensionByZero B X hX U ⋙
        presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1} :=
  rfl

/-- Extension by zero of abelian sheaves is a left adjoint, hence preserves colimits. -/
public instance abelianExtensionByZero_isLeftAdjoint :
    (abelianExtensionByZero B X hX U).IsLeftAdjoint :=
  (abelianExtensionByZeroAdjunction B X hX U).isLeftAdjoint

variable (Λ : Type v) [Ring Λ]

/-- Presheaves of `Λ`-modules on the small étale site of a scheme in a big étale site admit
sheafification at the universe `max (u + 1) v`: that site is essentially small there, and the
forgetful functor of `ModuleCat Λ` preserves filtered colimits. -/
public instance moduleSheaf_hasWeakSheafify :
    HasWeakSheafify (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ) := by
  have _ : PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) v} Λ)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat)
      (forget AddCommGrpCat)
  have _ : EssentiallySmall.{max (u + 1) v} (SmallEtale B X hX) := inferInstance
  have _ : HasSheafify (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) v} _ _
  infer_instance

/-- Restriction of étale sheaves of `Λ`-modules along the étale morphism `U ⟶ X`. Restriction
needs no colimits, so it is available in every module universe. -/
public abbrev moduleRestriction :
    Sheaf (SmallEtale.topology B X hX) (ModuleCat.{w} Λ) ⥤
      Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (ModuleCat.{w} Λ) :=
  (smallEtalePostcompose B X hX U).sheafPushforwardContinuous
    (ModuleCat.{w} Λ)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- **Stacks 03S3, part (3).** Extension by zero of étale sheaves of `Λ`-modules along the
étale morphism `U ⟶ X`. -/
public def moduleExtensionByZero :
    Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (ModuleCat.{max (u + 1) v} Λ) ⥤
      Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtalePostcompose B X hX U)
    (ModuleCat.{max (u + 1) v} Λ)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- **Stacks 03S3, part (3).** Extension by zero of sheaves of modules is left adjoint to
restriction. -/
@[stacks 03S3 "module_extension_by_zero",
  sga "4 XVII 6.2.11" "f_! ⊣ f^* (Λ-modules)",
  sga "4 IV 11.3.1" "étale site, Λ-modules"]
public def moduleExtensionByZeroAdjunction :
    moduleExtensionByZero B X hX U Λ ⊣ moduleRestriction B X hX U Λ :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtalePostcompose B X hX U)
    (ModuleCat.{max (u + 1) v} Λ)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- Extension by zero of sheaves of modules is a left adjoint, hence preserves colimits. -/
public instance moduleExtensionByZero_isLeftAdjoint :
    (moduleExtensionByZero B X hX U Λ).IsLeftAdjoint :=
  (moduleExtensionByZeroAdjunction B X hX U Λ).isLeftAdjoint

end AlgebraicGeometry

end
