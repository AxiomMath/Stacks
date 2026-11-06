module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChangeIso

/-!
# The module triple of a glueing triple with affine legs

In a formal glueing situation `(f : Y ⟶ X, Z, U, V)`, a glueing triple `G = (U' ⟵ V' ⟶ Y')` whose
legs `g_U : U' ⟶ U` and `g_Y : Y' ⟶ Y` are affine has a triple of quasi-coherent modules
`(g_{U*}𝒪_{U'}, g_{Y*}𝒪_{Y'}, φ)`, the comparison `φ` being the composite of the two affine base
change isomorphisms of Stacks 07U8 onto `g_{V*}𝒪_{V'}`.  This is the algebra triple whose
glueing is the affine case of Stacks 0AF4.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.affLegU`, `affLegY`, `affLegV`: the three
  spaces of the triple, and `affLegUHom`, `affLegYHom`, `affLegVHom`, `affLegVU`, `affLegVY` its
  five morphisms.
* `AlgebraicGeometry.Space.FormalGlueingSituation.moduleTripleOfAffineLegs`: the module triple.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_affLegVU` and
  `isPullback_affLegVY`: the two cartesian squares over the overlap.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_formalGlueingSpacesAffineCaseTriple
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- A pullback of presheaves on the big fppf site, found directly from `HasPullbacks`. -/
local instance (priority := high) hasPullback_presheaf_formalGlueingSpacesAffineCaseTriple
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS) (G : (affineLegs D).FullSubcategory)

/-- The space `U'` of a glueing triple. -/
def affLegU : AlgebraicSpaces B S hS := ⟨G.obj.obj.left.left, G.obj.property.2.1⟩

/-- The space `Y'` of a glueing triple. -/
def affLegY : AlgebraicSpaces B S hS := ⟨G.obj.obj.right.left, G.obj.property.2.2⟩

/-- The space `V' = V ×_U U'` of a glueing triple. -/
def affLegV : AlgebraicSpaces B S hS :=
  ⟨((Over.pullback (D.U.fromPreimage D.f)).obj G.obj.obj.left).left,
    isAlgebraicSpace_pullback B S hS _ _ G.obj.property.2.1 D.spaceV.2 D.spaceU.2⟩

/-- The leg `U' ⟶ U`. -/
def affLegUHom : D.affLegU G ⟶ D.spaceU := ObjectProperty.homMk G.obj.obj.left.hom

/-- The leg `Y' ⟶ Y`. -/
def affLegYHom : D.affLegY G ⟶ D.spaceY := ObjectProperty.homMk G.obj.obj.right.hom

/-- The leg `V' ⟶ V`. -/
def affLegVHom : D.affLegV G ⟶ D.spaceV :=
  ObjectProperty.homMk ((Over.pullback (D.U.fromPreimage D.f)).obj G.obj.obj.left).hom

/-- The projection `V' ⟶ U'`. -/
def affLegVU : D.affLegV G ⟶ D.affLegU G := ObjectProperty.homMk (pullback.fst _ _)

/-- The map `V' ⟶ Y'` given by the structure isomorphism of the triple. -/
def affLegVY : D.affLegV G ⟶ D.affLegY G :=
  ObjectProperty.homMk (G.obj.obj.hom.left ≫ pullback.fst G.obj.obj.right.hom D.V.ι)

/-- The square `V' = V ×_U U'` is cartesian. -/
theorem isPullback_affLegVU :
    IsPullback (D.affLegVU G) (D.affLegVHom G) (D.affLegUHom G) D.overlapRestriction :=
  IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ pullback.condition)
    (IsPullback.of_hasPullback G.obj.obj.left.hom (D.U.fromPreimage D.f))

/-- The square `V' ≅ V ×_Y Y'` is cartesian, through the structure isomorphism of the triple. -/
theorem isPullback_affLegVY :
    IsPullback (D.affLegVY G) (D.affLegVHom G) (D.affLegYHom G) D.openImmersionOver := by
  have : IsIso G.obj.obj.hom := G.obj.property.1
  have : IsIso G.obj.obj.hom.left := inferInstanceAs (IsIso ((Over.forget _).map G.obj.obj.hom))
  have w₂ : G.obj.obj.hom.left ≫ pullback.snd G.obj.obj.right.hom D.V.ι =
      pullback.snd G.obj.obj.left.hom (D.U.fromPreimage D.f) := Over.w G.obj.obj.hom
  have h : IsPullback (G.obj.obj.hom.left ≫ pullback.fst G.obj.obj.right.hom D.V.ι)
      (pullback.snd G.obj.obj.left.hom (D.U.fromPreimage D.f)) G.obj.obj.right.hom D.V.ι :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, w₂]⟩
      (asIso G.obj.obj.hom.left) rfl w₂
  exact IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ h.w) h

/-- **The module triple of a glueing triple with affine legs**: `(g_{U*}𝒪_{U'}, g_{Y*}𝒪_{Y'})`
with the comparison over `V` through `g_{V*}𝒪_{V'}`, by affine base change. -/
abbrev moduleTripleOfAffineLegs : D.moduleGlueingData :=
  ⟨⟨(modulePushforward B S hS (D.affLegUHom G)).obj
      (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G))),
    (modulePushforward B S hS (D.affLegYHom G)).obj
      (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G))),
    (modulePullbackPushforwardUnitIso (D.isPullback_affLegVU G) G.property.1).hom ≫
      (modulePullbackPushforwardUnitIso (D.isPullback_affLegVY G) G.property.2.2).inv⟩,
    ⟨inferInstance,
      isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS _ G.property.1 _
        (SheafOfModules.isQuasicoherentOnSite_unit _),
      isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS _ G.property.2.2 _
        (SheafOfModules.isQuasicoherentOnSite_unit _)⟩⟩

end AlgebraicGeometry.Space.FormalGlueingSituation
