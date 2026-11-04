module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseSpacesEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfModulesRestrictScalarsCongr

/-!
# The direct images of modules over a smaller base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site, `f : Z₁ ⟶ Z₂` a morphism of algebraic spaces
over `W` and `g : Y₁ ⟶ Y₂` one over `S`, matched by `εᵢ : Λ_h Zᵢ ≅ Yᵢ`. This file reduces the
comparison of the direct images of modules `g_* ⋙ (−)' ≅ (−)' ⋙ f_*`, for an arbitrary `f`, to
an identity between the structure maps `f♯` and `g♯`: the change of base of modules is the
inverse image of modules along restriction of sheaves of sets
(`Stacks.Sheaves.ToposPullback.restrictionModuleIso`), the direct images are inverse images of
modules along the direct images of sheaves of sets followed by restriction of scalars along the
structure maps, and those direct images of sheaves of sets commute with the change of base
(`AlgebraicGeometry.Space.smallerBaseSmallEtaleDirectImageIso`).

## Main definitions

* `AlgebraicGeometry.Space.smallerBaseSheafRestriction`: the change of base `(−)'` on sheaves of
  sets.
* `AlgebraicGeometry.Space.smallerBaseModulesEquivalenceIsoPullback`: the change of base of
  modules as an inverse image of modules along `(−)'`.
* `AlgebraicGeometry.Space.smallerBaseStructureSharpLeft` and
  `AlgebraicGeometry.Space.smallerBaseStructureSharpRight`: `g♯` carried over to `Z₂`, and `f♯`.
* `AlgebraicGeometry.Space.smallerBasePushforwardLeftIso` and
  `AlgebraicGeometry.Space.smallerBasePushforwardRightIso`: the two composites in normal form.
* `AlgebraicGeometry.Space.smallerBaseModulePushforwardIsoOfStructure` and
  `AlgebraicGeometry.Space.smallerBasePushforwardModulesIsoOfStructure`: the comparison of the
  direct images of modules, given the identity
  `smallerBaseStructureSharpLeft = smallerBaseStructureSharpRight` of the structure maps.

## The identity of the structure maps

It is proved in `StacksFrontier/AlgebraicGeometry/Spaces/SmallerBaseStructureSharp.lean`
(`AlgebraicGeometry.Space.smallerBaseStructureSharpLeft_eq_right`), chart by chart, which gives
the comparison unconditionally (`AlgebraicGeometry.Space.smallerBaseModulePushforwardIso`).

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Sheaves.ToposPullback

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS) {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B S hS}
  (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)

/-- The change of base on sheaves of sets: restriction along the equivalence of small étale
sites `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso`. -/
abbrev smallerBaseSheafRestriction :
    Sheaf (SmallEtale.topology B S hS Y.1) (Type u) ⥤ Sheaf (SmallEtale.topology B W hW Z.1)
        (Type u) :=
  (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor.sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B W hW Z.1) (SmallEtale.topology B S hS Y.1)

/-- **The change of base of modules is an inverse image of modules**: the functor of
`AlgebraicGeometry.Space.smallerBaseModulesEquivalenceOfIso` is the inverse image of modules of
Stacks 03D1 along the change of base of sheaves of sets, read over the structure sheaf of `Z`
through `Stacks.Sheaves.ToposPullback.restrictionRingIso`. -/
def smallerBaseModulesEquivalenceIsoPullback :
    (smallerBaseModulesEquivalenceOfIso B h ε).functor ≅
      pullbackModuleFunctor (SmallEtale.topology B W hW Z.1) (smallerBaseSheafRestriction B h ε)
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⋙
        SheafOfModules.restrictScalars (restrictionRingIso (SmallEtale.topology B W hW Z.1)
          (SmallEtale.topology B S hS Y.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).inv :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (Stacks.Sheaves.RingedPoint.sheafRestrictScalarsCompIsoId
      (restrictionRingIso (SmallEtale.topology B W hW Z.1)
          (SmallEtale.topology B S hS Y.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).hom
      (restrictionRingIso (SmallEtale.topology B W hW Z.1)
          (SmallEtale.topology B S hS Y.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).inv
      (Iso.inv_hom_id _)).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictionModuleIso (SmallEtale.topology B W hW Z.1)
      (SmallEtale.topology B S hS Y.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).symm
      (SheafOfModules.restrictScalars (restrictionRingIso (SmallEtale.topology B W hW Z.1)
          (SmallEtale.topology B S hS Y.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).inv)

section RestrictScalars

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R₁ R₂ R₃ : Sheaf J RingCat.{u}}

/-- Restriction of scalars along `b` and then along `a` is restriction of scalars along `a ≫ b`.
Stated at plain variables, where it holds on the nose, so that a consumer at large concrete
rings instantiates it instead of unfolding both sides. -/
def smallerBaseRestrictScalarsCompIso (a : R₁ ⟶ R₂) (b : R₂ ⟶ R₃) :
    SheafOfModules.restrictScalars.{u} b ⋙ SheafOfModules.restrictScalars.{u} a ≅
      SheafOfModules.restrictScalars.{u} (a ≫ b) :=
  Iso.refl _

end RestrictScalars

section DirectImage

variable {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B S hS}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
  {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂}
  (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)

/-- The structure map `g♯`, carried over to `Z₂`: the composite
`𝒪_{Z₂} ≅ (−)'𝒪_{Y₂} ⟶ (−)'g_*𝒪_{Y₁} ≅ f_*(−)'𝒪_{Y₁}` of the change of base of `g♯` with the
comparison `AlgebraicGeometry.Space.smallerBaseSmallEtaleDirectImageIso`, as a morphism of sheaves
of rings. -/
abbrev smallerBaseStructureSharpLeft :
    ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)).obj
        (structureRingSheaf B S hS Y₂) ⟶
      pullbackRingSheaf (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f)
        (pullbackRingSheaf (SmallEtale.topology B W hW Z₁.1) (smallerBaseSheafRestriction B h ε₁)
          (structureRingSheaf B S hS Y₁)) :=
  ((((restrictionRingIso (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
      (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor (structureRingSheaf B S hS Y₂)).inv ≫
      (pullbackRingSheafMap (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂)
      (structureSharp B S hS g))) ≫ (pullbackRingSheafCompIso (SmallEtale.topology B W hW Z₂.1)
      (SmallEtale.topology B S hS Y₂.1) (smallerBaseSheafRestriction B h ε₂)
      (smallEtaleDirectImage B S hS g) (structureRingSheaf B S hS Y₁)).hom) ≫
      (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B W hW Z₂.1)
      (structureRingSheaf B S hS Y₁) (smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom)) ≫
      (pullbackRingSheafCompIso (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B W hW Z₁.1)
      (smallEtaleDirectImage B W hW f) (smallerBaseSheafRestriction B h ε₁)
      (structureRingSheaf B S hS Y₁)).inv

/-- The structure map `f♯`, read over the change of base of `𝒪_{Y₁}`. -/
abbrev smallerBaseStructureSharpRight :
    ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)).obj
        (structureRingSheaf B S hS Y₂) ⟶
      pullbackRingSheaf (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f)
        (pullbackRingSheaf (SmallEtale.topology B W hW Z₁.1) (smallerBaseSheafRestriction B h ε₁)
          (structureRingSheaf B S hS Y₁)) :=
  structureSharp B W hW f ≫
    pullbackRingSheafMap (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f)
      (restrictionRingIso (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)
        (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor (structureRingSheaf B S hS Y₁)).inv

/-- The change of base followed by the direct image of modules along `f`, in normal form: the
inverse images of modules along `(−)'` and along `f_*`, followed by restriction of scalars along
`AlgebraicGeometry.Space.smallerBaseStructureSharpRight`. -/
def smallerBasePushforwardRightIso :
    (smallerBaseModulesEquivalenceOfIso B h ε₁).functor ⋙ modulePushforward B W hW f ≅
      ((pullbackModuleFunctor (SmallEtale.topology B W hW Z₁.1) (smallerBaseSheafRestriction B h ε₁)
          (structureRingSheaf B S hS Y₁)) ⋙ (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1)
              (smallEtaleDirectImage B W hW f)
          (pullbackRingSheaf (SmallEtale.topology B W hW Z₁.1) (smallerBaseSheafRestriction B h ε₁)
            (structureRingSheaf B S hS Y₁)))) ⋙
        SheafOfModules.restrictScalars (smallerBaseStructureSharpRight B h ε₁ ε₂) :=
  Functor.isoWhiskerRight (smallerBaseModulesEquivalenceIsoPullback B h ε₁)
      (modulePushforward B W hW f) ≪≫
    Functor.isoWhiskerLeft ((pullbackModuleFunctor (SmallEtale.topology B W hW Z₁.1)
        (smallerBaseSheafRestriction B h ε₁)
          (structureRingSheaf B S hS Y₁)) ⋙ SheafOfModules.restrictScalars (restrictionRingIso
              (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)
          (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor
              (structureRingSheaf B S hS Y₁)).inv)
      (Iso.refl _ : modulePushforward B W hW f ≅
        pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f)
          (((smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor.sheafPushforwardContinuous
              RingCat.{u}
          (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)).obj
          (structureRingSheaf B S hS Y₁)) ⋙
              (SheafOfModules.restrictScalars (structureSharp B W hW f))) ≪≫
    Functor.associator (pullbackModuleFunctor (SmallEtale.topology B W hW Z₁.1)
        (smallerBaseSheafRestriction B h ε₁)
          (structureRingSheaf B S hS Y₁)) (SheafOfModules.restrictScalars (restrictionRingIso
              (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)
          (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor
              (structureRingSheaf B S hS Y₁)).inv)
      (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f)
          (((smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor.sheafPushforwardContinuous
              RingCat.{u}
          (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)).obj
          (structureRingSheaf B S hS Y₁)) ⋙
              (SheafOfModules.restrictScalars (structureSharp B W hW f))) ≪≫
    Functor.isoWhiskerLeft (pullbackModuleFunctor (SmallEtale.topology B W hW Z₁.1)
        (smallerBaseSheafRestriction B h ε₁)
          (structureRingSheaf B S hS Y₁))
      ((Functor.associator (SheafOfModules.restrictScalars
          (restrictionRingIso (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)
          (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor
              (structureRingSheaf B S hS Y₁)).inv)
        (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f)
          (((smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor.sheafPushforwardContinuous
              RingCat.{u}
          (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)).obj
          (structureRingSheaf B S hS Y₁)))
              (SheafOfModules.restrictScalars (structureSharp B W hW f))).symm ≪≫
      Functor.isoWhiskerRight (pullbackModuleFunctorRestrictScalarsIso.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f)
            (restrictionRingIso (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)
          (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor
              (structureRingSheaf B S hS Y₁)).inv)
              (SheafOfModules.restrictScalars (structureSharp B W hW f)) ≪≫
      Functor.associator
          (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f)
          (pullbackRingSheaf (SmallEtale.topology B W hW Z₁.1) (smallerBaseSheafRestriction B h ε₁)
            (structureRingSheaf B S hS Y₁)))
                (SheafOfModules.restrictScalars (pullbackRingSheafMap.{u, u, u, u + 1, u, u + 1}
          (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f) (restrictionRingIso
              (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)
          (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor
              (structureRingSheaf B S hS Y₁)).inv))
              (SheafOfModules.restrictScalars (structureSharp B W hW f))) ≪≫
    (Functor.associator (pullbackModuleFunctor (SmallEtale.topology B W hW Z₁.1)
        (smallerBaseSheafRestriction B h ε₁)
          (structureRingSheaf B S hS Y₁)) (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1)
              (smallEtaleDirectImage B W hW f)
          (pullbackRingSheaf (SmallEtale.topology B W hW Z₁.1) (smallerBaseSheafRestriction B h ε₁)
            (structureRingSheaf B S hS Y₁)))
                ((SheafOfModules.restrictScalars (pullbackRingSheafMap.{u, u, u, u + 1, u, u + 1}
          (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f) (restrictionRingIso
              (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)
          (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor
              (structureRingSheaf B S hS Y₁)).inv)) ⋙
              (SheafOfModules.restrictScalars (structureSharp B W hW f)))).symm ≪≫
    Functor.isoWhiskerLeft ((pullbackModuleFunctor (SmallEtale.topology B W hW Z₁.1)
        (smallerBaseSheafRestriction B h ε₁)
          (structureRingSheaf B S hS Y₁)) ⋙ (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1)
              (smallEtaleDirectImage B W hW f)
          (pullbackRingSheaf (SmallEtale.topology B W hW Z₁.1) (smallerBaseSheafRestriction B h ε₁)
            (structureRingSheaf B S hS Y₁))))
      (smallerBaseRestrictScalarsCompIso (structureSharp B W hW f)
        (pullbackRingSheafMap.{u, u, u, u + 1, u, u + 1}
          (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f) (restrictionRingIso
              (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)
          (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor
              (structureRingSheaf B S hS Y₁)).inv))


/-- The direct image of modules along `g` followed by the change of base, in normal form: the
inverse images of modules along `(−)'` and along `f_*`, followed by restriction of scalars along
`AlgebraicGeometry.Space.smallerBaseStructureSharpLeft`. -/
def smallerBasePushforwardLeftIso :
    modulePushforward B S hS g ⋙ (smallerBaseModulesEquivalenceOfIso B h ε₂).functor ≅
      ((pullbackModuleFunctor (SmallEtale.topology B W hW Z₁.1) (smallerBaseSheafRestriction B h ε₁)
          (structureRingSheaf B S hS Y₁)) ⋙ (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1)
          (smallEtaleDirectImage B W hW f) (pullbackRingSheaf (SmallEtale.topology B W hW Z₁.1)
          (smallerBaseSheafRestriction B h ε₁) (structureRingSheaf B S hS Y₁)))) ⋙
        SheafOfModules.restrictScalars (smallerBaseStructureSharpLeft B h ε₁ ε₂ hfg) :=
  Functor.isoWhiskerLeft (modulePushforward B S hS g)
      (smallerBaseModulesEquivalenceIsoPullback B h ε₂) ≪≫
    Functor.isoWhiskerRight (Iso.refl _ : modulePushforward B S hS g ≅ (pullbackModuleFunctor
        (SmallEtale.topology B S hS Y₂.1) (smallEtaleDirectImage B S hS g)
        (structureRingSheaf B S hS Y₁)) ⋙
        (SheafOfModules.restrictScalars (structureSharp B S hS g))) ((pullbackModuleFunctor
        (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂)
        (structureRingSheaf B S hS Y₂)) ⋙ (SheafOfModules.restrictScalars (restrictionRingIso
        (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
        (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
        (structureRingSheaf B S hS Y₂)).inv)) ≪≫
    Functor.associator (pullbackModuleFunctor (SmallEtale.topology B S hS Y₂.1)
        (smallEtaleDirectImage B S hS g) (structureRingSheaf B S hS Y₁))
        (SheafOfModules.restrictScalars (structureSharp B S hS g)) ((pullbackModuleFunctor
        (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂)
        (structureRingSheaf B S hS Y₂)) ⋙ (SheafOfModules.restrictScalars (restrictionRingIso
        (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
        (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
        (structureRingSheaf B S hS Y₂)).inv)) ≪≫
    Functor.isoWhiskerLeft (pullbackModuleFunctor (SmallEtale.topology B S hS Y₂.1)
        (smallEtaleDirectImage B S hS g) (structureRingSheaf B S hS Y₁)) ((Functor.associator
        (SheafOfModules.restrictScalars (structureSharp B S hS g)) (pullbackModuleFunctor
        (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂)
        (structureRingSheaf B S hS Y₂)) (SheafOfModules.restrictScalars (restrictionRingIso
        (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
        (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
        (structureRingSheaf B S hS Y₂)).inv)).symm ≪≫
      Functor.isoWhiskerRight (pullbackModuleFunctorRestrictScalarsIso.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂)
        (structureSharp B S hS g)) (SheafOfModules.restrictScalars (restrictionRingIso
            (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
            (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
            (structureRingSheaf B S hS Y₂)).inv) ≪≫
      Functor.associator (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1)
          (smallerBaseSheafRestriction B h ε₂) (pullbackRingSheaf (SmallEtale.topology B S hS Y₂.1)
          (smallEtaleDirectImage B S hS g) (structureRingSheaf B S hS Y₁)))
          (SheafOfModules.restrictScalars (pullbackRingSheafMap (SmallEtale.topology B W hW Z₂.1)
          (smallerBaseSheafRestriction B h ε₂) (structureSharp B S hS g)))
          (SheafOfModules.restrictScalars (restrictionRingIso (SmallEtale.topology B W hW Z₂.1)
          (SmallEtale.topology B S hS Y₂.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
          (structureRingSheaf B S hS Y₂)).inv)) ≪≫
    (Functor.associator (pullbackModuleFunctor (SmallEtale.topology B S hS Y₂.1)
        (smallEtaleDirectImage B S hS g) (structureRingSheaf B S hS Y₁)) (pullbackModuleFunctor
        (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂) (pullbackRingSheaf
        (SmallEtale.topology B S hS Y₂.1) (smallEtaleDirectImage B S hS g)
        (structureRingSheaf B S hS Y₁))) ((SheafOfModules.restrictScalars (pullbackRingSheafMap
        (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂)
        (structureSharp B S hS g))) ⋙ (SheafOfModules.restrictScalars (restrictionRingIso
        (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
        (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
        (structureRingSheaf B S hS Y₂)).inv))).symm ≪≫
    Functor.isoWhiskerRight (pullbackModuleCompIso (SmallEtale.topology B W hW Z₂.1)
      (SmallEtale.topology B S hS Y₂.1) (smallerBaseSheafRestriction B h ε₂)
      (smallEtaleDirectImage B S hS g) (structureRingSheaf B S hS Y₁))
          ((SheafOfModules.restrictScalars (pullbackRingSheafMap (SmallEtale.topology B W hW Z₂.1)
          (smallerBaseSheafRestriction B h ε₂) (structureSharp B S hS g))) ⋙
          (SheafOfModules.restrictScalars (restrictionRingIso (SmallEtale.topology B W hW Z₂.1)
          (SmallEtale.topology B S hS Y₂.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
          (structureRingSheaf B S hS Y₂)).inv)) ≪≫
    Functor.associator (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1)
        (smallEtaleDirectImage B S hS g ⋙ smallerBaseSheafRestriction B h ε₂)
        (structureRingSheaf B S hS Y₁)) (SheafOfModules.restrictScalars (pullbackRingSheafCompIso
        (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
        (smallerBaseSheafRestriction B h ε₂) (smallEtaleDirectImage B S hS g)
        (structureRingSheaf B S hS Y₁)).hom) ((SheafOfModules.restrictScalars (pullbackRingSheafMap
        (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂)
        (structureSharp B S hS g))) ⋙ (SheafOfModules.restrictScalars (restrictionRingIso
        (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
        (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
        (structureRingSheaf B S hS Y₂)).inv)) ≪≫
    Functor.isoWhiskerRight (pullbackModuleFunctorIsoOfNatIso (SmallEtale.topology B W hW Z₂.1)
      (structureRingSheaf B S hS Y₁) (smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg)
      (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B W hW Z₂.1)
        (structureRingSheaf B S hS Y₁) (smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom)
      (ringSheafMap_pullbackRingSheafMapOfNatTrans _ _ _)) ((SheafOfModules.restrictScalars
          (pullbackRingSheafCompIso (SmallEtale.topology B W hW Z₂.1)
          (SmallEtale.topology B S hS Y₂.1) (smallerBaseSheafRestriction B h ε₂)
          (smallEtaleDirectImage B S hS g) (structureRingSheaf B S hS Y₁)).hom) ⋙
          ((SheafOfModules.restrictScalars (pullbackRingSheafMap (SmallEtale.topology B W hW Z₂.1)
          (smallerBaseSheafRestriction B h ε₂) (structureSharp B S hS g))) ⋙
          (SheafOfModules.restrictScalars (restrictionRingIso (SmallEtale.topology B W hW Z₂.1)
          (SmallEtale.topology B S hS Y₂.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
          (structureRingSheaf B S hS Y₂)).inv))) ≪≫
    Functor.associator (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1)
        (smallerBaseSheafRestriction B h ε₁ ⋙ smallEtaleDirectImage B W hW f)
        (structureRingSheaf B S hS Y₁)) (SheafOfModules.restrictScalars
        (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B W hW Z₂.1)
        (structureRingSheaf B S hS Y₁) (smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom))
        ((SheafOfModules.restrictScalars (pullbackRingSheafCompIso (SmallEtale.topology B W hW Z₂.1)
        (SmallEtale.topology B S hS Y₂.1) (smallerBaseSheafRestriction B h ε₂)
        (smallEtaleDirectImage B S hS g) (structureRingSheaf B S hS Y₁)).hom) ⋙
        ((SheafOfModules.restrictScalars (pullbackRingSheafMap (SmallEtale.topology B W hW Z₂.1)
        (smallerBaseSheafRestriction B h ε₂) (structureSharp B S hS g))) ⋙
        (SheafOfModules.restrictScalars (restrictionRingIso (SmallEtale.topology B W hW Z₂.1)
        (SmallEtale.topology B S hS Y₂.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
        (structureRingSheaf B S hS Y₂)).inv))) ≪≫
    Functor.isoWhiskerRight ((Functor.rightUnitor (pullbackModuleFunctor
        (SmallEtale.topology B W hW Z₂.1)
        (smallerBaseSheafRestriction B h ε₁ ⋙ smallEtaleDirectImage B W hW f)
        (structureRingSheaf B S hS Y₁))).symm ≪≫
      Functor.isoWhiskerLeft (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1)
          (smallerBaseSheafRestriction B h ε₁ ⋙ smallEtaleDirectImage B W hW f)
          (structureRingSheaf B S hS Y₁)) (Stacks.Sheaves.RingedPoint.sheafRestrictScalarsCompIsoId
        (pullbackRingSheafCompIso (SmallEtale.topology B W hW Z₂.1)
            (SmallEtale.topology B W hW Z₁.1) (smallEtaleDirectImage B W hW f)
            (smallerBaseSheafRestriction B h ε₁) (structureRingSheaf B S hS Y₁)).hom
            (pullbackRingSheafCompIso (SmallEtale.topology B W hW Z₂.1)
            (SmallEtale.topology B W hW Z₁.1) (smallEtaleDirectImage B W hW f)
            (smallerBaseSheafRestriction B h ε₁) (structureRingSheaf B S hS Y₁)).inv
            (Iso.inv_hom_id _)).symm ≪≫
      (Functor.associator (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1)
          (smallerBaseSheafRestriction B h ε₁ ⋙ smallEtaleDirectImage B W hW f)
          (structureRingSheaf B S hS Y₁)) (SheafOfModules.restrictScalars (pullbackRingSheafCompIso
          (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B W hW Z₁.1)
          (smallEtaleDirectImage B W hW f) (smallerBaseSheafRestriction B h ε₁)
          (structureRingSheaf B S hS Y₁)).hom) (SheafOfModules.restrictScalars
          (pullbackRingSheafCompIso (SmallEtale.topology B W hW Z₂.1)
          (SmallEtale.topology B W hW Z₁.1) (smallEtaleDirectImage B W hW f)
          (smallerBaseSheafRestriction B h ε₁) (structureRingSheaf B S hS Y₁)).inv)).symm ≪≫
      Functor.isoWhiskerRight (pullbackModuleCompIso (SmallEtale.topology B W hW Z₂.1)
        (SmallEtale.topology B W hW Z₁.1) (smallEtaleDirectImage B W hW f)
        (smallerBaseSheafRestriction B h ε₁) (structureRingSheaf B S hS Y₁)).symm
            (SheafOfModules.restrictScalars (pullbackRingSheafCompIso
            (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B W hW Z₁.1)
            (smallEtaleDirectImage B W hW f) (smallerBaseSheafRestriction B h ε₁)
            (structureRingSheaf B S hS Y₁)).inv))
      ((SheafOfModules.restrictScalars (pullbackRingSheafMapOfNatTrans
          (SmallEtale.topology B W hW Z₂.1) (structureRingSheaf B S hS Y₁)
          (smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom)) ⋙
          ((SheafOfModules.restrictScalars (pullbackRingSheafCompIso
          (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
          (smallerBaseSheafRestriction B h ε₂) (smallEtaleDirectImage B S hS g)
          (structureRingSheaf B S hS Y₁)).hom) ⋙ ((SheafOfModules.restrictScalars
          (pullbackRingSheafMap (SmallEtale.topology B W hW Z₂.1)
          (smallerBaseSheafRestriction B h ε₂) (structureSharp B S hS g))) ⋙
          (SheafOfModules.restrictScalars (restrictionRingIso (SmallEtale.topology B W hW Z₂.1)
          (SmallEtale.topology B S hS Y₂.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
          (structureRingSheaf B S hS Y₂)).inv)))) ≪≫
    Functor.associator ((pullbackModuleFunctor (SmallEtale.topology B W hW Z₁.1)
        (smallerBaseSheafRestriction B h ε₁) (structureRingSheaf B S hS Y₁)) ⋙
        (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f)
        (pullbackRingSheaf (SmallEtale.topology B W hW Z₁.1) (smallerBaseSheafRestriction B h ε₁)
        (structureRingSheaf B S hS Y₁)))) (SheafOfModules.restrictScalars (pullbackRingSheafCompIso
        (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B W hW Z₁.1)
        (smallEtaleDirectImage B W hW f) (smallerBaseSheafRestriction B h ε₁)
        (structureRingSheaf B S hS Y₁)).inv) ((SheafOfModules.restrictScalars
        (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B W hW Z₂.1)
        (structureRingSheaf B S hS Y₁) (smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom)) ⋙
        ((SheafOfModules.restrictScalars (pullbackRingSheafCompIso (SmallEtale.topology B W hW Z₂.1)
        (SmallEtale.topology B S hS Y₂.1) (smallerBaseSheafRestriction B h ε₂)
        (smallEtaleDirectImage B S hS g) (structureRingSheaf B S hS Y₁)).hom) ⋙
        ((SheafOfModules.restrictScalars (pullbackRingSheafMap (SmallEtale.topology B W hW Z₂.1)
        (smallerBaseSheafRestriction B h ε₂) (structureSharp B S hS g))) ⋙
        (SheafOfModules.restrictScalars (restrictionRingIso (SmallEtale.topology B W hW Z₂.1)
        (SmallEtale.topology B S hS Y₂.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
        (structureRingSheaf B S hS Y₂)).inv)))) ≪≫
    Functor.isoWhiskerLeft ((pullbackModuleFunctor (SmallEtale.topology B W hW Z₁.1)
        (smallerBaseSheafRestriction B h ε₁) (structureRingSheaf B S hS Y₁)) ⋙
        (pullbackModuleFunctor (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f)
        (pullbackRingSheaf (SmallEtale.topology B W hW Z₁.1) (smallerBaseSheafRestriction B h ε₁)
        (structureRingSheaf B S hS Y₁))))
      (Functor.isoWhiskerLeft (SheafOfModules.restrictScalars (pullbackRingSheafCompIso
          (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B W hW Z₁.1)
          (smallEtaleDirectImage B W hW f) (smallerBaseSheafRestriction B h ε₁)
          (structureRingSheaf B S hS Y₁)).inv) (Functor.isoWhiskerLeft
          (SheafOfModules.restrictScalars (pullbackRingSheafMapOfNatTrans
          (SmallEtale.topology B W hW Z₂.1) (structureRingSheaf B S hS Y₁)
          (smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom)) (Functor.isoWhiskerLeft
          (SheafOfModules.restrictScalars (pullbackRingSheafCompIso
          (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
          (smallerBaseSheafRestriction B h ε₂) (smallEtaleDirectImage B S hS g)
          (structureRingSheaf B S hS Y₁)).hom)
          (smallerBaseRestrictScalarsCompIso (restrictionRingIso (SmallEtale.topology B W hW Z₂.1)
              (SmallEtale.topology B S hS Y₂.1)
              (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
              (structureRingSheaf B S hS Y₂)).inv (pullbackRingSheafMap
              (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂)
              (structureSharp B S hS g))))) ≪≫
        Functor.isoWhiskerLeft (SheafOfModules.restrictScalars (pullbackRingSheafCompIso
            (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B W hW Z₁.1)
            (smallEtaleDirectImage B W hW f) (smallerBaseSheafRestriction B h ε₁)
            (structureRingSheaf B S hS Y₁)).inv) (Functor.isoWhiskerLeft
            (SheafOfModules.restrictScalars (pullbackRingSheafMapOfNatTrans
            (SmallEtale.topology B W hW Z₂.1) (structureRingSheaf B S hS Y₁)
            (smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom))
          (smallerBaseRestrictScalarsCompIso ((restrictionRingIso (SmallEtale.topology B W hW Z₂.1)
              (SmallEtale.topology B S hS Y₂.1)
              (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
              (structureRingSheaf B S hS Y₂)).inv ≫ (pullbackRingSheafMap
              (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂)
              (structureSharp B S hS g))) (pullbackRingSheafCompIso
              (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
              (smallerBaseSheafRestriction B h ε₂) (smallEtaleDirectImage B S hS g)
              (structureRingSheaf B S hS Y₁)).hom)) ≪≫
        Functor.isoWhiskerLeft (SheafOfModules.restrictScalars (pullbackRingSheafCompIso
            (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B W hW Z₁.1)
            (smallEtaleDirectImage B W hW f) (smallerBaseSheafRestriction B h ε₁)
            (structureRingSheaf B S hS Y₁)).inv)
          (smallerBaseRestrictScalarsCompIso (((restrictionRingIso (SmallEtale.topology B W hW Z₂.1)
              (SmallEtale.topology B S hS Y₂.1)
              (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
              (structureRingSheaf B S hS Y₂)).inv ≫ (pullbackRingSheafMap
              (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂)
              (structureSharp B S hS g))) ≫ (pullbackRingSheafCompIso
              (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
              (smallerBaseSheafRestriction B h ε₂) (smallEtaleDirectImage B S hS g)
              (structureRingSheaf B S hS Y₁)).hom) (pullbackRingSheafMapOfNatTrans
              (SmallEtale.topology B W hW Z₂.1) (structureRingSheaf B S hS Y₁)
              (smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom)) ≪≫
        smallerBaseRestrictScalarsCompIso ((((restrictionRingIso (SmallEtale.topology B W hW Z₂.1)
            (SmallEtale.topology B S hS Y₂.1) (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor
            (structureRingSheaf B S hS Y₂)).inv ≫ (pullbackRingSheafMap
            (SmallEtale.topology B W hW Z₂.1) (smallerBaseSheafRestriction B h ε₂)
            (structureSharp B S hS g))) ≫ (pullbackRingSheafCompIso
            (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₂.1)
            (smallerBaseSheafRestriction B h ε₂) (smallEtaleDirectImage B S hS g)
            (structureRingSheaf B S hS Y₁)).hom) ≫ (pullbackRingSheafMapOfNatTrans
            (SmallEtale.topology B W hW Z₂.1) (structureRingSheaf B S hS Y₁)
            (smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom)) (pullbackRingSheafCompIso
            (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B W hW Z₁.1)
            (smallEtaleDirectImage B W hW f) (smallerBaseSheafRestriction B h ε₁)
            (structureRingSheaf B S hS Y₁)).inv)


/-- **The direct images of modules commute with the change of base, given the identity of the
structure maps**: for an arbitrary morphism, `g_* ⋙ (−)' ≅ (−)' ⋙ f_*` for the direct images of
modules `AlgebraicGeometry.Space.modulePushforward`, as soon as the structure map `g♯` carried
over to `Z₂` (`AlgebraicGeometry.Space.smallerBaseStructureSharpLeft`) is the structure map `f♯`
(`AlgebraicGeometry.Space.smallerBaseStructureSharpRight`). Both composites are, in normal form,
the inverse images of modules along `(−)'` and along `f_*` followed by restriction of scalars along
these two maps. -/
def smallerBaseModulePushforwardIsoOfStructure
    (hstruct : smallerBaseStructureSharpLeft B h ε₁ ε₂ hfg =
      smallerBaseStructureSharpRight B h ε₁ ε₂) :
    modulePushforward B S hS g ⋙ (smallerBaseModulesEquivalenceOfIso B h ε₂).functor ≅
      (smallerBaseModulesEquivalenceOfIso B h ε₁).functor ⋙ modulePushforward B W hW f :=
  smallerBasePushforwardLeftIso B h ε₁ ε₂ hfg ≪≫
    Functor.isoWhiskerLeft _ (SheafOfModules.restrictScalarsCongr hstruct) ≪≫
    (smallerBasePushforwardRightIso B h ε₁ ε₂).symm

/-- `AlgebraicGeometry.Space.smallerBaseModulePushforwardIsoOfStructure` for the direct images of
modules of the morphisms of small étale ringed topoi, which the derived direct images derive. -/
def smallerBasePushforwardModulesIsoOfStructure
    (hstruct : smallerBaseStructureSharpLeft B h ε₁ ε₂ hfg =
      smallerBaseStructureSharpRight B h ε₁ ε₂) :
    (smallEtaleRingedToposHom B S hS g).pushforwardModules ⋙
        (smallerBaseModulesEquivalenceOfIso B h ε₂).functor ≅
      (smallerBaseModulesEquivalenceOfIso B h ε₁).functor ⋙
        (smallEtaleRingedToposHom B W hW f).pushforwardModules :=
  Functor.isoWhiskerRight (pushforwardModulesIsoModulePushforward B S hS g) _ ≪≫
    smallerBaseModulePushforwardIsoOfStructure B h ε₁ ε₂ hfg hstruct ≪≫
    Functor.isoWhiskerLeft _ (pushforwardModulesIsoModulePushforward B W hW f).symm

end DirectImage

end AlgebraicGeometry.Space

end
