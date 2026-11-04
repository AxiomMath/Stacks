module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.KInjectiveRestrictionAlongOverMap
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RelocalizationBaseChangeModules

/-!
# Base change for the derived direct image along a relocalization, on sheaves of modules

Let `(C, O)` be a ringed site and let
```
  X' --a--> X
  |b        |c
  V         V
  Y' --d--> Y
```
be a cartesian diagram of `C`. Each morphism `f : Z ⟶ W` of `C` gives a relocalization morphism of
ringed topoi `j_{Z/W} : (Sh(C/Z), O|_Z) ⟶ (Sh(C/W), O|_W)`, whose inverse image on sheaves of
modules is restriction along `Over.map f` and whose direct image is
`Stacks.SheafOfModules.Relocalization.pushforward`. This file proves that the derived direct images
satisfy base change over the square:
`Rj_{X/Y,*}` followed by `j_{Y'/Y}^*` is isomorphic to `j_{X'/X}^*` followed by `Rj_{X'/Y',*}`.

The underived statement is
`Stacks.SheafOfModules.Relocalization.nonempty_overMap_comp_pushforward_iso` together with the
coherence
`Stacks.SheafOfModules.Relocalization.structureMapSquare_eq_structureMap`, which identifies the
direct image the square produces with the direct image of the relocalization at `b`. Passing to
derived functors is the argument of Stacks 0EZ0, carried here by the category-general machinery of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Localization/AbelianSheavesOnALocalizedSite.lean`: a
composite of a right derived functor with an exact functor is the right derived functor of the
composite as soon as the unit of the composite is invertible on K-injective complexes, which holds
on both sides because the inverse image is exact and carries K-injective complexes to K-injective
complexes.

## Main results

* `Stacks.Cohomology.Localization.derivedModulesPushforwardBaseChangeIso`: **Stacks 0FN5**, base
  change for the derived direct image of sheaves of modules over a cartesian square of
  relocalizations.

## Implementation notes

The four derived functors and their units are parameters carrying
`CategoryTheory.Functor.IsRightDerivedFunctor` instances, rather than particular constructions:
the statement is then about any choice of right derived functors, which is what a consumer of the
tag applies it to, and it is the shape in which the abelian analogue
`Stacks.Cohomology.Localization.derivedOverPushforwardBaseChangeIso` is stated.

The exactness of the inverse image is
`Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits` and
`Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits`, its preservation of
K-injectivity is `Stacks.Cohomology.Localization.isKInjective_overMap`, and that sheaves of modules
on a site form a Grothendieck abelian category is Mathlib's instance for a small site, which the
slices of a site whose objects and morphisms live in one universe are.

Additivity of the direct image is read off from the underlying sheaf of abelian groups: the
forgetful functor `SheafOfModules.toSheaf` is faithful and additive, and the direct image followed
by it is, by definition, the forgetful functor followed by the direct image of sheaves of abelian
groups, which is additive because it is a right adjoint.

## References

* [Stacks Project, Tag 0FN5](https://stacks.math.columbia.edu/tag/0FN5)
* [Stacks Project, Tag 0EZ0](https://stacks.math.columbia.edu/tag/0EZ0), the same statement for
  sheaves of abelian groups
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3), the underived statement
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u wX wY wU wV

namespace Stacks.Cohomology.Localization

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

/-- Pointwise right Kan extensions along `(Over.map f).op` exist for coefficients in any category
with limits of the size of the site. The universe of the index categories is fixed by the one of
the coefficients, which is why this is stated rather than left to instance search: in a goal whose
coefficient category is still a metavariable the smallness of `Over Z` is resolved at the wrong
universe. -/
local instance hasPointwiseRightKanExtension_op_overMap (A : Type (u + 1)) [Category.{u} A]
    [HasLimitsOfSize.{u, u} A] {Z W : C} (f : Z ⟶ W) (G : (Over Z)ᵒᵖ ⥤ A) :
    (Over.map f).op.HasPointwiseRightKanExtension G :=
  inferInstance

variable (O : Sheaf J RingCat.{u})

/-- **The direct image of sheaves of modules along a relocalization is additive.** Its composite
with the forgetful functor to sheaves of abelian groups is the forgetful functor followed by the
direct image of sheaves of abelian groups, which is additive because it is a right adjoint; the
forgetful functor is faithful and additive, so additivity descends. -/
instance pushforward_additive {Z W : C} (f : Z ⟶ W) :
    (Stacks.SheafOfModules.Relocalization.pushforward J O f).Additive := by
  have h : Stacks.SheafOfModules.Relocalization.pushforward J O f ⋙
        _root_.SheafOfModules.toSheaf.{u} (O.over W)
      = _root_.SheafOfModules.toSheaf.{u} (O.over Z) ⋙
        (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u} (J.over Z) (J.over W) := rfl
  have : (Stacks.SheafOfModules.Relocalization.pushforward J O f ⋙
      _root_.SheafOfModules.toSheaf.{u} (O.over W)).Additive :=
    Functor.additive_of_iso (eqToIso h).symm
  exact Functor.additive_of_comp_faithful _ (_root_.SheafOfModules.toSheaf.{u} (O.over W))

variable {X' X Y' Y : C}

/-- **Stacks 0FN5.** For a cartesian square
```
  X' --a--> X
  |b        |c
  V         V
  Y' --d--> Y
```
of a ringed site `(C, O)`, the inverse image of sheaves of modules along the relocalization at `d`
after the derived direct image along the relocalization at `c` is naturally isomorphic to the
derived direct image along the relocalization at `b` after the inverse image along the
relocalization at `a`.

All four derived functors are arbitrary choices with their canonical transformations from the
corresponding functors on homotopy categories. -/
@[stacks 0FN5]
def derivedModulesPushforwardBaseChangeIso
    (a : X' ⟶ X) (b : X' ⟶ Y') (c : X ⟶ Y) (d : Y' ⟶ Y) (hsq : IsPullback a b c d)
    [HasDerivedCategory.{wX} (_root_.SheafOfModules.{u} (O.over X))]
    [HasDerivedCategory.{wY} (_root_.SheafOfModules.{u} (O.over Y))]
    [HasDerivedCategory.{wU} (_root_.SheafOfModules.{u} (O.over X'))]
    [HasDerivedCategory.{wV} (_root_.SheafOfModules.{u} (O.over Y'))]
    (Rc : DerivedCategory (_root_.SheafOfModules.{u} (O.over X)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (O.over Y)))
    (Rb : DerivedCategory (_root_.SheafOfModules.{u} (O.over X')) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (O.over Y')))
    (Ra : DerivedCategory (_root_.SheafOfModules.{u} (O.over X)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (O.over X')))
    (Rd : DerivedCategory (_root_.SheafOfModules.{u} (O.over Y)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (O.over Y')))
    (αc : homotopyToDerived (Stacks.SheafOfModules.Relocalization.pushforward J O c) ⟶
      DerivedCategory.Qh ⋙ Rc)
    (αb : homotopyToDerived (Stacks.SheafOfModules.Relocalization.pushforward J O b) ⟶
      DerivedCategory.Qh ⋙ Rb)
    (αa : homotopyToDerived (_root_.SheafOfModules.overMap.{u} O a) ⟶ DerivedCategory.Qh ⋙ Ra)
    (αd : homotopyToDerived (_root_.SheafOfModules.overMap.{u} O d) ⟶ DerivedCategory.Qh ⋙ Rd)
    [Rc.IsRightDerivedFunctor αc
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (O.over X)) (ComplexShape.up ℤ))]
    [Rb.IsRightDerivedFunctor αb
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (O.over X')) (ComplexShape.up ℤ))]
    [Ra.IsRightDerivedFunctor αa
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (O.over X)) (ComplexShape.up ℤ))]
    [Rd.IsRightDerivedFunctor αd
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (O.over Y)) (ComplexShape.up ℤ))] :
    Rc ⋙ Rd ≅ Ra ⋙ Rb := by
  let Fc := Stacks.SheafOfModules.Relocalization.pushforward J O c
  let Gd := _root_.SheafOfModules.overMap.{u} O d
  let Ga := _root_.SheafOfModules.overMap.{u} O a
  let Fb := Stacks.SheafOfModules.Relocalization.pushforward J O b
  haveI : PreservesFiniteLimits Gd :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits d
  haveI : PreservesFiniteColimits Gd :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits d
  haveI : PreservesFiniteLimits Ga :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits a
  haveI : PreservesFiniteColimits Ga :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits a
  let αleft := derivedCompositeUnit Fc Gd Rc Rd αc αd
  have hαleft : (Rc ⋙ Rd).IsRightDerivedFunctor αleft
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (O.over X)) (ComplexShape.up ℤ)) := by
    apply derivedComposite_isRightDerived Fc Gd Rc Rd αc αd
    intro I hI
    have : IsIso (αc.app ((HomotopyCategory.quotient
        (_root_.SheafOfModules.{u} (O.over X)) (ComplexShape.up ℤ)).obj I)) :=
      rightDerivedUnit_isIso_app_of_isKInjective
        (Fc.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Rc αc I hI
    have : IsIso αd := exactRightDerivedUnit_isIso Gd Rd αd
    dsimp [derivedCompositeUnit]
    infer_instance
  let αright := derivedCompositeUnit Ga Fb Ra Rb αa αb
  have hαright : (Ra ⋙ Rb).IsRightDerivedFunctor αright
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (O.over X)) (ComplexShape.up ℤ)) := by
    apply derivedComposite_isRightDerived Ga Fb Ra Rb αa αb
    intro I hI
    have : IsIso αa := exactRightDerivedUnit_isIso Ga Ra αa
    let I' := (Ga.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
    have : CochainComplex.IsKInjective I' := isKInjective_overMap J O a I
    have hαb' := rightDerivedUnit_isIso_app_of_isKInjective
      (Fb.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Rb αb I'
      (by infer_instance)
    dsimp [derivedCompositeUnit]
    have hαb : IsIso (αb.app ((Ga.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (_root_.SheafOfModules.{u} (O.over X))
          (ComplexShape.up ℤ)).obj I))) := by
      change IsIso (αb.app ((HomotopyCategory.quotient
        (_root_.SheafOfModules.{u} (O.over X')) (ComplexShape.up ℤ)).obj I'))
      exact hαb'
    have := hαb
    infer_instance
  let e₀ := (Stacks.SheafOfModules.Relocalization.nonempty_overMap_comp_pushforward_iso
    J O hsq).some
  have hfun : (Stacks.SheafOfModules.CocontinuousPushforward.of.{u} (J.over X') (J.over Y')
        (Over.map b) (Stacks.SheafOfModules.structureMapSquare
          (J' := J.over X') (K' := J.over Y')
          (Stacks.SheafOfModules.Relocalization.structureMap J O c)
          (Stacks.Sites.RelocalizationCofinality.overMapSquareEq hsq.toCommSq))).functor = Fb :=
    congrArg (fun φ => (Stacks.SheafOfModules.CocontinuousPushforward.of.{u}
        (J.over X') (J.over Y') (Over.map b) φ).functor)
      (Stacks.SheafOfModules.Relocalization.structureMapSquare_eq_structureMap J O hsq)
  let under : Fc ⋙ Gd ≅ Ga ⋙ Fb :=
    e₀.symm ≪≫ Functor.isoWhiskerLeft Ga (eqToIso hfun)
  let underH :=
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (Fc ⋙ Gd)) (ComplexShape.up ℤ)).symm ≪≫
      Functor.mapHomotopyCategoryCompIso under (ComplexShape.up ℤ)
  let underQ := Functor.isoWhiskerRight underH DerivedCategory.Qh
  exact Functor.rightDerivedNatIso (Rc ⋙ Rd) (Ra ⋙ Rb) αleft αright
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (O.over X)) (ComplexShape.up ℤ)) underQ

end Stacks.Cohomology.Localization

end
