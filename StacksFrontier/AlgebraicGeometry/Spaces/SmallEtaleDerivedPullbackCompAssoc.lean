module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangePastingOnRingedTopoi
public import StacksFrontier.CategoryTheory.Adjunction.UniqueCompOfNatIsoRight

/-!
# Associativity of the composition law of derived pullbacks of algebraic spaces

For morphisms `a : W ⟶ X`, `b : X ⟶ Y`, `c : Y ⟶ Z` of algebraic spaces, the two ways of
identifying `Lc^* ⋙ Lb^* ⋙ La^*` with `L(a ≫ b ≫ c)^*` through the composition law of Stacks 0D6D
(`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`) agree.  This is the cocycle
identity behind the compatibilities of the base change map with stacking squares (Stacks 0E46,
0E47).  We also record the composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` of derived direct
images, adjoint to the composition law of derived pullbacks.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleModulePullbackCompIso`: the composition law
  `g^* ⋙ f^* ≅ (f ≫ g)^*` of pullbacks of modules along the morphisms of small étale ringed topoi.
* `AlgebraicGeometry.Space.smallEtaleDerivedPushforwardCompIsoToposHom`: `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleModulePullbackCompIso_assoc`: its cocycle identity.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_assoc`: the cocycle identity
  of Stacks 0D6D for algebraic spaces.
* `AlgebraicGeometry.Space.conjugateEquiv_smallEtaleDerivedModulePullbackCompIso_inv`: the
  composition isomorphism of derived direct images is adjoint to that of derived pullbacks.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pullbackMapHomotopy)

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The composition law of pullbacks of modules -/

section Modules

variable {W X Y Z : AlgebraicSpaces B S hS}

/-- **The composition law of pullbacks of modules** along the morphisms of small étale ringed
topoi: the compositor of Stacks 03D6 followed by the 2-isomorphism of Stacks 03G8 between the
composite of the morphisms of ringed topoi and the morphism of ringed topoi of `f ≫ g`. -/
abbrev smallEtaleModulePullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS Y)
        (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS g).toModulesHom ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f).toModulesHom ≅
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS (f ≫ g)).toModulesHom :=
  (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g)).symm ≪≫ pullbackModulesCompTransport B S hS f g

/-- The composition law of pullbacks of modules is the comparison of left adjoints induced by
the composition law `f_* ⋙ g_* ≅ (f ≫ g)_*` of direct images of modules. -/
theorem smallEtaleModulePullbackCompIso_eq_leftAdjointCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleModulePullbackCompIso B S hS f g =
      Adjunction.leftAdjointCompIso
        (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS g))
        (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS f))
        (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS (f ≫ g)))
        (pushforwardModulesCompAt B S hS f g) :=
  Adjunction.leftAdjointUniq_symm_trans_leftAdjointUniq_ofNatIsoRight _ _ _ _ _ _

/-- **The cocycle identity for the composition law of pullbacks of modules.** -/
theorem smallEtaleModulePullbackCompIso_assoc (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    Functor.isoWhiskerLeft (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS Y)
        (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS c).toModulesHom)
          (smallEtaleModulePullbackCompIso B S hS a b) ≪≫
        smallEtaleModulePullbackCompIso B S hS (a ≫ b) c =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (smallEtaleModulePullbackCompIso B S hS b c)
          (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS W)
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS a).toModulesHom) ≪≫
        smallEtaleModulePullbackCompIso B S hS a (b ≫ c) := by
  simp only [smallEtaleModulePullbackCompIso_eq_leftAdjointCompIso]
  refine Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ ?_
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  exact (pushforwardModulesCompAt_assoc B S hS a b c M).symm

end Modules

/-! ### On homotopy categories -/

section Homotopy

variable {W X Y Z : AlgebraicSpaces B S hS}

/-- Degreewise pullback along a composite is induced by the composition law of pullbacks of
modules. -/
theorem smallEtaleUnderivedPullbackCompIso_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS (f ≫ g))
    smallEtaleUnderivedPullbackCompIso B S hS f g =
      Functor.mapHomotopyCategoryCompIso (smallEtaleModulePullbackCompIso B S hS f g)
        (ComplexShape.up ℤ) := by
  haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS f g)
  haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS (f ≫ g))
  exact Stacks.Homology.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso _ _ _

/-- **The cocycle identity for degreewise pullback** along three composable morphisms of
algebraic spaces, on unbounded homotopy categories. -/
theorem smallEtaleUnderivedPullbackCompIso_assoc (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    Functor.whiskerLeft (smallEtalePullbackMapHomotopy B S hS c)
          (smallEtaleUnderivedPullbackCompIso B S hS a b).hom ≫
        (smallEtaleUnderivedPullbackCompIso B S hS (a ≫ b) c).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (smallEtaleUnderivedPullbackCompIso B S hS b c).hom
          (smallEtalePullbackMapHomotopy B S hS a) ≫
        (smallEtaleUnderivedPullbackCompIso B S hS a (b ≫ c)).hom := by
  rw [smallEtaleUnderivedPullbackCompIso_eq, smallEtaleUnderivedPullbackCompIso_eq,
    smallEtaleUnderivedPullbackCompIso_eq, smallEtaleUnderivedPullbackCompIso_eq]
  exact Stacks.Cohomology.DerivedBaseChangeComposition.mapHomotopyCategoryCompIso_assoc _ _ _ _
    (congrArg Iso.hom (smallEtaleModulePullbackCompIso_assoc B S hS a b c)) _

end Homotopy

/-! ### The cocycle identity of Stacks 0D6D -/

section Derived

variable {W X Y Z : AlgebraicSpaces B S hS}

/-- **The cocycle identity of Stacks 0D6D for algebraic spaces.**  For composable morphisms
`a : W ⟶ X`, `b : X ⟶ Y`, `c : Y ⟶ Z` of algebraic spaces, the two ways of identifying
`Lc^* ⋙ Lb^* ⋙ La^*` with `L(a ≫ b ≫ c)^*` through the composition law agree. -/
theorem smallEtaleDerivedModulePullbackCompIso_assoc (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS c)
          (smallEtaleDerivedModulePullbackCompIso B S hS a b).hom ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS (a ≫ b) c).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (smallEtaleDerivedModulePullbackCompIso B S hS b c).hom
          (smallEtaleDerivedModulePullback B S hS a) ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS a (b ≫ c)).hom :=
  Stacks.Cohomology.DerivedBaseChangeComposition.leftDerived_comparison_assoc
    (smallEtaleDerivedModulePullbackComparison B S hS c)
    (smallEtaleDerivedModulePullbackComparison B S hS b)
    (smallEtaleDerivedModulePullbackComparison B S hS a)
    (smallEtaleDerivedModulePullbackComparison B S hS (b ≫ c))
    (smallEtaleDerivedModulePullbackComparison B S hS (a ≫ b))
    (smallEtaleDerivedModulePullbackComparison B S hS (a ≫ b ≫ c))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (smallEtaleUnderivedPullbackCompIso B S hS b c).hom
    (smallEtaleUnderivedPullbackCompIso B S hS a b).hom
    (smallEtaleUnderivedPullbackCompIso B S hS (a ≫ b) c).hom
    (smallEtaleUnderivedPullbackCompIso B S hS a (b ≫ c)).hom
    (smallEtaleDerivedModulePullbackCompIso B S hS b c).hom
    (smallEtaleDerivedModulePullbackCompIso B S hS a b).hom
    (smallEtaleDerivedModulePullbackCompIso B S hS (a ≫ b) c).hom
    (smallEtaleDerivedModulePullbackCompIso B S hS a (b ≫ c)).hom
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS b c)
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS a b)
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS (a ≫ b) c)
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS a (b ≫ c))
    (smallEtaleUnderivedPullbackCompIso_assoc B S hS a b c)

/-- The cocycle identity of Stacks 0D6D for algebraic spaces, at an object. -/
theorem smallEtaleDerivedModulePullbackCompIso_assoc_app (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (smallEtaleDerivedModulePullbackCompIso B S hS a b).hom.app
          ((smallEtaleDerivedModulePullback B S hS c).obj K) ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS (a ≫ b) c).hom.app K =
      (smallEtaleDerivedModulePullback B S hS a).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS b c).hom.app K) ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS a (b ≫ c)).hom.app K := by
  simpa using NatTrans.congr_app (smallEtaleDerivedModulePullbackCompIso_assoc B S hS a b c) K

end Derived

/-! ### The composition isomorphism of derived direct images -/

section Pushforward

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The composition isomorphism of derived direct images** `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` for
morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces: both are right adjoint to
`L(f ≫ g)^*`, the first through the composition law of Stacks 0D6D. -/
def smallEtaleDerivedPushforwardCompIsoToposHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPushforward (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f) ⋙
      derivedPushforward (X := smallEtaleRingedTopos B S hS Y)
        (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS g) ≅
    derivedPushforward (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS (f ≫ g)) :=
  Adjunction.rightAdjointUniq
    (((smallEtaleDerivedModuleAdjunction B S hS g).comp
      (smallEtaleDerivedModuleAdjunction B S hS f)).ofNatIsoLeft
        (smallEtaleDerivedModulePullbackCompIso B S hS f g))
    (smallEtaleDerivedModuleAdjunction B S hS (f ≫ g))

/-- The composition isomorphism of derived direct images is the conjugate of the inverse of the
composition law of derived pullbacks. -/
theorem conjugateEquiv_smallEtaleDerivedModulePullbackCompIso_inv (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((smallEtaleDerivedModuleAdjunction B S hS g).comp
        (smallEtaleDerivedModuleAdjunction B S hS f))
        (smallEtaleDerivedModuleAdjunction B S hS (f ≫ g))
        (smallEtaleDerivedModulePullbackCompIso B S hS f g).inv =
      (smallEtaleDerivedPushforwardCompIsoToposHom B S hS f g).hom :=
  Stacks.Cohomology.DerivedBaseChangePasting.conjugateEquiv_iso_inv _ _ _

/-- The conjugate of the composition law of derived pullbacks is the inverse of the composition
isomorphism of derived direct images. -/
theorem conjugateEquiv_smallEtaleDerivedModulePullbackCompIso_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (smallEtaleDerivedModuleAdjunction B S hS (f ≫ g))
        ((smallEtaleDerivedModuleAdjunction B S hS g).comp
          (smallEtaleDerivedModuleAdjunction B S hS f))
        (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom =
      (smallEtaleDerivedPushforwardCompIsoToposHom B S hS f g).inv := by
  have h := conjugateEquiv_comm (smallEtaleDerivedModuleAdjunction B S hS (f ≫ g))
    ((smallEtaleDerivedModuleAdjunction B S hS g).comp
      (smallEtaleDerivedModuleAdjunction B S hS f))
    (α := (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom)
    (β := (smallEtaleDerivedModulePullbackCompIso B S hS f g).inv) (Iso.inv_hom_id _)
  rw [conjugateEquiv_smallEtaleDerivedModulePullbackCompIso_inv] at h
  exact (Iso.comp_hom_eq_id _).1 h

end Pushforward

end AlgebraicGeometry.Space

end
