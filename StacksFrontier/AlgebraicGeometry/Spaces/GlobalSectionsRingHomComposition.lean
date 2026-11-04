module

public import StacksFrontier.CategoryTheory.Sites.GlobalSections.GlobalSectionsRingHomComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback

/-!
# The ring map on global functions of a composite of morphisms of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces induces a ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` on global
regular functions, `AlgebraicGeometry.Space.globalSectionsRingHomSite`, read at the small étale
ringed topoi. This ring map is contravariantly functorial, and the two ways round a commutative
square of algebraic spaces induce the same ring map.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardSetCompNatIso`: the comparison `f_* ⋙ g_* ≅ (f ≫ g)_*` of
  the geometric direct images of sheaves of sets along the morphisms of small étale ringed topoi.
* `AlgebraicGeometry.Space.pushforwardModulesCompNatIso`: the comparison
  `f_* ⋙ g_* ≅ (f ≫ g)_*` of direct images of `𝒪`-modules it induces.

## Main results

* `AlgebraicGeometry.Space.fSharpSet_smallEtaleRingedToposModulesHom` and
  `AlgebraicGeometry.Space.fSharpSetComp_smallEtaleRingedToposModulesHom`: the structure map of
  the morphism of small étale ringed topoi is `AlgebraicGeometry.Space.structureSharpSet`, and the
  comparison of the geometric direct images carries the composite structure map to the structure
  map of the composite.
* `AlgebraicGeometry.Space.globalSectionsRingHomSite_comp`: the ring map on global functions is
  contravariantly functorial.
* `AlgebraicGeometry.Space.globalSectionsRingHomSite_sq`: the two ways round a commutative square
  of algebraic spaces induce the same ring map on global functions.

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules (fSharpSet fSharpSetComp fSharpSetComp_eq
  pushforwardModules pushforwardModulesCompIso
  moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- The structure map of the morphism of small étale ringed topoi
`AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom`, on underlying sheaves of sets, is the
structure map `AlgebraicGeometry.Space.structureSharpSet` of sheaves of sets. -/
theorem fSharpSet_smallEtaleRingedToposModulesHom (f : X ⟶ Y) :
    fSharpSet (smallEtaleRingedToposModulesHom B S hS f) = structureSharpSet B S hS f :=
  (AlgebraicGeometry.RingedToposHom.ringFsharp_forget
    (smallEtaleRingedToposHom B S hS f)).trans (forgetRing_map_fSharp B S hS f)

/-- The comparison `f_* ⋙ g_* ≅ (f ≫ g)_*` of the geometric direct images of sheaves of sets
along the morphisms of small étale ringed topoi
`AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom`. -/
noncomputable def pushforwardSetCompNatIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforward ⋙
        (smallEtaleRingedToposModulesHom B S hS g).toToposHom.pushforward ≅
      (smallEtaleRingedToposModulesHom B S hS (f ≫ g)).toToposHom.pushforward :=
  smallToposMorphismTypeU_comp B S hS f g

/-- `AlgebraicGeometry.Space.pushforwardSetCompNatIso` is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, componentwise. -/
theorem pushforwardSetCompNatIso_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (pushforwardSetCompNatIso B S hS f g).hom.app T =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app T := rfl

/-- The composite structure map of the morphisms of small étale ringed topoi of two morphisms of
algebraic spaces is the composite of the two structure maps of sheaves of sets. -/
theorem fSharpSetComp_eq_structureSharpSet (f : X ⟶ Y) (g : Y ⟶ Z) :
    fSharpSetComp (smallEtaleRingedToposModulesHom B S hS f)
        (smallEtaleRingedToposModulesHom B S hS g) =
      structureSharpSet B S hS g ≫
        (smallEtaleDirectImage B S hS g).map (structureSharpSet B S hS f) :=
  congrArg₂ (fun a b ↦ a ≫ (smallEtaleDirectImage B S hS g).map b)
    (fSharpSet_smallEtaleRingedToposModulesHom B S hS g)
    (fSharpSet_smallEtaleRingedToposModulesHom B S hS f)

/-- The comparison of the geometric direct images carries the composite structure map to the
structure map of the composite. -/
theorem fSharpSetComp_smallEtaleRingedToposModulesHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    fSharpSetComp (smallEtaleRingedToposModulesHom B S hS f)
          (smallEtaleRingedToposModulesHom B S hS g) ≫
        (pushforwardSetCompNatIso B S hS f g).hom.app
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS X).O).ringSheaf =
      fSharpSet (smallEtaleRingedToposModulesHom B S hS (f ≫ g)) :=
  (congrArg (fun m ↦ m ≫ (smallToposMorphismTypeU_comp B S hS f g).hom.app
      (structureSetSheaf B S hS X)) (fSharpSetComp_eq_structureSharpSet B S hS f g)).trans
    (((Category.assoc _ _ _).trans (structureSharpSet_comp B S hS f g)).trans
      (fSharpSet_smallEtaleRingedToposModulesHom B S hS (f ≫ g)).symm)

/-- The comparison `f_* ⋙ g_* ≅ (f ≫ g)_*` of direct images of `𝒪`-modules along the morphisms
of small étale ringed topoi, which is `AlgebraicGeometry.Space.pushforwardSetCompNatIso` on
underlying sheaves of sets. -/
noncomputable def pushforwardModulesCompNatIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardModules (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposModulesHom B S hS f) ⋙
        pushforwardModules (X := smallEtaleRingedTopos B S hS Y)
          (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposModulesHom B S hS g) ≅
      pushforwardModules (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposModulesHom B S hS (f ≫ g)) :=
  pushforwardModulesCompIso (smallEtaleRingedToposModulesHom B S hS f)
    (smallEtaleRingedToposModulesHom B S hS g)
    (smallEtaleRingedToposModulesHom B S hS (f ≫ g))
    (pushforwardSetCompNatIso B S hS f g)
    (fSharpSetComp_smallEtaleRingedToposModulesHom B S hS f g)

/-- For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces, the ring map
`Γ(Z, 𝒪_Z) ⟶ Γ(X, 𝒪_X)` on global regular functions attached to `f ≫ g` is the ring map of `g`
followed by that of `f`. -/
theorem globalSectionsRingHomSite_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    globalSectionsRingHomSite B S hS (f ≫ g) =
      (globalSectionsRingHomSite B S hS f).comp (globalSectionsRingHomSite B S hS g) :=
  Stacks.Cohomology.SiteModules.globalSectionsRingHom_natTrans
    (smallEtaleRingedToposModulesHom B S hS f) (smallEtaleRingedToposModulesHom B S hS g)
    (smallEtaleRingedToposModulesHom B S hS (f ≫ g))
    (pushforwardSetCompNatIso B S hS f g).hom
    (pushforwardModulesCompNatIso B S hS f g).hom
    (fun N ↦ moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app
        (smallEtaleRingedToposModulesHom B S hS f)
        (smallEtaleRingedToposModulesHom B S hS g)
        (smallEtaleRingedToposModulesHom B S hS (f ≫ g))
        (pushforwardSetCompNatIso B S hS f g)
        (fSharpSetComp_smallEtaleRingedToposModulesHom B S hS f g) N)

/-- The two ways round a commutative square of algebraic spaces induce the same ring map on
global regular functions. -/
theorem globalSectionsRingHomSite_sq {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X)
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : g' ≫ f = f' ≫ g) :
    (globalSectionsRingHomSite B S hS g').comp (globalSectionsRingHomSite B S hS f) =
      (globalSectionsRingHomSite B S hS f').comp (globalSectionsRingHomSite B S hS g) :=
  ((globalSectionsRingHomSite_comp B S hS g' f).symm.trans
      (congrArg (globalSectionsRingHomSite B S hS (X := X') (Y := Y)) w)).trans
    (globalSectionsRingHomSite_comp B S hS f' g)

end AlgebraicGeometry.Space

end
