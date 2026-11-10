module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationMapAndFibres

/-!
# The adjunction unit followed by the map from the stalk of a direct image

Let `h : T ⟶ W` be a morphism of schemes and `y` a geometric point of `W`, and write
`T' = T ×_W Spec 𝒪^{sh}_{W,y}` with projections `p : T' ⟶ T` and `q : T' ⟶ Spec 𝒪^{sh}_{W,y}`.
For an object `M` of `D(W_étale)` there are two maps

`M_y ⟶ (Rh_* h⁻¹M)_y ⟶ RΓ(T', p⁻¹h⁻¹M)` and `M_y ⟶ RΓ(T', (q ≫ σ)⁻¹M)`,

where `σ : Spec 𝒪^{sh}_{W,y} ⟶ W` is the structure morphism: the stalk of the unit of
`h⁻¹ ⊣ Rh_*` followed by the map of Tag 0GIX from the stalk of a derived direct image, and the
map of Tag 0GJN for the scheme `T'` over the strict henselization. This file proves that they
agree, up to the composition isomorphism `p⁻¹h⁻¹M ≅ (q ≫ σ)⁻¹M`.

On abelian sheaves this is a triangle identity of `h⁻¹ ⊣ h_*`
(`AlgebraicGeometry.stalk_unit_comp_pushforwardStalkToStrictHenselizationSectionsAb`); on derived
categories each side is computed on the image of a complex by the factorizations of the derived
unit, of the map of Tag 0GIX and of the map of Tag 0GJN through the units of their derivations.

## Main results

* `AlgebraicGeometry.stalk_unit_comp_pushforwardStalkToStrictHenselizationSectionsAb` — the
  identity on abelian sheaves.
* `AlgebraicGeometry.derivedStalk_unit_comp_derivedPushforwardStalkToStrictHenselizationSections`
  — the identity on unbounded derived categories.

## References

* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
* [Stacks Project, Tag 0GJU](https://stacks.math.columbia.edu/tag/0GJU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {T W : Scheme.{u}} (hW : B.Contains W) (h : T ⟶ W)
  (y : GeometricPoint W)

/-- **The unit followed by the map from the stalk, on abelian sheaves.** For an abelian sheaf `F`
on `W`, the stalk at `y` of the unit `F ⟶ h_*h⁻¹F` followed by the map
`(h_*h⁻¹F)_y ⟶ Γ(T', p⁻¹h⁻¹F)` is the map `F_y ⟶ Γ(T', (q ≫ σ)⁻¹F)` of Tag 0GJN followed by the
composition isomorphism. The map from the stalk is the map of Tag 0GJN at `h_*h⁻¹F` followed by
the counit, so this is the naturality of the map of Tag 0GJN and a triangle identity. -/
theorem stalk_unit_comp_pushforwardStalkToStrictHenselizationSectionsAb
    (F : Sheaf (smallEtaleTopology W) Ab.{u + 1}) :
    (smallEtaleStalkAb y.hom).map ((smallEtaleAdjunctionAb h).unit.app F) ≫
        (pushforwardStalkToStrictHenselizationSectionsAb B hW h y).app
          ((smallEtalePullbackAb h).obj F) =
      (etaleStalkToSectionsAb B W hW y
          (strictHenselizationBaseChangeToStrictHenselization B hW h y)).app F ≫
        (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1}).map
          ((strictHenselizationBaseChangePullbackAbCompIso B hW h y).inv.app F) := by
  have hdef : (pushforwardStalkToStrictHenselizationSectionsAb B hW h y).app
        ((smallEtalePullbackAb h).obj F) =
      (etaleStalkToSectionsAb B W hW y
          (strictHenselizationBaseChangeToStrictHenselization B hW h y)).app
          ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb h).obj F)) ≫
        (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1}).map
          ((strictHenselizationBaseChangePullbackAbCompIso B hW h y).inv.app
            ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb h).obj F))) ≫
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1}).map
            ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y)).map
              ((smallEtaleAdjunctionAb h).counit.app ((smallEtalePullbackAb h).obj F))) := by
    simp only [pushforwardStalkToStrictHenselizationSectionsAb, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  let η : F ⟶ (smallEtalePushforwardAb h).obj ((smallEtalePullbackAb h).obj F) :=
    (smallEtaleAdjunctionAb h).unit.app F
  have hnat : (smallEtaleStalkAb y.hom).map η ≫ (etaleStalkToSectionsAb B W hW y
        (strictHenselizationBaseChangeToStrictHenselization B hW h y)).app
          ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb h).obj F)) =
      (etaleStalkToSectionsAb B W hW y
        (strictHenselizationBaseChangeToStrictHenselization B hW h y)).app F ≫
        (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1}).map
          ((smallEtalePullbackAb (strictHenselizationBaseChangeToStrictHenselization B hW h y ≫
            strictHenselizationToBase B W hW y)).map η) :=
    (etaleStalkToSectionsAb B W hW y
      (strictHenselizationBaseChangeToStrictHenselization B hW h y)).naturality η
  have hχ : (smallEtalePullbackAb (strictHenselizationBaseChangeToStrictHenselization B hW h y ≫
        strictHenselizationToBase B W hW y)).map η ≫
      (strictHenselizationBaseChangePullbackAbCompIso B hW h y).inv.app
        ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb h).obj F)) =
      (strictHenselizationBaseChangePullbackAbCompIso B hW h y).inv.app F ≫
        (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y)).map
          ((smallEtalePullbackAb h).map η) :=
    (strictHenselizationBaseChangePullbackAbCompIso B hW h y).inv.naturality η
  have htri : (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y)).map
        ((smallEtalePullbackAb h).map η) ≫
      (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y)).map
        ((smallEtaleAdjunctionAb h).counit.app ((smallEtalePullbackAb h).obj F)) = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact (congrArg (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y)).map
      ((smallEtaleAdjunctionAb h).left_triangle_components F)).trans
      (CategoryTheory.Functor.map_id _ _)
  change (smallEtaleStalkAb y.hom).map η ≫ _ = _
  rw [hdef, reassoc_of% hnat, ← Functor.map_comp, ← Functor.map_comp, reassoc_of% hχ, htri,
    Category.comp_id]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/- As in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationMapAndFibres`, the
preadditive structure of a category of abelian sheaves is read off its abelian structure, so that
the statements below agree on the nose with the generic lemmas about additive functors between
abelian categories which they are proved from. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive

/-- The stalk of the adjunction unit `F ⟶ h_*h⁻¹F`, as a transformation
`F_y ⟶ (h_*h⁻¹F)_y` from the stalk at `y` to its composite with `h⁻¹` and `h_*`. -/
def stalkUnit :
    smallEtaleStalkAb y.hom ⟶ smallEtalePullbackAb h ⋙
      (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom) :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (smallEtaleAdjunctionAb h).unit _ ≫
    (Functor.associator _ _ _).hom

/-- The stalk of the unit followed by the map from the stalk is the map of Tag 0GJN followed by
the composition isomorphism, as transformations
(`AlgebraicGeometry.stalk_unit_comp_pushforwardStalkToStrictHenselizationSectionsAb`). -/
theorem stalkUnit_comp_pushforwardStalkToStrictHenselizationSectionsAb :
    stalkUnit h y ≫ Functor.whiskerLeft (smallEtalePullbackAb h)
        (pushforwardStalkToStrictHenselizationSectionsAb B hW h y) ≫
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (strictHenselizationBaseChangePullbackAbCompIso B hW h y).hom
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1}) =
      etaleStalkToSectionsAb B W hW y
        (strictHenselizationBaseChangeToStrictHenselization B hW h y) := by
  ext F : 2
  have key := stalk_unit_comp_pushforwardStalkToStrictHenselizationSectionsAb B hW h y F
  simp only [stalkUnit, NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Category.id_comp]
  rw [Category.comp_id, reassoc_of% key, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

/-- The degreewise action of the stalk of the unit, on homotopy categories, is the stalk of the
unit of the adjunction on homotopy categories. -/
theorem mapHomotopyCategory_map_unit
    (J : HomotopyCategory (Sheaf (smallEtaleTopology W) Ab.{u + 1}) (.up ℤ)) :
    ((smallEtaleStalkAb y.hom).mapHomotopyCategory (.up ℤ)).map
        ((Adjunction.mapHomotopyCategoryAdjunction (smallEtaleAdjunctionAb h) (.up ℤ)).unit.app
          J) =
      (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp (smallEtaleStalkAb y.hom)
        (smallEtalePullbackAb h) (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom)
        (stalkUnit h y)).app J := by
  rw [Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_app]
  change ((smallEtaleStalkAb y.hom).mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient _ _).map
        (((smallEtaleAdjunctionAb h).mapHomologicalComplexAdjunction
          (ComplexShape.up ℤ)).unit.app J.as)) = _
  rw [Functor.mapHomotopyCategory_map]
  congr 1

/-- The stalk of the unit followed by the map from the stalk, on homotopy categories. -/
theorem stalkUnit_comp_pushforwardStalk_homotopy
    (J : HomotopyCategory (Sheaf (smallEtaleTopology W) Ab.{u + 1}) (.up ℤ)) :
    (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp (smallEtaleStalkAb y.hom)
        (smallEtalePullbackAb h) (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom)
        (stalkUnit h y)).app J ≫
      (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1})
          (pushforwardStalkToStrictHenselizationSectionsAb B hW h y)).app
        (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J) ≫
        ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y))
            Ab.{u + 1}).mapHomotopyCategory (.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso
            (strictHenselizationBaseChangePullbackAbCompIso B hW h y) (.up ℤ)).hom.app J) =
      (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp (smallEtaleStalkAb y.hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToStrictHenselization B hW h y ≫
            strictHenselizationToBase B W hW y))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1})
          (etaleStalkToSectionsAb B W hW y
            (strictHenselizationBaseChangeToStrictHenselization B hW h y))).app J := by
  rw [Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_trans,
    stalkUnit_comp_pushforwardStalkToStrictHenselizationSectionsAb]

/-- The comparison descended by the map of Tag 0GIX from the stalk, written out. -/
private theorem derivedPushforwardStalkToStrictHenselizationSectionsUnit_eq :
    derivedPushforwardStalkToStrictHenselizationSectionsUnit B hW h y =
      Functor.whiskerLeft ((smallEtalePushforwardAb h).mapHomotopyCategory (.up ℤ))
          (Functor.mapDerivedCategoryFactorsh (smallEtaleStalkAb y.hom)).hom ≫
        (Functor.associator ((smallEtalePushforwardAb h).mapHomotopyCategory (.up ℤ))
          ((smallEtaleStalkAb y.hom).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh).inv ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom)) (.up ℤ)).hom
          DerivedCategory.Qh ≫
        Stacks.DerivedFunctor.exactDerivedDescUnit
          (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1})
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y))
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hW h y))
          (pushforwardStalkToStrictHenselizationSectionsAb B hW h y) :=
  rfl

/-- The comparison descended by the map of Tag 0GIX from the stalk, on a complex: the bookkeeping
prefix contributes only the identification of the two actions of the stalk. -/
theorem derivedPushforwardStalkToStrictHenselizationSectionsUnit_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ)) :
    (derivedPushforwardStalkToStrictHenselizationSectionsUnit B hW h y).app J =
      (smallEtaleStalkAb y.hom).mapDerivedCategoryFactorsh.hom.app
          (((smallEtalePushforwardAb h).mapHomotopyCategory (.up ℤ)).obj J) ≫
        (Stacks.DerivedFunctor.exactDerivedDescUnit
          (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1})
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y))
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hW h y))
          (pushforwardStalkToStrictHenselizationSectionsAb B hW h y)).app J := by
  rw [derivedPushforwardStalkToStrictHenselizationSectionsUnit_eq]
  exact Stacks.DerivedFunctor.derivedStalkDescUnit_app (smallEtalePushforwardAb h)
    (smallEtaleStalkAb y.hom)
    (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hW h y) ⋙
      smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y))
    (Stacks.DerivedFunctor.exactDerivedDescUnit
          (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1})
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y))
          (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hW h y))
          (pushforwardStalkToStrictHenselizationSectionsAb B hW h y)) J

/-- The component of the lifted composition isomorphism
`smallEtaleDerivedPullbackAbCompIsoQhLift χ` at the image of a complex `J` is the composite of the
factorization isomorphisms of the pullbacks along `b` and `a` with the image of the composition
isomorphism induced by `χ` on `J`. -/
private theorem compIsoQhLift_hom_app_Qh {Z T₁ T₂ : Scheme.{u}} {b : T₁ ⟶ Z} {a : T₂ ⟶ T₁}
    {c : T₂ ⟶ Z}
    (χ : smallEtalePullbackAb b ⋙ smallEtalePullbackAb a ≅ smallEtalePullbackAb c)
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedPullbackAbCompIsoQhLift χ).hom.app (DerivedCategory.Qh.obj J) =
      (smallEtaleDerivedPullbackAb a).map
          ((smallEtalePullbackAb b).mapDerivedCategoryFactorsh.hom.app J) ≫
        (smallEtalePullbackAb a).mapDerivedCategoryFactorsh.hom.app
            (((smallEtalePullbackAb b).mapHomotopyCategory (.up ℤ)).obj J) ≫
          DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso χ (.up ℤ)).hom.app J) ≫
            (smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J :=
  smallEtaleDerivedPullbackAbCompIsoQhLiftHomApp χ J

/-- **The derived stalk of the unit followed by the map from the stalk, on a complex.** -/
theorem derivedStalk_unit_comp_derivedPushforwardStalk_Qh
    (J : HomotopyCategory (Sheaf (smallEtaleTopology W) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleStalkAb y.hom).mapDerivedCategoryFactorsh.inv.app J ≫
      (smallEtaleDerivedStalkAb y.hom).map
        ((smallEtaleDerivedAdjunctionAb h).unit.app (DerivedCategory.Qh.obj J)) ≫
        (derivedPushforwardStalkToStrictHenselizationSections B hW h y).app
          ((smallEtaleDerivedPullbackAb h).obj (DerivedCategory.Qh.obj J)) ≫
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y)).map
            ((smallEtaleDerivedPullbackAbCompIsoQhLift
              (strictHenselizationBaseChangePullbackAbCompIso B hW h y)).hom.app
                (DerivedCategory.Qh.obj J)) =
      (smallEtaleStalkAb y.hom).mapDerivedCategoryFactorsh.inv.app J ≫
        (vanishingCyclesMap B W hW y
          (strictHenselizationBaseChangeToStrictHenselization B hW h y)).app
          (DerivedCategory.Qh.obj J) := by
  let u : J ⟶ ((smallEtalePushforwardAb h).mapHomotopyCategory (.up ℤ)).obj
      (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J) :=
    (Adjunction.mapHomotopyCategoryAdjunction (smallEtaleAdjunctionAb h) (.up ℤ)).unit.app J
  have hunit : (smallEtaleDerivedAdjunctionAb h).unit.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map u ≫
        (smallEtaleDerivedPushforwardAbUnit h).app
          (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J) ≫
        (smallEtaleDerivedPushforwardAb h).map
          ((smallEtalePullbackAb h).mapDerivedCategoryFactorsh.inv.app J) :=
    smallEtaleDerivedAdjunctionAb_unit_app_Qh h J
  have e2 : DerivedCategory.Qh.map (((smallEtaleStalkAb y.hom).mapHomotopyCategory (.up ℤ)).map u) ≫
      (smallEtaleStalkAb y.hom).mapDerivedCategoryFactorsh.inv.app
        (((smallEtalePushforwardAb h).mapHomotopyCategory (.up ℤ)).obj
          (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J)) =
      (smallEtaleStalkAb y.hom).mapDerivedCategoryFactorsh.inv.app J ≫
        (smallEtaleDerivedStalkAb y.hom).map (DerivedCategory.Qh.map u) :=
    (smallEtaleStalkAb y.hom).mapDerivedCategoryFactorsh.inv.naturality u
  have hX : (smallEtaleDerivedStalkAb y.hom).map ((smallEtaleDerivedPushforwardAb h).map
        ((smallEtalePullbackAb h).mapDerivedCategoryFactorsh.inv.app J)) ≫
      (derivedPushforwardStalkToStrictHenselizationSections B hW h y).app
        ((smallEtaleDerivedPullbackAb h).obj (DerivedCategory.Qh.obj J)) =
      (derivedPushforwardStalkToStrictHenselizationSections B hW h y).app
          (DerivedCategory.Qh.obj (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J)) ≫
        (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y)).map
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hW h y)).map
            ((smallEtalePullbackAb h).mapDerivedCategoryFactorsh.inv.app J)) :=
    (derivedPushforwardStalkToStrictHenselizationSections B hW h y).naturality
      ((smallEtalePullbackAb h).mapDerivedCategoryFactorsh.inv.app J)
  have hfac : (smallEtaleDerivedStalkAb y.hom).map ((smallEtaleDerivedPushforwardAbUnit h).app
        (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J)) ≫
      (derivedPushforwardStalkToStrictHenselizationSections B hW h y).app
        (DerivedCategory.Qh.obj (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J)) =
      (smallEtaleStalkAb y.hom).mapDerivedCategoryFactorsh.hom.app
          (((smallEtalePushforwardAb h).mapHomotopyCategory (.up ℤ)).obj
            (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J)) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom)) (.up ℤ)).hom.app
            (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J)) ≫
        DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom)
          (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1})
          (pushforwardStalkToStrictHenselizationSectionsAb B hW h y)).app
            (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J)) ≫
        (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hW h y)).app
          ((Functor.mapHomotopyCategory
            (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y)) (.up ℤ)).obj
              (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J)) ≫
        (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y)).map
          ((Functor.mapDerivedCategoryFactorsh
            (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y))).inv.app
              (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J)) := by
    rw [Stacks.DerivedFunctor.Qh_map_mapHomotopyCategoryCompIso_refl_hom_app_comp,
      derivedPushforwardStalkToStrictHenselizationSections_fac_app,
      derivedPushforwardStalkToStrictHenselizationSectionsUnit_app,
      Stacks.DerivedFunctor.exactDerivedDescUnit_app]
  have hL := compIsoQhLift_hom_app_Qh
    (strictHenselizationBaseChangePullbackAbCompIso B hW h y) J
  have hΓ := ((smallEtaleDerivedGlobalSectionsUnit
    (strictHenselizationBaseChange B hW h y)).naturality ((Functor.mapHomotopyCategoryCompIso
      (strictHenselizationBaseChangePullbackAbCompIso B hW h y) (.up ℤ)).hom.app J)).symm
  simp only [Functor.comp_map] at hΓ
  have hV : (smallEtaleStalkAb y.hom).mapDerivedCategoryFactorsh.inv.app J ≫
        (vanishingCyclesMap B W hW y
          (strictHenselizationBaseChangeToStrictHenselization B hW h y)).app
          (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtaleStalkAb y.hom)
          (smallEtalePullbackAb
            (strictHenselizationBaseChangeToStrictHenselization B hW h y ≫
              strictHenselizationToBase B W hW y))
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hW h y)) Ab.{u + 1})
          (etaleStalkToSectionsAb B W hW y
            (strictHenselizationBaseChangeToStrictHenselization B hW h y))).app J) ≫
        (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hW h y)).app
            (((smallEtalePullbackAb
              (strictHenselizationBaseChangeToStrictHenselization B hW h y ≫
                strictHenselizationToBase B W hW y)).mapHomotopyCategory (.up ℤ)).obj J) ≫
          (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y)).map
            ((smallEtalePullbackAb
              (strictHenselizationBaseChangeToStrictHenselization B hW h y ≫
                strictHenselizationToBase B W hW y)).mapDerivedCategoryFactorsh.inv.app J) :=
    vanishingCyclesMap_fac_app B W hW y
      (strictHenselizationBaseChangeToStrictHenselization B hW h y) J
  have hc1 := ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y)).mapIso
      ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hW h y)).mapIso
        ((smallEtalePullbackAb h).mapDerivedCategoryFactorsh.app J))).inv_hom_id
  have hc2 := ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y)).mapIso
      ((Functor.mapDerivedCategoryFactorsh
        (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hW h y))).app
          (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J))).inv_hom_id
  simp only [Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom] at hc1 hc2
  have hE9 : ((smallEtaleStalkAb y.hom).mapHomotopyCategory (.up ℤ)).map u ≫
      (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom)) (.up ℤ)).hom.app
        (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J) =
      (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp (smallEtaleStalkAb y.hom)
        (smallEtalePullbackAb h) (smallEtalePushforwardAb h ⋙ smallEtaleStalkAb y.hom)
        (stalkUnit h y)).app J := by
    rw [Stacks.DerivedFunctor.mapHomotopyCategoryCompIso_refl_hom_app]
    exact (Category.comp_id _).trans (mapHomotopyCategory_map_unit h y J)
  have hH := stalkUnit_comp_pushforwardStalk_homotopy B hW h y J
  rw [hunit, hL, hV]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% e2, reassoc_of% hX, reassoc_of% hfac, Iso.inv_hom_id_app_assoc,
    reassoc_of% hc1, reassoc_of% hc2, reassoc_of% hΓ, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hE9, Category.assoc, hH]

/-- **The derived stalk of the unit followed by the map from the stalk of a derived direct
image is the map of Tag 0GJN.** For an object `M` of `D(W_étale)`, the stalk at `y` of the unit
`M ⟶ Rh_* h⁻¹M` of `h⁻¹ ⊣ Rh_*`, followed by the map
`(Rh_* h⁻¹M)_y ⟶ RΓ(T', p⁻¹h⁻¹M)` of Tag 0GIX and the composition isomorphism
`p⁻¹h⁻¹M ≅ (q ≫ σ)⁻¹M`, is the map `M_y ⟶ RΓ(T', (q ≫ σ)⁻¹M)` of Tag 0GJN for the scheme
`T' = T ×_W Spec 𝒪^{sh}_{W,y}` over the strict henselization.

Both sides are transformations out of the degreewise action of the exact stalk functor, which is
a right derived functor of itself, so it suffices that they agree on the image of every complex;
there each is computed through the units of the derivations involved, and the comparison is the
triangle identity of
`AlgebraicGeometry.stalk_unit_comp_pushforwardStalkToStrictHenselizationSectionsAb` applied
degreewise. -/
theorem derivedStalk_unit_comp_derivedPushforwardStalkToStrictHenselizationSections
    (M : smallEtaleDerivedCategory W) :
    (smallEtaleDerivedStalkAb y.hom).map ((smallEtaleDerivedAdjunctionAb h).unit.app M) ≫
      (derivedPushforwardStalkToStrictHenselizationSections B hW h y).app
        ((smallEtaleDerivedPullbackAb h).obj M) ≫
        (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y)).map
          ((smallEtaleDerivedPullbackAbCompIsoQhLift
            (strictHenselizationBaseChangePullbackAbCompIso B hW h y)).hom.app M) =
      (vanishingCyclesMap B W hW y
        (strictHenselizationBaseChangeToStrictHenselization B hW h y)).app M := by
  let γ : smallEtaleDerivedStalkAb y.hom ⟶
      smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToStrictHenselization B hW h y ≫
          strictHenselizationToBase B W hW y) ⋙
        smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hW h y) :=
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (smallEtaleDerivedAdjunctionAb h).unit _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (smallEtaleDerivedPullbackAb h)
        (derivedPushforwardStalkToStrictHenselizationSections B hW h y) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (smallEtaleDerivedPullbackAbCompIsoQhLift
        (strictHenselizationBaseChangePullbackAbCompIso B hW h y)).hom _
  have hγ : γ = vanishingCyclesMap B W hW y
      (strictHenselizationBaseChangeToStrictHenselization B hW h y) := by
    refine Functor.rightDerived_ext (smallEtaleDerivedStalkAb y.hom)
      (smallEtaleStalkAb y.hom).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology W) Ab.{u + 1}) (.up ℤ)) _ _ _ ?_
    ext J
    have := derivedStalk_unit_comp_derivedPushforwardStalk_Qh B hW h y J
    simpa [γ] using this
  have := NatTrans.congr_app hγ M
  simpa [γ] using this

end AlgebraicGeometry

end
