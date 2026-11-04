module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalenceTwoIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModule
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentPullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictBridge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphismsTwoSquare

/-!
# The strict components of a simplicial algebraic space against its degrees

Let `X` be a simplicial algebraic space, `e : (Sh(X_{spaces,étale}), 𝒪_X) ⟶ (Sh(total), 𝒪)` the
equivalence with the total ringed topos of its strict components (case (A) of Stacks 09WE),
`d_n` the inclusion of degree `n`, `g_n` the component morphism of Stacks 0D72 and `realize_n`
the equivalence of the degree-`n` component with `(Sh((X_n)_{spaces,étale}), 𝒪_{X_n})`. This file
shows `e ∘ d_n ≅ g_n ∘ realize_n` (Stacks 0DE7), on derived pullbacks
`Le^* ⋙ Ld_n^* ≅ D(g_n^{-1}) ⋙ L realize_n^*`, and, for an augmentation `a : X → Z` with
`b = a ∘ e⁻¹`, that the degree-`n` component of `Lb^*K` realizes to `La_n^*K`.

## Main definitions

* `SimplicialSpacesEtaleSite.strictDegreeTwoIso`: `e ∘ d_n ≅ g_n ∘ realize_n`.
* `SimplicialSiteSituation.derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree`:
  `Lg_n^* ≅ D(g_n^{-1})`.
* `SimplicialSpacesEtaleSite.strictDegreeDerivedIso`: the square of `strictDegreeTwoIso` on
  derived pullbacks.
* `SimplicialSpacesEtaleSite.strictAugmentationDegreeDerivedIso`:
  `Lb^* ⋙ D(g_n^{-1}) ⋙ L realize_n^* ≅ La_n^*`.

## Main results

* `forgetFSharp_componentRingedToposHom_eq_unit_simplicialSmallEtaleStrictDegree`: the structure
  map of `g_n` is the unit of restriction against right Kan extension.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry.RingedToposHom

open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

-- no global `HasDerivedCategory` instance at this universe
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

/-- The structure map of the component morphism `g_n`, on underlying sheaves of sets, is the
unit of restriction along the component inclusion against right Kan extension. -/
theorem forgetFSharp_componentRingedToposHom_eq_unit_simplicialSmallEtaleStrictDegree
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
    (n : SimplexCategory) :
    forgetFSharp (S.componentRingedToposHom O n) =
      ((componentFunctor S n).sheafAdjunctionCocontinuous (Type u) (S.componentTopology n)
        S.totalTopology).unit.app ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O) :=
  (S.forgetFSharp_componentRingedToposHom O n).trans
    (Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _)

/-- The derived pullback along a component morphism of ringed topoi exists. -/
instance
  hasLeftDerivedFunctor_pullbackOnHomotopy_componentRingedToposHom_simplicialSmallEtaleStrictDegree
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
    (n : SimplexCategory) :
    (pullbackOnHomotopy (S.componentRingedToposHom O n)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := S.totalRingedTopos O)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (S.componentRingedToposHom O n)

/-- **The derived pullback along `g_n` is the derived restriction to the component**:
`Lg_n^* ≅ D(g_n^{-1})`, restriction being exact. -/
def derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) (n : SimplexCategory) :
    derivedPullback (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
        (S.componentRingedToposHom O n) ≅ S.derivedComponentModuleRestriction O n :=
  Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso _ (S.componentModulesRestriction O n)
    (derivedPullback (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
      (S.componentRingedToposHom O n))
    (derivedPullbackComparison (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
      (S.componentRingedToposHom O n))
    (S.componentPullbackModulesRestrictionIso O n)

end CategoryTheory.SimplicialSiteSituation

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

/-- The comparison of total sites, with source spelled as the total category of the
simplicial-site situation. -/
def componentTotalComparison :
    (strictSituation X).totalCategory ⥤ SimplicialSpacesEtaleSite B S hS X :=
  strictTotalComparison X

/-- The comparison of total sites is an equivalence. -/
instance componentTotalComparison_isEquivalence :
    (componentTotalComparison X).IsEquivalence :=
  inferInstanceAs (strictTotalComparison X).IsEquivalence

/-- The comparison of total sites is continuous. -/
instance componentTotalComparison_isContinuous :
    (componentTotalComparison X).IsContinuous (strictSituation X).totalTopology (topology X) :=
  inferInstanceAs ((strictTotalComparison X).IsContinuous (strictSimplicialSite X).totalTopology
    (topology X))

/-- The square of the realization of the degree-`n` strict component, the component inclusion,
the degree inclusion and the comparison of total sites; it commutes. -/
def componentRealizeSquare (n : SimplexCategory) :
    TwoSquare (componentRealize X n)
      (SimplicialSiteSituation.componentFunctor (strictSituation X) n)
      (degreeInclusion X n) (componentTotalComparison X) :=
  (NatIso.ofComponents (F := componentRealize X n ⋙ degreeInclusion X n)
    (G := SimplicialSiteSituation.componentFunctor (strictSituation X) n ⋙
      componentTotalComparison X) (fun _ ↦ Iso.refl _) (fun g ↦
    (Category.comp_id _).trans ((strictTotalComparison_map_componentFunctor X n g).symm.trans
      (Category.id_comp _).symm))).hom

/-- The square of the realization commutes up to an isomorphism. -/
instance componentRealizeSquare_isIso (n : SimplexCategory) :
    IsIso (componentRealizeSquare X n).natTrans :=
  inferInstanceAs (IsIso (NatIso.ofComponents (F := componentRealize X n ⋙ degreeInclusion X n)
    (G := SimplicialSiteSituation.componentFunctor (strictSituation X) n ⋙
      componentTotalComparison X) (fun _ ↦ Iso.refl _) (fun g ↦
    (Category.comp_id _).trans ((strictTotalComparison_map_componentFunctor X n g).symm.trans
      (Category.id_comp _).symm))).hom)

/-- The square of the realization is Guitart exact, its horizontal functors being
equivalences. -/
instance componentRealizeSquare_guitartExact (n : SimplexCategory) :
    (componentRealizeSquare X n).GuitartExact :=
  TwoSquare.guitartExact_of_isEquivalence_of_isIso' _

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- **The comparison with the strict total site restricts degreewise** (Stacks 0DE7):
`e ∘ d_n ≅ g_n ∘ realize_n` as morphisms of ringed topoi
`(Sh((X_n)_{spaces,étale}), 𝒪_{X_n}) ⟶ (Sh(total), 𝒪)`, through the exchange of right Kan
extensions along the Guitart exact square of the realization. -/
def strictDegreeTwoIso (n : SimplexCategory) :
    TwoIso (A := spacesEtaleRingedTopos B S hS (X.obj (op n))) (B := strictRingedTopos X)
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := ringedTopos X) (Z := strictRingedTopos X)
        (strictRingedToposHom X) (degreeRingedToposHom X n))
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (Z := strictRingedTopos X)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n)) where
  e := (Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquareAndMorphismsTwoSquare (Type (u + 1))
    ((strictSituation X).componentTopology n) (SpacesEtale.topology B S hS (X.obj (op n)))
    (strictSituation X).totalTopology (topology X) (componentRealizeSquare X n)).symm
  commutes := by
    refine (eq_whisker
      (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (strictRingedToposHom X) (degreeRingedToposHom X n)) _).trans (Eq.trans ?_
      (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n)).symm)
    open SimplicialSiteSituation in
    rw [forgetFSharp_degreeRingedToposHom,
      forgetFSharp_componentRingedToposHom_eq_unit_simplicialSmallEtaleStrictDegree]
    refine ObjectProperty.hom_ext _ ?_
    have key := ranBaseChange_unit_comp_eq (A := Type (u + 1)) (componentRealizeSquare X n)
      (forgetFSharp (strictRingedToposHom X)).hom
      (𝟙 ((componentRealize X n).op ⋙ (degreeInclusion X n).op ⋙
        ((sheafToPresheaf (topology X) (Type (u + 1))).obj
          ((ringedTopos X).forgetRing.obj (ringedTopos X).O))))
      (forgetFSharp (strictComponentRingedToposHom X n)).hom (fun U ↦ by
        have e1 := ((sheafToPresheaf (topology X) (Type (u + 1))).obj
          ((ringedTopos X).forgetRing.obj (ringedTopos X).O)).map_id
            (op ((componentTotalComparison X).obj
              ((SimplicialSiteSituation.componentFunctor (strictSituation X) n).obj (unop U))))
        refine (congrArg (_ ≫ ·) ((congrArg (· ≫ _) e1).trans (Category.id_comp _))).trans ?_
        exact Category.comp_id _)
    have hid := (SimplicialSiteSituation.componentFunctor (strictSituation X) n).op.ran.map_id
      ((componentRealize X n).op ⋙ (degreeInclusion X n).op ⋙
        ((sheafToPresheaf (topology X) (Type (u + 1))).obj
          ((ringedTopos X).forgetRing.obj (ringedTopos X).O)))
    rw [hid] at key
    simp only at key
    change (forgetFSharp (strictRingedToposHom X)).hom ≫ Functor.whiskerLeft
        (componentTotalComparison X).op
        (((degreeInclusion X n).sheafAdjunctionCocontinuous (Type (u + 1))
          (SpacesEtale.topology B S hS (X.obj (op n))) (topology X)).unit.app
            ((ringedTopos X).forgetRing.obj (structureSheaf X))).hom ≫
        ((Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquareAndMorphismsTwoSquare (Type (u + 1))
            ((strictSituation X).componentTopology n) (SpacesEtale.topology B S hS (X.obj (op n)))
            (strictSituation X).totalTopology (topology X) (componentRealizeSquare X n)).inv.app
              ((spacesEtaleRingedTopos B S hS (X.obj (op n))).forgetRing.obj
                (SpacesEtale.structureSheaf B S hS (X.obj (op n))))).hom =
      (((SimplicialSiteSituation.componentFunctor (strictSituation X) n).sheafAdjunctionCocontinuous
          (Type (u + 1)) ((strictSituation X).componentTopology n)
          (strictSituation X).totalTopology).unit.app
            ((sheafCompose (strictSituation X).totalTopology (forget CommRingCat.{u + 1})).obj
              (strictStructureSheaf X))).hom ≫
        ((((strictSituation X).componentFunctor n).sheafPushforwardCocontinuous
          (Type (u + 1)) ((strictSituation X).componentTopology n)
          (strictSituation X).totalTopology).map
            (forgetFSharp (strictComponentRingedToposHom X n))).hom
    have hX : (((degreeInclusion X n).sheafAdjunctionCocontinuous (Type (u + 1))
          (SpacesEtale.topology B S hS (X.obj (op n))) (topology X)).unit.app
            ((ringedTopos X).forgetRing.obj (structureSheaf X))).hom =
        ((degreeInclusion X n).op.ranAdjunction (Type (u + 1))).unit.app
          ((ringedTopos X).forgetRing.obj (structureSheaf X)).obj :=
      Functor.sheafAdjunctionCocontinuous_unit_app_hom _ _ _ _ _
    have hY : ((((strictSituation X).componentFunctor n).sheafAdjunctionCocontinuous
          (Type (u + 1)) ((strictSituation X).componentTopology n)
          (strictSituation X).totalTopology).unit.app
            ((sheafCompose (strictSituation X).totalTopology (forget CommRingCat.{u + 1})).obj
              (strictStructureSheaf X))).hom =
        ((SimplicialSiteSituation.componentFunctor (strictSituation X) n).op.ranAdjunction
          (Type (u + 1))).unit.app
            ((sheafCompose (strictSituation X).totalTopology (forget CommRingCat.{u + 1})).obj
              (strictStructureSheaf X)).obj :=
      Functor.sheafAdjunctionCocontinuous_unit_app_hom _ _ _ _ _
    rw [hX, hY,
      Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquare_inv_app_hom_andMorphismsTwoSquare]
    exact key

/-- The derived pullback along the comparison with the strict total site exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictRingedToposHom :
    (pullbackOnHomotopy (strictRingedToposHom X)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := strictRingedTopos X)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (strictRingedToposHom X)

/-- The derived pullback along the inclusion of a degree exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_degreeRingedToposHom (n : SimplexCategory) :
    (pullbackOnHomotopy (degreeRingedToposHom X n)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := ringedTopos X)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (degreeRingedToposHom X n)

/-- **The strict comparison restricts degreewise on derived pullbacks**:
`Le^* ⋙ Ld_n^* ≅ D(g_n^{-1}) ⋙ L realize_n^*`, from `strictDegreeTwoIso` and Stacks 0D6D. -/
def strictDegreeDerivedIso (n : SimplexCategory) :
    derivedPullback (X := ringedTopos X) (Y := strictRingedTopos X) (strictRingedToposHom X) ⋙
        derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n))) (Y := ringedTopos X)
          (degreeRingedToposHom X n) ≅
      (strictSituation X).derivedComponentModuleRestriction (strictStructureSheaf X) n ⋙
        derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n) :=
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := ringedTopos X) (Z := strictRingedTopos X)
        (strictRingedToposHom X) (degreeRingedToposHom X n))
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (Z := strictRingedTopos X)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n))
  derivedPullbackCompIso (degreeRingedToposHom X n) (strictRingedToposHom X) ≪≫
    derivedPullbackIsoOfPullbackModulesIso
      (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := ringedTopos X) (Z := strictRingedTopos X)
        (strictRingedToposHom X) (degreeRingedToposHom X n))
      (ψ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (Z := strictRingedTopos X)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n))
      (strictDegreeTwoIso X n).pullbackModulesIso ≪≫
    (derivedPullbackCompIso (strictComponentRingedToposHom X n)
      ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)).symm ≪≫
    Functor.isoWhiskerRight
      ((strictSituation X).derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree
        (strictStructureSheaf X) n) _

section Augmentation

variable {X} {Z : AlgebraicSpaces B S hS} (a : X ⟶ (Functor.const _).obj Z)

/-- The augmentation read on the total site of the strict components:
`b = a ∘ e⁻¹ : (Sh(total), 𝒪) ⟶ (Sh(Z_{spaces,étale}), 𝒪_Z)`. -/
def strictAugmentationRingedToposHom :
    RingedToposHom (strictRingedTopos X) (spacesEtaleRingedTopos B S hS Z) :=
  RingedToposHom.comp (X := strictRingedTopos X) (Y := ringedTopos X)
    (Z := spacesEtaleRingedTopos B S hS Z) (augmentationRingedToposHom a)
    (strictRingedToposHomInverse X)

/-- `b ∘ e ≅ a`: going to the strict total site and back is the identity. -/
def strictAugmentationTwoIso :
    TwoIso (A := ringedTopos X) (B := spacesEtaleRingedTopos B S hS Z)
      (RingedToposHom.comp (X := ringedTopos X) (Y := strictRingedTopos X)
        (Z := spacesEtaleRingedTopos B S hS Z) (strictAugmentationRingedToposHom a)
        (strictRingedToposHom X))
      (augmentationRingedToposHom a) :=
  TwoIso.compInverseCompRingedToposEquivalenceTwoIso (augmentationRingedToposHom a)
    (strictRingedToposHom X)

/-- The derived pullback along the augmentation of the strict total site exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictAugmentationRingedToposHom :
    (pullbackOnHomotopy (strictAugmentationRingedToposHom a)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (strictAugmentationRingedToposHom a)

/-- The derived pullback along the augmentation of `X` exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_augmentationRingedToposHom :
    (pullbackOnHomotopy (augmentationRingedToposHom a)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (augmentationRingedToposHom a)

/-- **The components of `Lb^*K` realize to `La_n^*K`**:
`Lb^* ⋙ D(g_n^{-1}) ⋙ L realize_n^* ≅ La_n^*` for the augmentation `b = a ∘ e⁻¹` of the strict
total site, from `strictDegreeDerivedIso`, `b ∘ e ≅ a` and `a ∘ d_n ≅ a_n` (Stacks 0D6D). -/
def strictAugmentationDegreeDerivedIso (n : SimplexCategory) :
    derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
        (strictAugmentationRingedToposHom a) ⋙
      (strictSituation X).derivedComponentModuleRestriction (strictStructureSheaf X) n ⋙
        derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n) ≅
      derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS Z) (spacesEtaleRingedToposHom (a.app (op n))) :=
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := ringedTopos X) (Y := strictRingedTopos X)
        (Z := spacesEtaleRingedTopos B S hS Z) (strictAugmentationRingedToposHom a)
        (strictRingedToposHom X))
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := ringedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
        (augmentationRingedToposHom a) (degreeRingedToposHom X n))
  Functor.isoWhiskerLeft _ (strictDegreeDerivedIso X n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (derivedPullbackCompIso (strictRingedToposHom X) (strictAugmentationRingedToposHom a) ≪≫
        derivedPullbackIsoOfPullbackModulesIso
          (φ := RingedToposHom.comp (X := ringedTopos X) (Y := strictRingedTopos X)
            (Z := spacesEtaleRingedTopos B S hS Z) (strictAugmentationRingedToposHom a)
            (strictRingedToposHom X))
          (ψ := augmentationRingedToposHom a)
          (strictAugmentationTwoIso a).pullbackModulesIso) _ ≪≫
    derivedPullbackCompIso (degreeRingedToposHom X n) (augmentationRingedToposHom a) ≪≫
    derivedPullbackIsoOfPullbackModulesIso
      (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := ringedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
        (augmentationRingedToposHom a) (degreeRingedToposHom X n))
      (ψ := spacesEtaleRingedToposHom (a.app (op n)))
      (augmentationDegreeTwoIso a n).pullbackModulesIso

end Augmentation

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
