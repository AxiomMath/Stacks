module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleFinitePushforward
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquare
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Inverse image to the big étale topos and derived direct image along a proper morphism

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `f : Y ⟶ X` a proper
morphism of its objects. Stacks 0DGD, part (2), says that
`π_X⁻¹ R f_{small,*} K = R f_{big,*} π_Y⁻¹ K` for `K` in `D⁺(Y_étale)` with torsion cohomology
sheaves.

The source's proof: there is a canonical base-change map `π_X⁻¹ R f_{small,*} ⟶ R f_{big,*} π_Y⁻¹`
(Stacks 07A7); its restriction to the spaces-étale site of every object `g : X' ⟶ X` of the big
site is, by Stacks 0DGA, the base-change map `g⁻¹ R f_* ⟶ R f'_* (g')⁻¹` of Stacks 0DG3 for the
cartesian square `Y' = Y ×_X X'`, which is an isomorphism for `K` bounded below with torsion
cohomology.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleAbelianBaseChange`: the base-change map
  `f_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ f'_*` of abelian sheaves on the spaces-étale sites (Stacks 0DG0's map,
  on abelian sheaves).
* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleDerivedBaseChange`: the base-change map
  `g⁻¹ R f_* ⟶ R f'_* (g')⁻¹` of Stacks 0DG3 on the unbounded derived categories.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleAbelianBaseChange`: the abelian
  base-change map `π_X⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_Y⁻¹`.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleDerivedBaseChange`: the derived
  base-change map `π_X⁻¹ R f_{small,*} ⟶ R f_{big,*} π_Y⁻¹` of Stacks 07A7.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_of_isIso_mapDerivedCategory_smallEtaleRestriction`:
  the restrictions to the spaces-étale sites of all objects of the big site detect isomorphisms
  in the derived category of the big site.
* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_bigToSmallEtaleDerivedBaseChange_app_iff`: Stacks
  0DGD, part (2), at a K-injective complex, reduced to the unit of `R f_{big,*}`. Part (2) itself,
  `AlgebraicGeometry.BigEtaleSpaceSite.isIso_bigToSmallEtaleDerivedBaseChange_app`, is in
  `StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleTorsionDerivedPushforward`, after
  Stacks 0DG3.

## Implementation notes

All derived base-change maps are the descent of the degreewise underived map, followed by the
unit of the target's derived functor, along the universal property of the source as a right
derived functor (`Stacks.Homology.DerivedSquare.derivedSquare`); this is the construction of the
base change map for schemes, `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`. On a
K-injective complex `I` such a map is invertible exactly when the unit of the target's derived
functor is invertible at the image of `I`
(`Stacks.Homology.DerivedSquare.isIso_derivedSquare_app_iff`),
the underived map being invertible by part (1) resp. by Stacks 0DG0.

So part (2) at `I` is the assertion that the unit of `R f_{big,*}` is invertible at `π_Y⁻¹ I`.
Restricted to the spaces-étale site of `g : X' ⟶ X` it becomes the unit of `R f'_{small,*}` at
`(g')⁻¹ I` — the restriction `i_{g'}⁻¹` preserves K-injective complexes (Stacks 0DG8), so it
commutes with the derived direct images (Stacks 0DGA, part (3), in the form of a comparison of
derived-functor units built here) — and that is exactly what Stacks 0DG3 asserts at `I`. No
identification of the two base-change maps is needed, only of the units they factor through.

## References

* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
* [Stacks Project, Tag 0DG3](https://stacks.math.columbia.edu/tag/0DG3)
* [Stacks Project, Tag 0DGA](https://stacks.math.columbia.edu/tag/0DGA)
* [Stacks Project, Tag 0DG8](https://stacks.math.columbia.edu/tag/0DG8)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Homology.DerivedSquare (derivedSquare totalRightDerived totalRightDerivedUnit)
open Stacks.Cohomology.SiteCohomologyPresheaf (totalRightDerivedCompUnit
  isRightDerivedFunctor_totalRightDerived_comp totalRightDerivedCompUnit_app)

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard bigToSmallAbelianInverseImage_additive
  smallEtaleAbelianInverseImage_additive

set_option synthInstance.maxHeartbeats 400000 in
/- Lean v4.35.0: instance search for these limits on presheaves of the big fppf site and on the
Kan extensions defining the big direct image times out; supply them directly. -/
local instance hasLimitsOfSize_presheaf_BigSmallEtaleDerivedProperPushforward :
    HasLimitsOfSize.{0, 0} ((BigFppfOver T.fppfSite S T.fppf_mem)ᵒᵖ ⥤ Type u) := inferInstance

local instance hasLimitsOfShape_presheaf_BigSmallEtaleDerivedProperPushforward (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver T.fppfSite S T.fppf_mem)ᵒᵖ ⥤ Type u) :=
  HasLimitsOfSize.has_limits_of_shape _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of `StructuredArrow` shape in `Ab` is heavy
local instance hasLimitsOfShape_structuredArrow_BigSmallEtaleDerivedProperPushforward
    {X Y : T.Spaces} (f : Y ⟶ X) (V : (Over X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (Over.map f).op) Ab.{u + 1} := inferInstance

/-! ### Detecting isomorphisms on the spaces-étale sites -/

/-- A morphism of abelian sheaves on the big étale site of `X` is an isomorphism as soon as its
restriction to the spaces-étale site of every object `g : X' ⟶ X` is: its value on `g` is the
value of that restriction on the final object. -/
theorem isIso_of_isIso_smallEtaleRestriction_map {X : T.Spaces}
    {M N : Sheaf (T.bigEtaleTopology X) Ab.{u + 1}} (ψ : M ⟶ N)
    (h : ∀ V : Over X, IsIso ((smallEtaleRestriction T V.hom).map ψ)) : IsIso ψ := by
  suffices hV : ∀ V : Over X, IsIso (ψ.hom.app (op V)) by
    have : IsIso ((sheafToPresheaf _ _).map ψ) := NatIso.isIso_of_isIso_app ψ.hom
    exact isIso_of_reflects_iso ψ (sheafToPresheaf _ _)
  intro V
  have h₁ := h V
  have h₂ : IsIso (((smallEtaleRestriction T V.hom).map ψ).hom.app
      (op (Space.SpacesEtale.final T.fppfSite S T.fppf_mem V.left))) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _
      (@Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) _ h₁) _
  let e : (Over.map V.hom).obj ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem
      V.left).obj (Space.SpacesEtale.final T.fppfSite S T.fppf_mem V.left)) ≅ V :=
    Over.isoMk (Iso.refl _) (by simp [Space.SpacesEtale.final])
  exact (NatTrans.isIso_app_iff_of_iso ψ.hom e.op).mp h₂

/-- **The restrictions to the spaces-étale sites detect isomorphisms in the derived category of
the big étale site.** A morphism of `D((Spaces/X)_étale)` whose restriction to the spaces-étale
site of every object of the big site is an isomorphism is an isomorphism: restriction is exact,
so it commutes with the cohomology sheaves, and those are detected by
`AlgebraicGeometry.BigEtaleSpaceSite.isIso_of_isIso_smallEtaleRestriction_map`. -/
theorem isIso_of_isIso_mapDerivedCategory_smallEtaleRestriction {X : T.Spaces}
    {P Q : DerivedCategory (Sheaf (T.bigEtaleTopology X) Ab.{u + 1})} (φ : P ⟶ Q)
    (h : ∀ V : Over X, IsIso ((smallEtaleRestriction T V.hom).mapDerivedCategory.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_smallEtaleRestriction_map T _ fun V => ?_
  exact ((smallEtaleRestriction T V.hom).isIso_mapDerivedCategory_map_iff φ).mp (h V) n

/-! ### The base-change maps -/

/-- The lift to abelian sheaves of an invertible natural transformation of underlying sheaves of
sets is invertible. -/
theorem isIso_liftSheafNatTrans {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] {D : Type*} [Category* D] (J : GrothendieckTopology D)
    (F G : C ⥤ Sheaf J AddCommGrpCat.{u}) [F.Additive] [G.Additive]
    (a : F ⋙ sheafCompose J (forget AddCommGrpCat) ⟶ G ⋙ sheafCompose J (forget AddCommGrpCat))
    [IsIso a] : IsIso (ProEtale.liftSheafNatTrans J F G a) :=
  ⟨ProEtale.liftSheafNatTrans J G F (inv a), by
    ext X U x
    exact ConcreteCategory.congr_hom (CC := fun X : Type u => X)
      (congrArg (fun t => t.hom.app U) (NatTrans.congr_app (IsIso.hom_inv_id a) X)) x, by
    ext X U x
    exact ConcreteCategory.congr_hom (CC := fun X : Type u => X)
      (congrArg (fun t => t.hom.app U) (NatTrans.congr_app (IsIso.inv_hom_id a) X)) x⟩

section Maps

variable {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')

/-- **The base-change map of Stacks 0DG0 on abelian sheaves.** For a cartesian square
`Y' = Y ×_X X'`, the map `f_{small,*} ⋙ g_{small}⁻¹ ⟶ (g'_{small})⁻¹ ⋙ f'_{small,*}` of abelian
sheaves on the spaces-étale sites whose underlying map of sheaves of sets is the base-change map
`AlgebraicGeometry.Space.spacesToposBaseChangeSquare`. -/
def spacesEtaleAbelianBaseChange (sq : IsPullback g' f' f g) :
    smallEtalePushforward T f ⋙
        CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g) ⟶
      CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g') ⋙
        smallEtalePushforward T f' :=
  haveI : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  ProEtale.liftSheafNatTrans (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X') _ _
    (Functor.whiskerLeft
      (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (forget Ab.{u + 1}))
      (Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem g' f' f g sq))

/-- If the base-change map of sheaves of sets is invertible, so is the one of abelian sheaves. -/
theorem isIso_spacesEtaleAbelianBaseChange (sq : IsPullback g' f' f g)
    (h : IsIso (Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem g' f' f g sq)) :
    IsIso (spacesEtaleAbelianBaseChange T f g g' f' sq) := by
  have : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  unfold spacesEtaleAbelianBaseChange
  have : IsIso (Functor.whiskerLeft
      (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (forget Ab.{u + 1}))
      (Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem g' f' f g sq)) :=
    @Functor.isIso_whiskerLeft _ _ _ _ _ _ _ _ _ _ h
  exact @isIso_liftSheafNatTrans _ _ _ _ _ _ _ _ _ _ _ _ this

/-- **The base-change map of Stacks 0DG3.** For a cartesian square `Y' = Y ×_X X'` of algebraic
spaces of the big étale site, the canonical map `g⁻¹ R f_* ⟶ R f'_* (g')⁻¹` of functors on the
unbounded derived categories of abelian sheaves on the spaces-étale sites: the descent of the
abelian base-change map, followed by the unit of `R f'_*`, along the universal property of
`R f_* ⋙ g⁻¹` (as for schemes, `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`). -/
def spacesEtaleDerivedBaseChange (sq : IsPullback g' f' f g) :
    totalRightDerived (smallEtalePushforward T f) ⋙
        (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g)).mapDerivedCategory ⟶
      (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g')).mapDerivedCategory ⋙
        totalRightDerived (smallEtalePushforward T f') :=
  derivedSquare (spacesEtaleAbelianBaseChange T f g g' f' sq)

/-- The abelian base-change map `π_X⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_Y⁻¹`: its underlying map of
sheaves of sets is `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleBaseChange`, followed by
the identification of restriction along `Over.pullback f` with the big direct image. -/
def bigToSmallEtaleAbelianBaseChange :
    smallEtalePushforward T f ⋙
        CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T X) ⟶
      CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T Y) ⋙
        bigEtalePushforward T f :=
  haveI : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  ProEtale.liftSheafNatTrans (T.bigEtaleTopology X) _ _
    (Functor.whiskerLeft
        (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (forget Ab.{u + 1}))
        (bigToSmallEtaleBaseChange T f) ≫
      Functor.whiskerRight (Functor.whiskerLeft
        (CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T Y))
        ((Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso Ab.{u + 1}).inv)
        (sheafCompose (T.bigEtaleTopology X) (forget Ab.{u + 1})))

/-- For `f` proper, granted Stacks 0A3U, the abelian base-change map is the isomorphism of
Stacks 0DGD, part (1), for abelian sheaves. -/
theorem isIso_bigToSmallEtaleAbelianBaseChange
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w)) :
    IsIso (bigToSmallEtaleAbelianBaseChange T f) :=
  (bigToSmallEtaleAbelianPushforwardIso T f hf h0A3U).isIso_hom

/-- **The base-change map of Stacks 07A7 for `π`.** The canonical map
`π_X⁻¹ R f_{small,*} ⟶ R f_{big,*} π_Y⁻¹` of functors on the unbounded derived categories: the
descent of the abelian base-change map, followed by the unit of `R f_{big,*}`, along the universal
property of `R f_{small,*} ⋙ π_X⁻¹`. -/
def bigToSmallEtaleDerivedBaseChange :
    totalRightDerived (smallEtalePushforward T f) ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (bigToSmallEtaleMorphism T X)).mapDerivedCategory ⟶
      (CategoryTheory.Sites.abelianInverseImage
          (bigToSmallEtaleMorphism T Y)).mapDerivedCategory ⋙
        totalRightDerived (bigEtalePushforward T f) :=
  derivedSquare (bigToSmallEtaleAbelianBaseChange T f)

end Maps

/-! ### Restriction to a spaces-étale site and the derived big direct image -/

section Restriction

variable {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')

/-- **Stacks 0DF8 for abelian sheaves, with the big direct image as a Kan extension.** For a
cartesian square `Y' = Y ×_X X'`, restricting the big direct image along `f` to the spaces-étale
site of `X'` is restricting to the spaces-étale site of `Y'` and taking the small direct image
along `f'`. -/
def bigEtalePushforwardRestrictionIso (sq : IsPullback g' f' f g) :
    bigEtalePushforward T f ⋙ smallEtaleRestriction T g ≅
      smallEtaleRestriction T g' ⋙ smallEtalePushforward T f' :=
  Functor.isoWhiskerRight ((Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso Ab.{u + 1})
      (smallEtaleRestriction T g) ≪≫
    bigEtaleAbelianRestrictionBaseChangeIso T f g g' f' sq

/-- The derived-functor unit exhibiting `i_{g'}⁻¹ ⋙ R f'_{small,*}` as a right derived functor of
degreewise `i_{g'}⁻¹ ⋙ f'_{small,*}`. -/
def restrictionThenDerivedPushforwardUnit :
    (smallEtaleRestriction T g').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((smallEtalePushforward T f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ ((smallEtaleRestriction T g').mapDerivedCategory ⋙
        totalRightDerived (smallEtalePushforward T f')) :=
  Functor.whiskerLeft ((smallEtaleRestriction T g').mapHomotopyCategory (ComplexShape.up ℤ))
      (totalRightDerivedUnit (smallEtalePushforward T f')) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (smallEtaleRestriction T g').mapDerivedCategoryFactorsh.inv
      (totalRightDerived (smallEtalePushforward T f')) ≫
    (Functor.associator _ _ _).hom

/-- The component of `restrictionThenDerivedPushforwardUnit` at a complex `M` is the unit of
`R f'_{small,*}` at the restriction of `M`, followed by `R f'_{small,*}` applied to the
comparison between restricting before and after passing to the derived category. -/
theorem restrictionThenDerivedPushforwardUnit_app
    (M : HomotopyCategory (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1}) (ComplexShape.up ℤ)) :
    (restrictionThenDerivedPushforwardUnit T g' f').app M =
      (totalRightDerivedUnit (smallEtalePushforward T f')).app
          (((smallEtaleRestriction T g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        (totalRightDerived (smallEtalePushforward T f')).map
          ((smallEtaleRestriction T g').mapDerivedCategoryFactorsh.inv.app M) := by
  simp [restrictionThenDerivedPushforwardUnit]

/-- Restriction along `i_{g'}` preserves K-injective complexes (Stacks 0DG8), so
`i_{g'}⁻¹ ⋙ R f'_{small,*}` is a right derived functor of degreewise `i_{g'}⁻¹ ⋙ f'_{small,*}`. -/
theorem restrictionThenDerivedPushforward_isRightDerivedFunctor :
    ((smallEtaleRestriction T g').mapDerivedCategory ⋙
        totalRightDerived (smallEtalePushforward T f')).IsRightDerivedFunctor
      (restrictionThenDerivedPushforwardUnit T g' f')
      (HomotopyCategory.quasiIso (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1})
        (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I _ => ?_
  rw [restrictionThenDerivedPushforwardUnit_app]
  have := isKInjective_smallEtaleRestriction T g' I
  have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    ((smallEtalePushforward T f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (totalRightDerived (smallEtalePushforward T f'))
    (totalRightDerivedUnit (smallEtalePushforward T f'))
    (((smallEtaleRestriction T g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this inferInstance

/-- The comparison, on homotopy categories, of degreewise big direct image followed by
restriction to the spaces-étale site of `X'` with degreewise restriction to the spaces-étale
site of `Y'` followed by small direct image along `f'`. -/
def bigEtalePushforwardRestrictionHomotopyIso (sq : IsPullback g' f' f g) :
    ((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        (smallEtaleRestriction T g).mapDerivedCategory ≅
      (smallEtaleRestriction T g').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((smallEtalePushforward T f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ))
      (smallEtaleRestriction T g).mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (bigEtalePushforwardRestrictionIso T f g g' f' sq)
          (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (smallEtaleRestriction T g' ⋙ smallEtalePushforward T f'))
          (ComplexShape.up ℤ)).symm) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

/-- **Stacks 0DGA, part (3), on units.** Restricted to the spaces-étale site of `X'`, the unit of
`R f_{big,*}` at a complex `M` is invertible exactly when the unit of `R f'_{small,*}` is
invertible at the restriction of `M` to the spaces-étale site of `Y'`. The two composites
`R f_{big,*} ⋙ i_g⁻¹` and `i_{g'}⁻¹ ⋙ R f'_{small,*}` are right derived functors of isomorphic
functors, and the isomorphism of derived functors they induce is compatible with the units. -/
theorem isIso_map_totalRightDerivedUnit_bigEtalePushforward_iff (sq : IsPullback g' f' f g)
    (M : HomotopyCategory (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1}) (ComplexShape.up ℤ)) :
    IsIso ((smallEtaleRestriction T g).mapDerivedCategory.map
        ((totalRightDerivedUnit (bigEtalePushforward T f)).app M)) ↔
      IsIso ((totalRightDerivedUnit (smallEtalePushforward T f')).app
        (((smallEtaleRestriction T g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) := by
  have := isRightDerivedFunctor_totalRightDerived_comp
    ((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (smallEtaleRestriction T g).mapDerivedCategory
  have := restrictionThenDerivedPushforward_isRightDerivedFunctor T g' f'
  let τ := bigEtalePushforwardRestrictionHomotopyIso T f g g' f' sq
  have fac := NatTrans.congr_app (Functor.rightDerivedNatTrans_fac
    (totalRightDerived (bigEtalePushforward T f) ⋙ (smallEtaleRestriction T g).mapDerivedCategory)
    ((smallEtaleRestriction T g').mapDerivedCategory ⋙
      totalRightDerived (smallEtalePushforward T f'))
    (totalRightDerivedCompUnit
      ((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (smallEtaleRestriction T g).mapDerivedCategory)
    (restrictionThenDerivedPushforwardUnit T g' f')
    (HomotopyCategory.quasiIso (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1}) (ComplexShape.up ℤ))
    τ.hom) M
  let τD := Functor.rightDerivedNatTrans
    (totalRightDerived (bigEtalePushforward T f) ⋙ (smallEtaleRestriction T g).mapDerivedCategory)
    ((smallEtaleRestriction T g').mapDerivedCategory ⋙
      totalRightDerived (smallEtalePushforward T f'))
    (totalRightDerivedCompUnit
      ((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (smallEtaleRestriction T g).mapDerivedCategory)
    (restrictionThenDerivedPushforwardUnit T g' f')
    (HomotopyCategory.quasiIso (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1}) (ComplexShape.up ℤ))
    τ.hom
  have hτD : IsIso τD := (Functor.rightDerivedNatIso
    (totalRightDerived (bigEtalePushforward T f) ⋙ (smallEtaleRestriction T g).mapDerivedCategory)
    ((smallEtaleRestriction T g').mapDerivedCategory ⋙
      totalRightDerived (smallEtalePushforward T f'))
    (totalRightDerivedCompUnit
      ((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (smallEtaleRestriction T g).mapDerivedCategory)
    (restrictionThenDerivedPushforwardUnit T g' f')
    (HomotopyCategory.quasiIso (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1}) (ComplexShape.up ℤ))
    τ).isIso_hom
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, totalRightDerivedCompUnit_app] at fac
  rw [← isIso_comp_right_iff _ (τD.app (DerivedCategory.Qh.obj M)), fac, isIso_comp_left_iff,
    restrictionThenDerivedPushforwardUnit_app, isIso_comp_right_iff]

end Restriction

/-! ### Stacks 0DGD, part (2) -/

/-- **Stacks 0DG3 at a K-injective complex.** If the abelian base-change map is invertible, then
the derived base-change map `g⁻¹ R f_* ⟶ R f'_* (g')⁻¹` is invertible at a K-injective complex
`I` exactly when the unit of `R f'_*` is invertible at `(g')⁻¹ I`. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_iff {X Y X' Y' : T.Spaces} (f : Y ⟶ X)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    [IsIso (spacesEtaleAbelianBaseChange T f g g' f' sq)]
    (I : CochainComplex (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1}) ℤ) [I.IsKInjective] :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ↔
      IsIso ((totalRightDerivedUnit (smallEtalePushforward T f')).app
        (((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g')).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
  Stacks.Homology.DerivedSquare.isIso_derivedSquare_app_iff _ _
    (Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I)

/-- **Stacks 0DGD, part (2), at a K-injective complex.** If the abelian base-change map
`π_X⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_Y⁻¹` is invertible, then the derived base-change map is
invertible at a K-injective complex `I` exactly when the unit of `R f_{big,*}` is invertible at
`π_Y⁻¹ I`. -/
theorem isIso_bigToSmallEtaleDerivedBaseChange_app_iff {X Y : T.Spaces} (f : Y ⟶ X)
    [IsIso (bigToSmallEtaleAbelianBaseChange T f)]
    (I : CochainComplex (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1}) ℤ) [I.IsKInjective] :
    IsIso ((bigToSmallEtaleDerivedBaseChange T f).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ↔
      IsIso ((totalRightDerivedUnit (bigEtalePushforward T f)).app
        (((CategoryTheory.Sites.abelianInverseImage
          (bigToSmallEtaleMorphism T Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
  Stacks.Homology.DerivedSquare.isIso_derivedSquare_app_iff _ _
    (Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I)

/-- Restricted to the spaces-étale site of `Y'`, the inverse image of a complex along `π_Y` is its
inverse image along `g'_{small}` (Stacks 0DG7, on complexes). -/
def pulledAbelianInverseImageHomotopyIso {Y Y' : T.Spaces} (g' : Y' ⟶ Y)
    (M : HomotopyCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1}) (ComplexShape.up ℤ)) :
    ((smallEtaleRestriction T g').mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (((CategoryTheory.Sites.abelianInverseImage
          (bigToSmallEtaleMorphism T Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≅
      ((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g')).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj M :=
  (Functor.mapHomotopyCategoryCompIso (pulledAbelianInverseImageIso T g')
    (ComplexShape.up ℤ)).app M

/-- The cohomology-sheaf condition of Stacks 0DG3 and 0DGD, part (2): every cohomology sheaf is a
torsion abelian sheaf. -/
abbrev HasTorsionCohomology {Y : T.Spaces}
    (K : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) : Prop :=
  Stacks.Torsion.torsionCohomologyProperty
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) K

end AlgebraicGeometry.BigEtaleSpaceSite

end
