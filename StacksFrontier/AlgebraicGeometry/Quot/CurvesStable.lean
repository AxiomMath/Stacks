module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGeneratingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeOfRankEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence

/-!
# The subcategory of stable curves and the genus of a family of curves

This module carries the vocabulary of Stacks 0E76 and 0E78 that the moduli stacks of stable
curves are built from:

* the strictly full subcategory `Curves^{stable}` of families of curves which are stable in the
  sense of Stacks 0E75, the subcategory which Stacks 0E76 shows to be an open substack of the
  stack of curves;
* the genus condition of Stacks 0E6V, 0E78 and 0E83 on a family of curves `f : X → S`, that
  `R¹f_*𝒪_X` is a locally free `𝒪_S`-module of rank `g`;
* the subcategory `\overline{\mathcal M}_g`-to-be of stable families of genus `g`, the families
  which Stacks 0E78 shows to form an open and closed substack of `Curves^{stable}`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.firstDirectImage`: the first higher direct image `R¹f_*𝒪_X`
  of the structure sheaf of the total space of a family of curves, a module on the small étale
  site of the base.
* `AlgebraicGeometry.CurveFamily.HasGenus`: `R¹f_*𝒪_X` is locally free of rank `g`.
* `AlgebraicGeometry.IsStableCurveFamilyOfGenus`: stable, with `R¹f_*𝒪_X` locally free of
  rank `g`; this is condition (1)(b) of Stacks 0E78.
* `AlgebraicGeometry.CurvesStable`: the strictly full subcategory `Curves^{stable}`.
* `AlgebraicGeometry.CurvesStableOfGenus`: the full subcategory of stable families of genus
  `g`.

## Main results

* `AlgebraicGeometry.CurveFamily.hasGenus_unique`: over a base with a point the genus is unique.
* `AlgebraicGeometry.CurveFamily.firstDirectImageIsoOfIsEtale`: `R¹f_*𝒪_X` commutes with étale
  base change; so `AlgebraicGeometry.CurveFamily.hasGenus_of_hom_of_isEtale`: the genus is
  inherited along étale base change, and `AlgebraicGeometry.CurveFamily.hasGenus_of_iso`: it is
  invariant under isomorphism of families.
* `AlgebraicGeometry.CurveFamily.isPrestableCurveFamily_of_hom`: a family of curves mapping to
  a prestable family is prestable, i.e. prestability is stable under base change.
* `AlgebraicGeometry.CurveFamily.isStableCurveFamily_of_hom`: the same for stability.
* `AlgebraicGeometry.curvesPrestable_isStrictlyFull` and
  `AlgebraicGeometry.curvesStable_isStrictlyFull`: prestability and stability are invariant
  under isomorphism of families, so they cut out strictly full subcategories; so does being
  stable of genus `g` (`AlgebraicGeometry.curvesStableOfGenus_isStrictlyFull`).

## Implementation notes

The direct image is `AlgebraicGeometry.Space.modulePushforward` of Stacks 03LU between the small
étale sites of the total space and of the base, read as an algebraic space; its first right
derived functor exists because modules on the small étale site of an algebraic space have
injective resolutions (`AlgebraicGeometry.Space.hasInjectiveResolutions_modules`). The two local
priority raises on `Abelian` and `EnoughInjectives` are those of
`StacksFrontier/AlgebraicGeometry/Spaces/HigherPushforwardQuasicoherentUnconditional.lean`: without
them instance search commits to module-universe-`max` instances and fails on the universe
constraint.

"Locally free of rank `g`" is `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank` of
Stacks 0409 on the small étale ringed site of the base, i.e. local freeness for the étale
topology of the base scheme. For a quasi-coherent module, which `R¹f_*𝒪_X` is by Stacks 0720,
this is local freeness for the Zariski topology of the base, finite local freeness of a
quasi-coherent module descending along étale (indeed fpqc) coverings (Stacks 05B2). On the small
étale site of a scheme, with the rank kept, this comparison is
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOfRank_associatedModule_iff`.

Prestability and stability are stable under base change: nodality is Stacks 0DSF; the universal
bijectivity of global functions is by definition invariant under base change, because the fibre
product of the source with an algebraic space over its base is the fibre product of the target
with the same algebraic space over the target's base; and a field-valued point of the source's
base is a field-valued point of the target's base whose fibre is the same algebraic space, so
the fibrewise conditions transfer.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

namespace AlgebraicGeometry

universe u

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. -/
local instance (priority := high) {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W) (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### The genus of a family of curves -/

namespace CurveFamily

/-- The first higher direct image `R¹f_*𝒪_X` of the structure sheaf along the structure morphism
`f : X ⟶ S` of a family of curves, as a module on the small étale site of the base. -/
noncomputable def firstDirectImage (X : CurveFamily B hZ) :
    Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2 :=
  have := Space.hasInjectiveResolutions_modules B integerBase hZ X.total.1 X.total.2
  ((Space.modulePushforward B integerBase hZ X.toBase).rightDerived 1).obj
    (Space.structureSheafModule B integerBase hZ X.total)

/-- A family of curves `f : X ⟶ S` *has genus `g`* when `R¹f_*𝒪_X` is a locally free
`𝒪_S`-module of rank `g`. -/
abbrev HasGenus (X : CurveFamily B hZ) (g : ℕ) : Prop :=
  RingedSite.IsFiniteLocallyFreeOfRank
    (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
    (firstDirectImage B hZ X) g

/-- **The genus of a family of curves over a nonempty base is unique**: if `R¹f_*𝒪_X` is locally
free both of rank `g` and of rank `g'` and the base has a point, then `g = g'`. -/
theorem hasGenus_unique {X : CurveFamily B hZ} {g g' : ℕ} (h : HasGenus B hZ X g)
    (h' : HasGenus B hZ X g') (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    g = g' :=
  RingedSite.IsFiniteLocallyFreeOfRank.rank_eq h h' (fun W => Nonempty (Space.chartScheme W))
    (fun W ⟨x⟩ _ hT => Space.exists_mem_nonempty_of_mem_topology B integerBase hZ _ W hT x)
    (fun W ⟨x⟩ => by
      have : Nonempty (⊤ : (Space.chartScheme W).Opens) := ⟨⟨x, trivial⟩⟩
      show Nontrivial Γ(Space.chartScheme W, ⊤)
      infer_instance)
    (U := Space.selfChart B integerBase hZ X.base) ⟨s⟩

end CurveFamily

/-- A family of curves is *stable of genus `g`* when it is stable (Stacks 0E75) and `R¹f_*𝒪_X`
is a locally free `𝒪_S`-module of rank `g`: condition (1)(b) of Stacks 0E78. -/
abbrev IsStableCurveFamilyOfGenus (g : ℕ) (X : CurveFamily B hZ) : Prop :=
  IsStableCurveFamily B hZ X ∧ CurveFamily.HasGenus B hZ X g

/-- The full subcategory `Curves^{stable}` of families of curves which are stable. -/
@[sga "7 I 5.1" "special case"]
abbrev CurvesStable :=
  (show ObjectProperty (CurveFamily B hZ) from IsStableCurveFamily B hZ).FullSubcategory

/-- The full subcategory of families of curves which are stable of genus `g`. -/
abbrev CurvesStableOfGenus (g : ℕ) :=
  (show ObjectProperty (CurveFamily B hZ) from IsStableCurveFamilyOfGenus B hZ g).FullSubcategory

/-! ### Base change of prestability and stability -/

namespace CurveFamily

variable {B hZ}

/-- The fibre product of the total space of a family of curves with an algebraic space over its
base is, over that algebraic space, isomorphic to the fibre product of the total space of any
family it maps to, taken over the composite to that family's base. -/
noncomputable def fiberProductIsoOfHom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    {Z : AlgebraicSpaces B integerBase hZ} (g : Z ⟶ schemeSpace X.base) :
    AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase g ≅
      AlgebraicSpaces.fiberProduct B integerBase hZ Y.toBase (g ≫ schemeSpaceMap φ.baseMap) :=
  ((AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase g).paste_horiz
      φ.cartesian).isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ Y.toBase
      (g ≫ schemeSpaceMap φ.baseMap))

/-- The isomorphism `fiberProductIsoOfHom φ g` commutes with the second projections of the two
fibre products to `Z`. -/
theorem fiberProductIsoOfHom_hom_snd {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    {Z : AlgebraicSpaces B integerBase hZ} (g : Z ⟶ schemeSpace X.base) :
    (fiberProductIsoOfHom φ g).hom ≫
        (ObjectProperty.homMk (pullback.snd Y.toBase.hom (g ≫ schemeSpaceMap φ.baseMap).hom) :
          AlgebraicSpaces.fiberProduct B integerBase hZ Y.toBase (g ≫ schemeSpaceMap φ.baseMap)
            ⟶ Z) =
      ObjectProperty.homMk (pullback.snd X.toBase.hom g.hom) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- Pullback of global functions along an isomorphism of algebraic spaces is bijective. -/
theorem globalFunctionsMap_bijective_of_iso {U V : AlgebraicSpaces B integerBase hZ}
    (e : V ≅ U) :
    Function.Bijective (Space.globalFunctionsMap B integerBase hZ e.hom) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨Space.globalFunctionsMap B integerBase hZ e.inv, fun s => ?_, fun s => ?_⟩ <;>
  rw [← RingHom.comp_apply, ← Space.globalFunctionsMap_comp] <;>
  simp [Space.globalFunctionsMap_id]

/-- The universal bijectivity of global functions passes from a family of curves to every family
of curves mapping to it. -/
theorem hasUniversallyBijectiveGlobalFunctions_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : HasUniversallyBijectiveGlobalFunctions B hZ Y) :
    HasUniversallyBijectiveGlobalFunctions B hZ X := by
  intro Z g
  rw [← fiberProductIsoOfHom_hom_snd φ g, Space.globalFunctionsMap_comp]
  exact (globalFunctionsMap_bijective_of_iso (fiberProductIsoOfHom φ g)).comp
    (hY Z (g ≫ schemeSpaceMap φ.baseMap))

/-- A family of curves mapping to a prestable family of curves is prestable: it is a base change
of it, nodality is stable under base change by Stacks 0DSF, and the universal bijectivity of
global functions is stable under base change by definition. -/
theorem isPrestableCurveFamily_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsPrestableCurveFamily B hZ Y) : IsPrestableCurveFamily B hZ X :=
  have h : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B integerBase hZ⦄ (k : F ⟶ G) =>
        Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ k.hom) :=
    Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B integerBase hZ
  ⟨h.of_isPullback φ.cartesian hY.1, hasUniversallyBijectiveGlobalFunctions_of_hom φ hY.2⟩

/-- A family of curves mapping to a stable family of curves is stable. A field-valued point of
the base of the source is, through the morphism of bases, a field-valued point of the base of
the target, and a presentation of the fibre of the target there is a presentation of the fibre
of the source, the square of the morphism of families being cartesian. -/
theorem isStableCurveFamily_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsStableCurveFamily B hZ Y) : IsStableCurveFamily B hZ X := by
  refine ⟨isPrestableCurveFamily_of_hom φ hY.1, fun p => ?_⟩
  obtain ⟨V, v, q, hq, hgen⟩ := hY.2 (Space.FieldValuedPoint.map B integerBase hZ _
    (schemeSpaceMap φ.baseMap).hom p)
  have hsq := AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian
  have hval : yonedaEquiv.symm (Space.FieldValuedPoint.map B integerBase hZ _
      (schemeSpaceMap φ.baseMap).hom p).value =
        yonedaEquiv.symm p.value ≫ (schemeSpaceMap φ.baseMap).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  rw [hval] at hq
  have hw : q ≫ Y.toBase.hom = (yoneda.map v ≫ yonedaEquiv.symm p.value) ≫
      (schemeSpaceMap φ.baseMap).hom := by
    rw [Category.assoc]
    exact hq.w
  refine ⟨V, v, hsq.lift q (yoneda.map v ≫ yonedaEquiv.symm p.value) hw,
    IsPullback.of_right ?_ (hsq.lift_snd _ _ _) hsq, hgen⟩
  rw [hsq.lift_fst]
  exact hq

/-- The first higher direct image `R¹f_*𝒪_X` commutes with étale base change: for a morphism of
families of curves whose morphism of bases `S' ⟶ S` is étale, `R¹f'_*𝒪_{X'}` is the restriction
of `R¹f_*𝒪_X` to `S'` (Stacks 03LX). -/
noncomputable def firstDirectImageIsoOfIsEtale {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hφ : Space.IsEtale B integerBase hZ (schemeSpaceMap φ.baseMap).hom) :
    firstDirectImage B hZ X ≅
      (Space.etaleModulePullback B integerBase hZ (schemeSpaceMap φ.baseMap) hφ).obj
        (firstDirectImage B hZ Y) :=
  have := Space.hasInjectiveResolutions_modules B integerBase hZ X.total.1 X.total.2
  have := Space.hasInjectiveResolutions_modules B integerBase hZ Y.total.1 Y.total.2
  ((Space.modulePushforward B integerBase hZ X.toBase).rightDerived 1).mapIso
      (Space.etaleModulePullbackStructureSheafModuleIso B integerBase hZ φ.totalMap
        (Space.isEtale_of_isPullback B integerBase hZ X.toBase φ.totalMap
          (schemeSpaceMap φ.baseMap) Y.toBase φ.cartesian.flip hφ)).symm ≪≫
    (Space.moduleHigherPushforwardEtaleBaseChangeIso B integerBase hZ φ.totalMap X.toBase
      Y.toBase (schemeSpaceMap φ.baseMap) φ.cartesian hφ 1).app
        (Space.structureSheafModule B integerBase hZ Y.total)

/-- **The genus is inherited along étale base change**: a family of curves mapping to a family of
genus `g` over an étale morphism of bases has genus `g`. -/
theorem hasGenus_of_hom_of_isEtale {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hφ : Space.IsEtale B integerBase hZ (schemeSpaceMap φ.baseMap).hom) {g : ℕ}
    (h : HasGenus B hZ Y g) : HasGenus B hZ X g :=
  RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ (firstDirectImageIsoOfIsEtale φ hφ).symm
    (Space.isFiniteLocallyFreeOfRank_etaleModulePullback B integerBase hZ _ hφ _ h)

/-- The morphism of bases of an isomorphism of families of curves is étale. -/
theorem isEtale_schemeSpaceMap_baseMap_of_iso {X Y : CurveFamily B hZ} (e : X ≅ Y) :
    Space.IsEtale B integerBase hZ (schemeSpaceMap e.hom.baseMap).hom :=
  have : IsIso e.hom.baseMap := ⟨e.inv.baseMap, congrArg Hom.baseMap e.hom_inv_id,
    congrArg Hom.baseMap e.inv_hom_id⟩
  Space.isEtale_of_isIso B integerBase hZ (yoneda.map e.hom.baseMap)

/-- **The genus is invariant under isomorphism of families of curves.** -/
theorem hasGenus_of_iso {X Y : CurveFamily B hZ} (e : X ≅ Y) {g : ℕ} (h : HasGenus B hZ Y g) :
    HasGenus B hZ X g :=
  hasGenus_of_hom_of_isEtale e.hom (isEtale_schemeSpaceMap_baseMap_of_iso e) h

end CurveFamily

/-- Being stable of genus `g` is invariant under isomorphism of families, so the stable families
of genus `g` form a strictly full subcategory of the category of families of curves. -/
theorem curvesStableOfGenus_isStrictlyFull (g : ℕ) :
    (show ObjectProperty (CurveFamily B hZ) from
      IsStableCurveFamilyOfGenus B hZ g).IsClosedUnderIsomorphisms :=
  ⟨fun e hX => ⟨CurveFamily.isStableCurveFamily_of_hom e.inv hX.1,
    CurveFamily.hasGenus_of_iso e.symm hX.2⟩⟩

/-- Prestability of a family of curves is invariant under isomorphism of families, so the
prestable families form a strictly full subcategory of the category of families of curves. -/
theorem curvesPrestable_isStrictlyFull :
    (show ObjectProperty (CurveFamily B hZ) from
      IsPrestableCurveFamily B hZ).IsClosedUnderIsomorphisms :=
  ⟨fun e hX => CurveFamily.isPrestableCurveFamily_of_hom e.inv hX⟩

/-- Stability of a family of curves is invariant under isomorphism of families, so
`Curves^{stable}` is a strictly full subcategory of the category of families of curves: the
first of the conditions making it an open substack. -/
theorem curvesStable_isStrictlyFull :
    (show ObjectProperty (CurveFamily B hZ) from
      IsStableCurveFamily B hZ).IsClosedUnderIsomorphisms :=
  ⟨fun e hX => CurveFamily.isStableCurveFamily_of_hom e.inv hX⟩

end AlgebraicGeometry

end
