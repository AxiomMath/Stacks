module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFlatInverseImage
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleToposRingedHom
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFaithfullyFlatInverseImage
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleInverseImageReflectsZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCompIso
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackExactFromExtendScalars
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# `ε^*` exists, is exact, and detects the zero sheaf

Let `ε = id_{small, étale, Zar} : S_étale → S_Zar` be the morphism of ringed sites of
Stacks 070R, for a scheme `S`.  Stacks 08H8 asserts four things about it: that it is flat, that
the pullback `ε^* : Mod(𝒪_S) → Mod(𝒪_{S_étale})` exists, that it is exact, and that `ε^*𝓕 = 0`
implies `𝓕 = 0`.  The flatness assertion is
`AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`, which is Stacks 0GNA.
This module supplies the **other three**.

*Existence* is immediate: the pullback of sheaves of modules along an abstract morphism of
ringed topoi comes with its adjunction to the pushforward by construction
(`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`, Stacks 03D7), so `ε_*` has
a left adjoint on the nose.

*Exactness* is the substantive middle assertion, and the bulk of this module.  The argument is
Stacks 04JC, second assertion: the pullback of sheaves of modules along a flat morphism of
ringed topoi is exact.  Two things have to be arranged before it applies.

*The shape of the morphism.*  Exactness of the pullback is available for an
`AlgebraicGeometry.RingedToposHom` — the two-field morphism of ringed topoi of Stacks 01D3 (2),
whose geometric datum is an arbitrary morphism of topoi — at *independent* object universes for
the two sites, which is what `ε` needs, the opens of `S` forming a `Type u` and the small étale
site a `Type (u + 1)`.  `AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom` is `ε` in
that shape.

*The structure map.*  That structure takes the inverse image of sheaves of commutative rings to
be the one transported from the inverse image of sheaves of *sets*, whereas Stacks 0GNA is
proved for Mathlib's pullback of `CommRingCat`-valued sheaves.  The two agree by uniqueness of
left adjoints (`AlgebraicGeometry.SmallEtale.invCommRingIso`), and
`AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom_fSharpInverseImage` says the
structure map of the former is the structure map of the latter read through that comparison.
Flatness does not transport along the comparison without work — it is stated after a universe
lift of the sections — but the only consequence of flatness the exactness proof uses, left
exactness of extension of scalars, does:
`Stacks.Sheaves.RingedToposModules.preservesFiniteLimits_extendScalars_comp_iso`.  So
`Stacks.Sheaves.RingedToposModules.exactFunctor_pullbackModules_of_preservesFiniteLimits`, the
form of Stacks 04JC with that hypothesis in place of flatness, is what is applied.

*Detection of the zero sheaf* splits along the definition of the pullback, which is the inverse
image of Stacks 03D2 followed by extension of scalars along the structure map.  Extension of
scalars reflects the zero object because the structure map is *faithfully* flat, locally, over
the comparison presheaf `(f : V → S) ↦ 𝒪_S(f(V))`
(`AlgebraicGeometry.SmallEtale.locallyFaithfullyFlat_imageSectionsRestriction`), which is what
the declaration
`isZero_of_isZero_extendScalars_obj_of_locallyFaithfullyFlat_comp`
of `Stacks.Sheaves.RingedToposModules`
consumes; and the inverse image reflects it by
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_inverseImageModules`, an elementary argument
turning an étale covering into a Zariski covering of image opens.  The locally bijective map
the first of those asks for is the comparison
`AlgebraicGeometry.SmallEtale.imageSectionsToInverseImageCommRing`, which is the sheafification
unit `(f : V → S) ↦ 𝒪_S(f(V))` `⟶` `ε⁻¹𝒪_{S_Zar}` read through the comparison of the two
constructions of `ε⁻¹` on sheaves of commutative rings.

## Main results

* `AlgebraicGeometry.SmallEtale.isRightAdjoint_toZariskiModulePushforward`: **Stacks 08H8**, the
  existence assertion.
* `AlgebraicGeometry.SmallEtale.exactFunctor_pullbackModules_toZariski`: **Stacks 08H8**, the
  exactness assertion.
* `AlgebraicGeometry.SmallEtale.isZero_of_isZero_toZariskiModulePullback`: **Stacks 08H8**, the
  faithfulness assertion.

## Implementation notes

The functor whose exactness is asserted is the pullback of sheaves of modules along `ε` in the
sense of Stacks 03D6 (2), i.e. the left adjoint of the pushforward — the adjunction is
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` — so it is `ε^*` as the source
means it.  Its identification with the existing associated-module functor
`AlgebraicGeometry.SmallEtale.associatedModule` of Stacks 03DU (4), which
`AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom_fSharpRing` prepares on the pushforward
side, is not carried out here.

## References

* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 0GNA](https://stacks.math.columbia.edu/tag/0GNA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`ε^*` on sheaves of modules**: the pullback of Stacks 03D6 (2) along the abstract morphism
of ringed topoi of `ε = id_{small, étale, Zar} : S_étale → S_Zar`, i.e. the left adjoint of the
pushforward.  Named with its source and target categories spelled out, so that the universes of
the two sites are solved for from the shape of the type. -/
public noncomputable abbrev toZariskiModulePullback :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos B S hS).O) :=
  (toZariskiAbstractRingedToposHom B S hS).toRingedToposModulesHom.pullbackModules

/-- **`ε_*` on sheaves of modules**: the direct image of Stacks 03D6 (1) along the abstract
morphism of ringed topoi of `ε = id_{small, étale, Zar} : S_étale → S_Zar`.  Named with its
source and target categories spelled out, as `AlgebraicGeometry.SmallEtale.toZariskiModulePullback`
is. -/
public noncomputable abbrev toZariskiModulePushforward :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos B S hS).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O) :=
  pushforwardModules (X := ringedTopos B S hS) (Y := S.zariskiRingedTopos)
    (toZariskiAbstractRingedToposHom B S hS).toRingedToposModulesHom

/-- **`ε^*` is left adjoint to `ε_*` on sheaves of modules**, the Stacks 03D7 adjunction of the
abstract morphism of ringed topoi of `ε = id_{small, étale, Zar} : S_étale → S_Zar`. -/
public noncomputable def toZariskiModulePullbackAdjPushforward :
    toZariskiModulePullback B S hS ⊣ toZariskiModulePushforward B S hS :=
  pullbackAdjPushforwardModules
    (toZariskiAbstractRingedToposHom B S hS).toRingedToposModulesHom

/-- **Stacks 08H8, the existence assertion.**  The direct image `ε_*` of sheaves of modules
along `ε = id_{small, étale, Zar} : S_étale → S_Zar` has a left adjoint, i.e. the pullback
`ε^* : Mod(𝒪_S) ⟶ Mod(𝒪_{S_étale})` exists.

The left adjoint is `AlgebraicGeometry.SmallEtale.toZariskiModulePullback` and the adjunction
exhibiting it is `AlgebraicGeometry.SmallEtale.toZariskiModulePullbackAdjPushforward`. -/
@[stacks 08H8 "the existence assertion: the direct image `ε_*` of sheaves of modules along `ε`
  has a left adjoint, i.e. `ε^* : Mod(𝒪_S) ⟶ Mod(𝒪_{S_étale})` exists.  Both functors are
  taken in the sense of Stacks 03D6 for the two-field morphism of ringed topoi of Stacks
  01D3 (2) carrying `ε`, which is the library's spelling of the pair; the left adjoint is
  `AlgebraicGeometry.SmallEtale.toZariskiModulePullback`"]
public theorem isRightAdjoint_toZariskiModulePushforward :
    (toZariskiModulePushforward B S hS).IsRightAdjoint :=
  (toZariskiModulePullbackAdjPushforward B S hS).isRightAdjoint

/-- The structure map of `ε` is the structure map of `inverseImageCommRing` read through the
comparison of the two constructions of `ε⁻¹`. -/
private theorem fSharpInverseImage_hom_eq_comp :
    (toZariskiAbstractRingedToposHom B S hS).fSharpInverseImage.hom =
      ((invCommRingIso B S hS).hom.app S.zariskiCommRingSheaf).hom ≫
        (inverseImageStructureMap B S hS).hom := by
  rw [toZariskiAbstractRingedToposHom_fSharpInverseImage]
  rfl

/-- **Stacks 08H8, the exactness assertion.**  The pullback `ε^*` of sheaves of modules along
`ε = id_{small, étale, Zar} : S_étale → S_Zar` is exact: it preserves finite limits and finite
colimits.

The flatness assertion of the same tag is
`AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`, which is Stacks 0GNA;
the remaining assertion, that `ε^*𝓕 = 0` implies `𝓕 = 0`, is not carried here. -/
@[stacks 08H8 "the exactness assertion: `ε^* : Mod(𝒪_S) ⟶ Mod(𝒪_{S_étale})` is exact, for `ε`
  the morphism of ringed topoi of Equation 75.4.0.1 in the two-field shape of Stacks 01D3 (2).
  The flatness assertion is carried by
  `AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`; the implication
  `ε^*𝓕 = 0 ⟹ 𝓕 = 0` is not carried here"]
public theorem exactFunctor_pullbackModules_toZariski :
    exactFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O))
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos B S hS).O))
      (toZariskiModulePullback B S hS) := by
  refine exactFunctor_pullbackModules_of_preservesFiniteLimits
    (toZariskiAbstractRingedToposHom B S hS) ?_
  have h₂ := extendScalars_preservesFiniteLimits (topology B S hS)
    (inverseImageStructureMap B S hS) (isFlatMapULift_inverseImageStructureMap B S hS)
  rw [fSharpInverseImage_hom_eq_comp B S hS]
  exact preservesFiniteLimits_extendScalars_comp_iso (topology B S hS)
    ((invCommRingIso B S hS).hom.app S.zariskiCommRingSheaf).hom
    (inverseImageStructureMap B S hS).hom _ _ _
    ((sheafCompose (topology B S hS) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
      ((invCommRingIso B S hS).app S.zariskiCommRingSheaf)) rfl h₂

/-! ### `ε^*𝓕 = 0` implies `𝓕 = 0` -/

/-- The comparison of the two constructions of `ε⁻¹` on sheaves of commutative rings, at the
structure sheaf of `S`: on the left the one transported from the inverse image of sheaves of
sets along the morphism of topoi, which is the one the abstract morphism of ringed topoi uses,
on the right Mathlib's pullback of `CommRingCat`-valued sheaves, which is the one
`AlgebraicGeometry.SmallEtale.inverseImageStructureMap` and
`AlgebraicGeometry.SmallEtale.imageSectionsToInverseImage` are stated for. -/
public noncomputable abbrev invCommRingIsoStructure :
    (inverseImageCommRingFunctor.{u, u, u, u + 1, u, u} (toposHom B S hS)).obj
        S.zariskiCommRingSheaf ≅
      (inverseImageCommRing B S hS).obj S.zariskiCommRingSheaf :=
  (invCommRingIso B S hS).app S.zariskiCommRingSheaf

/-- `AlgebraicGeometry.SmallEtale.invCommRingIsoStructure` read on sheaves of not necessarily
commutative rings.  Spelled through `CategoryTheory.sheafCompose` rather than as a whiskering,
so that the source of the comparison is the object the local bijectivity instances for
`AlgebraicGeometry.SmallEtale.imageSectionsToInverseImageRing` are stated at. -/
public noncomputable abbrev invCommRingIsoStructureRing :
    (sheafCompose (topology B S hS) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor.{u, u, u, u + 1, u, u} (toposHom B S hS)).obj
          S.zariskiCommRingSheaf) ≅
      (sheafCompose (topology B S hS) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRing B S hS).obj S.zariskiCommRingSheaf) :=
  (sheafCompose (topology B S hS) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
    (invCommRingIsoStructure B S hS)

public instance isIso_invCommRingIsoStructureRing_inv_hom :
    IsIso ((invCommRingIsoStructureRing B S hS).inv.hom) :=
  inferInstanceAs (IsIso ((sheafToPresheaf (topology B S hS) RingCat.{u}).mapIso
    (invCommRingIsoStructureRing B S hS)).inv)

/-- **The comparison `(f : V → S) ↦ 𝒪_S(f(V))` `⟶` `ε⁻¹𝒪_{S_Zar}`, at the inverse image of
sheaves of commutative rings the abstract morphism of ringed topoi uses.**  It is
`AlgebraicGeometry.SmallEtale.imageSectionsToInverseImage` followed by the comparison of the
two constructions of `ε⁻¹`, hence still a sheafification unit up to isomorphism, hence locally
bijective. -/
public noncomputable def imageSectionsToInverseImageCommRing :
    imageSectionsPresheaf B S hS ⟶
      ((inverseImageCommRingFunctor.{u, u, u, u + 1, u, u} (toposHom B S hS)).obj
        S.zariskiCommRingSheaf).obj :=
  imageSectionsToInverseImage B S hS ≫ (invCommRingIsoStructure B S hS).inv.hom

/-- The comparison is locally injective, being a sheafification unit followed by an
isomorphism. -/
public instance isLocallyInjective_imageSectionsToInverseImageCommRing :
    Presheaf.IsLocallyInjective (topology B S hS)
      (Functor.whiskerRight (imageSectionsToInverseImageCommRing B S hS)
        (forget₂ CommRingCat.{u} RingCat.{u})) :=
  inferInstanceAs (Presheaf.IsLocallyInjective (topology B S hS)
    (imageSectionsToInverseImageRing B S hS ≫ (invCommRingIsoStructureRing B S hS).inv.hom))

/-- The comparison is locally surjective, being a sheafification unit followed by an
isomorphism. -/
public instance isLocallySurjective_imageSectionsToInverseImageCommRing :
    Presheaf.IsLocallySurjective (topology B S hS)
      (Functor.whiskerRight (imageSectionsToInverseImageCommRing B S hS)
        (forget₂ CommRingCat.{u} RingCat.{u})) :=
  inferInstanceAs (Presheaf.IsLocallySurjective (topology B S hS)
    (imageSectionsToInverseImageRing B S hS ≫ (invCommRingIsoStructureRing B S hS).inv.hom))

/-- **The comparison followed by the structure map of `ε` is the restriction
`𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`.**  This is
`AlgebraicGeometry.SmallEtale.imageSectionsToInverseImage_comp_inverseImageStructureMap` read
at the inverse image of sheaves of commutative rings the abstract morphism of ringed topoi
uses: the comparison of the two constructions of `ε⁻¹` cancels against its inverse, by
`AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom_fSharpInverseImage`.

It is what makes the faithful flatness recorded by
`AlgebraicGeometry.SmallEtale.locallyFaithfullyFlat_imageSectionsRestriction` a hypothesis
about the structure map of the abstract morphism. -/
public theorem imageSectionsToInverseImageCommRing_comp_fSharpCommRing :
    imageSectionsToInverseImageCommRing B S hS ≫
        fSharpCommRing (toZariskiAbstractRingedToposHom B S hS).toRingedToposModulesHom
      = imageSectionsRestriction B S hS := by
  have hθ : fSharpCommRing (toZariskiAbstractRingedToposHom B S hS).toRingedToposModulesHom
      = (invCommRingIsoStructure B S hS).hom.hom ≫ (inverseImageStructureMap B S hS).hom := by
    exact fSharpInverseImage_hom_eq_comp B S hS
  have hid : (invCommRingIsoStructure B S hS).inv.hom ≫
      (invCommRingIsoStructure B S hS).hom.hom = 𝟙 _ :=
    congrArg (fun m : (inverseImageCommRing B S hS).obj S.zariskiCommRingSheaf ⟶
        (inverseImageCommRing B S hS).obj S.zariskiCommRingSheaf => m.hom)
      (invCommRingIsoStructure B S hS).inv_hom_id
  rw [hθ]
  show imageSectionsToInverseImage B S hS ≫ (invCommRingIsoStructure B S hS).inv.hom ≫
    ((invCommRingIsoStructure B S hS).hom.hom ≫ (inverseImageStructureMap B S hS).hom) = _
  rw [← Category.assoc ((invCommRingIsoStructure B S hS).inv.hom), hid, Category.id_comp]
  exact imageSectionsToInverseImage_comp_inverseImageStructureMap B S hS

/-- **Stacks 08H8, the faithfulness assertion.**  If the pullback `ε^*𝓕` of a sheaf of
`𝒪_S`-modules along `ε = id_{small, étale, Zar} : S_étale → S_Zar` vanishes, then `𝓕` vanishes.

The pullback is the inverse image of Stacks 03D2 followed by extension of scalars along the
structure map, and the two halves are reflected separately.  Extension of scalars reflects the
zero sheaf because the structure map is locally faithfully flat over the comparison presheaf
`(f : V → S) ↦ 𝒪_S(f(V))`
(`AlgebraicGeometry.SmallEtale.locallyFaithfullyFlat_imageSectionsRestriction`), and the
inverse image reflects it by
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_inverseImageModules`. -/
@[stacks 08H8 "the faithfulness assertion: `ε^*𝓕 = 0 ⟹ 𝓕 = 0`, for `ε^*` the pullback of
  sheaves of modules of Stacks 03D6 (2) along the two-field morphism of ringed topoi of
  Stacks 01D3 (2) carrying `ε`.  The flatness assertion is carried by
  `AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`, the exactness
  assertion by `AlgebraicGeometry.SmallEtale.exactFunctor_pullbackModules_toZariski` and the
  existence assertion by
  `AlgebraicGeometry.SmallEtale.isRightAdjoint_toZariskiModulePushforward`"]
public theorem isZero_of_isZero_toZariskiModulePullback
    (𝓕 : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O))
    (h : IsZero ((toZariskiModulePullback B S hS).obj 𝓕)) : IsZero 𝓕 := by
  refine isZero_of_isZero_inverseImageModules B S hS 𝓕 ?_
  have hσ : LocallyFaithfullyFlat (topology B S hS)
      (imageSectionsToInverseImageCommRing B S hS ≫
        fSharpCommRing (toZariskiAbstractRingedToposHom B S hS).toRingedToposModulesHom) := by
    rw [imageSectionsToInverseImageCommRing_comp_fSharpCommRing]
    exact locallyFaithfullyFlat_imageSectionsRestriction B S hS
  exact @isZero_of_isZero_extendScalars_obj_of_locallyFaithfullyFlat_comp
    (SmallEtale B S hS) _ (topology B S hS) _ _
    (fSharpCommRing (toZariskiAbstractRingedToposHom B S hS).toRingedToposModulesHom)
    _ (imageSectionsToInverseImageCommRing B S hS)
    (inverseImageRingSheaf (toposHom B S hS)
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos B S hS).O).property
    _ _ (isLocallyInjective_imageSectionsToInverseImageCommRing B S hS)
    (isLocallySurjective_imageSectionsToInverseImageCommRing B S hS)
    hσ ((toZariskiModuleInverseImage B S hS).obj 𝓕) h

end AlgebraicGeometry.SmallEtale

end
