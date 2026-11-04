module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.LocalizationShriekInteger
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero of the restriction of an abelian sheaf is tensoring with `Z_F^#`

Let `C` be a site, let `F` be a sheaf of sets on `C` and let `j : Sh(C)/F ⟶ Sh(C)` be the
localization morphism. Two identifications are available separately, in two different ambient
categories of abelian sheaves:

* `j_! ℤ ≅ Z_F^#`, the free abelian sheaf on `F`, for sheaves valued in `AddCommGrpCat`;
* `j_!(j⁻¹ H) ≅ j_! ℤ ⊗ H`, for sheaves valued in `ModuleCat (ULift ℤ)`, which is the ambient
  category carrying the tensor product, and in which `j_! ℤ` appears as the tensor unit.

This file bridges the two, so that the conclusion of the source is reached:

`j_!(j⁻¹ H) ≅ Z_F^# ⊗_ℤ H`.

The bridge is the change of coefficients along the equivalence
`ModuleCat (ULift ℤ) ≌ AddCommGrpCat` — restriction of scalars along `ULift ℤ ≃+* ℤ` followed
by the forgetful functor from `ℤ`-modules — induced on sheaves by
`CategoryTheory.Sheaf.coefficientEquivalence`. What has to be checked is that the bridge is
compatible with the two structures involved in the statement: it commutes with the two extension
by zero functors, and it carries the tensor unit to the constant sheaf on `ULift ℤ`, which is
the sheaf whose extension by zero is `Z_F^#`.

Both compatibilities are uniqueness of a left adjoint, not extra data. Extension by zero is, on
either side, the left adjoint of restriction along the projection `C/F ⥤ C`, and restriction
commutes with a change of coefficients on the nose, the one operation precomposing the
underlying presheaf with the projection and the other postcomposing it with the change of
coefficients. The same argument identifies sheafification across the bridge, and the tensor unit
of `Sheaf K (ModuleCat (ULift ℤ))` is the sheafification of the constant presheaf on the tensor
unit `ULift ℤ`.

## Main definitions

* `Stacks.Sites.Localization.integerModuleAddCommGrpEquivalence`: `ULift ℤ`-modules are abelian
  groups.
* `Stacks.Sites.Localization.sheafIntegerModuleEquivalence`: the induced equivalence of the two
  categories of abelian sheaves on a site.

## Main results

* `Stacks.Sites.Localization.shriekCoefficientIso`: extension by zero along the localization
  projection commutes with the change of coefficients.
* `Stacks.Sites.Localization.tensorUnitIsoConstantSheaf`: the change of coefficients carries the
  tensor unit to the constant sheaf on `ULift ℤ`.
* `Stacks.Sites.Localization.jShriekUnitIsoFreeAbelianSheaf`: `j_! ℤ ≅ Z_F^#` in the ambient
  category of sheaves of `ULift ℤ`-modules.
* `Stacks.Sites.Localization.jShriekPullbackIsoShriekUnitTensor`: part (b) of the source,
  `j_!(j⁻¹ H) ≅ j_! ℤ ⊗ H`, with the five instance hypotheses of the arbitrary-size form
  `jShriekPullbackIsoTensor` discharged.
* `Stacks.Sites.Localization.jShriekPullbackIsoFreeAbelianSheafTensor`: the conclusion of the
  source, `j_!(j⁻¹ H) ≅ Z_F^# ⊗ H`.

## Implementation notes

Nothing here is assumed of the site. Sheafification of `ModuleCat`-valued presheaves, the
monoidality of the sheafification localizer and the left Kan extensions along the localization
projection are all consequences of the site being small, through the one instance
`preservesColimitsOfShape_cover_op_forget_moduleCat` that Mathlib's construction needs and does
not declare; so the two identifications below carry no hypothesis beyond the data of the source.

The free abelian sheaf `Z_F^#` is an `AddCommGrpCat`-valued sheaf, and the tensor product is
formed in `ModuleCat (ULift ℤ)`-valued sheaves; the statement therefore transports `Z_F^#`
through the inverse of the equivalence rather than transporting the tensor product, which would
require a monoidal structure on `AddCommGrpCat` that Mathlib does not provide.

## References

* [Stacks Project, Tag 0EYY](https://stacks.math.columbia.edu/tag/0EYY)
* [Stacks Project, Tag 03AC](https://stacks.math.columbia.edu/tag/03AC), the free abelian sheaf.
* [Stacks Project, Tag 04IP](https://stacks.math.columbia.edu/tag/04IP), the localization
  morphism.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite

universe u

namespace Stacks.Sites.Localization

/-- Modules over `ULift ℤ` are abelian groups: restrict scalars along the ring isomorphism
`ULift ℤ ≃+* ℤ` and forget the `ℤ`-module structure. -/
abbrev integerModuleAddCommGrpEquivalence :
    ModuleCat.{u} (ULift.{u} ℤ) ≌ AddCommGrpCat.{u} :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)).symm.trans
    AddCommGrpCat.moduleCatIntEquivalence.symm

/-- The tensor unit of `ModuleCat (ULift ℤ)` is the abelian group `ULift ℤ`. -/
def integerModuleUnitIso :
    integerModuleAddCommGrpEquivalence.functor.obj
        (𝟙_ (ModuleCat.{u} (ULift.{u} ℤ))) ≅ AddCommGrpCat.of (ULift.{u} ℤ) :=
  Iso.refl _

/-- The forgetful functor from `R`-modules preserves the colimits indexed by the covers of an
object of a site: `(K.Cover X)ᵒᵖ` is filtered, and the forgetful functor preserves filtered
colimits.

This is the one hypothesis of Mathlib's construction of sheafification for `ModuleCat`-valued
presheaves that instance search does not supply on its own. With it,
`HasSheafify K (ModuleCat.{u} R)` holds on every small site, hence so do `HasWeakSheafify`, the
monoidality of the sheafification localizer and the existence of the left Kan extensions along
the localization projection — so the identifications below are stated for an arbitrary site,
with no assumption the source does not make. -/
instance preservesColimitsOfShape_cover_op_forget_moduleCat {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) (X : D) (R : Type u) [Ring R] :
    PreservesColimitsOfShape (K.Cover X)ᵒᵖ (forget (ModuleCat.{u} R)) :=
  PreservesFilteredColimitsOfSize.preserves_filtered_colimits _

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

attribute [local instance] localizationProjection_isContinuous

/-- Sheaves of `ULift ℤ`-modules and sheaves of abelian groups on a site are the same thing:
the change of coefficients along `integerModuleAddCommGrpEquivalence`. -/
@[sga "4 IV 11.1.5" "partial"]
abbrev sheafIntegerModuleEquivalence :
    Sheaf J (ModuleCat.{u} (ULift.{u} ℤ)) ≌ Sheaf J AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.coefficientEquivalence J integerModuleAddCommGrpEquivalence.{u}

/-- Extension by zero along the projection `C/F ⥤ C` commutes with the change of coefficients
between sheaves of `ULift ℤ`-modules and sheaves of abelian groups.

Both composites are left adjoint to the composite of restriction along the projection with the
inverse change of coefficients — and restriction along the projection precomposes the underlying
presheaf with the projection while the change of coefficients postcomposes it, so the two
composite right adjoints are the same functor. The isomorphism is the uniqueness of a left
adjoint. -/
def shriekCoefficientIso (F : Sheaf J (Type u)) :
    abelianLocalizationShriek J F ⋙ (sheafIntegerModuleEquivalence J).functor ≅
      (sheafIntegerModuleEquivalence (localizationTopology J F)).functor ⋙
        Stacks.Sites.abelianShriek (localizationProjection J F)
          (localizationTopology J F) J :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (localizationProjection J F) (ModuleCat.{u} (ULift.{u} ℤ))
        (localizationTopology J F) J).comp
      (sheafIntegerModuleEquivalence J).toAdjunction).leftAdjointUniq
    (((sheafIntegerModuleEquivalence (localizationTopology J F)).toAdjunction.comp
      (Stacks.Sites.abelianShriekAdjunction (localizationProjection J F)
        (localizationTopology J F) J)).ofNatIsoRight (Iso.refl _))

section Unit

variable {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)

/-- Sheafification commutes with the change of coefficients between presheaves of
`ULift ℤ`-modules and presheaves of abelian groups: both composites are left adjoint to the
underlying presheaf followed by the inverse change of coefficients. -/
def presheafToSheafCoefficientIso :
    presheafToSheaf K (ModuleCat.{u} (ULift.{u} ℤ)) ⋙
        (sheafIntegerModuleEquivalence K).functor ≅
      (Functor.whiskeringRight Dᵒᵖ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}).obj
          integerModuleAddCommGrpEquivalence.functor ⋙
        presheafToSheaf K AddCommGrpCat.{u} :=
  ((sheafificationAdjunction K (ModuleCat.{u} (ULift.{u} ℤ))).comp
      (sheafIntegerModuleEquivalence K).toAdjunction).leftAdjointUniq
    ((integerModuleAddCommGrpEquivalence.congrRight.toAdjunction.comp
      (sheafificationAdjunction K AddCommGrpCat.{u})).ofNatIsoRight (Iso.refl _))

/-- The change of coefficients carries the tensor unit of the category of sheaves of
`ULift ℤ`-modules to the constant sheaf on the abelian group `ULift ℤ`.

The tensor unit is the sheafification of the constant presheaf on the tensor unit of
`ModuleCat (ULift ℤ)`, and sheafification commutes with the change of coefficients. -/
def tensorUnitIsoConstantSheaf :
    let := Sheaf.monoidalCategory K (ModuleCat.{u} (ULift.{u} ℤ))
    (sheafIntegerModuleEquivalence K).functor.obj (𝟙_ _) ≅
      (constantSheaf K AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  let := Sheaf.monoidalCategory K (ModuleCat.{u} (ULift.{u} ℤ))
  let L := presheafToSheaf K (ModuleCat.{u} (ULift.{u} ℤ))
  let : L.Monoidal := inferInstance
  exact (sheafIntegerModuleEquivalence K).functor.mapIso (Functor.Monoidal.εIso L) ≪≫
    (presheafToSheafCoefficientIso K).app
      ((Functor.const Dᵒᵖ).obj (𝟙_ (ModuleCat.{u} (ULift.{u} ℤ)))) ≪≫
    (presheafToSheaf K AddCommGrpCat.{u}).mapIso
      (Functor.constComp Dᵒᵖ (𝟙_ (ModuleCat.{u} (ULift.{u} ℤ)))
        integerModuleAddCommGrpEquivalence.functor) ≪≫
    (constantSheaf K AddCommGrpCat.{u}).mapIso integerModuleUnitIso.{u}

end Unit

variable (F : Sheaf J (Type u))

/-- **Stacks Project, Tag 0EYY**, part (a), in the ambient category of sheaves of
`ULift ℤ`-modules. The extension by zero of the tensor unit along the localization morphism
`j : Sh(C)/F ⟶ Sh(C)` is the free abelian sheaf `Z_F^#` on `F`, read through the equivalence
between sheaves of `ULift ℤ`-modules and sheaves of abelian groups.

This transports the `AddCommGrpCat`-valued statement
`localizationShriek_constantInteger_iso_freeAbSheaf` across the bridge, using that the bridge
commutes with extension by zero and carries the tensor unit to the constant sheaf on
`ULift ℤ`. -/
@[stacks 0EYY "j_! ℤ = Z_F^#, in the ambient category carrying the tensor product"]
def jShriekUnitIsoFreeAbelianSheaf :
    let := Sheaf.monoidalCategory (localizationTopology J F)
      (ModuleCat.{u} (ULift.{u} ℤ))
    (abelianLocalizationShriek J F).obj (𝟙_ _) ≅
      (sheafIntegerModuleEquivalence J).inverse.obj
        ((Presheaf.freeAbelianSheaf J).obj ((sheafToPresheaf J (Type u)).obj F)) := by
  let := Sheaf.monoidalCategory (localizationTopology J F)
    (ModuleCat.{u} (ULift.{u} ℤ))
  exact (sheafIntegerModuleEquivalence J).unitIso.app
      ((abelianLocalizationShriek J F).obj (𝟙_ _)) ≪≫
    (sheafIntegerModuleEquivalence J).inverse.mapIso
      ((shriekCoefficientIso J F).app (𝟙_ _) ≪≫
        (Stacks.Sites.abelianShriek (localizationProjection J F)
          (localizationTopology J F) J).mapIso
            (tensorUnitIsoConstantSheaf (localizationTopology J F)) ≪≫
        localizationShriek_constantInteger_iso_freeAbSheaf J F)

/-- **Stacks Project, Tag 0EYY**, part (b), with no hypothesis beyond the data of the source.
For the localization morphism `j : Sh(C)/F ⟶ Sh(C)` and an abelian sheaf `H` on `C`,

`j_!(j⁻¹ H) ≅ j_! ℤ ⊗_ℤ H`.

This is `jShriekPullbackIsoTensor`, which is proved for a site of arbitrary size and therefore
states sheafification of `ModuleCat`-valued presheaves on `C` and on `C/F`, the monoidality of
the two sheafification localizers and the left Kan extensions along `C/F ⥤ C` as hypotheses.
On a site all five are available: the monoidality of the two localizers from
`CategoryTheory.GrothendieckTopology.W.monoidal`, the left Kan extensions from Mathlib's
pointwise construction `CategoryTheory.Functor.pointwiseLeftKanExtension`, and the two
sheafifications through `preservesColimitsOfShape_cover_op_forget_moduleCat` above. So part (b)
carries no hypothesis the source does not make. -/
@[stacks 0EYY "j_!(j⁻¹ H) = j_! ℤ ⊗ H, with no hypothesis beyond the data of the source"]
def jShriekPullbackIsoShriekUnitTensor
    (H : Sheaf J (ModuleCat.{u} (ULift.{u} ℤ))) :
    let := Sheaf.monoidalCategory J (ModuleCat.{u} (ULift.{u} ℤ))
    let := Sheaf.monoidalCategory (localizationTopology J F)
      (ModuleCat.{u} (ULift.{u} ℤ))
    (abelianLocalizationShriek J F).obj
        ((abelianLocalizationInverseImage J F).obj H) ≅
      (abelianLocalizationShriek J F).obj (𝟙_ _) ⊗ H := by
  let := Sheaf.monoidalCategory J (ModuleCat.{u} (ULift.{u} ℤ))
  let := Sheaf.monoidalCategory (localizationTopology J F)
    (ModuleCat.{u} (ULift.{u} ℤ))
  exact jShriekPullbackIsoTensor J F H

/-- **Stacks Project, Tag 0EYY**, the conclusion. For the localization morphism
`j : Sh(C)/F ⟶ Sh(C)` and an abelian sheaf `H` on `C`,

`j_!(j⁻¹ H) ≅ Z_F^# ⊗_ℤ H`,

the free abelian sheaf on `F` tensored with `H`. This combines part (b),
`jShriekPullbackIsoTensor`, with the identification of `j_! ℤ` with `Z_F^#` of part (a). -/
@[stacks 0EYY "j_!(j⁻¹ H) = Z_F^# ⊗ H, the two parts joined"]
def jShriekPullbackIsoFreeAbelianSheafTensor
    (H : Sheaf J (ModuleCat.{u} (ULift.{u} ℤ))) :
    let := Sheaf.monoidalCategory J (ModuleCat.{u} (ULift.{u} ℤ))
    (abelianLocalizationShriek J F).obj
        ((abelianLocalizationInverseImage J F).obj H) ≅
      (sheafIntegerModuleEquivalence J).inverse.obj
        ((Presheaf.freeAbelianSheaf J).obj ((sheafToPresheaf J (Type u)).obj F)) ⊗ H := by
  let := Sheaf.monoidalCategory J (ModuleCat.{u} (ULift.{u} ℤ))
  let := Sheaf.monoidalCategory (localizationTopology J F)
    (ModuleCat.{u} (ULift.{u} ℤ))
  exact jShriekPullbackIsoTensor J F H ≪≫
    (tensorRight H).mapIso (jShriekUnitIsoFreeAbelianSheaf J F)

end Stacks.Sites.Localization

end
