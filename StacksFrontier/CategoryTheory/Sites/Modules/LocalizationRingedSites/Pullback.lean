module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.DirectImage
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalizationInverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback along the localization of a ringed site is restriction to the slice

Let `(C, O)` be a ringed site and `U` an object of `C`. Pulling a sheaf of `O`-modules back
along the localization morphism of ringed topoi `π : (Sh(C/U), O|_U) ⟶ (Sh(C), O)` of Stacks
04IX is the same thing as restricting it to the localized site, i.e. Mathlib's
`SheafOfModules.overFunctor`.

## Main definitions

* `AlgebraicGeometry.RingedSite.localizationRestrictScalars` and
  `AlgebraicGeometry.RingedSite.localizationExtendScalars`: restriction and extension of scalars
  along the structure map of the localization.
* `AlgebraicGeometry.RingedSite.localizationExtendRestrictAdjunction`: Stacks 03CZ for that
  structure map, and `AlgebraicGeometry.RingedSite.localizationExtendRestrictCounitIso` its
  counit read as an isomorphism.

## Main results

* `AlgebraicGeometry.RingedSite.localizationPullbackIsoRestriction`: the isomorphism between
  pullback along the localization morphism and `SheafOfModules.overFunctor`.
* `AlgebraicGeometry.RingedSite.localizationPullbackIsoRestriction_eq`: that isomorphism written
  out as the composite of its named factors.
* `AlgebraicGeometry.RingedSite.localizationPullbackIsoRestriction_exists`: the isomorphism, in
  `Nonempty` form.

## Implementation notes

The structure map of the localization is `overInverseImageFsharp`, which is
`overInverseImageRingIso` composed with the identity; the composition is not a definitional
identity for morphisms of sheaves of rings, so the adjunction is transported along
`CategoryTheory.Adjunction.ofNatIsoRight`.

Fullness of restriction of scalars along an isomorphism of sheaves of rings,
`AlgebraicGeometry.RingedSite.restrictScalarsFullyFaithful`, is derived from
`PresheafOfModules.restrictHomEquivOfIsLocallySurjective`.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u v

namespace AlgebraicGeometry.RingedSite

/-- Restriction of scalars along an isomorphism of sheaves of rings is fully faithful. -/
noncomputable def restrictScalarsFullyFaithful {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u}} (a : R ⟶ S) [IsIso a] :
    (SheafOfModules.restrictScalars.{u} a).FullyFaithful := by
  letI : IsIso a.hom := inferInstanceAs (IsIso ((sheafToPresheaf J RingCat).map a))
  exact
    { preimage := fun {_ F'} f =>
        ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective a.hom F'.isSheaf).symm f.val⟩
      map_preimage := fun f => SheafOfModules.Hom.ext
        ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective a.hom _).apply_symm_apply _)
      preimage_map := fun f => SheafOfModules.Hom.ext
        ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective a.hom _).symm_apply_apply _) }

variable (X : RingedSite.{u, v, max u v}) (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [hcomm : (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [X.J.HasSheafCompose (forget RingCat.{max u v})]
  [hring : (X.J.over U).HasSheafCompose (forget RingCat.{max u v})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [hab : (X.J.over U).HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{max u v}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-! ### The ingredients of Stacks 04IX for a localization -/

/-- Restriction of scalars along `AlgebraicGeometry.RingedSite.overInverseImageRingIso`, the
identification of the inverse image of the structure sheaf with its restriction to the slice
site at `U`. -/
noncomputable def localizationRestrictScalars :
    SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) ⥤
      SheafOfModules.{max u v}
        ((inverseImageRingFunctor (X.overMorphismOfTopoi U)).obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  SheafOfModules.restrictScalars.{max u v} (X.overInverseImageRingIso U).hom

/-- Extension of scalars along the structure map of the localization morphism at `U`. -/
noncomputable def localizationExtendScalars :
    SheafOfModules.{max u v}
        (inverseImageRingSheaf (X.localizationMorphism U).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos X).O)) ⥤
      SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (X.over U)).O) :=
  extendScalarsFSharp (X := ringedTopos (X.over U)) (Y := ringedTopos X)
    (X.localizationMorphism U)

/-- Restriction of scalars along the structure map of the localization is fully faithful, that
structure map being an isomorphism of sheaves of rings. -/
noncomputable def localizationRestrictScalarsFullyFaithful :
    (localizationRestrictScalars X U).FullyFaithful :=
  restrictScalarsFullyFaithful (X.overInverseImageRingIso U).hom

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] hcomm
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max u v})] hab
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{max u v}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Restriction of scalars along the morphism of sheaves of commutative rings underlying the
structure map of the localization at `U` is `localizationRestrictScalars`. -/
theorem localizationRestrictScalars_eq :
    SheafOfModules.restrictScalars.{max u v}
        (commRingSheafMap (X.J.over U) (fSharpCommRing (X.localizationMorphism U))
          (inverseImageRingSheaf (X.localizationMorphism U).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos X).O)).property
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (X.over U)).O).property) =
      localizationRestrictScalars X U :=
  congrArg SheafOfModules.restrictScalars
    ((commRingSheafMap_fSharpCommRing (X.localizationMorphism U)).trans
      (X.overInverseImageFsharp_eq U))

/-- Extension of scalars along the structure map of the localization at `U` is left adjoint to
restriction of scalars along it. -/
noncomputable def localizationExtendRestrictAdjunction :
    localizationExtendScalars X U ⊣ localizationRestrictScalars X U :=
  Adjunction.ofNatIsoRight
    (extendRestrictScalarsAdjunction (X.J.over U) (fSharpCommRing (X.localizationMorphism U))
      (inverseImageRingSheaf (X.localizationMorphism U).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos X).O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (X.over U)).O).property)
    (eqToIso (localizationRestrictScalars_eq X U))

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] hcomm
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max u v})] hab in
/-- The counit of `localizationExtendRestrictAdjunction` is an isomorphism, its right adjoint
being fully faithful. -/
theorem isIso_localizationExtendRestrictAdjunction_counit :
    IsIso (localizationExtendRestrictAdjunction X U).counit :=
  @Adjunction.counit_isIso_of_R_fully_faithful _ _ _ _ (localizationExtendScalars X U)
    (localizationRestrictScalars X U) (localizationExtendRestrictAdjunction X U)
    (localizationRestrictScalarsFullyFaithful X U).full
    (localizationRestrictScalarsFullyFaithful X U).faithful

/-- The counit of `localizationExtendRestrictAdjunction`, as an isomorphism. -/
noncomputable def localizationExtendRestrictCounitIso :
    localizationRestrictScalars X U ⋙ localizationExtendScalars X U ≅ 𝟭 _ :=
  @asIso _ _ _ _ (localizationExtendRestrictAdjunction X U).counit
    (isIso_localizationExtendRestrictAdjunction_counit X U)

/-- **Stacks 04IX.** Pullback of sheaves of modules along the localization morphism of ringed
topoi at `U` is restriction to the localized site. -/
noncomputable def localizationPullbackIsoRestriction :
    (X.localizationMorphism U).pullbackModules ≅
      SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U := by
  have := hcomm
  have := hring
  have := hab
  let f := X.localizationMorphism U
  let k := (restrictionRingIso (X.J.over U) X.J (Over.forget U)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom
  let E := extendScalarsFSharp (X := ringedTopos (X.over U)) (Y := ringedTopos X) f
  let R := SheafOfModules.restrictScalars.{max u v} k
  let ff := restrictScalarsFullyFaithful k
  have hk : (SheafOfModules.restrictScalars.{max u v}
      (commRingSheafMap (X.J.over U) (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos X).O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (X.over U)).O).property)) = R :=
    congrArg SheafOfModules.restrictScalars
      ((commRingSheafMap_fSharpCommRing f).trans (X.overInverseImageFsharp_eq U))
  let adj : E ⊣ R :=
    Adjunction.ofNatIsoRight
      (extendRestrictScalarsAdjunction (X.J.over U) (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos X).O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (X.over U)).O).property)
      (eqToIso hk)
  have hc : IsIso adj.counit :=
    @Adjunction.counit_isIso_of_R_fully_faithful _ _ _ _ E R adj ff.full ff.faithful
  let counitIso : R ⋙ E ≅ 𝟭 _ := @asIso _ _ _ _ adj.counit hc
  exact Functor.isoWhiskerRight
      (restrictionModuleIso (X.J.over U) X.J (Over.forget U)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) E ≪≫
    Functor.associator
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) R E ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) counitIso ≪≫
      Functor.rightUnitor
        (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- `AlgebraicGeometry.RingedSite.localizationPullbackIsoRestriction` written out as the
composite of its four named factors. -/
theorem localizationPullbackIsoRestriction_eq :
    localizationPullbackIsoRestriction X U =
      Functor.isoWhiskerRight
          (restrictionModuleIso (X.J.over U) X.J (Over.forget U)
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (localizationExtendScalars X U) ≪≫
        Functor.associator
          (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
          (localizationRestrictScalars X U) (localizationExtendScalars X U) ≪≫
        Functor.isoWhiskerLeft
          (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
          (localizationExtendRestrictCounitIso X U) ≪≫
          Functor.rightUnitor
            (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- Pullback of sheaves of modules along the localization morphism of ringed topoi at `U` is
isomorphic to restriction to the localized site. -/
@[stacks 04IX "module_restriction"]
theorem localizationPullbackIsoRestriction_exists :
    Nonempty ((X.localizationMorphism U).pullbackModules ≅
      SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
  ⟨localizationPullbackIsoRestriction X U⟩

end AlgebraicGeometry.RingedSite

end
