module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusion
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportPushforward
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovarianceInjectivity

/-!
# Covariance for a separated morphism is the extension by zero of Stacks 0F53

Let `j : X' ⟶ X` be an open immersion and let `f : X ⟶ Y` be separated, locally of finite type
and locally quasi-finite in a big étale site. For such an `f` the finite-support direct image
presheaf `f_{p!}` is the proper-support direct image `f_!` of Stacks 0F4X, by the isomorphism of
Stacks 0F6N, and under that identification the covariance map `(j ≫ f)_{p!}(F|_{X'}) ⟶ f_{p!}F`
of Stacks 0F6S is the extension by zero `(j ≫ f)_!(F|_{X'}) ⟶ f_!F` of Stacks 0F53. This is
Stacks 0F6S, part (2).

## Main results

* `AlgebraicGeometry.SmallEtale.finiteSupportPushforwardIso_generator` — for a separated
  morphism the isomorphism of Stacks 0F6N carries a colimit generator to the extension by zero
  of the supported section to `X_V`.
* `AlgebraicGeometry.SmallEtale.eq_finiteSupportExtension_of_unit_eq` — a section of `F` on
  `X_V` supported on the image of an eligible support and restricting on `X'_V` to a given
  supported section is the extension by zero of that section.
* `AlgebraicGeometry.SmallEtale.openCovariancePresheafMap_comp_finiteSupportPushforwardIso` —
  **Stacks 0F6S, part (2)**: the two maps agree.

## Implementation notes

For a separated morphism the canonical open of an eligible support is all of `X_V`, so a
supported section is the same thing as a section of `f_!F` over the test object and the
isomorphism of Stacks 0F6N is extension by zero in the sense of
`AlgebraicGeometry.SmallEtale.finiteSupportExtension`. Both maps are therefore determined on a
colimit generator by one section of `F` on `X_V`, and the two sections agree because they have
the same support, contained in the image of `X'_V`, and the same restriction to `X'_V`:
restriction to the canonical open of the image support is injective on sections supported
there, which is `AlgebraicGeometry.SmallEtale.covarianceTargetOpenMap_restrict_injective`.

## References

* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
* [Stacks Project, Tag 0F6N](https://stacks.math.columbia.edu/tag/0F6N)
* [Stacks Project, Tag 0F53](https://stacks.math.columbia.edu/tag/0F53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section Generator

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- For a separated morphism the comparison of Stacks 0F6N carries the colimit generator of an
eligible support to the extension by zero of the supported section to `X_V`. -/
public theorem finiteSupportPushforwardIso_generator (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V)
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    ((fShriekSubsheaf B f F).val.arrow.hom.app (op V)).hom
        ((((finiteSupportPushforwardIso.{u, max (u + 1) v} B f).val.hom.app F).app
          (op V)).hom ((finiteSupportPushforwardGenerator B f F V E).hom s)) =
      finiteSupportExtension B f F V E s := by
  refine finiteSupportOpen_restrict_injective B f F V E ?_
  rw [finiteSupportExtension_restrict]
  exact (finiteSupportPushforwardIso.{u, max (u + 1) v} B f).property F V E s

end Generator

section Separated

attribute [local instance] isSeparated_openImmersion_comp

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)] [IsSeparated (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

omit [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The natural transformation of base changes along `j` is the comparison of iterated base
change followed by the counit of the post-composition adjunction. -/
public theorem openBaseChangeMap_app (V : SmallEtale B Y.obj Y.property) :
    (openBaseChangeMap B j f).app V =
      (openPostcompose B j).map
          ((smallEtaleBaseChange_compIso B X' X Y j f).val.inv.app V) ≫
        (openPostcomposeAdjunction B j).counit.app (baseChange B f V) := by
  simp [openBaseChangeMap]

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- A section of `F` on `X_V` supported on the image of an eligible support of `j ≫ f` whose
restriction to `X'_V` is the extension by zero of a supported section is the extension by zero
on `X_V` of that section read on the whole source. -/
public theorem eq_finiteSupportExtension_of_unit_eq (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V)
    (a : supportedSections B X'.obj X'.property ((openRestriction.{u, v} B j).obj F)
      (baseChange B (j ≫ f) V) E.1 (finiteSupport_isLocallyClosed B (j ≫ f) V E))
    (t : F.obj.obj (op (baseChange B f V)))
    (hsub : supportSection B X.obj X.property F (baseChange B f V) t ⊆
      (imageFiniteSupport B j f V E).1)
    (hres : (((smallEtaleBaseChange B j).sheafAdjunctionContinuous
          AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
        (op (baseChange B f V)) t =
      (((openRestriction.{u, v} B j).obj F).obj.map
          ((smallEtaleBaseChange_compIso B X' X Y j f).val.hom.app V).op).hom
        (finiteSupportExtension B (j ≫ f) ((openRestriction.{u, v} B j).obj F) V E a)) :
    t = finiteSupportExtension B f F V (imageFiniteSupport B j f V E)
      (covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E) a) := by
  have hfac : covarianceTargetOpenMap B j f V E (imageFiniteSupport B j f V E)
          (imageFiniteSupport_coe B j f V E) ≫
        openObjectι B X.obj X.property (baseChange B f V)
          (finiteSupportOpen B f V (imageFiniteSupport B j f V E)) =
      (openPostcompose B j).map
          (openObjectι B X'.obj X'.property (baseChange B (j ≫ f) V)
            (finiteSupportOpen B (j ≫ f) V E)) ≫
        (openBaseChangeMap B j f).app V :=
    covarianceTargetOpenMap_fac B j f V E (imageFiniteSupport B j f V E)
      (imageFiniteSupport_coe B j f V E)
  have hid : ∀ z, ((openRestrictionIso.{u, v} B j).inv.app F).hom.app
        (op ((smallEtaleBaseChange B j).obj (baseChange B f V)))
        (((openRestrictionIso.{u, v} B j).hom.app F).hom.app
          (op ((smallEtaleBaseChange B j).obj (baseChange B f V))) z) = z := fun z =>
    ConcreteCategory.congr_hom
      (congrArg (fun k => k.hom.app
          (op ((smallEtaleBaseChange B j).obj (baseChange B f V))))
        ((openRestrictionIso.{u, v} B j).hom_inv_id_app F)) z
  have hcancelF (z : ((openRestriction.{u, v} B j).obj F).obj.obj
      (op (baseChange B (j ≫ f) V))) :
      (((openRestriction.{u, v} B j).obj F).obj.map
          ((smallEtaleBaseChange_compIso B X' X Y j f).val.inv.app V).op).hom
        ((((openRestriction.{u, v} B j).obj F).obj.map
          ((smallEtaleBaseChange_compIso B X' X Y j f).val.hom.app V).op).hom z) = z := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      (smallEtaleBaseChange_compIso B X' X Y j f).val.inv_hom_id_app V, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  have hnat {W₁ W₂ : SmallEtale B X'.obj X'.property} (g : W₁ ⟶ W₂)
      (z : ((openRestriction.{u, v} B j).obj F).obj.obj (op W₂)) :
      F.obj.map ((openPostcompose B j).map g).op
          (((openRestrictionIso.{u, v} B j).inv.app F).hom.app (op W₂) z) =
        ((openRestrictionIso.{u, v} B j).inv.app F).hom.app (op W₁)
          ((((openRestriction.{u, v} B j).obj F).obj.map g.op).hom z) := by
    have h := ConcreteCategory.congr_hom
      (((openRestrictionIso.{u, v} B j).inv.app F).hom.naturality g.op) z
    simp only [ConcreteCategory.comp_apply, openPostcompose_sheafPushforward_map] at h
    exact h.symm
  have hcounit : F.obj.map ((openPostcomposeAdjunction B j).counit.app
        (baseChange B f V)).op t =
      ((openRestrictionIso.{u, v} B j).inv.app F).hom.app
          (op ((smallEtaleBaseChange B j).obj (baseChange B f V)))
        ((((openRestriction.{u, v} B j).obj F).obj.map
          ((smallEtaleBaseChange_compIso B X' X Y j f).val.hom.app V).op).hom
          (finiteSupportExtension B (j ≫ f) ((openRestriction.{u, v} B j).obj F) V E a)) := by
    rw [← hres, ← openRestrictionIso_unit_app B j F (baseChange B f V) t]
    exact (hid _).symm
  have hobcm : F.obj.map ((openBaseChangeMap B j f).app V).op t =
      ((openRestrictionIso.{u, v} B j).inv.app F).hom.app
          (op (baseChange B (j ≫ f) V))
        (finiteSupportExtension B (j ≫ f) ((openRestriction.{u, v} B j).obj F) V E a) := by
    rw [openBaseChangeMap_app, op_comp, F.obj.map_comp, ConcreteCategory.comp_apply,
      hcounit,
      hnat (W₂ := (smallEtaleBaseChange B j).obj (baseChange B f V))
        ((smallEtaleBaseChange_compIso B X' X Y j f).val.inv.app V), hcancelF]
  have hmem : F.obj.map (openObjectι B X.obj X.property (baseChange B f V)
        (finiteSupportOpen B f V (imageFiniteSupport B j f V E))).op t ∈
      sectionsSupportedOn B X.obj X.property F
        (openCovarianceSupportObject B f V (imageFiniteSupport B j f V E))
        ((openCovarianceSupportOpen B f V (imageFiniteSupport B j f V E)).ι.base ⁻¹'
          (imageFiniteSupport B j f V E).1) := by
    change supportSection B X.obj X.property F _ _ ⊆ _
    rw [supportSection_map, openObjectι_map]
    exact Set.preimage_mono hsub
  have hcomp : F.obj.map (covarianceTargetOpenMap B j f V E
          (imageFiniteSupport B j f V E) (imageFiniteSupport_coe B j f V E)).op
        (F.obj.map (openObjectι B X.obj X.property (baseChange B f V)
          (finiteSupportOpen B f V (imageFiniteSupport B j f V E))).op t) =
      F.obj.map (covarianceTargetOpenMap B j f V E
          (imageFiniteSupport B j f V E) (imageFiniteSupport_coe B j f V E)).op
        (covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E) a).val := by
    rw [covarianceSectionMap_restrict, ← ConcreteCategory.comp_apply, ← F.obj.map_comp,
      ← op_comp, hfac, op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, hobcm, hnat,
      finiteSupportExtension_restrict]
  refine finiteSupportOpen_restrict_injective B f F V (imageFiniteSupport B j f V E) ?_
  rw [finiteSupportExtension_restrict]
  exact congrArg Subtype.val
    (covarianceTargetOpenMap_restrict_injective B j f F V E (imageFiniteSupport B j f V E)
      (imageFiniteSupport_coe B j f V E) (a₁ := ⟨_, hmem⟩) hcomp)

omit [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The extension by zero of Stacks 0F53 of the section of `(j ≫ f)_!(F|_{X'})` attached to a
section supported on an eligible support is the extension by zero on `X_V` of that section read
on the whole source. -/
public theorem openInclusionShriekMap_finiteSupportExtension
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B (j ≫ f) V)
    (a : supportedSections B X'.obj X'.property ((openRestriction.{u, v} B j).obj F)
      (baseChange B (j ≫ f) V) E.1 (finiteSupport_isLocallyClosed B (j ≫ f) V E))
    (x : (fShriekSubsheaf B (j ≫ f) ((openRestriction.{u, v} B j).obj F)).val.obj.left.obj.obj
      (op V))
    (hx : ((fShriekSubsheaf B (j ≫ f) ((openRestriction.{u, v} B j).obj F)).val.arrow.hom.app
          (op V)).hom x =
        finiteSupportExtension B (j ≫ f) ((openRestriction.{u, v} B j).obj F) V E a) :
    ((fShriekSubsheaf B f F).val.arrow.hom.app (op V)).hom
        (((openInclusionShriekMap.{u, max (u + 1) v} B j f F).val.hom.app (op V)).hom x) =
      finiteSupportExtension B f F V (imageFiniteSupport B j f V E)
        (covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E) a) := by
  classical
  obtain ⟨hres, hsupp⟩ := (openInclusionShriekMap.{u, max (u + 1) v} B j f F).property.2 V x
  have hD : (imageFiniteSupport B j f V E).1 = (openBaseChangeHom B j f V).base '' E.1 :=
    imageFiniteSupport_coe B j f V E
  have hobc : openBaseChangeHom B j f V =
      (SmallEtale.toScheme B X'.obj X'.property).map
          ((smallEtaleBaseChange_compIso B X' X Y j f).val.inv.app V) ≫
        B.inclusion.map (pullback.fst ((baseChange B f V).obj.hom) j) := rfl
  have hcancel (y : (SmallEtale.toScheme B X'.obj X'.property).obj
      ((smallEtaleBaseChange B j).obj (baseChange B f V))) :
      ((SmallEtale.toScheme B X'.obj X'.property).map
          ((smallEtaleBaseChange_compIso B X' X Y j f).val.inv.app V)).base
        (((SmallEtale.toScheme B X'.obj X'.property).map
          ((smallEtaleBaseChange_compIso B X' X Y j f).val.hom.app V)).base y) = y := by
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp,
      (smallEtaleBaseChange_compIso B X' X Y j f).val.hom_inv_id_app V,
      CategoryTheory.Functor.map_id]
    rfl
  have hs'supp : supportSection B X'.obj X'.property ((openRestriction.{u, v} B j).obj F)
      (baseChange B (j ≫ f) V)
      (((fShriekSubsheaf B (j ≫ f) ((openRestriction.{u, v} B j).obj F)).val.arrow.hom.app
        (op V)).hom x) ⊆ E.1 := by
    rw [hx]
    exact supportSection_finiteSupportExtension_subset B (j ≫ f)
      ((openRestriction.{u, v} B j).obj F) V E a
  have hsubset : supportSection B X.obj X.property F (baseChange B f V)
        (((fShriekSubsheaf B f F).val.arrow.hom.app (op V)).hom
          (((openInclusionShriekMap.{u, max (u + 1) v} B j f F).val.hom.app (op V)).hom x)) ⊆
      (imageFiniteSupport B j f V E).1 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hsupp.subset hz
    rw [hD]
    refine ⟨((SmallEtale.toScheme B X'.obj X'.property).map
        ((smallEtaleBaseChange_compIso B X' X Y j f).val.hom.app V)).base y,
      hs'supp ((supportSection_map B X'.obj X'.property
        ((openRestriction.{u, v} B j).obj F) _ _
        ((smallEtaleBaseChange_compIso B X' X Y j f).val.hom.app V) _).subset hy), ?_⟩
    rw [hobc, Scheme.Hom.comp_apply]
    exact congrArg _ (hcancel y)
  refine eq_finiteSupportExtension_of_unit_eq B j f F V E a _ hsubset ?_
  rw [← hx]
  exact hres.symm

/-- **Stacks 0F6S, part (2).** For a separated morphism the covariance map of finite-support
direct-image presheaves attached to an open subscheme of the source is the extension by zero of
Stacks 0F53, transported along the isomorphism of Stacks 0F6N. -/
@[stacks 0F6S "part (2), agreement with the map of Stacks 0F53 through Stacks 0F6N"]
public theorem openCovariancePresheafMap_comp_finiteSupportPushforwardIso :
    (openCovariancePresheafMap.{u, v} B j f).val.app F ≫
        (finiteSupportPushforwardIso.{u, max (u + 1) v} B f).val.hom.app F =
      (finiteSupportPushforwardIso.{u, max (u + 1) v} B (j ≫ f)).val.hom.app
          ((openRestriction.{u, v} B j).obj F) ≫
        (openInclusionShriekMap.{u, max (u + 1) v} B j f F).val.hom := by
  apply NatTrans.ext
  funext V
  obtain ⟨V⟩ := V
  apply finiteSupportPushforwardGenerator_hom_ext B (j ≫ f) ((openRestriction B j).obj F) V
  intro E
  change finiteSupportPushforwardGenerator B (j ≫ f) ((openRestriction B j).obj F) V E ≫
      covariancePresheafApp B j f F V ≫
        ((finiteSupportPushforwardIso.{u, max (u + 1) v} B f).val.hom.app F).app (op V) =
    finiteSupportPushforwardGenerator B (j ≫ f) ((openRestriction B j).obj F) V E ≫
      ((finiteSupportPushforwardIso.{u, max (u + 1) v} B (j ≫ f)).val.hom.app
          ((openRestriction.{u, v} B j).obj F)).app (op V) ≫
        (openInclusionShriekMap.{u, max (u + 1) v} B j f F).val.hom.app (op V)
  rw [← Category.assoc, covariancePresheafApp_generator B j f F V E
    (imageFiniteSupport B j f V E) (imageFiniteSupport_coe B j f V E), Category.assoc]
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  refine fShriekSubsheaf_arrow_app_injective B f F V ?_
  refine Eq.trans ?_ (openInclusionShriekMap_finiteSupportExtension B j f F V E s _
    (finiteSupportPushforwardIso_generator B (j ≫ f)
      ((openRestriction.{u, v} B j).obj F) V E s)).symm
  exact finiteSupportPushforwardIso_generator B f F V (imageFiniteSupport B j f V E)
    (covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E) s)

end Separated

end AlgebraicGeometry.SmallEtale

end
