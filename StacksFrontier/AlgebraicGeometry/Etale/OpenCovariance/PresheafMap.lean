module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance.ExtensionByZero

/-!
# The covariance map of finite-support direct images under an open immersion

Let `j : X' ⟶ X` be an open immersion in a big étale site and let `f : X ⟶ Y` be locally of
finite type and locally quasi-finite. Restricting an abelian sheaf `F` on the small étale site
of `X` to `X'` and forming the finite-support direct image along `j ≫ f` gives a presheaf on
the small étale site of `Y` which maps canonically to the finite-support direct image of `F`
along `f`: on each colimit generator, a section with support finite over an étale test object
`V`, living on `X'_V`, extends by zero to a section on `X_V` with support the image of the
original support. This file assembles these extensions into a natural map of presheaves and
sheafifies it.

## Main definitions

* `AlgebraicGeometry.SmallEtale.CovarianceGeneratorData` — the data of a covariance map on one
  colimit generator, and `AlgebraicGeometry.SmallEtale.OpenCovariancePresheafMapSpec` the
  characterization of a natural presheaf map by that data on every generator.
* `AlgebraicGeometry.SmallEtale.openCovariancePresheafMap` — the covariance map
  `(j ≫ f)_{p!}(F|_{X'}) ⟶ f_{p!}F` of finite-support direct-image presheaves, and
  `AlgebraicGeometry.SmallEtale.openCovarianceShriekMap` its sheafification
  `(j ≫ f)_!(F|_{X'}) ⟶ f_!F`.

## Implementation notes

`AlgebraicGeometry.SmallEtale.finiteSupportPushforwardGenerator` is a convenience abbreviation
for the colimit generator of the finite-support direct image presheaf.

## References

* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)]

section Generator

/-- Moving the `eqToHom`s of a generator identity to the other side. -/
private theorem comp_eqToHom_eq_of_eq {C : Type*} [Category C] {A B X X' Y Y' : C}
    {ι : A ⟶ X} {ι' : B ⟶ Y} {a : A ⟶ B} {m : X' ⟶ Y'} {p : X = X'} {q : Y' = Y}
    (h : ι ≫ eqToHom p ≫ m ≫ eqToHom q = a ≫ ι') :
    (ι ≫ eqToHom p) ≫ m = a ≫ ι' ≫ eqToHom q.symm := by
  subst p q
  simpa using h

variable {S T : B.Scheme} (g : S ⟶ T) [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyQuasiFinite (B.inclusion.map g)]
  (F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v})

/-- The colimit generator of the finite-support direct image presheaf attached to a support
finite over the étale test object. -/
public abbrev finiteSupportPushforwardGenerator (V : SmallEtale B T.obj T.property)
    (E : FiniteSupport B g V) :
    (finiteSupportDiagram B g F V).obj E ⟶
      ((finiteSupportPushforward.{u, max (u + 1) v} B g
        (fun _ => inferInstance)).val.obj F).obj (op V) :=
  colimit.ι (finiteSupportDiagram B g F V) E ≫
    eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B g
      (fun _ => inferInstance)).property.obj_eq F V).symm

/-- Two maps out of the finite-support direct image presheaf agreeing on every colimit
generator are equal. -/
public theorem finiteSupportPushforwardGenerator_hom_ext
    (V : SmallEtale B T.obj T.property) {A : AddCommGrpCat.{max (u + 1) v}}
    {a b : ((finiteSupportPushforward.{u, max (u + 1) v} B g
      (fun _ => inferInstance)).val.obj F).obj (op V) ⟶ A}
    (h : ∀ E, finiteSupportPushforwardGenerator B g F V E ≫ a =
      finiteSupportPushforwardGenerator B g F V E ≫ b) : a = b := by
  apply (cancel_epi (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B g
    (fun _ => inferInstance)).property.obj_eq F V).symm)).mp
  apply colimit.hom_ext
  intro E
  exact (Category.assoc _ _ _).symm.trans ((h E).trans (Category.assoc _ _ _))

/-- The restriction map of the finite-support direct image presheaf on a colimit
generator. -/
public theorem finiteSupportPushforwardGenerator_restrict
    {V V' : SmallEtale B T.obj T.property} (k : V' ⟶ V) (E : FiniteSupport B g V) :
    finiteSupportPushforwardGenerator B g F V E ≫
        ((finiteSupportPushforward.{u, max (u + 1) v} B g
          (fun _ => inferInstance)).val.obj F).map k.op =
      AddCommGrpCat.ofHom (finiteSupportBaseChange B g F k E).sectionsMap ≫
        finiteSupportPushforwardGenerator B g F V'
          (finiteSupportBaseChange B g F k E).support := by
  exact comp_eqToHom_eq_of_eq ((finiteSupportPushforward.{u, max (u + 1) v} B g
    (fun _ => inferInstance)).property.map_restrict F k E)

/-- The action of a morphism of abelian sheaves on the finite-support direct image presheaf,
on a colimit generator. -/
public theorem finiteSupportPushforwardGenerator_sheaf
    (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v})
    (φ : F ⟶ G) (V : SmallEtale B T.obj T.property) (E : FiniteSupport B g V) :
    finiteSupportPushforwardGenerator B g F V E ≫
        ((finiteSupportPushforward.{u, max (u + 1) v} B g
          (fun _ => inferInstance)).val.map φ).app (op V) =
      AddCommGrpCat.ofHom (supportedSectionsSheafMap B S.obj S.property φ
        (baseChange B g V) E.1 (finiteSupport_isLocallyClosed B g V E)) ≫
        finiteSupportPushforwardGenerator B g G V E := by
  exact comp_eqToHom_eq_of_eq ((finiteSupportPushforward.{u, max (u + 1) v} B g
    (fun _ => inferInstance)).property.map_sheaf φ V E)

end Generator

section Colimit

variable (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The canonical maps on supported sections are compatible with the transition maps of the
finite-support diagram. -/
public theorem covarianceSectionMap_transition (V : SmallEtale B Y.obj Y.property)
    {E E' : FiniteSupport B (j ≫ f) V} (h : E ⟶ E') :
    (finiteSupportDiagram B (j ≫ f) ((openRestriction B j).obj F) V).map h ≫
        AddCommGrpCat.ofHom (covarianceSectionMap B j f F V E' _
          (imageFiniteSupport_coe B j f V E')) =
      AddCommGrpCat.ofHom (covarianceSectionMap B j f F V E _
          (imageFiniteSupport_coe B j f V E)) ≫
        (finiteSupportDiagram B f F V).map
          (homOfLE (imageFiniteSupport_mono B j f V (leOfHom h))) := by
  have hc := covarianceTargetOpenMap_square B j f (𝟙 V) E E' _ _
    (imageFiniteSupport_coe B j f V E) (imageFiniteSupport_coe B j f V E')
    (finiteSupportTransitionOpenMap B (j ≫ f) V h)
    (finiteSupportTransitionOpenMap B f V
      (homOfLE (imageFiniteSupport_mono B j f V (leOfHom h))))
    (by
      simp only [CategoryTheory.Functor.map_id, Category.comp_id, openObjectHomOfLE_map]
      exact Scheme.homOfLE_ι _ _)
    (by
      simp only [CategoryTheory.Functor.map_id, Category.comp_id, openObjectHomOfLE_map]
      exact Scheme.homOfLE_ι _ _)
  exact AddCommGrpCat.hom_ext (covarianceSectionMap_map B j f F V V E E' _ _
    (imageFiniteSupport_coe B j f V E) (imageFiniteSupport_coe B j f V E')
    _ _ hc _ _ (finiteSupportDiagram_map_val B (j ≫ f) _ V h)
      (finiteSupportDiagram_map_val B f F V
        (homOfLE (imageFiniteSupport_mono B j f V (leOfHom h))))).symm

/-- The canonical map on finite-support sections over an étale test object. -/
public def covarianceColimitMap (V : SmallEtale B Y.obj Y.property) :
    finiteSupportSections B (j ≫ f) ((openRestriction B j).obj F) V ⟶
      finiteSupportSections B f F V :=
  colimit.desc _
    { pt := finiteSupportSections B f F V
      ι :=
        { app E := AddCommGrpCat.ofHom (covarianceSectionMap B j f F V E _
              (imageFiniteSupport_coe B j f V E)) ≫
            colimit.ι (finiteSupportDiagram B f F V) (imageFiniteSupport B j f V E)
          naturality E E' h := by
            dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
            rw [Category.comp_id]
            refine (Category.assoc _ _ _).symm.trans ?_
            refine Eq.trans (congrArg (fun z => z ≫
              colimit.ι (finiteSupportDiagram B f F V) (imageFiniteSupport B j f V E'))
              (covarianceSectionMap_transition B j f F V h)) ?_
            exact (Category.assoc _ _ _).trans
              (congrArg (fun z => AddCommGrpCat.ofHom (covarianceSectionMap B j f F V E _
                  (imageFiniteSupport_coe B j f V E)) ≫ z)
                (colimit.w (finiteSupportDiagram B f F V)
                  (homOfLE (imageFiniteSupport_mono B j f V (leOfHom h))))) } }

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The canonical map on finite-support sections on a colimit generator. -/
public theorem covarianceColimitMap_ι (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) :
    colimit.ι (finiteSupportDiagram B (j ≫ f) ((openRestriction B j).obj F) V) E ≫
        covarianceColimitMap B j f F V =
      AddCommGrpCat.ofHom (covarianceSectionMap B j f F V E _
          (imageFiniteSupport_coe B j f V E)) ≫
        colimit.ι (finiteSupportDiagram B f F V) (imageFiniteSupport B j f V E) :=
  colimit.ι_desc _ E

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The canonical map on finite-support sections on a colimit generator, for any support
realizing the image. -/
public theorem covarianceColimitMap_ι_of_image (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    colimit.ι (finiteSupportDiagram B (j ≫ f) ((openRestriction B j).obj F) V) E ≫
        covarianceColimitMap B j f F V =
      AddCommGrpCat.ofHom (covarianceSectionMap B j f F V E D hD) ≫
        colimit.ι (finiteSupportDiagram B f F V) D := by
  obtain rfl : D = imageFiniteSupport B j f V E :=
    Subtype.ext (hD.trans (imageFiniteSupport_coe B j f V E).symm)
  exact covarianceColimitMap_ι B j f F V E

/-- On each finite-support generator, the target support is the image under the open immersion
and the target section restricts to the original section. The map of canonical support opens
records the comparison of the two restrictions of the sheaf. -/
public structure CovarianceGeneratorData (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) where
  /-- The support of the extended section. -/
  support : FiniteSupport B f V
  /-- The support of the extended section is the image of the original support. -/
  support_eq : support.1 = (openBaseChangeHom B j f V).base '' E.1
  /-- The extension map on supported sections. -/
  sectionMap :
    supportedSections B X'.obj X'.property ((openRestriction B j).obj F)
        (baseChange B (j ≫ f) V) E.1 (finiteSupport_isLocallyClosed B (j ≫ f) V E) →+
      supportedSections B X.obj X.property F (baseChange B f V) support.1
        (finiteSupport_isLocallyClosed B f V support)
  /-- The comparison of canonical support opens. -/
  openMap :
    openObject B X'.obj X'.property (baseChange B (j ≫ f) V)
        (supportOpen B X'.obj X'.property (baseChange B (j ≫ f) V) E.1
          (finiteSupport_isLocallyClosed B (j ≫ f) V E)) ⟶
      (smallEtaleBaseChange B j).obj
        (openObject B X.obj X.property (baseChange B f V)
          (supportOpen B X.obj X.property (baseChange B f V) support.1
            (finiteSupport_isLocallyClosed B f V support)))
  /-- The comparison of canonical support opens lies over the induced open immersion. -/
  openMap_commutes :
    (SmallEtale.toScheme B X'.obj X'.property).map openMap ≫
        B.inclusion.map (pullback.fst
          ((openObject B X.obj X.property (baseChange B f V)
            (supportOpen B X.obj X.property (baseChange B f V) support.1
              (finiteSupport_isLocallyClosed B f V support))).obj.hom) j) ≫
        (supportOpen B X.obj X.property (baseChange B f V) support.1
          (finiteSupport_isLocallyClosed B f V support)).ι =
      (supportOpen B X'.obj X'.property (baseChange B (j ≫ f) V) E.1
        (finiteSupport_isLocallyClosed B (j ≫ f) V E)).ι ≫ openBaseChangeHom B j f V
  /-- The extended section restricts to the original section on the open subscheme. -/
  sectionMap_apply : ∀ s,
    ((openRestriction B j).obj F).obj.map openMap.op
      ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous
        AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
          (op (openObject B X.obj X.property (baseChange B f V)
            (supportOpen B X.obj X.property (baseChange B f V) support.1
              (finiteSupport_isLocallyClosed B f V support))))
          (sectionMap s).val) = s.val

/-- The canonical covariance data on a finite-support generator. -/
public def covarianceGeneratorData (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) : CovarianceGeneratorData B j f F V E where
  support := imageFiniteSupport B j f V E
  support_eq := imageFiniteSupport_coe B j f V E
  sectionMap := covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E)
  openMap := covarianceOpenMap B j f V E _ (imageFiniteSupport_coe B j f V E)
  openMap_commutes := covarianceOpenMap_commutes B j f V E _
    (imageFiniteSupport_coe B j f V E)
  sectionMap_apply s := by
    have hm : F.obj.map ((openPostcomposeAdjunction B j).counit.app
          (openCovarianceSupportObject B f V (imageFiniteSupport B j f V E))).op ≫
        F.obj.map ((openPostcompose B j).map
          (covarianceOpenMap B j f V E _ (imageFiniteSupport_coe B j f V E))).op =
      F.obj.map (covarianceTargetOpenMap B j f V E _
        (imageFiniteSupport_coe B j f V E)).op := by
      rw [← Functor.map_comp, ← op_comp,
        covarianceOpenMap_counit B j f V E _ (imageFiniteSupport_coe B j f V E)]
    rw [← openRestrictionIso_unit_app]
    refine Eq.trans
      ((ConcreteCategory.comp_apply _ _ _).symm.trans
        ((ConcreteCategory.congr_hom
          (((openRestrictionIso.{u, v} B j).hom.app F).hom.naturality
            (covarianceOpenMap B j f V E _ (imageFiniteSupport_coe B j f V E)).op).symm _).trans
          (ConcreteCategory.comp_apply _ _ _))) ?_
    refine Eq.trans (congrArg (((openRestrictionIso.{u, v} B j).hom.app F).hom.app
        (op (openCovarianceSupportObject B (j ≫ f) V E)))
      ((ConcreteCategory.comp_apply _ _ _).symm.trans
        (ConcreteCategory.congr_hom hm _))) ?_
    rw [covarianceSectionMap_restrict]
    exact ConcreteCategory.congr_hom
      (congrArg (fun k => k.hom.app (op (openCovarianceSupportObject B (j ≫ f) V E)))
        ((openRestrictionIso.{u, v} B j).inv_hom_id_app F)) s.val

end Colimit

section Presheaf

variable (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)]

/-- The covariance map of finite-support direct-image presheaves over an étale test
object. -/
public def covariancePresheafApp
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (V : SmallEtale B Y.obj Y.property) :
    ((openFiniteSupportPushforward.{u, v} B j f).obj F).obj (op V) ⟶
      ((wholeFiniteSupportPushforward.{u, v} B f).obj F).obj (op V) :=
  eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B (j ≫ f)
      (fun _ => inferInstance)).property.obj_eq ((openRestriction B j).obj F) V) ≫
    covarianceColimitMap B j f F V ≫
      eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
        (fun _ => inferInstance)).property.obj_eq F V).symm

/-- The covariance map on a colimit generator is the canonical map on supported sections. -/
public theorem covariancePresheafApp_generator
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B (j ≫ f) V)
    (D : FiniteSupport B f V) (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    finiteSupportPushforwardGenerator B (j ≫ f) ((openRestriction B j).obj F) V E ≫
        covariancePresheafApp B j f F V =
      AddCommGrpCat.ofHom (covarianceSectionMap B j f F V E D hD) ≫
        finiteSupportPushforwardGenerator B f F V D := by
  simp only [finiteSupportPushforwardGenerator, covariancePresheafApp, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ eqToHom _)
    (covarianceColimitMap_ι_of_image B j f F V E D hD)) ?_
  exact Category.assoc _ _ _

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- Base change of the image support is the image of the base change of the support. -/
public theorem baseChange_image_support
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    (finiteSupportBaseChange B f F g D).support.1 =
      (openBaseChangeHom B j f V').base ''
        (finiteSupportBaseChange B (j ≫ f) ((openRestriction B j).obj F) g E).support.1 := by
  rw [(finiteSupportBaseChange B f F g D).support_eq,
    (finiteSupportBaseChange B (j ≫ f) ((openRestriction B j).obj F) g E).support_eq,
    hD, openBaseChangeHom_image_preimage]

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The canonical map on supported sections commutes with base change along a morphism of
étale test objects. -/
private theorem covarianceSectionMap_baseChange
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V) (E : FiniteSupport B (j ≫ f) V)
    (hD' : (finiteSupportBaseChange B f F g (imageFiniteSupport B j f V E)).support.1 =
      (openBaseChangeHom B j f V').base ''
        (finiteSupportBaseChange B (j ≫ f) ((openRestriction B j).obj F) g E).support.1) :
    AddCommGrpCat.ofHom
          (finiteSupportBaseChange B (j ≫ f) ((openRestriction B j).obj F) g E).sectionsMap ≫
        AddCommGrpCat.ofHom (covarianceSectionMap B j f F V'
          (finiteSupportBaseChange B (j ≫ f) ((openRestriction B j).obj F) g E).support
          (finiteSupportBaseChange B f F g (imageFiniteSupport B j f V E)).support hD') =
      AddCommGrpCat.ofHom (covarianceSectionMap B j f F V E _
          (imageFiniteSupport_coe B j f V E)) ≫
        AddCommGrpCat.ofHom
          (finiteSupportBaseChange B f F g (imageFiniteSupport B j f V E)).sectionsMap := by
  have hc := covarianceTargetOpenMap_square B j f g E
    (finiteSupportBaseChange B (j ≫ f) ((openRestriction B j).obj F) g E).support
    (imageFiniteSupport B j f V E)
    (finiteSupportBaseChange B f F g (imageFiniteSupport B j f V E)).support
    (imageFiniteSupport_coe B j f V E) hD'
    (finiteSupportBaseChange B (j ≫ f) ((openRestriction B j).obj F) g E).openMap
    (finiteSupportBaseChange B f F g (imageFiniteSupport B j f V E)).openMap
    (finiteSupportBaseChange B (j ≫ f) ((openRestriction B j).obj F) g E).openMap_commutes
    (finiteSupportBaseChange B f F g (imageFiniteSupport B j f V E)).openMap_commutes
  exact AddCommGrpCat.hom_ext (covarianceSectionMap_map B j f F V V' E _ _ _
    (imageFiniteSupport_coe B j f V E) hD' _ _ hc _ _
    (finiteSupportBaseChange B (j ≫ f) ((openRestriction B j).obj F) g E).sectionsMap_apply
    (finiteSupportBaseChange B f F g (imageFiniteSupport B j f V E)).sectionsMap_apply).symm

/-- Pasting identities for generators of two parallel squares into one square. -/
private theorem comp_eq_of_square {C : Type*} [Category C] {G G' H H' P P' Q Q' : C}
    {gE : G ⟶ P} {gE' : G' ⟶ P'} {gD : H ⟶ Q} {gD' : H' ⟶ Q'}
    {m : P ⟶ P'} {n : Q ⟶ Q'} {c : P ⟶ Q} {c' : P' ⟶ Q'}
    {a : G ⟶ G'} {b : G' ⟶ H'} {x : G ⟶ H} {y : H ⟶ H'}
    (hm : gE ≫ m = a ≫ gE') (hc' : gE' ≫ c' = b ≫ gD') (hs : a ≫ b = x ≫ y)
    (hn : gD ≫ n = y ≫ gD') (hc : gE ≫ c = x ≫ gD) :
    gE ≫ m ≫ c' = gE ≫ c ≫ n := by
  rw [← Category.assoc, hm, Category.assoc, hc', ← Category.assoc, hs, Category.assoc, ← hn,
    ← Category.assoc, ← hc, Category.assoc]

/-- The covariance map is natural in the étale test object. -/
public theorem covariancePresheafApp_naturality
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V) :
    ((openFiniteSupportPushforward.{u, v} B j f).obj F).map g.op ≫
        covariancePresheafApp B j f F V' =
      covariancePresheafApp B j f F V ≫
        ((wholeFiniteSupportPushforward.{u, v} B f).obj F).map g.op := by
  refine finiteSupportPushforwardGenerator_hom_ext B (j ≫ f) _ V fun E => ?_
  have hD' : (finiteSupportBaseChange B f F g (imageFiniteSupport B j f V E)).support.1 =
      (openBaseChangeHom B j f V').base ''
        (finiteSupportBaseChange B (j ≫ f) ((openRestriction B j).obj F) g E).support.1 :=
    baseChange_image_support B j f F g E _ (imageFiniteSupport_coe B j f V E)
  exact comp_eq_of_square
    (finiteSupportPushforwardGenerator_restrict B (j ≫ f) ((openRestriction B j).obj F) g E)
    (covariancePresheafApp_generator B j f F V' _ _ hD')
    (covarianceSectionMap_baseChange B j f F g E hD')
    (finiteSupportPushforwardGenerator_restrict B f F g (imageFiniteSupport B j f V E))
    (covariancePresheafApp_generator B j f F V E _ (imageFiniteSupport_coe B j f V E))

/-- The covariance map of finite-support direct-image presheaves. -/
public def covariancePresheafMap
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    (openFiniteSupportPushforward.{u, v} B j f).obj F ⟶
      (wholeFiniteSupportPushforward.{u, v} B f).obj F where
  app V := covariancePresheafApp B j f F V.unop
  naturality _ _ g := covariancePresheafApp_naturality B j f F g.unop

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The canonical map on supported sections commutes with a morphism of abelian sheaves. -/
private theorem covarianceSectionMap_sheaf_comp
    (F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (φ : F ⟶ G) (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B (j ≫ f) V) :
    AddCommGrpCat.ofHom (supportedSectionsSheafMap B X'.obj X'.property
        ((openRestriction B j).map φ) (baseChange B (j ≫ f) V) E.1
        (finiteSupport_isLocallyClosed B (j ≫ f) V E)) ≫
      AddCommGrpCat.ofHom (covarianceSectionMap B j f G V E _
        (imageFiniteSupport_coe B j f V E)) =
    AddCommGrpCat.ofHom (covarianceSectionMap B j f F V E _
        (imageFiniteSupport_coe B j f V E)) ≫
      AddCommGrpCat.ofHom (supportedSectionsSheafMap B X.obj X.property φ
        (baseChange B f V) (imageFiniteSupport B j f V E).1
        (finiteSupport_isLocallyClosed B f V (imageFiniteSupport B j f V E))) :=
  AddCommGrpCat.hom_ext (covarianceSectionMap_sheaf B j f F G φ V E _
    (imageFiniteSupport_coe B j f V E)).symm

/-- The covariance map is natural in the abelian sheaf. -/
public theorem covariancePresheafMap_naturality
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) :
    (openFiniteSupportPushforward.{u, v} B j f).map φ ≫ covariancePresheafMap B j f G =
      covariancePresheafMap B j f F ≫ (wholeFiniteSupportPushforward.{u, v} B f).map φ := by
  apply NatTrans.ext
  funext V
  show ((openFiniteSupportPushforward.{u, v} B j f).map φ).app V ≫
      covariancePresheafApp B j f G V.unop =
    covariancePresheafApp B j f F V.unop ≫
      ((wholeFiniteSupportPushforward.{u, v} B f).map φ).app V
  refine finiteSupportPushforwardGenerator_hom_ext B (j ≫ f) _ V.unop fun E => ?_
  exact comp_eq_of_square
    (finiteSupportPushforwardGenerator_sheaf B (j ≫ f) ((openRestriction B j).obj F)
      ((openRestriction B j).obj G) ((openRestriction B j).map φ) V.unop E)
    (covariancePresheafApp_generator B j f G V.unop E _ (imageFiniteSupport_coe B j f V.unop E))
    (covarianceSectionMap_sheaf_comp B j f F G φ V.unop E)
    (finiteSupportPushforwardGenerator_sheaf B f F G φ V.unop (imageFiniteSupport B j f V.unop E))
    (covariancePresheafApp_generator B j f F V.unop E _ (imageFiniteSupport_coe B j f V.unop E))

/-- A natural presheaf map acts on a finite-support generator by regarding its support and
section on the open subscheme as a support and section on the whole source. -/
public def OpenCovariancePresheafMapSpec
    (α : openFiniteSupportPushforward.{u, v} B j f ⟶
      wholeFiniteSupportPushforward.{u, v} B f) : Prop :=
  ∀ (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B (j ≫ f) V),
    ∃ d : CovarianceGeneratorData B j f F V E,
      colimit.ι (finiteSupportDiagram B (j ≫ f) ((openRestriction B j).obj F) V) E ≫
          eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B (j ≫ f)
            (fun _ => inferInstance)).property.obj_eq
              ((openRestriction B j).obj F) V).symm ≫
          (α.app F).app (op V) ≫
          eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).property.obj_eq F V) =
        AddCommGrpCat.ofHom d.sectionMap ≫
          colimit.ι (finiteSupportDiagram B f F V) d.support

/-- The canonical covariance map of finite-support direct-image presheaves for an open
subscheme of the source. Its generator formula and the canonical extension of supported
sections are part of the construction; naturality in the test object and in the abelian sheaf
is part of its being a natural transformation of functors. -/
@[stacks 0F6S "covariance, presheaf map"]
public def openCovariancePresheafMap :
    {α : openFiniteSupportPushforward.{u, v} B j f ⟶
      wholeFiniteSupportPushforward.{u, v} B f //
      OpenCovariancePresheafMapSpec B j f α} := by
  refine ⟨{ app F := covariancePresheafMap B j f F
            naturality _ _ φ := covariancePresheafMap_naturality B j f φ }, ?_⟩
  intro F V E
  refine ⟨covarianceGeneratorData B j f F V E, ?_⟩
  change colimit.ι (finiteSupportDiagram B (j ≫ f) ((openRestriction B j).obj F) V) E ≫
      eqToHom _ ≫ covariancePresheafApp B j f F V ≫ eqToHom _ =
    AddCommGrpCat.ofHom (covarianceSectionMap B j f F V E _
      (imageFiniteSupport_coe B j f V E)) ≫
      colimit.ι (finiteSupportDiagram B f F V) (imageFiniteSupport B j f V E)
  have h := covariancePresheafApp_generator B j f F V E _
    (imageFiniteSupport_coe B j f V E)
  simp only [finiteSupportPushforwardGenerator] at h
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ eqToHom
      ((finiteSupportPushforward.{u, max (u + 1) v} B f
        (fun _ => inferInstance)).property.obj_eq F V)) h) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => AddCommGrpCat.ofHom
      (covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E)) ≫ z)
    (Category.assoc _ _ _)) ?_
  simp only [eqToHom_trans, eqToHom_refl]
  exact congrArg (fun z => AddCommGrpCat.ofHom
    (covarianceSectionMap B j f F V E _ (imageFiniteSupport_coe B j f V E)) ≫ z)
    (Category.comp_id _)

/-- Restriction to the open subscheme followed by the direct image with compact support along
the composite. -/
public abbrev openShriekPushforward :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v} :=
  openRestriction.{u, v} B j ⋙ fShriekFunctor.{u, v} B (j ≫ f)

/-- Sheafifying the canonical presheaf map gives covariance of the direct image with compact
support under an open immersion of the source. -/
@[stacks 0F6S "covariance"]
public def openCovarianceShriekMap :
    openShriekPushforward.{u, v} B j f ⟶ fShriekFunctor.{u, v} B f :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (openCovariancePresheafMap B j f).val
      (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
        AddCommGrpCat.{max (u + 1) v})

end Presheaf

end AlgebraicGeometry.SmallEtale

end
