module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite-support direct image is the proper-support direct image

Let `f : X ⟶ Y` be a morphism of a big étale site which is separated, locally of finite type and
locally quasi-finite as a morphism of schemes. The finite-support direct image presheaf
`f_{p!}F` of [Stacks, Tag 0F6M] is isomorphic to the proper-support sheaf `f_!F` of
[Stacks, Tag 0F4X], as functors on abelian sheaves on the small étale site of `X`, by an
isomorphism described on the colimit generators.

## Main definitions

* `AlgebraicGeometry.SmallEtale.properSupportPresheafFunctor` — the proper-support direct image
  as a functor to abelian presheaves on the small étale site of `Y`.
* `AlgebraicGeometry.SmallEtale.finiteSupportDiagramBaseChange` — base change of supported
  sections along `V' ⟶ V`, as a morphism between the values of the diagrams of supported
  sections.
* `AlgebraicGeometry.SmallEtale.finiteSupportComparison` — the comparison
  `f_{p!}F ⟶ f_!F` of abelian presheaves on the small étale site of `Y`, and
  `AlgebraicGeometry.SmallEtale.finiteSupportComparisonNatTrans` the same comparison as a
  transformation of functors in `F`.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_finiteSupportComparisonNatTrans` — the comparison is an
  isomorphism.
* `AlgebraicGeometry.SmallEtale.finiteSupportPushforwardIso` — the resulting isomorphism of
  functors, together with the description of its value on the colimit generators: the generator
  of an eligible support carrying a supported section goes to the section of `f_!F` which
  restricts to that section on the canonical open of the support.

## References

* [Stacks Project, Tag 0F6N](https://stacks.math.columbia.edu/tag/0F6N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section ProperSupportPresheaf

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)]

/-- The map on proper-support sections induced by a morphism of abelian sheaves on the small
étale site of `X`, as a morphism of abelian presheaves on the small étale site of `Y`. -/
public def properSupportPresheafMap
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}} (φ : F ⟶ G) :
    (properSupportSheaf B f F).obj ⟶ (properSupportSheaf B f G).obj :=
  ((properSupportFunctor B f).map φ).hom

/-- The proper-support direct image `f_!` of [Stacks, Tag 0F4X] as a functor from abelian sheaves
on the small étale site of `X` to abelian presheaves on the small étale site of `Y`: the
proper-support direct image followed by the inclusion of sheaves into presheaves. -/
public abbrev properSupportPresheafFunctor :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v} ⥤
      ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{v}) where
  obj F := (properSupportSheaf B f F).obj
  map φ := properSupportPresheafMap B f φ
  map_id F := by
    dsimp only [properSupportPresheafMap]
    rw [(properSupportFunctor B f).map_id]
    rfl
  map_comp φ ψ := by
    dsimp only [properSupportPresheafMap]
    rw [(properSupportFunctor B f).map_comp]
    rfl

end ProperSupportPresheaf

section Comparison

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v})

/-- Base change of supported sections along a morphism `V' ⟶ V` of the small étale site of `Y`,
read as a morphism from the value of the diagram of supported sections at an eligible support
over `V` to its value at the inverse image of that support. -/
public def finiteSupportDiagramBaseChange {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    (E : FiniteSupport B f V) :
    (finiteSupportDiagram B f F V).obj E ⟶
      (finiteSupportDiagram B f F V').obj (finiteSupportBaseChange B f F g E).support :=
  AddCommGrpCat.ofHom (finiteSupportBaseChange B f F g E).sectionsMap

variable (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{max u v} (FiniteSupport B f V))
  (P : {P : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v} ⥤
      ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) //
    FiniteSupportPushforwardSpec B f hsmall P})

omit [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The restriction rule of the finite-support direct image on a colimit generator, with base
change of supported sections read as a morphism of the diagrams of supported sections. -/
private lemma map_restrict_diagramBaseChange {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    (E : FiniteSupport B f V) :
    letI := hsmall V
    letI := hsmall V'
    colimit.ι (finiteSupportDiagram B f F V) E ≫
        eqToHom (P.property.obj_eq F V).symm ≫
        (P.val.obj F).map g.op ≫ eqToHom (P.property.obj_eq F V') =
      finiteSupportDiagramBaseChange B f F g E ≫
        colimit.ι (finiteSupportDiagram B f F V')
          (finiteSupportBaseChange B f F g E).support :=
  P.property.map_restrict F g E

/-- The comparison from the finite-support direct image of `F` to its proper-support direct
image, as a morphism of abelian presheaves on the small étale site of `Y`, given over an étale
test object by the sectionwise comparison. -/
public def finiteSupportComparison : P.val.obj F ⟶ (properSupportSheaf B f F).obj where
  app V := finiteSupportComparisonApp B f F hsmall P V.unop
  naturality := by
    classical
    rintro ⟨V⟩ ⟨V'⟩ g
    apply (cancel_epi (eqToHom (P.property.obj_eq F V).symm)).1
    apply colimit.hom_ext
    intro E
    have hs := map_restrict_diagramBaseChange B f F hsmall P g.unop E
    simp only [Quiver.Hom.op_unop] at hs
    dsimp only [finiteSupportComparisonApp]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% hs, finiteSupportColimitToProper_ι]
    conv_rhs => rw [← Category.assoc, finiteSupportColimitToProper_ι]
    ext s
    exact finiteSupportStageMap_restrict B f F g.unop E s

end Comparison

section Functorial

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)]
  (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{max u v} (FiniteSupport B f V))
  (P : {P : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v} ⥤
      ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) //
    FiniteSupportPushforwardSpec B f hsmall P})

omit [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The action of a morphism of abelian sheaves on the finite-support direct image, read on a
colimit generator through the induced morphism of the diagrams of supported sections. -/
private lemma map_sheaf_diagramMap
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v}}
    (φ : F ⟶ G) (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    letI := hsmall V
    colimit.ι (finiteSupportDiagram B f F V) E ≫
        eqToHom (P.property.obj_eq F V).symm ≫
        (P.val.map φ).app (op V) ≫ eqToHom (P.property.obj_eq G V) =
      (finiteSupportDiagramMap B f φ V).app E ≫
        colimit.ι (finiteSupportDiagram B f G V) E :=
  P.property.map_sheaf φ V E

/-- The comparison from the finite-support direct image to the proper-support direct image, as a
transformation of functors on abelian sheaves. -/
public def finiteSupportComparisonNatTrans :
    P.val ⟶ properSupportPresheafFunctor.{u, max u v} B f where
  app F := finiteSupportComparison B f F hsmall P
  naturality := by
    classical
    intro F G φ
    ext ⟨V⟩ : 2
    dsimp only [NatTrans.comp_app, finiteSupportComparison]
    apply (cancel_epi (eqToHom (P.property.obj_eq F V).symm)).1
    apply colimit.hom_ext
    intro E
    have hs := map_sheaf_diagramMap B f hsmall P φ V E
    dsimp only [finiteSupportComparisonApp]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% hs, finiteSupportColimitToProper_ι]
    conv_rhs => rw [← Category.assoc, finiteSupportColimitToProper_ι]
    ext s
    exact finiteSupportStageMap_sheaf B f φ V E s

/-- The comparison from the finite-support direct image to the proper-support direct image is an
isomorphism of functors. -/
public instance isIso_finiteSupportComparisonNatTrans :
    IsIso (finiteSupportComparisonNatTrans.{u, v} B f hsmall P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  have := hsmall V.unop
  dsimp only [finiteSupportComparisonNatTrans, finiteSupportComparison,
    finiteSupportComparisonApp]
  have : IsIso (finiteSupportColimitToProper B f F V.unop) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (finiteSupportColimitToProper_bijective B f F V.unop)
  infer_instance

end Functorial

/-- For a separated, locally finite type and locally quasi-finite morphism `f` of a big étale
site, the finite-support direct image presheaf `f_{p!}` of [Stacks, Tag 0F6M] is isomorphic to
the proper-support direct image `f_!` of [Stacks, Tag 0F4X], as functors from abelian
sheaves on the small étale site of `X` to abelian presheaves on the small étale site of `Y`. The
isomorphism is pinned down on the colimit generators: the generator of an eligible support
carrying a supported section goes to the section of `f_!F` which restricts to that section on
the canonical open of the support. -/
@[stacks 0F6N, sga "4 XVII 6.3.16" "colimit formula"]
public def finiteSupportPushforwardIso (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
    [LocallyQuasiFinite (B.inclusion.map f)] :
    let hsmall : ∀ V : SmallEtale B Y.obj Y.property,
      Small.{max u v} (FiniteSupport B f V) := fun _ => inferInstance
    let P := finiteSupportPushforward.{u, max u v} B f hsmall
    {e : P.val ≅ properSupportFunctor B f ⋙
        sheafToPresheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max u v} //
      ∀ (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v})
        (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
        (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E)),
        letI := hsmall V
        (F.obj.map (openObjectι B X.obj X.property (baseChange B f V)
            (finiteSupportOpen B f V E)).op).hom
          ((colimit.ι (finiteSupportDiagram B f F V) E ≫
            eqToHom (P.property.obj_eq F V).symm ≫
            (e.hom.app F).app (op V) ≫
            (fShriekSubsheaf B f F).val.arrow.hom.app (op V)).hom s) = s.val} := by
  classical
  intro hsmall P
  refine ⟨(asIso (finiteSupportComparisonNatTrans.{u, v} B f hsmall P) :
    P.val ≅ properSupportPresheafFunctor.{u, max u v} B f), ?_⟩
  intro F V E s
  have := hsmall V
  have hι := finiteSupportComparisonApp_ι B f F hsmall P V E
  change (F.obj.map (openObjectι B X.obj X.property (baseChange B f V)
        (finiteSupportOpen B f V E)).op).hom
      ((colimit.ι (finiteSupportDiagram B f F V) E ≫
        eqToHom (P.property.obj_eq F V).symm ≫
        finiteSupportComparisonApp B f F hsmall P V ≫
        (fShriekSubsheaf B f F).val.arrow.hom.app (op V)).hom s) = s.val
  have h := ConcreteCategory.congr_hom
    ((reassoc_of% hι) ((fShriekSubsheaf B f F).val.arrow.hom.app (op V))) s
  exact (congrArg _ (h.trans (finiteSupportStageMap_arrow B f F V E s))).trans
    (finiteSupportExtension_restrict B f F V E s)

end AlgebraicGeometry.SmallEtale

end
