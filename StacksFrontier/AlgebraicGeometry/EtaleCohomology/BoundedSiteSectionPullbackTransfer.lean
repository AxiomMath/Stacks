module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CoefficientsGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.Shrink
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeSupport

/-!
# Pulling back sections along base change, on the two presentations of the small étale site

Let `B` be a big étale site and `p : P ⟶ X` a morphism of its underlying category. The small
étale site of a scheme has two presentations in this library: the size-bounded site
`AlgebraicGeometry.SmallEtale` of Stacks 021B, on which the inverse image along `p` is
`CategoryTheory.Functor.sheafPullback` for `AlgebraicGeometry.smallEtaleBaseChange`, and
Mathlib's site `AlgebraicGeometry.Scheme.Etale`, on which it is
`Stacks.EtaleCohomology.smallEtaleInverseImage`. This file shows that pulling back a section of
an abelian sheaf on the first and then restricting to global sections agrees, under explicit
bijections, with pulling back the corresponding section of the corresponding sheaf of sets on the
second.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_sectionPullback_transfer`: the transfer statement.
* `AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChange_unit_apply`: the comparison of
  inverse images along the restriction functors carries a pulled-back section to the
  pulled-back section.
* `Stacks.Sites.coefficientPullbackTwoSquare_unit`: the comparison of inverse images with a
  change of coefficients matches the units of the two adjunctions.
* `Stacks.Sites.sheafPullbackConstruction_unit_app_hom`: the unit of the constructed
  inverse-image adjunction is the Kan extension unit followed by sheafification.
* `AlgebraicGeometry.SmallEtale.preservesLeftKanExtensions_forget_smallEtaleBaseChange_max`:
  the forgetful functor of abelian groups of any universe at least `u + 1` preserves left Kan
  extensions along the opposite of base change of étale schemes.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.Sites

section Abstract

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {F : C ⥤ D} {G : D ⥤ E}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {A : Type*} [Category* A] [F.IsContinuous J K] [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L]

/-- The comparison `CategoryTheory.Functor.sheafPushforwardContinuousComp'` along the identity
isomorphism of a composite is the identity on sections. -/
public theorem sheafPushforwardContinuousComp'_refl_hom_app (M : Sheaf L A) (U : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousComp' (Iso.refl (F ⋙ G)) A J K L).hom.app M).hom.app U =
      𝟙 _ := by
  rw [Functor.sheafPushforwardContinuousComp', Iso.trans_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuousComp_hom_app_hom_app]
  exact (Category.id_comp _).trans (M.obj.map_id _)

/-- The inverse of `CategoryTheory.Functor.sheafPushforwardContinuousComp'` along the identity
isomorphism of a composite is the identity on sections. -/
public theorem sheafPushforwardContinuousComp'_refl_inv_app (M : Sheaf L A) (U : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousComp' (Iso.refl (F ⋙ G)) A J K L).inv.app M).hom.app U =
      𝟙 _ := by
  rw [Functor.sheafPushforwardContinuousComp', Iso.trans_inv, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuousComp_inv_app_hom_app]
  exact (Category.comp_id _).trans (M.obj.map_id _)

/-- The direct image of a natural isomorphism of functors of sites acts on sections by
restriction along the inverse. -/
private theorem sheafPushforwardContinuousIso_hom_app_app {F' : C ⥤ D} [F'.IsContinuous J K]
    (e : F ≅ F') (M : Sheaf K A) (U : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousIso e A J K).hom.app M).hom.app U =
      M.obj.map (e.inv.app U.unop).op :=
  rfl
end Abstract

section Unit

variable {C D : Type*} [Category* C] [Category* D] (uf : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
  {A : Type*} [Category* A] [HasWeakSheafify K A] [∀ P : Cᵒᵖ ⥤ A, uf.op.HasLeftKanExtension P]

/-- **The unit of the inverse-image/direct-image adjunction of
`CategoryTheory.Functor.sheafPullbackConstruction`** is the unit of the left Kan extension
followed by the sheafification unit, restricted along the functor of sites. -/
public theorem sheafPullbackConstruction_unit_app_hom (c : Sheaf J A) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A J K).unit.app c).hom =
      uf.op.leftKanExtensionUnit c.obj ≫
        Functor.whiskerLeft uf.op (toSheafify K (uf.op.leftKanExtension c.obj)) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
      (L := Functor.sheafPullbackConstruction.sheafPullback uf A J K)
      (R := uf.sheafPushforwardContinuous A J K)
      ((uf.op.lanAdjunction A).comp (sheafificationAdjunction K A))
      (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id (Sheaf K A))
      (Iso.refl _) (Iso.refl _) c
  refine h.trans ?_
  simp only [Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
    sheafificationAdjunction_unit_app, ObjectProperty.ι_obj, Iso.refl_hom, NatTrans.id_app]
  exact (congrArg (_ ≫ ·) ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
    (Category.id_comp _))).trans (Category.comp_id _)

end Unit

section Coefficients

variable {C D : Type*} [Category* C] [Category* D] (uf : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
  {A B : Type*} [Category* A] [Category* B] (Gf : A ⥤ B)
  [HasWeakSheafify K A] [HasWeakSheafify K B]
  [∀ P : Cᵒᵖ ⥤ A, uf.op.HasLeftKanExtension P] [∀ P : Cᵒᵖ ⥤ B, uf.op.HasLeftKanExtension P]
  [J.HasSheafCompose Gf] [K.HasSheafCompose Gf]

/-- **The comparison of inverse images with a change of coefficients matches the two units.**
The unit of the inverse-image adjunction for `B`-valued sheaves, followed by the direct image of
`Stacks.EtaleCohomology.coefficientPullbackTwoSquare`, is the coefficient functor applied to the
unit for `A`-valued sheaves. This is `CategoryTheory.unit_mateEquiv_symm` for the identity
comparison of direct images. -/
public theorem coefficientPullbackTwoSquare_unit (c : Sheaf J A) :
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf B J K).unit.app
          ((sheafCompose J Gf).obj c) ≫
        (uf.sheafPushforwardContinuous B J K).map
          ((Stacks.EtaleCohomology.coefficientPullbackTwoSquare uf J K Gf).app c) =
      (sheafCompose J Gf).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A J K).unit.app c) :=
  (unit_mateEquiv_symm (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A J K)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf B J K)
      (Stacks.EtaleCohomology.coefficientPushforwardTwoSquare uf J K Gf) c).symm.trans
    (Category.comp_id _)

end Coefficients

end Stacks.Sites

namespace AlgebraicGeometry.SmallEtale

open Stacks.Sites

section Comparison

variable (B : BigEtaleSite.{u})

variable {S T : B.Scheme} (f : T ⟶ S) {A : Type*} [Category* A] in
/-- **The component of the comparison of direct images along the two presentations of the small
étale site** is restriction along the comparison of the two base changes. -/
public theorem toEtaleSitePushforwardBaseChangeIso_hom_app_app
    (M : Sheaf T.obj.smallEtaleTopology A)
    (V : SmallEtale B S.obj S.property) :
    ((toEtaleSitePushforwardBaseChangeIso B f A).hom.app M).hom.app (op V) =
      M.obj.map ((toEtaleSiteBaseChangeIso B f).hom.app V).op := by
  have : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous (B.inclusion.map f)
  have : (toEtaleSite B S.obj S.property ⋙
      Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      (topology B S.obj S.property) T.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ S.obj.smallEtaleTopology _
  have : (AlgebraicGeometry.smallEtaleBaseChange B f ⋙
      toEtaleSite B T.obj T.property).IsContinuous
      (topology B S.obj S.property) T.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (topology B T.obj T.property) _
  unfold toEtaleSitePushforwardBaseChangeIso
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, NatTrans.comp_app, sheafPushforwardContinuousComp'_refl_hom_app,
    sheafPushforwardContinuousComp'_refl_inv_app, sheafPushforwardContinuousIso_hom_app_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

end Comparison

section Forget

/-- **The forgetful functor of abelian groups preserves left Kan extensions along the opposite of
base change of étale schemes**, for abelian groups in every universe at least `u + 1`. This is
`Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange` with the
coefficient universe left free: base change is representably flat, so the costructured-arrow
categories indexing the Kan extension are filtered, and the forgetful functor preserves filtered
colimits of their size. -/
public instance preservesLeftKanExtensions_forget_smallEtaleBaseChange_max {X Y : Scheme.{u}}
    (i : Y ⟶ X) :
    (forget AddCommGrpCat.{max (u + 1) v}).PreservesLeftKanExtensions
      (Stacks.EtaleCohomology.smallEtaleBaseChange i).op := by
  intro Q
  have hfil : ∀ V : Y.Etaleᵒᵖ,
      IsFiltered (CostructuredArrow (Stacks.EtaleCohomology.smallEtaleBaseChange i).op V) :=
    fun V => IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (Stacks.EtaleCohomology.smallEtaleBaseChange i) V.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
  infer_instance

end Forget

variable (B : BigEtaleSite.{u}) {P X : B.Scheme} (p : P ⟶ X)

/-- Equal morphisms of sheaves act equally on sections. -/
private theorem sheafHom_app_apply_congr {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] {M N : Sheaf J A}
    {f g : M ⟶ N} (h : f = g) (U : Cᵒᵖ) (x : ToType (M.obj.obj U)) :
    ConcreteCategory.hom (f.hom.app U) x = ConcreteCategory.hom (g.hom.app U) x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg InducedCategory.Hom.hom h) U) x

section MateUnit

variable {LU : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf P.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  (adjU : LU ⊣ (Stacks.EtaleCohomology.smallEtaleBaseChange
      (B.inclusion.map p)).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      X.obj.smallEtaleTopology P.obj.smallEtaleTopology)

/-- **The comparison of inverse images along the restriction functors carries a pulled-back
section to the pulled-back section.** Let `M` be an abelian sheaf on Mathlib's small étale site
of `X` and `t` a section of `M` over the image of an object `V` of the bounded site. Pulling `t`
back to the bounded inverse image of the restriction of `M`, restricting along
`a : final ⟶ V ×_X P`, and applying the comparison
`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChange` gives the restriction of the
pullback of `t` to Mathlib's inverse image along the corresponding morphism of Mathlib's site.

This is the unit identity of a mate, `CategoryTheory.unit_mateEquiv`, for the square whose mate
is the comparison of direct images
(`AlgebraicGeometry.SmallEtale.mateEquiv_restrictionPullbackBaseChange`). -/
public theorem restrictionPullbackBaseChange_unit_apply
    (M : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (V : SmallEtale B X.obj X.property)
    (a : SmallEtale.final B P.obj P.property ⟶ (smallEtaleBaseChange B p).obj V)
    (t : M.obj.obj (op ((toEtaleSite B X.obj X.property).obj V))) :
    ((restrictionPullbackBaseChange B AddCommGrpCat.{max (u + 1) v} p adjU
        ((smallEtaleBaseChange B p).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B P.obj P.property))).app M).hom.app
        (op (SmallEtale.final B P.obj P.property))
      ((((smallEtaleBaseChange B p).sheafPullback AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B P.obj P.property)).obj
          (((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
            AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B X.obj X.property)
            X.obj.smallEtaleTopology).obj M)).obj.map a.op
        ((((smallEtaleBaseChange B p).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B P.obj P.property)).unit.app
          (((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
            AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B X.obj X.property)
            X.obj.smallEtaleTopology).obj M)).hom.app (op V) t)) =
      (LU.obj M).obj.map ((toEtaleSite B P.obj P.property).map a ≫
          (toEtaleSiteBaseChangeIso B p).hom.app V).op
        ((adjU.unit.app M).hom.app (op ((toEtaleSite B X.obj X.property).obj V)) t) := by
  set adjB := (smallEtaleBaseChange B p).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B P.obj P.property)
  set α := restrictionPullbackBaseChange B AddCommGrpCat.{max (u + 1) v} p adjU adjB
  have h2 := sheafHom_app_apply_congr (unit_mateEquiv adjU adjB α M) (op V) t
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h2
  refine (NatTrans.naturality_apply (α.app M).hom a.op _).trans ?_
  have hm' : ((mateEquiv adjU adjB) α).app (LU.obj M) =
      (toEtaleSitePushforwardBaseChangeIso B p AddCommGrpCat.{max (u + 1) v}).hom.app (LU.obj M) :=
    NatTrans.congr_app
      (mateEquiv_restrictionPullbackBaseChange B AddCommGrpCat.{max (u + 1) v} p adjU adjB) _
  have h3 : ConcreteCategory.hom ((α.app M).hom.app
        (op ((smallEtaleBaseChange B p).obj V)))
        (ConcreteCategory.hom ((adjB.unit.app
          (((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
            AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B X.obj X.property)
            X.obj.smallEtaleTopology).obj M)).hom.app (op V)) t) =
      ConcreteCategory.hom ((LU.obj M).obj.map ((toEtaleSiteBaseChangeIso B p).hom.app V).op)
        (ConcreteCategory.hom ((adjU.unit.app M).hom.app
          (op ((toEtaleSite B X.obj X.property).obj V))) t) := by
    refine h2.symm.trans ?_
    refine (sheafHom_app_apply_congr hm' (op V) _).trans ?_
    exact ConcreteCategory.congr_hom (toEtaleSitePushforwardBaseChangeIso_hom_app_app B p _ _) _
  rw [h3]
  exact (ConcreteCategory.congr_hom ((LU.obj M).obj.map_comp
    ((toEtaleSiteBaseChangeIso B p).hom.app V).op ((toEtaleSite B P.obj P.property).map a).op)
    _).symm

end MateUnit

/-- The morphism `a.hom.left ≫ baseChangeObjProjection B p V`, read in all schemes, lies over
`p`: it is the condition under which it lifts to a morphism of Mathlib's small étale site of `P`
from the identity object into the base change of `V`. -/
public theorem baseChangeLift_condition (V : SmallEtale B X.obj X.property)
    (a : SmallEtale.final B P.obj P.property ⟶ (smallEtaleBaseChange B p).obj V) :
    B.inclusion.map (a.hom.left ≫ baseChangeObjProjection B p V) ≫
      ((toEtaleSite B X.obj X.property).obj V).hom = B.inclusion.map p := by
  change B.inclusion.map _ ≫ B.inclusion.map V.obj.hom = _
  rw [← B.inclusion.map_comp, Category.assoc, (isPullback_baseChangeObjProjection B p V).w,
    ← Category.assoc, Over.w a.hom]
  exact congrArg B.inclusion.map (Category.id_comp p)

/-- A morphism of Mathlib's small étale site of `P` from the identity object whose underlying
morphism is the identity, followed by the image of `a` and the comparison of base changes, is the
lift of `a.hom.left ≫ baseChangeObjProjection B p V`. -/
public theorem comp_toEtaleSiteBaseChangeIso_hom_eq_smallEtaleBaseChangeLift
    (V : SmallEtale B X.obj X.property)
    (a : SmallEtale.final B P.obj P.property ⟶ (smallEtaleBaseChange B p).obj V)
    (τ : Scheme.Etale.mk (𝟙 P.obj) ⟶
      (toEtaleSite B P.obj P.property).obj (SmallEtale.final B P.obj P.property))
    (hτ : τ.left = 𝟙 P.obj) :
    τ ≫ (toEtaleSite B P.obj P.property).map a ≫ (toEtaleSiteBaseChangeIso B p).hom.app V =
      Stacks.EtaleCohomology.smallEtaleBaseChangeLift (B.inclusion.map p)
        ((toEtaleSite B X.obj X.property).obj V)
        (B.inclusion.map (a.hom.left ≫ baseChangeObjProjection B p V))
        (baseChangeLift_condition B p V a) := by
  apply MorphismProperty.Over.Hom.ext
  refine Eq.trans ?_ (Stacks.EtaleCohomology.smallEtaleBaseChangeLift_left (B.inclusion.map p) _
    _ (baseChangeLift_condition B p V a)).symm
  apply pullback.hom_ext
  · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
    have hml : (τ ≫ (toEtaleSite B P.obj P.property).map a ≫
        (toEtaleSiteBaseChangeIso B p).hom.app V).left = τ.left ≫ B.inclusion.map a.hom.left ≫
          (PreservesPullback.iso B.inclusion V.obj.hom p).hom := rfl
    rw [hml, hτ]
    refine (congrArg (· ≫ _) (Category.id_comp _)).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (B.inclusion.map a.hom.left ≫ ·)
      (PreservesPullback.iso_hom_fst B.inclusion V.obj.hom p)).trans
        (B.inclusion.map_comp _ _).symm)
  · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
    exact MorphismProperty.Over.w _

/-- **Pulling back sections along base change agrees on the two presentations of the small étale
site.** Let `B` be a big étale site, `p : P ⟶ X` a morphism of its underlying category and `G` an
abelian sheaf on the bounded small étale site of `X` (Stacks 021B). There is a sheaf of sets `H`
on Mathlib's small étale site of `X` — the underlying sheaf of sets of the abelian sheaf
corresponding to `G` under `AlgebraicGeometry.SmallEtale.sheafEquiv` — together with bijections

* `eX`: the sections of `G` over `U` with the sections of `H` over the image of `U`, and
* `eP`: the global sections of the bounded inverse image `p⁻¹G` with the global sections of
  Mathlib's inverse image `p⁻¹H`,

such that `eP` carries the bounded pullback of a section `s` of `G` over `V`, restricted along
`a : P ⟶ V ×_X P`, to the pullback of `eX s` along `p`, restricted along the corresponding
morphism of Mathlib's site.

The bijection `eP` is the comparison of inverse images along the restriction functors
(`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChange`) followed by the change of
coefficients from abelian groups to sets
(`Stacks.EtaleCohomology.coefficientPullbackTwoSquare`); the compatibility with pullback of
sections is the unit identity of the first as a mate
(`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChange_unit_apply`) and of the second
(`Stacks.Sites.coefficientPullbackTwoSquare_unit`). -/
public theorem exists_sectionPullback_transfer
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    ∃ (H : Sheaf (Scheme.smallEtaleTopology X.obj) (Type (max (u + 1) v)))
      (eX : ∀ U : SmallEtale B X.obj X.property,
        G.obj.obj (op U) ≃ H.obj.obj (op ((toEtaleSite B X.obj X.property).obj U)))
      (eP : ((((smallEtaleBaseChange B p).sheafPullback AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B P.obj P.property)).obj
            G).obj.obj (op (SmallEtale.final B P.obj P.property))) ≃
        ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} (B.inclusion.map p)).obj H).obj.obj
          (op (Scheme.Etale.mk (𝟙 P.obj)))),
      ∀ (V : SmallEtale B X.obj X.property)
        (a : SmallEtale.final B P.obj P.property ⟶ (smallEtaleBaseChange B p).obj V)
        (s : G.obj.obj (op V)),
        eP (pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} G V _ a s) =
          ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} (B.inclusion.map p)).obj H).obj.map
            (Stacks.EtaleCohomology.smallEtaleBaseChangeLift (B.inclusion.map p)
              ((toEtaleSite B X.obj X.property).obj V)
              (B.inclusion.map (a.hom.left ≫ baseChangeObjProjection B p V))
              (baseChangeLift_condition B p V a)).op
            (Stacks.EtaleCohomology.smallEtaleSectionPullback.{u, v} (B.inclusion.map p) H
              ((toEtaleSite B X.obj X.property).obj V) (eX V s)) := by
  let Ab := AddCommGrpCat.{max (u + 1) v}
  let JX := SmallEtale.topology B X.obj X.property
  let JP := SmallEtale.topology B P.obj P.property
  let KX := Scheme.smallEtaleTopology X.obj
  let KP := Scheme.smallEtaleTopology P.obj
  let uU := Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map p)
  let E := sheafEquiv B X.obj X.property Ab
  let GU := E.functor.obj G
  let H := (sheafCompose KX (forget Ab)).obj GU
  let adjB := (smallEtaleBaseChange B p).sheafAdjunctionContinuous Ab JX JP
  let adjU := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uU Ab KX KP
  let β := restrictionPullbackBaseChange B Ab p adjU adjB
  let η : G ≅ ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous Ab JX KX).obj GU :=
    E.unitIso.app G
  let θ := ((smallEtaleBaseChange B p).sheafPullback Ab JX JP).mapIso η ≪≫
    asIso (β.app GU)
  let τ : Scheme.Etale.mk (𝟙 P.obj) ≅ (toEtaleSite B P.obj P.property).obj
      (SmallEtale.final B P.obj P.property) :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simp [toEtaleSite, SmallEtale.final])
  let comp :=
    (Stacks.EtaleCohomology.coefficientPullbackTwoSquare uU KX KP (forget Ab)).app GU
  let eX : ∀ U : SmallEtale B X.obj X.property,
      G.obj.obj (op U) ≃ H.obj.obj (op ((toEtaleSite B X.obj X.property).obj U)) := fun U =>
    ((forget Ab).mapIso (((sheafToPresheaf JX Ab).mapIso η).app (op U))).toEquiv
  let eP := ((forget Ab).mapIso (((sheafToPresheaf JP Ab).mapIso θ).app
      (op (SmallEtale.final B P.obj P.property)) ≪≫
      ((Functor.sheafPullbackConstruction.sheafPullback uU Ab KX KP).obj GU).obj.mapIso τ.op) ≪≫
    (((sheafToPresheaf KP (Type (max (u + 1) v))).mapIso (asIso comp)).app
      (op (Scheme.Etale.mk (𝟙 P.obj)))).symm).toEquiv
  refine ⟨H, eX, eP, fun V a s => ?_⟩
  let LB := (smallEtaleBaseChange B p).sheafPullback Ab JX JP
  let LU := Functor.sheafPullbackConstruction.sheafPullback uU Ab KX KP
  let W := (toEtaleSite B X.obj X.property).obj V
  let x : H.obj.obj (op W) := eX V s
  let unitU := (adjU.unit.app GU).hom.app (op W)
  have hA : ConcreteCategory.hom ((θ.hom).hom.app (op (SmallEtale.final B P.obj P.property)))
      (pullbackSectionAlongHom B p Ab G V _ a s) =
      ConcreteCategory.hom ((LU.obj GU).obj.map ((toEtaleSite B P.obj P.property).map a ≫
        (toEtaleSiteBaseChangeIso B p).hom.app V).op) (ConcreteCategory.hom unitU x) := by
    have hη := sheafHom_app_apply_congr (adjB.unit.naturality η.hom) (op V) s
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply] at hη
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    refine (congrArg _ (NatTrans.naturality_apply (LB.map η.hom).hom a.op _)).trans ?_
    refine (congrArg (fun z => ConcreteCategory.hom ((β.app GU).hom.app
      (op (SmallEtale.final B P.obj P.property))) (ConcreteCategory.hom
        ((LB.obj (((toEtaleSite B X.obj X.property).sheafPushforwardContinuous Ab JX KX).obj
          GU)).obj.map a.op) z)) hη.symm).trans ?_
    exact restrictionPullbackBaseChange_unit_apply B p adjU GU V a x
  let adjT := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uU
    (Type (max (u + 1) v)) KX KP
  let LT := Functor.sheafPullbackConstruction.sheafPullback uU (Type (max (u + 1) v)) KX KP
  let m : Scheme.Etale.mk (𝟙 P.obj) ⟶ uU.obj W :=
    τ.hom ≫ (toEtaleSite B P.obj P.property).map a ≫ (toEtaleSiteBaseChangeIso B p).hom.app V
  let y := (adjT.unit.app H).hom.app (op W) x
  have hcU : comp.hom.app (op (uU.obj W)) y = ConcreteCategory.hom unitU x := by
    have h1 := sheafHom_app_apply_congr
      (coefficientPullbackTwoSquare_unit uU KX KP (forget Ab) GU) (op W) x
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply, sheafCompose_map_hom, Functor.whiskerRight_app] at h1
    exact h1
  have hC : comp.hom.app (op (Scheme.Etale.mk (𝟙 P.obj))) ((LT.obj H).obj.map m.op y) =
      ConcreteCategory.hom ((LU.obj GU).obj.map m.op) (ConcreteCategory.hom unitU x) := by
    have h2 := NatTrans.naturality_apply comp.hom m.op y
    rwa [hcU] at h2
  have hE : ConcreteCategory.hom ((LU.obj GU).obj.map τ.hom.op)
      (ConcreteCategory.hom ((θ.hom).hom.app (op (SmallEtale.final B P.obj P.property)))
        (pullbackSectionAlongHom B p Ab G V _ a s)) =
      ConcreteCategory.hom ((LU.obj GU).obj.map m.op) (ConcreteCategory.hom unitU x) := by
    rw [hA]
    exact (ConcreteCategory.congr_hom ((LU.obj GU).obj.map_comp _ τ.hom.op) _).symm
  let Ic := ((sheafToPresheaf KP (Type (max (u + 1) v))).mapIso (asIso comp)).app
    (op (Scheme.Etale.mk (𝟙 P.obj)))
  have hP : eP (pullbackSectionAlongHom B p Ab G V _ a s) = (LT.obj H).obj.map m.op y := by
    have h1 : eP (pullbackSectionAlongHom B p Ab G V _ a s) =
        Ic.inv (ConcreteCategory.hom ((LU.obj GU).obj.map τ.hom.op)
          (ConcreteCategory.hom ((θ.hom).hom.app (op (SmallEtale.final B P.obj P.property)))
            (pullbackSectionAlongHom B p Ab G V _ a s))) := rfl
    have h2 : Ic.hom ((LT.obj H).obj.map m.op y) =
        ConcreteCategory.hom ((LU.obj GU).obj.map m.op) (ConcreteCategory.hom unitU x) := hC
    rw [h1, hE, ← h2]
    exact Ic.hom_inv_id_apply _
  have hy :
      y = Stacks.EtaleCohomology.smallEtaleSectionPullback.{u, v} (B.inclusion.map p) H W x := by
    have h3 := NatTrans.congr_app (sheafPullbackConstruction_unit_app_hom uU KX KP H) (op W)
    exact ConcreteCategory.congr_hom h3 x
  have hm : m = Stacks.EtaleCohomology.smallEtaleBaseChangeLift (B.inclusion.map p) W
      (B.inclusion.map (a.hom.left ≫ baseChangeObjProjection B p V))
      (baseChangeLift_condition B p V a) :=
    comp_toEtaleSiteBaseChangeIso_hom_eq_smallEtaleBaseChangeLift B p V a τ.hom rfl
  refine hP.trans ?_
  rw [← hy, ← hm]
  rfl

end AlgebraicGeometry.SmallEtale

end
