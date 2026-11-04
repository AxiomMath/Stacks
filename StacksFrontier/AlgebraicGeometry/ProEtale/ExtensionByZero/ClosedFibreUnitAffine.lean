module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSiteLiftOfClosedFibre
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSiteClopenPieces
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.ClosedFibreWContractible
public import StacksFrontier.CategoryTheory.Sites.CoverLifting

/-!
# The unit of the closed-immersion adjunction at a w-contractible affine base

Let `i : Z ⟶ X` be a closed immersion of affine schemes. On the sites `X_app` and `Z_app` of
affine objects with ind-étale ring of global sections, carrying the topologies induced from the
small pro-étale sites, base change `u : X_app ⥤ Z_app` has the fully faithful left adjoint `v`
of [Stacks, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK). The direct image along `u` then
has the explicit left adjoint `G ↦ (G ∘ v)^#`, whose unit at an object `U` of `X_app` is the
restriction of `G` along the counit `v(u(U)) ⟶ U` followed by the unit of sheafification at
`u(U)`.

Restriction to `X_app` and to `Z_app` are equivalences of topoi by
[Stacks, Tag 098X](https://stacks.math.columbia.edu/tag/098X), and they carry the direct image of
abelian pro-étale sheaves along `i` to the direct image along `u`; so the unit
`F ⟶ i_* i^{-1} F` of abelian pro-étale sheaves is invertible on sections over an object of
`X_app` as soon as the unit of the explicit adjunction is.

When `Γ(X, ⊤)` is w-contractible and the ideal of `Z` lies in its Jacobson radical — every point
of `X` specializes into `Z` — both factors of that unit are invertible at the final object `X`:
the counit `v(u(X)) ⟶ X` by the ring-theoretic retraction behind
[Stacks, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC), and the unit of sheafification at
`u(X) = Z` because `Z` is weakly contractible, every covering of it is refined by the base change
of a clopen decomposition of `X`, and a sheaf sends a clopen decomposition to a product. Hence
`F(X) = (i^{-1} F)(Z)` through the unit, for every abelian sheaf `F` on `X_proétale`.

## Main definitions

* `AlgebraicGeometry.ProEtale.appSheafPullback` and
  `AlgebraicGeometry.ProEtale.appSheafAdjunction`: the left adjoint `G ↦ (G ∘ v)^#` of the direct
  image along `u`, and the adjunction.
* `AlgebraicGeometry.ProEtale.AppSmallProetale.top`: the final object `S` of `S_app`.

## Main results

* `AlgebraicGeometry.ProEtale.appSheafAdjunction_unit_app_hom_app`: the formula for its unit.
* `AlgebraicGeometry.ProEtale.isIso_proetaleUnit_app_of_isIso_appSheafAdjunction_unit`: the unit
  of `i^{-1} ⊣ i_*` at an object of `X_app` is invertible when the unit of `appSheafAdjunction`
  is invertible there.
* `AlgebraicGeometry.ProEtale.isIso_counit_app_of_isOpenImmersion_of_isClosed`: the counit of
  `v ⊣ u` is invertible at every clopen piece of a w-contractible `X` whose closed fibre contains
  the closed points.
* `AlgebraicGeometry.ProEtale.isIso_toSheafify_app_appProetaleBaseChange_top`: the sheafification
  of `V ↦ G(v(V))` does not change its sections over `u(X)`.
* `AlgebraicGeometry.ProEtale.isIso_proetaleUnit_app_top`: the unit `F ⟶ i_* i^{-1} F` is
  invertible on global sections.

## References

* [Stacks Project, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.ProEtale

/-- The site `S_app` is essentially small relative to any universe containing its objects. -/
instance AppSmallProetale.essentiallySmall (S : Scheme.{u}) :
    EssentiallySmall.{max (u + 1) v} (AppSmallProetale S) :=
  essentiallySmall_of_small_of_locallySmall _

/-- Abelian presheaves on `S_app` admit sheafification for the induced topology. -/
instance AppSmallProetale.hasSheafify_addCommGrp (S : Scheme.{u}) :
    HasSheafify (AppSmallProetale.inducedTopology S) AddCommGrpCat.{max (u + 1) v} :=
  hasSheafifyEssentiallySmallSite _ _

/-- Sheafification of abelian presheaves on `S_app` inverts exactly the locally bijective
morphisms. -/
instance AppSmallProetale.wEqualsLocallyBijective_addCommGrp (S : Scheme.{u}) :
    (AppSmallProetale.inducedTopology S).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

section Adjunction

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsAffine X] [IsAffine Z]
variable (A : Type*) [Category A] [HasWeakSheafify (AppSmallProetale.inducedTopology Z) A]

/-- The inverse image along the closed immersion `i` on the sites `S_app`: a sheaf `G` on
`X_app` goes to the sheafification of `V ↦ G(v(V))`, where `v` is the left adjoint of base
change of Stacks 09BK. -/
abbrev appSheafPullback :
    Sheaf (AppSmallProetale.inducedTopology X) A ⥤ Sheaf (AppSmallProetale.inducedTopology Z) A :=
  sheafToPresheaf (AppSmallProetale.inducedTopology X) A ⋙
    (Functor.whiskeringLeft _ _ _).obj (appProetaleLift i).op ⋙
    presheafToSheaf (AppSmallProetale.inducedTopology Z) A

/-- The inverse image `appSheafPullback` is left adjoint to the direct image along base change:
restriction along `v` is left adjoint to restriction along `u` on presheaves, because `v ⊣ u`,
and sheafification is left adjoint to the inclusion of sheaves. -/
def appSheafAdjunction :
    appSheafPullback i A ⊣
      (appProetaleBaseChange i).sheafPushforwardContinuous A
        (AppSmallProetale.inducedTopology X) (AppSmallProetale.inducedTopology Z) :=
  Adjunction.restrictFullyFaithful
    ((Functor.whiskeringLeftAdjunctionOfAdjunction A
      (appProetaleLiftAdjunction i)).comp (sheafificationAdjunction _ _))
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    ((Functor.leftUnitor _).trans
      ((appProetaleBaseChange i).sheafPushforwardContinuousCompSheafToPresheafIso _ _ _).symm)

/-- The unit of `appSheafAdjunction` at a sheaf `G` and an object `U` of `X_app` is the
restriction of `G` along the counit `v(u(U)) ⟶ U`, followed by the unit of sheafification of
`G ∘ v` at `u(U)`. -/
theorem appSheafAdjunction_unit_app_hom_app (G : Sheaf (AppSmallProetale.inducedTopology X) A)
    (U : AppSmallProetale X) :
    ((appSheafAdjunction i A).unit.app G).hom.app (op U) =
      G.obj.map ((appProetaleLiftAdjunction i).counit.app U).op ≫
        (toSheafify (AppSmallProetale.inducedTopology Z) ((appProetaleLift i).op ⋙ G.obj)).app
          (op ((appProetaleBaseChange i).obj U)) := by
  simp only [appSheafAdjunction, Adjunction.restrictFullyFaithful,
    Functor.whiskeringLeftAdjunctionOfAdjunction]
  simp only [Functor.id_obj, Functor.comp_obj, ObjectProperty.ι_obj, Functor.whiskeringLeft_obj_obj,
    Functor.FullyFaithful.homEquiv, Iso.symm_symm_eq, Equiv.trans_def, NatIso.trans_app,
    Equiv.symm_mk, Adjunction.mkOfHomEquiv_unit_app, Equiv.trans_apply, Equiv.coe_fn_mk,
    Functor.id_map, Iso.homCongr_apply, Iso.app_inv, Functor.rightUnitor_inv_app, Iso.refl_hom,
    Category.comp_id, Iso.refl_inv, Iso.trans_hom, Iso.app_hom, Functor.leftUnitor_hom_app,
    Iso.symm_hom, Category.id_comp, ObjectProperty.homMk_hom, NatTrans.comp_app, Functor.op_obj,
    Functor.sheafPushforwardContinuousCompSheafToPresheafIso_inv_app_app]
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  simp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, ObjectProperty.ι_obj,
    sheafificationAdjunction_unit_app, Functor.whiskeringLeft_obj_map, Functor.comp_map,
    ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom, Functor.whiskerLeft_id',
    Category.comp_id, NatTrans.comp_app, Functor.op_obj, Adjunction.whiskerLeft_unit_app_app,
    Adjunction.op_unit, NatTrans.op_app, Functor.id_obj, Functor.whiskerLeft_app]
  exact Category.comp_id _

end Adjunction

section Transport

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsAffine X] [IsAffine Z]

/-- Restriction to `S_app` carries the direct image of abelian pro-étale sheaves along `i` to
the direct image along base change `u` on the sites `S_app`. -/
def appRestrictionDirectImageIso :
    (AppSmallProetale.inclusion Z).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (AppSmallProetale.inducedTopology Z) (Scheme.ProEt.topology Z) ⋙
      (appProetaleBaseChange i).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (AppSmallProetale.inducedTopology X) (AppSmallProetale.inducedTopology Z) ≅
    Abelian.proetaleDirectImage.{u, v} i ⋙
      (AppSmallProetale.inclusion X).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (AppSmallProetale.inducedTopology X) (Scheme.ProEt.topology X) := by
  have hc : (AppSmallProetale.inclusion X ⋙ Scheme.proetaleBaseChange i).IsContinuous
      (AppSmallProetale.inducedTopology X) (Scheme.ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology X) _
  exact Functor.sheafPushforwardContinuousComp'
      (eFG := eqToIso (appProetaleBaseChange_comp_inclusion i))
      (A := AddCommGrpCat.{max (u + 1) v}) (J := AppSmallProetale.inducedTopology X)
      (K := AppSmallProetale.inducedTopology Z) (L := Scheme.ProEt.topology Z) ≪≫
    (Functor.sheafPushforwardContinuousComp' (eFG := Iso.refl _)
      (A := AddCommGrpCat.{max (u + 1) v}) (J := AppSmallProetale.inducedTopology X)
      (K := Scheme.ProEt.topology X) (L := Scheme.ProEt.topology Z)).symm

/-- **Transport of the unit to the sites `S_app`.** The unit `F ⟶ i_* i^{-1} F` of the abelian
pro-étale adjunction is invertible on sections over an object `U` of `X_app` as soon as the
unit of `appSheafAdjunction` at the restriction of `F` to `X_app` is invertible there.

Both composites `i^{-1}` followed by restriction to `Z_app`, and restriction to `X_app` followed
by `appSheafPullback`, are left adjoint to the same functor up to the isomorphism
`appRestrictionDirectImageIso`, and the two restrictions are equivalences (Stacks 098X); the
isomorphism between the two left adjoints that this produces intertwines the units. -/
theorem isIso_proetaleUnit_app_of_isIso_appSheafAdjunction_unit
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) (U : AppSmallProetale X)
    (h : IsIso (((appSheafAdjunction i AddCommGrpCat.{max (u + 1) v}).unit.app
      (((AppSmallProetale.inclusion X).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (AppSmallProetale.inducedTopology X) (Scheme.ProEt.topology X)).obj F)).hom.app
          (op U))) :
    IsIso (((Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).unit.app F).hom.app
      (op ((AppSmallProetale.inclusion X).obj U))) := by
  let A := AddCommGrpCat.{max (u + 1) v}
  let RX := (AppSmallProetale.inclusion X).sheafPushforwardContinuous A
    (AppSmallProetale.inducedTopology X) (Scheme.ProEt.topology X)
  let RZ := (AppSmallProetale.inclusion Z).sheafPushforwardContinuous A
    (AppSmallProetale.inducedTopology Z) (Scheme.ProEt.topology Z)
  let Su := (appProetaleBaseChange i).sheafPushforwardContinuous A
    (AppSmallProetale.inducedTopology X) (AppSmallProetale.inducedTopology Z)
  let D := Abelian.proetaleDirectImage.{u, v} i
  let eX := RX.asEquivalence
  let eZ := RZ.asEquivalence
  let adj1 := Abelian.proetaleInverseImageDirectImageAdj.{u, v} i
  let adjA := appSheafAdjunction i A
  let B1 := adj1.comp eZ.toAdjunction
  let B2 := eX.toAdjunction.comp adjA
  let key : RZ ⋙ Su ≅ D ⋙ RX := appRestrictionDirectImageIso.{u, v} i
  let ρ : Su ⋙ eX.inverse ≅ eZ.inverse ⋙ D :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight eZ.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft eZ.inverse ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight key eX.inverse ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft D eX.unitIso.symm ≪≫ Functor.rightUnitor D)
  let c := Adjunction.leftAdjointUniq B1 (B2.ofNatIsoRight ρ)
  have hu := Adjunction.unit_leftAdjointUniq_hom_app B1 (B2.ofNatIsoRight ρ) F
  let E := RX ⋙ (sheafSections (AppSmallProetale.inducedTopology X) A).obj (op U)
  have hE := congrArg E.map hu
  simp only [B1, B2, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.comp_unit_app, Functor.map_comp, Category.assoc, Equivalence.toAdjunction_unit]
    at hE
  have hd : IsIso (E.map (eX.inverse.map (adjA.unit.app (eX.functor.obj F)))) := by
    show IsIso (((sheafSections (AppSmallProetale.inducedTopology X) A).obj (op U)).map
      (eX.functor.map (eX.inverse.map (adjA.unit.app (eX.functor.obj F)))))
    rw [Equivalence.fun_inv_map, Functor.map_comp, Functor.map_comp]
    have : IsIso (((sheafSections (AppSmallProetale.inducedTopology X) A).obj (op U)).map
        (adjA.unit.app (eX.functor.obj F))) := h
    infer_instance
  have hrhs : IsIso (E.map (eX.unit.app F) ≫
      E.map (eX.inverse.map (adjA.unit.app (eX.functor.obj F))) ≫
        E.map (ρ.hom.app ((eX.functor ⋙ appSheafPullback i A).obj F))) := by
    infer_instance
  rw [← hE] at hrhs
  have h2 : IsIso (E.map ((Abelian.proetaleDirectImage i).map
      (eZ.unit.app ((Abelian.proetaleInverseImage i).obj F))) ≫
        E.map ((eZ.inverse ⋙ Abelian.proetaleDirectImage i).map (c.hom.app F))) :=
    inferInstance
  exact IsIso.of_isIso_comp_right (E.map (adj1.unit.app F))
    (E.map ((Abelian.proetaleDirectImage i).map
      (eZ.unit.app ((Abelian.proetaleInverseImage i).obj F))) ≫
        E.map ((eZ.inverse ⋙ Abelian.proetaleDirectImage i).map (c.hom.app F)))

end Transport

section Top

/-- An affine object of the small pro-étale site of an affine scheme whose structure morphism
is étale is an object of `S_app`. -/
theorem isAppSmall_of_etale {S : Scheme.{u}} [IsAffine S] (V : S.ProEt) [IsAffine V.left]
    [Etale V.hom] : IsAppSmall S V := by
  refine ⟨‹IsAffine V.left›, ?_⟩
  have : IsAffine ((𝟭 Scheme).obj V.left) := ‹IsAffine V.left›
  have : IsAffine ((Functor.fromPUnit S).obj V.right) := ‹IsAffine S›
  let : Algebra Γ(S, ⊤) Γ(V.left, ⊤) := V.hom.appTop.hom.toAlgebra
  exact indEtale_of_etale
    (HasRingHomProperty.appTop (P := @Etale) V.hom inferInstance).toAlgebra

/-- The final object of `S_app`: the scheme `S` itself. -/
def AppSmallProetale.top (S : Scheme.{u}) [IsAffine S] : AppSmallProetale S :=
  haveI : IsAffine (Scheme.ProEt.mk (𝟙 S)).left := ‹IsAffine S›
  haveI : Etale (Scheme.ProEt.mk (𝟙 S)).hom := inferInstanceAs (Etale (𝟙 S))
  ⟨Scheme.ProEt.mk (𝟙 S), isAppSmall_of_etale (Scheme.ProEt.mk (𝟙 S))⟩

/-- `S` is a final object of `S_app`. -/
def AppSmallProetale.isTerminalTop (S : Scheme.{u}) [IsAffine S] :
    IsTerminal (AppSmallProetale.top S) :=
  IsTerminal.ofUniqueHom
    (fun U ↦ ObjectProperty.homMk (MorphismProperty.Over.homMk U.obj.hom (Category.comp_id _)))
    (fun U f ↦ ObjectProperty.hom_ext _ (MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).symm.trans (MorphismProperty.Over.w f.hom))))

end Top

section Sheafification

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsAffine X] [IsAffine Z]

/-- A clopen piece `U` of `X` is an object of `X_app` at which the counit of `v ⊣ u` is
invertible, provided `Γ(X, ⊤)` is w-contractible and the ideal of `Z` lies in its Jacobson
radical: `Γ(U, ⊤)` is a quotient of `Γ(X, ⊤)` by a finitely generated ideal, hence
w-contractible, and the image of the Jacobson radical lies in the Jacobson radical. -/
theorem isIso_counit_app_of_isOpenImmersion_of_isClosed
    (hA : ProetaleWContractible.IsWContractible.{u, u} Γ(X, ⊤))
    (hI : appTopKer i ≤ Ring.jacobson Γ(X, ⊤))
    (U : AppSmallProetale X) [IsOpenImmersion U.obj.hom]
    (hU : IsClosed (Set.range U.obj.hom.base)) :
    IsIso ((appProetaleLiftAdjunction i).counit.app U) := by
  have _ : IsClosedImmersion U.obj.hom := IsClosedImmersion.of_isPreimmersion _ hU
  have _ : IsAffine U.obj.left := U.property.1
  have _ : IsAffine ((Functor.fromPUnit X).obj U.obj.right) := ‹IsAffine X›
  have hsurj : Function.Surjective U.obj.hom.appTop.hom := surjective_appTop_hom U.obj.hom
  have hfp : U.obj.hom.appTop.hom.FinitePresentation :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) U.obj.hom inferInstance
  let : Algebra Γ(X, ⊤) Γ(U.obj.left, ⊤) := U.obj.hom.appTop.hom.toAlgebra
  have : Algebra.FinitePresentation Γ(X, ⊤) Γ(U.obj.left, ⊤) := hfp
  have hker : (RingHom.ker U.obj.hom.appTop.hom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId Γ(X, ⊤) Γ(U.obj.left, ⊤))
      hsurj
  refine isIso_counit_app_of_isWContractible i U
    (isWContractible_of_surjective_of_fg_ker _ hsurj hker hA) ?_
  refine (Ideal.map_mono hI).trans (Ideal.map_le_iff_le_comap.mpr ?_)
  have : RingHomSurjective U.obj.hom.appTop.hom := ⟨hsurj⟩
  exact Ring.le_comap_jacobson (f := U.obj.hom.appTop.hom)

/-- The counit of `v ⊣ u` is invertible at the final object of `X_app`, under the hypotheses of
`isIso_counit_app_of_isOpenImmersion_of_isClosed`. -/
private theorem isIso_counit_app_top
    (hA : ProetaleWContractible.IsWContractible.{u, u} Γ(X, ⊤))
    (hI : appTopKer i ≤ Ring.jacobson Γ(X, ⊤)) :
    IsIso ((appProetaleLiftAdjunction i).counit.app (AppSmallProetale.top X)) := by
  have _ : IsOpenImmersion (AppSmallProetale.top X).obj.hom :=
    inferInstanceAs (IsOpenImmersion (𝟙 X))
  refine isIso_counit_app_of_isOpenImmersion_of_isClosed i hA hI _ ?_
  have : Set.range (AppSmallProetale.top X).obj.hom.base = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ ⟨x, rfl⟩
  rw [this]
  exact isClosed_univ

/-- **Sheafification is invisible at the closed fibre of `X`.** Let `Γ(X, ⊤)` be w-contractible
and let the ideal of `Z` lie in its Jacobson radical. For an abelian sheaf `G` on `X_app`, the
unit of sheafification of `V ↦ G(v(V))` is invertible on sections over `u(X)`, the closed fibre
`X ×_X Z` viewed as an object of `Z_app`.

This is the sheafification step of Stacks 09BL (2) at the final object. A covering sieve of
`u(X)` contains a finite family `Y_k ⟶ u(X)` covering it, by Stacks 098H, since `u(X)` is
affine with w-contractible ring of global sections. The lifts `v(Y_k)` cover `X`: every point of
`X` specializes into `Z`, the image of `v(Y_k)` contains the image of `Y_k`, and images of flat
morphisms are stable under generalization. Again by Stacks 098H this covering is refined by a
clopen decomposition `X = ∐ X_m`, whose base change to `Z` lies in the sieve. The counit
`v(u(X_m)) ⟶ X_m` is invertible, so the sections of `V ↦ G(v(V))` over `u(X)` and over the
`u(X_m)` are those of `G` over `X` and over the `X_m`, and `G` sends the clopen decomposition to
a product. The split-refinement criterion then applies. -/
theorem isIso_toSheafify_app_appProetaleBaseChange_top
    (hA : ProetaleWContractible.IsWContractible.{u, u} Γ(X, ⊤))
    (hI : appTopKer i ≤ Ring.jacobson Γ(X, ⊤))
    (G : Sheaf (AppSmallProetale.inducedTopology X) AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((toSheafify (AppSmallProetale.inducedTopology Z)
      ((appProetaleLift i).op ⋙ G.obj)).app
        (op ((appProetaleBaseChange i).obj (AppSmallProetale.top X)))) := by
  classical
  let JX := AppSmallProetale.inducedTopology X
  let JZ := AppSmallProetale.inducedTopology Z
  let ιX := AppSmallProetale.inclusion X
  let ιZ := AppSmallProetale.inclusion Z
  let uf := appProetaleBaseChange i
  let vf := appProetaleLift i
  let adj := appProetaleLiftAdjunction i
  let top := AppSmallProetale.top X
  let T := uf.obj top
  let P := vf.op ⋙ G.obj
  have _ := adj.rightAdjoint_preservesLimits
  have hT : IsTerminal T := (AppSmallProetale.isTerminalTop X).isTerminalObj uf
  have _ : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  rw [ConcreteCategory.isIso_iff_bijective]
  have hQ : Presheaf.IsSheaf JZ (sheafify JZ P ⋙ forget AddCommGrpCat.{max (u + 1) v}) :=
    ((sheafCompose JZ (forget AddCommGrpCat.{max (u + 1) v})).obj
      ((presheafToSheaf JZ _).obj P)).property
  refine GrothendieckTopology.bijective_app_of_isLocallyBijective_of_splitRefinements JZ
    (toSheafify JZ P) hQ T (fun S hS ↦ ?_)
  have hspecX : ∀ x : X, ∃ z : Z, x ⤳ i.base z :=
    exists_specializes_of_ker_appTop_le_ringJacobson i hI
  -- the closed fibre `u(X)` is affine and weakly contractible
  have _ : IsAffine (ιZ.obj T).left := T.property.1
  have hpt (z : Z) : ∃ t : (ιZ.obj T).left,
      (pullback.fst (𝟙 X) i).base t = i.base z ∧ (ιZ.obj T).hom.base t = z := by
    have hcond : i ≫ 𝟙 X = 𝟙 Z ≫ i := (Category.comp_id _).trans (Category.id_comp _).symm
    exact ⟨(pullback.lift i (𝟙 Z) hcond).base z,
      congrArg (fun f : Z ⟶ X ↦ f.base z) (pullback.lift_fst i (𝟙 Z) hcond),
      congrArg (fun f : Z ⟶ Z ↦ f.base z) (pullback.lift_snd i (𝟙 Z) hcond)⟩
  have hTwc : ProetaleWContractible.IsWContractible.{u, u} Γ((ιZ.obj T).left, ⊤) := by
    have hj : IsClosedImmersion (pullback.fst (𝟙 X) i) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback (𝟙 X) i).flip ‹_›
    have hpa : IsAffine (pullback (𝟙 X) i) := ‹IsAffine (ιZ.obj T).left›
    refine @isWContractible_appTop_of_specializes _ _ (pullback.fst (𝟙 X) i) _ hpa hj hA
      (fun x ↦ ?_)
    obtain ⟨z, hz⟩ := hspecX x
    obtain ⟨t, ht, -⟩ := hpt z
    exact ⟨t, ht ▸ hz⟩
  have hTw : (Scheme.ProEt.topology Z).IsWeaklyContractible (ιZ.obj T) :=
    isWeaklyContractible_of_isWContractible _ hTwc
  have hS' : S.functorPushforward ιZ ∈ Scheme.ProEt.topology Z (ιZ.obj T) :=
    (ιZ.functorPushforward_mem_iff JZ (Scheme.ProEt.topology Z)).mpr hS
  obtain ⟨nZ, UZ, fZ, hdecZ, hfZ, hmemZ⟩ :=
    Scheme.ProEt.exists_clopenDecomposition_of_isWeaklyContractible _ hTw _ hS'
  choose Y b c hb hfac using fun k ↦ (hmemZ k)
  -- the lifts `v(Y_k)` cover `X`
  let V : Fin nZ → X.ProEt := fun k ↦ ιX.obj (vf.obj (Y k))
  let a : (k : Fin nZ) → V k ⟶ ιX.obj top :=
    fun k ↦ ιX.map ((AppSmallProetale.isTerminalTop X).from _)
  have ha (k : Fin nZ) : (a k).hom.left = (V k).hom :=
    (Category.comp_id _).symm.trans (MorphismProperty.Over.w (a k))
  have hcovX : Sieve.ofArrows V a ∈ Scheme.ProEt.topology X (ιX.obj top) := by
    refine sieve_ofArrows_mem_proetaleTopology V a (fun k ↦ ?_) (fun k ↦ ?_) (fun x ↦ ?_)
    · rw [ha]
      exact (V k).prop
    · rw [ha]
      have : IsAffine (V k).left := (vf.obj (Y k)).property.1
      have : CompactSpace ((𝟭 Scheme).obj (V k).left) :=
        inferInstanceAs (CompactSpace (V k).left)
      have : QuasiSeparatedSpace (ιX.obj top).left := inferInstanceAs (QuasiSeparatedSpace X)
      exact quasiCompact_of_compactSpace _
    · obtain ⟨z, hz⟩ := hspecX x
      obtain ⟨t, -, htz⟩ := hpt z
      have ht : t ∈ ⋃ k, Set.range (fZ k).base := by
        rw [hdecZ.cover]
        trivial
      obtain ⟨k, w0, hw0⟩ := Set.mem_iUnion.mp ht
      have hf : fZ k = (c k).left ≫ (b k).hom.left :=
        congrArg (fun q ↦ q.left) (hfac k)
      let y0 := (c k).left.base w0
      have e1 : (Y k).obj.hom = (b k).hom.left ≫ (ιZ.obj T).hom :=
        (MorphismProperty.Over.w (b k).hom).symm
      have hz0 : (Y k).obj.hom.base y0 = z := by
        calc (Y k).obj.hom.base y0 = (ιZ.obj T).hom.base ((b k).hom.left.base y0) := by
              rw [e1]
              rfl
          _ = (ιZ.obj T).hom.base ((fZ k).base w0) := by
              rw [hf]
              rfl
          _ = z := by rw [hw0, htz]
      let η := adj.unit.app (Y k)
      let W := vf.obj (Y k)
      let p0 := (pullback.fst W.obj.hom i).base (η.hom.left.base y0)
      have e2 : (Y k).obj.hom = η.hom.left ≫ pullback.snd W.obj.hom i :=
        (MorphismProperty.Over.w η.hom).symm
      have hp0 : W.obj.hom.base p0 = i.base z := by
        calc W.obj.hom.base p0 = (pullback.fst W.obj.hom i ≫ W.obj.hom).base
              (η.hom.left.base y0) := rfl
          _ = (pullback.snd W.obj.hom i ≫ i).base (η.hom.left.base y0) := by
              rw [pullback.condition]
          _ = i.base ((η.hom.left ≫ pullback.snd W.obj.hom i).base y0) := rfl
          _ = i.base z := by rw [← e2, hz0]
      obtain ⟨y, -, hy⟩ := Flat.generalizingMap W.obj.hom (hp0 ▸ hz)
      refine ⟨k, y, ?_⟩
      rw [ha]
      exact hy
  -- a clopen decomposition of `X` refining that covering
  have _ : IsAffine (ιX.obj top).left := ‹IsAffine X›
  have hTopW : (Scheme.ProEt.topology X).IsWeaklyContractible (ιX.obj top) :=
    isWeaklyContractible_of_isWContractible _ hA
  obtain ⟨n, U, g, hdec, hg, hmemX⟩ :=
    Scheme.ProEt.exists_clopenDecomposition_of_isWeaklyContractible _ hTopW _ hcovX
  have hpiece (m : Fin n) : IsAppSmall X ((ιX.obj top).clopenDecompositionObj g hg m) := by
    have _ := hdec.openImmersion m
    have _ := hg m
    exact isAppSmall_of_isOpenImmersion_of_isClosed top.property (g m) (hdec.clopen m).isClosed
  let piece : Fin n → AppSmallProetale X := fun m ↦ ⟨_, hpiece m⟩
  let tm : (m : Fin n) → piece m ⟶ top := fun m ↦ (AppSmallProetale.isTerminalTop X).from _
  have htm (m : Fin n) : ιX.map (tm m) = (ιX.obj top).clopenDecompositionHom g hg m := by
    refine (Scheme.ProEt.forgetFullyFaithful X).map_injective ?_
    ext
    have h := MorphismProperty.Over.w (ιX.map (tm m))
    exact (Category.comp_id _).symm.trans (h.trans (Category.comp_id _))
  have hdecP : ProetaleWContractible.IsClopenDecompositionCover (fun m ↦ (piece m).obj.left)
      (fun m ↦ (tm m).hom.left) := by
    have : (fun m ↦ (tm m).hom.left) = g := funext fun m ↦ congrArg (fun q ↦ q.left) (htm m)
    rw [this]
    exact hdec
  -- the counit is invertible at `X` and at the pieces
  have hεtop : IsIso (adj.counit.app top) := isIso_counit_app_top i hA hI
  have hεpiece (m : Fin n) : IsIso (adj.counit.app (piece m)) := by
    have e : (piece m).obj.hom = g m := Category.comp_id _
    have _ : IsOpenImmersion (piece m).obj.hom := e ▸ hdec.openImmersion m
    refine isIso_counit_app_of_isOpenImmersion_of_isClosed i hA hI (piece m) ?_
    rw [e]
    exact (hdec.clopen m).isClosed
  -- the split family
  have hcovJX : Sieve.ofArrows piece tm ∈ JX top := by
    refine (ιX.functorPushforward_mem_iff JX (Scheme.ProEt.topology X)).mp ?_
    refine (Scheme.ProEt.topology X).superset_covering ?_
      (Scheme.ProEt.sieve_ofArrows_clopenDecomposition_mem_topology _ g hdec hg)
    rintro T' f hf
    obtain ⟨m, a', rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hf
    exact ⟨piece m, tm m, a', Sieve.ofArrows_mk _ _ m, by rw [htm]⟩
  have hcovJZ : Sieve.ofArrows (fun m ↦ uf.obj (piece m)) (fun m ↦ uf.map (tm m)) ∈ JZ T := by
    refine JZ.superset_covering ?_
      ((CoverPreserving.of_isContinuous uf JX JZ).cover_preserve hcovJX)
    rintro T' f ⟨Y', g', h', hg', rfl⟩
    obtain ⟨m, a', rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg'
    rw [Functor.map_comp, ← Category.assoc]
    exact (Sieve.ofArrows _ _).downward_closed (Sieve.ofArrows_mk _ _ m) _
  have hmem (m : Fin n) : S.arrows (uf.map (tm m)) := by
    obtain ⟨k, c', hc'⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp (hmemX m)
    let d : piece m ⟶ vf.obj (Y k) := ιX.preimage c'
    have : uf.map (tm m) = (uf.map d ≫ inv (adj.unit.app (Y k))) ≫ b k := hT.hom_ext _ _
    rw [this]
    exact S.downward_closed (hb k) _
  refine ⟨n, fun m ↦ uf.obj (piece m), fun m ↦ uf.map (tm m), hcovJZ, hmem, ?_⟩
  -- the product condition
  have hGsh : Presheaf.IsSheaf JX (G.obj ⋙ forget AddCommGrpCat.{max (u + 1) v}) :=
    ((sheafCompose JX (forget AddCommGrpCat.{max (u + 1) v})).obj G).property
  have hΦ := AppSmallProetale.bijective_sections_of_isClopenDecompositionCover
    (G.obj ⋙ forget AddCommGrpCat.{max (u + 1) v}) hGsh tm hdecP
  have key (y : ToType (G.obj.obj (op top))) (m : Fin n) :
      P.map (uf.map (tm m)).op (G.obj.map (adj.counit.app top).op y) =
        G.obj.map (adj.counit.app (piece m)).op (G.obj.map (tm m).op y) := by
    have hnat := adj.counit.naturality (tm m)
    show (G.obj.map (adj.counit.app top).op ≫ G.obj.map (vf.map (uf.map (tm m))).op) y =
      (G.obj.map (tm m).op ≫ G.obj.map (adj.counit.app (piece m)).op) y
    rw [← G.obj.map_comp, ← G.obj.map_comp, ← op_comp, ← op_comp]
    exact congrArg (fun q ↦ G.obj.map q.op y) hnat
  have hα : Function.Bijective (G.obj.map (adj.counit.app top).op) :=
    ConcreteCategory.bijective_of_isIso _
  have hβ : Function.Bijective (fun (x : (m : Fin n) → ToType (G.obj.obj (op (piece m))))
      (m : Fin n) ↦ G.obj.map (adj.counit.app (piece m)).op (x m)) :=
    Function.Bijective.piMap (fun m ↦ ConcreteCategory.bijective_of_isIso _)
  have hcomp : (fun x m ↦ P.map (uf.map (tm m)).op x) ∘ (G.obj.map (adj.counit.app top).op) =
      (fun (x : (m : Fin n) → ToType (G.obj.obj (op (piece m)))) m ↦
        G.obj.map (adj.counit.app (piece m)).op (x m)) ∘
        (fun y m ↦ G.obj.map (tm m).op y) :=
    funext fun y ↦ funext fun m ↦ key y m
  refine (Function.Bijective.of_comp_iff _ hα).mp ?_
  rw [hcomp]
  exact hβ.comp hΦ

/-- **The unit at a w-contractible affine base.** Let `i : Z ⟶ X` be a closed immersion of affine
schemes such that `Γ(X, ⊤)` is w-contractible and the ideal of `Z` lies in the Jacobson radical
of `Γ(X, ⊤)`, i.e. every point of `X` specializes into `Z`. Then for every abelian sheaf `F` on
`X_proétale` the unit `F ⟶ i_* i^{-1} F` is invertible on global sections:
`F(X) = (i^{-1} F)(Z)`.

This is Stacks 09AC at the final object: the unit of the adjunction on `X_app` is the
restriction along the counit `v(u(X)) ⟶ X`, which is invertible (Stacks 09BK, via the
ring-theoretic retraction), followed by the unit of sheafification at `u(X)`, which is
invertible by `isIso_toSheafify_app_appProetaleBaseChange_top`; and the unit transports to the
small pro-étale sites by `isIso_proetaleUnit_app_of_isIso_appSheafAdjunction_unit`. -/
theorem isIso_proetaleUnit_app_top
    (hA : ProetaleWContractible.IsWContractible.{u, u} Γ(X, ⊤))
    (hI : appTopKer i ≤ Ring.jacobson Γ(X, ⊤))
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    IsIso (((Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).unit.app F).hom.app
      (op ((AppSmallProetale.inclusion X).obj (AppSmallProetale.top X)))) := by
  refine isIso_proetaleUnit_app_of_isIso_appSheafAdjunction_unit i F _ ?_
  rw [appSheafAdjunction_unit_app_hom_app]
  have := isIso_counit_app_top i hA hI
  have hs := isIso_toSheafify_app_appProetaleBaseChange_top.{u, v} i hA hI
    (((AppSmallProetale.inclusion X).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (AppSmallProetale.inducedTopology X) (Scheme.ProEt.topology X)).obj F)
  have hm : IsIso ((((AppSmallProetale.inclusion X).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (AppSmallProetale.inducedTopology X)
      (Scheme.ProEt.topology X)).obj F).obj.map
        ((appProetaleLiftAdjunction i).counit.app (AppSmallProetale.top X)).op) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso' hm hs

end Sheafification

end AlgebraicGeometry.ProEtale

end
