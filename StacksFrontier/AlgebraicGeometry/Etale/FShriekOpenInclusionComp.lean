module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekComposition
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance
public import StacksFrontier.AlgebraicGeometry.Etale.SupportTransport
public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSectionsClopen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.CategoryTheory.Bicategory.OverPullbackPseudofunctor

/-!
# Transitivity of extension by zero along nested open subschemes

Let `f : X ⟶ Y` be a separated morphism locally of finite type in a big étale site and let
`i : X'' ⟶ X'` and `j : X' ⟶ X` be open immersions in that site. An abelian sheaf `F` on the
small étale site of `X` can be restricted to `X''` in two ways: in one step along `i ≫ j`, or
in two steps along `j` and then along `i`. The two restrictions are canonically isomorphic,
and the induced comparison of proper-support direct images identifies the extension-by-zero
map of `i ≫ j` with the composite of the extension-by-zero maps of `i` and of `j`.

## Main results

* `AlgebraicGeometry.SmallEtale.openInclusionShriekCompComparison`: the comparison of the two
  proper-support direct images, bundled with the equation that pins it down inside the ordinary
  direct image.
* `AlgebraicGeometry.SmallEtale.openInclusionShriekCompIso`: that comparison as an isomorphism.
* `AlgebraicGeometry.SmallEtale.openInclusionShriekCompIso_ambient`: the comparison is the
  restriction comparison read inside the ordinary direct images.
* `AlgebraicGeometry.SmallEtale.openInclusionShriekMap_comp`: transitivity of extension by
  zero.

## Implementation notes

The comparison is not constructed by hand. Both proper-support direct images sit as subsheaves
of ordinary direct images along `X'' ⟶ Y`, and the two ordinary direct images are identified by
the comparison of restrictions together with the associativity of `i ≫ j ≫ f`. Under that
identification the two subsheaves have the same sections, because the proper-support condition
only refers to the support of a section and to the projection to the test object, and neither
changes. Comparing subobjects with equal sections produces the isomorphism, and the equation
characterising it inside the ordinary direct image comes for free.

Transitivity itself is a statement about sections. Both sides of the equation are sections of
`f_! F` over a test object, and the composite open immersion `i ≫ j` is an open immersion onto
which both sides have their support, so it suffices to compare their restrictions there. That
restriction is the unit of the restriction adjunction up to the canonical identification of the
two descriptions of restriction, and on units the comparison is the coherence of the inverse
images with composition.

## References

* [Stacks Project, Tag 0F53](https://stacks.math.columbia.edu/tag/0F53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

attribute [local implicit_reducible] smallEtaleBaseChange

section Support

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

end Support

section ProperSupport

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}

/-- Applying the inverse of an isomorphism of abelian sheaves undoes applying it, sectionwise. -/
private theorem sheafIso_inv_hom_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A A' : Sheaf J AddCommGrpCat.{v}} (e : A ≅ A') (U : Cᵒᵖ) (z : A'.obj.obj U) :
    e.hom.hom.app U (e.inv.hom.app U z) = z :=
  congrArg (fun k => k z) (congrArg (fun k : A' ⟶ A' => k.hom.app U) e.inv_hom_id)

/-- The proper-support condition of Tag 0F4X as a condition on a closed subset of the fibre
product, which is all that it depends on. -/
private def IsProperSupportCloseds (f : X ⟶ Y) (V : SmallEtale B Y.obj Y.property)
    (Z : Closeds ((SmallEtale.toScheme B X.obj X.property).obj
      ((smallEtaleBaseChange B f).obj V))) : Prop :=
  let _ := hasPullbacks_bigEtaleSite B
  IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
    B.inclusion.map (pullback.fst V.obj.hom f))

private theorem properSupportSections_eq_closeds (f : X ⟶ Y)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj V))) :
    properSupportSections B f F V s =
      IsProperSupportCloseds B f V
        (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj V) s).compl :=
  rfl

/-- **Stacks 0F4X.** The proper-support condition is invariant under an isomorphism of the
abelian sheaf, since isomorphic sections have the same support. -/
public theorem properSupportSections_sheafIso (f : X ⟶ Y)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}}
    (e : F ≅ G) (V : SmallEtale B Y.obj Y.property)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj V))) :
    properSupportSections B f F V s ↔
      properSupportSections B f G V
        (e.hom.hom.app (op ((smallEtaleBaseChange B f).obj V)) s) := by
  let U := (smallEtaleBaseChange B f).obj V
  have h₁ := supportSection_map_subset B X.obj X.property F G e.hom U s
  have h₂ := supportSection_map_subset B X.obj X.property G F e.inv U
    (e.hom.hom.app (op U) s)
  have heval : e.inv.hom.app (op U) (e.hom.hom.app (op U) s) = s :=
    sheafIso_inv_hom_app_apply e.symm (op U) s
  rw [heval] at h₂
  have hz : (zeroOpen B X.obj X.property F U s).compl =
      (zeroOpen B X.obj X.property G U (e.hom.hom.app (op U) s)).compl :=
    Closeds.ext (Set.Subset.antisymm h₂ h₁)
  rw [properSupportSections_eq_closeds, properSupportSections_eq_closeds, hz]

/-- **Stacks 0F4X.** The proper-support condition is invariant under replacing the structure
morphism by an equal one, after transporting the section along the induced identification of
the fibre products. -/
public theorem properSupportSections_congr {g h : X ⟶ Y} (hgh : g = h)
    [LocallyOfFiniteType (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map h)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property)
    (s : F.obj.obj (op ((smallEtaleBaseChange B g).obj V))) :
    properSupportSections B g F V s ↔
      properSupportSections B h F V
        (F.obj.map (eqToIso (congrArg
          (fun k : X ⟶ Y => (smallEtaleBaseChange B k).obj V) hgh)).inv.op s) := by
  subst hgh
  simp

end ProperSupport

section Projections

variable (B : BigEtaleSite.{u})

private theorem pullbackComp_inv_projection {C : Type*} [Category C] {P Q R : C}
    (g : P ⟶ Q) (h : Q ⟶ R) [HasPullbacksAlong g] [HasPullbacksAlong h] (W : Over R) :
    ((Over.pullbackComp g h).inv.app W).left ≫ pullback.fst W.hom (g ≫ h) =
      pullback.fst ((Over.pullback h).obj W).hom g ≫ pullback.fst W.hom h := by
  have identity := congrArg (fun morphism => morphism.left)
    ((Over.pullbackComp g h).inv_hom_id_app W)
  simp only [Over.comp_left, Over.id_left] at identity
  rw [← Over.pullbackComp_left_fst_fst g h W, ← Category.assoc, identity, Category.id_comp]

private theorem smallEtaleComp_hom_projection {P Q R : B.Scheme}
    (g : P ⟶ Q) (h : Q ⟶ R) (W : SmallEtale B R.obj R.property) :
    ((SmallEtale.inclusion B P.obj P.property).map
        ((smallEtaleBaseChange_compIso B P Q R g h).val.hom.app W)).left ≫
          pullback.fst W.obj.hom (g ≫ h) =
      pullback.fst (pullback.snd W.obj.hom h) g ≫ pullback.fst W.obj.hom h := by
  rw [smallEtaleBaseChange_compIso_app]
  exact pullbackComp_inv_projection g h W.obj

private theorem smallEtaleComp_inv_projection {P Q R : B.Scheme}
    (g : P ⟶ Q) (h : Q ⟶ R) (W : SmallEtale B R.obj R.property) :
    ((SmallEtale.inclusion B P.obj P.property).map
        ((smallEtaleBaseChange_compIso B P Q R g h).val.inv.app W)).left ≫
          pullback.fst (pullback.snd W.obj.hom h) g ≫ pullback.fst W.obj.hom h =
      pullback.fst W.obj.hom (g ≫ h) := by
  have comparison : (SmallEtale.inclusion B P.obj P.property).mapIso
      ((smallEtaleBaseChange_compIso B P Q R g h).val.app W) =
      ((Over.pullbackComp g h).app W.obj).symm :=
    Iso.ext (smallEtaleBaseChange_compIso_app B P Q R g h W)
  have inverse := congrArg (fun comparison => comparison.inv.left) comparison
  rw [show ((SmallEtale.inclusion B P.obj P.property).map
      ((smallEtaleBaseChange_compIso B P Q R g h).val.inv.app W)).left =
      ((Over.pullbackComp g h).hom.app W.obj).left from inverse]
  exact Over.pullbackComp_left_fst_fst g h W.obj

private theorem smallEtaleBaseChange_map_projection {P Q : B.Scheme} (g : P ⟶ Q)
    {W V : SmallEtale B Q.obj Q.property} (morphism : W ⟶ V) :
    ((SmallEtale.inclusion B P.obj P.property).map
        ((smallEtaleBaseChange B g).map morphism)).left ≫ pullback.fst V.obj.hom g =
      pullback.fst W.obj.hom g ≫
        ((SmallEtale.inclusion B Q.obj Q.property).map morphism).left := by
  change ((Over.pullback g).map
    ((SmallEtale.inclusion B Q.obj Q.property).map morphism)).left ≫ _ = _
  exact pullback.lift_fst _ _ _

private theorem smallEtaleBaseChange_eq_projection {P Q : B.Scheme} {g h : P ⟶ Q}
    (equality : g = h) (W : SmallEtale B Q.obj Q.property) :
    ((SmallEtale.inclusion B P.obj P.property).map
        (eqToHom (congrArg (fun morphism => (smallEtaleBaseChange B morphism).obj W)
          equality))).left ≫ pullback.fst W.obj.hom h = pullback.fst W.obj.hom g := by
  cases equality
  simp

end Projections

section Restriction

/-- Restriction along the counit of post-composition with an open immersion is injective on
sections modulo the unit of the restriction adjunction: the two descriptions of restriction are
identified by the uniqueness of left adjoints, so two sections with the same image under the
unit have the same restriction. -/
private theorem map_counit_eq_of_unit_eq (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (W : SmallEtale B X.obj X.property) (s t : F.obj.obj (op W))
    (h : (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) s =
        (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) t) :
    F.obj.map ((openPostcomposeAdjunction B j).counit.app W).op s =
      F.obj.map ((openPostcomposeAdjunction B j).counit.app W).op t := by
  let adj₁ := Adjunction.sheafPushforwardContinuous (openPostcomposeAdjunction B j)
    (SmallEtale.topology B X'.obj X'.property) (SmallEtale.topology B X.obj X.property)
    (E := AddCommGrpCat.{v})
  let adj₂ := (smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B X'.obj X'.property)
  let e := Adjunction.leftAdjointUniq adj₁ adj₂
  have key (a : F.obj.obj (op W)) :
      (e.hom.app F).hom.app (op ((smallEtaleBaseChange B j).obj W))
          (F.obj.map ((openPostcomposeAdjunction B j).counit.app W).op a) =
        (adj₂.unit.app F).hom.app (op W) a :=
    congrArg (fun η => η.hom.app (op W) a)
      (Adjunction.unit_leftAdjointUniq_hom_app adj₁ adj₂ F)
  exact mono_app_injective (e.hom.app F) _ ((key s).trans (h.trans (key t).symm))

end Restriction

section CompIso

/-- The comparison of the two proper-support direct images of a sheaf restricted to a nested
open subscheme — restricted in two steps, or in one — together with the equation inside the
ordinary direct image that pins the comparison down.

See [Stacks Project, Tag 0F53](https://stacks.math.columbia.edu/tag/0F53). -/
public noncomputable def openInclusionShriekCompComparison
    (B : BigEtaleSite.{u}) {X'' X' X Y : B.Scheme}
    (i : X'' ⟶ X') (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map i)]
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    letI : IsOpenImmersion (B.inclusion.map (i ≫ j)) := by
      change IsOpenImmersion (B.inclusion.map i ≫ B.inclusion.map j)
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map (i ≫ j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map i ≫ B.inclusion.map (j ≫ f))
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map ((i ≫ j) ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map (i ≫ j) ≫ B.inclusion.map f)
      infer_instance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    let F'' := ((smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X''.obj X''.property)).obj F'
    let Fd := ((smallEtaleBaseChange B (i ≫ j)).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X''.obj X''.property)).obj F
    let Pi := (smallEtaleBaseChange B (i ≫ j ≫ f)).sheafPushforwardContinuous
      AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X''.obj X''.property)
    let Pd := (smallEtaleBaseChange B ((i ≫ j) ≫ f)).sheafPushforwardContinuous
      AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X''.obj X''.property)
    let G'' := (fShriekSubsheaf B (i ≫ j ≫ f) F'').val
    let Gd := (fShriekSubsheaf B ((i ≫ j) ≫ f) Fd).val
    let restrictionIso := (smallEtaleSheafPullbackCompIso B X'' X' X i j
      AddCommGrpCat.{v}).app F
    let pushforwardIso : Pi ≅ Pd :=
      eqToIso (congrArg (fun g : X'' ⟶ Y =>
        (smallEtaleBaseChange B g).sheafPushforwardContinuous
          AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X''.obj X''.property))
        (Category.assoc i j f).symm)
    { comparison : G''.obj.left ≅ Gd.obj.left //
      comparison.hom ≫ Gd.arrow =
        G''.arrow ≫ (Pi.mapIso restrictionIso ≪≫ pushforwardIso.app Fd).hom } := by
  letI : IsOpenImmersion (B.inclusion.map (i ≫ j)) := by
    change IsOpenImmersion (B.inclusion.map i ≫ B.inclusion.map j)
    infer_instance
  letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
    change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
    infer_instance
  letI : LocallyOfFiniteType (B.inclusion.map (i ≫ j ≫ f)) := by
    change LocallyOfFiniteType (B.inclusion.map i ≫ B.inclusion.map (j ≫ f))
    infer_instance
  letI : LocallyOfFiniteType (B.inclusion.map ((i ≫ j) ≫ f)) := by
    change LocallyOfFiniteType (B.inclusion.map (i ≫ j) ≫ B.inclusion.map f)
    infer_instance
  let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)).obj F
  let F'' := ((smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X'.obj X'.property)
    (SmallEtale.topology B X''.obj X''.property)).obj F'
  let Fd := ((smallEtaleBaseChange B (i ≫ j)).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X''.obj X''.property)).obj F
  let Pi := (smallEtaleBaseChange B (i ≫ j ≫ f)).sheafPushforwardContinuous
    AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X''.obj X''.property)
  let Pd := (smallEtaleBaseChange B ((i ≫ j) ≫ f)).sheafPushforwardContinuous
    AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X''.obj X''.property)
  let G'' := (fShriekSubsheaf B (i ≫ j ≫ f) F'').val
  let Gd := (fShriekSubsheaf B ((i ≫ j) ≫ f) Fd).val
  let restrictionIso := (smallEtaleSheafPullbackCompIso B X'' X' X i j
    AddCommGrpCat.{v}).app F
  have hEq : i ≫ j ≫ f = (i ≫ j) ≫ f := (Category.assoc i j f).symm
  let pushforwardIso : Pi ≅ Pd :=
    eqToIso (congrArg (fun g : X'' ⟶ Y =>
      (smallEtaleBaseChange B g).sheafPushforwardContinuous
        AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X''.obj X''.property))
      hEq)
  let ambientIso : Pi.obj F'' ≅ Pd.obj Fd :=
    Pi.mapIso restrictionIso ≪≫ pushforwardIso.app Fd
  let siteIso (V : SmallEtale B Y.obj Y.property) :=
    eqToIso (congrArg (fun g : X'' ⟶ Y => (smallEtaleBaseChange B g).obj V) hEq)
  have hamb (V : SmallEtale B Y.obj Y.property)
      (s : F''.obj.obj (op ((smallEtaleBaseChange B (i ≫ j ≫ f)).obj V))) :
      ambientIso.hom.hom.app (op V) s =
        Fd.obj.map (siteIso V).inv.op
          (restrictionIso.hom.hom.app
            (op ((smallEtaleBaseChange B (i ≫ j ≫ f)).obj V)) s) := by
    simp only [ambientIso, Iso.trans_hom]
    simp [Pi, pushforwardIso, siteIso,
      CategoryTheory.eqToHom_op, CategoryTheory.eqToHom_map]
    rfl
  let PS₁ := fShriekSubsheaf B (i ≫ j ≫ f) F''
  let PS₂ := fShriekSubsheaf B ((i ≫ j) ≫ f) Fd
  have hproper (V : SmallEtale B Y.obj Y.property)
      (s : F''.obj.obj (op ((smallEtaleBaseChange B (i ≫ j ≫ f)).obj V))) :
      properSupportSections B (i ≫ j ≫ f) F'' V s ↔
        properSupportSections B ((i ≫ j) ≫ f) Fd V
          (ambientIso.hom.hom.app (op V) s) := by
    rw [hamb V s]
    exact (properSupportSections_sheafIso B (i ≫ j ≫ f) restrictionIso V s).trans
      (properSupportSections_congr B hEq Fd V _)
  let α : G''.obj.left ⟶ Pi.obj F'' := G''.arrow
  let β : Gd.obj.left ⟶ Pi.obj F'' := Gd.arrow ≫ ambientIso.inv
  haveI : Mono α := inferInstance
  haveI : Mono β := by dsimp only [β]; infer_instance
  have hinv (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) (z : (Pd.obj Fd).obj.obj U) :
      ambientIso.hom.hom.app U (ambientIso.inv.hom.app U z) = z :=
    congrArg (fun k => k z)
      (congrArg (fun k : Pd.obj Fd ⟶ Pd.obj Fd => k.hom.app U) ambientIso.inv_hom_id)
  have hhom (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) (z : (Pi.obj F'').obj.obj U) :
      ambientIso.inv.hom.app U (ambientIso.hom.hom.app U z) = z :=
    congrArg (fun k => k z)
      (congrArg (fun k : Pi.obj F'' ⟶ Pi.obj F'' => k.hom.app U) ambientIso.hom_inv_id)
  have hrange (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) (x : (Pi.obj F'').obj.obj U) :
      (∃ y, α.hom.app U y = x) ↔ (∃ y, β.hom.app U y = x) := by
    calc (∃ y, α.hom.app U y = x)
        ↔ properSupportSections B (i ≫ j ≫ f) F'' (unop U) x := PS₁.property (unop U) x
      _ ↔ properSupportSections B ((i ≫ j) ≫ f) Fd (unop U)
            (ambientIso.hom.hom.app U x) := hproper (unop U) x
      _ ↔ (∃ y, Gd.arrow.hom.app U y = ambientIso.hom.hom.app U x) :=
            (PS₂.property (unop U) _).symm
      _ ↔ (∃ y, β.hom.app U y = x) := by
            refine exists_congr fun y => ?_
            change Gd.arrow.hom.app U y = ambientIso.hom.hom.app U x ↔
              ambientIso.inv.hom.app U (Gd.arrow.hom.app U y) = x
            exact ⟨fun hy => by rw [hy]; exact hhom U x, fun hy => by rw [← hy, hinv]⟩
  obtain ⟨comparison, hcomparison⟩ := isoOfRangeEq α β hrange
  refine ⟨comparison, ?_⟩
  apply (cancel_mono ambientIso.inv).1
  change comparison.hom ≫ (Gd.arrow ≫ ambientIso.inv) =
    (G''.arrow ≫ ambientIso.hom) ≫ ambientIso.inv
  simp only [Category.assoc, ambientIso.hom_inv_id]
  exact hcomparison

/-- **Stacks 0F53.** Restricting an abelian sheaf to a nested open subscheme in two steps or in
one gives canonically isomorphic proper-support direct images. -/
@[stacks 0F53 "open_inclusion_trans"]
public noncomputable def openInclusionShriekCompIso
    (B : BigEtaleSite.{u}) {X'' X' X Y : B.Scheme}
    (i : X'' ⟶ X') (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map i)]
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    letI : IsOpenImmersion (B.inclusion.map (i ≫ j)) := by
      change IsOpenImmersion (B.inclusion.map i ≫ B.inclusion.map j)
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map (i ≫ j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map i ≫ B.inclusion.map (j ≫ f))
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map ((i ≫ j) ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map (i ≫ j) ≫ B.inclusion.map f)
      infer_instance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    let F'' := ((smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X''.obj X''.property)).obj F'
    let Fd := ((smallEtaleBaseChange B (i ≫ j)).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X''.obj X''.property)).obj F
    (fShriekSubsheaf B (i ≫ j ≫ f) F'').val.obj.left ≅
      (fShriekSubsheaf B ((i ≫ j) ≫ f) Fd).val.obj.left :=
  (openInclusionShriekCompComparison B i j f F).val

/-- **Stacks 0F53.** The comparison of proper-support direct images is the comparison of
restrictions, read inside the ordinary direct images. -/
@[stacks 0F53 "open_inclusion_trans"]
public theorem openInclusionShriekCompIso_ambient
    (B : BigEtaleSite.{u}) {X'' X' X Y : B.Scheme}
    (i : X'' ⟶ X') (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map i)]
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    letI : IsOpenImmersion (B.inclusion.map (i ≫ j)) := by
      change IsOpenImmersion (B.inclusion.map i ≫ B.inclusion.map j)
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map (i ≫ j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map i ≫ B.inclusion.map (j ≫ f))
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map ((i ≫ j) ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map (i ≫ j) ≫ B.inclusion.map f)
      infer_instance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    let F'' := ((smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X''.obj X''.property)).obj F'
    let Fd := ((smallEtaleBaseChange B (i ≫ j)).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X''.obj X''.property)).obj F
    let Pi := (smallEtaleBaseChange B (i ≫ j ≫ f)).sheafPushforwardContinuous
      AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X''.obj X''.property)
    let Pd := (smallEtaleBaseChange B ((i ≫ j) ≫ f)).sheafPushforwardContinuous
      AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X''.obj X''.property)
    let restrictionIso := (smallEtaleSheafPullbackCompIso B X'' X' X i j
      AddCommGrpCat.{v}).app F
    let pushforwardIso : Pi ≅ Pd :=
      eqToIso (congrArg (fun g : X'' ⟶ Y =>
        (smallEtaleBaseChange B g).sheafPushforwardContinuous
          AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X''.obj X''.property))
        (Category.assoc i j f).symm)
    (openInclusionShriekCompIso B i j f F).hom ≫
        (fShriekSubsheaf B ((i ≫ j) ≫ f) Fd).val.arrow =
      (fShriekSubsheaf B (i ≫ j ≫ f) F'').val.arrow ≫
        (Pi.mapIso restrictionIso ≪≫ pushforwardIso.app Fd).hom := by
  unfold openInclusionShriekCompIso
  exact (openInclusionShriekCompComparison B i j f F).property

end CompIso

section Transitivity

/-- **Stacks 0F53.** Extension by zero is transitive: for nested open subschemes
`X'' ⟶ X' ⟶ X` of the source of a separated morphism locally of finite type, the canonical map
from the proper-support direct image on `X''` is the composite of the two successive canonical
maps, once the two proper-support direct images on `X''` are identified. -/
@[stacks 0F53 "open_inclusion_trans"]
public theorem openInclusionShriekMap_comp
    (B : BigEtaleSite.{u}) {X'' X' X Y : B.Scheme}
    (i : X'' ⟶ X') (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map i)]
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    letI : IsOpenImmersion (B.inclusion.map (i ≫ j)) := by
      change IsOpenImmersion (B.inclusion.map i ≫ B.inclusion.map j)
      infer_instance
    letI : IsSeparated (B.inclusion.map (j ≫ f)) := by
      change IsSeparated (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map (i ≫ j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map i ≫ B.inclusion.map (j ≫ f))
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map ((i ≫ j) ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map (i ≫ j) ≫ B.inclusion.map f)
      infer_instance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    (openInclusionShriekCompIso B i j f F).hom ≫
        (openInclusionShriekMap B (i ≫ j) f F).val =
      (openInclusionShriekMap B i (j ≫ f) F').val ≫
        (openInclusionShriekMap B j f F).val := by
  let : IsOpenImmersion (B.inclusion.map (i ≫ j)) := by
    change IsOpenImmersion (B.inclusion.map i ≫ B.inclusion.map j)
    infer_instance
  let : IsSeparated (B.inclusion.map (j ≫ f)) := by
    change IsSeparated (B.inclusion.map j ≫ B.inclusion.map f)
    infer_instance
  let : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
    change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
    infer_instance
  let : LocallyOfFiniteType (B.inclusion.map (i ≫ j ≫ f)) := by
    change LocallyOfFiniteType (B.inclusion.map i ≫ B.inclusion.map (j ≫ f))
    infer_instance
  let : LocallyOfFiniteType (B.inclusion.map ((i ≫ j) ≫ f)) := by
    change LocallyOfFiniteType (B.inclusion.map (i ≫ j) ≫ B.inclusion.map f)
    infer_instance
  let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)).obj F
  let F'' := ((smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X'.obj X'.property)
    (SmallEtale.topology B X''.obj X''.property)).obj F'
  let Fd := ((smallEtaleBaseChange B (i ≫ j)).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X''.obj X''.property)).obj F
  let G'' := (fShriekSubsheaf B (i ≫ j ≫ f) F'').val
  let Gd := (fShriekSubsheaf B ((i ≫ j) ≫ f) Fd).val
  let G' := (fShriekSubsheaf B (j ≫ f) F').val
  let G := (fShriekSubsheaf B f F).val
  let hcomp := openInclusionShriekCompIso B i j f F
  let mdPack := openInclusionShriekMap B (i ≫ j) f F
  let miPack := openInclusionShriekMap B i (j ≫ f) F'
  let mjPack := openInclusionShriekMap B j f F
  let md := mdPack.val
  let mi := miPack.val
  let mj := mjPack.val
  apply (cancel_mono G.arrow).1
  apply Sheaf.homEquiv.injective
  ext V a
  change G.arrow.hom.app V (md.hom.app V (hcomp.hom.hom.app V a)) =
    G.arrow.hom.app V (mj.hom.app V (mi.hom.app V a))
  let VY : SmallEtale B Y.obj Y.property := unop V
  have hd := mdPack.property.2 VY (hcomp.hom.hom.app V a)
  have hi := miPack.property.2 VY a
  have hj := mjPack.property.2 VY (mi.hom.app V a)
  rcases hd with ⟨hd₁, hd₂⟩
  rcases hi with ⟨hi₁, hi₂⟩
  rcases hj with ⟨hj₁, hj₂⟩
  let W := (smallEtaleBaseChange B f).obj VY
  let ij : X'' ⟶ X := i ≫ j
  have hfst : IsOpenImmersion
      (B.inclusion.map (pullback.fst (Over.hom W.obj) ij)) := by
    apply MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback (Over.hom W.obj) ij).flip.map B.inclusion)
    infer_instance
  let k : (openPostcompose B ij).obj ((smallEtaleBaseChange B ij).obj W) ⟶ W :=
    (openPostcomposeAdjunction B ij).counit.app W
  have hkScheme : (SmallEtale.toScheme B X.obj X.property).map k =
      B.inclusion.map (pullback.fst (Over.hom W.obj) ij) :=
    openPostcomposeAdjunction_counit_toScheme B ij W
  let sD := G.arrow.hom.app V (md.hom.app V (hcomp.hom.hom.app V a))
  let sN := G.arrow.hom.app V (mj.hom.app V (mi.hom.app V a))
  change F.obj.obj (op W) at sD
  change F.obj.obj (op W) at sN
  change sD = sN
  have hsd : supportSection B X.obj X.property F W sD ⊆
      Set.range ((SmallEtale.toScheme B X.obj X.property).map k).base := by
    change supportSection B X.obj X.property F W
        (G.arrow.hom.app V (md.hom.app V (hcomp.hom.hom.app V a))) ⊆ _
    rw [hkScheme, hd₂]
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, rfl⟩
  let Wj := (smallEtaleBaseChange B j).obj W
  let Wc := (smallEtaleBaseChange B (j ≫ f)).obj VY
  let ejf := (smallEtaleBaseChange_compIso B X' X Y j f).val.app VY
  let eIJsite := (smallEtaleBaseChange_compIso B X'' X' X i j).val.app W
  let eif := (smallEtaleBaseChange_compIso B X'' X' Y i (j ≫ f)).val.app VY
  let eijf := (smallEtaleBaseChange_compIso B X'' X Y ij f).val.app VY
  have hAssoc : i ≫ j ≫ f = ij ≫ f := (Category.assoc i j f).symm
  let castAssoc := eqToHom
    (congrArg (fun g : X'' ⟶ Y => (smallEtaleBaseChange B g).obj VY) hAssoc)
  let castIso := eqToIso
    (congrArg (fun g : X'' ⟶ Y => (smallEtaleBaseChange B g).obj VY) hAssoc)
  let adjI := (smallEtaleBaseChange B i).sheafAdjunctionContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X'.obj X'.property) (SmallEtale.topology B X''.obj X''.property)
  let adjJ := (smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B X'.obj X'.property)
  let adjIJ := (smallEtaleBaseChange B (i ≫ j)).sheafAdjunctionContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B X''.obj X''.property)
  let sMid := (G'.arrow.hom.app V) (mi.hom.app V a)
  change F''.obj.map eif.hom.op
      (G''.arrow.hom.app V a) =
    (((adjI.unit.app F').hom.app (op Wc))) sMid
    at hi₁
  change F'.obj.map ejf.hom.op sMid =
    (((adjJ.unit.app F).hom.app (op W))) sN at hj₁
  have hWj_left : Over.left Wj.obj = pullback (Over.hom W.obj) j := rfl
  let fstJ : Over.left Wj.obj ⟶ Over.left W.obj :=
    eqToHom hWj_left ≫ pullback.fst (Over.hom W.obj) j
  let q := pullback.fst (Over.hom Wc.obj) i ≫
    (((SmallEtale.inclusion B X'.obj X'.property).map ejf.inv).left ≫ fstJ)
  let p := pullback.snd (Over.hom Wc.obj) i
  have hWj : Over.hom Wj.obj = pullback.snd (Over.hom W.obj) j := by
    simp [Wj, smallEtaleBaseChange_obj_obj]
  have hOver' :
      ((SmallEtale.inclusion B X'.obj X'.property).map ejf.inv).left ≫
          pullback.snd (Over.hom W.obj) j = Over.hom Wc.obj := by
    rw [← hWj]
    exact Over.w ((SmallEtale.inclusion B X'.obj X'.property).map ejf.inv)
  have hpbj : pullback.fst (Over.hom W.obj) j ≫ Over.hom W.obj =
      pullback.snd (Over.hom W.obj) j ≫ j := pullback.condition
  have hfstJ : fstJ ≫ Over.hom W.obj =
      pullback.fst (Over.hom W.obj) j ≫ Over.hom W.obj := rfl
  have hpbi : pullback.fst (Over.hom Wc.obj) i ≫ Over.hom Wc.obj =
      pullback.snd (Over.hom Wc.obj) i ≫ i := pullback.condition
  have hchain :
      (((SmallEtale.inclusion B X'.obj X'.property).map ejf.inv).left ≫ fstJ) ≫
        Over.hom W.obj = Over.hom Wc.obj ≫ j := by
    rw [Category.assoc, hfstJ, hpbj, reassoc_of% hOver']
  have hcone : q ≫ Over.hom W.obj = p ≫ ij := by
    dsimp only [q, p, ij]
    calc
      _ = pullback.fst (Over.hom Wc.obj) i ≫
          ((((SmallEtale.inclusion B X'.obj X'.property).map ejf.inv).left ≫
            pullback.fst (Over.hom W.obj) j) ≫ Over.hom W.obj) := Category.assoc _ _ _
      _ = pullback.fst (Over.hom Wc.obj) i ≫ (Over.hom Wc.obj ≫ j) :=
        congrArg (fun g => pullback.fst (Over.hom Wc.obj) i ≫ g) hchain
      _ = pullback.snd (Over.hom Wc.obj) i ≫ i ≫ j := by
        calc
          _ = (pullback.fst (Over.hom Wc.obj) i ≫ Over.hom Wc.obj) ≫ j :=
            (Category.assoc _ _ _).symm
          _ = (pullback.snd (Over.hom Wc.obj) i ≫ i) ≫ j :=
            congrArg (fun g => g ≫ j) hpbi
          _ = pullback.snd (Over.hom Wc.obj) i ≫ i ≫ j := Category.assoc _ _ _
      _ = pullback.snd (Over.hom Wc.obj) i ≫ ij := rfl
  let lB := pullback.lift q p hcone
  have hlB : lB ≫ pullback.fst (Over.hom W.obj) ij = q := pullback.lift_fst _ _ _
  have hfactor : (B.inclusion.map lB) ≫
      (SmallEtale.toScheme B X.obj X.property).map k = B.inclusion.map q := by
    rw [hkScheme]
    change B.inclusion.map lB ≫ B.inclusion.map
      (pullback.fst (Over.hom W.obj) ij) = B.inclusion.map q
    rw [← Functor.map_comp, hlB]
  have htransport' :
      supportSection B X'.obj X'.property F' Wj (F'.obj.map ejf.hom.op sMid) =
        ((SmallEtale.toScheme B X'.obj X'.property).map ejf.symm.hom).base ''
          supportSection B X'.obj X'.property F' Wc sMid :=
    supportSection_map_inv B X'.obj X'.property F' ejf.symm sMid
  have hmap : ((SmallEtale.toScheme B X'.obj X'.property).map ejf.symm.hom).base =
      (B.inclusion.map
        ((SmallEtale.inclusion B X'.obj X'.property).map ejf.inv).left).base := by
    change ((BigEtaleOver.toScheme B X'.obj X'.property).map
      ((SmallEtale.inclusion B X'.obj X'.property).map ejf.symm.hom)).base = _
    rw [Iso.symm_hom]
    rfl
  have hsn : supportSection B X.obj X.property F W sN ⊆
      Set.range ((SmallEtale.toScheme B X.obj X.property).map k).base := by
    intro x hx
    rw [hj₂] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    change y ∈ supportSection B X'.obj X'.property F' Wj
      (F'.obj.map ejf.hom.op sMid) at hy
    rw [htransport'] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    change z ∈ supportSection B X'.obj X'.property F' Wc sMid at hz
    rw [hi₂] at hz
    obtain ⟨w, hw, hzw⟩ := hz
    refine ⟨(B.inclusion.map lB).base w, ?_⟩
    have hq : (B.inclusion.map q).base w = x := by
      have hqcomp : (B.inclusion.map q).base =
          (B.inclusion.map (pullback.fst (Over.hom Wc.obj) i)).base ≫
            (B.inclusion.map
              ((SmallEtale.inclusion B X'.obj X'.property).map ejf.inv).left).base ≫
              (B.inclusion.map fstJ).base := by
        dsimp only [q]
        simp only [Functor.map_comp, Scheme.Hom.comp_base]
      have hfstJ_point : (B.inclusion.map fstJ).base y =
          (B.inclusion.map (pullback.fst (Over.hom W.obj) j)).base y := rfl
      rw [hqcomp, TopCat.comp_app, TopCat.comp_app, hzw, ← hmap]
      exact (congrArg (fun y => (B.inclusion.map fstJ).base y) hyz).trans
        (hfstJ_point.trans hxy)
    exact (congrArg (fun m => m.base w) hfactor).trans hq
  let : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map k) := by
    rw [hkScheme]
    exact hfst
  apply eq_of_map_eq_of_supportSection_subset B X.obj X.property F k sD sN hsd hsn
  apply map_counit_eq_of_unit_eq B ij F W sD sN
  let Pi := (smallEtaleBaseChange B (i ≫ j ≫ f)).sheafPushforwardContinuous
    AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X''.obj X''.property)
  let Pd := (smallEtaleBaseChange B ((i ≫ j) ≫ f)).sheafPushforwardContinuous
    AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X''.obj X''.property)
  let restrictionIso := (smallEtaleSheafPullbackCompIso B X'' X' X i j
    AddCommGrpCat.{v}).app F
  let pushforwardIso : Pi ≅ Pd :=
    eqToIso (congrArg (fun g : X'' ⟶ Y =>
      (smallEtaleBaseChange B g).sheafPushforwardContinuous
        AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X''.obj X''.property))
      (Category.assoc i j f).symm)
  let ambientIso : Pi.obj F'' ≅ Pd.obj Fd :=
    Pi.mapIso restrictionIso ≪≫ pushforwardIso.app Fd
  have hamb : hcomp.hom ≫ Gd.arrow = G''.arrow ≫ ambientIso.hom := by
    simpa only [hcomp, ambientIso, Pi, Pd, restrictionIso, pushforwardIso] using
      (openInclusionShriekCompIso_ambient B i j f F)
  have hambV : Gd.arrow.hom.app V (hcomp.hom.hom.app V a) =
      ambientIso.hom.hom.app V (G''.arrow.hom.app V a) :=
    congrArg (fun φ => φ a) (congrArg (fun φ => φ.hom.app V) hamb)
  have hcoh := CategoryTheory.unit_conjugateEquiv
    (adjJ.comp adjI) adjIJ
    (smallEtaleSheafPullbackCompIso B X'' X' X i j AddCommGrpCat.{v}).inv F
  simp only [adjI, adjJ, adjIJ, smallEtaleSheafPullbackCompIso, Functor.sheafPullbackComp',
    CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
    CategoryTheory.Adjunction.comp_unit_app] at hcoh
  have hcohApp := congrArg (fun m => m.hom.app (op W)) hcoh
  have hcohVal := congrArg (fun fn => fn sN) hcohApp
  have hSite : eIJsite.inv ≫ (smallEtaleBaseChange B i).map ejf.hom ≫
      eif.hom ≫ castAssoc = eijf.hom := by
    let I := SmallEtale.inclusion B X''.obj X''.property
    apply I.map_injective
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (I.map eIJsite.inv).left ≫ (I.map
            ((smallEtaleBaseChange B i).map ejf.hom)).left ≫
            (I.map eif.hom).left ≫ (I.map castAssoc).left ≫
            pullback.fst VY.obj.hom (ij ≫ f) =
          (I.map eijf.hom).left ≫ pullback.fst VY.obj.hom (ij ≫ f)
      rw [smallEtaleBaseChange_eq_projection B hAssoc VY]
      dsimp only [I, eIJsite, eif, eijf]
      simp only [Iso.app_hom, Iso.app_inv]
      rw [smallEtaleComp_hom_projection B ij f VY,
        smallEtaleComp_hom_projection B i (j ≫ f) VY]
      have hmapi := smallEtaleBaseChange_map_projection B i ejf.hom
      change ((SmallEtale.inclusion B X''.obj X''.property).map
            ((smallEtaleBaseChange B i).map ejf.hom)).left ≫
            pullback.fst (pullback.snd VY.obj.hom (j ≫ f)) i =
          pullback.fst (pullback.snd W.obj.hom j) i ≫
            ((SmallEtale.inclusion B X'.obj X'.property).map ejf.hom).left at hmapi
      rw [← Category.assoc _ _ (pullback.fst VY.obj.hom (j ≫ f)), hmapi]
      simp only [Category.assoc]
      dsimp only [ejf]
      simp only [Iso.app_hom]
      rw [smallEtaleComp_hom_projection B j f VY]
      have hinvp := smallEtaleComp_inv_projection B i j W
      simpa only [Category.assoc, W, ij, smallEtaleBaseChange_obj_obj,
        Over.pullback_obj_hom] using
        congrArg (fun morphism => morphism ≫ pullback.fst VY.obj.hom f) hinvp
    · exact (Over.w (I.map
        (eIJsite.inv ≫ (smallEtaleBaseChange B i).map ejf.hom ≫
          eif.hom ≫ castAssoc))).trans (Over.w (I.map eijf.hom)).symm
  rw [← hd₁, hambV]
  simp only [ambientIso, Iso.trans_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, Functor.mapIso_hom, ConcreteCategory.comp_apply]
  have hcohValues :
      F''.obj.map eIJsite.inv.op ((adjI.unit.app F').hom.app
          (op ((smallEtaleBaseChange B j).obj W)) ((adjJ.unit.app F).hom.app (op W) sN)) =
        restrictionIso.inv.hom.app (op ((smallEtaleBaseChange B ij).obj W))
          ((adjIJ.unit.app F).hom.app (op W) sN) := by
    simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
      Functor.sheafPushforwardContinuous_map_hom_app,
      Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at hcohVal
    exact hcohVal
  have hambientValue : ambientIso.hom.hom.app V (G''.arrow.hom.app V a) =
      Fd.obj.map castIso.inv.op
        (restrictionIso.hom.hom.app
          (op ((smallEtaleBaseChange B (i ≫ j ≫ f)).obj VY))
          (G''.arrow.hom.app V a)) := by
    simp only [ambientIso, Iso.trans_hom]
    simp [Pi, pushforwardIso, castIso,
      CategoryTheory.eqToHom_op, CategoryTheory.eqToHom_map]
    rfl
  have hcast : eijf.hom ≫ castIso.inv =
      eIJsite.inv ≫ (smallEtaleBaseChange B i).map ejf.hom ≫ eif.hom := by
    rw [← hSite]
    change (eIJsite.inv ≫ (smallEtaleBaseChange B i).map ejf.hom ≫
      eif.hom ≫ castIso.hom) ≫ castIso.inv = _
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change Fd.obj.map eijf.hom.op
    (ambientIso.hom.hom.app V (G''.arrow.hom.app V a)) = _
  rw [hambientValue, ← CategoryTheory.comp_apply, ← Fd.obj.map_comp, ← op_comp, hcast,
    op_comp, op_comp, Fd.obj.map_comp, Fd.obj.map_comp]
  change Fd.obj.map eIJsite.inv.op
      (Fd.obj.map ((smallEtaleBaseChange B i).map ejf.hom).op
        (Fd.obj.map eif.hom.op
          (restrictionIso.hom.hom.app
            (op ((smallEtaleBaseChange B (i ≫ j ≫ f)).obj VY))
            (G''.arrow.hom.app V a)))) = _
  have hrestrictionValue := congrArg (fun morphism => morphism (G''.arrow.hom.app V a))
    (restrictionIso.hom.hom.naturality
      (eIJsite.inv ≫ (smallEtaleBaseChange B i).map ejf.hom ≫ eif.hom).op)
  change (F''.obj.map
        (eIJsite.inv ≫ (smallEtaleBaseChange B i).map ejf.hom ≫ eif.hom).op ≫
      restrictionIso.hom.hom.app (op ((smallEtaleBaseChange B ij).obj W)))
        (G''.arrow.hom.app V a) =
    (restrictionIso.hom.hom.app
        (op ((smallEtaleBaseChange B (i ≫ j ≫ f)).obj VY)) ≫
      Fd.obj.map (eIJsite.inv ≫ (smallEtaleBaseChange B i).map ejf.hom ≫ eif.hom).op)
        (G''.arrow.hom.app V a) at hrestrictionValue
  simp only [op_comp, Functor.map_comp] at hrestrictionValue
  change restrictionIso.hom.hom.app (op ((smallEtaleBaseChange B ij).obj W))
      (F''.obj.map eIJsite.inv.op
        (F''.obj.map ((smallEtaleBaseChange B i).map ejf.hom).op
          (F''.obj.map eif.hom.op (G''.arrow.hom.app V a)))) =
    Fd.obj.map eIJsite.inv.op
      (Fd.obj.map ((smallEtaleBaseChange B i).map ejf.hom).op
        (Fd.obj.map eif.hom.op
          (restrictionIso.hom.hom.app
            (op ((smallEtaleBaseChange B (i ≫ j ≫ f)).obj VY))
            (G''.arrow.hom.app V a)))) at hrestrictionValue
  rw [← hrestrictionValue, hi₁]
  have hunitNaturalValue := congrArg (fun morphism => morphism sMid)
    ((adjI.unit.app F').hom.naturality
      ejf.hom.op).symm
  change F''.obj.map ((smallEtaleBaseChange B i).map ejf.hom).op
      (((adjI.unit.app F').hom.app (op Wc))
          sMid) =
    (((adjI.unit.app F').hom.app (op Wj)))
      (F'.obj.map ejf.hom.op sMid) at hunitNaturalValue
  rw [hunitNaturalValue, hj₁, hcohValues]
  exact sheafIso_inv_hom_app_apply restrictionIso _ _

end Transitivity

end AlgebraicGeometry.SmallEtale

end
