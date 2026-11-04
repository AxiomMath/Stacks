module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactSupport
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCover
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusionComp
public import StacksFrontier.AlgebraicGeometry.Etale.SupportTransport

/-!
# Compactly supported sections and open subschemes

Let `X` be a separated scheme locally of finite type over a field `k`, let `F` be an abelian
sheaf on the small étale site of `X` inside a big étale site, and let `X' ⊆ X` be an open
subscheme. Extension by zero gives an injection of the compactly supported sections of the
restriction of `F` to `X'` into the compactly supported sections of `F`, characterised by its
restriction back to `X'` and by the fact that it carries supports to their images. These
injections are the identity for `X' = X` and compose for nested open subschemes, so compactly
supported sections form a precosheaf on the Zariski site of `X`. Its image is the set of
compactly supported sections of `F` whose support is contained in `X'`; hence two compactly
supported sections on two open subschemes with a common extension by zero both come from their
intersection, and a compactly supported section whose support splits as a disjoint union of a
closed subset of one open subscheme and a closed subset of the other is the sum of two
extensions by zero.

## Main definitions

* `AlgebraicGeometry.SmallEtale.compactlySupportedSections_openInclusion` — the canonical
  injection on compactly supported sections induced by extension by zero along an open
  immersion, together with the two equations that characterise it.

## Main results

* `AlgebraicGeometry.SmallEtale.compactlySupportedSections_openInclusion_id` — for the identity
  open immersion the injection is surjective, hence an isomorphism.
* `AlgebraicGeometry.SmallEtale.compactlySupportedSections_openInclusion_comp` — the injections
  compose, up to the canonical identification of the two restrictions to the smaller open
  subscheme.
* `AlgebraicGeometry.SmallEtale.exists_compactlySupportedSections_openInclusion_eq` — the image
  of the injection consists of the compactly supported sections supported inside the open
  subscheme.
* `AlgebraicGeometry.SmallEtale.exists_compactlySupportedSections_openInclusion_inter` —
  Mayer–Vietoris: a compactly supported section lying in the images of two open subschemes
  comes from their intersection.
* `AlgebraicGeometry.SmallEtale.exists_compactlySupportedSections_openInclusion_add` — gluing:
  a compactly supported section whose support is a disjoint union of closed subsets of two
  open subschemes is the sum of two extensions by zero.

## Implementation notes

Global sections are sections over the final object of the small étale site, and the final
object of the small étale site of an open subscheme is the base change of the final object of
the ambient one; that identification is what lets the extension-by-zero map of Tag 0F53, which
is a map of proper-support direct images over an arbitrary test object, be evaluated on global
sections. A compactly supported section of the restriction therefore has proper support over
the ambient test object, and its image under extension by zero is compactly supported because
the image of a closed subset proper over the base field under a morphism to a separated scheme
is again proper over the base field.

The characterisation of the injection is used rather than its construction in the two
precosheaf laws: the identity law is the statement that the unit of the restriction adjunction
along an identity is an isomorphism, and the composition law compares the two units through the
coherence of restriction with composition. In both cases a section of the ambient sheaf
supported inside the open subscheme is determined by its restriction there, which is what
reduces the laws to statements about units.

The description of the image runs the same comparison backwards: a section supported inside the
open subscheme is the extension by zero of the transport of its unit along the identification of
the base change of the final object with the final object of the open subscheme, which is
compactly supported because the support of that transport is the inverse image of the original
support.

Gluing is the splitting of a section along a disjoint decomposition of its support: the
restriction to the complement of the second closed subset is supported on the inverse image of
the first, and the extension by zero of Tag 0F6F of that restriction is a section supported on
the first subset whose difference with the original section vanishes on that complement, hence
is supported on the second subset. The two summands are compactly supported because their
supports are closed subsets of the original support. Note that the surjectivity of the sum map
without such a decomposition of the support is false: on a proper curve `X` over `k` with the
constant sheaf `ℤ`, the two complements of a pair of distinct closed points cover `X`, while
`H^0_c` of each of them vanishes and `H^0_c(X, ℤ) = ℤ`.

## References

* [Stacks Project, Tag 0F74](https://stacks.math.columbia.edu/tag/0F74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

section FinalObject

/-- The base change of the final object of the small étale site along a morphism is the final
object of the small étale site of the source. -/
public noncomputable def baseChangeFinalIso (B : BigEtaleSite.{u}) {S T : B.Scheme}
    (g : T ⟶ S) :
    (smallEtaleBaseChange B g).obj (SmallEtale.final B S.obj S.property) ≅
      SmallEtale.final B T.obj T.property := by
  have hw : g ≫ 𝟙 (B.obj S.obj S.property) = 𝟙 (B.obj T.obj T.property) ≫ g := by
    rw [Category.comp_id, Category.id_comp]
  have hiso : IsIso (pullback.snd (𝟙 (B.obj S.obj S.property)) g) := by
    refine ⟨⟨pullback.lift g (𝟙 (B.obj T.obj T.property)) hw, ?_, by rw [pullback.lift_snd]⟩⟩
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp,
        ← Category.comp_id (pullback.fst (𝟙 (B.obj S.obj S.property)) g)]
      exact pullback.condition.symm
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  exact ObjectProperty.isoMk (BigEtaleOver.IsEtaleOver B T.obj T.property)
    (Over.isoMk (@asIso _ _ _ _ _ hiso))

/-- Global sections of a sheaf on the small étale site of the source are the sections of its
direct image over the final object of the target. -/
private noncomputable def pushforwardFinalSectionsIso (B : BigEtaleSite.{u}) {S T : B.Scheme}
    (g : T ⟶ S) (F : Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{v}) :
    F.obj.obj (op (SmallEtale.final B T.obj T.property)) ≅
      (((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj F).obj.obj
        (op (SmallEtale.final B S.obj S.property)) := by
  simpa only [Functor.sheafPushforwardContinuous_obj_obj_obj] using
    (F.obj.mapIso (baseChangeFinalIso B g).symm.op).symm

end FinalObject

section ProperSupport

variable (k : Type u) [Field k] (B : BigEtaleSite.{u})

/-- A compactly supported section of the restriction of an abelian sheaf to an open subscheme
has proper support as a section of the proper-support direct image along that open immersion:
the base change of the final object is isomorphic to the final object of the open subscheme,
and the isomorphism carries the support to the support. -/
private theorem properSupportSections_compactSection {X' X : B.Scheme} (j : X' ⟶ X)
    (f : X.obj ⟶ Spec (.of k)) [hf : IsSeparated f] [LocallyOfFiniteType f]
    [IsOpenImmersion (B.inclusion.map j)]
    [hJ : LocallyOfFiniteType (B.inclusion.map j ≫ f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (s : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property
      (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).obj F)) :
    properSupportSections B (j ≫ 𝟙 X)
      (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).obj F)
      (SmallEtale.final B X.obj X.property)
      (((((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).obj F).obj.mapIso
        (baseChangeFinalIso B (j ≫ 𝟙 X)).symm.op).inv s.1) := by
  let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)).obj F
  let U := SmallEtale.final B X.obj X.property
  let V := SmallEtale.final B X'.obj X'.property
  let A := (smallEtaleBaseChange B (j ≫ 𝟙 X)).obj U
  let e := baseChangeFinalIso B (j ≫ 𝟙 X)
  let qIso := (SmallEtale.toScheme B X'.obj X'.property).mapIso e
  let q := qIso.hom
  let ZV : Closeds X'.obj := (zeroOpen B X'.obj X'.property F' V s.1).compl
  let ZA : Closeds ((SmallEtale.toScheme B X'.obj X'.property).obj A) :=
    (zeroOpen B X'.obj X'.property F' A ((F'.obj.mapIso e.symm.op).inv s.1)).compl
  have hs : IsProperOver (B.inclusion.map j ≫ f) ZV :=
    (mem_compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property F' s.1).mp s.2
  have htransport : supportSection B X'.obj X'.property F' V s.1 =
      q.base '' supportSection B X'.obj X'.property F' A
        ((F'.obj.mapIso e.symm.op).inv s.1) := by
    have ht := supportSection_map_inv B X'.obj X'.property F' e
      ((F'.obj.mapIso e.symm.op).inv s.1)
    rwa [show F'.obj.map e.inv.op ((F'.obj.mapIso e.symm.op).inv s.1) = s.1 from
      (F'.obj.mapIso e.symm.op).inv_hom_id_apply s.1] at ht
  have hbij : Function.Bijective q.base := by
    refine ⟨fun x y h => ?_, fun y => ⟨qIso.inv.base y, ?_⟩⟩
    · calc x = qIso.inv.base (q.base x) := (congrArg (fun g => g.base x) qIso.hom_inv_id).symm
        _ = qIso.inv.base (q.base y) := congrArg qIso.inv.base h
        _ = y := congrArg (fun g => g.base y) qIso.hom_inv_id
    · exact congrArg (fun g => g y) (congrArg (fun g => g.base) qIso.inv_hom_id)
  have hqType : LocallyOfFiniteType q := by
    have hcomp : LocallyOfFiniteType (q ≫ qIso.inv) := by
      rw [qIso.hom_inv_id]
      infer_instance
    exact locallyOfFiniteType_of_comp q qIso.inv
  have hqcomp : LocallyOfFiniteType (q ≫ (B.inclusion.map j ≫ f)) :=
    @locallyOfFiniteType_comp _ _ _ q (B.inclusion.map j ≫ f) hqType hJ
  have hpreimage : ZA = ZV.preimage q.continuous := by
    apply SetLike.coe_injective
    change supportSection B X'.obj X'.property F' A ((F'.obj.mapIso e.symm.op).inv s.1) =
      q.base ⁻¹' supportSection B X'.obj X'.property F' V s.1
    rw [htransport, Set.preimage_image_eq _ hbij.1]
  have hproperA : IsProperOver (q ≫ (B.inclusion.map j ≫ f)) ZA := by
    rw [hpreimage]
    exact @isProperOver_preimage _ _ _ q (B.inclusion.map j ≫ f) (by infer_instance) hJ ZV hs
  change IsProper ((Scheme.IdealSheafData.vanishingIdeal ZA).subschemeι ≫
    B.inclusion.map (pullback.fst U.obj.hom (j ≫ 𝟙 X)))
  have hcond : pullback.snd U.obj.hom (j ≫ 𝟙 X) ≫ j =
      pullback.fst U.obj.hom (j ≫ 𝟙 X) := by
    have h := (pullback.condition (f := U.obj.hom) (g := j ≫ 𝟙 X)).symm
    have h1 : pullback.snd U.obj.hom (j ≫ 𝟙 X) ≫ j =
        pullback.snd U.obj.hom (j ≫ 𝟙 X) ≫ (j ≫ 𝟙 X) :=
      congrArg (fun m => pullback.snd U.obj.hom (j ≫ 𝟙 X) ≫ m) (Category.comp_id j).symm
    have h2 : pullback.fst U.obj.hom (j ≫ 𝟙 X) ≫ U.obj.hom =
        pullback.fst U.obj.hom (j ≫ 𝟙 X) :=
      Category.comp_id (pullback.fst U.obj.hom (j ≫ 𝟙 X))
    exact h1.trans (h.trans h2)
  have hproj : q ≫ B.inclusion.map j =
      B.inclusion.map (pullback.fst U.obj.hom (j ≫ 𝟙 X)) := by
    have h := congrArg B.inclusion.map hcond
    rwa [B.inclusion.map_comp] at h
  have hcomp : IsProper ((Scheme.IdealSheafData.vanishingIdeal ZA).subschemeι ≫
      B.inclusion.map (pullback.fst U.obj.hom (j ≫ 𝟙 X)) ≫ f) := by
    have hfac : q ≫ (B.inclusion.map j ≫ f) =
        B.inclusion.map (pullback.fst U.obj.hom (j ≫ 𝟙 X)) ≫ f := by
      rw [← Category.assoc, hproj]
      rfl
    have hEq : (Scheme.IdealSheafData.vanishingIdeal ZA).subschemeι ≫
        (q ≫ (B.inclusion.map j ≫ f)) =
        (Scheme.IdealSheafData.vanishingIdeal ZA).subschemeι ≫
          (B.inclusion.map (pullback.fst U.obj.hom (j ≫ 𝟙 X)) ≫ f) :=
      congrArg (fun g => (Scheme.IdealSheafData.vanishingIdeal ZA).subschemeι ≫ g) hfac
    rw [← hEq]
    exact hproperA
  exact @IsProper.of_comp _ _ _
    ((Scheme.IdealSheafData.vanishingIdeal ZA).subschemeι ≫
      B.inclusion.map (pullback.fst U.obj.hom (j ≫ 𝟙 X))) f hcomp hf

/-- The data of the canonical injection on compactly supported sections induced by extension by
zero along an open immersion, with the two equations that pin it down. -/
private noncomputable def compactlySupportedSectionsOpenInclusionData {X' X : B.Scheme}
    (j : X' ⟶ X) (f : X.obj ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    letI : LocallyOfFiniteType (B.inclusion.map j ≫ f) := inferInstance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    {φ : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property F' →+
        compactlySupportedSections k X.obj f B X.property F //
      Function.Injective φ ∧
      ∀ s, (F'.obj.map ((SmallEtale.finalIsTerminal B X'.obj X'.property).from
            ((smallEtaleBaseChange B j).obj (SmallEtale.final B X.obj X.property))).op s.1 =
          (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
              (op (SmallEtale.final B X.obj X.property)) (φ s).1) ∧
        (supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) (φ s).1 =
          (B.inclusion.map j).base ''
            supportSection B X'.obj X'.property F'
              (SmallEtale.final B X'.obj X'.property) s.1)} := by
  classical
  letI : LocallyOfFiniteType (B.inclusion.map j) :=
    locallyOfFiniteType_of_comp (B.inclusion.map j) f
  letI : LocallyOfFiniteType (B.inclusion.map (j ≫ 𝟙 X)) := by
    change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map (𝟙 X))
    infer_instance
  let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)).obj F
  let U := SmallEtale.final B X.obj X.property
  let e := baseChangeFinalIso B (j ≫ 𝟙 X)
  let srcIso := F'.obj.mapIso e.symm.op
  let sourcePackage := fShriekSubsheaf B (j ≫ 𝟙 X) F'
  let source := sourcePackage.val
  let targetPackage := fShriekSubsheaf B (𝟙 X) F
  let target := targetPackage.val
  let ext := openInclusionShriekMap B j (𝟙 X) F
  let extMap := ext.val
  let pushIso := pushforwardFinalSectionsIso B (𝟙 X) F
  let sourceAmbientIso := pushforwardFinalSectionsIso B (j ≫ 𝟙 X) F'
  have hproper (s : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property
      F') : properSupportSections B (j ≫ 𝟙 X) F' U (srcIso.inv s.1) :=
    properSupportSections_compactSection k B j f F s
  have hsourceAmbient (s : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B
      X'.property F') : sourceAmbientIso.hom s.1 = F'.obj.map e.hom.op s.1 := rfl
  have hpre (s : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property F') :
      ∃ a : source.obj.left.obj.obj (op U),
        source.arrow.hom.app (op U) a = sourceAmbientIso.hom s.1 :=
    (sourcePackage.property U (sourceAmbientIso.hom s.1)).2 (hproper s)
  let lift (s : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property F') :
      source.obj.left.obj.obj (op U) := Classical.choose (hpre s)
  have lift_spec (s : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property
      F') : source.arrow.hom.app (op U) (lift s) = sourceAmbientIso.hom s.1 :=
    Classical.choose_spec (hpre s)
  have hinjSource : Function.Injective (source.arrow.hom.app (op U)) :=
    mono_app_injective source.arrow (op U)
  let liftHom : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property F' →+
      source.obj.left.obj.obj (op U) :=
    { toFun := lift
      map_zero' := by
        apply hinjSource
        rw [lift_spec]
        change (ConcreteCategory.hom sourceAmbientIso.hom) 0 =
          (ConcreteCategory.hom (source.arrow.hom.app (op U))) 0
        simp
      map_add' s t := by
        apply hinjSource
        rw [lift_spec (s + t),
          map_add (ConcreteCategory.hom (source.arrow.hom.app (op U))) (lift s) (lift t),
          lift_spec s, lift_spec t]
        exact map_add (ConcreteCategory.hom sourceAmbientIso.hom) s.1 t.1 }
  let raw : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property F' →+
      F.obj.obj (op U) :=
    { toFun := fun s => pushIso.inv.hom
        ((target.arrow.hom.app (op U)).hom ((extMap.hom.app (op U)).hom (liftHom s)))
      map_zero' := by simp only [map_zero]
      map_add' _ _ := by simp only [map_add] }
  have hsupport (s : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property
      F') : supportSection B X.obj X.property F U (raw s) =
        (B.inclusion.map j).base ''
          supportSection B X'.obj X'.property F' (SmallEtale.final B X'.obj X'.property) s.1 := by
    let eId := baseChangeFinalIso B (𝟙 X)
    let eComp := smallEtaleBaseChange_compIso B X' X X j (𝟙 X)
    let eA := asIso (eComp.val.hom.app U) ≪≫ e
    obtain ⟨-, hSupp⟩ := ext.property.2 U (lift s)
    have hTargetSec : (target.arrow.hom.app (op U)) ((extMap.hom.app (op U)) (lift s)) =
        F.obj.map eId.hom.op (raw s) := by
      change _ = pushIso.hom (pushIso.inv _)
      exact (pushIso.inv_hom_id_apply _).symm
    have hSourceSec : F'.obj.map (eComp.val.hom.app U).op
          ((source.arrow.hom.app (op U)) (lift s)) = F'.obj.map eA.hom.op s.1 := by
      rw [lift_spec, hsourceAmbient]
      simp [eA]
    have hTargetSupport' : supportSection B X.obj X.property F
          ((smallEtaleBaseChange B (𝟙 X)).obj U) (F.obj.map eId.hom.op (raw s)) =
        ((SmallEtale.toScheme B X.obj X.property).map eId.symm.hom).base ''
          supportSection B X.obj X.property F U (raw s) := by
      simpa using supportSection_map_inv B X.obj X.property F eId.symm (raw s)
    let sW := F'.obj.map (eComp.val.hom.app U).op ((source.arrow.hom.app (op U)) (lift s))
    have hSourceSupport := supportSection_map_inv B X'.obj X'.property F' eA sW
    rw [hTargetSec, hTargetSupport'] at hSupp
    have hSourceSupport' : supportSection B X'.obj X'.property F'
          (SmallEtale.final B X'.obj X'.property) s.1 =
        ((SmallEtale.toScheme B X'.obj X'.property).map eA.hom).base ''
          supportSection B X'.obj X'.property F'
            ((smallEtaleBaseChange B j).obj ((smallEtaleBaseChange B (𝟙 X)).obj U)) sW := by
      have hback : F'.obj.map eA.inv.op sW = s.1 := by
        change F'.obj.map eA.inv.op (F'.obj.map (eComp.val.hom.app U).op
          ((source.arrow.hom.app (op U)) (lift s))) = s.1
        rw [hSourceSec]
        exact (F'.obj.mapIso eA.symm.op).inv_hom_id_apply s.1
      rwa [hback] at hSourceSupport
    have hgeom : B.inclusion.map (pullback.fst
          (Over.hom ((smallEtaleBaseChange B (𝟙 X)).obj U).obj) j) ≫
        (SmallEtale.toScheme B X.obj X.property).map eId.hom =
          (SmallEtale.toScheme B X'.obj X'.property).map eA.hom ≫ B.inclusion.map j := by
      let A₀ := (smallEtaleBaseChange B (𝟙 X)).obj U
      let W := (smallEtaleBaseChange B (𝟙 X) ⋙ smallEtaleBaseChange B j).obj U
      have heId : eId.hom.hom.left = A₀.obj.hom := by
        have h := Over.w eId.hom.hom
        change eId.hom.hom.left ≫ 𝟙 _ = A₀.obj.hom at h
        simpa only [Category.comp_id] using h
      have heA : eA.hom.hom.left = W.obj.hom := by
        have h := Over.w eA.hom.hom
        change eA.hom.hom.left ≫ 𝟙 _ = W.obj.hom at h
        simpa only [Category.comp_id] using h
      change B.inclusion.map (pullback.fst A₀.obj.hom j) ≫
          B.inclusion.map eId.hom.hom.left =
        B.inclusion.map eA.hom.hom.left ≫ B.inclusion.map j
      rw [heId, heA]
      have hc := congrArg B.inclusion.map
        (pullback.condition (f := A₀.obj.hom) (g := j))
      rwa [B.inclusion.map_comp, B.inclusion.map_comp] at hc
    let q := (SmallEtale.toScheme B X.obj X.property).mapIso eId
    let r := (SmallEtale.toScheme B X'.obj X'.property).mapIso eA
    let p := B.inclusion.map (pullback.fst
      (Over.hom ((smallEtaleBaseChange B (𝟙 X)).obj U).obj) j)
    have hcancel (y : (SmallEtale.toScheme B X.obj X.property).obj U) :
        q.hom.base (q.inv.base y) = y :=
      congrArg (fun g => g.base y) q.inv_hom_id
    have hpoint (z : (SmallEtale.toScheme B X'.obj X'.property).obj
        ((smallEtaleBaseChange B j).obj ((smallEtaleBaseChange B (𝟙 X)).obj U))) :
        q.hom.base (p.base z) = (B.inclusion.map j).base (r.hom.base z) :=
      congrArg (fun g => g.base z) hgeom
    ext y
    refine ⟨fun hy => ?_, ?_⟩
    · have hy' : q.inv.base y ∈ q.inv.base ''
          supportSection B X.obj X.property F U (raw s) := ⟨y, hy, rfl⟩
      obtain ⟨z, hz, he⟩ : q.inv.base y ∈ p.base ''
          supportSection B X'.obj X'.property F'
            ((smallEtaleBaseChange B j).obj ((smallEtaleBaseChange B (𝟙 X)).obj U)) sW :=
        hSupp ▸ hy'
      refine ⟨r.hom.base z, hSourceSupport'.symm ▸ ⟨z, hz, rfl⟩, ?_⟩
      exact (hpoint z).symm.trans ((congrArg q.hom.base he).trans (hcancel y))
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ r.hom.base ''
          supportSection B X'.obj X'.property F'
            ((smallEtaleBaseChange B j).obj ((smallEtaleBaseChange B (𝟙 X)).obj U)) sW :=
        hSourceSupport' ▸ hx
      obtain ⟨z, hz, rfl⟩ := hx'
      have hz' : p.base z ∈ q.inv.base ''
          supportSection B X.obj X.property F U (raw s) := hSupp.symm ▸ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, he⟩ := hz'
      have he' : y = (B.inclusion.map j).base (r.hom.base z) :=
        (hcancel y).symm.trans ((congrArg q.hom.base he).trans (hpoint z))
      exact he' ▸ hy
  let φ : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property F' →+
      compactlySupportedSections k X.obj f B X.property F :=
    { toFun := fun s => ⟨raw s, by
        have hs : IsProperOver (B.inclusion.map j ≫ f)
            (zeroOpen B X'.obj X'.property F'
              (SmallEtale.final B X'.obj X'.property) s.1).compl :=
          (mem_compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property
            F' s.1).mp s.2
        have hi := isProperOver_image (B.inclusion.map j ≫ f) f (B.inclusion.map j) rfl
          (zeroOpen B X'.obj X'.property F'
            (SmallEtale.final B X'.obj X'.property) s.1).compl hs
        rw [mem_compactlySupportedSections]
        refine isProperOver_of_le f (le_of_eq ?_) hi
        exact Closeds.ext (hsupport s)⟩
      map_zero' := Subtype.ext raw.map_zero
      map_add' := fun s t => Subtype.ext (raw.map_add s t) }
  refine ⟨φ, ?_, ?_⟩
  · intro s t hst
    apply Subtype.ext
    have htarget : Function.Injective (target.arrow.hom.app (op U)) :=
      mono_app_injective target.arrow (op U)
    have hext : Function.Injective (extMap.hom.app (op U)) := by
      have : Mono extMap := ext.property.1
      exact mono_app_injective extMap (op U)
    have hraw : raw s = raw t := congrArg Subtype.val hst
    have htargetEq : target.arrow.hom.app (op U) (extMap.hom.app (op U) (lift s)) =
        target.arrow.hom.app (op U) (extMap.hom.app (op U) (lift t)) := by
      change pushIso.inv (target.arrow.hom.app (op U) (extMap.hom.app (op U) (lift s))) =
        pushIso.inv (target.arrow.hom.app (op U) (extMap.hom.app (op U) (lift t))) at hraw
      simpa using congrArg pushIso.hom hraw
    have hinjSrcIso : Function.Injective srcIso.inv := fun x y h => by
      simpa using congrArg srcIso.hom h
    refine hinjSrcIso ?_
    have hAmb : sourceAmbientIso.hom s.1 = sourceAmbientIso.hom t.1 := by
      rw [← lift_spec s, ← lift_spec t, hext (htarget htargetEq)]
    rwa [hsourceAmbient s, hsourceAmbient t] at hAmb
  · intro s
    refine ⟨?_, hsupport s⟩
    obtain ⟨hrest, -⟩ := ext.property.2 U (lift s)
    let eId := baseChangeFinalIso B (𝟙 X)
    let η := ((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).unit.app F
    let r := (SmallEtale.finalIsTerminal B X'.obj X'.property).from
      ((smallEtaleBaseChange B j).obj U)
    let c := (smallEtaleBaseChange_compIso B X' X X j (𝟙 X)).val
    have hm : c.hom.app U ≫ e.hom = (smallEtaleBaseChange B j).map eId.hom ≫ r :=
      (SmallEtale.finalIsTerminal B X'.obj X'.property).hom_ext _ _
    have ht : target.arrow.hom.app (op U) (extMap.hom.app (op U) (lift s)) =
        F.obj.map eId.hom.op (raw s) := by
      change _ = pushIso.hom (pushIso.inv _)
      exact (pushIso.inv_hom_id_apply _).symm
    change F'.obj.map (c.hom.app U).op (source.arrow.hom.app (op U) (lift s)) =
      η.hom.app (op ((smallEtaleBaseChange B (𝟙 X)).obj U))
        (target.arrow.hom.app (op U) (extMap.hom.app (op U) (lift s))) at hrest
    rw [lift_spec, hsourceAmbient, ht] at hrest
    have hn := congrArg (fun h => h (raw s)) (η.hom.naturality eId.hom.op)
    change η.hom.app _ (F.obj.map eId.hom.op (raw s)) =
      F'.obj.map ((smallEtaleBaseChange B j).map eId.hom).op
        (η.hom.app (op U) (raw s)) at hn
    rw [hn] at hrest
    have hscomp : F'.obj.map (c.hom.app U).op (F'.obj.map e.hom.op s.1) =
        F'.obj.map ((smallEtaleBaseChange B j).map eId.hom).op (F'.obj.map r.op s.1) := by
      have hh := congrArg (fun a => F'.obj.map a.op) hm
      simpa only [op_comp, Functor.map_comp, AddCommGrpCat.comp_apply] using
        congrArg (fun a => a s.1) hh
    rw [hscomp] at hrest
    exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance hrest

/-- **Stacks 0F74.** Extension by zero gives a canonical injection on compactly supported
sections along an open immersion, characterised by the restriction of its value back to the
open subscheme and by the equality of supports. -/
@[stacks 0F74 "canonical injection"]
public noncomputable def compactlySupportedSections_openInclusion {X' X : B.Scheme}
    (j : X' ⟶ X) (f : X.obj ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    letI : LocallyOfFiniteType (B.inclusion.map j ≫ f) := inferInstance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    {φ : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property F' →+
        compactlySupportedSections k X.obj f B X.property F //
      Function.Injective φ ∧
      ∀ s, (F'.obj.map ((SmallEtale.finalIsTerminal B X'.obj X'.property).from
            ((smallEtaleBaseChange B j).obj (SmallEtale.final B X.obj X.property))).op s.1 =
          (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
              (op (SmallEtale.final B X.obj X.property)) (φ s).1) ∧
        (supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) (φ s).1 =
          (B.inclusion.map j).base ''
            supportSection B X'.obj X'.property F'
              (SmallEtale.final B X'.obj X'.property) s.1)} :=
  Classical.choice (by exact ⟨compactlySupportedSectionsOpenInclusionData k B j f F⟩)

end ProperSupport

section Precosheaf

variable (k : Type u) [Field k] (B : BigEtaleSite.{u})

/-- **Stacks 0F74.** For the identity open immersion extension by zero is surjective on
compactly supported sections, hence an isomorphism: the unit of the restriction adjunction
along an identity is an isomorphism, and the characterising restriction equation identifies the
injection with it. -/
@[stacks 0F74 "precosheaf identity"]
public theorem compactlySupportedSections_openInclusion_id (X : B.Scheme)
    (f : X.obj ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    Function.Surjective (compactlySupportedSections_openInclusion k B (𝟙 X) f F).1 := by
  let J := SmallEtale.topology B X.obj X.property
  let Q := smallEtaleBaseChange B (𝟙 X)
  let L := Q.sheafPullback AddCommGrpCat.{v} J J
  let R := Q.sheafPushforwardContinuous AddCommGrpCat.{v} J J
  let adj := Q.sheafAdjunctionContinuous AddCommGrpCat.{v} J J
  let er := Functor.sheafPushforwardContinuousId' (smallEtaleBaseChange_idIso B X)
    AddCommGrpCat.{v} J
  have : R.IsEquivalence := Functor.isEquivalence_of_iso er.symm
  let eF : F ≅ L.obj F := asIso (adj.unit.app F) ≪≫ er.app (L.obj F)
  let U := SmallEtale.final B X.obj X.property
  intro s
  let tval := eF.hom.hom.app (op U) s.1
  have ht : tval ∈ compactlySupportedSections k X.obj (B.inclusion.map (𝟙 X) ≫ f) B X.property
      (L.obj F) := by
    rw [mem_compactlySupportedSections]
    have he := supportSection_sheafIso B X.obj X.property eF U s.1
    have hz : (zeroOpen B X.obj X.property (L.obj F) U tval).compl =
        (zeroOpen B X.obj X.property F U s.1).compl := SetLike.coe_injective he
    rw [hz]
    simpa using (mem_compactlySupportedSections k X.obj f B X.property F s.1).mp s.2
  refine ⟨⟨tval, ht⟩, ?_⟩
  apply Subtype.ext
  have h := ((compactlySupportedSections_openInclusion k B (𝟙 X) f F).property.2
    ⟨tval, ht⟩).1
  have he : (SmallEtale.finalIsTerminal B X.obj X.property).from (Q.obj U) =
      (smallEtaleBaseChange_idIso B X).hom.app U :=
    (SmallEtale.finalIsTerminal B X.obj X.property).hom_ext _ _
  conv at h => lhs; rw [he]
  have hh : (L.obj F).obj.map ((smallEtaleBaseChange_idIso B X).hom.app U).op tval =
      (adj.unit.app F).hom.app (op U) s.1 := by
    change (L.obj F).obj.map ((smallEtaleBaseChange_idIso B X).hom.app U).op
      ((er.hom.app (L.obj F)).hom.app (op U) ((adj.unit.app F).hom.app (op U) s.1)) = _
    rw [Functor.sheafPushforwardContinuousId'_hom_app_hom_app]
    exact ((L.obj F).obj.mapIso ((smallEtaleBaseChange_idIso B X).app U).op).inv_hom_id_apply _
  rw [hh] at h
  have : IsIso ((adj.unit.app F).hom.app (op U)) := by
    change IsIso (((sheafToPresheaf J AddCommGrpCat).map (adj.unit.app F)).app (op U))
    infer_instance
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance h.symm

/-- Two global sections supported inside an open subscheme with the same image under the unit of
the restriction adjunction to that open subscheme are equal. -/
private theorem eq_of_unit_eq_of_supportSection_subset {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (a b : F.obj.obj (op (SmallEtale.final B X.obj X.property)))
    (ha : supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) a ⊆
      Set.range (B.inclusion.map j).base)
    (hb : supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) b ⊆
      Set.range (B.inclusion.map j).base)
    (hab : (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
            (op (SmallEtale.final B X.obj X.property)) a =
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
            (op (SmallEtale.final B X.obj X.property)) b) : a = b := by
  let U := SmallEtale.final B X.obj X.property
  let Q := smallEtaleBaseChange B j
  let adj := Q.sheafAdjunctionContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B X'.obj X'.property)
  let adj' := Adjunction.sheafPushforwardContinuous (openPostcomposeAdjunction B j)
    (SmallEtale.topology B X'.obj X'.property) (SmallEtale.topology B X.obj X.property)
    (E := AddCommGrpCat.{v})
  let e := adj.leftAdjointUniq adj'
  have hunit := congrArg (fun m => m.hom.app (op U))
    (Adjunction.unit_leftAdjointUniq_hom_app adj adj' F)
  let p := (openPostcomposeAdjunction B j).counit.app U
  have hres : F.obj.map p.op a = F.obj.map p.op b := by
    have h := congrArg (fun z => (e.hom.app F).hom.app (op (Q.obj U)) z) hab
    have hunit' (z : F.obj.obj (op U)) := congrArg (fun m => m z) hunit
    exact (hunit' a).symm.trans (h.trans (hunit' b))
  have hp : (SmallEtale.toScheme B X.obj X.property).map p =
      B.inclusion.map (pullback.fst U.obj.hom j) :=
    openPostcomposeAdjunction_counit_toScheme B j U
  have : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map p) := by
    rw [hp]
    have := hasPullbacks_bigEtaleSite B
    have := preservesPullbacks_bigEtaleSiteInclusion B
    exact MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback U.obj.hom j).map B.inclusion).flip
      (inferInstance : IsOpenImmersion (B.inclusion.map j))
  have hzero : F.obj.map p.op (a - b) = 0 := by
    change (F.obj.map p.op).hom (a - b) = 0
    rw [map_sub, hres, sub_self]
  have hvan := (map_eq_zero_iff_le_zeroOpen B X.obj X.property F U (a - b) _ p).mp hzero
  have hrange : Set.range ((SmallEtale.toScheme B X.obj X.property).map p).base =
      Set.range (B.inclusion.map j).base := by
    let e₀ := baseChangeFinalIso B j
    have hproj : (SmallEtale.toScheme B X'.obj X'.property).map e₀.hom ≫ B.inclusion.map j =
        (SmallEtale.toScheme B X.obj X.property).map p := by
      change B.inclusion.map (pullback.snd U.obj.hom j ≫ j) =
        B.inclusion.map (pullback.fst U.obj.hom j ≫ U.obj.hom)
      rw [pullback.condition]
    rw [← hproj]
    have : IsIso ((SmallEtale.toScheme B X'.obj X'.property).map e₀.hom) :=
      (SmallEtale.toScheme B X'.obj X'.property).map_isIso e₀.hom
    exact @scheme_range_comp_iso _ _ _ _ this _
  have hs : supportSection B X.obj X.property F U (a - b) ⊆
      Set.range (B.inclusion.map j).base := by
    rw [sub_eq_add_neg]
    refine (supportSection_add_subset B X.obj X.property F U a (-b)).trans
      (Set.union_subset ha ?_)
    rwa [supportSection_neg]
  have htop : zeroOpen B X.obj X.property F U (a - b) = ⊤ := by
    refine top_unique fun x _ => ?_
    by_contra h
    have hx : x ∈ Set.range ((SmallEtale.toScheme B X.obj X.property).map p).base := by
      rw [hrange]
      exact hs h
    exact h (hvan hx)
  have hz := (map_eq_zero_iff_le_zeroOpen B X.obj X.property F U (a - b) U (𝟙 U)).mpr
    (by simp [htop])
  exact sub_eq_zero.mp (by simpa using hz)

/-- **Stacks 0F74.** Extension by zero on compactly supported sections is transitive for
composable open immersions, once the two restrictions of the sheaf to the smallest open
subscheme are identified by the canonical comparison of inverse images. -/
@[stacks 0F74 "precosheaf composition"]
public theorem compactlySupportedSections_openInclusion_comp {X'' X' X : B.Scheme}
    (i : X'' ⟶ X') (j : X' ⟶ X) (f : X.obj ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f]
    [IsOpenImmersion (B.inclusion.map i)] [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    letI : IsOpenImmersion (B.inclusion.map (i ≫ j)) := by
      change IsOpenImmersion (B.inclusion.map i ≫ B.inclusion.map j)
      infer_instance
    letI : IsSeparated (B.inclusion.map j ≫ f) := by infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map j ≫ f) := by infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map i ≫ (B.inclusion.map j ≫ f)) := by
      infer_instance
    letI : LocallyOfFiniteType (B.inclusion.map (i ≫ j) ≫ f) := by
      change LocallyOfFiniteType (B.inclusion.map i ≫ B.inclusion.map j ≫ f)
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
    ∀ (s : compactlySupportedSections k X''.obj (B.inclusion.map i ≫ (B.inclusion.map j ≫ f))
        B X''.property F''),
      ∃ (t : compactlySupportedSections k X''.obj (B.inclusion.map (i ≫ j) ≫ f) B X''.property
        Fd),
        (((smallEtaleSheafPullbackCompIso B X'' X' X i j AddCommGrpCat.{v}).app F).hom.hom.app
            (op (SmallEtale.final B X''.obj X''.property)) s.1 = t.1) ∧
        ((compactlySupportedSections_openInclusion k B j f F).1
          ((compactlySupportedSections_openInclusion k B i (B.inclusion.map j ≫ f) F').1 s) =
          (compactlySupportedSections_openInclusion k B (i ≫ j) f F).1 t) := by
  have : IsOpenImmersion (B.inclusion.map (i ≫ j)) := by
    change IsOpenImmersion (B.inclusion.map i ≫ B.inclusion.map j)
    infer_instance
  dsimp only
  intro s
  let J := SmallEtale.topology B X.obj X.property
  let J' := SmallEtale.topology B X'.obj X'.property
  let J'' := SmallEtale.topology B X''.obj X''.property
  let Qj := smallEtaleBaseChange B j
  let Qi := smallEtaleBaseChange B i
  let Qd := smallEtaleBaseChange B (i ≫ j)
  let aj := Qj.sheafAdjunctionContinuous AddCommGrpCat.{v} J J'
  let ai := Qi.sheafAdjunctionContinuous AddCommGrpCat.{v} J' J''
  let ad := Qd.sheafAdjunctionContinuous AddCommGrpCat.{v} J J''
  let F' := (Qj.sheafPullback AddCommGrpCat.{v} J J').obj F
  let F'' := (Qi.sheafPullback AddCommGrpCat.{v} J' J'').obj F'
  let Fd := (Qd.sheafPullback AddCommGrpCat.{v} J J'').obj F
  let e := (smallEtaleSheafPullbackCompIso B X'' X' X i j AddCommGrpCat.{v}).app F
  let U := SmallEtale.final B X.obj X.property
  let V := SmallEtale.final B X'.obj X'.property
  let W := SmallEtale.final B X''.obj X''.property
  let tval := e.hom.hom.app (op W) s.1
  have ht : tval ∈ compactlySupportedSections k X''.obj (B.inclusion.map (i ≫ j) ≫ f) B
      X''.property Fd := by
    rw [mem_compactlySupportedSections]
    have he := supportSection_sheafIso B X''.obj X''.property e W s.1
    have hz : (zeroOpen B X''.obj X''.property Fd W tval).compl =
        (zeroOpen B X''.obj X''.property F'' W s.1).compl := SetLike.coe_injective he
    rw [hz]
    simpa only [Functor.map_comp, Category.assoc] using
      (mem_compactlySupportedSections k X''.obj
        (B.inclusion.map i ≫ (B.inclusion.map j ≫ f)) B X''.property F'' s.1).mp s.2
  let t : compactlySupportedSections k X''.obj (B.inclusion.map (i ≫ j) ≫ f) B X''.property Fd :=
    ⟨tval, ht⟩
  refine ⟨t, rfl, ?_⟩
  let sj := (compactlySupportedSections_openInclusion k B i (B.inclusion.map j ≫ f) F').val s
  let a := (compactlySupportedSections_openInclusion k B j f F).val sj
  let b := (compactlySupportedSections_openInclusion k B (i ≫ j) f F).val t
  apply Subtype.ext
  change a.1 = b.1
  have hi := (compactlySupportedSections_openInclusion k B i
    (B.inclusion.map j ≫ f) F').property.2 s
  have hj := (compactlySupportedSections_openInclusion k B j f F).property.2 sj
  have hd := (compactlySupportedSections_openInclusion k B (i ≫ j) f F).property.2 t
  refine eq_of_unit_eq_of_supportSection_subset B (i ≫ j) F a.1 b.1 ?_ ?_ ?_
  · change supportSection B X.obj X.property F U a.1 ⊆ _
    rw [hj.2, hi.2]
    rintro x ⟨y, ⟨z, _, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  · rw [hd.2]
    exact Set.image_subset_range _ _
  · let rj := (SmallEtale.finalIsTerminal B X'.obj X'.property).from (Qj.obj U)
    let ri := (SmallEtale.finalIsTerminal B X''.obj X''.property).from (Qi.obj V)
    let rd := (SmallEtale.finalIsTerminal B X''.obj X''.property).from (Qd.obj U)
    let c := (smallEtaleBaseChange_compIso B X'' X' X i j).val
    let er := Functor.sheafPushforwardContinuousComp' c AddCommGrpCat.{v} J J' J''
    have hu := congrArg (fun m => m.hom.app (op U))
      (CategoryTheory.unit_conjugateEquiv_symm ad (aj.comp ai) er.inv F)
    have hu' : Fd.obj.map (c.hom.app U).op ((ad.unit.app F).hom.app (op U) a.1) =
        e.hom.hom.app (op (Qi.obj (Qj.obj U)))
          ((ai.unit.app F').hom.app (op (Qj.obj U))
            ((aj.unit.app F).hom.app (op U) a.1)) := congrArg (fun m => m a.1) hu
    have hjr : (aj.unit.app F).hom.app (op U) a.1 = F'.obj.map rj.op sj.1 := hj.1.symm
    have hir : (ai.unit.app F').hom.app (op V) sj.1 = F''.obj.map ri.op s.1 := hi.1.symm
    have hn := congrArg (fun m => m sj.1) ((ai.unit.app F').hom.naturality rj.op)
    change (ai.unit.app F').hom.app (op (Qj.obj U)) (F'.obj.map rj.op sj.1) =
      F''.obj.map (Qi.map rj).op ((ai.unit.app F').hom.app (op V) sj.1) at hn
    rw [hjr, hn, hir] at hu'
    have hmaps : c.hom.app U ≫ rd = Qi.map rj ≫ ri :=
      (SmallEtale.finalIsTerminal B X''.obj X''.property).hom_ext _ _
    have heval : e.hom.hom.app (op (Qi.obj (Qj.obj U)))
        (F''.obj.map (Qi.map rj).op (F''.obj.map ri.op s.1)) =
        Fd.obj.map (c.hom.app U).op (Fd.obj.map rd.op t.1) := by
      have hh := congrArg (fun m => m s.1) (e.hom.hom.naturality (Qi.map rj ≫ ri).op)
      change e.hom.hom.app _ (F''.obj.map (Qi.map rj ≫ ri).op s.1) =
        Fd.obj.map (Qi.map rj ≫ ri).op t.1 at hh
      conv at hh => rhs; rw [← hmaps]
      simpa only [op_comp, Functor.map_comp, AddCommGrpCat.comp_apply] using hh
    rw [heval] at hu'
    exact ((AddCommGrpCat.mono_iff_injective (Fd.obj.map (c.hom.app U).op)).mp inferInstance
      hu').trans hd.1

end Precosheaf

section Cosheaf

variable (k : Type u) [Field k] (B : BigEtaleSite.{u})

/-- The counit of the post-composition adjunction is an open immersion of schemes: it is the
projection of the fibre product with the open subscheme. -/
private theorem isOpenImmersion_counit {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] (W : SmallEtale B X.obj X.property) :
    IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map
      ((openPostcomposeAdjunction B j).counit.app W)) := by
  rw [openPostcomposeAdjunction_counit_toScheme B j W]
  have := hasPullbacks_bigEtaleSite B
  have := preservesPullbacks_bigEtaleSiteInclusion B
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback W.obj.hom j).map B.inclusion).flip
    (inferInstance : IsOpenImmersion (B.inclusion.map j))

/-- The support of the unit of the restriction adjunction along an open immersion lies in the
inverse image of the support: the unit is, up to the comparison of the two descriptions of
restriction, the restriction of the section along the projection of the fibre product. -/
private theorem supportSection_unit_subset {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (W : SmallEtale B X.obj X.property) (t : F.obj.obj (op W)) :
    supportSection B X'.obj X'.property
        (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).obj F)
        ((smallEtaleBaseChange B j).obj W)
        ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) t) ⊆
      ((SmallEtale.toScheme B X.obj X.property).map
          ((openPostcomposeAdjunction B j).counit.app W)).base ⁻¹'
        supportSection B X.obj X.property F W t := by
  classical
  let J := SmallEtale.topology B X.obj X.property
  let J' := SmallEtale.topology B X'.obj X'.property
  let Q := smallEtaleBaseChange B j
  let adj := Q.sheafAdjunctionContinuous AddCommGrpCat.{v} J J'
  let adj' := Adjunction.sheafPushforwardContinuous (openPostcomposeAdjunction B j) J' J
    (E := AddCommGrpCat.{v})
  let PF := ((openPostcompose B j).sheafPushforwardContinuous AddCommGrpCat.{v} J' J).obj F
  let ι := adj'.leftAdjointUniq adj
  let p := (openPostcomposeAdjunction B j).counit.app W
  let g := (SmallEtale.toScheme B X.obj X.property).map p
  let _ : IsOpenImmersion g := isOpenImmersion_counit B j W
  have hunit : (ι.app F).hom.hom.app (op (Q.obj W)) (F.obj.map p.op t) =
      (adj.unit.app F).hom.app (op W) t :=
    congrArg (fun η => η.hom.app (op W) t)
      (Adjunction.unit_leftAdjointUniq_hom_app adj' adj F)
  have hsupp : supportSection B X'.obj X'.property (Q.sheafPullback AddCommGrpCat.{v} J J' |>.obj F)
        (Q.obj W) ((adj.unit.app F).hom.app (op W) t) =
      supportSection B X'.obj X'.property PF (Q.obj W) (F.obj.map p.op t) := by
    rw [← hunit]
    exact supportSection_sheafIso B X'.obj X'.property (ι.app F) (Q.obj W) (F.obj.map p.op t)
  rw [hsupp]
  let Oset : Set ((SmallEtale.toScheme B X'.obj X'.property).obj (Q.obj W)) :=
    g.base ⁻¹' (zeroOpen B X.obj X.property F W t :
      Set ((SmallEtale.toScheme B X.obj X.property).obj W))
  have hOopen : IsOpen Oset :=
    (zeroOpen B X.obj X.property F W t).isOpen.preimage g.continuous
  let O : ((SmallEtale.toScheme B X'.obj X'.property).obj (Q.obj W)).Opens := ⟨Oset, hOopen⟩
  let i := openObjectι B X'.obj X'.property (Q.obj W) O
  refine (supportSection_subset_iff_zero_on_open B X'.obj X'.property PF i _ ?_ _).mpr ?_
  · rw [openObjectι_range]
    change (O : Set ((SmallEtale.toScheme B X'.obj X'.property).obj (Q.obj W))) =
      (g.base ⁻¹' supportSection B X.obj X.property F W t)ᶜ
    rw [supportSection, Set.preimage_compl, compl_compl]
    rfl
  · change F.obj.map ((openPostcompose B j).map i).op (F.obj.map p.op t) = 0
    rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp]
    refine (map_eq_zero_iff_range_subset_zeroOpen B X.obj X.property F W t _
      ((openPostcompose B j).map i ≫ p)).mpr ?_
    rintro y ⟨z, rfl⟩
    have hmem : ((SmallEtale.toScheme B X'.obj X'.property).map
          (openObjectι B X'.obj X'.property (Q.obj W) O)).base z ∈
        Set.range ((SmallEtale.toScheme B X'.obj X'.property).map
          (openObjectι B X'.obj X'.property (Q.obj W) O)).base := Set.mem_range_self z
    rw [openObjectι_range] at hmem
    have hmemO : ((SmallEtale.toScheme B X'.obj X'.property).map i).base z ∈ Oset := hmem
    rw [Functor.map_comp]
    exact hmemO

/-- The restriction of a global section of `F` to an open subscheme, as a global section of the
restriction of `F` to that open subscheme. -/
private noncomputable def restrictGlobalSection {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (t : F.obj.obj (op (SmallEtale.final B X.obj X.property))) :
    (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).obj F).obj.obj
      (op (SmallEtale.final B X'.obj X'.property)) :=
  (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F).obj.map
    (baseChangeFinalIso B j).inv.op
      ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
          (op (SmallEtale.final B X.obj X.property)) t)

/-- The support of the restriction of a global section to an open subscheme is contained in the
inverse image of the support. -/
private theorem supportSection_restrictGlobalSection {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (t : F.obj.obj (op (SmallEtale.final B X.obj X.property))) :
    supportSection B X'.obj X'.property
        (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).obj F)
        (SmallEtale.final B X'.obj X'.property) (restrictGlobalSection B j F t) ⊆
      (B.inclusion.map j).base ⁻¹'
        supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) t := by
  let U := SmallEtale.final B X.obj X.property
  let e₀ := baseChangeFinalIso B j
  let p := (openPostcomposeAdjunction B j).counit.app U
  have hproj : (SmallEtale.toScheme B X'.obj X'.property).map e₀.hom ≫ B.inclusion.map j =
      (SmallEtale.toScheme B X.obj X.property).map p := by
    change B.inclusion.map (pullback.snd U.obj.hom j ≫ j) =
      B.inclusion.map (pullback.fst U.obj.hom j ≫ U.obj.hom)
    rw [pullback.condition]
  have hmapinv : supportSection B X'.obj X'.property
        (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).obj F)
        (SmallEtale.final B X'.obj X'.property) (restrictGlobalSection B j F t) =
      ((SmallEtale.toScheme B X'.obj X'.property).map e₀.hom).base ''
        supportSection B X'.obj X'.property
          (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).obj F)
          ((smallEtaleBaseChange B j).obj U)
          ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op U) t) :=
    supportSection_map_inv B X'.obj X'.property _ e₀ _
  intro y hy
  rw [hmapinv] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxg := supportSection_unit_subset B j F U t hx
  have hpt : ((SmallEtale.toScheme B X.obj X.property).map p).base x =
      (B.inclusion.map j).base
        (((SmallEtale.toScheme B X'.obj X'.property).map e₀.hom).base x) :=
    (congrArg (fun m => m.base x) hproj).symm
  change (B.inclusion.map j).base
    (((SmallEtale.toScheme B X'.obj X'.property).map e₀.hom).base x) ∈
      supportSection B X.obj X.property F U t
  rw [← hpt]
  exact hxg

/-- **Stacks 0F74.** A compactly supported section of `F` is the extension by zero of a
compactly supported section on an open subscheme exactly when its support lies in that open
subscheme: this identifies the image of the canonical injection. -/
@[stacks 0F74 "cosheaf, image of the canonical injection"]
public theorem exists_compactlySupportedSections_openInclusion_eq {X' X : B.Scheme}
    (j : X' ⟶ X) (f : X.obj ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (t : compactlySupportedSections k X.obj f B X.property F) :
    letI : LocallyOfFiniteType (B.inclusion.map j ≫ f) := inferInstance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    (∃ s : compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property F',
        (compactlySupportedSections_openInclusion k B j f F).1 s = t) ↔
      supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) t.1 ⊆
        Set.range (B.inclusion.map j).base := by
  have : LocallyOfFiniteType (B.inclusion.map j ≫ f) := inferInstance
  dsimp only
  constructor
  · rintro ⟨s, rfl⟩
    rw [((compactlySupportedSections_openInclusion k B j f F).property.2 s).2]
    exact Set.image_subset_range _ _
  · intro hsub
    have hsupp := supportSection_restrictGlobalSection B j F t.1
    have hpre := isProperOver_preimage_of_subset_range (B.inclusion.map j) f
      (zeroOpen B X.obj X.property F (SmallEtale.final B X.obj X.property) t.1).compl t.2 hsub
    have hmem : restrictGlobalSection B j F t.1 ∈
        compactlySupportedSections k X'.obj (B.inclusion.map j ≫ f) B X'.property
          (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).obj F) := by
      rw [mem_compactlySupportedSections]
      exact isProperOver_of_le (B.inclusion.map j ≫ f) (fun x hx => hsupp hx) hpre
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    refine eq_of_unit_eq_of_supportSection_subset B j F _ t.1 ?_ hsub ?_
    · rw [((compactlySupportedSections_openInclusion k B j f F).property.2 ⟨_, hmem⟩).2]
      exact Set.image_subset_range _ _
    · have hr : (SmallEtale.finalIsTerminal B X'.obj X'.property).from
          ((smallEtaleBaseChange B j).obj (SmallEtale.final B X.obj X.property)) =
            (baseChangeFinalIso B j).hom :=
        (SmallEtale.finalIsTerminal B X'.obj X'.property).hom_ext _ _
      have h1 := ((compactlySupportedSections_openInclusion k B j f F).property.2 ⟨_, hmem⟩).1
      refine h1.symm.trans (Eq.trans ?_ (((((smallEtaleBaseChange B j).sheafPullback
        AddCommGrpCat.{v} (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).obj F).obj.mapIso
          (baseChangeFinalIso B j).symm.op).hom_inv_id_apply _))
      exact congrArg (fun m => (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).obj F).obj.map m.op
          (restrictGlobalSection B j F t.1)) hr

/-- The image of the fibre product of two open subschemes of `X` is the intersection of their
images: the fibre product is their intersection as an open subscheme of `X`. -/
public theorem range_pullback_fst_comp {X₁ X₂ X : B.Scheme} (j₁ : X₁ ⟶ X) (j₂ : X₂ ⟶ X)
    [IsOpenImmersion (B.inclusion.map j₁)] [IsOpenImmersion (B.inclusion.map j₂)] :
    Set.range (B.inclusion.map (pullback.fst j₁ j₂ ≫ j₁)).base =
      Set.range (B.inclusion.map j₁).base ∩ Set.range (B.inclusion.map j₂).base := by
  have hpb := (IsPullback.of_hasPullback j₁ j₂).map B.inclusion
  rw [B.inclusion.map_comp]
  calc Set.range (B.inclusion.map (pullback.fst j₁ j₂) ≫ B.inclusion.map j₁).base
      = Set.range ((hpb.isoPullback.hom ≫
          pullback.fst (B.inclusion.map j₁) (B.inclusion.map j₂)) ≫ B.inclusion.map j₁).base := by
        rw [hpb.isoPullback_hom_fst]
    _ = Set.range (pullback.fst (B.inclusion.map j₁) (B.inclusion.map j₂) ≫
          B.inclusion.map j₁).base := by
        rw [Category.assoc]
        exact scheme_range_comp_iso hpb.isoPullback.hom _
    _ = (B.inclusion.map j₁).base ''
          Set.range (pullback.fst (B.inclusion.map j₁) (B.inclusion.map j₂)).base := by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    _ = (B.inclusion.map j₁).base ''
          ((B.inclusion.map j₁).base ⁻¹' Set.range (B.inclusion.map j₂).base) := by
        rw [Scheme.Pullback.range_fst]
    _ = Set.range (B.inclusion.map j₂).base ∩ Set.range (B.inclusion.map j₁).base :=
        Set.image_preimage_eq_inter_range
    _ = _ := Set.inter_comm _ _

/-- **Stacks 0F74.** Mayer–Vietoris for compactly supported sections: two compactly supported
sections on open subschemes with the same extension by zero both come from a compactly
supported section on the intersection of the two open subschemes, an open subscheme `X₀` whose
image is the intersection of the two images — for instance their fibre product, by
`AlgebraicGeometry.SmallEtale.range_pullback_fst_comp`. -/
@[stacks 0F74 "cosheaf, Mayer–Vietoris"]
public theorem exists_compactlySupportedSections_openInclusion_inter {X₀ X₁ X₂ X : B.Scheme}
    (j₀ : X₀ ⟶ X) (j₁ : X₁ ⟶ X) (j₂ : X₂ ⟶ X) (f : X.obj ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [IsOpenImmersion (B.inclusion.map j₀)]
    [IsOpenImmersion (B.inclusion.map j₁)] [IsOpenImmersion (B.inclusion.map j₂)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (h₀ : Set.range (B.inclusion.map j₀).base =
      Set.range (B.inclusion.map j₁).base ∩ Set.range (B.inclusion.map j₂).base) :
    ∀ (s₁ : compactlySupportedSections k X₁.obj (B.inclusion.map j₁ ≫ f) B X₁.property
        (((smallEtaleBaseChange B j₁).sheafPullback AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X₁.obj X₁.property)).obj F))
      (s₂ : compactlySupportedSections k X₂.obj (B.inclusion.map j₂ ≫ f) B X₂.property
        (((smallEtaleBaseChange B j₂).sheafPullback AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X₂.obj X₂.property)).obj F)),
      (compactlySupportedSections_openInclusion k B j₁ f F).1 s₁ =
          (compactlySupportedSections_openInclusion k B j₂ f F).1 s₂ →
        ∃ s₀ : compactlySupportedSections k X₀.obj (B.inclusion.map j₀ ≫ f) B X₀.property
            (((smallEtaleBaseChange B j₀).sheafPullback AddCommGrpCat.{v}
              (SmallEtale.topology B X.obj X.property)
              (SmallEtale.topology B X₀.obj X₀.property)).obj F),
          (compactlySupportedSections_openInclusion k B j₀ f F).1 s₀ =
            (compactlySupportedSections_openInclusion k B j₁ f F).1 s₁ := by
  intro s₁ s₂ hs
  have h1 := ((compactlySupportedSections_openInclusion k B j₁ f F).property.2 s₁).2
  have h2 := ((compactlySupportedSections_openInclusion k B j₂ f F).property.2 s₂).2
  have hcomb := h1.symm.trans ((congrArg
    (fun z : compactlySupportedSections k X.obj f B X.property F =>
      supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) z.1) hs).trans h2)
  have hsupp : supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property)
      ((compactlySupportedSections_openInclusion k B j₁ f F).1 s₁).1 ⊆
        Set.range (B.inclusion.map j₀).base := by
    rw [h1]
    exact Set.Subset.trans (Set.subset_inter (Set.image_subset_range _ _)
      (hcomb.subset.trans (Set.image_subset_range _ _))) h₀.symm.subset
  exact (exists_compactlySupportedSections_openInclusion_eq k B j₀ f F _).mpr hsupp

/-- A global section whose support is the union of two disjoint closed subsets, the second one
the complement of the image of an open immersion `φ` of the site, is the sum of a section
supported in the first and a section supported in the second: the first summand is the
extension by zero of the restriction along `φ`, which is supported on the inverse image of the
first subset, given here as a closed subscheme `i`. -/
private theorem exists_eq_add_of_supportSection_union {X : B.Scheme}
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (W : SmallEtale B X.obj X.property) (φ : W ⟶ SmallEtale.final B X.obj X.property)
    [IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map φ)]
    {Zs : Scheme.{u}} (i : Zs ⟶ (SmallEtale.toScheme B X.obj X.property).obj W)
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B X.obj X.property).map φ)]
    (s : F.obj.obj (op (SmallEtale.final B X.obj X.property)))
    (Z₁ Z₂ : Set ((SmallEtale.toScheme B X.obj X.property).obj
      (SmallEtale.final B X.obj X.property)))
    (hZ₁ : IsClosed Z₁) (hdisj : Disjoint Z₁ Z₂)
    (hrange : Set.range ((SmallEtale.toScheme B X.obj X.property).map φ).base = Z₂ᶜ)
    (hi : Set.range i.base = ((SmallEtale.toScheme B X.obj X.property).map φ).base ⁻¹' Z₁)
    (hsupp : supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) s =
      Z₁ ∪ Z₂) :
    ∃ s₁ : F.obj.obj (op (SmallEtale.final B X.obj X.property)),
      supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) s₁ ⊆ Z₁ ∧
        supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) (s - s₁) ⊆
          Z₂ := by
  let T := SmallEtale.toScheme B X.obj X.property
  have hZ₁sub : Z₁ ⊆ Set.range (T.map φ).base := by
    rw [hrange]
    exact fun _ hx => Set.disjoint_left.mp hdisj hx
  have hstepA : supportSection B X.obj X.property F W (F.obj.map φ.op s) ⊆ Set.range i.base := by
    rw [hi]
    let Oset : Set (T.obj W) := (T.map φ).base ⁻¹' (Z₁ᶜ : Set (T.obj (SmallEtale.final B X.obj
      X.property)))
    have hOopen : IsOpen Oset := hZ₁.isOpen_compl.preimage (T.map φ).continuous
    let O : (T.obj W).Opens := ⟨Oset, hOopen⟩
    let i' := openObjectι B X.obj X.property W O
    refine (supportSection_subset_iff_zero_on_open B X.obj X.property F i' _ ?_ _).mpr ?_
    · rw [openObjectι_range]
      change (T.map φ).base ⁻¹' (Z₁ᶜ : Set (T.obj (SmallEtale.final B X.obj X.property))) =
        ((T.map φ).base ⁻¹' Z₁)ᶜ
      rw [Set.preimage_compl]
    · rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp]
      refine (map_eq_zero_iff_range_subset_zeroOpen B X.obj X.property F
        (SmallEtale.final B X.obj X.property) s _ (i' ≫ φ)).mpr ?_
      rintro y ⟨z, rfl⟩
      have hmem : (T.map (openObjectι B X.obj X.property W O)).base z ∈
          Set.range (T.map (openObjectι B X.obj X.property W O)).base := Set.mem_range_self z
      rw [openObjectι_range] at hmem
      have hx : (T.map i').base z ∈ Oset := hmem
      have hnot : (T.map φ).base ((T.map i').base z) ∉
          supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) s := by
        rw [hsupp]
        rintro (h | h)
        · exact hx h
        · exact (hrange ▸ Set.mem_range_self (f := (T.map φ).base) ((T.map i').base z)) h
      have heq : (T.map (i' ≫ φ)).base z = (T.map φ).base ((T.map i').base z) := by
        rw [Functor.map_comp]
        rfl
      rw [heq]
      exact not_not.mp hnot
  have hrangecomp : Set.range (i ≫ T.map φ).base = Z₁ := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hi,
      Set.image_preimage_eq_inter_range]
    exact Set.inter_eq_left.mpr hZ₁sub
  let e := supportedSectionsEquiv B X.obj X.property F (SmallEtale.final B X.obj X.property) W φ
    Zs i
  have hres : F.obj.map φ.op (e.symm ⟨F.obj.map φ.op s, hstepA⟩).val =
      F.obj.map φ.op s := by
    have hcond : Set.preimage (T.map (𝟙 W ≫ φ)).base (Set.range (i ≫ T.map φ).base) =
        Set.preimage (T.map (𝟙 W)).base (Set.range i.base) := by
      change Set.preimage (T.map φ).base (Set.range ((T.map φ).base ∘ i.base)) =
        Set.range i.base
      rw [Set.range_comp]
      exact Set.preimage_image_eq _ (T.map φ).isOpenEmbedding.injective
    have ht := supportedSectionsEquiv_restrict B X.obj X.property F
      (SmallEtale.final B X.obj X.property) W φ Zs i W (𝟙 W) hcond
      (e.symm ⟨F.obj.map φ.op s, hstepA⟩)
    have hE := congrArg Subtype.val (e.apply_symm_apply ⟨F.obj.map φ.op s, hstepA⟩)
    rw [hE] at ht
    simpa using ht.symm
  refine ⟨(e.symm ⟨F.obj.map φ.op s, hstepA⟩).val, ?_, ?_⟩
  · intro x hx
    have h := (e.symm ⟨F.obj.map φ.op s, hstepA⟩).property hx
    rwa [hrangecomp] at h
  · refine (supportSection_subset_iff_zero_on_open B X.obj X.property F φ Z₂ hrange _).mpr ?_
    change (F.obj.map φ.op).hom (s - (e.symm ⟨F.obj.map φ.op s, hstepA⟩).val) = 0
    rw [map_sub, hres, sub_self]

/-- **Stacks 0F74.** Gluing for compactly supported sections: a compactly supported section
whose support is the union of two disjoint closed subsets, one inside each of two open
subschemes, is the sum of the extensions by zero of compactly supported sections on those two
open subschemes. -/
@[stacks 0F74 "cosheaf, gluing"]
public theorem exists_compactlySupportedSections_openInclusion_add {X₁ X₂ X : B.Scheme}
    (j₁ : X₁ ⟶ X) (j₂ : X₂ ⟶ X) (f : X.obj ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f]
    [IsOpenImmersion (B.inclusion.map j₁)] [IsOpenImmersion (B.inclusion.map j₂)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (t : compactlySupportedSections k X.obj f B X.property F)
    (Z₁ Z₂ : Set ((SmallEtale.toScheme B X.obj X.property).obj
      (SmallEtale.final B X.obj X.property)))
    (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂) (hdisj : Disjoint Z₁ Z₂)
    (hsupp : supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) t.1 =
      Z₁ ∪ Z₂)
    (h₁ : Z₁ ⊆ Set.range (B.inclusion.map j₁).base)
    (h₂ : Z₂ ⊆ Set.range (B.inclusion.map j₂).base) :
    ∃ (s₁ : compactlySupportedSections k X₁.obj (B.inclusion.map j₁ ≫ f) B X₁.property
        (((smallEtaleBaseChange B j₁).sheafPullback AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X₁.obj X₁.property)).obj F))
      (s₂ : compactlySupportedSections k X₂.obj (B.inclusion.map j₂ ≫ f) B X₂.property
        (((smallEtaleBaseChange B j₂).sheafPullback AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X₂.obj X₂.property)).obj F)),
      (compactlySupportedSections_openInclusion k B j₁ f F).1 s₁ +
        (compactlySupportedSections_openInclusion k B j₂ f F).1 s₂ = t := by
  have hZ₁proper : IsProperOver f (⟨Z₁, hZ₁⟩ : Closeds
      ((SmallEtale.toScheme B X.obj X.property).obj
        (SmallEtale.final B X.obj X.property))) := by
    refine isProperOver_of_le f (fun x hx => ?_) t.2
    change x ∈ supportSection B X.obj X.property F (SmallEtale.final B X.obj X.property) t.1
    rw [hsupp]
    exact Or.inl hx
  have hlft : @LocallyOfFiniteType ((SmallEtale.toScheme B X.obj X.property).obj
      (SmallEtale.final B X.obj X.property)) _ f := (inferInstance : LocallyOfFiniteType f)
  have hsep : @IsSeparated ((SmallEtale.toScheme B X.obj X.property).obj
      (SmallEtale.final B X.obj X.property)) _ f := (inferInstance : IsSeparated f)
  have hZ₁sub : Z₁ ⊆ Set.range ((SmallEtale.toScheme B X.obj X.property).map
      (openObjectι B X.obj X.property (SmallEtale.final B X.obj X.property)
        ⟨Z₂ᶜ, hZ₂.isOpen_compl⟩)).base := by
    rw [openObjectι_range]
    exact fun _ hx => Set.disjoint_left.mp hdisj hx
  have hC₁closed : IsClosed (((SmallEtale.toScheme B X.obj X.property).map
      (openObjectι B X.obj X.property (SmallEtale.final B X.obj X.property)
        ⟨Z₂ᶜ, hZ₂.isOpen_compl⟩)).base ⁻¹' Z₁) :=
    hZ₁.preimage ((SmallEtale.toScheme B X.obj X.property).map
      (openObjectι B X.obj X.property (SmallEtale.final B X.obj X.property)
        ⟨Z₂ᶜ, hZ₂.isOpen_compl⟩)).continuous
  have hproper : IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (⟨_, hC₁closed⟩ : Closeds _)).subschemeι ≫ (SmallEtale.toScheme B X.obj X.property).map
      (openObjectι B X.obj X.property (SmallEtale.final B X.obj X.property)
        ⟨Z₂ᶜ, hZ₂.isOpen_compl⟩) ≫ f) :=
    isProperOver_preimage_of_subset_range ((SmallEtale.toScheme B X.obj X.property).map
      (openObjectι B X.obj X.property (SmallEtale.final B X.obj X.property)
        ⟨Z₂ᶜ, hZ₂.isOpen_compl⟩)) f ⟨Z₁, hZ₁⟩ hZ₁proper hZ₁sub
  have : IsClosedImmersion ((Scheme.IdealSheafData.vanishingIdeal
      (⟨_, hC₁closed⟩ : Closeds _)).subschemeι ≫ (SmallEtale.toScheme B X.obj X.property).map
      (openObjectι B X.obj X.property (SmallEtale.final B X.obj X.property)
        ⟨Z₂ᶜ, hZ₂.isOpen_compl⟩)) :=
    closedImmersion_of_proper_comp_separated _ ((SmallEtale.toScheme B X.obj X.property).map
      (openObjectι B X.obj X.property (SmallEtale.final B X.obj X.property)
        ⟨Z₂ᶜ, hZ₂.isOpen_compl⟩)) f hproper
  obtain ⟨u, hu₁, hu₂⟩ := exists_eq_add_of_supportSection_union B F
    (openObject B X.obj X.property (SmallEtale.final B X.obj X.property)
      ⟨Z₂ᶜ, hZ₂.isOpen_compl⟩)
    (openObjectι B X.obj X.property (SmallEtale.final B X.obj X.property)
      ⟨Z₂ᶜ, hZ₂.isOpen_compl⟩)
    (Scheme.IdealSheafData.vanishingIdeal (⟨_, hC₁closed⟩ : Closeds _)).subschemeι t.1 Z₁ Z₂
    hZ₁ hdisj (openObjectι_range B X.obj X.property (SmallEtale.final B X.obj X.property)
      ⟨Z₂ᶜ, hZ₂.isOpen_compl⟩)
    (by rw [Scheme.IdealSheafData.range_subschemeι]
        exact Scheme.IdealSheafData.coe_support_vanishingIdeal _) hsupp
  have hu₁mem : u ∈ compactlySupportedSections k X.obj f B X.property F := by
    rw [mem_compactlySupportedSections]
    exact isProperOver_of_le f (fun x hx => hu₁ hx) hZ₁proper
  obtain ⟨s₁, hs₁⟩ := (exists_compactlySupportedSections_openInclusion_eq k B j₁ f F
    ⟨u, hu₁mem⟩).mpr (fun x hx => h₁ (hu₁ hx))
  obtain ⟨s₂, hs₂⟩ := (exists_compactlySupportedSections_openInclusion_eq k B j₂ f F
    ⟨t.1 - u, sub_mem t.2 hu₁mem⟩).mpr (fun x hx => h₂ (hu₂ hx))
  refine ⟨s₁, s₂, ?_⟩
  rw [hs₁, hs₂]
  apply Subtype.ext
  change u + (t.1 - u) = t.1
  abel

end Cosheaf

end AlgebraicGeometry.SmallEtale

end
