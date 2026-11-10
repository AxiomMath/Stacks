module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LowerShriekSliceEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lower shriek of abelian sheaves commutes with localization

Let `u : C ⥤ D` be a continuous functor of sites, let `g : Sh(C) ⟶ Sh(D)` be the associated
morphism of topoi and let `U` be an object of `C`, with `V = u(U)`. Stacks 03EG localizes `u` at
`U`: the functor `u' = Over.post u : C/U ⥤ D/V` sits in a commutative square

```
  C/U --j_U--> C
   | u'         | u
   v            v
  D/V --j_V--> D
```

with the two localization functors. This file proves two consequences of that square used in
Stacks 0798. The first is the identity for lower shriek of abelian sheaves

`g_!^{Ab} j_{U!} = j_{V!} (g')^{Ab}_!`.

The second is that the extension by zero of a module along `j_U` has the extension by zero of the
underlying abelian sheaf as its underlying abelian sheaf: the comparison transformation of
Stacks 0798 is an isomorphism for the localization morphism `j_U`. For a general morphism of
ringed sites it is not, by `Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`.

## Main results

* `Stacks.SheafOfModules.abelianShriekOverIso`: the square of lower shriek functors on abelian
  sheaves, `j_{U!}` followed by `g_!^{Ab}` is `(g')^{Ab}_!` followed by `j_{V!}`.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_sliceEquivalence`: the comparison
  transformation of Stacks 0798 is an isomorphism whenever every slice functor of the functor of
  sites is an equivalence and the structure morphism of rings is the identity of `g^{-1} O_D`.
* `Stacks.SheafOfModules.lowerShriekForgetOverForgetIso`: forgetting the module structure commutes
  with extension by zero along `C/U ⥤ C`.
* `Stacks.SheafOfModules.homEquiv_comp_lowerShriekForgetComparison`: the composition law for the
  comparison transformation along a composite functor of sites.
* `Stacks.SheafOfModules.lowerShriekForgetComparison_localizedSquare`: the comparison
  transformation is compatible with the localized square, read in its two ways.
* `Stacks.SheafOfModules.localizedStructureSheafComparison`: the canonical map
  `(g')_!^{Ab} O_U ⟶ O_{u(U)}`.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_localizedStructureSheafComparison`:
  the two lower shrieks agree as soon as every `(g')_!^{Ab} O_U ⟶ O_{u(U)}` is an isomorphism.

## References

* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 03EG](https://stacks.math.columbia.edu/tag/03EG)
* [Stacks Project, Tag 04BG](https://stacks.math.columbia.edu/tag/04BG)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u r t u₁ u₂ u₃ v₁ v₂ v₃

namespace Stacks.SheafOfModules

section Square

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K] (U : C)
  [(Over.post u : Over U ⥤ Over (u.obj U)).IsContinuous (J.over U) (K.over (u.obj U))]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [((Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{w} (J.over U) J).IsRightAdjoint]
  [((Over.forget (u.obj U)).sheafPushforwardContinuous AddCommGrpCat.{w}
    (K.over (u.obj U)) K).IsRightAdjoint]
  [((Over.post u : Over U ⥤ Over (u.obj U)).sheafPushforwardContinuous AddCommGrpCat.{w}
    (J.over U) (K.over (u.obj U))).IsRightAdjoint]

/-- The two composite restriction functors of the localized square of Stacks 03EG agree. -/
def sheafPushforwardOverIso :
    (Over.forget (u.obj U)).sheafPushforwardContinuous AddCommGrpCat.{w}
          (K.over (u.obj U)) K ⋙
        (Over.post u : Over U ⥤ Over (u.obj U)).sheafPushforwardContinuous AddCommGrpCat.{w}
          (J.over U) (K.over (u.obj U)) ≅
      u.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
        (Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{w} (J.over U) J := by
  haveI : (Over.forget U ⋙ u).IsContinuous (J.over U) K :=
    Functor.isContinuous_comp (Over.forget U) u (J.over U) J K
  exact Functor.sheafPushforwardContinuousComp'
      (eqToIso (Over.post_forget_eq_forget_comp u U)) AddCommGrpCat.{w} (J.over U)
      (K.over (u.obj U)) K ≪≫
    (Functor.sheafPushforwardContinuousComp (Over.forget U) u AddCommGrpCat.{w}
      (J.over U) J K).symm

/-- Lower shriek of abelian sheaves commutes with localization: with `V = u(U)` and
`g' : Sh(C/U) ⟶ Sh(D/V)` the morphism of topoi induced by the localized functor `u' = Over.post u`
of Stacks 03EG,

`g_!^{Ab} ∘ j_{U!} ≅ j_{V!} ∘ (g')^{Ab}_!`. -/
@[stacks 0798 "`g_!^{Ab} j_{U!} = j_{u(U)!} (g')^{Ab}_!`, the consequence of the localized \
square of Stacks 03EG that the remark uses"]
def abelianShriekOverIso :
    (Over.forget U).sheafPullback AddCommGrpCat.{w} (J.over U) J ⋙
        u.sheafPullback AddCommGrpCat.{w} J K ≅
      (Over.post u : Over U ⥤ Over (u.obj U)).sheafPullback AddCommGrpCat.{w}
          (J.over U) (K.over (u.obj U)) ⋙
        (Over.forget (u.obj U)).sheafPullback AddCommGrpCat.{w} (K.over (u.obj U)) K :=
  (((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{w} (J.over U) J).comp
      (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)).leftAdjointUniq
    ((((Over.post u : Over U ⥤ Over (u.obj U)).sheafAdjunctionContinuous AddCommGrpCat.{w}
        (J.over U) (K.over (u.obj U))).comp
      ((Over.forget (u.obj U)).sheafAdjunctionContinuous AddCommGrpCat.{w}
        (K.over (u.obj U)) K)).ofNatIsoRight (sheafPushforwardOverIso J K u U))

end Square

/-- A morphism obtained as an adjoint transpose is an isomorphism exactly when the datum it
transposes is universal: `(adj.homEquiv X Y).symm α` is invertible if and only if every morphism
`X ⟶ G Z` factors uniquely through `α`. -/
theorem isIso_homEquiv_symm_iff {A : Type*} [Category A] {B : Type*} [Category B]
    {L : A ⥤ B} {G : B ⥤ A} (adj : L ⊣ G) {X : A} {Y : B} (α : X ⟶ G.obj Y) :
    IsIso ((adj.homEquiv X Y).symm α) ↔
      ∀ Z : B, Function.Bijective (fun (g : Y ⟶ Z) => α ≫ G.map g) := by
  rw [isIso_iff_coyoneda_map_bijective]
  refine forall_congr' fun Z => ?_
  have key : (fun (g : Y ⟶ Z) => α ≫ G.map g) =
      (adj.homEquiv X Z) ∘ (fun (g : Y ⟶ Z) => (adj.homEquiv X Y).symm α ≫ g) := by
    funext g
    simp only [Function.comp_apply, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
  rw [key, (adj.homEquiv X Z).bijective.of_comp_iff']

/-- Precomposition with the canonical map from a presheaf to its sheafification is bijective on
morphisms to a sheaf. -/
theorem bijective_toSheafify_comp {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{w}] (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (Z : Sheaf J AddCommGrpCat.{w}) :
    Function.Bijective
      (fun (h : CategoryTheory.sheafify J P ⟶ Z.obj) => CategoryTheory.toSheafify J P ≫ h) := by
  constructor
  · intro h₁ h₂ h
    exact CategoryTheory.sheafify_hom_ext J h₁ h₂ Z.property h
  · intro β
    exact ⟨CategoryTheory.sheafifyLift J β Z.property, by simp⟩

section SliceEquivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{u})
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(PresheafOfModules.pushforward.{w} (F := F) (𝟙 (F.op ⋙ R.obj))).IsRightAdjoint]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{w}, F.op.HasPointwiseLeftKanExtension G]
  [∀ x : C, (Over.post (X := x) F).IsEquivalence]

open Stacks.ModuleLowerShriek

/-- The left adjoint of restriction along `g : (C, g^{-1} O_D) ⟶ (D, O_D)` exists as soon as it
does for the identity of `F.op ⋙ O_D`. -/
instance isRightAdjoint_pushforward_structureMap_hom :
    (PresheafOfModules.pushforward.{w} (F := F) (structureMap J K F R).hom).IsRightAdjoint :=
  inferInstanceAs (PresheafOfModules.pushforward.{w} (F := F)
    (𝟙 (F.op ⋙ R.obj))).IsRightAdjoint

omit [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(PresheafOfModules.pushforward.{w} (F := F) (𝟙 (F.op ⋙ R.obj))).IsRightAdjoint] in
/-- The unit of the concrete lower-shriek adjunction on presheaves of modules is the unit of the
left Kan extension of the underlying abelian presheaf. -/
theorem moduleLanAdjunction_unit_app (M : PresheafOfModules.{w} (F.op ⋙ R.obj)) :
    (moduleLanAdjunction F R.obj).unit.app M = moduleLanUnit F R.obj M := by
  change moduleLanUnit F R.obj M ≫ (PresheafOfModules.pushforward _).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

omit [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The underlying abelian presheaf of lower shriek on presheaves of modules is the left Kan
extension of the underlying abelian presheaf, with the forgotten unit as its unit. -/
theorem isLeftKanExtension_toPresheaf_pullback (M : PresheafOfModules.{w} (F.op ⋙ R.obj)) :
    ((PresheafOfModules.toPresheaf R.obj).obj
        ((PresheafOfModules.pullback.{w} (F := F) (𝟙 (F.op ⋙ R.obj))).obj M)).IsLeftKanExtension
      ((PresheafOfModules.toPresheaf (F.op ⋙ R.obj)).map
        ((PresheafOfModules.pullbackPushforwardAdjunction.{w}
          (F := F) (𝟙 (F.op ⋙ R.obj))).unit.app M)) := by
  have inst : ((PresheafOfModules.toPresheaf R.obj).obj (moduleLan F R.obj M)).IsLeftKanExtension
      ((PresheafOfModules.toPresheaf (F.op ⋙ R.obj)).map (moduleLanUnit F R.obj M)) :=
    inferInstanceAs ((F.op.leftKanExtension M.presheaf).IsLeftKanExtension
      (F.op.leftKanExtensionUnit M.presheaf))
  refine (Functor.isLeftKanExtension_iff_of_iso
    ((PresheafOfModules.toPresheaf R.obj).mapIso
      ((Adjunction.leftAdjointUniq (moduleLanAdjunction F R.obj)
        (PresheafOfModules.pullbackPushforwardAdjunction.{w}
          (F := F) (𝟙 (F.op ⋙ R.obj)))).app M))
    ((PresheafOfModules.toPresheaf (F.op ⋙ R.obj)).map (moduleLanUnit F R.obj M)) _ ?_).mp inst
  have h := Adjunction.unit_leftAdjointUniq_hom_app (moduleLanAdjunction F R.obj)
    (PresheafOfModules.pullbackPushforwardAdjunction.{w} (F := F) (𝟙 (F.op ⋙ R.obj))) M
  rw [moduleLanAdjunction_unit_app] at h
  exact congrArg (PresheafOfModules.toPresheaf (F.op ⋙ R.obj)).map h

/-- The comparison transformation of Stacks 0798 is an isomorphism at every sheaf of modules
when every slice functor of the functor of sites is an equivalence and the structure morphism of
rings is the identity of `g^{-1} O_D`. -/
theorem isIso_lowerShriekForgetComparison_app_of_sliceEquivalence
    (M : SheafOfModules.{w} (inverseImageRing J K F R)) :
    IsIso ((lowerShriekForgetComparison.{u, w} F (structureMap J K F R)).app M) := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (SheafOfModules.pullbackPushforwardAdjunction.{w} (structureMap J K F R))
    (SheafOfModules.PullbackConstruction.adjunction.{w} (structureMap J K F R)) M
  have hu' : (SheafOfModules.PullbackConstruction.adjunction.{w}
          (structureMap J K F R)).unit.app M ≫
        (SheafOfModules.pushforward.{w} (structureMap J K F R)).map
          ((Adjunction.leftAdjointUniq
            (SheafOfModules.pullbackPushforwardAdjunction.{w} (structureMap J K F R))
            (SheafOfModules.PullbackConstruction.adjunction.{w}
              (structureMap J K F R))).inv.app M) =
      (SheafOfModules.pullbackPushforwardAdjunction.{w} (structureMap J K F R)).unit.app M := by
    rw [← hu]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have key : (SheafOfModules.toSheaf (inverseImageRing J K F R)).map
        ((SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap J K F R)).unit.app M) =
      (SheafOfModules.toSheaf (inverseImageRing J K F R)).map
          ((SheafOfModules.PullbackConstruction.adjunction.{w}
            (structureMap J K F R)).unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
          ((SheafOfModules.toSheaf R).map
            ((Adjunction.leftAdjointUniq
              (SheafOfModules.pullbackPushforwardAdjunction.{w} (structureMap J K F R))
              (SheafOfModules.PullbackConstruction.adjunction.{w}
                (structureMap J K F R))).inv.app M)) := by
    rw [← hu', CategoryTheory.Functor.map_comp]
    rfl
  have hc := Adjunction.homEquiv_naturality_right_symm
    (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)
    ((SheafOfModules.toSheaf (inverseImageRing J K F R)).map
      ((SheafOfModules.PullbackConstruction.adjunction.{w} (structureMap J K F R)).unit.app M))
    ((SheafOfModules.toSheaf R).map
      ((Adjunction.leftAdjointUniq
        (SheafOfModules.pullbackPushforwardAdjunction.{w} (structureMap J K F R))
        (SheafOfModules.PullbackConstruction.adjunction.{w}
          (structureMap J K F R))).inv.app M))
  simp only [CategoryTheory.Functor.id_obj] at hc
  have hfinal : (lowerShriekForgetComparison.{u, w} F (structureMap J K F R)).app M =
      (((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
          ((SheafOfModules.toSheaf (inverseImageRing J K F R)).obj M)
          ((SheafOfModules.toSheaf R).obj
            ((SheafOfModules.forget (inverseImageRing J K F R) ⋙
              PresheafOfModules.pullback.{w} (structureMap J K F R).hom ⋙
              PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).obj M))).symm
        ((SheafOfModules.toSheaf (inverseImageRing J K F R)).map
          ((SheafOfModules.PullbackConstruction.adjunction.{w}
            (structureMap J K F R)).unit.app M))) ≫
      (SheafOfModules.toSheaf R).map
        ((Adjunction.leftAdjointUniq
          (SheafOfModules.pullbackPushforwardAdjunction.{w} (structureMap J K F R))
          (SheafOfModules.PullbackConstruction.adjunction.{w}
            (structureMap J K F R))).inv.app M) :=
    (((Equiv.eq_symm_apply _).mpr
      (lowerShriekForgetComparison_homEquiv F (structureMap J K F R) M)).trans
        (congrArg (fun x => ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
          ((SheafOfModules.toSheaf (inverseImageRing J K F R)).obj M)
          ((SheafOfModules.toSheaf R).obj
            ((SheafOfModules.pullback.{w} (structureMap J K F R)).obj M))).symm x) key)).trans hc
  rw [hfinal]
  have main : IsIso (((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
      ((SheafOfModules.toSheaf (inverseImageRing J K F R)).obj M)
      ((SheafOfModules.toSheaf R).obj
        ((SheafOfModules.forget (inverseImageRing J K F R) ⋙
          PresheafOfModules.pullback.{w} (structureMap J K F R).hom ⋙
          PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).obj M))).symm
      ((SheafOfModules.toSheaf (inverseImageRing J K F R)).map
        ((SheafOfModules.PullbackConstruction.adjunction.{w}
          (structureMap J K F R)).unit.app M))) := by
    refine (isIso_homEquiv_symm_iff (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K) _).mpr ?_
    intro Z
    have hbij : Function.Bijective
        (fun (h : CategoryTheory.sheafify K
            ((PresheafOfModules.pullback.{w} (F := F) (𝟙 (F.op ⋙ R.obj))).obj M.val).presheaf ⟶
              Z.obj) =>
          (PresheafOfModules.toPresheaf (F.op ⋙ R.obj)).map
            (((SheafOfModules.PullbackConstruction.adjunction.{w}
              (structureMap J K F R)).unit.app M).val) ≫ Functor.whiskerLeft F.op h) := by
      have inst := isLeftKanExtension_toPresheaf_pullback K F R M.val
      have hlan := (Functor.homEquivOfIsLeftKanExtension
        ((PresheafOfModules.toPresheaf R.obj).obj
          ((PresheafOfModules.pullback.{w} (F := F) (𝟙 (F.op ⋙ R.obj))).obj M.val))
        ((PresheafOfModules.toPresheaf (F.op ⋙ R.obj)).map
          ((PresheafOfModules.pullbackPushforwardAdjunction.{w}
            (F := F) (𝟙 (F.op ⋙ R.obj))).unit.app M.val)) Z.obj).bijective
      have hsh := bijective_toSheafify_comp K
        ((PresheafOfModules.pullback.{w} (F := F) (𝟙 (F.op ⋙ R.obj))).obj M.val).presheaf Z
      exact hlan.comp hsh
    rw [← (((fullyFaithfulSheafToPresheaf J AddCommGrpCat.{w}).homEquiv
      (X := (SheafOfModules.toSheaf (inverseImageRing J K F R)).obj M)
      (Y := (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj Z)).bijective.of_comp_iff' _)]
    exact hbij.comp ((fullyFaithfulSheafToPresheaf K AddCommGrpCat.{w}).homEquiv
      (X := (SheafOfModules.toSheaf R).obj
        ((SheafOfModules.forget (inverseImageRing J K F R) ⋙
          PresheafOfModules.pullback.{w} (structureMap J K F R).hom ⋙
          PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).obj M))
      (Y := Z)).bijective
  have := main
  infer_instance

/-- The comparison transformation of Stacks 0798 is an isomorphism of functors when every slice
functor of the functor of sites is an equivalence and the structure morphism of rings is the
identity of `g^{-1} O_D`. -/
theorem isIso_lowerShriekForgetComparison_of_sliceEquivalence :
    IsIso (lowerShriekForgetComparison.{u, w} F (structureMap J K F R)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun M => isIso_lowerShriekForgetComparison_app_of_sliceEquivalence J K F R M

end SliceEquivalence

section Localization

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})
  (U : C)
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(PresheafOfModules.pushforward.{w} (F := Over.forget U)
    (𝟙 ((Over.forget U).op ⋙ R.obj))).IsRightAdjoint]
  [∀ G : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w}, (Over.forget U).op.HasPointwiseLeftKanExtension G]

omit [∀ G : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w}, (Over.forget U).op.HasPointwiseLeftKanExtension G] in
/-- Every slice functor of a localization functor `C/U ⥤ C` is an equivalence. -/
theorem isEquivalence_overPost_overForget (x : Over U) :
    (Over.post (X := x) (Over.forget U)).IsEquivalence := by
  have h : Over.post (X := x) (Over.forget U) = Over.iteratedSliceForward x := rfl
  rw [h]
  exact (Over.iteratedSliceEquiv x).isEquivalence_functor

/-- For an object `U` of a site `C` with a sheaf of rings `O`, the underlying abelian sheaf of
`j_{U!} M` is `j_{U!}^{Ab}` of the underlying abelian sheaf of `M`, naturally in the sheaf of
`O_U`-modules `M`; the isomorphism is the comparison transformation of Stacks 0798 for the
localization morphism. -/
def lowerShriekForgetOverForgetIso :
    _root_.SheafOfModules.toSheaf.{w} (inverseImageRing (J.over U) J (Over.forget U) R) ⋙
        (Over.forget U).sheafPullback AddCommGrpCat.{w} (J.over U) J ≅
      _root_.SheafOfModules.pullback.{w} (structureMap (J.over U) J (Over.forget U) R) ⋙
        _root_.SheafOfModules.toSheaf.{w} R :=
  haveI : ∀ x : Over U, (Over.post (X := x) (Over.forget U)).IsEquivalence :=
    isEquivalence_overPost_overForget U
  haveI := isIso_lowerShriekForgetComparison_of_sliceEquivalence.{w, u}
    (J.over U) J (Over.forget U) R
  asIso (lowerShriekForgetComparison.{u, w} (Over.forget U)
    (structureMap (J.over U) J (Over.forget U) R))

end Localization

/-- Transposing along the canonical isomorphism of two left adjoints of one functor: composing
a morphism out of the second left adjoint with that isomorphism and transposing under the first
adjunction gives the transpose under the second. -/
theorem homEquiv_leftAdjointUniq_hom_app_comp {A : Type*} [Category A] {B : Type*} [Category B]
    {L L' : A ⥤ B} {G : B ⥤ A} (adj1 : L ⊣ G) (adj2 : L' ⊣ G) (X : A) {Y : B}
    (g : L'.obj X ⟶ Y) :
    adj1.homEquiv X Y ((Adjunction.leftAdjointUniq adj1 adj2).hom.app X ≫ g) =
      adj2.homEquiv X Y g := by
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

/-- The canonical isomorphism of two left adjoints of one functor is invertible at every object. -/
private theorem isIso_leftAdjointUniq_hom_app {A : Type*} [Category A] {B : Type*} [Category B]
    {L L' : A ⥤ B} {G : B ⥤ A} (adj1 : L ⊣ G) (adj2 : L' ⊣ G) (X : A) :
    IsIso ((Adjunction.leftAdjointUniq adj1 adj2).hom.app X) :=
  haveI := Iso.isIso_hom (Adjunction.leftAdjointUniq adj1 adj2)
  NatIso.isIso_app_of_isIso _ X

section Composition

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {E : Type u₃} [Category.{v₃} E]
  (JA : GrothendieckTopology A) (JB : GrothendieckTopology B) (JE : GrothendieckTopology E)
  (a : A ⥤ B) [a.IsContinuous JA JB] (b : B ⥤ E) [b.IsContinuous JB JE]
  (O : Sheaf JE RingCat.{r})

/-- Taking the underlying abelian sheaf of a sheaf of modules and then restricting along a
continuous functor of sites is restricting the sheaf of modules and then taking the underlying
abelian sheaf. -/
@[sga "4 IV 11.2.3" "partial"]
theorem toSheaf_comp_sheafPushforwardContinuous (S : Sheaf JB RingCat.{r}) :
    _root_.SheafOfModules.toSheaf.{w} S ⋙
        a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB =
      _root_.SheafOfModules.pushforward.{w} (structureMap JA JB a S) ⋙
        _root_.SheafOfModules.toSheaf.{w} (inverseImageRing JA JB a S) := rfl

/-- Restriction along a continuous functor of sites of the underlying abelian morphism of a
morphism of sheaves of modules is the underlying abelian morphism of the restricted morphism. -/
@[sga "4 IV 11.2.3" "partial"]
theorem sheafPushforwardContinuous_map_toSheaf_map (S : Sheaf JB RingCat.{r})
    {M N : _root_.SheafOfModules.{w} S} (f : M ⟶ N) :
    (a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB).map
        ((_root_.SheafOfModules.toSheaf.{w} S).map f) =
      (_root_.SheafOfModules.toSheaf.{w} (inverseImageRing JA JB a S)).map
        ((_root_.SheafOfModules.pushforward.{w} (structureMap JA JB a S)).map f) := rfl

/-- Applying the forgetful functor to a morphism into a restriction composed with the
restriction of a morphism gives the forgotten morphism followed by the restriction of the forgotten
morphism. -/
theorem toSheaf_map_comp (S : Sheaf JB RingCat.{r})
    {M : _root_.SheafOfModules.{w} (inverseImageRing JA JB a S)}
    {X Y : _root_.SheafOfModules.{w} S}
    (φ : M ⟶ (_root_.SheafOfModules.pushforward.{w} (structureMap JA JB a S)).obj X)
    (g : X ⟶ Y) :
    (_root_.SheafOfModules.toSheaf.{w} (inverseImageRing JA JB a S)).map
        (φ ≫ (_root_.SheafOfModules.pushforward.{w} (structureMap JA JB a S)).map g) =
      (_root_.SheafOfModules.toSheaf.{w} (inverseImageRing JA JB a S)).map φ ≫
        (a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB).map
          ((_root_.SheafOfModules.toSheaf.{w} S).map g) := by
  rw [CategoryTheory.Functor.map_comp, sheafPushforwardContinuous_map_toSheaf_map]
  rfl

variable
  [(_root_.SheafOfModules.pushforward.{w}
    (structureMap JA JB a (inverseImageRing JB JE b O))).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w} (structureMap JB JE b O)).IsRightAdjoint]

/-- The unit of the first of two lower-shriek adjunctions for modules followed by the
restriction of (the unit of the second followed by a restricted morphism) is the unit of the
composite adjunction followed by the twice-restricted morphism. -/
theorem comp_unit_app_comp
    (M : _root_.SheafOfModules.{w} (inverseImageRing JA JB a (inverseImageRing JB JE b O)))
    {N : _root_.SheafOfModules.{w} O}
    (ψ : (_root_.SheafOfModules.pullback.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O)) ⋙
          _root_.SheafOfModules.pullback.{w} (structureMap JB JE b O)).obj M ⟶ N) :
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap JA JB a (inverseImageRing JB JE b O))).unit.app M ≫
        (_root_.SheafOfModules.pushforward.{w}
          (structureMap JA JB a (inverseImageRing JB JE b O))).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
              (structureMap JB JE b O)).unit.app
              ((_root_.SheafOfModules.pullback.{w}
                (structureMap JA JB a (inverseImageRing JB JE b O))).obj M) ≫
            (_root_.SheafOfModules.pushforward.{w} (structureMap JB JE b O)).map ψ) =
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O))).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap JB JE b O))).unit.app M ≫
        (_root_.SheafOfModules.pushforward.{w} (structureMap JB JE b O) ⋙
          _root_.SheafOfModules.pushforward.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O))).map ψ := by
  rw [Adjunction.comp_unit_app, CategoryTheory.Functor.comp_map, Category.assoc,
    ← CategoryTheory.Functor.map_comp]

/-- The forgotten unit of a composite of two lower-shriek adjunctions for modules is the
forgotten unit of the first adjunction followed by the restriction of the forgotten unit of the
second. -/
theorem toSheaf_map_comp_unit
    (M : _root_.SheafOfModules.{w} (inverseImageRing JA JB a (inverseImageRing JB JE b O))) :
    (_root_.SheafOfModules.toSheaf.{w}
          (inverseImageRing JA JB a (inverseImageRing JB JE b O))).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap JA JB a (inverseImageRing JB JE b O))).unit.app M) ≫
      (a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB).map
        ((_root_.SheafOfModules.toSheaf.{w} (inverseImageRing JB JE b O)).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap JB JE b O)).unit.app
            ((_root_.SheafOfModules.pullback.{w}
              (structureMap JA JB a (inverseImageRing JB JE b O))).obj M))) =
      (_root_.SheafOfModules.toSheaf.{w}
          (inverseImageRing JA JB a (inverseImageRing JB JE b O))).map
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O))).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap JB JE b O))).unit.app M) := by
  rw [Adjunction.comp_unit_app, toSheaf_map_comp]

/-- The split forgotten unit of the composite adjunction, followed by the twice-restricted image
of a morphism, is the split forgotten unit with that morphism absorbed into the inner one. -/
theorem splitUnit_comp_assoc
    (M : _root_.SheafOfModules.{w} (inverseImageRing JA JB a (inverseImageRing JB JE b O)))
    {N : _root_.SheafOfModules.{w} O}
    (ψ : (_root_.SheafOfModules.pullback.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O)) ⋙
          _root_.SheafOfModules.pullback.{w} (structureMap JB JE b O)).obj M ⟶ N) :
    ((_root_.SheafOfModules.toSheaf.{w}
          (inverseImageRing JA JB a (inverseImageRing JB JE b O))).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O))).unit.app M) ≫
        (a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB).map
          ((_root_.SheafOfModules.toSheaf.{w} (inverseImageRing JB JE b O)).map
            ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
              (structureMap JB JE b O)).unit.app
              ((_root_.SheafOfModules.pullback.{w}
                (structureMap JA JB a (inverseImageRing JB JE b O))).obj M)))) ≫
      (b.sheafPushforwardContinuous AddCommGrpCat.{w} JB JE ⋙
          a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB).map
        ((_root_.SheafOfModules.toSheaf.{w} O).map ψ) =
    (_root_.SheafOfModules.toSheaf.{w}
          (inverseImageRing JA JB a (inverseImageRing JB JE b O))).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap JA JB a (inverseImageRing JB JE b O))).unit.app M) ≫
      (a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB).map
        ((_root_.SheafOfModules.toSheaf.{w} (inverseImageRing JB JE b O)).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
              (structureMap JB JE b O)).unit.app
              ((_root_.SheafOfModules.pullback.{w}
                (structureMap JA JB a (inverseImageRing JB JE b O))).obj M) ≫
            (_root_.SheafOfModules.pushforward.{w} (structureMap JB JE b O)).map ψ)) := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans (whisker_eq _ (Eq.trans
    (CategoryTheory.Functor.comp_map (b.sheafPushforwardContinuous AddCommGrpCat.{w} JB JE)
      (a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB)
      ((_root_.SheafOfModules.toSheaf.{w} O).map ψ))
    (congrArg (a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB).map
      (sheafPushforwardContinuous_map_toSheaf_map JB JE b O ψ)))) ?_
  exact (CategoryTheory.Functor.map_comp (_root_.SheafOfModules.toSheaf.{w}
      (inverseImageRing JB JE b O) ⋙
      a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB) _ _).symm

/-- The split forgotten unit with a twice-restricted morphism absorbed is the forgotten unit of
the composite, followed by that morphism. -/
theorem toSheaf_map_comp_unit_comp
    (M : _root_.SheafOfModules.{w} (inverseImageRing JA JB a (inverseImageRing JB JE b O)))
    {N : _root_.SheafOfModules.{w} O}
    (ψ : (_root_.SheafOfModules.pullback.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O)) ⋙
          _root_.SheafOfModules.pullback.{w} (structureMap JB JE b O)).obj M ⟶ N) :
    (_root_.SheafOfModules.toSheaf.{w}
          (inverseImageRing JA JB a (inverseImageRing JB JE b O))).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap JA JB a (inverseImageRing JB JE b O))).unit.app M) ≫
      (a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB).map
        ((_root_.SheafOfModules.toSheaf.{w} (inverseImageRing JB JE b O)).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
              (structureMap JB JE b O)).unit.app
              ((_root_.SheafOfModules.pullback.{w}
                (structureMap JA JB a (inverseImageRing JB JE b O))).obj M) ≫
            (_root_.SheafOfModules.pushforward.{w} (structureMap JB JE b O)).map ψ)) =
      (_root_.SheafOfModules.toSheaf.{w}
          (inverseImageRing JA JB a (inverseImageRing JB JE b O))).map
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
              (structureMap JA JB a (inverseImageRing JB JE b O))).comp
            (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
              (structureMap JB JE b O))).unit.app M ≫
          (_root_.SheafOfModules.pushforward.{w} (structureMap JB JE b O) ⋙
            _root_.SheafOfModules.pushforward.{w}
              (structureMap JA JB a (inverseImageRing JB JE b O))).map ψ) :=
  Eq.trans (toSheaf_map_comp JA JB a (inverseImageRing JB JE b O)
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
        (structureMap JA JB a (inverseImageRing JB JE b O))).unit.app M)
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap JB JE b O)).unit.app
          ((_root_.SheafOfModules.pullback.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O))).obj M) ≫
        (_root_.SheafOfModules.pushforward.{w} (structureMap JB JE b O)).map ψ)).symm
    (congrArg (_root_.SheafOfModules.toSheaf.{w}
        (inverseImageRing JA JB a (inverseImageRing JB JE b O))).map
      (comp_unit_app_comp JA JB JE a b O M ψ))

variable
  [(a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB).IsRightAdjoint]
  [(b.sheafPushforwardContinuous AddCommGrpCat.{w} JB JE).IsRightAdjoint]

/-- The composition law for the comparison transformation of Stacks 0798. For a composite
`a ⋙ b` of continuous functors of sites, with the structure sheaves the successive restrictions
of a sheaf of rings on the target, the composite

`b_!^{Ab} (c^a) ≫ c^b`

of the two comparison transformations is the adjoint transpose, under the composite of the two
lower-shriek adjunctions for abelian sheaves, of the forgotten unit of the composite of the two
lower-shriek adjunctions for modules, written with the two units separated. -/
@[stacks 0798 "the composition law for the comparison transformation \
`g_!^{Ab} ∘ forget ⟶ forget ∘ g_!`"]
theorem homEquiv_comp_lowerShriekForgetComparison
    (M : _root_.SheafOfModules.{w} (inverseImageRing JA JB a (inverseImageRing JB JE b O))) :
    ((a.sheafAdjunctionContinuous AddCommGrpCat.{w} JA JB).comp
        (b.sheafAdjunctionContinuous AddCommGrpCat.{w} JB JE)).homEquiv _ _
      ((b.sheafPullback AddCommGrpCat.{w} JB JE).map
          ((lowerShriekForgetComparison a
            (structureMap JA JB a (inverseImageRing JB JE b O))).app M) ≫
        (lowerShriekForgetComparison b (structureMap JB JE b O)).app
          ((_root_.SheafOfModules.pullback.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O))).obj M)) =
      (_root_.SheafOfModules.toSheaf.{w}
            (inverseImageRing JA JB a (inverseImageRing JB JE b O))).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O))).unit.app M) ≫
        (a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB).map
          ((_root_.SheafOfModules.toSheaf.{w} (inverseImageRing JB JE b O)).map
            ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
              (structureMap JB JE b O)).unit.app
              ((_root_.SheafOfModules.pullback.{w}
                (structureMap JA JB a (inverseImageRing JB JE b O))).obj M))) := by
  rw [Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  dsimp only [CategoryTheory.Functor.comp_obj]
  rw [lowerShriekForgetComparison_homEquiv]
  refine (Adjunction.homEquiv_naturality_right _ _ _).trans ?_
  rw [lowerShriekForgetComparison_homEquiv]
  rfl

/-- The adjoint transpose of the composite of the two comparison transformations followed by the
forgotten image of a morphism `ψ` out of the composite lower shriek on modules is the split
forgotten unit of the composite module adjunction with `ψ` absorbed into its inner unit. -/
theorem homEquiv_comp_lowerShriekForgetComparison_comp
    (M : _root_.SheafOfModules.{w} (inverseImageRing JA JB a (inverseImageRing JB JE b O)))
    {N : _root_.SheafOfModules.{w} O}
    (ψ : (_root_.SheafOfModules.pullback.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O)) ⋙
          _root_.SheafOfModules.pullback.{w} (structureMap JB JE b O)).obj M ⟶ N) :
    ((a.sheafAdjunctionContinuous AddCommGrpCat.{w} JA JB).comp
        (b.sheafAdjunctionContinuous AddCommGrpCat.{w} JB JE)).homEquiv _ _
      (((b.sheafPullback AddCommGrpCat.{w} JB JE).map
            ((lowerShriekForgetComparison a
              (structureMap JA JB a (inverseImageRing JB JE b O))).app M) ≫
          (lowerShriekForgetComparison b (structureMap JB JE b O)).app
            ((_root_.SheafOfModules.pullback.{w}
              (structureMap JA JB a (inverseImageRing JB JE b O))).obj M)) ≫
        (_root_.SheafOfModules.toSheaf.{w} O).map ψ) =
      (_root_.SheafOfModules.toSheaf.{w}
          (inverseImageRing JA JB a (inverseImageRing JB JE b O))).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap JA JB a (inverseImageRing JB JE b O))).unit.app M) ≫
        (a.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB).map
          ((_root_.SheafOfModules.toSheaf.{w} (inverseImageRing JB JE b O)).map
            ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
                (structureMap JB JE b O)).unit.app
                ((_root_.SheafOfModules.pullback.{w}
                  (structureMap JA JB a (inverseImageRing JB JE b O))).obj M) ≫
              (_root_.SheafOfModules.pushforward.{w} (structureMap JB JE b O)).map ψ)) := by
  refine Eq.trans (Adjunction.homEquiv_naturality_right
    ((a.sheafAdjunctionContinuous AddCommGrpCat.{w} JA JB).comp
      (b.sheafAdjunctionContinuous AddCommGrpCat.{w} JB JE)) _
    ((_root_.SheafOfModules.toSheaf.{w} O).map ψ)) ?_
  refine Eq.trans (eq_whisker
    (homEquiv_comp_lowerShriekForgetComparison JA JB JE a b O M) _) ?_
  exact splitUnit_comp_assoc JA JB JE a b O M ψ

end Composition

/-- A functor between categories with terminal objects which carries one to the other is
final. -/
theorem final_of_isTerminal {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (F : A ⥤ B) {t : A} (ht : Limits.IsTerminal t) (ht' : Limits.IsTerminal (F.obj t)) :
    F.Final := by
  refine ⟨fun d => isConnected_of_isTerminal _
    (Limits.IsTerminal.ofUniqueHom (X := StructuredArrow.mk (S := d) (ht'.from d))
      (fun X => StructuredArrow.homMk (ht.from X.right) (ht'.hom_ext _ _)) ?_)⟩
  intro X f
  exact StructuredArrow.hom_ext _ _ (ht.hom_ext _ _)

/-- Localizing a continuous functor of sites is final: `Over.post u : C/U ⥤ D/u(U)` is a final
functor. -/
instance final_overPost {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (F : A ⥤ B) (X : A) : (Over.post (X := X) F).Final :=
  final_of_isTerminal _ Over.mkIdTerminal
    (Limits.IsTerminal.ofIso Over.mkIdTerminal
      (Over.isoMk (Iso.refl _) (by simp [Over.post])))

section LocalizedSquare

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K] (O : Sheaf K RingCat.{w}) (V : C)
  [(Over.post (X := V) u).IsContinuous (J.over V) (K.over (u.obj V))]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [((Over.forget V).sheafPushforwardContinuous AddCommGrpCat.{w} (J.over V) J).IsRightAdjoint]
  [((Over.forget (u.obj V)).sheafPushforwardContinuous AddCommGrpCat.{w}
    (K.over (u.obj V)) K).IsRightAdjoint]
  [((Over.post (X := V) u).sheafPushforwardContinuous AddCommGrpCat.{w}
    (J.over V) (K.over (u.obj V))).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w}
    (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O))).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w}
    (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w} (structureMap (J.over V) (K.over (u.obj V))
    (Over.post (X := V) u) (O.over (u.obj V)))).IsRightAdjoint]

/-- The component at a sheaf of modules of the uniqueness isomorphism of the two composite lower
shrieks on modules obtained by reading the functor `C/U ⥤ D` of the localized square of
Stacks 03EG in its two ways. -/
def localizedSquareModuleComparison
    (M : _root_.SheafOfModules.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))) :
    (_root_.SheafOfModules.pullback.{w}
            (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O)) ⋙
          _root_.SheafOfModules.pullback.{w} (structureMap J K u O)).obj M ⟶
      (_root_.SheafOfModules.pullback.{w} (structureMap (J.over V) (K.over (u.obj V))
              (Over.post (X := V) u) (O.over (u.obj V))) ⋙
          _root_.SheafOfModules.pullback.{w}
            (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)).obj M :=
  (Adjunction.leftAdjointUniq
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O))).comp
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} (structureMap J K u O)))
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
            (O.over (u.obj V)))).comp
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)))).hom.app M

omit [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [((Over.forget V).sheafPushforwardContinuous AddCommGrpCat.{w} (J.over V) J).IsRightAdjoint]
  [((Over.forget (u.obj V)).sheafPushforwardContinuous AddCommGrpCat.{w}
    (K.over (u.obj V)) K).IsRightAdjoint]
  [((Over.post (X := V) u).sheafPushforwardContinuous AddCommGrpCat.{w}
    (J.over V) (K.over (u.obj V))).IsRightAdjoint] in
/-- The comparison `Stacks.SheafOfModules.localizedSquareModuleComparison` is an
isomorphism. -/
theorem isIso_localizedSquareModuleComparison
    (M : _root_.SheafOfModules.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))) :
    IsIso (localizedSquareModuleComparison J K u O V M) := by
  unfold localizedSquareModuleComparison
  exact isIso_leftAdjointUniq_hom_app _ _ _

/-- The forgotten unit of the composite module adjunction of the second reading of the
localized square, with one restriction of scalars turned into a restriction of abelian sheaves in
its target. -/
def localizedSquareUnit
    (M : _root_.SheafOfModules.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))) :
    (_root_.SheafOfModules.toSheaf.{w}
          (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))).obj M ⟶
      ((Over.post (X := V) u).sheafPushforwardContinuous AddCommGrpCat.{w}
          (J.over V) (K.over (u.obj V))).obj
        ((_root_.SheafOfModules.toSheaf.{w} (O.over (u.obj V))).obj
          ((_root_.SheafOfModules.pushforward.{w}
              (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)).obj
            ((_root_.SheafOfModules.pullback.{w} (structureMap (J.over V) (K.over (u.obj V))
                    (Over.post (X := V) u) (O.over (u.obj V))) ⋙
                _root_.SheafOfModules.pullback.{w}
                  (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)).obj M))) :=
  (_root_.SheafOfModules.toSheaf.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))).map
    (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
            (O.over (u.obj V)))).comp
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
          (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O))).unit.app M)

omit [((Over.forget (u.obj V)).sheafPushforwardContinuous AddCommGrpCat.{w}
    (K.over (u.obj V)) K).IsRightAdjoint]
  [((Over.post (X := V) u).sheafPushforwardContinuous AddCommGrpCat.{w}
    (J.over V) (K.over (u.obj V))).IsRightAdjoint] in
/-- The transpose of the first reading of the localized square, split into its two
comparisons. -/
theorem squareTransposeLeftSplit
    (M : _root_.SheafOfModules.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))) :
    (((Over.forget V).sheafAdjunctionContinuous AddCommGrpCat.{w} (J.over V) J).comp
        (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)).homEquiv _ _
      (((u.sheafPullback AddCommGrpCat.{w} J K).map
            ((lowerShriekForgetComparison (Over.forget V)
              (structureMap (J.over V) J (Over.forget V)
                (inverseImageRing J K u O))).app M) ≫
          (lowerShriekForgetComparison u (structureMap J K u O)).app
            ((_root_.SheafOfModules.pullback.{w}
              (structureMap (J.over V) J (Over.forget V)
                (inverseImageRing J K u O))).obj M)) ≫
        (_root_.SheafOfModules.toSheaf.{w} O).map
          (localizedSquareModuleComparison J K u O V M)) =
      (_root_.SheafOfModules.toSheaf.{w}
            (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap (J.over V) J (Over.forget V)
              (inverseImageRing J K u O))).unit.app M) ≫
        ((Over.forget V).sheafPushforwardContinuous AddCommGrpCat.{w} (J.over V) J).map
          ((_root_.SheafOfModules.toSheaf.{w} (inverseImageRing J K u O)).map
            ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
                (structureMap J K u O)).unit.app
                ((_root_.SheafOfModules.pullback.{w}
                  (structureMap (J.over V) J (Over.forget V)
                    (inverseImageRing J K u O))).obj M) ≫
              (_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).map
                (localizedSquareModuleComparison J K u O V M))) :=
  homEquiv_comp_lowerShriekForgetComparison_comp (J.over V) J K (Over.forget V) u O M
    (localizedSquareModuleComparison J K u O V M)

omit [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [((Over.forget V).sheafPushforwardContinuous AddCommGrpCat.{w} (J.over V) J).IsRightAdjoint]
  [((Over.forget (u.obj V)).sheafPushforwardContinuous AddCommGrpCat.{w}
    (K.over (u.obj V)) K).IsRightAdjoint]
  [((Over.post (X := V) u).sheafPushforwardContinuous AddCommGrpCat.{w}
    (J.over V) (K.over (u.obj V))).IsRightAdjoint] in
/-- The split transpose of the first reading of the localized square is the forgotten unit of
the second reading. -/
theorem squareTransposeLeftModule
    (M : _root_.SheafOfModules.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))) :
    (_root_.SheafOfModules.toSheaf.{w}
            (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap (J.over V) J (Over.forget V)
              (inverseImageRing J K u O))).unit.app M) ≫
        ((Over.forget V).sheafPushforwardContinuous AddCommGrpCat.{w} (J.over V) J).map
          ((_root_.SheafOfModules.toSheaf.{w} (inverseImageRing J K u O)).map
            ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
                (structureMap J K u O)).unit.app
                ((_root_.SheafOfModules.pullback.{w}
                  (structureMap (J.over V) J (Over.forget V)
                    (inverseImageRing J K u O))).obj M) ≫
              (_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).map
                (localizedSquareModuleComparison J K u O V M))) =
      localizedSquareUnit J K u O V M :=
  Eq.trans (toSheaf_map_comp_unit_comp (J.over V) J K (Over.forget V) u O M
      (localizedSquareModuleComparison J K u O V M))
    (congrArg (_root_.SheafOfModules.toSheaf.{w}
        (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))).map
      (Adjunction.unit_leftAdjointUniq_hom_app
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O))).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} (structureMap J K u O)))
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
              (O.over (u.obj V)))).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O))) M))

omit [((Over.forget (u.obj V)).sheafPushforwardContinuous AddCommGrpCat.{w}
    (K.over (u.obj V)) K).IsRightAdjoint]
  [((Over.post (X := V) u).sheafPushforwardContinuous AddCommGrpCat.{w}
    (J.over V) (K.over (u.obj V))).IsRightAdjoint] in
/-- Composing the two comparison transformations of the reading `j_U` followed by `u` with the
identification of the two composite lower shrieks on modules and transposing gives the forgotten
unit of the composite module adjunction of the other reading. -/
theorem squareTransposeLeft
    (M : _root_.SheafOfModules.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))) :
    (((Over.forget V).sheafAdjunctionContinuous AddCommGrpCat.{w} (J.over V) J).comp
        (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)).homEquiv _ _
      (((u.sheafPullback AddCommGrpCat.{w} J K).map
            ((lowerShriekForgetComparison (Over.forget V)
              (structureMap (J.over V) J (Over.forget V)
                (inverseImageRing J K u O))).app M) ≫
          (lowerShriekForgetComparison u (structureMap J K u O)).app
            ((_root_.SheafOfModules.pullback.{w}
              (structureMap (J.over V) J (Over.forget V)
                (inverseImageRing J K u O))).obj M)) ≫
        (_root_.SheafOfModules.toSheaf.{w} O).map
          (localizedSquareModuleComparison J K u O V M)) =
      localizedSquareUnit J K u O V M :=
  Eq.trans (squareTransposeLeftSplit J K u O V M) (squareTransposeLeftModule J K u O V M)

omit [(_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w}
    (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O))).IsRightAdjoint] in
/-- The transpose of the second reading of the localized square, split into its two
comparisons. -/
theorem squareTransposeRightSplit
    (M : _root_.SheafOfModules.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))) :
    (((Over.forget V).sheafAdjunctionContinuous AddCommGrpCat.{w} (J.over V) J).comp
        (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)).homEquiv _ _
      ((Adjunction.leftAdjointUniq
            (((Over.forget V).sheafAdjunctionContinuous AddCommGrpCat.{w} (J.over V) J).comp
              (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K))
            (((Over.post (X := V) u).sheafAdjunctionContinuous AddCommGrpCat.{w}
                (J.over V) (K.over (u.obj V))).comp
              ((Over.forget (u.obj V)).sheafAdjunctionContinuous AddCommGrpCat.{w}
                (K.over (u.obj V)) K))).hom.app
          ((_root_.SheafOfModules.toSheaf.{w}
            (inverseImageRing (J.over V) J (Over.forget V)
              (inverseImageRing J K u O))).obj M) ≫
        (((Over.forget (u.obj V)).sheafPullback AddCommGrpCat.{w} (K.over (u.obj V)) K).map
            ((lowerShriekForgetComparison (Over.post (X := V) u)
              (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
                (O.over (u.obj V)))).app M) ≫
          (lowerShriekForgetComparison (Over.forget (u.obj V))
            (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)).app
            ((_root_.SheafOfModules.pullback.{w}
              (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
                (O.over (u.obj V)))).obj M))) =
      (_root_.SheafOfModules.toSheaf.{w} (inverseImageRing (J.over V) (K.over (u.obj V))
            (Over.post (X := V) u) (O.over (u.obj V)))).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
              (O.over (u.obj V)))).unit.app M) ≫
        ((Over.post (X := V) u).sheafPushforwardContinuous AddCommGrpCat.{w}
            (J.over V) (K.over (u.obj V))).map
          ((_root_.SheafOfModules.toSheaf.{w} (O.over (u.obj V))).map
            ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
              (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)).unit.app
              ((_root_.SheafOfModules.pullback.{w}
                (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
                  (O.over (u.obj V)))).obj M))) :=
  Eq.trans (homEquiv_leftAdjointUniq_hom_app_comp
      (((Over.forget V).sheafAdjunctionContinuous AddCommGrpCat.{w} (J.over V) J).comp
        (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K))
      (((Over.post (X := V) u).sheafAdjunctionContinuous AddCommGrpCat.{w}
          (J.over V) (K.over (u.obj V))).comp
        ((Over.forget (u.obj V)).sheafAdjunctionContinuous AddCommGrpCat.{w}
          (K.over (u.obj V)) K))
      ((_root_.SheafOfModules.toSheaf.{w}
        (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))).obj M)
      ((((Over.forget (u.obj V)).sheafPullback AddCommGrpCat.{w} (K.over (u.obj V)) K).map
          ((lowerShriekForgetComparison (Over.post (X := V) u)
            (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
              (O.over (u.obj V)))).app M) ≫
        (lowerShriekForgetComparison (Over.forget (u.obj V))
          (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)).app
          ((_root_.SheafOfModules.pullback.{w}
            (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
              (O.over (u.obj V)))).obj M))))
    (homEquiv_comp_lowerShriekForgetComparison (J.over V) (K.over (u.obj V)) K
      (Over.post (X := V) u) (Over.forget (u.obj V)) O M)

omit [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [((Over.forget V).sheafPushforwardContinuous AddCommGrpCat.{w} (J.over V) J).IsRightAdjoint]
  [((Over.forget (u.obj V)).sheafPushforwardContinuous AddCommGrpCat.{w}
    (K.over (u.obj V)) K).IsRightAdjoint]
  [((Over.post (X := V) u).sheafPushforwardContinuous AddCommGrpCat.{w}
    (J.over V) (K.over (u.obj V))).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w}
    (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O))).IsRightAdjoint] in
/-- The split transpose of the second reading of the localized square is the forgotten unit of
its composite module adjunction. -/
theorem squareTransposeRightModule
    (M : _root_.SheafOfModules.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))) :
    (_root_.SheafOfModules.toSheaf.{w} (inverseImageRing (J.over V) (K.over (u.obj V))
            (Over.post (X := V) u) (O.over (u.obj V)))).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
            (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
              (O.over (u.obj V)))).unit.app M) ≫
        ((Over.post (X := V) u).sheafPushforwardContinuous AddCommGrpCat.{w}
            (J.over V) (K.over (u.obj V))).map
          ((_root_.SheafOfModules.toSheaf.{w} (O.over (u.obj V))).map
            ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w}
              (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)).unit.app
              ((_root_.SheafOfModules.pullback.{w}
                (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
                  (O.over (u.obj V)))).obj M))) =
      localizedSquareUnit J K u O V M :=
  toSheaf_map_comp_unit (J.over V) (K.over (u.obj V)) K
    (Over.post (X := V) u) (Over.forget (u.obj V)) O M

omit [(_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w}
    (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O))).IsRightAdjoint] in
/-- The transpose of the second reading of the localized square is the same forgotten unit as
for the first reading. -/
theorem squareTransposeRight
    (M : _root_.SheafOfModules.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))) :
    (((Over.forget V).sheafAdjunctionContinuous AddCommGrpCat.{w} (J.over V) J).comp
        (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)).homEquiv _ _
      ((Adjunction.leftAdjointUniq
            (((Over.forget V).sheafAdjunctionContinuous AddCommGrpCat.{w} (J.over V) J).comp
              (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K))
            (((Over.post (X := V) u).sheafAdjunctionContinuous AddCommGrpCat.{w}
                (J.over V) (K.over (u.obj V))).comp
              ((Over.forget (u.obj V)).sheafAdjunctionContinuous AddCommGrpCat.{w}
                (K.over (u.obj V)) K))).hom.app
          ((_root_.SheafOfModules.toSheaf.{w}
            (inverseImageRing (J.over V) J (Over.forget V)
              (inverseImageRing J K u O))).obj M) ≫
        (((Over.forget (u.obj V)).sheafPullback AddCommGrpCat.{w} (K.over (u.obj V)) K).map
            ((lowerShriekForgetComparison (Over.post (X := V) u)
              (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
                (O.over (u.obj V)))).app M) ≫
          (lowerShriekForgetComparison (Over.forget (u.obj V))
            (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)).app
            ((_root_.SheafOfModules.pullback.{w}
              (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
                (O.over (u.obj V)))).obj M))) =
      localizedSquareUnit J K u O V M :=
  Eq.trans (squareTransposeRightSplit J K u O V M) (squareTransposeRightModule J K u O V M)

/-- The comparison transformation of Stacks 0798 is compatible with the localized square of
Stacks 03EG. Reading the functor `C/U ⥤ D` of the square in its two ways, as `j_U` followed by
`u` and as `u' = Over.post u` followed by `j_{u(U)}`, gives two composites of comparison
transformations; they agree after the canonical identifications of the two composite lower
shrieks, on abelian sheaves and on modules. -/
theorem lowerShriekForgetComparison_localizedSquare
    (M : _root_.SheafOfModules.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))) :
    ((u.sheafPullback AddCommGrpCat.{w} J K).map
          ((lowerShriekForgetComparison (Over.forget V)
            (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O))).app M) ≫
        (lowerShriekForgetComparison u (structureMap J K u O)).app
          ((_root_.SheafOfModules.pullback.{w}
            (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O))).obj M)) ≫
      (_root_.SheafOfModules.toSheaf.{w} O).map
        (localizedSquareModuleComparison J K u O V M) =
    (Adjunction.leftAdjointUniq
          (((Over.forget V).sheafAdjunctionContinuous AddCommGrpCat.{w} (J.over V) J).comp
            (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K))
          (((Over.post (X := V) u).sheafAdjunctionContinuous AddCommGrpCat.{w}
              (J.over V) (K.over (u.obj V))).comp
            ((Over.forget (u.obj V)).sheafAdjunctionContinuous AddCommGrpCat.{w}
              (K.over (u.obj V)) K))).hom.app
        ((_root_.SheafOfModules.toSheaf.{w}
          (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))).obj M) ≫
      (((Over.forget (u.obj V)).sheafPullback AddCommGrpCat.{w} (K.over (u.obj V)) K).map
          ((lowerShriekForgetComparison (Over.post (X := V) u)
            (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
              (O.over (u.obj V)))).app M) ≫
        (lowerShriekForgetComparison (Over.forget (u.obj V))
          (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)).app
          ((_root_.SheafOfModules.pullback.{w}
            (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
              (O.over (u.obj V)))).obj M)) :=
  ((((Over.forget V).sheafAdjunctionContinuous AddCommGrpCat.{w} (J.over V) J).comp
      (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)).homEquiv _ _).injective
    (Eq.trans (squareTransposeLeft J K u O V M) (Eq.symm (squareTransposeRight J K u O V M)))

/-- If the comparison transformation of Stacks 0798 for the localized functor
`u' = Over.post u : C/U ⥤ D/u(U)` is an isomorphism at a sheaf of modules `M` on `C/U`, then the
comparison for `u` is an isomorphism at `j_{U!} M`. -/
theorem isIso_lowerShriekForgetComparison_app_pullback_of_isIso
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [(PresheafOfModules.pushforward.{w} (F := Over.forget V)
      (𝟙 ((Over.forget V).op ⋙ (inverseImageRing J K u O).obj))).IsRightAdjoint]
    [∀ G : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{w}, (Over.forget V).op.HasPointwiseLeftKanExtension G]
    [(PresheafOfModules.pushforward.{w} (F := Over.forget (u.obj V))
      (𝟙 ((Over.forget (u.obj V)).op ⋙ O.obj))).IsRightAdjoint]
    [∀ G : (Over (u.obj V))ᵒᵖ ⥤ AddCommGrpCat.{w},
      (Over.forget (u.obj V)).op.HasPointwiseLeftKanExtension G]
    (M : _root_.SheafOfModules.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O)))
    (h : IsIso ((lowerShriekForgetComparison (Over.post (X := V) u)
      (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
        (O.over (u.obj V)))).app M)) :
    IsIso ((lowerShriekForgetComparison u (structureMap J K u O)).app
      ((_root_.SheafOfModules.pullback.{w}
        (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O))).obj M)) := by
  have := h
  have : ∀ x : Over V, (Over.post (X := x) (Over.forget V)).IsEquivalence :=
    isEquivalence_overPost_overForget V
  have h1 := isIso_lowerShriekForgetComparison_app_of_sliceEquivalence (J.over V) J
    (Over.forget V) (inverseImageRing J K u O) M
  have : ∀ x : Over (u.obj V), (Over.post (X := x) (Over.forget (u.obj V))).IsEquivalence :=
    isEquivalence_overPost_overForget (u.obj V)
  have h2 := isIso_lowerShriekForgetComparison_app_of_sliceEquivalence (K.over (u.obj V)) K
    (Over.forget (u.obj V)) O ((_root_.SheafOfModules.pullback.{w}
      (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
        (O.over (u.obj V)))).obj M)
  have := isIso_localizedSquareModuleComparison J K u O V M
  have he := isIso_leftAdjointUniq_hom_app
    (((Over.forget V).sheafAdjunctionContinuous AddCommGrpCat.{w} (J.over V) J).comp
      (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K))
    (((Over.post (X := V) u).sheafAdjunctionContinuous AddCommGrpCat.{w}
        (J.over V) (K.over (u.obj V))).comp
      ((Over.forget (u.obj V)).sheafAdjunctionContinuous AddCommGrpCat.{w}
        (K.over (u.obj V)) K))
    ((_root_.SheafOfModules.toSheaf.{w}
      (inverseImageRing (J.over V) J (Over.forget V) (inverseImageRing J K u O))).obj M)
  have hc3 := Functor.map_isIso ((Over.forget (u.obj V)).sheafPullback AddCommGrpCat.{w}
      (K.over (u.obj V)) K) ((lowerShriekForgetComparison (Over.post (X := V) u)
      (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
        (O.over (u.obj V)))).app M)
  have := IsIso.of_isIso_fac_right
    (hh := IsIso.comp_isIso' he (IsIso.comp_isIso' hc3 h2))
    (lowerShriekForgetComparison_localizedSquare J K u O V M)
  exact IsIso.of_isIso_comp_left ((u.sheafPullback AddCommGrpCat.{w} J K).map
    ((lowerShriekForgetComparison (Over.forget V)
      (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O))).app M)) _

/-- The canonical map `(g')_!^{Ab} O_U ⟶ O_{u(U)}` of Stacks 0798: lower shriek of abelian
sheaves applied to the underlying abelian sheaf of the structure sheaf of the localized source
site, mapping to the underlying abelian sheaf of the structure sheaf of the localized target
site. It is the comparison transformation of Stacks 0798 for the localized functor, evaluated at
the structure sheaf, followed by the canonical map `g'_! O_U ⟶ O_{u(U)}` of sheaves of
modules. -/
@[stacks 0798 "the canonical map of equation 0799, `κ_U : (g')_!^{Ab} O_U ⟶ O_{u(U)}`"]
def localizedStructureSheafComparison :
    ((Over.post (X := V) u).sheafPullback AddCommGrpCat.{w} (J.over V) (K.over (u.obj V))).obj
        ((_root_.SheafOfModules.toSheaf.{w} (inverseImageRing (J.over V) (K.over (u.obj V))
            (Over.post (X := V) u) (O.over (u.obj V)))).obj
          (_root_.SheafOfModules.unit _)) ⟶
      (_root_.SheafOfModules.toSheaf.{w} (O.over (u.obj V))).obj
        (_root_.SheafOfModules.unit (O.over (u.obj V))) :=
  (lowerShriekForgetComparison (Over.post (X := V) u)
        (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
          (O.over (u.obj V)))).app (_root_.SheafOfModules.unit _) ≫
    (_root_.SheafOfModules.toSheaf.{w} (O.over (u.obj V))).map
      (_root_.SheafOfModules.pullbackObjUnitToUnit
        (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u) (O.over (u.obj V))))

omit [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [((Over.forget V).sheafPushforwardContinuous AddCommGrpCat.{w} (J.over V) J).IsRightAdjoint]
  [((Over.forget (u.obj V)).sheafPushforwardContinuous AddCommGrpCat.{w}
    (K.over (u.obj V)) K).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w} (structureMap J K u O)).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w}
    (structureMap (J.over V) J (Over.forget V) (inverseImageRing J K u O))).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{w}
    (structureMap (K.over (u.obj V)) K (Over.forget (u.obj V)) O)).IsRightAdjoint] in
/-- If the canonical map `(g')_!^{Ab} O_U ⟶ O_{u(U)}` is an isomorphism then so is the comparison
transformation of Stacks 0798 for the localized functor at the structure sheaf. -/
theorem isIso_lowerShriekForgetComparison_app_unit_of_isIso
    (h : IsIso (localizedStructureSheafComparison J K u O V)) :
    IsIso ((lowerShriekForgetComparison (Over.post (X := V) u)
      (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
        (O.over (u.obj V)))).app (_root_.SheafOfModules.unit _)) := by
  have h' : IsIso ((lowerShriekForgetComparison (Over.post (X := V) u)
        (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
          (O.over (u.obj V)))).app (_root_.SheafOfModules.unit _) ≫
      (_root_.SheafOfModules.toSheaf.{w} (O.over (u.obj V))).map
        (_root_.SheafOfModules.pullbackObjUnitToUnit
          (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
            (O.over (u.obj V))))) := h
  exact IsIso.of_isIso_comp_right _
    ((_root_.SheafOfModules.toSheaf.{w} (O.over (u.obj V))).map
      (_root_.SheafOfModules.pullbackObjUnitToUnit
        (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
          (O.over (u.obj V)))))

end LocalizedSquare

section Criterion

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
  (O : Sheaf K RingCat.{max u₁ v₁ u₂ v₂ t})
  [∀ V : C, (Over.post (X := V) u).IsContinuous (J.over V) (K.over (u.obj V))]
  [HasWeakSheafify J AddCommGrpCat.{max u₁ v₁ u₂ v₂ t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ u₂ v₂ t}]
  [HasWeakSheafify K AddCommGrpCat.{max u₁ v₁ u₂ v₂ t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ u₂ v₂ t}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ t} J K).IsRightAdjoint]
  [∀ V : C, ((Over.forget V).sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ t}
    (J.over V) J).IsRightAdjoint]
  [∀ W : D, ((Over.forget W).sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ t}
    (K.over W) K).IsRightAdjoint]
  [∀ V : C, ((Over.post (X := V) u).sheafPushforwardContinuous
    AddCommGrpCat.{max u₁ v₁ u₂ v₂ t} (J.over V) (K.over (u.obj V))).IsRightAdjoint]
  [∀ V : C, (_root_.SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ t} (F := Over.forget V)
    (𝟙 ((inverseImageRing J K u O).over V))).IsRightAdjoint]
  [∀ W : D, (_root_.SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ t} (F := Over.forget W)
    (𝟙 (O.over W))).IsRightAdjoint]
  [∀ V : C, (_root_.SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ t}
    (structureMap (J.over V) (K.over (u.obj V)) (Over.post (X := V) u)
      (O.over (u.obj V)))).IsRightAdjoint]
  [∀ V : C, (PresheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ t} (F := Over.forget V)
    (𝟙 ((Over.forget V).op ⋙ (inverseImageRing J K u O).obj))).IsRightAdjoint]
  [∀ V : C, ∀ G : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁ u₂ v₂ t},
    (Over.forget V).op.HasPointwiseLeftKanExtension G]
  [∀ W : D, (PresheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ t} (F := Over.forget W)
    (𝟙 ((Over.forget W).op ⋙ O.obj))).IsRightAdjoint]
  [∀ W : D, ∀ G : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁ u₂ v₂ t},
    (Over.forget W).op.HasPointwiseLeftKanExtension G]

/-- Lower shriek on sheaves of modules agrees with lower shriek on the underlying abelian
sheaves, that is, the comparison transformation `Stacks.SheafOfModules.lowerShriekForgetComparison`
is an isomorphism, as soon as, for every object `U` of the source site, the canonical map

`(g')_!^{Ab} O_U ⟶ O_{u(U)}`

of `Stacks.SheafOfModules.localizedStructureSheafComparison` is an isomorphism, `g'` being the
morphism of topoi induced by the localized functor `u' = Over.post u : C/U ⥤ D/u(U)` of Stacks
03EG. -/
@[stacks 0798 "the criterion: `g_! = g_!^{Ab}` if the canonical map of equation 0799 is an \
isomorphism for every object `U`"]
theorem isIso_lowerShriekForgetComparison_of_localizedStructureSheafComparison
    (h : ∀ V : C, IsIso (localizedStructureSheafComparison J K u O V)) :
    IsIso (lowerShriekForgetComparison u (structureMap J K u O)) := by
  rw [isIso_lowerShriekForgetComparison_iff_extensionByZeroUnit.{t, u₁, u₂, v₁, v₂}]
  intro V
  have hu := isIso_lowerShriekForgetComparison_app_unit_of_isIso J K u O V (h V)
  have hp := isIso_lowerShriekForgetComparison_app_pullback_of_isIso J K u O V
    (_root_.SheafOfModules.unit _) hu
  have hsp := (NatTrans.isIso_app_iff_of_iso
    (lowerShriekForgetComparison u (structureMap J K u O))
    (extensionByZeroUnitSpellingIso.{max u₂ v₂ t, u₁, v₁} (inverseImageRing J K u O) V)).mpr
    inferInstance
  exact IsIso.comp_isIso' hsp inferInstance

end Criterion

end Stacks.SheafOfModules

end
