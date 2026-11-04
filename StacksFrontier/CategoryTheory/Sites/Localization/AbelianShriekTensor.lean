module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero and tensor products on a localized topos

Let `F` be a sheaf of sets on a site `C` and let `C/F` be the site of pairs `(U, s)` with
`s ∈ F(U)`, whose topos is the slice topos `Sh(C)/F` (Stacks 0791). Write `j` for the
localization morphism, so that `j⁻¹` is restriction of sheaves to `C/F` and `j_!` is extension
by zero, the left adjoint of `j⁻¹`. For every abelian sheaf `H` on `C` there is an isomorphism

`j_! (j⁻¹ H) ≅ (j_! ℤ) ⊗ H`,

where `ℤ` is the constant abelian sheaf on `C/F`, i.e. the tensor unit.

The proof is the one of the source, read off from the formula for `j_!` as left Kan extension
followed by sheafification. Before sheafifying, the left Kan extension of the restriction of `H`
along the projection `C/F ⥤ C` is the presheaf `U ↦ ⨁_{s ∈ F(U)} H(U)`, the direct sum indexed
by the sections of `F`. That presheaf is identified with `(⨁_{s ∈ F(U)} ℤ) ⊗ H(U)` objectwise,
because tensoring commutes with colimits and the unit absorbs into each summand; sheafifying is
monoidal, so the isomorphism descends to sheaves.

## Main definitions

* `Stacks.Sites.Localization.LocalizationSite`: the site `C/F` of pairs `(U, s)`.
* `Stacks.Sites.Localization.localizationProjection` and
  `Stacks.Sites.Localization.localizationTopology`: its projection to `C` and the induced
  topology.
* `Stacks.Sites.Localization.abelianLocalizationInverseImage`: the functor `j⁻¹` on abelian
  sheaves.
* `Stacks.Sites.Localization.abelianLocalizationShriek`: the functor `j_!` on abelian sheaves,
  as left Kan extension followed by sheafification.

## Main results

* `Stacks.Sites.Localization.localizationProjection_isContinuous`: the projection is a
  continuous functor of sites.
* `Stacks.Sites.Localization.jShriekPullbackIsoTensor`: the isomorphism
  `j_!(j⁻¹ H) ≅ j_! ℤ ⊗ H`.

## Implementation notes

Everything here is stated for a site of arbitrary size, `C : Type u` with `Category.{v} C`, so
the objects the statement is about are hypotheses rather than constructions: sheafification of
`ModuleCat (ULift ℤ)`-valued presheaves on `C` and on `C/F`, the monoidality of the two
sheafification localizers, and the left Kan extensions along `C/F ⥤ C` — this last being what
makes `abelianLocalizationShriek`, the functor `j_!`, exist. On a site, which is what the source
assumes, every one of them holds, and
`StacksFrontier.CategoryTheory.Sites.Localization.AbelianShriekIntegerBridge` states the conclusion
with none of them assumed.

The site of pairs is `CostructuredArrow yoneda F.obj` with the topology restricted from `J`;
Stacks 0791 identifies its topos with `Sh(C)/F` and the functors induced by the projection with
the localization morphism's `j⁻¹` and `j_!`, so no separate slice-topos construction is needed.

Abelian sheaves are taken as sheaves valued in `ModuleCat (ULift ℤ)` rather than
`AddCommGrpCat`. This is the universe-polymorphic form of the equivalence between abelian
groups and `ℤ`-modules, and it is what gives the monoidal structure in which the statement is
phrased: the tensor unit is then the constant sheaf denoted `ℤ` in the source. The conclusion is
the isomorphism itself, the source asserting an equality of sheaves;
`StacksFrontier.CategoryTheory.Sites.Localization.AbelianShriekIntegerBridge` transports it along
the equivalence with `AddCommGrpCat`-valued sheaves and identifies the tensor unit there with
the free abelian sheaf on `F`.

The presheaf-level direct sum is built as a colimit over the discrete category on `F(U)` rather
than as a `DirectSum`, so that the comparison with the left Kan extension is the colimit
universal property and the tensor identification is `preservesColimitIso` for `tensorLeft`.

## References

* [Stacks Project, Tag 0EYY](https://stacks.math.columbia.edu/tag/0EYY)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791), the slice topos.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits
open Opposite

universe u v

namespace Stacks.Sites.Localization

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The site category `C/F` whose objects are pairs `(U, s)` with `s ∈ F(U)`. -/
abbrev LocalizationSite (F : Sheaf J (Type v)) :=
  CostructuredArrow yoneda F.obj

/-- The projection from the localization site `C/F` to `C`. -/
abbrev localizationProjection (F : Sheaf J (Type v)) : LocalizationSite J F ⥤ C :=
  CostructuredArrow.proj yoneda F.obj

/-- The topology on `C/F` induced by the topology on `C`. -/
abbrev localizationTopology (F : Sheaf J (Type v)) :=
  (localizationProjection J F).restrictedTopology J

/-- The localization projection is continuous. -/
theorem localizationProjection_isContinuous (F : Sheaf J (Type v)) :
    (localizationProjection J F).IsContinuous (localizationTopology J F) J :=
  (F.property.exists_sheafEquivalence_costructuredArrow_yoneda).2.2.choose

private abbrev localizationSiteObject (F : Sheaf J (Type v)) (U : C)
    (s : F.obj.obj (op U)) : LocalizationSite J F :=
  CostructuredArrow.mk (yonedaEquiv.symm s)

private def localizationSiteHom (F : Sheaf J (Type v)) {U V : C}
    (f : V ⟶ U) (t : F.obj.obj (op U)) (s : F.obj.obj (op V))
  (h : F.obj.map f.op t = s) :
    localizationSiteObject J F V s ⟶ localizationSiteObject J F U t :=
  CostructuredArrow.homMk f (by
    change yoneda.map f ≫ yonedaEquiv.symm t = yonedaEquiv.symm s
    rw [← h]
    exact yonedaEquiv_symm_naturality_left f F.obj t)

private lemma localizationSiteObject_yonedaEquiv (F : Sheaf J (Type v))
    (X : LocalizationSite J F) :
    localizationSiteObject J F X.left (yonedaEquiv X.hom) = X := by
  dsimp [localizationSiteObject]
  rw [CostructuredArrow.eq_mk X]
  congr 1
  exact Equiv.apply_symm_apply _ _

/-! The direct sum indexed by sections of `F`, with restriction maps induced by `F` and `H`. -/

private noncomputable def localizationIndexedSum (F : Sheaf J (Type v))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)) :
    Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ) where
  obj U := colimit ((Functor.const (Discrete (F.obj.obj U))).obj (H.obj U))
  map {U V} f := by
    let S := (Functor.const (Discrete (F.obj.obj U))).obj (H.obj U)
    let T := (Functor.const (Discrete (F.obj.obj V))).obj (H.obj V)
    exact colimit.desc S
      { pt := colimit T
        ι :=
          { app := fun s => H.map f ≫ colimit.ι T (Discrete.mk (F.obj.map f s.as))
            naturality := by
              rintro ⟨s⟩ ⟨t⟩ ⟨⟨rfl⟩⟩
              simp } }
  map_id U := by
    apply colimit.hom_ext
    intro s
    simp only [Functor.const_obj_obj, colimit.ι_desc, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
    rw [F.obj.map_id]
    rfl
  map_comp {U V W} f g := by
    apply colimit.hom_ext
    intro s
    simp only [Functor.const_obj_obj, colimit.ι_desc, Functor.map_comp,
      Category.assoc, colimit.ι_desc_assoc]
    rw [F.obj.map_comp]
    rfl

private noncomputable def localizationIndexedSumι (F : Sheaf J (Type v))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)) (U : Cᵒᵖ)
    (s : F.obj.obj U) : H.obj U ⟶ (localizationIndexedSum J F H).obj U :=
  colimit.ι ((Functor.const (Discrete (F.obj.obj U))).obj (H.obj U)) (Discrete.mk s)

private noncomputable def localizationIndexedSumUnit (F : Sheaf J (Type v))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)) :
    (localizationProjection J F).op ⋙ H ⟶
      (localizationProjection J F).op ⋙ localizationIndexedSum J F H where
  app X := localizationIndexedSumι J F H (op X.unop.left) (yonedaEquiv X.unop.hom)
  naturality {X Y} f := by
    simp only [Functor.comp_obj, Functor.comp_map]
    have hs : F.obj.map (f.unop.left.op) (yonedaEquiv X.unop.hom) =
        yonedaEquiv Y.unop.hom := by
      apply (Equiv.injective yonedaEquiv.symm)
      rw [← yonedaEquiv_symm_naturality_left (F := F.obj) f.unop.left
        (yonedaEquiv X.unop.hom)]
      simp only [Equiv.symm_apply_apply]
      exact CostructuredArrow.w f.unop
    dsimp [localizationIndexedSumι, localizationIndexedSum]
    rw [colimit.ι_desc]
    dsimp
    rw [hs]

private noncomputable def localizationIndexedSumToLan (F : Sheaf J (Type v))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ))
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P] :
    localizationIndexedSum J F H ⟶
      (localizationProjection J F).op.lan.obj
        ((localizationProjection J F).op ⋙ H) where
  app U := by
    let P := (localizationProjection J F).op ⋙ H
    let adj := (localizationProjection J F).op.lanAdjunction
      (ModuleCat.{v} (ULift.{v} ℤ))
    let D := (Functor.const (Discrete (F.obj.obj U))).obj (H.obj U)
    exact colimit.desc D
      { pt := ((localizationProjection J F).op.lan.obj P).obj U
        ι :=
          { app := fun s =>
              (adj.unit.app P).app (op (localizationSiteObject J F U.unop s.as))
            naturality := by
              rintro ⟨s⟩ ⟨t⟩ ⟨⟨rfl⟩⟩
              simp } }
  naturality {U V} f := by
    apply colimit.hom_ext
    intro s
    dsimp [localizationIndexedSum]
    have h : H.map f ≫
        (((localizationProjection J F).op.lanAdjunction
          (ModuleCat.{v} (ULift.{v} ℤ))).unit.app
            ((localizationProjection J F).op ⋙ H)).app
          (op (localizationSiteObject J F V.unop (F.obj.map f s.as))) =
        (((localizationProjection J F).op.lanAdjunction
          (ModuleCat.{v} (ULift.{v} ℤ))).unit.app
            ((localizationProjection J F).op ⋙ H)).app
          (op (localizationSiteObject J F U.unop s.as)) ≫
        ((localizationProjection J F).op.lan.obj
          ((localizationProjection J F).op ⋙ H)).map f :=
      (((localizationProjection J F).op.lanAdjunction
        (ModuleCat.{v} (ULift.{v} ℤ))).unit.app
          ((localizationProjection J F).op ⋙ H)).naturality
        (localizationSiteHom J F f.unop s.as (F.obj.map f s.as) rfl).op
    simpa only [Functor.comp_obj, Functor.comp_map, Opposite.op_unop,
      Opposite.unop_op, colimit.ι_desc_assoc, Category.assoc, colimit.ι_desc] using h

private noncomputable def localizationLanToIndexedSum (F : Sheaf J (Type v))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ))
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P] :
    ((localizationProjection J F).op.lan.obj
      ((localizationProjection J F).op ⋙ H)) ⟶ localizationIndexedSum J F H :=
  (((localizationProjection J F).op.lanAdjunction (ModuleCat.{v} (ULift.{v} ℤ))).homEquiv
    ((localizationProjection J F).op ⋙ H) (localizationIndexedSum J F H)).symm
      (localizationIndexedSumUnit J F H)

private noncomputable def localizationIndexedSumTensorApp
    (F : Sheaf J (Type v)) (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ))
    (U : Cᵒᵖ) :
    ((localizationIndexedSum J F
      ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ))))).obj U) ⊗
        H.obj U ≅ (localizationIndexedSum J F H).obj U := by
  let D := (Functor.const (Discrete (F.obj.obj U))).obj
    (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ)))
  let T := MonoidalCategory.tensorLeft (H.obj U)
  let e : D ⋙ T ≅ (Functor.const (Discrete (F.obj.obj U))).obj (H.obj U) :=
    NatIso.ofComponents (fun _ => MonoidalCategory.rightUnitor (H.obj U)) (by
      rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl⟩⟩
      simp)
  exact BraidedCategory.braiding
      ((localizationIndexedSum J F
        ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ))))).obj U)
      (H.obj U) ≪≫ CategoryTheory.preservesColimitIso T D ≪≫
    HasColimit.isoOfNatIso e

private noncomputable def localizationIndexedSumTensorInvApp
    (F : Sheaf J (Type v)) (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ))
    (U : Cᵒᵖ) :
    (localizationIndexedSum J F H).obj U ⟶
      ((localizationIndexedSum J F
        ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ))))).obj U) ⊗
        H.obj U := by
  let D := (Functor.const (Discrete (F.obj.obj U))).obj (H.obj U)
  exact colimit.desc D
    { pt := ((localizationIndexedSum J F
        ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ))))).obj U) ⊗ H.obj U
      ι :=
        { app := fun s =>
            (MonoidalCategory.leftUnitor (H.obj U)).inv ≫
              MonoidalCategory.tensorHom
                (localizationIndexedSumι J F
                  ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ)))) U s.as)
                (𝟙 (H.obj U))
          naturality := by
            rintro ⟨s⟩ ⟨t⟩ ⟨⟨rfl⟩⟩
            simp } }

private lemma localizationIndexedSumTensorInvApp_eq_inv
    (F : Sheaf J (Type v)) (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ))
    (U : Cᵒᵖ) :
    localizationIndexedSumTensorInvApp J F H U =
      (localizationIndexedSumTensorApp J F H U).inv := by
  apply colimit.hom_ext
  intro s
  simp [localizationIndexedSumTensorInvApp, localizationIndexedSumTensorApp,
    localizationIndexedSum, localizationIndexedSumι,
    Category.assoc]

private noncomputable def localizationIndexedSumTensorInv
    (F : Sheaf J (Type v)) (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)) :
    localizationIndexedSum J F H ⟶
      localizationIndexedSum J F
        ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ)))) ⊗ H where
  app U := localizationIndexedSumTensorInvApp J F H U
  naturality {U V} f := by
    apply colimit.hom_ext
    intro s
    let L := localizationIndexedSum J F
      ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ))))
    let iU := localizationIndexedSumι J F
      ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ)))) U s.as
    let iV := localizationIndexedSumι J F
      ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ)))) V
        (F.obj.map f s.as)
    let jU := localizationIndexedSumι J F H U s.as
    let jV := localizationIndexedSumι J F H V (F.obj.map f s.as)
    have hi : iU ≫ L.map f = iV := by
      dsimp [iU, iV, L, localizationIndexedSumι, localizationIndexedSum]
      rw [colimit.ι_desc]
      simp
    have hmap : jU ≫ (localizationIndexedSum J F H).map f = H.map f ≫ jV := by
      dsimp [jU, jV, localizationIndexedSumι, localizationIndexedSum]
      rw [colimit.ι_desc]
    have hgen (W : Cᵒᵖ) (t : F.obj.obj W) :
        localizationIndexedSumι J F H W t ≫ localizationIndexedSumTensorInvApp J F H W =
          (MonoidalCategory.leftUnitor (H.obj W)).inv ≫
            (localizationIndexedSumι J F
              ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ)))) W t ▷ H.obj W) := by
      dsimp [localizationIndexedSumTensorInvApp, localizationIndexedSumι, localizationIndexedSum]
      rw [colimit.ι_desc]
      simp [MonoidalCategory.tensorHom_def]
    have hgenU := hgen U s.as
    have hgenV := hgen V (F.obj.map f s.as)
    change jU ≫ (localizationIndexedSum J F H).map f ≫
        localizationIndexedSumTensorInvApp J F H V =
      jU ≫ localizationIndexedSumTensorInvApp J F H U ≫
        (L.map f ⊗ₘ H.map f)
    rw [reassoc_of% hmap, hgenV, reassoc_of% hgenU]
    refine (MonoidalCategory.leftUnitor_inv_comp_tensorHom iV (H.map f)).symm.trans ?_
    rw [← hi]
    simp [MonoidalCategory.tensorHom_def, L]
    rfl

private noncomputable def localizationIndexedSumTensorInvIso
    (F : Sheaf J (Type v)) (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)) :
    localizationIndexedSum J F H ≅
      localizationIndexedSum J F
        ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ)))) ⊗ H := by
  have (U : Cᵒᵖ) : IsIso ((localizationIndexedSumTensorInv J F H).app U) := by
    change IsIso (localizationIndexedSumTensorInvApp J F H U)
    rw [localizationIndexedSumTensorInvApp_eq_inv J F H U]
    infer_instance
  have := NatIso.isIso_of_isIso_app (localizationIndexedSumTensorInv J F H)
  exact asIso (localizationIndexedSumTensorInv J F H)

private lemma localizationIndexedSumUnit_comp_toLan (F : Sheaf J (Type v))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ))
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P] :
    localizationIndexedSumUnit J F H ≫
      Functor.whiskerLeft (localizationProjection J F).op
        (localizationIndexedSumToLan J F H) =
      ((localizationProjection J F).op.lanAdjunction
        (ModuleCat.{v} (ULift.{v} ℤ))).unit.app
          ((localizationProjection J F).op ⋙ H) := by
  apply NatTrans.ext
  funext X
  let P := (localizationProjection J F).op ⋙ H
  let η := ((localizationProjection J F).op.lanAdjunction
    (ModuleCat.{v} (ULift.{v} ℤ))).unit.app P
  let A := localizationSiteObject J F X.unop.left (yonedaEquiv X.unop.hom)
  have hA : A = X.unop := localizationSiteObject_yonedaEquiv J F X.unop
  let e : op A ⟶ X := eqToHom (congrArg op hA)
  dsimp [NatTrans.comp_app, Functor.whiskerLeft_app,
    localizationIndexedSumUnit, localizationIndexedSumι,
    localizationIndexedSumToLan, localizationIndexedSum]
  rw [colimit.ι_desc]
  simpa [η, P, e, A, hA, Functor.comp_map, Functor.op_map,
    Functor.comp_obj, Functor.op_obj, localizationProjection,
    CostructuredArrow.proj_map, CostructuredArrow.proj_obj] using (η.naturality e).symm

private lemma unit_comp_whiskerLeft_localizationLanToIndexedSum (F : Sheaf J (Type v))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ))
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P] :
    (((localizationProjection J F).op.lanAdjunction
      (ModuleCat.{v} (ULift.{v} ℤ))).unit.app ((localizationProjection J F).op ⋙ H)) ≫
      Functor.whiskerLeft (localizationProjection J F).op
        (localizationLanToIndexedSum J F H) = localizationIndexedSumUnit J F H := by
  exact (((localizationProjection J F).op.lanAdjunction _).homEquiv _ _).apply_symm_apply _

private lemma localizationLanToIndexedSum_comp_toLan (F : Sheaf J (Type v))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ))
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P] :
    localizationLanToIndexedSum J F H ≫ localizationIndexedSumToLan J F H =
      𝟙 _ := by
  let G := (localizationProjection J F).op
  let P := G ⋙ H
  let ψ := localizationLanToIndexedSum J F H
  let φ := localizationIndexedSumToLan J F H
  let adj := G.lanAdjunction (ModuleCat.{v} (ULift.{v} ℤ))
  let η := adj.unit.app P
  have hψ : η ≫ Functor.whiskerLeft G ψ = localizationIndexedSumUnit J F H :=
    unit_comp_whiskerLeft_localizationLanToIndexedSum J F H
  apply (adj.homEquiv P (G.lan.obj P)).injective
  change η ≫ Functor.whiskerLeft G (ψ ≫ φ) =
    η ≫ Functor.whiskerLeft G (𝟙 (G.lan.obj P))
  rw [Functor.whiskerLeft_comp, ← Category.assoc, hψ, localizationIndexedSumUnit_comp_toLan J F H]
  rfl

private lemma localizationIndexedSumToLan_comp_lanToIndexedSum
    (F : Sheaf J (Type v))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ))
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P] :
    localizationIndexedSumToLan J F H ≫ localizationLanToIndexedSum J F H =
      𝟙 _ := by
  apply NatTrans.ext
  funext U
  apply colimit.hom_ext
  intro s
  let A := localizationSiteObject J F U.unop s.as
  let η := ((localizationProjection J F).op.lanAdjunction
    (ModuleCat.{v} (ULift.{v} ℤ))).unit.app
      ((localizationProjection J F).op ⋙ H)
  have hφ : localizationIndexedSumι J F H U s.as ≫
      (localizationIndexedSumToLan J F H).app U = η.app (op A) := by
    dsimp [localizationIndexedSumι, localizationIndexedSumToLan,
      localizationIndexedSum]
    rw [colimit.ι_desc]
  have hψA := congrArg (fun t => t.app (op A))
    (unit_comp_whiskerLeft_localizationLanToIndexedSum J F H)
  calc
    localizationIndexedSumι J F H U s.as ≫
        (localizationIndexedSumToLan J F H).app U ≫
          (localizationLanToIndexedSum J F H).app U =
        η.app (op A) ≫ (localizationLanToIndexedSum J F H).app U := by
          rw [← Category.assoc, hφ]
    _ = (localizationIndexedSumUnit J F H).app (op A) := by
          simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
            Functor.comp_obj, localizationProjection,
            Functor.op_obj, CostructuredArrow.proj_obj,
            Opposite.unop_op, Opposite.op_unop, A,
            localizationSiteObject, CostructuredArrow.mk_left] using hψA
    _ = localizationIndexedSumι J F H U s.as := by
          simp [localizationIndexedSumUnit, A, localizationSiteObject]

private noncomputable def localizationLanIndexedSumIso (F : Sheaf J (Type v))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ))
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P] :
    ((localizationProjection J F).op.lan.obj
      ((localizationProjection J F).op ⋙ H)) ≅ localizationIndexedSum J F H :=
  ⟨localizationLanToIndexedSum J F H, localizationIndexedSumToLan J F H,
    localizationLanToIndexedSum_comp_toLan J F H,
    localizationIndexedSumToLan_comp_lanToIndexedSum J F H⟩

private noncomputable def localizationLanTensorIso (F : Sheaf J (Type v))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ))
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P] :
    ((localizationProjection J F).op.lan.obj
      ((localizationProjection J F).op ⋙ H)) ≅
      ((localizationProjection J F).op.lan.obj
        ((localizationProjection J F).op ⋙
          ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ)))))) ⊗ H :=
  localizationLanIndexedSumIso J F H ≪≫ localizationIndexedSumTensorInvIso J F H ≪≫
    Functor.mapIso (MonoidalCategory.tensorRight H)
      (localizationLanIndexedSumIso J F
        ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ))))).symm

private noncomputable def localizationSheafifiedLanTensorIso (F : Sheaf J (Type v))
    [HasWeakSheafify J (ModuleCat.{v} (ULift.{v} ℤ))]
    [(J.W (A := ModuleCat.{v} (ULift.{v} ℤ))).IsMonoidal]
    (H : Sheaf J (ModuleCat.{v} (ULift.{v} ℤ)))
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P] :
    let := Sheaf.monoidalCategory J (ModuleCat.{v} (ULift.{v} ℤ))
    ((presheafToSheaf J (ModuleCat.{v} (ULift.{v} ℤ))).obj
      ((localizationProjection J F).op.lan.obj
        ((localizationProjection J F).op ⋙ H.obj))) ≅
    ((presheafToSheaf J (ModuleCat.{v} (ULift.{v} ℤ))).obj
      ((localizationProjection J F).op.lan.obj
        ((localizationProjection J F).op ⋙
          ((Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ))))))) ⊗ H := by
  let A := ModuleCat.{v} (ULift.{v} ℤ)
  let I := (Functor.const Cᵒᵖ).obj (𝟙_ A)
  let L := presheafToSheaf J A
  let := Sheaf.monoidalCategory J A
  let : L.Monoidal := inferInstance
  exact L.mapIso (localizationLanTensorIso J F H.obj) ≪≫
    (Functor.Monoidal.μIso L
      ((localizationProjection J F).op.lan.obj ((localizationProjection J F).op ⋙ I))
      H.obj).symm ≪≫
    Functor.mapIso (MonoidalCategory.tensorLeft
      (L.obj ((localizationProjection J F).op.lan.obj ((localizationProjection J F).op ⋙ I))))
      (asIso ((sheafificationAdjunction J A).counit.app H))

/-- The inverse-image functor `j⁻¹` on abelian sheaves for localization at `F`. -/
noncomputable def abelianLocalizationInverseImage (F : Sheaf J (Type v)) :
    Sheaf J (ModuleCat.{v} (ULift.{v} ℤ)) ⥤
      Sheaf (localizationTopology J F) (ModuleCat.{v} (ULift.{v} ℤ)) := by
  let := localizationProjection_isContinuous J F
  exact (localizationProjection J F).sheafPushforwardContinuous
    (ModuleCat.{v} (ULift.{v} ℤ)) (localizationTopology J F) J

/-- Extension by zero `j_!` on abelian sheaves for localization at `F`, given
by left Kan extension and sheafification. -/
noncomputable def abelianLocalizationShriek (F : Sheaf J (Type v))
    [HasWeakSheafify J (ModuleCat.{v} (ULift.{v} ℤ))]
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P] :
    Sheaf (localizationTopology J F) (ModuleCat.{v} (ULift.{v} ℤ)) ⥤
      Sheaf J (ModuleCat.{v} (ULift.{v} ℤ)) := by
  let := localizationProjection_isContinuous J F
  exact Functor.sheafPullbackConstruction.sheafPullback
    (localizationProjection J F) (ModuleCat.{v} (ULift.{v} ℤ))
      (localizationTopology J F) J

private noncomputable def localizationShriekUnitLanIso (F : Sheaf J (Type v))
    [HasWeakSheafify J (ModuleCat.{v} (ULift.{v} ℤ))]
    [HasWeakSheafify (localizationTopology J F) (ModuleCat.{v} (ULift.{v} ℤ))]
    [((localizationTopology J F).W
      (A := ModuleCat.{v} (ULift.{v} ℤ))).IsMonoidal]
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P] :
    let := Sheaf.monoidalCategory (localizationTopology J F)
      (ModuleCat.{v} (ULift.{v} ℤ))
    (abelianLocalizationShriek J F).obj (𝟙_ _) ≅
      (presheafToSheaf J (ModuleCat.{v} (ULift.{v} ℤ))).obj
        ((localizationProjection J F).op.lan.obj
          ((localizationProjection J F).op ⋙
            (Functor.const Cᵒᵖ).obj (𝟙_ (ModuleCat.{v} (ULift.{v} ℤ))))) := by
  let A := ModuleCat.{v} (ULift.{v} ℤ)
  let K := localizationTopology J F
  let G := localizationProjection J F
  let I := (Functor.const Cᵒᵖ).obj (𝟙_ A)
  let P := G.op ⋙ I
  let L₁ := presheafToSheaf K A
  let := localizationProjection_isContinuous J F
  let : MonoidalCategory (Sheaf K A) := Sheaf.monoidalCategory K A
  let : L₁.Monoidal := inferInstance
  let adjShriek := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A K J
  let adjLoc := sheafificationAdjunction K A
  let adjBase := sheafificationAdjunction J A
  let adjLan := G.op.lanAdjunction A
  let e := (adjLoc.comp adjShriek).leftAdjointUniq (adjLan.comp adjBase)
  exact (abelianLocalizationShriek J F).mapIso (Functor.Monoidal.εIso L₁) ≪≫
    e.app P

/-- **Stacks Project, Tag 0EYY.** Extension by zero of the restriction of an
abelian sheaf is its tensor product with the extension by zero of the constant
integer sheaf. -/
@[no_expose]
noncomputable def jShriekPullbackIsoTensor (F : Sheaf J (Type v))
    [HasWeakSheafify J (ModuleCat.{v} (ULift.{v} ℤ))]
    [HasWeakSheafify (localizationTopology J F) (ModuleCat.{v} (ULift.{v} ℤ))]
    [(J.W (A := ModuleCat.{v} (ULift.{v} ℤ))).IsMonoidal]
    [((localizationTopology J F).W
      (A := ModuleCat.{v} (ULift.{v} ℤ))).IsMonoidal]
    [∀ (P : (LocalizationSite J F)ᵒᵖ ⥤ ModuleCat.{v} (ULift.{v} ℤ)),
      (localizationProjection J F).op.HasLeftKanExtension P]
    (H : Sheaf J (ModuleCat.{v} (ULift.{v} ℤ))) :
    let := Sheaf.monoidalCategory J (ModuleCat.{v} (ULift.{v} ℤ))
    let := Sheaf.monoidalCategory (localizationTopology J F)
      (ModuleCat.{v} (ULift.{v} ℤ))
    (abelianLocalizationShriek J F).obj
        ((abelianLocalizationInverseImage J F).obj H) ≅
      (abelianLocalizationShriek J F).obj (𝟙_ _) ⊗ H := by
  let := Sheaf.monoidalCategory J (ModuleCat.{v} (ULift.{v} ℤ))
  let := Sheaf.monoidalCategory (localizationTopology J F)
    (ModuleCat.{v} (ULift.{v} ℤ))
  exact localizationSheafifiedLanTensorIso J F H ≪≫
    (tensorRight H).mapIso (localizationShriekUnitLanIso J F).symm

end Stacks.Sites.Localization

end
