module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending étale schemes over a limit of schemes

Let `D` be a cofiltered inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms and limit `c`. A scheme étale and of finite presentation over the limit is
the base change of a scheme étale and of finite presentation over some stage ([Stacks, Tag 01ZM]
and [Stacks, Tag 07RP]). Morphisms from the base change to the limit of a scheme over a stage, into
a scheme locally of finite presentation over that stage, come from a later stage, and two of them
agreeing over the limit agree at a later stage ([Stacks, Tag 01ZC]).

## Main results

* `AlgebraicGeometry.Scheme.exists_etale_isPullback_of_isLimit`: an étale morphism of finite
  presentation to the limit is a base change of one to a stage.
* `AlgebraicGeometry.Scheme.exists_stage_hom_of_baseChange`: a morphism over the limit into a
  scheme locally of finite presentation over a stage comes from a later stage.
* `AlgebraicGeometry.Scheme.exists_stage_eq_of_baseChange`: two morphisms into a scheme locally of
  finite type over a stage which agree over the limit agree at a later stage.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  (hc : IsLimit c) [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- **An étale morphism of finite presentation to the limit of a cofiltered system of
quasi-compact and quasi-separated schemes with affine transition morphisms is the base change of
an étale morphism of finite presentation to a stage.** -/
theorem exists_etale_isPullback_of_isLimit {M : Scheme.{u}} (p : M ⟶ c.pt) [Etale p]
    [QuasiCompact p] [QuasiSeparated p] :
    ∃ (i : I) (M₀ : Scheme.{u}) (p₀ : M₀ ⟶ D.obj i) (m : M ⟶ M₀),
      Etale p₀ ∧ QuasiCompact p₀ ∧ QuasiSeparated p₀ ∧ IsPullback m p p₀ (c.π.app i) := by
  obtain ⟨i, X, hX, ⟨e⟩⟩ := LimitFPObjectDescent.exists_model_of_finitePresentation D c hc
    (Over.mk p) ⟨(inferInstance : LocallyOfFinitePresentation p),
      (inferInstance : QuasiCompact p), (inferInstance : QuasiSeparated p)⟩
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let f₀ : X ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk X.hom (Category.comp_id _)
  have he : e.hom.left ≫ pullback.snd X.hom (c.π.app i) = p := Over.w e.hom
  have hiff : ∀ {T : Scheme.{u}} (g : T ⟶ D.obj i),
      Etale ((Over.pullback g).map f₀).left ↔ Etale (pullback.snd X.hom g) := fun g => by
    have hw : ((Over.pullback g).map f₀).left ≫ pullback.snd (𝟙 (D.obj i)) g =
        pullback.snd X.hom g := Over.w ((Over.pullback g).map f₀)
    rw [← hw]
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @Etale) _ _).symm
  have hinv : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id]; rfl
  have hsnd : pullback.snd X.hom (c.π.app i) = e.inv.left ≫ p := by
    calc pullback.snd X.hom (c.π.app i)
        = (e.inv.left ≫ e.hom.left) ≫ pullback.snd X.hom (c.π.app i) := by
          rw [hinv, Category.id_comp]
      _ = e.inv.left ≫ p := by rw [Category.assoc, he]
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have : Etale ((Over.pullback (c.π.app i)).map f₀).left := by
    rw [hiff, hsnd]
    infer_instance
  have : LocallyOfFinitePresentation f₀.left := inferInstanceAs (LocallyOfFinitePresentation X.hom)
  obtain ⟨j, hj⟩ := exists_etale_pullback_of_isLimit D c hc i X (Over.mk (𝟙 _)) f₀
  rw [hiff] at hj
  have hcw : c.π.app j.left ≫ D.map j.hom = c.π.app i := c.w j.hom
  let m : M ⟶ pullback X.hom (D.map j.hom) :=
    pullback.lift (e.hom.left ≫ pullback.fst X.hom (c.π.app i)) (p ≫ c.π.app j.left) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, he, Category.assoc, hcw])
  have hpb : IsPullback (e.hom.left ≫ pullback.fst X.hom (c.π.app i)) p X.hom (c.π.app i) :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, he]⟩
      ((Over.forget _).mapIso e) rfl he
  refine ⟨j.left, _, pullback.snd X.hom (D.map j.hom), m, hj, inferInstance, inferInstance, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rwa [pullback.lift_fst, hcw]

omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **A morphism from the base change to the limit of a scheme over a stage, into a scheme locally
of finite presentation over that stage, comes from a later stage** ([Stacks, Tag 01ZC]). -/
@[sga "3 VIB 3.8" "partial"]
theorem exists_stage_hom_of_baseChange (i : I) (X : Over (D.obj i)) [CompactSpace X.left]
    [QuasiSeparatedSpace X.left] {Y : Scheme.{u}} (y : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation y] (a : pullback (c.π.app i) X.hom ⟶ Y)
    (ha : a ≫ y = pullback.snd _ _ ≫ X.hom) :
    ∃ (j : Over i) (g : pullback (D.map j.hom) X.hom ⟶ Y),
      g ≫ y = pullback.snd _ _ ≫ X.hom ∧
        baseChangeTransition (D.map j.hom) (c.π.app i) (c.π.app j.left) (by simp) X ≫ g = a := by
  have : ∀ {a b : Over i} (g : a ⟶ b), IsAffineHom ((baseChangeDiagram D i X).map g) :=
    fun g => isAffineHom_baseChangeDiagram_map D i X g
  have : ∀ a : Over i, CompactSpace ((baseChangeDiagram D i X).obj a) :=
    compactSpace_baseChangeDiagram_obj D i X
  have : ∀ a : Over i, QuasiSeparatedSpace ((baseChangeDiagram D i X).obj a) :=
    quasiSeparatedSpace_baseChangeDiagram_obj D i X
  obtain ⟨j, g, hg₁, hg₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (baseChangeDiagram D i X) (baseChangeStructureMap D i X) y (baseChangeCone D c i X)
    (baseChangeConeIsLimit D hc i X) a (by
      ext j
      change baseChangeTransition (D.map j.hom) (c.π.app i) (c.π.app j.left) (by simp) X ≫
        (pullback.snd (D.map j.hom) X.hom ≫ X.hom) = a ≫ y
      rw [← Category.assoc, baseChangeTransition_snd, ha])
  exact ⟨j, g, hg₂, hg₁⟩

omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **Two morphisms from a scheme over a stage, into a scheme locally of finite type over that
stage, which agree after base change to the limit agree after base change to a later stage**
([Stacks, Tag 01ZC]). -/
theorem exists_stage_eq_of_baseChange (i : I) (X : Over (D.obj i)) [CompactSpace X.left]
    {Y : Scheme.{u}} (y : Y ⟶ D.obj i) [LocallyOfFiniteType y] (u v : X.left ⟶ Y)
    (hu : u ≫ y = X.hom) (hv : v ≫ y = X.hom)
    (h : pullback.snd (c.π.app i) X.hom ≫ u = pullback.snd (c.π.app i) X.hom ≫ v) :
    ∃ (j : I) (e : j ⟶ i), pullback.snd (D.map e) X.hom ≫ u = pullback.snd (D.map e) X.hom ≫ v := by
  have : ∀ {a b : Over i} (g : a ⟶ b), IsAffineHom ((baseChangeDiagram D i X).map g) :=
    fun g => isAffineHom_baseChangeDiagram_map D i X g
  have : ∀ a : Over i, CompactSpace ((baseChangeDiagram D i X).obj a) :=
    compactSpace_baseChangeDiagram_obj D i X
  obtain ⟨k, hik, hk⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (baseChangeDiagram D i X) (baseChangeStructureMap D i X) y (baseChangeCone D c i X)
    (baseChangeConeIsLimit D hc i X) (i := Over.mk (𝟙 i))
    (pullback.snd (D.map (𝟙 i)) X.hom ≫ u) (pullback.snd (D.map (𝟙 i)) X.hom ≫ v)
    (by change pullback.snd _ _ ≫ X.hom = (pullback.snd _ _ ≫ u) ≫ y; rw [Category.assoc, hu])
    (by change pullback.snd _ _ ≫ X.hom = (pullback.snd _ _ ≫ v) ≫ y; rw [Category.assoc, hv])
    (by
      change baseChangeTransition (D.map (𝟙 i)) (c.π.app i) (c.π.app i) (by simp) X ≫
        pullback.snd _ _ ≫ u = baseChangeTransition (D.map (𝟙 i)) (c.π.app i) (c.π.app i)
          (by simp) X ≫ pullback.snd _ _ ≫ v
      rw [← Category.assoc, ← Category.assoc, baseChangeTransition_snd, h])
  refine ⟨k.left, k.hom, ?_⟩
  have hw : D.map hik.left ≫ D.map (𝟙 i) = D.map k.hom := by
    rw [← D.map_comp]
    exact congrArg D.map (by simpa using Over.w hik)
  change baseChangeTransition (D.map (𝟙 i)) (D.map k.hom) (D.map hik.left) hw X ≫
      pullback.snd _ _ ≫ u = baseChangeTransition (D.map (𝟙 i)) (D.map k.hom) (D.map hik.left)
        hw X ≫ pullback.snd _ _ ≫ v at hk
  rwa [← Category.assoc, ← Category.assoc, baseChangeTransition_snd] at hk

end AlgebraicGeometry.Scheme

end
