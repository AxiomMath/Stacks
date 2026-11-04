module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Unconditional
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.ChowQcqs.Basic
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamilies
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of a polarized family to a finite stage

Let `S = lim Sᵢ` be the limit of a cofiltered inverse system of affine schemes. A proper, flat,
finitely presented `X ⟶ S` carrying a relatively ample invertible module is the base change of
such a datum over some `Sᵢ`.

## References

* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The base change of an identity morphism is an isomorphism. -/
private lemma isIso_pullback_snd_id {A W : Scheme.{u}} (g : W ⟶ A) :
    IsIso (pullback.snd (𝟙 A) g) := by
  refine ⟨(pullback.lift g (𝟙 W) (by simp) : W ⟶ pullback (𝟙 A) g), ?_, ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst]
      exact pullback.condition.symm.trans (Category.comp_id _)
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · exact pullback.lift_snd _ _ _

/-- A morphism of a slice category, read as a morphism into the terminal object. -/
private def toSliceTerminal {A : Scheme.{u}} (X : Over A) : X ⟶ Over.mk (𝟙 A) :=
  Over.homMk X.hom (Category.comp_id X.hom)

/-- A base-change-stable property holds of the base change of the structure morphism of a slice
object exactly when it holds of the base change of its morphism into the terminal object. -/
private lemma prop_overPullback_map_toSliceTerminal_iff (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {A W : Scheme.{u}} (g : W ⟶ A) (X : Over A) :
    P ((Over.pullback g).map (toSliceTerminal X)).left ↔ P (pullback.snd X.hom g) := by
  have hw : ((Over.pullback g).map (toSliceTerminal X)).left ≫ pullback.snd (𝟙 A) g =
      pullback.snd X.hom g := Over.w ((Over.pullback g).map (toSliceTerminal X))
  have hiso := isIso_pullback_snd_id (A := A) g
  have key : P (((Over.pullback g).map (toSliceTerminal X)).left ≫ pullback.snd (𝟙 A) g) ↔
      P ((Over.pullback g).map (toSliceTerminal X)).left :=
    P.cancel_right_of_respectsIso _ _
  rw [hw] at key
  exact key.symm

/-- A property stable under base change and under isomorphism survives passage from a stage to a
later one. -/
private lemma prop_overPullback_of_le {J : Type u} [Category.{u} J] (E : J ⥤ Scheme.{u}) {j₀ : J}
    {X Y : Over (E.obj j₀)} (f₀ : X ⟶ Y) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {j k : J} (e : j ⟶ j₀) (g : k ⟶ j)
    (hp : P ((Over.pullback (E.map e)).map f₀).left) :
    P ((Over.pullback (E.map (g ≫ e))).map f₀).left := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [E.map_comp]
  refine (MorphismProperty.arrow_mk_iso_iff P (Arrow.isoMk
    ((Over.forget _).mapIso ((Over.pullbackComp (E.map g) (E.map e)).app X))
    ((Over.forget _).mapIso ((Over.pullbackComp (E.map g) (E.map e)).app Y))
    (congrArg (fun z ↦ z.left)
      ((Over.pullbackComp (E.map g) (E.map e)).hom.naturality f₀)).symm)).2 ?_
  exact MorphismProperty.overPullbackMap (P := P) (E.map g) _ hp

/-- Two properties of the base changes of a fixed morphism which persist under passage to later
stages hold at a common stage. -/
private lemma exists_common_stage {J : Type u} [Category.{u} J] [IsCofiltered J] {j₀ : J}
    (P Q : ∀ {j : J}, (j ⟶ j₀) → Prop)
    (hP : ∃ (j : J) (e : j ⟶ j₀), P e) (hQ : ∃ (j : J) (e : j ⟶ j₀), Q e)
    (hPb : ∀ {j k : J} (e : j ⟶ j₀) (g : k ⟶ j), P e → P (g ≫ e))
    (hQb : ∀ {j k : J} (e : j ⟶ j₀) (g : k ⟶ j), Q e → Q (g ≫ e)) :
    ∃ (j : J) (e : j ⟶ j₀), P e ∧ Q e := by
  obtain ⟨j, e, he⟩ := hP
  obtain ⟨k, f, hf⟩ := hQ
  obtain ⟨l, g, h, hcomm⟩ := IsCofiltered.cospan e f
  refine ⟨l, g ≫ e, hPb e g he, ?_⟩
  rw [hcomm]
  exact hQb f h hf

/-- Finite presentation is stable under base change. -/
private lemma finitePresentation_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (hf : FinitePresentation f) :
    FinitePresentation snd :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFinitePresentation) h
      hf.1,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) h hf.2.1,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated) h hf.2.2⟩

/-- A proper, flat, finitely presented morphism to the limit of a cofiltered system of affine
schemes is the base change of a proper, flat, finitely presented morphism over some stage. -/
@[sga "3 VIB 10.0" "(ii), special case"]
lemma exists_stage_properFlatModel {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} (f : X ⟶ c.pt) [IsProper f] [Flat f] (hfp : FinitePresentation f) :
    ∃ (i : I) (Xᵢ : Scheme.{u}) (fᵢ : Xᵢ ⟶ D.obj i) (g : X ⟶ Xᵢ),
      IsProper fᵢ ∧ Flat fᵢ ∧ FinitePresentation fᵢ ∧ IsPullback g f fᵢ (c.π.app i) := by
  have hAff : ∀ {i j : I} (k : i ⟶ j), IsAffineHom (D.map k) := fun _ => inferInstance
  have hCpt : ∀ i : I, CompactSpace (D.obj i) := fun _ => inferInstance
  have hQS : ∀ i : I, QuasiSeparatedSpace (D.obj i) := fun _ => inferInstance
  have hriPr : MorphismProperty.RespectsIso (@IsProper) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hriFl : MorphismProperty.RespectsIso (@Flat) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨i₀, X₀, hfp₀, ⟨e⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc (Over.mk f) hfp
  set eL : X ≅ Limits.pullback X₀.hom (c.π.app i₀) := (Over.forget c.pt).mapIso e with heL
  have hew : eL.hom ≫ pullback.snd X₀.hom (c.π.app i₀) = f := Over.w e.hom
  have hA : IsPullback (eL.hom ≫ pullback.fst X₀.hom (c.π.app i₀)) f X₀.hom (c.π.app i₀) :=
    IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hew]⟩ eL rfl hew
  have hcancel : ∀ (P : MorphismProperty Scheme.{u}) [P.RespectsIso],
      P (pullback.snd X₀.hom (c.π.app i₀)) ↔ P f := by
    intro P _
    rw [← hew]
    exact (P.cancel_left_of_respectsIso eL.hom _).symm
  have : CompactSpace X₀.left :=
    have := hfp₀.2.1
    QuasiCompact.compactSpace_of_compactSpace X₀.hom
  have : QuasiSeparatedSpace X₀.left :=
    have := hfp₀.2.2
    quasiSeparatedSpace_of_quasiSeparated X₀.hom
  have hlft : LocallyOfFiniteType (toSliceTerminal X₀).left :=
    have := hfp₀.1
    inferInstanceAs (LocallyOfFiniteType X₀.hom)
  have hlfp : LocallyOfFinitePresentation (toSliceTerminal X₀).left := hfp₀.1
  have hp0 : IsProper ((Over.pullback (c.π.app i₀)).map (toSliceTerminal X₀)).left :=
    (prop_overPullback_map_toSliceTerminal_iff (@IsProper) _ X₀).mpr ((hcancel _).mpr ‹IsProper f›)
  have hf0 : Flat ((Over.pullback (c.π.app i₀)).map (toSliceTerminal X₀)).left :=
    (prop_overPullback_map_toSliceTerminal_iff (@Flat) _ X₀).mpr ((hcancel _).mpr ‹Flat f›)
  have hT1 : CompactSpace (Over.mk (𝟙 (D.obj i₀))).left := hCpt i₀
  have hT2 : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i₀))).left := hQS i₀
  obtain ⟨j₁, k₁, hp₁⟩ := exists_isProper_baseChange_of_isLimit D c i₀ hc X₀
    (Over.mk (𝟙 (D.obj i₀))) (toSliceTerminal X₀)
  obtain ⟨j₂, k₂, hf₂⟩ := exists_flat_baseChange_of_limitBaseChange D c i₀ X₀
    (Over.mk (𝟙 (D.obj i₀))) (toSliceTerminal X₀) hc
  obtain ⟨i₁, h₁, hpr₁, hfl₁⟩ := exists_common_stage
    (fun {j} (k : j ⟶ i₀) => IsProper ((Over.pullback (D.map k)).map (toSliceTerminal X₀)).left)
    (fun {j} (k : j ⟶ i₀) => Flat ((Over.pullback (D.map k)).map (toSliceTerminal X₀)).left)
    ⟨j₁, k₁, hp₁⟩ ⟨j₂, k₂, hf₂⟩
    (fun k g hp => prop_overPullback_of_le D (toSliceTerminal X₀) (@IsProper) k g hp)
    (fun k g hp => prop_overPullback_of_le D (toSliceTerminal X₀) (@Flat) k g hp)
  have hsq : IsPullback (pullback.fst X₀.hom (D.map h₁)) (pullback.snd X₀.hom (D.map h₁))
      X₀.hom (D.map h₁) := IsPullback.of_hasPullback X₀.hom (D.map h₁)
  have hcond : (eL.hom ≫ pullback.fst X₀.hom (c.π.app i₀)) ≫ X₀.hom =
      (f ≫ c.π.app i₁) ≫ D.map h₁ := by
    rw [hA.w, Category.assoc, c.w h₁]
  refine ⟨i₁, Limits.pullback X₀.hom (D.map h₁), pullback.snd X₀.hom (D.map h₁),
    pullback.lift (eL.hom ≫ pullback.fst X₀.hom (c.π.app i₀)) (f ≫ c.π.app i₁) hcond,
    (prop_overPullback_map_toSliceTerminal_iff (@IsProper) _ X₀).mp hpr₁,
    (prop_overPullback_map_toSliceTerminal_iff (@Flat) _ X₀).mp hfl₁,
    finitePresentation_of_isPullback hsq hfp₀, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, c.w h₁]
  exact hA

/-- The pullback of an invertible sheaf of modules is invertible. -/
private lemma isInvertible_pullback {Y Z : Scheme.{u}} (p : Y ⟶ Z) (M : Z.Modules)
    (hM : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M) :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback p).obj M) :=
  have := hM
  Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback p.toLRSHom.toShHom M

/-- Invertibility of a module on a scheme, in the spelling the ampleness API keys on. -/
private lemma isInvertible_ringedSpace {Z : Scheme.{u}} {M : Z.Modules}
    (h : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M) :
    SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing
        Z.toRingedSpace).property M := h

/-- **Descent of a polarized family to a stage.** Over the limit of a cofiltered inverse system of
affine schemes, a proper, flat, finitely presented morphism carrying a relatively ample invertible
module is the base change of such a datum over some stage. -/
theorem exists_stage_polarizedModel {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} (f : X ⟶ c.pt) [IsProper f] [Flat f] (hfp : FinitePresentation f)
    (L : X.Modules) (hLinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    (hLamp : letI := hLinv; Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ (i : I) (Xᵢ : Scheme.{u}) (fᵢ : Xᵢ ⟶ D.obj i) (Lᵢ : Xᵢ.Modules)
      (hinv : SheafOfModules.IsInvertible Xᵢ.presheaf Xᵢ.ringCatSheaf.2 Lᵢ) (g : X ⟶ Xᵢ),
      IsProper fᵢ ∧ Flat fᵢ ∧ FinitePresentation fᵢ ∧
        (letI := hinv; Stacks.RelativeAmple.IsRelativelyAmple fᵢ Lᵢ) ∧
        IsPullback g f fᵢ (c.π.app i) ∧ Nonempty ((Scheme.Modules.pullback g).obj Lᵢ ≅ L) := by
  obtain ⟨i₁, X₁, f₁, g₁, hpr₁, hfl₁, hfp₁, hpb₁⟩ := exists_stage_properFlatModel D c hc f hfp
  have hAff : ∀ {i j : I} (k : i ⟶ j), IsAffineHom (D.map k) := fun _ => inferInstance
  have ⟨_, hqc, hqs⟩ := hfp₁
  have hX1c : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have hX1q : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated f₁
  have hEaff : ∀ {j k : Over i₁} (g : j ⟶ k), IsAffineHom ((pullbackDiagram D i₁ f₁).map g) :=
    fun g => isAffineHom_pullbackDiagram_map D i₁ f₁ g (hAff g.left)
  have hsnd : ∀ j : Over i₁, IsAffineHom (pullback.snd (D.map j.hom) f₁) := fun j =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback (D.map j.hom) f₁) (hAff j.hom)
  have hqcs : ∀ j : Over i₁, QuasiCompact (pullback.snd (D.map j.hom) f₁) := fun j =>
    have := hAff j.hom
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback (D.map j.hom) f₁) inferInstance
  have hqss : ∀ j : Over i₁, QuasiSeparated (pullback.snd (D.map j.hom) f₁) := fun j =>
    have := hAff j.hom
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback (D.map j.hom) f₁) inferInstance
  have hEc : ∀ j : Over i₁, CompactSpace ((pullbackDiagram D i₁ f₁).obj j) := fun j =>
    have := hqcs j
    (QuasiCompact.compactSpace_of_compactSpace (pullback.snd (D.map j.hom) f₁) :)
  have hEq : ∀ j : Over i₁, QuasiSeparatedSpace ((pullbackDiagram D i₁ f₁).obj j) := fun j =>
    have := hqss j
    (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.map j.hom) f₁) :)
  have hu1 : hpb₁.flip.isoPullback.hom ≫ pullback.fst (c.π.app i₁) f₁ = f :=
    hpb₁.flip.isoPullback_hom_fst
  have hu2 : hpb₁.flip.isoPullback.hom ≫ pullback.snd (c.π.app i₁) f₁ = g₁ :=
    hpb₁.flip.isoPullback_hom_snd
  have hcX : IsLimit ((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom) :=
    (isLimitPullbackCone D c hc i₁ f₁).ofIsoLimit
      (Cone.ext hpb₁.flip.isoPullback (fun j => rfl)).symm
  obtain ⟨j₀, Lj, hLj, ⟨eL⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit
      (pullbackDiagram D i₁ f₁) ((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom)
      hcX L hLinv
  have haffc : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have hampX : Scheme.Modules.IsAmple X L := by
    have := hLinv
    exact (Stacks.AmpleBridge.isAmple_iff_isAmple X L).mp
      ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).mp
        ((Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f L).mpr hLamp))
  have hinvPB : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing
        X.toRingedSpace).property ((Scheme.Modules.pullback
        (((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom).π.app j₀)).obj Lj) :=
    isInvertible_pullback _ Lj hLj
  have hampPB : Scheme.Modules.IsAmple X ((Scheme.Modules.pullback
      (((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom).π.app j₀)).obj Lj) :=
    Scheme.Modules.isAmple_of_iso eL hampX
  have := isInvertible_ringedSpace hLj
  obtain ⟨j', gj, hamp⟩ :=
    Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs
      (pullbackDiagram D i₁ f₁) ((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom)
      hcX j₀ Lj hampPB
  have he1 : (pullbackCone D c i₁ f₁).π.app j' ≫ pullback.fst (D.map j'.hom) f₁ =
      pullback.fst (c.π.app i₁) f₁ ≫ c.π.app j'.left := pullback.lift_fst _ _ _
  have he2 : (pullbackCone D c i₁ f₁).π.app j' ≫ pullback.snd (D.map j'.hom) f₁ =
      pullback.snd (c.π.app i₁) f₁ := pullback.lift_snd _ _ _
  have hmid : ((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom).π.app j' ≫
      pullback.fst (D.map j'.hom) f₁ = f ≫ c.π.app j'.left :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => hpb₁.flip.isoPullback.hom ≫ k) he1).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ c.π.app j'.left) hu1)))
  have hcmp : ((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom).π.app j' ≫
      pullback.snd (D.map j'.hom) f₁ = g₁ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => hpb₁.flip.isoPullback.hom ≫ k) he2).trans hu2)
  have hw : ((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom).π.app j' ≫
      (pullbackDiagram D i₁ f₁).map gj =
    ((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom).π.app j₀ :=
    ((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom).w gj
  refine ⟨j'.left, Limits.pullback (D.map j'.hom) f₁, pullback.fst (D.map j'.hom) f₁,
    (Scheme.Modules.pullback ((pullbackDiagram D i₁ f₁).map gj)).obj Lj,
    isInvertible_pullback _ Lj hLj,
    ((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom).π.app j',
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (D.map j'.hom) f₁).flip hpr₁,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback (D.map j'.hom) f₁).flip hfl₁,
    finitePresentation_of_isPullback
      (IsPullback.of_hasPullback (D.map j'.hom) f₁).flip hfp₁, ?_, ?_, ?_⟩
  · have h1 : SheafOfModules.IsInvertible (Limits.pullback (D.map j'.hom) f₁).presheaf
        (Limits.pullback (D.map j'.hom) f₁).ringCatSheaf.2
        ((Scheme.Modules.pullback ((pullbackDiagram D i₁ f₁).map gj)).obj Lj) :=
      isInvertible_pullback _ Lj hLj
    have := isInvertible_ringedSpace h1
    exact (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple _ _).mp
      ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple
        (pullback.fst (D.map j'.hom) f₁) _).mpr
          ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr hamp))
  · refine IsPullback.of_right ?_ hmid (IsPullback.of_hasPullback (D.map j'.hom) f₁).flip
    have hgoal : IsPullback g₁ f f₁ (c.π.app j'.left ≫ D.map j'.hom) := by
      rw [c.w j'.hom]
      exact hpb₁
    exact cast (congrArg (fun k : X ⟶ X₁ =>
      IsPullback k f f₁ (c.π.app j'.left ≫ D.map j'.hom)) hcmp).symm hgoal
  · exact ⟨(Scheme.Modules.pullbackComp
      (((pullbackCone D c i₁ f₁).extend hpb₁.flip.isoPullback.hom).π.app j')
      ((pullbackDiagram D i₁ f₁).map gj)).app Lj ≪≫
        eqToIso (congrArg (fun k => (Scheme.Modules.pullback k).obj Lj) hw) ≪≫ eL.symm⟩

end AlgebraicGeometry

end
