module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekAssociativity
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompPiece
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompSeparated

/-!
# The map `c` of Stacks 0F79: `(g ∘ f)_! ⟶ g_! ∘ f_!` for `g` separated of finite type

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of a big étale site with `f` and `f ≫ g` locally
quasi-finite and `g` separated and locally of finite type. Here `f_!` and `(f ≫ g)_!` are the
direct images with compact support of locally quasi-finite morphisms (Stacks 0F6R, the
sheafified finite-support direct image) and `g_!` is the proper-support direct image of
Stacks 0F4X. This file constructs the map of the proof of Stacks 0F79,

`c' : (f ≫ g)_! F ⟶ g_!(f_! F)`.

A local generator `(T, s)` of `(f ≫ g)_{p!} F` over `W` — a section `s` of `F` over `X_W`
supported on a support `T ⊆ X_W` finite over `W` — is sent to the generator `(T, s)` of
`f_{p!} F` over `W ×_Z Y`, through `X_{W ×_Z Y} = X_W`: the support `T` is finite over
`W ×_Z Y` because `W ×_Z Y ⟶ W` is separated (`AlgebraicGeometry.SmallEtale.sepCompSupport`).
The resulting section of `f_! F` over `W ×_Z Y` is supported in the image of `T`, which is closed
and proper over `W`, so it is a section of `g_!(f_! F)` over `W`. This gives a morphism of
presheaves `(f ≫ g)_{p!} F ⟶ g_!(f_! F)`, and sheafifying gives `c'`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sepCompApp` — the transported generators over `W`.
* `AlgebraicGeometry.SmallEtale.sepCompProperMap` — the transported generators as a morphism of
  presheaves to the proper-support direct image `g_!(f_! F)`.
* `AlgebraicGeometry.SmallEtale.sepCompShriekMap` — its sheafification
  `(f ≫ g)_! F ⟶ g_!(f_! F)`.

## Main results

* `AlgebraicGeometry.SmallEtale.sepCompApp_naturality` — the transport is natural in `W`.
* `AlgebraicGeometry.SmallEtale.properSupportSections_sepCompApp` — the transported sections
  have support proper over `W`.

## References

* [Stacks Project, Tag 0F79](https://stacks.math.columbia.edu/tag/0F79)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

section Transport

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated (B.inclusion.map g)]

/-- The support attached to a support finite over `W` is monotone in it. -/
public theorem sepCompSupport_mono (W : SmallEtale B Z.obj Z.property)
    {E E₂ : FiniteSupport B (f ≫ g) W} (h : E ≤ E₂) :
    sepCompSupport B f g W E ≤ sepCompSupport B f g W E₂ :=
  Set.preimage_mono h

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The transport of sections supported on a support `E` finite over `W`, through
`X_{W ×_Z Y} = X_W`, to sections supported on any support finite over `W ×_Z Y` with the
underlying set of `AlgebraicGeometry.SmallEtale.sepCompSupport`. -/
public def sepCompGenMap (W : SmallEtale B Z.obj Z.property) (E : FiniteSupport B (f ≫ g) W)
    (E' : FiniteSupport B f (baseChange B g W)) (hE' : E'.1 = (sepCompMap B f g W).base ⁻¹' E.1) :
    supportedSections B X.obj X.property F (baseChange B (f ≫ g) W) E.1
        (finiteSupport_isLocallyClosed B _ W E) →+
      supportedSections B X.obj X.property F (baseChange B f (baseChange B g W)) E'.1
        (finiteSupport_isLocallyClosed B f _ _) :=
  supportedSectionsPullback B X.obj X.property F
    ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W) E.1
    (finiteSupport_isLocallyClosed B _ W E) E'.1 (finiteSupport_isLocallyClosed B f _ _) hE'

/-- The transport for the support `AlgebraicGeometry.SmallEtale.sepCompSupport` itself is the
construction `AlgebraicGeometry.SmallEtale.sepCompSection`. -/
public theorem sepCompGenMap_sepCompSupport (W : SmallEtale B Z.obj Z.property)
    (E : FiniteSupport B (f ≫ g) W) :
    sepCompGenMap B f g F W E (sepCompSupport B f g W E) rfl = sepCompSection B f g F W E :=
  rfl

/-- The transport commutes with the transitions along inclusions of supports. -/
public theorem sepCompSection_transition (W : SmallEtale B Z.obj Z.property)
    {E E₂ : FiniteSupport B (f ≫ g) W} (h : E ⟶ E₂) :
    (finiteSupportDiagram B (f ≫ g) F W).map h ≫
        AddCommGrpCat.ofHom (sepCompSection B f g F W E₂) =
      AddCommGrpCat.ofHom (sepCompSection B f g F W E) ≫
        (finiteSupportDiagram B f F (baseChange B g W)).map
          (homOfLE (sepCompSupport_mono B f g W (leOfHom h))) := by
  refine ConcreteCategory.hom_ext _ _ fun a => ?_
  exact DFunLike.congr_fun (supportedSectionsPullback_transition B X.obj X.property F
    ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W) E.1 E₂.1
    (finiteSupport_isLocallyClosed B _ W E) (finiteSupport_isLocallyClosed B _ W E₂)
    (leOfHom h) (finiteSupport_closedWithin B _ W E E₂ (leOfHom h))
    (sepCompSupport B f g W E).1 (sepCompSupport B f g W E₂).1
    (finiteSupport_isLocallyClosed B f _ _) (finiteSupport_isLocallyClosed B f _ _)
    (sepCompSupport_mono B f g W (leOfHom h))
    (finiteSupport_closedWithin B f _ _ _ (sepCompSupport_mono B f g W (leOfHom h))) rfl rfl) a

end Transport

section Generator

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- **The map `c` of Stacks 0F79 on a generator.** A section supported on a support finite over
`W`, transported to `X_{W ×_Z Y}` and read as a section of `f_! F` over `W ×_Z Y`. -/
public abbrev sepCompGenerator (W : SmallEtale B Z.obj Z.property)
    (E : FiniteSupport B (f ≫ g) W) :
    (finiteSupportDiagram B (f ≫ g) F W).obj E ⟶
      ((fShriekFunctor.{u, v} B f).obj F).obj.obj (op (baseChange B g W)) :=
  AddCommGrpCat.ofHom (sepCompSection B f g F W E) ≫
    finiteSupportPushforwardGenerator B f F (baseChange B g W) (sepCompSupport B f g W E) ≫
    (toSheafify (SmallEtale.topology B Y.obj Y.property)
      ((finiteSupportPushforward.{u, max (u + 1) v} B f
        (fun _ => inferInstance)).val.obj F)).app (op (baseChange B g W))

/-- The generator map may be computed with any support realizing the attached support. -/
public theorem sepCompGenerator_eq (W : SmallEtale B Z.obj Z.property)
    (E : FiniteSupport B (f ≫ g) W) (E' : FiniteSupport B f (baseChange B g W))
    (hE' : E'.1 = (sepCompMap B f g W).base ⁻¹' E.1) :
    sepCompGenerator B f g F W E =
      AddCommGrpCat.ofHom (sepCompGenMap B f g F W E E' hE') ≫
        finiteSupportPushforwardGenerator B f F (baseChange B g W) E' ≫
        (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).val.obj F)).app (op (baseChange B g W)) := by
  have he : E' = sepCompSupport B f g W E := Subtype.ext hE'
  subst he
  rfl

/-- The cocone of transported generators, with vertex the sections of `f_! F` over
`W ×_Z Y`. -/
public def sepCompCocone (W : SmallEtale B Z.obj Z.property) :
    Cocone (finiteSupportDiagram B (f ≫ g) F W) where
  pt := ((fShriekFunctor.{u, v} B f).obj F).obj.obj (op (baseChange B g W))
  ι :=
    { app E := sepCompGenerator B f g F W E
      naturality E E₂ h := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map]
        have ht := sepCompSection_transition B f g F W h
        have hw : (finiteSupportDiagram B f F (baseChange B g W)).map
              (homOfLE (sepCompSupport_mono B f g W (leOfHom h))) ≫
            finiteSupportPushforwardGenerator B f F _ (sepCompSupport B f g W E₂) =
            finiteSupportPushforwardGenerator B f F _ (sepCompSupport B f g W E) := by
          simp only [finiteSupportPushforwardGenerator]
          rw [← Category.assoc, colimit.w]
        let ts := (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).val.obj F)).app (op (baseChange B g W))
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫
            finiteSupportPushforwardGenerator B f F _ (sepCompSupport B f g W E₂) ≫ ts) ht).trans
          ((Category.assoc _ _ _).trans (congrArg (AddCommGrpCat.ofHom
            (sepCompSection B f g F W E) ≫ ·) ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ ts) hw))))) }

variable [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map (f ≫ g))]

/-- **The transported generators**, as a map from the finite-support sections of `F` along
`f ≫ g` over `W` to the sections of `f_! F` over `W ×_Z Y`. -/
public def sepCompApp (W : SmallEtale B Z.obj Z.property) :
    ((finiteSupportPushforward.{u, max (u + 1) v} B (f ≫ g)
        (fun _ => inferInstance)).val.obj F).obj (op W) ⟶
      ((fShriekFunctor.{u, v} B f).obj F).obj.obj (op (baseChange B g W)) :=
  colimit.desc _ (sepCompCocone B f g F W)

/-- The transported generators on a colimit generator. -/
public theorem sepCompApp_generator (W : SmallEtale B Z.obj Z.property)
    (E : FiniteSupport B (f ≫ g) W) :
    finiteSupportPushforwardGenerator B (f ≫ g) F W E ≫ sepCompApp B f g F W =
      sepCompGenerator B f g F W E := by
  simp only [finiteSupportPushforwardGenerator, sepCompApp]
  exact colimit.ι_desc _ _

/-- **The transported generators are natural in the test object.** -/
public theorem sepCompApp_naturality {W W' : SmallEtale B Z.obj Z.property} (φ : W' ⟶ W) :
    ((finiteSupportPushforward.{u, max (u + 1) v} B (f ≫ g)
        (fun _ => inferInstance)).val.obj F).map φ.op ≫ sepCompApp B f g F W' =
      sepCompApp B f g F W ≫
        ((fShriekFunctor.{u, v} B f).obj F).obj.map ((smallEtaleBaseChange B g).map φ).op := by
  apply finiteSupportPushforwardGenerator_hom_ext B (f ≫ g) F W
  intro E
  let ψ := (smallEtaleBaseChange B g).map φ
  have hl := finiteSupportPushforwardGenerator_restrict B (f ≫ g) F φ E
  have hr := finiteSupportPushforwardGenerator_restrict B f F ψ (sepCompSupport B f g W E)
  set d := finiteSupportBaseChange B (f ≫ g) F φ E
  set dE := finiteSupportBaseChange B f F ψ (sepCompSupport B f g W E)
  have hnat : (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map ψ) ≫
        sepCompMap B f g W =
      sepCompMap B f g W' ≫
        (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B (f ≫ g)).map φ) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.naturality φ)
  have hE' : dE.support.1 = (sepCompMap B f g W').base ⁻¹' d.support.1 := by
    rw [dE.support_eq, d.support_eq]
    ext x
    show (sepCompMap B f g W).base (((SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map ψ)).base x) ∈ E.1 ↔
      ((SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B (f ≫ g)).map φ)).base ((sepCompMap B f g W').base x) ∈ E.1
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat]
  have hs : AddCommGrpCat.ofHom d.sectionsMap ≫
      AddCommGrpCat.ofHom (sepCompGenMap B f g F W' d.support dE.support hE') =
      AddCommGrpCat.ofHom (sepCompSection B f g F W E) ≫ AddCommGrpCat.ofHom dE.sectionsMap := by
    refine ConcreteCategory.hom_ext _ _ fun a => Subtype.ext ?_
    show (sepCompGenMap B f g F W' d.support dE.support hE' (d.sectionsMap a)).val =
      (dE.sectionsMap (sepCompSection B f g F W E a)).val
    rw [dE.sectionsMap_apply]
    show F.obj.map _ (d.sectionsMap a).val = F.obj.map dE.openMap.op (F.obj.map _ a.val)
    rw [d.sectionsMap_apply]
    exact supportedSectionsPullback_square B X.obj X.property F
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W)
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W')
      ((smallEtaleBaseChange B (f ≫ g)).map φ) ((smallEtaleBaseChange B f).map ψ)
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.naturality φ).symm
      E.1 _ d.support.1 _ (sepCompSupport B f g W E).1 _ dE.support.1 _ rfl hE'
      d.openMap d.openMap_commutes dE.openMap dE.openMap_commutes a.val
  have hn := (toSheafify (SmallEtale.topology B Y.obj Y.property)
    ((finiteSupportPushforward.{u, max (u + 1) v} B f
      (fun _ => inferInstance)).val.obj F)).naturality ψ.op
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ sepCompApp B f g F W') hl).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (AddCommGrpCat.ofHom d.sectionsMap ≫ ·)
    ((sepCompApp_generator B f g F W' d.support).trans
      (sepCompGenerator_eq B f g F W' d.support dE.support hE'))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hs).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ _) (sepCompApp_generator B f g F W E).symm)
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (AddCommGrpCat.ofHom (sepCompSection B f g F W E) ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hr.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (finiteSupportPushforwardGenerator B f F (baseChange B g W)
    (sepCompSupport B f g W E) ≫ ·) hn).trans ?_
  exact (Category.assoc _ _ _).symm

end Generator

section Support

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]

/-- The image in `W ×_Z Y` of the support attached to a support `E ⊆ X_W` finite over `W`. -/
public abbrev sepCompImage (W : SmallEtale B Z.obj Z.property) (E : FiniteSupport B (f ≫ g) W) :
    Set ((SmallEtale.toScheme B Y.obj Y.property).obj (baseChange B g W)) :=
  (B.inclusion.map (baseChangeObjProjection B f (baseChange B g W))).base ''
    (sepCompSupport B f g W E).1

/-- The image in `W ×_Z Y` of a support finite over `W` is closed and proper over `W`, the
morphism `W ×_Z Y ⟶ W` being separated and locally of finite type. -/
public theorem exists_isProperOver_sepCompImage (W : SmallEtale B Z.obj Z.property)
    (E : FiniteSupport B (f ≫ g) W) :
    ∃ hC : IsClosed (sepCompImage B f g W E),
      haveI := locallyOfFiniteType_baseChangeProjection B g W
      IsProperOver (B.inclusion.map (pullback.fst W.obj.hom g)) ⟨sepCompImage B f g W E, hC⟩ := by
  obtain ⟨Zs, i, hi, hfin, hrange⟩ := E.property
  have : IsImmersion i := hi
  let p := i ≫ B.inclusion.map (pullback.fst W.obj.hom (f ≫ g))
  let r := i ≫ sepCompInv B f g W ≫
    B.inclusion.map (baseChangeObjProjection B f (baseChange B g W))
  let q := B.inclusion.map (pullback.fst W.obj.hom g)
  have : IsFinite p := hfin
  have : IsSeparated q := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback W.obj.hom g).map B.inclusion).flip inferInstance
  have : LocallyOfFiniteType q := locallyOfFiniteType_baseChangeProjection B g W
  have hfg : r ≫ q = p := by
    have h := congrArg (sepCompInv B f g W ≫ ·) (sepCompMap_fst B f g W)
    simp only [← Category.assoc, sepCompInv_sepCompMap, Category.id_comp] at h
    simp only [r, q, p]
    exact congrArg (i ≫ ·) ((Category.assoc _ _ _).symm.trans h.symm)
  have hZ : IsProperOver p ⊤ := by
    show IsProper ((Scheme.IdealSheafData.vanishingIdeal ⊤).subschemeι ≫ p)
    infer_instance
  have hrange' : Set.range (i ≫ sepCompInv B f g W).base = (sepCompSupport B f g W E).1 := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show (sepCompMap B f g W).base ((sepCompInv B f g W).base y) ∈ E.1
      rw [← Scheme.Hom.comp_apply, sepCompInv_sepCompMap]
      exact hy
    · intro hx
      refine ⟨_, hx, ?_⟩
      show (sepCompInv B f g W).base ((sepCompMap B f g W).base x) = x
      rw [← Scheme.Hom.comp_apply, sepCompMap_sepCompInv]
      rfl
  have hset : r.base '' ((⊤ : Closeds Zs) : Set Zs) = sepCompImage B f g W E := by
    show r.base '' Set.univ = _
    rw [Set.image_univ]
    show Set.range ((i ≫ sepCompInv B f g W) ≫
      B.inclusion.map (baseChangeObjProjection B f (baseChange B g W))).base = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange']
  have hC : IsClosed (sepCompImage B f g W E) :=
    hset ▸ isClosed_image_of_isProperOver p q r hfg ⊤ hZ
  refine ⟨hC, ?_⟩
  have he : (⟨sepCompImage B f g W E, hC⟩ : Closeds _) =
      ⟨r.base '' ((⊤ : Closeds Zs) : Set Zs),
        isClosed_image_of_isProperOver p q r hfg ⊤ hZ⟩ := Closeds.ext hset.symm
  exact he ▸ isProperOver_image p q r hfg ⊤ hZ

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The transported generator of a supported section is supported in the image of the
support. -/
public theorem supportSection_sepCompGenerator_subset (W : SmallEtale B Z.obj Z.property)
    (E : FiniteSupport B (f ≫ g) W) (a : (finiteSupportDiagram B (f ≫ g) F W).obj E) :
    supportSection B Y.obj Y.property ((fShriekFunctor.{u, v} B f).obj F) (baseChange B g W)
        (sepCompGenerator B f g F W E a) ⊆ sepCompImage B f g W E := by
  obtain ⟨hC, -⟩ := exists_isProperOver_sepCompImage B f g W E
  exact supportSection_toSheafify_generator_subset B F (baseChange B g W)
    (sepCompSupport B f g W E) (sepCompSection B f g F W E a) _ hC (Set.subset_preimage_image _ _)

/-- The transported generator of a supported section has support proper over `W`. -/
public theorem properSupportSections_sepCompGenerator (W : SmallEtale B Z.obj Z.property)
    (E : FiniteSupport B (f ≫ g) W) (a : (finiteSupportDiagram B (f ≫ g) F W).obj E) :
    properSupportSections B g ((fShriekFunctor.{u, v} B f).obj F) W
      (sepCompGenerator B f g F W E a) := by
  obtain ⟨hC, hP⟩ := exists_isProperOver_sepCompImage B f g W E
  have := locallyOfFiniteType_baseChangeProjection B g W
  exact isProperOver_of_le (B.inclusion.map (pullback.fst W.obj.hom g))
    (supportSection_sepCompGenerator_subset B f g F W E a) hP

variable [LocallyQuasiFinite (B.inclusion.map (f ≫ g))]

/-- Every transported section has support proper over `W`. -/
public theorem properSupportSections_sepCompApp (W : SmallEtale B Z.obj Z.property)
    (x : ((finiteSupportPushforward.{u, max (u + 1) v} B (f ≫ g)
        (fun _ => inferInstance)).val.obj F).obj (op W)) :
    properSupportSections B g ((fShriekFunctor.{u, v} B f).obj F) W
      (sepCompApp B f g F W x) := by
  obtain ⟨n, E, t, hx⟩ := exists_finiteSupport_sum B (f ≫ g) F W x
  let H := (properSupportSubgroup B g ((fShriekFunctor.{u, v} B f).obj F) W).comap
    (sepCompApp B f g F W).hom
  show x ∈ H
  rw [hx]
  refine H.sum_mem fun i _ => ?_
  show properSupportSections B g ((fShriekFunctor.{u, v} B f).obj F) W
    ((finiteSupportPushforwardGenerator B (f ≫ g) F W (E i) ≫ sepCompApp B f g F W) (t i))
  rw [ConcreteCategory.congr_hom (sepCompApp_generator B f g F W (E i)) (t i)]
  exact properSupportSections_sepCompGenerator B f g F W (E i) (t i)

/-- **The map `c` of Stacks 0F79, before sheafification.** The transported generators, as a
morphism of presheaves from the finite-support direct image `(f ≫ g)_{p!} F` to the
proper-support direct image `g_!(f_! F)`. -/
public def sepCompProperMap :
    (finiteSupportPushforward.{u, max (u + 1) v} B (f ≫ g)
        (fun _ => inferInstance)).val.obj F ⟶
      properSupportPresheaf B g ((fShriekFunctor.{u, v} B f).obj F) where
  app W := AddCommGrpCat.ofHom
    (AddMonoidHom.codRestrict (sepCompApp B f g F W.unop).hom _
      (properSupportSections_sepCompApp B f g F W.unop))
  naturality W W' φ := by
    refine ConcreteCategory.hom_ext _ _ fun x => Subtype.ext ?_
    change sepCompApp B f g F W'.unop
        ((((finiteSupportPushforward.{u, max (u + 1) v} B (f ≫ g)
          (fun _ => inferInstance)).val.obj F).map φ) x) =
      ((fShriekFunctor.{u, v} B f).obj F).obj.map ((smallEtaleBaseChange B g).map φ.unop).op
        (sepCompApp B f g F W.unop x)
    exact ConcreteCategory.congr_hom (sepCompApp_naturality B f g F φ.unop) x

/-- The map `c` lands in the proper-support direct image as the transported generators. -/
public theorem sepCompProperMap_app_val (W : SmallEtale B Z.obj Z.property)
    (x : ((finiteSupportPushforward.{u, max (u + 1) v} B (f ≫ g)
        (fun _ => inferInstance)).val.obj F).obj (op W)) :
    ((sepCompProperMap B f g F).app (op W) x).val = sepCompApp B f g F W x :=
  rfl

/-- **The map `c'` of Stacks 0F79**: the sheafification of the transported generators, a
morphism `(f ≫ g)_! F ⟶ g_!(f_! F)` from the direct image with compact support along the locally
quasi-finite morphism `f ≫ g` to the proper-support direct image along `g` of the direct image
with compact support along `f`. -/
public def sepCompShriekMap :
    (fShriekFunctor.{u, v} B (f ≫ g)).obj F ⟶
      (properSupportFunctor.{u, max (u + 1) v} B g).obj ((fShriekFunctor.{u, v} B f).obj F) :=
  ⟨sheafifyLift (SmallEtale.topology B Z.obj Z.property) (sepCompProperMap B f g F)
    (properSupportSheaf B g ((fShriekFunctor.{u, v} B f).obj F)).cond⟩

/-- The map `c'` restricts along the sheafification unit to the map `c`. -/
public theorem toSheafify_sepCompShriekMap :
    toSheafify (SmallEtale.topology B Z.obj Z.property)
        ((finiteSupportPushforward.{u, max (u + 1) v} B (f ≫ g)
          (fun _ => inferInstance)).val.obj F) ≫ (sepCompShriekMap B f g F).hom =
      sepCompProperMap B f g F :=
  toSheafify_sheafifyLift _ _ _

/-- The map `c'` on the image of a generator: the transported generator. -/
public theorem properSupportSection_sepCompShriekMap_generator (W : SmallEtale B Z.obj Z.property)
    (E : FiniteSupport B (f ≫ g) W) (a : (finiteSupportDiagram B (f ≫ g) F W).obj E) :
    properSupportSection B g ((fShriekFunctor.{u, v} B f).obj F) W
        ((sepCompShriekMap B f g F).hom.app (op W)
          ((finiteSupportPushforwardGenerator B (f ≫ g) F W E ≫
            (toSheafify (SmallEtale.topology B Z.obj Z.property)
              ((finiteSupportPushforward.{u, max (u + 1) v} B (f ≫ g)
                (fun _ => inferInstance)).val.obj F)).app (op W)) a)) =
      sepCompGenerator B f g F W E a := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_sepCompShriekMap B f g F) (op W)) (finiteSupportPushforwardGenerator B (f ≫ g)
      F W E a)
  refine (congrArg Subtype.val h).trans ?_
  exact ConcreteCategory.congr_hom (sepCompApp_generator B f g F W E) a

end Support

end AlgebraicGeometry.SmallEtale

end
