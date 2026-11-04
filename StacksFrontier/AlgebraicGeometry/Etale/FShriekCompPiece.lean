module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompGenerator
public import StacksFrontier.AlgebraicGeometry.Cohomology.ProperOverBase.Functoriality
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportPushforward

/-!
# The composition comparison on an open piece

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be locally quasi-finite morphisms of a big étale site and let
`jX : X' ⟶ X`, `jY : Y' ⟶ Y` be open immersions with `X' = X ×_Y Y'` and `jY ≫ g` separated.
This file builds the piece of the comparison `(f ≫ g)_! ⟶ g_! f_!` of Stacks 0F6T on `X'`:

`(jX ≫ f ≫ g)_!(F|_{X'}) ⟶ g_!(f_! F)`.

A generator of the left side over `W` is transported to a section of `f_! F` over
`W ×_Z Y'` (`StacksFrontier.AlgebraicGeometry.Etale.FShriekCompGenerator`). That section has support
proper over `W`: it lies in the image of the support of the generator, which is finite over `W`.
It is therefore a section of the direct image with proper support of `(f_! F)|_{Y'}` along the
separated morphism `jY ≫ g`, which is the finite-support direct image by Stacks 0F6N; the
covariance of Stacks 0F6S for `jY` carries it to `g_{p!}(f_! F)`, and sheafifying gives the map.

## Main definitions

* `AlgebraicGeometry.SmallEtale.compChartPresheafMap` — the transported generators as a morphism
  of presheaves.
* `AlgebraicGeometry.SmallEtale.compPiecePresheafMap` and
  `AlgebraicGeometry.SmallEtale.compPieceMap` — the piece of the comparison, before and after
  sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

section Restriction

variable (B : BigEtaleSite.{u}) {Y' Y : B.Scheme} (jY : Y' ⟶ Y)
  [IsOpenImmersion (B.inclusion.map jY)]
  (G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})

/-- The comparison of the two descriptions of restriction does not enlarge supports. -/
public theorem supportSection_openRestrictionIso_hom_subset (Q : SmallEtale B Y'.obj Y'.property)
    (t : G.obj.obj (op ((openPostcompose B jY).obj Q))) :
    supportSection B Y'.obj Y'.property ((openRestriction.{u, v} B jY).obj G) Q
        (((openRestrictionIso.{u, v} B jY).hom.app G).hom.app (op Q) t) ⊆
      supportSection B Y.obj Y.property G ((openPostcompose B jY).obj Q) t := by
  let U : ((SmallEtale.toScheme B Y'.obj Y'.property).obj Q).Opens :=
    zeroOpen B Y.obj Y.property G ((openPostcompose B jY).obj Q) t
  let i := openObjectι B Y'.obj Y'.property Q U
  have : IsOpenImmersion ((SmallEtale.toScheme B Y'.obj Y'.property).map i) :=
    isOpenImmersion_openObjectι B Y'.obj Y'.property Q U
  have hiY : IsOpenImmersion ((SmallEtale.toScheme B Y.obj Y.property).map
      ((openPostcompose B jY).map i)) := by
    rw [openPostcompose_toScheme_map]
    exact isOpenImmersion_openObjectι B Y'.obj Y'.property Q U
  have h0 : G.obj.map ((openPostcompose B jY).map i).op t = 0 := by
    rw [map_eq_zero_iff_le_zeroOpen]
    exact (openObjectι_opensRange B Y'.obj Y'.property Q U).le
  have hn : ((openRestrictionIso.{u, v} B jY).hom.app G).hom.app
        (op (openObject B Y'.obj Y'.property Q U))
        (G.obj.map ((openPostcompose B jY).map i).op t) =
      ((openRestriction.{u, v} B jY).obj G).obj.map i.op
        (((openRestrictionIso.{u, v} B jY).hom.app G).hom.app (op Q) t) :=
    ConcreteCategory.congr_hom
      (((openRestrictionIso.{u, v} B jY).hom.app G).hom.naturality i.op) t
  have hz : ((openRestriction.{u, v} B jY).obj G).obj.map i.op
      (((openRestrictionIso.{u, v} B jY).hom.app G).hom.app (op Q) t) = 0 :=
    hn.symm.trans ((congrArg (((openRestrictionIso.{u, v} B jY).hom.app G).hom.app
      (op (openObject B Y'.obj Y'.property Q U))) h0).trans (map_zero _))
  have hle : (U : Set ((SmallEtale.toScheme B Y'.obj Y'.property).obj Q)) ⊆
      (zeroOpen B Y'.obj Y'.property ((openRestriction.{u, v} B jY).obj G) Q
        (((openRestrictionIso.{u, v} B jY).hom.app G).hom.app (op Q) t) :
          Set ((SmallEtale.toScheme B Y'.obj Y'.property).obj Q)) :=
    ((openObjectι_opensRange B Y'.obj Y'.property Q U).ge.trans
      ((map_eq_zero_iff_le_zeroOpen B Y'.obj Y'.property
        ((openRestriction.{u, v} B jY).obj G) Q _ _ i).1 hz) :)
  exact fun x hx hxU => hx (hle hxU)

end Restriction

section Empty

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- A section supported on the empty set is zero. -/
public theorem supportedSections_eq_zero_of_eq_empty (Q : SmallEtale B S hS)
    (E : Set ((SmallEtale.toScheme B S hS).obj Q)) (hE : IsLocallyClosed E) (h : E = ∅)
    (x : supportedSections B S hS F Q E hE) : x = 0 := by
  apply Subtype.ext
  have hs : supportSection B S hS F _ x.val = ∅ := by
    refine Set.eq_empty_of_subset_empty (x.property.trans ?_)
    intro y hy
    have : (supportOpen B S hS Q E hE).ι y ∈ E := hy
    exact (h ▸ this : (supportOpen B S hS Q E hE).ι y ∈ (∅ : Set _))
  have htop : zeroOpen B S hS F _ x.val = ⊤ := by
    apply SetLike.coe_injective
    have := congrArg compl hs
    simp only [supportSection, compl_compl, Set.compl_empty] at this
    exact this
  have h0 := (map_eq_zero_iff_le_zeroOpen B S hS F _ x.val _
    (𝟙 (openObject B S hS Q (supportOpen B S hS Q E hE)))).2 (by rw [htop]; exact le_top)
  simpa using h0

end Empty

section Image

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' : B.Scheme}
  {f : X ⟶ Y} (g : Y ⟶ Z) {jX : X' ⟶ X} {jY : Y' ⟶ Y} {f' : X' ⟶ Y'}
  [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)]
  [IsSeparated (B.inclusion.map (jY ≫ g))] [LocallyOfFiniteType (B.inclusion.map g)]
  (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)

/-- The image in `W ×_Z Y'` of a support `T ⊆ W ×_Z X'` finite over `W`. -/
public abbrev compChartImage (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W) :
    Set ((SmallEtale.toScheme B Y.obj Y.property).obj (compChartBase B g jY W)) :=
  (B.inclusion.map (compChartMap B g sq W)).base '' T.1

/-- The image of a support finite over `W` is closed in `W ×_Z Y'` and proper over `W`, the
morphism `W ×_Z Y' ⟶ W` being separated. -/
public theorem exists_isProperOver_compChartImage (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W) :
    ∃ hC : IsClosed (compChartImage B g sq W T),
      haveI := locallyOfFiniteType_baseChangeProjection B (jY ≫ g) W
      IsProperOver (B.inclusion.map (pullback.fst W.obj.hom (jY ≫ g)))
        ⟨compChartImage B g sq W T, hC⟩ := by
  obtain ⟨Zs, i, hi, hfin, hrange⟩ := T.property
  have : IsImmersion i := hi
  let p := i ≫ B.inclusion.map (fiberProjection B (jX ≫ f ≫ g) W)
  let r := i ≫ B.inclusion.map (compChartMap B g sq W)
  let q := B.inclusion.map (fiberProjection B (jY ≫ g) W)
  have : IsFinite p := hfin
  have : IsSeparated q := MorphismProperty.of_isPullback
    ((isPullback_fiberProjection B (jY ≫ g) W).map B.inclusion).flip inferInstance
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback
    ((isPullback_fiberProjection B (jY ≫ g) W).map B.inclusion).flip inferInstance
  have hfg : r ≫ q = p :=
    (Category.assoc _ _ _).trans (congrArg (fun m => i ≫ m)
      ((B.inclusion.map_comp _ _).symm.trans
        (congrArg B.inclusion.map (compChartMap_fst B g sq W))))
  have hZ : IsProperOver p ⊤ := by
    show IsProper ((Scheme.IdealSheafData.vanishingIdeal ⊤).subschemeι ≫ p)
    infer_instance
  have himg := isProperOver_image p q r hfg ⊤ hZ
  have hset : r.base '' ((⊤ : Closeds Zs) : Set Zs) = compChartImage B g sq W T := by
    show r.base '' Set.univ = _
    rw [Set.image_univ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
    rfl
  have hC := hset ▸ isClosed_image_of_isProperOver p q r hfg ⊤ hZ
  exact ⟨hC, (Closeds.ext hset.symm : (⟨_, hC⟩ : Closeds _) = ⟨_, _⟩) ▸ himg⟩

end Image

section Support

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' : B.Scheme}
  {f : X ⟶ Y} (g : Y ⟶ Z) {jX : X' ⟶ X} {jY : Y' ⟶ Y} {f' : X' ⟶ Y'}
  [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)]
  [IsSeparated (B.inclusion.map (jY ≫ g))]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The section of `f_! F` obtained by sheafifying a generator supported on a support `E` is
supported in every closed subset of the base whose inverse image contains `E`. -/
public theorem supportSection_toSheafify_generator_subset (W' : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f W')
    (s : supportedSections B X.obj X.property F (baseChange B f W') E.1
      (finiteSupport_isLocallyClosed B f W' E))
    (C : Set ((SmallEtale.toScheme B Y.obj Y.property).obj W')) (hC : IsClosed C)
    (hE : E.1 ⊆ (B.inclusion.map (baseChangeObjProjection B f W')).base ⁻¹' C) :
    supportSection B Y.obj Y.property ((fShriekFunctor.{u, v} B f).obj F) W'
        ((finiteSupportPushforwardGenerator B f F W' E ≫
          (toSheafify (SmallEtale.topology B Y.obj Y.property)
            ((finiteSupportPushforward.{u, max (u + 1) v} B f
              (fun _ => inferInstance)).val.obj F)).app (op W')) s) ⊆ C := by
  let U₀ : ((SmallEtale.toScheme B Y.obj Y.property).obj W').Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  let i₀ := openObjectι B Y.obj Y.property W' U₀
  have hR : Set.range ((SmallEtale.toScheme B Y.obj Y.property).map i₀).base = Cᶜ :=
    openObjectι_range B Y.obj Y.property W' U₀
  refine (supportSection_subset_iff_zero_on_open B Y.obj Y.property
    ((fShriekFunctor.{u, v} B f).obj F) i₀ C hR _).2 ?_
  let d := finiteSupportBaseChange B f F i₀ E
  have hempty : d.support.1 = ∅ := by
    rw [d.support_eq]
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    have h2 : (B.inclusion.map (baseChangeObjProjection B f W'))
        ((SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map i₀) y) =
        (SmallEtale.toScheme B Y.obj Y.property).map i₀
          (B.inclusion.map (baseChangeObjProjection B f _) y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun m => m.base y)
        ((B.inclusion.map_comp _ _).symm.trans
          ((congrArg B.inclusion.map (baseChangeObjProjection_naturality B f i₀)).trans
            (B.inclusion.map_comp _ _)))
    have hin : (SmallEtale.toScheme B Y.obj Y.property).map i₀
        (B.inclusion.map (baseChangeObjProjection B f _) y) ∈ Cᶜ := by
      rw [← hR]
      exact ⟨_, rfl⟩
    exact hin (h2 ▸ hE hy)
  have hn := ConcreteCategory.congr_hom ((toSheafify (SmallEtale.topology B Y.obj Y.property)
    ((finiteSupportPushforward.{u, max (u + 1) v} B f
      (fun _ => inferInstance)).val.obj F)).naturality i₀.op)
    ((finiteSupportPushforwardGenerator B f F W' E) s)
  have hr := ConcreteCategory.congr_hom
    (finiteSupportPushforwardGenerator_restrict B f F i₀ E) s
  have h0 : d.sectionsMap s = 0 :=
    supportedSections_eq_zero_of_eq_empty B X.obj X.property F _ _ _ hempty _
  refine hn.symm.trans ?_
  refine (congrArg ((toSheafify (SmallEtale.topology B Y.obj Y.property)
    ((finiteSupportPushforward.{u, max (u + 1) v} B f
      (fun _ => inferInstance)).val.obj F)).app (op _)) hr).trans ?_
  show ((toSheafify (SmallEtale.topology B Y.obj Y.property)
    ((finiteSupportPushforward.{u, max (u + 1) v} B f
      (fun _ => inferInstance)).val.obj F)).app (op _))
      ((finiteSupportPushforwardGenerator B f F _ d.support) (d.sectionsMap s)) = 0
  rw [h0]
  exact (congrArg _ (AddMonoidHom.map_zero _)).trans (AddMonoidHom.map_zero _)

end Support

section Piece

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' : B.Scheme}
  {f : X ⟶ Y} (g : Y ⟶ Z) {jX : X' ⟶ X} {jY : Y' ⟶ Y} {f' : X' ⟶ Y'}
  [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)]
  [IsSeparated (B.inclusion.map (jY ≫ g))]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The comparison of the two descriptions of the restriction of `f_! F` to `Y'`, on the
sections over `W ×_Z Y'`. -/
public abbrev compChartRestrict (W : SmallEtale B Z.obj Z.property) :
    ((fShriekFunctor.{u, v} B f).obj F).obj.obj (op (compChartBase B g jY W)) ⟶
      ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)).obj.obj
        (op (baseChange B (jY ≫ g) W)) :=
  ((openRestrictionIso.{u, v} B jY).hom.app ((fShriekFunctor.{u, v} B f).obj F)).hom.app
    (op (baseChange B (jY ≫ g) W))

/-- The transported generator of a supported section is supported in the image of the support. -/
public theorem supportSection_compChartRestrict_subset (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W)
    (a : (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F) W).obj T) :
    supportSection B Y'.obj Y'.property
        ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F))
        (baseChange B (jY ≫ g) W)
        (compChartRestrict B g F W ((colimit.ι _ T ≫ compChartApp B g sq hsq F W) a)) ⊆
      compChartImage B g sq W T := by
  obtain ⟨hC, -⟩ := exists_isProperOver_compChartImage B g sq W T
  have hsupp : supportSection B Y.obj Y.property ((fShriekFunctor.{u, v} B f).obj F)
      (compChartBase B g jY W) ((colimit.ι _ T ≫ compChartApp B g sq hsq F W) a) ⊆
        compChartImage B g sq W T := by
    show supportSection B Y.obj Y.property ((fShriekFunctor.{u, v} B f).obj F)
      (compChartBase B g jY W) ((colimit.ι _ T ≫ colimit.desc _
        (compChartCocone B g sq hsq F W)) a) ⊆ _
    rw [colimit.ι_desc]
    show supportSection B Y.obj Y.property ((fShriekFunctor.{u, v} B f).obj F)
      (compChartBase B g jY W) ((finiteSupportPushforwardGenerator B f F _
        (compChartSupport B g sq hsq W T) ≫ (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).val.obj F)).app (op (compChartBase B g jY W)))
        (compChartGenMap B g sq hsq F W T _ (imageFiniteSupport_coe B jX (f ≫ g) W T)
          (compChartSupport B g sq hsq W T) (compChartSupport_coe B g sq hsq W T) a)) ⊆ _
    refine supportSection_toSheafify_generator_subset B F _ _ _ _ hC ?_
    rw [compChartSupport_coe, imageFiniteSupport_coe, compChartInclusion_preimage_image]
    rintro _ ⟨x, hx, rfl⟩
    show B.inclusion.map (baseChangeObjProjection B f _)
      (B.inclusion.map (compChartHom B g sq W).hom.left x) ∈ compChartImage B g sq W T
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, compChartHom_proj]
    exact ⟨x, hx, rfl⟩
  exact (supportSection_openRestrictionIso_hom_subset B jY
    ((fShriekFunctor.{u, v} B f).obj F) (baseChange B (jY ≫ g) W) _).trans hsupp

/-- The transported generator of a supported section has support proper over `W`. -/
public theorem properSupportSections_compChartApp_ι (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W)
    (a : (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F) W).obj T) :
    properSupportSections B (jY ≫ g)
      ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)) W
      (compChartRestrict B g F W ((colimit.ι _ T ≫ compChartApp B g sq hsq F W) a)) := by
  obtain ⟨hC, hP⟩ := exists_isProperOver_compChartImage B g sq W T
  have := locallyOfFiniteType_baseChangeProjection B (jY ≫ g) W
  exact isProperOver_of_le (B.inclusion.map (pullback.fst W.obj.hom (jY ≫ g)))
    (supportSection_compChartRestrict_subset B g sq hsq F W T a) hP

/-- Every transported section has support proper over `W`. -/
public theorem properSupportSections_compChartApp (W : SmallEtale B Z.obj Z.property)
    (x : ((finiteSupportPushforward.{u, max (u + 1) v} B (jX ≫ f ≫ g)
        (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B jX).obj F)).obj (op W)) :
    properSupportSections B (jY ≫ g)
      ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)) W
      (compChartRestrict B g F W (compChartApp B g sq hsq F W x)) := by
  obtain ⟨n, E, t, hx⟩ := exists_finiteSupport_sum B (jX ≫ f ≫ g)
    ((openRestriction.{u, v} B jX).obj F) W x
  let H := (properSupportSubgroup B (jY ≫ g)
    ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)) W).comap
      ((compChartRestrict B g F W).hom.comp (compChartApp B g sq hsq F W).hom)
  show x ∈ H
  rw [hx]
  exact H.sum_mem fun i _ => properSupportSections_compChartApp_ι B g sq hsq F W (E i) (t i)

/-- **The transported generators, as sections with proper support.** For each `W` the
transported generators land in the sections of `(f_! F)|_{Y'}` over `W ×_Z Y'` with support
proper over `W`, naturally in `W`: a morphism of presheaves to the direct image with proper
support of `(f_! F)|_{Y'}` along `jY ≫ g`. -/
public def compPieceProperMap :
    (finiteSupportPushforward.{u, max (u + 1) v} B (jX ≫ f ≫ g)
        (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B jX).obj F) ⟶
      properSupportPresheaf B (jY ≫ g)
        ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)) where
  app W := AddCommGrpCat.ofHom
    (AddMonoidHom.codRestrict ((compChartRestrict B g F W.unop).hom.comp
      (compChartApp B g sq hsq F W.unop).hom) _
      (properSupportSections_compChartApp B g sq hsq F W.unop))
  naturality W W' φ := by
    refine ConcreteCategory.hom_ext _ _ fun x => Subtype.ext ?_
    change compChartRestrict B g F W'.unop (compChartApp B g sq hsq F W'.unop
        ((((finiteSupportPushforward.{u, max (u + 1) v} B (jX ≫ f ≫ g)
          (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B jX).obj F)).map φ) x)) =
      ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)).obj.map
        ((smallEtaleBaseChange B (jY ≫ g)).map φ.unop).op
        (compChartRestrict B g F W.unop (compChartApp B g sq hsq F W.unop x))
    have h1 := ConcreteCategory.congr_hom (compChartApp_naturality B g sq hsq F φ.unop) x
    simp only [ConcreteCategory.comp_apply] at h1
    rw [show φ = φ.unop.op from rfl, h1]
    exact ConcreteCategory.congr_hom
      (((openRestrictionIso.{u, v} B jY).hom.app ((fShriekFunctor.{u, v} B f).obj F)).hom.naturality
        ((smallEtaleBaseChange B (jY ≫ g)).map φ.unop).op) _

/-- **The piece of the composition comparison, before sheafification**: the transported
generators, read in the finite-support direct image of `(f_! F)|_{Y'}` along the separated
morphism `jY ≫ g` through Stacks 0F6N, and sheafified there. -/
public def compPiecePresheafMap :
    (finiteSupportPushforward.{u, max (u + 1) v} B (jX ≫ f ≫ g)
        (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B jX).obj F) ⟶
      ((fShriekFunctor.{u, v} B (jY ≫ g)).obj
        ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F))).obj :=
  compPieceProperMap B g sq hsq F ≫
    ((finiteSupportPushforwardIso.{u, max (u + 1) v} B (jY ≫ g)).val.inv.app
      ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F))) ≫
    toSheafify (SmallEtale.topology B Z.obj Z.property) _

/-- **The piece of the composition comparison** of Stacks 0F6T on the open piece `X'`:
`(jX ≫ f ≫ g)_!(F|_{X'}) ⟶ (jY ≫ g)_!((f_! F)|_{Y'}) ⟶ g_!(f_! F)`, the second arrow being the
covariance of Stacks 0F6S for `jY`. -/
public def compPieceMap :
    (openShriekPushforward.{u, v} B jX (f ≫ g)).obj F ⟶
      (fShriekFunctor.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F) :=
  ⟨sheafifyLift (SmallEtale.topology B Z.obj Z.property) (compPiecePresheafMap B g sq hsq F)
      (Sheaf.cond _)⟩ ≫
    (openCovarianceShriekMap.{u, v} B jY g).app ((fShriekFunctor.{u, v} B f).obj F)

end Piece

end AlgebraicGeometry.SmallEtale

end
