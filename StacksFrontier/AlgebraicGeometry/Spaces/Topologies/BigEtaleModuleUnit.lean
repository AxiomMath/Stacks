module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedPushforwardModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtale
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposPullbackComp

/-!
# The unit of `ε_X^* ⊣ ε_{X,*}` at `π_X^*𝓕`

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes and `X` an object of `T`. For a
quasi-coherent `𝒪_X`-module `𝓕` on the spaces-étale site of `X`, the unit
`π_X^*𝓕 ⟶ ε_{X,*}ε_X^*π_X^*𝓕` is an isomorphism and `a_X^* ≅ ε_X^*π_X^*`; hence
`ε_{X,*}a_X^*𝓕 ≅ π_X^*𝓕`, the `ε_X` half of Stacks 0DGN (6).

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToBigEtale_unit_app_pullback`: the unit
  `π_X^*𝓕 ⟶ ε_{X,*}ε_X^*π_X^*𝓕` is an isomorphism.
* `AlgebraicGeometry.BigFppfSpaceSite.nonempty_pullbackTopos_iso_comp`: `a_X^* ≅ ε_X^*π_X^*`.
* `AlgebraicGeometry.BigFppfSpaceSite.nonempty_fppfToBigEtale_pushforward_pullback_iso`:
  `ε_{X,*}a_X^*𝓕 ≅ π_X^*𝓕`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v' u u' w

namespace AlgebraicGeometry.RingedToposSiteHom

/-- Two morphisms of ringed topoi with the same functor and the same structure map are equal. -/
theorem ext_of_heq {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
    (f g : RingedToposSiteHom X Y) (hu : f.u = g.u) (hs : HEq f.fSharp g.fSharp) : f = g := by
  cases f; cases g; cases hu; cases hs; rfl

end AlgebraicGeometry.RingedToposSiteHom

namespace AlgebraicGeometry.RingedSite

/-- Two morphisms of ringed sites with the same functor and the same structure map are equal. -/
theorem Hom.ext_of_heq {X Y : RingedSite.{u, u, w}} (f g : Hom X Y) (hu : f.u = g.u)
    (hs : HEq f.fsharp g.fsharp) : f = g := by
  cases f; cases g; cases hu; cases hs; rfl

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (E : BigEtaleSpaceSite S) (X : E.Spaces)

/-- **The morphism `π_X` of Stacks 0DGM as a morphism of ringed sites**
`((Spaces/X)_étale, 𝒪) ⟶ (X_{spaces,étale}, 𝒪_X)`: the inclusion of the spaces-étale site, with
the identity structure map. -/
noncomputable def spacesEtaleRestrictionRingedSiteHom :
    RingedSite.Hom (E.bigEtaleRingedSite X)
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X) where
  u := Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X
  isMorphismOfSites := inclusion_isMorphismOfSites E X
  fsharp := 𝟙 _

/-- The morphism `π_X` of ringed sites presents the morphism of ringed topoi `π_X`. -/
theorem spacesEtaleRestrictionRingedSiteHom_toRingedToposSiteHom :
    (spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom =
      spacesEtaleRestrictionRingedHom E X :=
  rfl

/-- If an `𝒪_X`-module `𝓕` has a global presentation over an object `W` of the spaces-étale site
of `X`, then `π_X^*𝓕` has a global presentation over `W` seen in the big étale site of `X`. -/
theorem hasGlobalPresentation_over_pullback
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).O))
    (W : Space.SpacesEtale E.fppfSite S E.fppf_mem X) (hF : (F.over W).HasGlobalPresentation) :
    (((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F).over
      ((Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X).obj W)).HasGlobalPresentation := by
  have : HasFiniteLimits (Space.SpacesEtale E.fppfSite S E.fppf_mem X) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  have : PreservesFiniteLimits (spacesEtaleRestrictionRingedSiteHom E X).u :=
    inferInstanceAs (PreservesFiniteLimits (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X))
  exact Stacks.Sheaves.LocalizedPullback.hasGlobalPresentation_over_pullbackTopos
    (spacesEtaleRestrictionRingedSiteHom E X) W hF

/-- The objects of the big étale site of `X` represented by an affine scheme over which the
pullback `π_X^*𝓕` of a module has a global presentation. -/
def IsPresentedAffine
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).O)) :
    ObjectProperty (Over X) :=
  fun W ↦ IsAffineSchemeOver E X W ∧
    (((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F).over
      W).HasGlobalPresentation

/-- For a quasi-coherent module `𝓕`, the affine objects of the big étale site of `X` over which
`π_X^*𝓕` has a global presentation form a cover-dense subcategory. -/
instance isCoverDense_isPresentedAffine
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).O))
    [hF : F.IsQuasicoherentOnSite] :
    (IsPresentedAffine E X F).ι.IsCoverDense (E.bigEtaleTopology X) where
  is_cover V := by
    have hcp := CoverPreserving.of_isContinuous
      (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (E.bigEtaleTopology X)
    obtain ⟨I, Vi, fi, hcov, hpres⟩ := hF.locally_hasGlobalPresentation
      (Space.SpacesEtale.final E.fppfSite S E.fppf_mem X)
    have h1 := hcp.cover_preserve hcov
    have h2 := GrothendieckTopology.pullback_stable _ (Over.mkIdTerminal.from V) h1
    refine GrothendieckTopology.superset_covering _ ?_
      (GrothendieckTopology.bind_covering _ h2
        (fun W _ _ ↦ BigEtaleSpaceSite.generate_affineSchemePresieve_mem _ W))
    rintro Z _ ⟨W, g, z, hg, hz, rfl⟩
    obtain ⟨Z', z₁, z₂, hz₂, rfl⟩ := hz
    obtain ⟨Y', f', h', hf', he⟩ := hg
    obtain ⟨Y'', k, f'', ⟨i⟩, rfl⟩ := hf'
    refine ⟨⟨⟨Z', ⟨hz₂, ?_⟩⟩, z₁, z₂ ≫ z, (Category.assoc _ _ _).symm⟩⟩
    exact SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} _
      (z₂ ≫ h' ≫ (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X).map k)
      (hasGlobalPresentation_over_pullback E X F _ (hpres i))

end AlgebraicGeometry.BigEtaleSpaceSite

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite) (X : T.Spaces)

/-- An `𝒪_X`-module on the spaces-étale site of `X`, read on the spaces-étale site of `X` seen as
an algebraic space of the big étale site: the two sites coincide once the fppf site of schemes of
the big étale site is identified with the one of `T`. -/
noncomputable def toEtaleSpaceModules :
    SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O) ⥤
    SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h X)).O) := by
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    exact 𝟭 _

namespace AffineSchemesOver

variable {X : T.Spaces} {V : BigFppfSpaceOver T X} (K : GrothendieckTopology (Over V))
  [hcd : (toSlice T V).IsCoverDense K]

/-- The ring presheaf of the affine schemes over `V`, for the topology induced from `K` and a
sheaf of rings on the slice with the sections of the big fppf structure sheaf, has commuting
sections. -/
theorem commSections_ringRestriction (R : Sheaf K RingCat.{u + 1})
    (hR : R.obj = (sliceRingSheaf (T := T) (V := V)).obj) :
    Stacks.TerminalBaseChange.CommSections
      (Stacks.DenseSubsiteModules.ringRestriction ((toSlice T V).inducedTopology K) K
        (toSlice T V) R).obj := by
  obtain ⟨P, hP⟩ := R
  change P = _ at hR
  subst hR
  exact inferInstanceAs (Stacks.TerminalBaseChange.CommSections (ringPresheaf (T := T) (V := V)))

/-- **The base change presheaf is a sheaf for the topology induced from any topology on the
slice for which every big fppf sheaf is a sheaf.** -/
theorem baseChangeIsSheaf_of_isSheaf (R : Sheaf K RingCat.{u + 1})
    (hR : R.obj = (sliceRingSheaf (T := T) (V := V)).obj)
    (hK : ∀ P : Sheaf ((BigFppfSpaceOver.topology T X).over V) AddCommGrpCat.{u + 1},
      Presheaf.IsSheaf K P.obj)
    (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ V.left) :
    haveI := commSections_ringRestriction T K R hR
    Stacks.DenseSubsiteBaseChange.BaseChangeIsSheaf ((toSlice T V).inducedTopology K) K
      (toSlice T V) R (isTerminalOfIso V₀ hV₀ e) := by
  obtain ⟨P, hP⟩ := R
  change P = _ at hR
  subst hR
  intro M
  let Pab := (SheafOfModules.toSheaf _).obj ((associatedSheaf V₀ hV₀ e).obj M)
  let Q : Sheaf K AddCommGrpCat.{u + 1} := ⟨Pab.obj, hK Pab⟩
  let eb₀ := (sheafToPresheaf _ _).mapIso ((SheafOfModules.toSheaf _).mapIso
      ((Stacks.DenseSubsiteBaseChange.associatedSheafRestrictionIso
        (baseChangeIsSheaf V₀ hV₀ e)).app M))
  let eb : (toSlice T V).op ⋙ Q.obj ≅
      ((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1} (ringPresheaf (T := T) (V := V))
          (isTerminalOfIso V₀ hV₀ e)).obj M).presheaf := eb₀
  exact (Presheaf.isSheaf_of_iso_iff eb).1 ((toSlice T V).op_comp_isSheaf _ _ Q)

end AffineSchemesOver

set_option maxHeartbeats 1000000 in
-- the proof elaborates sheafification and module pullback along the fppf-to-étale ringed hom
set_option synthInstance.maxHeartbeats 400000 in
-- instance search for sheafification on the slices of the big fppf site is expensive
open AffineSchemesOver Stacks.DenseSubsiteBaseChange in
/-- **The unit of `ε_X^* ⊣ ε_{X,*}` is invertible on sections over an affine object** over which
the module has a global presentation. -/
theorem isIso_fppfToBigEtale_unit_val_app_of_hasGlobalPresentation
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (E.bigEtaleRingedSite (etaleSpace T E h X)).O))
    {W : Over (etaleSpace T E h X)} (hW : BigEtaleSpaceSite.IsAffineSchemeOver E _ W)
    (hG : (G.over W).HasGlobalPresentation) :
    IsIso (((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (fppfToBigEtaleRingedHom T E h X).ringedToposHom).unit.app G).val.app (op W)) := by
  have i1 : PLift (HasWeakSheafify (bigFppfRingedSite T X).J AddCommGrpCat.{u + 1}) :=
    ⟨inferInstance⟩
  have i2 : PLift ((bigFppfRingedSite T X).J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}) :=
    ⟨inferInstance⟩
  have hK0 : ∀ P : Sheaf ((bigFppfRingedSite T X).over
        ((fppfToBigEtaleRingedHom T E h X).u.obj W)).J AddCommGrpCat.{u + 1},
      Presheaf.IsSheaf ((E.bigEtaleRingedSite (etaleSpace T E h X)).over W).J
        (((fppfToBigEtaleRingedHom T E h X).localized W).u.op ⋙ P.obj) := by
    intro P
    have := ((fppfToBigEtaleRingedHom T E h X).localized W).isMorphismOfSites.isContinuous
    exact ((((fppfToBigEtaleRingedHom T E h X).localized W).u.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} _ _).obj P).property
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    let E' : BigEtaleSpaceSite S := ⟨eSchemeSite, eSchemeMem, T.schemeSite, eFppfMem, eInitial,
      eInitialSmall, eInitialEtale, eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite,
      eRepresentative⟩
    obtain ⟨V₀, hV₀, ⟨e⟩⟩ := hW
    obtain ⟨p⟩ :=
      SheafOfModules.HasGlobalPresentation.nonempty_presentation.{u + 1, u + 1, u + 1} hG
    let Y := E'.bigEtaleRingedSite (etaleSpace T E' rfl X)
    let f : RingedSite.Hom (bigFppfRingedSite T X) Y :=
      { u := 𝟭 (BigFppfSpaceOver T X)
        isMorphismOfSites := (fppfToBigEtaleRingedHom T E' rfl X).isMorphismOfSites
        fsharp := (fppfToBigEtaleRingedHom T E' rfl X).fsharp }
    have hf : fppfToBigEtaleRingedHom T E' rfl X = f :=
      RingedSite.Hom.ext_of_heq _ _ rfl HEq.rfl
    let W' : BigFppfSpaceOver T X := W
    let Wy : Y.C := W
    let K : GrothendieckTopology (Over Wy) := Y.J.over Wy
    let R : Sheaf K RingCat.{u + 1} := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over Wy
    let A₀ : AffineSchemesOver T W' := ofIso V₀ hV₀ e
    let vs : AffineSchemesOver T W' ⥤ Over Wy := toSlice T W'
    have : vs.Full := inferInstanceAs (toSlice T W').Full
    have : vs.Faithful := inferInstanceAs (toSlice T W').Faithful
    have hcd : vs.IsCoverDense K :=
      toSlice_isCoverDense_of_generate_mem W' (E'.bigEtaleTopology X)
        (fun Y => BigEtaleSpaceSite.generate_affineSchemePresieve_mem E' Y)
    have : Stacks.TerminalBaseChange.CommSections
        (Stacks.DenseSubsiteModules.ringRestriction (vs.inducedTopology K) K vs R).obj :=
      commSections_ringRestriction T _ (hcd := hcd) R rfl
    have hs : Stacks.DenseSubsiteBaseChange.BaseChangeIsSheaf (vs.inducedTopology K) K vs R
        (isTerminalOfIso V₀ hV₀ e) :=
      baseChangeIsSheaf_of_isSheaf T _ (hcd := hcd) R rfl hK0 V₀ hV₀ e
    let hT : IsTerminal (vs.obj A₀) := isTerminal_toSlice_ofIso V₀ hV₀ e
    have iK1 : HasSheafify K AddCommGrpCat.{u + 1} := inferInstance
    have iK2 : K.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance
    have iD : vs.IsDenseSubsite (vs.inducedTopology K) K := inferInstance
    have iL : ∀ X, HasLimitsOfShape (StructuredArrow X vs.op) AddCommGrpCat.{u + 1} :=
      fun _ => HasLimitsOfSize.has_limits_of_shape _
    have iK3 : (vs.sheafPushforwardContinuous AddCommGrpCat.{u + 1} (vs.inducedTopology K)
      K).IsEquivalence := inferInstance
    obtain ⟨M, ⟨i⟩⟩ := exists_iso_associatedSheaf_of_presentation hs hT p
    let t : Over Wy := vs.obj A₀
    let hb := AffineSchemesOver.baseChangeIsSheaf (V := W') V₀ hV₀ e
    let ψ : ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over Wy).obj.obj (op t) ≃+*
        (ringPresheaf (T := T) (V := W')).obj (op A₀) := RingEquiv.refl _
    let Eq := ModuleCat.restrictScalarsEquivalenceOfRingEquiv ψ
    let adjS := associatedSheafAdj hs
    let ffS := associatedSheafFullyFaithful hs
    let adjB := associatedSheafAdj hb
    let ffB := associatedSheafFullyFaithful hb
    let e₂ : (f.localized Wy).toRingedToposSiteHom.pushforwardTopos ⋙
        SheafOfModules.evaluation.{u + 1}
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over Wy) (op t) ≅
        SheafOfModules.evaluation.{u + 1}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfRingedSite T X).O).over (f.u.obj Wy))
          (op ((Over.post f.u).obj t)) ⋙ Eq.functor :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext; rfl)
    let j : t.left ≅ W := Over.isoMk (f := Over.mk (e.hom ≫ W.hom)) (g := W) e rfl
    have key := @RingedSite.Hom.isIso_unit_val_app_of_fullyFaithful _ _ f i1.down i2.down Wy G t
      (associatedSheaf hs) adjS ffS
      (associatedSheaf hb) adjB ffB Eq e₂ M i W j
    rw [← hf] at key
    convert key using 3

/-- **The unit `π_X^*𝓕 ⟶ ε_{X,*}ε_X^*π_X^*𝓕` is an isomorphism** for a quasi-coherent module
`𝓕` on the spaces-étale site. -/
theorem isIso_fppfToBigEtale_unit_app_pullback
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h X)).O))
    [F.IsQuasicoherentOnSite] :
    IsIso ((fppfToBigEtaleRingedHom T E h
      X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app
      ((BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos.obj F)) :=
  (fppfToBigEtaleRingedHom T E h
    X).isIso_pullbackPushforwardAdjunctionTopos_unit_app_of_isCoverDense
    _ (BigEtaleSpaceSite.IsPresentedAffine E (etaleSpace T E h X) F).ι
    (fun U ↦ isIso_fppfToBigEtale_unit_val_app_of_hasGlobalPresentation T E h X _ U.property.1
      U.property.2)

/-- **`a_X = π_X ∘ ε_X` on pullbacks**: `a_X^* ≅ ε_X^* ∘ π_X^*`, the spaces-étale site of `X`
being read on the big étale site of `X` through `toEtaleSpaceModules`. -/
theorem nonempty_pullbackTopos_iso_comp :
    Nonempty ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos ≅
      toEtaleSpaceModules T E h X ⋙
        (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
          (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos ⋙
        (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pullbackTopos) := by
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    let E' : BigEtaleSpaceSite S := ⟨eSchemeSite, eSchemeMem, T.schemeSite, eFppfMem, eInitial,
      eInitialSmall, eInitialEtale, eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite,
      eRepresentative⟩
    have hcomp : (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E'
        (etaleSpace T E' rfl X)).toRingedToposSiteHom.comp
        (fppfToBigEtaleRingedHom T E' rfl X).toRingedToposSiteHom =
        (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom := by
      refine RingedToposSiteHom.ext_of_heq _ _ rfl (heq_of_eq ?_)
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext U
      ext x
      rfl
    rw [← hcomp]
    exact ⟨(RingedToposSiteHom.pullbackToposComp
        (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E'
          (etaleSpace T E' rfl X)).toRingedToposSiteHom
        (fppfToBigEtaleRingedHom T E' rfl X).toRingedToposSiteHom).symm ≪≫
      (Functor.leftUnitor _).symm⟩

/-- **Stacks 0DGN (6), the `ε_X` half: `ε_{X,*}a_X^*𝓕 ≅ π_X^*𝓕`** for a quasi-coherent
`𝒪_X`-module `𝓕` on the spaces-étale site of `X`. -/
theorem nonempty_fppfToBigEtale_pushforward_pullback_iso
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [hF : F.IsQuasicoherentOnSite] :
    Nonempty ((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.obj
        ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F) ≅
      (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos.obj
          ((toEtaleSpaceModules T E h X).obj F)) := by
  obtain ⟨c⟩ := nonempty_pullbackTopos_iso_comp T E h X
  have : ((toEtaleSpaceModules T E h X).obj F).IsQuasicoherentOnSite := by
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      change T.schemeSite = eFppfSite at h
      cases h
      exact hF
  have := isIso_fppfToBigEtale_unit_app_pullback T E h X ((toEtaleSpaceModules T E h X).obj F)
  exact ⟨(fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.mapIso
    (c.app F) ≪≫ (asIso ((fppfToBigEtaleRingedHom T E h
      X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app _)).symm⟩

end AlgebraicGeometry.BigFppfSpaceSite
