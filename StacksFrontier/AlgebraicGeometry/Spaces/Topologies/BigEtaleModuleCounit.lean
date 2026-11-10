module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSpaceSiteOfBigEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtaleModulePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherentOfHom

/-!
# The counit of `π_X^* ⊣ π_{X,*}` on quasi-coherent modules

Let `π_X : ((Spaces/X)_étale, 𝒪) ⟶ (X_{spaces,étale}, 𝒪_X)` be the morphism of Stacks 0DGM. A
quasi-coherent module `𝓖` on the big étale site of `X` is a sheaf for the fppf topology: the
unit `𝓖 ⟶ ε_{X,*}ε_X^*𝓖` is invertible, on the affine objects over which `𝓖` is presented by the
argument of Stacks 0DGN (6) and hence everywhere. Then Stacks 0DGN (5) and (6) for `a_X` show
that `𝓖 ≅ π_X^*𝓗` with `𝓗 = a_{X,*}ε_X^*𝓖` quasi-coherent, so the counit
`π_X^*π_{X,*}𝓖 ⟶ 𝓖` is invertible and `π_{X,*}𝓖` is quasi-coherent. The auxiliary big fppf
site is `AlgebraicGeometry.BigEtaleSpaceSite.bigFppfSpaceSite`, so the results on `π_X` mention
none.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToBigEtale_unit_app_of_isQuasicoherentOnSite`:
  the unit `𝓖 ⟶ ε_{X,*}ε_X^*𝓖` is an isomorphism for a quasi-coherent `𝓖`.
* `AlgebraicGeometry.BigEtaleSpaceSite.exists_isQuasicoherentOnSite_iso_pullback`: every
  quasi-coherent module on the big étale site of `X` is `π_X^*𝓗` with `𝓗` quasi-coherent.
* `BigEtaleSpaceSite.isIso_spacesEtaleRestriction_counit_app_of_isQuasicoherentOnSite`: the counit
  `π_X^*π_{X,*}𝓖 ⟶ 𝓖` is an isomorphism and `π_{X,*}𝓖` is quasi-coherent.

## References

* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u


namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (E : BigEtaleSpaceSite S) (X : E.Spaces)

/-- The objects of the big étale site of `X` represented by an affine scheme over which a module
has a global presentation. -/
def IsPresentedAffineModule
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (E.bigEtaleRingedSite X).O)) :
    ObjectProperty (Over X) :=
  fun W ↦ IsAffineSchemeOver E X W ∧ (G.over W).HasGlobalPresentation

/-- For a quasi-coherent module, the affine objects over which it has a global presentation are
cover-dense in the big étale site. -/
instance isCoverDense_isPresentedAffineModule
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (E.bigEtaleRingedSite X).O))
    [hG : G.IsQuasicoherentOnSite] :
    (IsPresentedAffineModule E X G).ι.IsCoverDense (E.bigEtaleTopology X) where
  is_cover V := by
    obtain ⟨I, Vi, fi, hcov, hpres⟩ := hG.locally_hasGlobalPresentation V
    refine GrothendieckTopology.superset_covering _ ?_
      (GrothendieckTopology.bind_covering _ hcov
        (fun W _ _ ↦ BigEtaleSpaceSite.generate_affineSchemePresieve_mem _ W))
    rintro Z _ ⟨W, g, z, hg, hz, rfl⟩
    obtain ⟨Z', z₁, z₂, hz₂, rfl⟩ := hz
    obtain ⟨Y', a, f', ⟨i⟩, rfl⟩ := hg
    refine ⟨⟨⟨Z', ⟨hz₂, ?_⟩⟩, z₁, z₂ ≫ a ≫ fi i, by simp⟩⟩
    exact SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} _ (z₂ ≫ a) (hpres i)

end AlgebraicGeometry.BigEtaleSpaceSite

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite) (X : T.Spaces)

/-- **A quasi-coherent module on the big étale site of `X` is a sheaf for the fppf topology**: the
unit `G ⟶ ε_{X,*}ε_X^*G` is an isomorphism. -/
theorem isIso_fppfToBigEtale_unit_app_of_isQuasicoherentOnSite
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (E.bigEtaleRingedSite (etaleSpace T E h X)).O))
    [G.IsQuasicoherentOnSite] :
    IsIso ((fppfToBigEtaleRingedHom T E h
      X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app G) :=
  (fppfToBigEtaleRingedHom T E h
    X).isIso_pullbackPushforwardAdjunctionTopos_unit_app_of_isCoverDense
    _ (BigEtaleSpaceSite.IsPresentedAffineModule E (etaleSpace T E h X) G).ι
    (fun U ↦ isIso_fppfToBigEtale_unit_val_app_of_hasGlobalPresentation T E h X _ U.property.1
      U.property.2)

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the sheaf-of-modules structures on the big étale ringed site is slow
/-- The pullback along `ε_X` of a quasi-coherent module is quasi-coherent (Stacks 03DO). -/
theorem isQuasicoherentOnSite_fppfToBigEtale_pullbackTopos
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (E.bigEtaleRingedSite (etaleSpace T E h X)).O))
    [hG : G.IsQuasicoherentOnSite] :
    ((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pullbackTopos.obj
      G).IsQuasicoherentOnSite :=
  Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom
    (fppfToBigEtaleRingedHom T E h X)
    (fun A ↦ ⟨(Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).functor.obj A,
      ⟨(Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).unitIso.hom.app A⟩⟩) hG

/-- **Every quasi-coherent module on the big étale site of `X` is `π_X^*𝓗` for a quasi-coherent
`𝒪_X`-module `𝓗`**. -/
theorem exists_isQuasicoherentOnSite_iso_pullback
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (E.bigEtaleRingedSite (etaleSpace T E h X)).O))
    [G.IsQuasicoherentOnSite] :
    ∃ H : SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O),
      H.IsQuasicoherentOnSite ∧
      Nonempty (G ≅ (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos.obj
          ((toEtaleSpaceModules T E h X).obj H)) := by
  let ε := (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom
  let a := (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom
  have := isIso_fppfToBigEtale_unit_app_of_isQuasicoherentOnSite T E h X G
  have := isQuasicoherentOnSite_fppfToBigEtale_pullbackTopos T E h X G
  let G' := ε.pullbackTopos.obj G
  let H := a.pushforwardTopos.obj G'
  have : H.IsQuasicoherentOnSite := isQuasicoherentOnSite_pushforward_of_isQuasicoherentOnSite G'
  have := isIso_counit_app_of_isQuasicoherentOnSite G'
  obtain ⟨c⟩ := nonempty_fppfToBigEtale_pushforward_pullback_iso T E h X H
  exact ⟨H, inferInstance, ⟨asIso (ε.pullbackPushforwardAdjunctionTopos.unit.app G) ≪≫
    ε.pushforwardTopos.mapIso (asIso (a.pullbackPushforwardAdjunctionTopos.counit.app G')).symm ≪≫
    c⟩⟩

end AlgebraicGeometry.BigFppfSpaceSite

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (E : BigEtaleSpaceSite S) (X : E.Spaces)

/-- **Every quasi-coherent module on `((Spaces/X)_étale, 𝒪)` is `π_X^*𝓗` for a quasi-coherent
`𝒪_X`-module `𝓗`**. -/
theorem exists_isQuasicoherentOnSite_iso_pullback
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (E.bigEtaleRingedSite X).O))
    [hG : G.IsQuasicoherentOnSite] :
    ∃ H : SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).O),
      H.IsQuasicoherentOnSite ∧
      Nonempty (G ≅ (spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        H) := by
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    let E' : BigEtaleSpaceSite S := ⟨eSchemeSite, eSchemeMem, eFppfSite, eFppfMem, eInitial,
      eInitialSmall, eInitialEtale, eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite,
      eRepresentative⟩
    exact @BigFppfSpaceSite.exists_isQuasicoherentOnSite_iso_pullback _ E'.bigFppfSpaceSite E' rfl X
      G hG

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the sheaf-of-modules structures on the spaces-étale ringed site is slow
/-- The pullback along `π_X` of a quasi-coherent module is quasi-coherent (Stacks 03DO). -/
theorem isQuasicoherentOnSite_spacesEtaleRestriction_pullbackTopos
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).O))
    [hF : F.IsQuasicoherentOnSite] :
    ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
      F).IsQuasicoherentOnSite :=
  Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom
    (spacesEtaleRestrictionRingedSiteHom E X)
    (fun A ↦ ⟨Space.SpacesEtale.final E.fppfSite S E.fppf_mem X, ⟨Over.homMk A.hom⟩⟩) hF

/-- **For a quasi-coherent module `𝓖` on the big étale site of `X` the counit
`π_X^*π_{X,*}𝓖 ⟶ 𝓖` is an isomorphism and `π_{X,*}𝓖` is quasi-coherent**. -/
theorem isIso_spacesEtaleRestriction_counit_app_of_isQuasicoherentOnSite
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (E.bigEtaleRingedSite X).O))
    [G.IsQuasicoherentOnSite] :
    IsIso ((spacesEtaleRestrictionRingedSiteHom E
      X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.counit.app G) ∧
    ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pushforwardTopos.obj
      G).IsQuasicoherentOnSite := by
  obtain ⟨H, hH, ⟨e⟩⟩ := exists_isQuasicoherentOnSite_iso_pullback E X G
  let adj := (spacesEtaleRestrictionRingedSiteHom E
    X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
  have := isIso_spacesEtaleRestriction_unit E X
  have h₁ : IsIso (adj.counit.app
      ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj H)) := by
    rw [← IsIso.inv_eq_of_hom_inv_id (adj.left_triangle_components H)]
    infer_instance
  refine ⟨?_, ?_⟩
  · rw [(Iso.eq_comp_inv e).2 (adj.counit_naturality e.hom).symm]
    infer_instance
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso (asIso (adj.unit.app H) ≪≫
      (spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pushforwardTopos.mapIso e.symm)
      hH

end AlgebraicGeometry.BigEtaleSpaceSite

end
