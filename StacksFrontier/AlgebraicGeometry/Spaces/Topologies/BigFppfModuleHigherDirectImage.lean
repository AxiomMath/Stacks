module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffinePresentedModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfEtaleRingedComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherent

/-!
# Higher direct images along `a_X` and `ε_X` of pulled back quasi-coherent modules

Let `T` be a big fppf site of algebraic spaces over a scheme `S` and `X` one of its objects, and
let `a_X : ((Spaces/X)_fppf, 𝒪) ⟶ (X_{spaces,étale}, 𝒪_X)` be the morphism of ringed sites of
Stacks 0DGM. For an `𝒪_X`-module `𝓕` with a global presentation over an object `W` of the
spaces-étale site, the pullback `a_X^*𝓕` has a global presentation over the image of `W`; for a
quasi-coherent `𝓕` the higher direct images of `a_X^*𝓕` along `a_X` and along the
change-of-topology morphism `ε_X` to the big étale site vanish.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.hasGlobalPresentation_over_pullback`: global
  presentations travel along `a_X^*`.
* `AlgebraicGeometry.BigFppfSpaceSite.isZero_rightDerived_pushforward_pullback`:
  `R^p a_{X,*}(a_X^*𝓕) = 0` for `p > 0`.
* `AlgebraicGeometry.BigFppfSpaceSite.isZero_rightDerived_fppfToBigEtale_pushforward_pullback`:
  `R^p ε_{X,*}(a_X^*𝓕) = 0` for `p > 0`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces}

/-- **Global presentations travel along `a_X^*`**: if an `𝒪_X`-module `𝓕` has a global
presentation over an object `W` of the spaces-étale site of `X`, then its pullback to
`(Spaces/X)_fppf` has a global presentation over the image of `W`. -/
theorem hasGlobalPresentation_over_pullback
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    (W : Space.SpacesEtale T.schemeSite S T.scheme_mem X) (hF : (F.over W).HasGlobalPresentation) :
    (((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F).over
      ((Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).obj W)).HasGlobalPresentation :=
  Stacks.Sheaves.LocalizedPullback.hasGlobalPresentation_over_pullbackTopos
    (fppfToSpacesEtaleRingedSiteHom T X) W hF

/-- The objects of the spaces-étale site of `X` represented by an affine scheme over which a
module has a global presentation. -/
def presentedAffinePresieve
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    (V : Space.SpacesEtale T.schemeSite S T.scheme_mem X) : Presieve V :=
  fun W _ ↦ Space.SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem X W ∧
    (F.over W).HasGlobalPresentation

/-- **A quasi-coherent module is presented over a covering family of affine objects** of every
object of the spaces-étale site. -/
theorem generate_presentedAffinePresieve_mem
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [hF : F.IsQuasicoherentOnSite] (V : Space.SpacesEtale T.schemeSite S T.scheme_mem X) :
    Sieve.generate (presentedAffinePresieve F V) ∈
      Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X V := by
  obtain ⟨I, Vi, fi, hcov, hpres⟩ := hF.locally_hasGlobalPresentation V
  refine (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).superset_covering ?_
    ((Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).bind_covering hcov
      (fun Y _ _ ↦ Space.SpacesEtale.generate_affineSchemePresieve_mem T.schemeSite S
        T.scheme_mem X Y))
  rintro Z _ ⟨Y, g, z, ⟨Z', z₁, z₂, ⟨i⟩, rfl⟩, ⟨Z'', g₁, g₂, hg₂, rfl⟩, rfl⟩
  refine ⟨Z'', g₁, g₂ ≫ z₁ ≫ fi i, ⟨hg₂, ?_⟩, by simp⟩
  exact SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} F (g₂ ≫ z₁) (hpres i)

/-- The functor of `a_X`, read through the morphism of ringed topoi, is continuous. -/
instance fppfToSpacesEtale_isContinuous :
    (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.u.IsContinuous
      (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X)
      (BigFppfSpaceOver.topology T X) :=
  (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.isContinuous

/-- The direct image along `a_X` of sheaves of modules is additive. -/
instance fppfToSpacesEtale_pushforward_additive :
    (SheafOfModules.pushforward.{u + 1}
      (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.fSharpRing).Additive where
  map_add := by intros; rfl

/-- The direct image along `a_X` of sheaves of modules is additive. -/
instance fppfToSpacesEtale_pushforwardTopos_additive :
    (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos.Additive where
  map_add := by intros; rfl

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- **The higher direct images along `a_X` of the pullback of a quasi-coherent module vanish**:
`R^p a_{X,*}(a_X^*𝓕) = 0` for `p > 0`. -/
theorem isZero_rightDerived_pushforward_pullback
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [F.IsQuasicoherentOnSite] (p : ℕ) (hp : 0 < p) :
    IsZero
      ((((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos).rightDerived
        p).obj
          ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve.{
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.u _ _
    (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.fSharpRing (q + 1) _ (fun V ↦ ?_)
  refine ⟨presentedAffinePresieve F V, generate_presentedAffinePresieve_mem F V,
    fun W g hg ↦ ?_⟩
  refine
    Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'_chgUniv
      _ _ _ q _ ?_
  exact isZero_H'_of_hasGlobalPresentation _ _ hg.1 (hasGlobalPresentation_over_pullback F W hg.2)
    (q + 1) (Nat.succ_pos q)

section Epsilon

variable (E : BigEtaleSpaceSite S) (h : T.schemeSite = E.fppfSite)

/-- The objects `W` of the big étale site of `X` whose image under `ε_X` is affine and maps to an
object of the spaces-étale site of `X` over which a module has a global presentation. -/
def epsilonPresentedAffinePresieve
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    (V : Over (etaleSpace T E h X)) : Presieve V :=
  fun W _ ↦ BigFppfSpaceOver.IsAffineSchemeOver T X
      ((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u.obj W) ∧
    ∃ Y : Space.SpacesEtale T.schemeSite S T.scheme_mem X, (F.over Y).HasGlobalPresentation ∧
      Nonempty ((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u.obj W ⟶
        (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).obj Y)

/-- **A quasi-coherent module is presented, after `ε_X`, over a covering family of affine objects**
of every object of the big étale site of `X`. -/
theorem generate_epsilonPresentedAffinePresieve_mem
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [hF : F.IsQuasicoherentOnSite] (V : Over (etaleSpace T E h X)) :
    Sieve.generate (epsilonPresentedAffinePresieve E h F V) ∈
      E.bigEtaleTopology (etaleSpace T E h X) V := by
  have hcp := CoverPreserving.of_isContinuous
    (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem (etaleSpace T E h X))
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
    (E.bigEtaleTopology (etaleSpace T E h X))
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    obtain ⟨I, Vi, fi, hcov, hpres⟩ := hF.locally_hasGlobalPresentation
      (Space.SpacesEtale.final T.schemeSite S T.scheme_mem X)
    refine GrothendieckTopology.superset_covering _ ?_
      (GrothendieckTopology.bind_covering _
        (GrothendieckTopology.pullback_stable _ (Over.mkIdTerminal.from V)
          (hcp.cover_preserve hcov))
        (fun W _ _ ↦ BigEtaleSpaceSite.generate_affineSchemePresieve_mem _ W))
    rintro Z _ ⟨W, g, z, ⟨Y', f', h', ⟨Y'', k, f'', ⟨i⟩, rfl⟩, he⟩, ⟨Z', z₁, z₂, hz₂, rfl⟩, rfl⟩
    refine ⟨Z', z₁, z₂ ≫ z, ⟨hz₂, Y', ?_, ⟨Over.homMk (z₂ ≫ h').left ?_⟩⟩, by simp⟩
    · exact SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} F k (hpres i)
    · exact (Over.w (z₂ ≫ h')).trans (Category.comp_id _).symm

/-- The functor of `ε_X`, read through the morphism of ringed topoi, is continuous. -/
instance fppfToBigEtaleRingedHom_isContinuous :
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u.IsContinuous
      (E.bigEtaleTopology (etaleSpace T E h X)) (BigFppfSpaceOver.topology T X) :=
  (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.isContinuous

/-- The direct image along `ε_X` of sheaves of modules is additive. -/
instance fppfToBigEtaleRingedHom_pushforward_additive :
    (SheafOfModules.pushforward.{u + 1}
      (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.fSharpRing).Additive where
  map_add := by intros; rfl

/-- The direct image along `ε_X` of sheaves of modules is additive. -/
instance fppfToBigEtaleRingedHom_pushforwardTopos_additive :
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.Additive where
  map_add := by intros; rfl

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- **The higher direct images along `ε_X` of the pullback of a quasi-coherent module vanish**:
`R^p ε_{X,*}(a_X^*𝓕) = 0` for `p > 0`. -/
theorem isZero_rightDerived_fppfToBigEtale_pushforward_pullback
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [F.IsQuasicoherentOnSite] (p : ℕ) (hp : 0 < p) :
    IsZero ((((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos).rightDerived
      p).obj ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve.{
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u _ _
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.fSharpRing (q + 1) _ (fun V ↦ ?_)
  refine ⟨epsilonPresentedAffinePresieve E h F V,
    generate_epsilonPresentedAffinePresieve_mem E h F V, fun W g hg ↦ ?_⟩
  obtain ⟨hW, Y, hY, ⟨φ⟩⟩ := hg
  refine
    Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'_chgUniv
      _ _ _ q _ ?_
  exact isZero_H'_of_hasGlobalPresentation _ _ hW
    (SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} _ φ
      (hasGlobalPresentation_over_pullback F Y hY)) (q + 1) (Nat.succ_pos q)

end Epsilon

end AlgebraicGeometry.BigFppfSpaceSite

end
