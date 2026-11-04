module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleAssociatedModulePullbackEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing

/-!
# Derived direct images along `ε_X` and `a_X` of pulled back quasi-coherent modules

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site over the
same big fppf site of schemes, `X` an object of `T` and `𝓕` a quasi-coherent `𝒪_X`-module on
the spaces-étale site of `X`. The module `a_X^*𝓕` is right acyclic for `ε_{X,*}` and for
`a_{X,*}`; with Stacks 0DGN (6) this says that `π_X^*𝓕 ⟶ Rε_{X,*}(a_X^*𝓕)` and
`𝓕 ⟶ Ra_{X,*}(a_X^*𝓕)` are isomorphisms (Stacks 0DGP).

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.rightAcyclic_pushforward_pullback`,
  `AlgebraicGeometry.BigFppfSpaceSite.rightAcyclic_fppfToBigEtale_pushforward_pullback`:
  `a_X^*𝓕` is right acyclic for `a_{X,*}` and for `ε_{X,*}`.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_derivedPushforward_pullback_of_quasicoherent`:
  `π_X^*𝓕 ≅ ε_{X,*}(a_X^*𝓕)` and the unit `𝓕 ⟶ a_{X,*}(a_X^*𝓕)` is an isomorphism, with
  `a_X^*𝓕` right acyclic for `ε_{X,*}` and for `a_{X,*}` (Stacks 0DGP).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces}

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Sheaves of modules on the big fppf ringed site of `X` have enough injectives. -/
theorem enoughInjectives_bigFppfModules :
    EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X)).O)) :=
  inferInstance

attribute [local instance] enoughInjectives_bigFppfModules

/-- Sheaves of modules on the spaces-étale ringed topos of `X` form an abelian category, read at
the universes of the ringed topos. -/
noncomputable local instance abelian_spacesEtaleRingedToposModules :
    Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X)).O)) :=
  inferInstance

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- **`a_X^*𝓕` is right acyclic for `a_{X,*}`**: the canonical map `a_{X,*}a_X^*𝓕 ⟶ Ra_{X,*}a_X^*𝓕`
is an isomorphism for a quasi-coherent `𝓕`. -/
theorem rightAcyclic_pushforward_pullback
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [F.IsQuasicoherentOnSite] :
    Functor.rightAcyclic.{u + 2, u + 2}
      (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos
      ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F) := by
  refine Stacks.Cohomology.ModuleDirectImageOnACover.rightAcyclic_pushforward_of_presieve.{
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 2, u + 2}
    (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.u _ _
    (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.fSharpRing _ (fun p hp V ↦ ?_)
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by lia⟩
  refine ⟨presentedAffinePresieve F V, generate_presentedAffinePresieve_mem F V,
    fun W g hg ↦ ?_⟩
  open Stacks.Cohomology.ModuleDirectImageOnACover in
  refine isZero_rightDerived_evaluation_of_isZero_H'_chgUniv.{u + 1, u + 1, u + 1} _ _ _ q _ ?_
  exact isZero_H'_of_hasGlobalPresentation _ _ hg.1 (hasGlobalPresentation_over_pullback F W hg.2)
    (q + 1) (Nat.succ_pos q)

variable (E : BigEtaleSpaceSite S) (h : T.schemeSite = E.fppfSite)

/-- Sheaves of modules on the big étale ringed topos of the étale space of `X` form an abelian
category, read at the universes of the ringed topos. -/
noncomputable local instance abelian_bigEtaleRingedToposModules :
    Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (E.bigEtaleRingedSite (T.etaleSpace E h X))).O)) :=
  inferInstance

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- **`a_X^*𝓕` is right acyclic for `ε_{X,*}`**: the canonical map `ε_{X,*}a_X^*𝓕 ⟶ Rε_{X,*}a_X^*𝓕`
is an isomorphism for a quasi-coherent `𝓕`. -/
theorem rightAcyclic_fppfToBigEtale_pushforward_pullback
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [F.IsQuasicoherentOnSite] :
    Functor.rightAcyclic.{u + 2, u + 2}
      (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos
      ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F) := by
  refine Stacks.Cohomology.ModuleDirectImageOnACover.rightAcyclic_pushforward_of_presieve.{
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 2, u + 2}
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u _ _
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.fSharpRing _ (fun p hp V ↦ ?_)
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by lia⟩
  refine ⟨epsilonPresentedAffinePresieve E h F V,
    generate_epsilonPresentedAffinePresieve_mem E h F V, fun W g hg ↦ ?_⟩
  obtain ⟨hW, Y, hY, ⟨φ⟩⟩ := hg
  open Stacks.Cohomology.ModuleDirectImageOnACover in
  refine isZero_rightDerived_evaluation_of_isZero_H'_chgUniv.{u + 1, u + 1, u + 1} _ _ _ q _ ?_
  exact isZero_H'_of_hasGlobalPresentation _ _ hW
    (SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} _ φ
      (hasGlobalPresentation_over_pullback F Y hY)) (q + 1) (Nat.succ_pos q)

/-- **Stacks 0DGP**, at the underived direct images: for a quasi-coherent `𝒪_X`-module `𝓕` on the
spaces-étale site of `X`, there is an isomorphism `π_X^*𝓕 ≅ ε_{X,*}(a_X^*𝓕)` and `a_X^*𝓕` is right
acyclic for `ε_{X,*}`, and the unit `𝓕 ⟶ a_{X,*}(a_X^*𝓕)` is an isomorphism and `a_X^*𝓕` is right
acyclic for `a_{X,*}`. -/
theorem isIso_derivedPushforward_pullback_of_quasicoherent
    (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S) (h : T.schemeSite = E.fppfSite)
    (X : T.Spaces)
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [F.IsQuasicoherentOnSite] :
    (Nonempty ((BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos.obj
          ((toEtaleSpaceModules T E h X).obj F) ≅
        (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.obj
          ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F)) ∧
      Functor.rightAcyclic.{u + 2, u + 2}
        (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos
        ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F)) ∧
    (IsIso ((RingedToposSiteHom.pullbackPushforwardAdjunctionTopos
        (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom).unit.app F) ∧
      Functor.rightAcyclic.{u + 2, u + 2}
        (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos
        ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F)) := by
  obtain ⟨⟨e⟩, hunit⟩ := pushforward_pullback_of_quasicoherent T E h X F
  exact ⟨⟨⟨e.symm⟩, rightAcyclic_fppfToBigEtale_pushforward_pullback E h F⟩,
    hunit, rightAcyclic_pushforward_pullback F⟩

end AlgebraicGeometry.BigFppfSpaceSite

