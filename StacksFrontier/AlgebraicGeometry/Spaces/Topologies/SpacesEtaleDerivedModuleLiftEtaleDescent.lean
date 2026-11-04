module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedModuleLiftEssImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedModuleLiftPullback

/-!
# Descent of the essential image of `ι` along a surjective étale morphism

Let `a : U ⟶ X` be an étale morphism of algebraic spaces and let `j : U_{spaces,étale} ⥤
X_{spaces,étale}` be postcomposition with `a`. The pullback of modules along the morphism of
spaces-étale ringed topoi of `a` is restriction along `j`, so the sections of `a^*N` over
`W ⟶ U` are the sections of `N` over `W ⟶ U ⟶ X`. If `a` is moreover surjective, the
projection `V ×_X U ⟶ V` covers `V`, so the sections of `N` over `V` inject into those of
`a^*N` over `V ×_X U`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtalePostcompPushforwardAdjunction`: restriction
  of modules along `j` is left adjoint to the direct image along `a`.
* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtalePullbackModulesIsoPostcomp`: the pullback of
  modules along `a` is restriction along `j`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.small_val_obj_of_small_pullbackModules`: a module on
  `X_{spaces,étale}` whose pullback along a surjective étale `a` has `u`-small sections has
  `u`-small sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.BigEtaleSpaceSite

attribute [local instance 5000] SheafOfModules.instAbelian
-- No global `HasDerivedCategory` instance applies to modules on the small étale site, which is
-- not a `SmallCategory`; at low priority the standard model chooses nothing where a global one
-- exists. The spaces-étale model is passed explicitly.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 5000] Space.SmallEtale.instHasSheafify
  Space.SmallEtale.instWEqualsLocallyBijective

open Space.SimplicialSpacesEtaleSite Stacks.Cohomology.DerivedPullbackOfToposHom

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X U : T.Spaces} (a : U ⟶ X)
  (ha : Space.IsEtale T.fppfSite S T.fppf_mem a.hom)

/-- The structure map of restriction along postcomposition with an étale `a`: the rings of
sections over `W ⟶ U` and over `W ⟶ U ⟶ X` are both the global functions on `W`. -/
def spacesEtalePostcompRingSheafHom :
    Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem U).O ⟶
      ((Space.spacesEtalePostcomp T.fppfSite S T.fppf_mem a ha).sheafPushforwardContinuous
        RingCat.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem U)
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X).O) :=
  ObjectProperty.homMk (𝟙 _)

/-- **Restriction along postcomposition is left adjoint to the direct image**, on modules over
the spaces-étale sites, for an étale `a`. -/
def spacesEtalePostcompPushforwardAdjunction :
    SheafOfModules.pushforward.{u + 1} (spacesEtalePostcompRingSheafHom T a ha) ⊣
      (smallEtaleRingedSiteHom T a).pushforwardTopos :=
  SheafOfModules.pushforwardPushforwardAdj
    (Space.spacesEtalePostcompAdjunction T.fppfSite S T.fppf_mem a ha)
    (spacesEtalePostcompRingSheafHom T a ha) (smallEtaleRingedSiteHom T a).fSharpRing
    (by ext V x; rfl) (by
      refine NatTrans.ext (funext fun W ↦ ?_)
      have key := congrArg (Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem X).map
        ((Space.spacesEtalePostcompAdjunction T.fppfSite S T.fppf_mem a ha).left_triangle_components
          W.unop)
      rw [Functor.map_comp] at key
      replace key := key.trans ((Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem X).map_id _)
      have h := congrArg (fun g ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((Space.globalFunctionsPresheaf T.fppfSite S T.fppf_mem).map g.op)) key
      simp only [op_comp, Functor.map_comp, op_id] at h
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
      exact (Category.id_comp _).trans h)

/-- **The pullback of modules along an étale morphism of algebraic spaces is restriction along
postcomposition**, on the spaces-étale sites: both are left adjoint to the direct image. -/
def spacesEtalePullbackModulesIsoPostcomp :
    (spacesEtaleRingedToposHom a).toModulesHom.pullbackModules ≅
      SheafOfModules.pushforward.{u + 1} (spacesEtalePostcompRingSheafHom T a ha) :=
  spacesEtalePullbackModulesIsoPullbackTopos T a ≪≫
    (smallEtaleRingedSiteHom T a).pullbackPushforwardAdjunctionTopos.leftAdjointUniq
      (spacesEtalePostcompPushforwardAdjunction T a ha)

include ha in
/-- **Smallness of sections descends along a surjective étale morphism.** If the pullback of a
module `N` on `X_{spaces,étale}` along a surjective étale `a : U ⟶ X` has `u`-small sections,
so has `N`: its sections over `V` inject into those of `a^*N` over `V ×_X U`. -/
theorem small_val_obj_of_small_pullbackModules
    (hsurj : Space.IsSurjective T.fppfSite S T.fppf_mem a.hom)
    (N : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X).O))
    (hN : ∀ W, Small.{u}
      (((spacesEtaleRingedToposHom a).toModulesHom.pullbackModules.obj N).val.obj W))
    (V : (Space.SpacesEtale T.fppfSite S T.fppf_mem X)ᵒᵖ) : Small.{u} (N.val.obj V) := by
  let c := (Space.spacesEtalePostcompAdjunction T.fppfSite S T.fppf_mem a ha).counit.app V.unop
  have h₁ : Small.{u} (N.val.obj (op ((Space.spacesEtalePostcomp T.fppfSite S T.fppf_mem a ha).obj
      ((Space.spacesBaseChange T.fppfSite S T.fppf_mem a).functor.obj V.unop)))) :=
    @small_map _ _ (hN (op ((Space.spacesBaseChange T.fppfSite S T.fppf_mem a).functor.obj V.unop)))
      ((PresheafOfModules.evaluation _ _).mapIso ((SheafOfModules.forget _).mapIso
        ((spacesEtalePullbackModulesIsoPostcomp T a ha).app N))).toLinearEquiv.toEquiv.symm
  have hcov : Sieve.generate (Presieve.singleton c) ∈
      Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X V.unop := by
    rw [Space.SpacesEtale.mem_topology_iff_sievePointwiseCover]
    intro x
    obtain ⟨y, hy⟩ := Space.isSurjective_of_isPullback T.fppfSite S T.fppf_mem
      (IsPullback.of_hasPullback V.unop.1.hom a).flip hsurj x
    exact ⟨_, c, Sieve.le_generate _ _ _ (Presieve.singleton_self c), y, hy⟩
  have hinj : Function.Injective (N.val.presheaf.map c.op) := by
    intro x y hxy
    refine ((SheafOfModules.toSheaf _).obj N).isSeparated _ _ hcov x y ?_
    rintro Z f ⟨Z', g, k, hk, rfl⟩
    cases hk
    show N.val.presheaf.map (g ≫ c).op x = N.val.presheaf.map (g ≫ c).op y
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hxy]
  exact @small_of_injective _ _ h₁ _ hinj

include ha in
/-- **The essential image of `ι` descends along a surjective étale morphism.** Let `a : U ⟶ X`
be surjective and étale and let `K ∈ D_QCoh(𝒪_{X_{spaces,étale}})` be such that `La^*K ≅ ιL₀`
for some `L₀ ∈ D(𝒪_{U_étale})`. Then `K ≅ ιL` for some `L ∈ D_QCoh(𝒪_{X_étale})`. -/
theorem exists_toSpacesEtaleDerivedModules_obj_iso_of_derivedPullback_iso
    (hsurj : Space.IsSurjective T.fppfSite S T.fppf_mem a.hom)
    (K : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.fppfSite S T.fppf_mem X).O)) _ _
      (Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem X))
    (hK : @DerivedCategoryB.derivedCategoryB _ _ _
      (Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem X)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.spacesEtaleRingedSite T.fppfSite S T.fppf_mem X).O)) K)
    (L₀ : DerivedCategory (Space.Modules.{u, u} T.fppfSite S T.fppf_mem U.1 U.2))
    (e : (derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem U)
        (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
        (spacesEtaleRingedToposHom a)).obj K ≅
      (Space.toSpacesEtaleDerivedModules T.fppfSite S T.fppf_mem U).obj L₀) :
    ∃ L : DerivedCategory (Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2),
      Space.QcohDerived T.fppfSite S T.fppf_mem X L ∧
        Nonempty ((Space.toSpacesEtaleDerivedModules T.fppfSite S T.fppf_mem X).obj L ≅ K) := by
  let := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem X
  let := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem U
  have : (spacesEtaleRingedToposHom a).toModulesHom.pullbackModules.Additive :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_additive
      (spacesEtaleRingedToposHom a).toModulesHom
  have := Space.preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact a
    (Space.isFlat_of_isEtale T.fppfSite S T.fppf_mem ha)
  have : PreservesFiniteColimits (spacesEtaleRingedToposHom a).toModulesHom.pullbackModules :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_preservesFiniteColimits
      (spacesEtaleRingedToposHom a).toModulesHom
  let ε := Stacks.Homology.leftDerivedIsoMapDerivedCategory _
    (derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem U)
      (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X) (spacesEtaleRingedToposHom a))
    (derivedPullbackComparison (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem U)
      (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X) (spacesEtaleRingedToposHom a))
  refine Space.exists_toSpacesEtaleDerivedModules_obj_iso T.fppfSite S T.fppf_mem X K (fun q ↦ ?_)
  let N := (DerivedCategory.homologyFunctor _ q).obj K
  have eN : (spacesEtaleRingedToposHom a).toModulesHom.pullbackModules.obj N ≅
      (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem U).obj
        ((DerivedCategory.homologyFunctor _ q).obj L₀) :=
    ((Functor.mapDerivedCategoryHomologyFunctorIso
        (spacesEtaleRingedToposHom a).toModulesHom.pullbackModules q).app K).symm ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso (ε.app K).symm ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (Space.toSpacesEtaleDerivedModulesHomologyIso T.fppfSite S T.fppf_mem U q).app L₀
  have hsmall : ∀ V, Small.{u} (N.val.obj V) :=
    small_val_obj_of_small_pullbackModules T a ha hsurj N (fun W ↦ @small_map _ _
      (Space.small_toSpacesEtaleModules_obj T.fppfSite S T.fppf_mem U _ W)
      ((PresheafOfModules.evaluation _ W).mapIso
        ((SheafOfModules.forget _).mapIso eN)).toLinearEquiv.toEquiv)
  obtain ⟨M, ⟨i⟩⟩ :=
    ((Space.toSpacesEtaleModules_full_faithful_essImage T.fppfSite S T.fppf_mem X).2.2 N).2 hsmall
  have : ((Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X).obj M).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso i.symm (hK q)
  exact ⟨M, Space.isQuasicoherentOnSite_of_toSpacesEtaleModules T.fppfSite S T.fppf_mem X M, ⟨i⟩⟩

end AlgebraicGeometry.BigEtaleSpaceSite

end
