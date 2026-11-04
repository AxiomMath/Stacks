module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallToBigEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRelocalization
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.SliceTransitionIso

/-!
# Restricting `π_X^*𝓕` to the spaces-étale site of `Y` (Stacks 0DG7, for modules)

Let `E` be a big étale site of algebraic spaces over a scheme `S`, `g : Y ⟶ X` a morphism of its
objects, `π_X : ((Spaces/X)_étale, 𝒪) ⟶ (X_{spaces,étale}, 𝒪_X)` the comparison morphism and
`i_g : Y_{spaces,étale} ⥤ (Spaces/X)_étale` the inclusion of Stacks 0DF2. For a quasi-coherent
`𝒪_X`-module `𝓕` on the spaces-étale site of `X`, the restriction of `π_X^*𝓕` along `i_g` is the
inverse image `g_{small}^*𝓕`: the module version of the section rule of Stacks 0DG7.

The proof follows the local argument of Stacks 0D7M. The projections `V ×_X Y ⟶ V` form a
transformation from base change followed by `i_g` to the inclusion of `X_{spaces,étale}`,
compatible with the structure maps, so restriction of modules along the two inclusions is related
by a transition `g_{small}^*(π_{X,*}𝓖) ⟶ i_g^*𝓖`. It is invertible at the structure sheaf, where it
is the comparison of structure sheaves, hence at every module which is locally globally presented
on `X_{spaces,étale}`, such as `π_X^*𝓕`. Finally the unit `𝓕 ⟶ π_{X,*}π_X^*𝓕` is an isomorphism for
every `𝓕`, the inclusion of the spaces-étale site being continuous, cocontinuous and fully
faithful.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.inclusionTransition`: the projections `V ×_X Y ⟶ V`.
* `AlgebraicGeometry.BigEtaleSpaceSite.inclusionFunctorSharp`: the structure map of `i_g`.
* `AlgebraicGeometry.BigEtaleSpaceSite.pullbackTopos_iso_restriction_pullbackTopos`:
  **`g_{small}^*𝓕 ≅ i_g^*(π_X^*𝓕)`** for a quasi-coherent `𝓕`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_spacesEtaleRestriction_unit`: the unit
  `𝓕 ⟶ π_{X,*}π_X^*𝓕` is an isomorphism.
* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_siteTransitionPullback_app_pullback`: the transition
  `g_{small}^*(π_{X,*}π_X^*𝓕) ⟶ i_g^*(π_X^*𝓕)` is an isomorphism for a quasi-coherent `𝓕`.
* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_inclusionFunctorTransitionPullback_app_pullback`: for
  `h : Z ⟶ Y`, the transition `h_{small}^*(i_f^*π_X^*𝓕) ⟶ i_{h ≫ f}^*π_X^*𝓕` along the projections
  `inclusionFunctorTransition` is an isomorphism for a quasi-coherent `𝓕`.

## References

* [Stacks Project, Tag 0DG7](https://stacks.math.columbia.edu/tag/0DG7)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (E : BigEtaleSpaceSite S)

/-- **The unit `𝓕 ⟶ π_{X,*}π_X^*𝓕` is an isomorphism** for every `𝒪_X`-module `𝓕` on the
spaces-étale site of `X`: the inclusion of the spaces-étale site into the big étale site is
continuous, cocontinuous and fully faithful, and the structure map of `π_X` is the identity. -/
theorem isIso_spacesEtaleRestriction_unit (X : E.Spaces) :
    IsIso (spacesEtaleRestrictionRingedSiteHom E
      X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit := by
  have : IsIso (restrictSharp E X) := inferInstanceAs (IsIso (𝟙 _))
  exact SheafOfModules.isIso_unit_of_isIso_coefficient.{u + 1, u + 1}
    (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (E.bigEtaleTopology X)
    (bigEtaleRingSheaf E X) (restrictSharp E X)
    (spacesEtaleRestrictionRingedSiteHom E
      X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos

variable {X Y : E.Spaces} (g : Y ⟶ X)

/-- The projections `V ×_X Y ⟶ V`, as a transformation from base change along `g` followed by the
inclusion `i_g` of Stacks 0DF2 to the inclusion of the spaces-étale site of `X`. -/
def inclusionTransition :
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem g).functor ⋙ inclusionFunctor E g ⟶
      Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X where
  app V := Over.homMk ((Space.spacesBaseChange E.fppfSite S E.fppf_mem g).projection.app V)
    pullback.condition
  naturality _ _ a := Over.OverMorphism.ext
    ((Space.spacesBaseChange E.fppfSite S E.fppf_mem g).projection.naturality a)

/-- The structure map of the inclusion `i_g`: an object étale over `Y` has the same ring of global
regular functions in the spaces-étale site of `Y` and in the big étale site of `X`. -/
def inclusionFunctorSharp :
    spacesEtaleRingSheaf E Y ⟶
      ((inclusionFunctor E g).sheafPushforwardContinuous RingCat.{u + 1}
        (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
        (E.bigEtaleTopology X)).obj (bigEtaleRingSheaf E X) :=
  𝟙 _

/-- The structure maps of `π_X`, `i_g` and `g_{small}` are compatible with the projections
`V ×_X Y ⟶ V`. -/
theorem ringCompatible_inclusionTransition :
    (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem g).RingCompatible
      (bigEtaleRingSheaf E X) (inclusionTransition E g) (inclusionFunctorSharp E g)
      (restrictSharp E X) :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl))

/-- Restricting the structure sheaf of the big étale site of `X` to the spaces-étale site of `X`
gives its structure sheaf, on the nose. -/
theorem pushforward_restrictSharp_unit :
    (SheafOfModules.pushforward.{u + 1} (restrictSharp E X)).obj
      (SheafOfModules.unit (bigEtaleRingSheaf E X)) =
        SheafOfModules.unit (spacesEtaleRingSheaf E X) :=
  rfl

/-- Restricting the structure sheaf of the big étale site of `X` along `i_g` gives the structure
sheaf of the spaces-étale site of `Y`, on the nose. -/
theorem pushforward_inclusionFunctorSharp_unit :
    (SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E g)).obj
      (SheafOfModules.unit (bigEtaleRingSheaf E X)) =
        SheafOfModules.unit (spacesEtaleRingSheaf E Y) :=
  rfl

/-- The transition `f^*(ρ_{G'}𝒪) ⟶ ρ_G𝒪` at the structure sheaf is an isomorphism as soon as the
restrictions of `𝒪` are the structure sheaves and its transpose is the structure map of `f`. -/
private theorem isIso_siteTransitionPullback_app_unit_of_eq
    {T : Type u} [SmallCategory T] {JT : GrothendieckTopology T} (R : Sheaf JT RingCat.{u})
    {X' Y' : RingedSite.{u, u, u}} (φ : RingedSite.Hom X' Y') {G : X'.C ⥤ T} {G' : Y'.C ⥤ T}
    [G.IsContinuous X'.J JT] [G'.IsContinuous Y'.J JT] (τ : φ.u ⋙ G ⟶ G')
    (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J) X'.O) ⟶
      (G.sheafPushforwardContinuous RingCat.{u} X'.J JT).obj R)
    (ψ' : (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y'.J) Y'.O) ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} Y'.J JT).obj R)
    (hτ : φ.RingCompatible R τ ψ ψ')
    (hA : (SheafOfModules.pushforward.{u} ψ').obj (SheafOfModules.unit R) =
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y'.J) Y'.O))
    (hB : (SheafOfModules.pushforward.{u} ψ).obj (SheafOfModules.unit R) =
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J) X'.O))
    (hβ : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y'.J) Y'.O)).map
        ((φ.siteTransition R τ ψ ψ' hτ).app (SheafOfModules.unit R)) ≍
      (sheafCompose Y'.J (forget RingCat.{u})).map φ.toRingedToposSiteHom.fSharpRing) :
    IsIso ((φ.siteTransitionPullback R τ ψ ψ' hτ).app (SheafOfModules.unit R)) := by
  rw [φ.siteTransitionPullback_app R τ ψ ψ' hτ]
  exact φ.ringedToposHom.isIso_homEquiv_symm_of_eq_unit hA hB _ hβ

/-- The transition `g_{small}^*(π_{X,*}𝒪) ⟶ i_g^*𝒪` is an isomorphism: its transpose is the
structure map of `g_{small}`. -/
theorem isIso_siteTransitionPullback_app_unit :
    IsIso (((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem g).siteTransitionPullback
      (bigEtaleRingSheaf E X) (inclusionTransition E g) (inclusionFunctorSharp E g)
      (restrictSharp E X) (ringCompatible_inclusionTransition E g)).app
        (SheafOfModules.unit _)) := by
  refine isIso_siteTransitionPullback_app_unit_of_eq _ _ _ _ _ _
    (pushforward_restrictSharp_unit E) (pushforward_inclusionFunctorSharp_unit E g) ?_
  exact heq_of_eq (Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl)))

/-- **The transition `g_{small}^*(π_{X,*}π_X^*𝓕) ⟶ i_g^*(π_X^*𝓕)` is an isomorphism** for a
quasi-coherent `𝒪_X`-module `𝓕`: `π_X^*𝓕` is globally presented over the objects of a covering of
every object of `X_{spaces,étale}` (Stacks 0D7M). -/
theorem isIso_siteTransitionPullback_app_pullback
    (F : SheafOfModules.{u + 1} (spacesEtaleRingSheaf E X)) [hF : F.IsQuasicoherentOnSite] :
    IsIso (((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem g).siteTransitionPullback
      (bigEtaleRingSheaf E X) (inclusionTransition E g) (inclusionFunctorSharp E g)
      (restrictSharp E X) (ringCompatible_inclusionTransition E g)).app
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F)) := by
  refine (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem
      g).isIso_siteTransitionPullback_app_of_locally
    (bigEtaleRingSheaf E X) (inclusionTransition E g) (inclusionFunctorSharp E g)
    (restrictSharp E X) (ringCompatible_inclusionTransition E g)
    (isIso_siteTransitionPullback_app_unit E g) _ fun U ↦ ?_
  obtain ⟨I, V, f, hcov, hpres⟩ := hF.locally_hasGlobalPresentation U
  refine ⟨Presieve.ofArrows V f, hcov, fun W a ha ↦ ?_⟩
  obtain ⟨i⟩ := ha
  exact hasGlobalPresentation_over_pullback E X F (V i) (hpres i)

/-- **Stacks 0DG7 for quasi-coherent modules: `g_{small}^*𝓕 ≅ i_g^*(π_X^*𝓕)`.** For a
quasi-coherent `𝒪_X`-module `𝓕` on the spaces-étale site of `X` and `g : Y ⟶ X`, the restriction
of `π_X^*𝓕` to the spaces-étale site of `Y` along the inclusion `i_g` of Stacks 0DF2 is the inverse
image of `𝓕` along `g_{small}`. It is the unit `𝓕 ≅ π_{X,*}π_X^*𝓕` followed by the transition
`g_{small}^*(π_{X,*}π_X^*𝓕) ≅ i_g^*(π_X^*𝓕)`. -/
def pullbackTopos_iso_restriction_pullbackTopos
    (F : SheafOfModules.{u + 1} (spacesEtaleRingSheaf E X)) [F.IsQuasicoherentOnSite] :
    (smallEtaleRingedSiteHom E g).pullbackTopos.obj F ≅
      (SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E g)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F) :=
  haveI := isIso_spacesEtaleRestriction_unit E X
  (Adjunction.leftAdjointUniq
    ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem g).ringedToposHom).ofNatIsoRight
      (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem g).pushforwardToposIso)
    (smallEtaleRingedSiteHom E g).pullbackPushforwardAdjunctionTopos).symm.app F ≪≫
  (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1, u + 1,
      u + 1, u + 1}
      ((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem
        g).ringedToposHom).toModulesHom).mapIso
    (asIso ((spacesEtaleRestrictionRingedSiteHom E
      X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app F)) ≪≫
  @asIso _ _ _ _ (((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem g).siteTransitionPullback
      (bigEtaleRingSheaf E X) (inclusionTransition E g) (inclusionFunctorSharp E g)
      (restrictSharp E X) (ringCompatible_inclusionTransition E g)).app
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F))
    (isIso_siteTransitionPullback_app_pullback E g F)

end AlgebraicGeometry.BigEtaleSpaceSite

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (E : BigEtaleSpaceSite S) {X Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X)

/-- The projections `V ×_Y Z ⟶ V`, for `h : Z ⟶ Y` and `f : Y ⟶ X`, as a transformation from base
change along `h` followed by the inclusion `i_{h ≫ f}` to the inclusion `i_f` of Stacks 0DF2. -/
def inclusionFunctorTransition :
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor ⋙ inclusionFunctor E (h ≫ f) ⟶
      inclusionFunctor E f where
  app V := Over.homMk ((Space.spacesBaseChange E.fppfSite S E.fppf_mem h).projection.app V)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) pullback.condition))
  naturality _ _ a := Over.OverMorphism.ext
    ((Space.spacesBaseChange E.fppfSite S E.fppf_mem h).projection.naturality a)

/-- The structure maps of `i_f`, `i_{h ≫ f}` and `h_{small}` are compatible with the projections
`V ×_Y Z ⟶ V`. -/
theorem ringCompatible_inclusionFunctorTransition :
    (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).RingCompatible
      (bigEtaleRingSheaf E X) (inclusionFunctorTransition E h f) (inclusionFunctorSharp E (h ≫ f))
      (inclusionFunctorSharp E f) :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl))

/-- The transition `h_{small}^*(i_f^*𝒪) ⟶ i_{h ≫ f}^*𝒪` is an isomorphism: its transpose is the
structure map of `h_{small}`. -/
theorem isIso_inclusionFunctorTransitionPullback_app_unit :
    IsIso (((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).siteTransitionPullback
      (bigEtaleRingSheaf E X) (inclusionFunctorTransition E h f) (inclusionFunctorSharp E (h ≫ f))
      (inclusionFunctorSharp E f) (ringCompatible_inclusionFunctorTransition E h f)).app
        (SheafOfModules.unit _)) := by
  refine isIso_siteTransitionPullback_app_unit_of_eq _ _ _ _ _ _
    (pushforward_inclusionFunctorSharp_unit E f) (pushforward_inclusionFunctorSharp_unit E (h ≫ f))
    ?_
  exact heq_of_eq (Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl)))

/-- **The transition `h_{small}^*(i_f^*π_X^*𝓕) ⟶ i_{h ≫ f}^*π_X^*𝓕` is an isomorphism** for a
quasi-coherent `𝒪_X`-module `𝓕`: over the base changes to `Y` of the objects of a covering of
`X_{spaces,étale}` on which `𝓕` is globally presented, `π_X^*𝓕` restricted along `i_f` is globally
presented (Stacks 0D7M). -/
theorem isIso_inclusionFunctorTransitionPullback_app_pullback
    (F : SheafOfModules.{u + 1} (spacesEtaleRingSheaf E X)) [hF : F.IsQuasicoherentOnSite] :
    IsIso (((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).siteTransitionPullback
      (bigEtaleRingSheaf E X) (inclusionFunctorTransition E h f) (inclusionFunctorSharp E (h ≫ f))
      (inclusionFunctorSharp E f) (ringCompatible_inclusionFunctorTransition E h f)).app
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F)) := by
  have := (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem f).isMorphismOfSites.isContinuous
  have :=
    (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem
      f).isMorphismOfSites.preservesFiniteLimits
  have hTop := Stacks.Sites.coversTop_obj_of_preservesFiniteLimits
    (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem f).u
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
  have hcov := GrothendieckTopology.coversTop_obj_subtype
    (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem f).u _ _ hTop
    (fun V ↦ (F.over V).HasGlobalPresentation) (fun U ↦ by
      obtain ⟨I, V, φ, hφ, hpres⟩ := hF.locally_hasGlobalPresentation U
      exact ⟨Presieve.ofArrows V φ, hφ, fun W a ⟨i⟩ ↦ hpres i⟩)
  refine (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem
      h).isIso_siteTransitionPullback_app_of_locally
    (bigEtaleRingSheaf E X) (inclusionFunctorTransition E h f) (inclusionFunctorSharp E (h ≫ f))
    (inclusionFunctorSharp E f) (ringCompatible_inclusionFunctorTransition E h f)
    (isIso_inclusionFunctorTransitionPullback_app_unit E h f) _ fun U ↦
      ⟨(Sieve.ofObjects _ U).arrows, by rw [Sieve.generate_sieve]; exact hcov U, ?_⟩
  rintro W a ⟨⟨V, hV⟩, ⟨b⟩⟩
  exact SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} _
    ((inclusionFunctor E f).map b ≫ (inclusionTransition E f).app V)
    (hasGlobalPresentation_over_pullback E X F V hV)

end AlgebraicGeometry.BigEtaleSpaceSite
