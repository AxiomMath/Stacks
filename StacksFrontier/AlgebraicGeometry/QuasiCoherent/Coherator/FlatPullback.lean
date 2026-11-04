module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QuasiCoherentPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison

/-!
# Pullback on quasi-coherent modules

Let `f : X ⟶ Y` be a morphism of schemes.  The inverse image of a quasi-coherent module is
quasi-coherent ([Stacks, Tag 01BG]), so pullback restricts to a functor
`f^* : QCoh(𝒪_Y) ⥤ QCoh(𝒪_X)`.  It is left adjoint to the pushforward
`AlgebraicGeometry.quasicoherentPushforward` of a quasi-compact quasi-separated morphism, by
restriction of the adjunction between pullback and pushforward of all modules along the two
fully faithful inclusions.  When `f` is flat the restricted pullback is exact.

This is the left adjoint through which [Stacks, Tag 08D8] identifies the two composites of
derived functors there: exactness of `f^*` on quasi-coherent modules is what makes it induce a
functor of derived categories with no derivation.

## Main definitions

* `AlgebraicGeometry.quasicoherentPullback`: pullback restricted to quasi-coherent modules.
* `AlgebraicGeometry.quasicoherentPullbackPushforwardAdjunction`: its adjunction with
  `AlgebraicGeometry.quasicoherentPushforward`.

## Main results

* `AlgebraicGeometry.quasicoherentPullback_preservesFiniteLimits` and
  `AlgebraicGeometry.quasicoherentPullback_preservesFiniteColimits`: exactness of `f^*` on
  quasi-coherent modules for a flat `f`.

## Implementation notes

Right exactness of pullback on *all* modules is unconditional, pullback being a left adjoint;
left exactness is `AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat`.  Both
transfer to the restriction because the inclusion of the quasi-coherent modules is exact (the
quasi-coherent modules are a weak Serre subcategory) and reflects isomorphisms.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 08D8](https://stacks.math.columbia.edu/tag/08D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Pullback of `𝒪_Y`-modules along a morphism of schemes, restricted to quasi-coherent
modules. -/
public noncomputable def quasicoherentPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.QuasicoherentModules Y ⥤ Scheme.QuasicoherentModules X :=
  ObjectProperty.lift (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙ Scheme.Modules.pullback f)
    (fun M => have := M.2
      Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback f M.obj)

/-- **Pullback is left adjoint to pushforward on quasi-coherent modules.**  The adjunction
between pullback and pushforward of all `𝒪`-modules restricts along the fully faithful
inclusions of the quasi-coherent modules, both restrictions being defined by the respective
preservation of quasi-coherence. -/
public noncomputable def quasicoherentPullbackPushforwardAdjunction {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    quasicoherentPullback f ⊣ quasicoherentPushforward f :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).restrictFullyFaithful
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).liftCompιIso _ _).symm
    ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).liftCompιIso _ _).symm

/-- Pullback restricted to quasi-coherent modules is additive, being a left adjoint between
additive categories. -/
public instance quasicoherentPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : (quasicoherentPullback f).Additive :=
  (quasicoherentPullbackPushforwardAdjunction f).left_adjoint_additive

/-- Pullback of all `𝒪_Y`-modules is right exact, being a left adjoint. -/
public theorem preservesFiniteColimits_modulesPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (Scheme.Modules.pullback f) := by
  have : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  infer_instance

/-- **Pullback along a flat morphism is left exact on quasi-coherent modules.**  The inclusion of
the quasi-coherent modules is exact and reflects isomorphisms, so left exactness is inherited
from pullback of all modules, which is left exact because `f` is flat. -/
public theorem quasicoherentPullback_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] : PreservesFiniteLimits (quasicoherentPullback f) :=
  @preservesFiniteLimits_of_reflects_of_preserves _ _ _ _ _ _
    (quasicoherentPullback f) (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
    (@preservesFiniteLimits_of_natIso _ _ _ _ _ _
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).liftCompιIso _ _).symm
      (@comp_preservesFiniteLimits _ _ _ _ _ _ _ _ inferInstance
        (preservesFiniteLimits_modulesPullback_of_flat f)))
    inferInstance

/-- **Pullback is right exact on quasi-coherent modules.**  The inclusion of the quasi-coherent
modules is exact and reflects isomorphisms, so right exactness is inherited from pullback of all
modules, which is right exact unconditionally. -/
public theorem quasicoherentPullback_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (quasicoherentPullback f) :=
  @preservesFiniteColimits_of_reflects_of_preserves _ _ _ _ _ _
    (quasicoherentPullback f) (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
    (@preservesFiniteColimits_of_natIso _ _ _ _ _ _
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).liftCompιIso _ _).symm
      (@comp_preservesFiniteColimits _ _ _ _ _ _ _ _ inferInstance
        (preservesFiniteColimits_modulesPullback f)))
    inferInstance

end AlgebraicGeometry

end
