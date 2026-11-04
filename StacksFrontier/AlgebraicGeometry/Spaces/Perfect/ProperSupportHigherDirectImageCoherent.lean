module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompOfAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperSupportCoherentPushforwardNoetherian

/-!
# Coherence of the higher direct images of a coherent module with proper support

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` locally Noetherian, and let `𝓕` be a coherent `𝒪_X`-module whose support is proper
over `Y`.  Then `R^p f_*𝓕` is a coherent `𝒪_Y`-module for every `p ≥ 0` (Stacks 08GC).

The source's proof writes `𝓕 = i_*𝓖` for a closed subspace `i : Z → X` proper over `Y`
(Stacks 0CZI), uses that `R^q i_*𝓖 = 0` for `q > 0` (Stacks 07UH), the Leray degeneration
`R^p f_*(i_*𝓖) = R^p (f ∘ i)_*𝓖` (Stacks 0734) and the coherence of `R^p (f ∘ i)_*𝓖`
(Stacks 08AR). This is
`isCoherent_rightDerived_modulePushforward_of_hasProperSupport_of_isQuasicoherent`, with its
two inputs supplied by `coherentHigherDirectImageOfProper_of_isLocallyNoetherian` (Stacks 08AR)
and `higherDirectImageCompOfAcyclic` (Stacks 0734).

## Main results

* `AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_properSupport`: the
  higher direct images of a coherent module with support proper over a locally Noetherian base
  are coherent.

## References

* [Stacks Project, Tag 08GC](https://stacks.math.columbia.edu/tag/08GC)
-/

@[expose] public section

open CategoryTheory

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite type,
with `Y` locally Noetherian, and let `𝓕` be a coherent `𝒪_X`-module with support proper over
`Y`. Then `R^p f_*𝓕` is a coherent `𝒪_Y`-module for every `p`. -/
@[stacks 08GC]
theorem isCoherent_rightDerived_modulePushforward_of_properSupport
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hsupp : HasProperSupport B S hS X.2 Y.2 f.hom hf ((SheafOfModules.toSheaf _).obj F))
    (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived p).obj F) :=
  isCoherent_rightDerived_modulePushforward_of_hasProperSupport_of_isQuasicoherent B S hS f hf hY F
    hF hsupp (coherentHigherDirectImageOfProper_of_isLocallyNoetherian B S hS Y hY)
    (higherDirectImageCompOfAcyclic f) p

end AlgebraicGeometry.Space
