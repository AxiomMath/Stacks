module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFlatRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# `ε^*` is exact: the second assertion of Stacks 08H8

Stacks 08H8 asserts three things about the morphism of ringed sites
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of Stacks 08H7: that it is flat, that `ε^*` is exact, and that
`ε^*𝓕 = 0` implies `𝓕 = 0`.  The first is formalized as
`AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap` (Stacks 0GNA).  The second
is proved here.

Two ingredients make this possible.

* The criterion `Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap` (Stacks
  04JC) needs a `CategoryTheory.MorphismOfTopoi` for `ε`.  That is
  `AlgebraicGeometry.SmallEtale.toZariskiToposHom`, and
  `AlgebraicGeometry.SmallEtale.exactFunctor_pullbackModules_toZariskiRingedSiteHom` already
  applies the criterion to it, carrying the flatness as a hypothesis.
* That hypothesis is the flatness at the topos spelling of the structure map, which is
  `AlgebraicGeometry.SmallEtale.isFlatMapULift_fSharpInverseImage_toZariskiRingedSiteHom`.

What the criterion yields is exactness of
`Stacks.Sheaves.RingedToposModules.pullbackModules`, the pullback of sheaves of modules along the
four-field morphism of ringed topoi.  `ε^*` itself is
`AlgebraicGeometry.SmallEtale.associatedModule`, which is the pullback along the *site-presented*
morphism.  The two are identified by
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral`, and exactness transports
along an isomorphism of functors.

Right exactness and additivity of `ε^*` are not proved here and never were in question: both
follow from `ε^*` being a left adjoint, and are the instances
`AlgebraicGeometry.SmallEtale.preservesFiniteColimits_associatedModuleOfSheaf` and
`AlgebraicGeometry.SmallEtale.additive_associatedModuleOfSheaf`.  With left exactness added, `ε^*`
has all three properties that `CategoryTheory.Functor.mapDerivedCategory` asks of a functor, so
`ε^*` acts on derived categories — which is what makes the second clause of Stacks 08HE
expressible.

## Main results

* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule`: **`ε^*` is left exact.**
* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModuleOfSheaf`: the same at the
  retyping `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, where the source carries the
  category instance of `SheafOfModules.{u} S.ringCatSheaf`.  This is the spelling in which the
  rest of the development takes exactness of `ε^*` as a hypothesis, and it is supplied as an
  instance so that those hypotheses are discharged.

## Implementation notes

`CategoryTheory.Limits.PreservesFiniteLimits` is `Prop`-valued, so supplying it as an instance
cannot make a statement elsewhere mean something different from what it meant when the hypothesis
was open: by proof irrelevance there is nothing for two instances to disagree about.

The `@[stacks 08H8]` attribute is *not* claimed here.  It is registered on
`isFlatMapULift_inverseImageStructureMap` with a clause string saying that only the flatness
assertion is carried there; the clause for exactness is attached below, and the zero-detection
assertion remains unproved for a general `𝒪_S`-module (it is proved for a quasi-coherent one, as
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule`).

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The exactness assertion of Stacks 08H8.**  The associated-module functor
`ε^* = (𝓕 ↦ 𝓕^a)` of Stacks 03DU (4) at `τ = étale` is left exact.

Stacks 08H8 deduces this from flatness of `ε`, which is Stacks 0GNA; the criterion is Stacks
04JC, available for the pullback of sheaves of modules along the four-field morphism of ringed
topoi attached to `ε`, and that pullback is `ε^*` by
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral`. -/
@[stacks 08H8 "the exactness assertion: `ε^* : Mod(𝒪_S) → Mod(𝒪_étale)` is left exact, hence
  exact, right exactness being automatic for a left adjoint.  The flatness assertion is carried
  by isFlatMapULift_inverseImageStructureMap; the zero-detection assertion
  `ε^*𝓕 = 0 ⟹ 𝓕 = 0` is not carried here, and is available for a quasi-coherent module as
  isZero_of_isZero_associatedModule"]
public theorem preservesFiniteLimits_associatedModule :
    PreservesFiniteLimits (associatedModule B S hS) := by
  have hpf : PreservesFiniteLimits (RingedToposHom.pullbackModules.{u, u, u, u + 1, u, u}
      (toZariskiRingedSiteHom B S hS).toRingedToposHom.toRingedToposModulesHom) :=
    exactFunctor_pullbackModules_toZariskiRingedSiteHom B S hS
      (isFlatMapULift_fSharpInverseImage_toZariskiRingedSiteHom B S hS)
  exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    (RingedSite.HomGeneral.pullbackModulesToposIsoGeneral (toZariskiRingedSiteHom B S hS)) hpf

/-- `ε^*` is left exact, recorded at the retyping
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`.

This is the spelling in which the development states the exactness assertion of Stacks 08H8 as a
hypothesis — in particular in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedEquivalence.lean` — so it
is supplied as an instance, which discharges those hypotheses. -/
public instance preservesFiniteLimits_associatedModuleOfSheaf :
    PreservesFiniteLimits (associatedModuleOfSheaf B S hS) :=
  have h : PreservesFiniteLimits (associatedModule B S hS) :=
    preservesFiniteLimits_associatedModule B S hS
  h

end AlgebraicGeometry.SmallEtale

end
