module

public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.DualSheafStalk.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat pullback of a coherent reflexive module

Let `f : X ⟶ Y` be a flat morphism of integral locally Noetherian schemes and let `G` be a
coherent reflexive `𝒪_Y`-module.  Then `f^*G` is reflexive.  Together with
`AlgebraicGeometry.isCoherent_pullback` this is
[Stacks, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF), whose statement is the
conjunction of the two: those two declarations are the covering set of the tag, and each carries
it.

## Main results

* `isReflexive_pullback_stalk`: the stalk of `f^*G` at `x` is a reflexive module over the local
  ring, as soon as the stalk of `G` at `f x` is reflexive over its own.  This is the algebraic
  core, namely reflexivity under flat base change, run at the stalks.
* `isReflexive_pullback`: **the reflexivity clause of Tag 0EBF.**

## Implementation notes

The proof is the one the Stacks Project omits, referring to the algebraic analogue
[Stacks, Tag 0EB9](https://stacks.math.columbia.edu/tag/0EB9): reflexivity is checked on stalks
by Tag 0AY3, the stalk of a pullback is the base change of the stalk along the map of local rings
by Tag 0098, and reflexivity of a finite module over a Noetherian domain is stable under flat
base change, which is `isReflexive_baseChange_of_flat`.

The three inputs are
`Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_iff_forall_isReflexive_stalk_of_isCoherent`,
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` and
`isReflexive_baseChange_of_flat`; coherence of the pullback, which Tag 0AY3 needs on the source,
is `AlgebraicGeometry.isCoherent_pullback`.

The base-change equivalence of Tag 0098 is stated for a morphism of ringed spaces and carries the
`Algebra` structure built from the stalk map of that morphism.  It is used here only through its
existence, so it is re-obtained as a `Nonempty` at the scheme-level spelling of that structure;
transporting `Module.IsReflexive` needs no more than an abstract linear equivalence.

The stalkwise criterion of Tag 0AY3 needs, on both source and target, that the dual of a
coherent module is again of finite presentation; that is the first assertion of
[Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ) at `𝒢 = 𝒪_X` fed through Tag
01XZ, and it is proved for an arbitrary scheme as
`Stacks.AlgebraicGeometry.ReflexiveModules.hasLocalKernelPresentationDual`, so neither clause of
Tag 0EBF carries it as a hypothesis.

## References

* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0EB9](https://stacks.math.columbia.edu/tag/0EB9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- **Reflexivity of the stalks of a flat pullback.**  If the stalk of `G` at `f x` is a
reflexive module over `𝒪_{Y, f x}`, then the stalk of `f^*G` at `x` is a reflexive module over
`𝒪_{X, x}`.

The stalk of the pullback is the base change along the map of local rings by Tag 0098, that map
is flat because `f` is, the local rings are Noetherian domains because the schemes are integral
and locally Noetherian, and the stalk of `G` is a finite module because `G` is of finite type; so
`isReflexive_baseChange_of_flat` applies. -/
public theorem isReflexive_pullback_stalk {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (G : Y.Modules)
    [G.IsFiniteType] (x : X)
    (hG : Module.IsReflexive (ringStalk Y.sheaf (f.base x)) (modStalk G (f.base x))) :
    Module.IsReflexive (ringStalk X.sheaf x)
      (modStalk ((Scheme.Modules.pullback f).obj G) x) := by
  let _ : Algebra (ringStalk Y.sheaf (f.base x)) (ringStalk X.sheaf x) :=
    (f.stalkMap x).hom.toAlgebra
  have key (S : Scheme.{u}) [IsIntegral S] [IsLocallyNoetherian S] (s : S) :
      IsDomain (ringStalk S.sheaf s) ∧ IsNoetherianRing (ringStalk S.sheaf s) :=
    ⟨inferInstanceAs (IsDomain (S.presheaf.stalk s)),
      inferInstanceAs (IsNoetherianRing (S.presheaf.stalk s))⟩
  obtain ⟨_, _⟩ := key Y (f.base x)
  obtain ⟨_, _⟩ := key X x
  have hfin : Module.Finite (ringStalk Y.sheaf (f.base x)) (modStalk G (f.base x)) :=
    SheafOfModules.finite_stalk Y.sheaf G (f.base x)
  have hflat : Module.Flat (ringStalk Y.sheaf (f.base x)) (ringStalk X.sheaf x) :=
    AlgebraicGeometry.Flat.stalkMap f x
  have hT : Module.IsReflexive (ringStalk X.sheaf x)
      (TensorProduct (ringStalk Y.sheaf (f.base x)) (ringStalk X.sheaf x)
        (modStalk G (f.base x))) := isReflexive_baseChange_of_flat
  obtain ⟨e⟩ : Nonempty (modStalk ((Scheme.Modules.pullback f).obj G) x ≃ₗ[ringStalk X.sheaf x]
      TensorProduct (ringStalk Y.sheaf (f.base x)) (ringStalk X.sheaf x)
        (modStalk G (f.base x))) :=
    ⟨(RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      f.toLRSHom.toShHom G x).choose⟩
  exact Module.equiv e.symm

/-- **The reflexivity clause of Stacks, Tag 0EBF**: the pullback of a coherent reflexive module
along a flat morphism of integral locally Noetherian schemes is reflexive.

Reflexivity is checked on stalks by Tag 0AY3, on the target to read off reflexivity of the
stalks of `G` and on the source to put reflexivity of the stalks of `f^*G` back together;
coherence of `f^*G`, which the source half needs, is `AlgebraicGeometry.isCoherent_pullback`,
and that declaration carries the coherence clause of the tag. -/
@[stacks 0EBF "reflexivity of the pullback"]
public theorem isReflexive_pullback {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] (G : Y.Modules) [G.IsCoherent] (hG : IsReflexive G) :
    IsReflexive ((Scheme.Modules.pullback f).obj G) := by
  have hcohX : ((Scheme.Modules.pullback f).obj G).IsCoherent := isCoherent_pullback f G
  have hftG : G.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have hstalkG := (isReflexive_iff_forall_isReflexive_stalk_of_isCoherent Y G
    inferInstance).mp hG
  exact (isReflexive_iff_forall_isReflexive_stalk_of_isCoherent X _ hcohX).mpr
    fun x => isReflexive_pullback_stalk f G x (hstalkG (f.base x))

end Stacks.AlgebraicGeometry.ReflexiveModules

end
