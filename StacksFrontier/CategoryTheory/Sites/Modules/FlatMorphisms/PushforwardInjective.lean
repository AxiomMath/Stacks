module

public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Flat direct image preserves injective modules

Stacks 0730. For a *flat* morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` the
direct image `f_* : Mod(O_C) ⟶ Mod(O_D)` sends injective sheaves of modules to injective
sheaves of modules.

## Main results

* `AlgebraicGeometry.RingedToposHom.pushforwardModules_injective`: the direct image along a
  flat morphism of ringed topoi preserves injective objects.

## Implementation notes

The argument is the standard one. The direct image is right adjoint to the pullback
(Stacks 03D7, `AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModulesViaComparison`,
the form of 03D7 stated through the four-field `toRingedToposModulesHom`); for a flat
morphism the pullback is exact (Stacks 04JC,
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`), so in particular it
preserves monomorphisms, and a right adjoint whose left adjoint preserves monomorphisms
preserves injective objects. Exactness gives
`CategoryTheory.Limits.PreservesFiniteLimits` for the pullback, and monomorphisms are read off
from it as the pullbacks `CategoryTheory.Limits.cospan g g` it preserves, by
`CategoryTheory.preserves_mono_of_preservesLimit`.

The direct image used is `AlgebraicGeometry.RingedToposHom.pushforwardModules`, the
formalization of Stacks 03D6 part (1) for the two-field morphism of ringed topoi of Stacks 01D3
part (2) — the Stacks 03D1 direct image followed by restriction of scalars along the
direct-image form `f♯` of the structure map. The development's other formalization of that
clause, `Stacks.Sheaves.RingedToposModules.pushforwardModules` for the four-field morphism, is
isomorphic to it by `AlgebraicGeometry.RingedToposHom.pushforwardModulesIso`, so the statement
does not depend on which of the two is taken. Flatness is Stacks 04JB,
`AlgebraicGeometry.RingedToposHom.IsFlat`, namely flatness of the inverse-image form of the
structure map.

The `CategoryTheory.GrothendieckTopology.HasSheafCompose` witnesses that the target site and
the underlying-set and underlying-group forgetful functors need are the global instances of
`StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing`, which is why they do
not appear here as hypotheses. Pinning them that way is also what lets the statement elaborate
as a named declaration: synthesizing them through
`CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize` at the use site instead leaves
`CategoryTheory.Limits.PreservesLimitsOfSize` with an unassigned universe argument, whose
`UnivLE` side conditions are then postponed as universe constraints that cannot be discharged
when the declaration abstracts its universe parameters.

## References

* [Stacks Project, Tag 0730](https://stacks.math.columbia.edu/tag/0730)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Sheaves.RingedToposModules

universe v u v' u' w

namespace AlgebraicGeometry.RingedToposHom

/-- **Stacks 0730.** The direct image of a sheaf of modules along a *flat* morphism of ringed
topoi is injective whenever the sheaf is. -/
@[stacks 0730, sga "4 V 4.9" "clause 3"]
theorem pushforwardModules_injective {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    (f : RingedToposHom X Y) (hf : f.IsFlat)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [Injective I] :
    Injective (f.pushforwardModules.obj I) := by
  let F := f.toRingedToposModulesHom.pullbackModules
  have hAdj : F ⊣ f.pushforwardModules := f.pullbackAdjPushforwardModulesViaComparison
  have hExact : exactFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) F :=
    pullbackModules_exact_of_isFlatMap f hf
  have : PreservesFiniteLimits F := ((exactFunctor_iff F).mp hExact).1
  have : F.PreservesMonomorphisms := by
    constructor
    intro A B g _
    have : PreservesLimit (cospan g g) F := inferInstance
    exact preserves_mono_of_preservesLimit F g
  have : f.pushforwardModules.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms hAdj
  exact Functor.injective_obj _ _

end AlgebraicGeometry.RingedToposHom

end
