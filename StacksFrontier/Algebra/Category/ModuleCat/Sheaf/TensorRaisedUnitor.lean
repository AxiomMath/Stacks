module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRaisedColimits

/-!
# The left unitor of the tensor product at a raised module universe

`SheafOfModules.HasGlobalPresentation` presents a sheaf of modules as a cokernel of a map between
coproducts of copies of `SheafOfModules.uliftForPresentation (SheafOfModules.unit R)`, the
structure sheaf with the universe of its sections raised to one containing the site.  Presenting a
tensor product that way needs, at exactly one point, that tensoring with that object changes
nothing — the monoidal unit.  This file provides it.

Mathlib's monoidal structure on modules requires the module universe to contain the universe of
the ring, and `Mathlib/Algebra/Category/ModuleCat/Monoidal/Basic.lean` states that the reason is
the monoidal unit.  Here the unit is the lifted structure sheaf rather than the structure sheaf,
the lift goes *up*, and the comparison is the composite of `ULift.moduleEquiv` on the scalar
factor with `TensorProduct.lid`: a lifted scalar acting on a section.  So no relation between the
module universe and the ring universe is needed, and none is assumed.

## Main definitions

* `Stacks.SheafOfModules.TensorRaised.liftedUnit`: the universe-lifted structure sheaf.

## Main results

* `Stacks.SheafOfModules.TensorRaised.presheafUnitorIso`: the objectwise unitor.
* `Stacks.SheafOfModules.TensorRaised.unitorIso`: **the left unitor** — tensoring with the lifted
  structure sheaf is the identity up to isomorphism.

## Implementation notes

The sheaf-level unitor is read off from the objectwise one through
`Stacks.SheafOfModules.UliftTensor.isoOfLocallyBijective`: the tensor product receives its own
sheafification unit, the target receives its identity, and both are locally bijective, so an
isomorphism of the two sources gives one of the two sheaves.  No sheafification of the target is
formed.

Naturality of the objectwise unitor is the semilinearity of the restriction maps of a presheaf
of modules, `PresheafOfModules.map_smul`, and nothing else.

## References

* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

universe u v w t

namespace Stacks.SheafOfModules.TensorRaised

open Stacks.SheafOfModules.UliftTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The universe-lifted structure sheaf, the object a global presentation is a presentation
by. -/
noncomputable abbrev liftedUnit (R : Sheaf J CommRingCat.{w}) :
    SheafOfModules.{max t w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R) :=
  SheafOfModules.uliftForPresentation.{u, v, w, w, t}
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R))

/-- Tensoring with the universe-lifted structure sheaf changes nothing, objectwise: a lifted
scalar acts on a section. -/
noncomputable def presheafUnitorIso (R : Sheaf J CommRingCat.{w})
    (N : PresheafOfModules.{max t w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R).obj) :
    PresheafOfModules.tensorObj (liftedUnit.{u, v, w, t} R).val N ≅ N :=
  PresheafOfModules.isoMk
    (fun X ↦ ((TensorProduct.congr ULift.moduleEquiv (LinearEquiv.refl _ _)).trans
      (TensorProduct.lid _ _)).toModuleIso)
    (by
      intro X Y f
      refine ModuleCat.tensor_ext fun x y ↦ ?_
      exact (N.map_smul f x.down y).symm)

/-- **The left unitor at the raised universe.**  The tensor product of the universe-lifted
structure sheaf with a sheaf of modules is that sheaf. -/
noncomputable def unitorIso [HasWeakSheafify J AddCommGrpCat.{max t w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max t w}] (R : Sheaf J CommRingCat.{w})
    (N : SheafOfModules.{max t w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} (R)).obj
      (liftedUnit.{u, v, w, t} R)).obj N ≅ N :=
  isoOfLocallyBijective
    (sheafifyUnit (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)
      (PresheafOfModules.tensorObj (liftedUnit.{u, v, w, t} R).val N.val))
    (𝟙 N.val)
    (isLocallyInjective_sheafifyUnit _) (isLocallySurjective_sheafifyUnit _)
    inferInstance inferInstance
    (presheafUnitorIso.{u, v, w, t} R N.val)

end Stacks.SheafOfModules.TensorRaised

end
