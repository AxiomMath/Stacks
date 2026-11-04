module

public import StacksFrontier.AlgebraicGeometry.Etale.ModuleUpperShriekQuasiFinite

import StacksCore.Tactic.StacksAttribute

/-!
# The adjunction `f_! ⊣ Rf^!` on derived categories of sheaves of `Λ`-modules

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site and let `Λ` be a ring.
The direct image with compact support with coefficients in `Λ`, the functor
`AlgebraicGeometry.SmallEtale.fShriekMod`, is the `Λ`-linear lift of the `f_!` of Stacks 0F6R,
and its right adjoint `f^! : Mod(Y_étale, Λ) ⥤ Mod(X_étale, Λ)`, the
`AlgebraicGeometry.SmallEtale.fUpperShriekMod` of
`StacksFrontier.AlgebraicGeometry.Etale.ModuleUpperShriekQuasiFinite`, is Stacks 0F59 part (3).
This file derives that upper shriek and produces the adjunction `f_! ⊣ Rf^!` on unbounded
derived categories of sheaves of `Λ`-modules, which is Stacks 0F5N for a general coefficient
ring.

## Main definitions

* `AlgebraicGeometry.SmallEtale.moduleRUpperShriekFunctor` — the total right derived functor
  `Rf^!` of the upper shriek on sheaves of `Λ`-modules, with
  `AlgebraicGeometry.SmallEtale.moduleRUpperShriekFunctorUnit` its comparison map.

## Main results

* `AlgebraicGeometry.SmallEtale.moduleFShriekRUpperShriekAdjunction` — **Stacks 0F5N for a
  general coefficient ring**: `f_! ⊣ Rf^!` on `D(X_étale, Λ)` and `D(Y_étale, Λ)`, for `f_!` and
  `f^!` themselves rather than for a lift taken as data.

## Implementation notes

`AlgebraicGeometry.SmallEtale.moduleFShriekDerivedAdjunction` and
`AlgebraicGeometry.SmallEtale.moduleFShriekDerivedFunctor` take the `Λ`-linear direct image with
compact support as data together with a right adjoint; here they are read at the actual `f_!`,
the functor `AlgebraicGeometry.SmallEtale.fShriekMod`, whose right adjoint is the one supplied by
Stacks 0F59 part (3) in
`StacksFrontier.AlgebraicGeometry.Etale.ModuleUpperShriekQuasiFinite`. Nothing is assumed beyond
`f` being locally quasi-finite, `Λ` being a ring, and the two derived categories existing.

The coefficient universe is the cutoff `max (u + 1) v r` at which `f_!` is defined, as it is for
`AlgebraicGeometry.SmallEtale.fShriekMod`, and the universe arguments are supplied explicitly for
the same reason: left implicit they produce a stuck universe constraint.

## References

* [Stacks Project, Tag 0F59](https://stacks.math.columbia.edu/tag/0F59)
* [Stacks Project, Tag 0F5N](https://stacks.math.columbia.edu/tag/0F5N)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SmallEtale

universe u v w r

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, v, r} B Y Λ)]

/-- The upper shriek on sheaves of `Λ`-modules, read on the unbounded homotopy category and
composed with the localization, has a pointwise total right derived functor: sheaves of
`Λ`-modules on a small étale site are Grothendieck abelian, so every complex admits a
K-injective resolution. -/
public instance moduleUpperShriekQh_hasPointwiseRightDerivedFunctor :
    (moduleUpperShriekQh.{u, v, w, r} B Λ f (fShriekMod.{u, v, r} B Λ f)
        (fShriekModForgetIso.{u, v, r} B Λ f)).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, v, r} B Y Λ) (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K

/-- `Rf^!`, a total right derived functor of the upper shriek `f^!` of Stacks 0F59 part (3), on
unbounded derived categories of étale sheaves of `Λ`-modules. -/
public def moduleRUpperShriekFunctor :
    DerivedCategory (ModuleSheaf.{u, v, r} B Y Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, v, r} B X Λ) :=
  (moduleUpperShriekQh.{u, v, w, r} B Λ f (fShriekMod.{u, v, r} B Λ f)
      (fShriekModForgetIso.{u, v, r} B Λ f)).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, v, r} B Y Λ) (ComplexShape.up ℤ))

/-- The comparison map exhibiting `moduleRUpperShriekFunctor` as a right derived functor of the
upper shriek on sheaves of `Λ`-modules. -/
public def moduleRUpperShriekFunctorUnit :
    moduleUpperShriekQh.{u, v, w, r} B Λ f (fShriekMod.{u, v, r} B Λ f)
        (fShriekModForgetIso.{u, v, r} B Λ f) ⟶
      DerivedCategory.Qh ⋙ moduleRUpperShriekFunctor.{u, v, w, r} B Λ f :=
  (moduleUpperShriekQh.{u, v, w, r} B Λ f (fShriekMod.{u, v, r} B Λ f)
      (fShriekModForgetIso.{u, v, r} B Λ f)).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, v, r} B Y Λ) (ComplexShape.up ℤ))

/-- `moduleRUpperShriekFunctor` is a total right derived functor of the upper shriek on sheaves
of `Λ`-modules, with comparison map `moduleRUpperShriekFunctorUnit`. -/
public instance moduleRUpperShriekFunctor_isRightDerivedFunctor :
    (moduleRUpperShriekFunctor.{u, v, w, r} B Λ f).IsRightDerivedFunctor
      (moduleRUpperShriekFunctorUnit.{u, v, w, r} B Λ f)
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, v, r} B Y Λ) (ComplexShape.up ℤ)) := by
  unfold moduleRUpperShriekFunctor moduleRUpperShriekFunctorUnit
  infer_instance

/-- **Stacks 0F5N.** Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes and let `Λ` be
a ring. The direct image with compact support `f_!` of Stacks 0F6R and the upper shriek `f^!` of
Stacks 0F59 induce adjoint functors `f_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` and
`Rf^! : D(Y_étale, Λ) ⟶ D(X_étale, Λ)` on unbounded derived categories of étale sheaves of
`Λ`-modules.

The functor `f_!` with coefficients in `Λ` is `AlgebraicGeometry.SmallEtale.fShriekMod`; it is
exact and therefore needs no deriving, and `Rf^!` is the total right derived functor of the `f^!`
of Stacks 0F59 part (3). -/
@[stacks 0F5N "general coefficient ring Λ, for f_! and f^! themselves",
  sga "4 XVIII 3.1.5" "special case"]
public def moduleFShriekRUpperShriekAdjunction :
    moduleFShriekDerivedFunctor.{u, v, w, r} B Λ f (fShriekMod.{u, v, r} B Λ f)
        (fShriekModForgetIso.{u, v, r} B Λ f) ⊣
      moduleRUpperShriekFunctor.{u, v, w, r} B Λ f :=
  moduleFShriekDerivedAdjunction.{u, v, w, r} B Λ f (fShriekMod.{u, v, r} B Λ f)
    (fShriekModForgetIso.{u, v, r} B Λ f) _
    (moduleRUpperShriekFunctorUnit.{u, v, w, r} B Λ f)

end AlgebraicGeometry.SmallEtale

end
