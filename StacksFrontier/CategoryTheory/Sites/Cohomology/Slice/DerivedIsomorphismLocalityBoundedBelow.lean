module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.DerivedIsomorphismLocality
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.DerivedLocality

/-!
# Invertibility in the bounded below derived category of sheaves of modules is local on the site

`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` says that invertibility of a
morphism of the *unbounded* derived category `D(Mod(R))` of sheaves of modules on a site may be
checked after restriction to the slices over a family of objects covering the final object.  This
file carries that criterion to the **bounded below** derived category `D⁺(Mod(R))`, which is where
the base change map of **Stacks 0736** and so the comparison of **Stacks 073K**, part (1) live.

Nothing about the inclusion `D⁺ ⟶ D` is needed, and in particular the criterion is not deduced
from the unbounded one:  both are the same two-step composition, and in the bounded below case
both steps are already available.  A morphism of `D⁺` is invertible exactly when every one of its
homology maps is — `CategoryTheory.DerivedCategory.Plus.isIso_iff` — and restriction to a slice is
exact, so its bounded below right derived functor carries the degree-`n` homology map of a
morphism to the degree-`n` homology map of the restriction;  that is
`Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_map_homologyFunctor_map`, which is stated for an
arbitrary exact functor between abelian categories with enough injectives on the source.  The
hypothesis therefore says that each homology map of `f` is invertible after restriction to every
member of the family, and invertibility of a morphism of sheaves of modules is local on the site
by `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over`.

## Main results

* `Stacks.SheafOfModules.isIso_of_coversTop_rightDerivedFunctorPlus`: **invertibility in
  `D⁺(Mod(R))` is local on the site.**
* `Stacks.SheafOfModules.isIso_rightDerivedFunctorPlus_iff_of_coversTop`: the same as a
  criterion.

## Implementation notes

*Why the restriction is read as a right derived functor and not as `mapDerivedCategoryPlus`.*
The unbounded criterion is stated at `CategoryTheory.Functor.mapDerivedCategory`, the degreewise
action of an exact functor.  The consumer here is **Stacks 073K**, part (1), where the restriction
of the base change map to a slice is taken by the same functor the base change map's own inverse
images are taken by — `Stacks.Cohomology.ToposBaseChange.flatPullback`, which is
`rightDerivedFunctorPlus` of the inverse image.  Stating the criterion at
`rightDerivedFunctorPlus` is what makes the hypothesis the one that consumer has, and it costs an
`EnoughInjectives` instance on the source, which is where the right derived functor comes from.

*Where the file sits.*  It reuses
`Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_map_homologyFunctor_map`, which is generic —
an arbitrary exact additive functor between abelian categories — but is declared in
`StacksFrontier/AlgebraicGeometry/FlatModuleCohomologyBaseChange/DerivedLocality.lean`, beside the
scheme-theoretic locality statement it was first used for.  Importing it here brings that file's
closure in;  the alternative was a second copy of it, which is worse.  Moving it to a module of
its own, beside `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso`, is owed.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe d w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (SheafOfModules.{w} R)]
  [∀ V : C, HasDerivedCategory.{d} (SheafOfModules.{w} (R.over V))]
  [EnoughInjectives (SheafOfModules.{w} R)]

attribute [local instance] LocalCokernel.overFunctor_preservesFiniteLimits

attribute [local instance] LocalCokernel.overFunctor_preservesFiniteColimits

/-- **Invertibility in the bounded below derived category of sheaves of modules is local on the
site.**  Let `V : ι → C` be a family of objects covering the final object of the site.  A morphism
of `D⁺(Mod(R))` whose image under the bounded below right derived functor of restriction to the
slice site over each `V i` is an isomorphism is itself an isomorphism.

A morphism of `D⁺` is invertible exactly when every homology map of it is;  restriction to a slice
is exact, so its right derived functor carries the degree-`n` homology map of `f` to the degree-`n`
homology map of the restriction of `f`;  and invertibility of a morphism of sheaves of modules is
local on the site.

This is the locality step the reduction of **Stacks 073K**, part (1) to part (2) runs through, at
the seating `Stacks.Cohomology.ToposBaseChange.baseChangeMap` lives at.  It is not that reduction:
it says that invertibility of a *given* morphism may be checked on a covering, and says nothing
about the restricted morphism being the one part (2) is about — that is the pasting law of
**Stacks 0E47**, and is separate. -/
theorem isIso_of_coversTop_rightDerivedFunctorPlus {ι : Type*} {V : ι → C}
    (hV : J.CoversTop V) {K L : DerivedCategory.Plus (SheafOfModules.{w} R)} (f : K ⟶ L)
    (hf : ∀ i, IsIso ((SheafOfModules.overFunctor.{w} R (V i)).rightDerivedFunctorPlus.map f)) :
    IsIso f := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hV _ fun i => ?_
  exact Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_map_homologyFunctor_map
    (SheafOfModules.overFunctor.{w} R (V i)) f (hf i) n

/-- **Invertibility in `D⁺(Mod(R))`, as a local criterion.**  A morphism of `D⁺(Mod(R))` is an
isomorphism exactly when its image under the bounded below right derived functor of restriction to
the slice site over each member of a family of objects covering the final object is one.  The
forward direction is functoriality. -/
theorem isIso_rightDerivedFunctorPlus_iff_of_coversTop {ι : Type*} {V : ι → C}
    (hV : J.CoversTop V) {K L : DerivedCategory.Plus (SheafOfModules.{w} R)} (f : K ⟶ L) :
    IsIso f ↔
      ∀ i, IsIso ((SheafOfModules.overFunctor.{w} R (V i)).rightDerivedFunctorPlus.map f) :=
  ⟨fun hf i => by
      have := hf
      exact Functor.map_isIso _ _,
    isIso_of_coversTop_rightDerivedFunctorPlus hV f⟩

end Stacks.SheafOfModules

end
