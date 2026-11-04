module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility in the derived category of a ringed site is local on the site

Let `R` be a sheaf of rings on a site `(C, J)` and let `f : K ⟶ L` be a morphism of the
unbounded derived category `D(Mod(R))`. This file proves that `f` is an isomorphism as soon as
its image under restriction to the slice site over each member of a family of objects covering
the final object is one.

The three inputs are all already in the library.

* Invertibility in the derived category is invertibility of every homology map, which is
  Mathlib's `DerivedCategory.isIso_iff`.
* Restriction of sheaves of modules to a slice is exact, so it commutes with the homology of
  the derived category: the homology of the restricted morphism is the restriction of the
  homology map. That is
  `CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff`, applied to the restriction
  functor, whose exactness is
  `Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits` together with
  `Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits`.
* Invertibility of a morphism of sheaves of modules is local on the site, which is
  `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over`.

So the hypothesis says that each homology map of `f` restricts to an isomorphism over every
member of the family, hence is an isomorphism, hence `f` is one.

## Main results

* `Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`: **invertibility in
  `D(Mod(R))` is local on the site.**
* `Stacks.SheafOfModules.isIso_mapDerivedCategory_iff_of_coversTop`: the same as a criterion,
  the converse direction being functoriality.

## Implementation notes

This is the derived-category counterpart of
`Stacks.SheafOfModules.quasiIso_of_coversTop` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality`, and it is not a
consequence of it: a morphism of `D(Mod(R))` need not be the class of a morphism of complexes,
so there is nothing to apply the chain-level statement to. The route is the same shape, with
`CategoryTheory.Functor.mapDerivedCategory` in place of
`CategoryTheory.Functor.mapHomologicalComplex` and the homology comparison taken from
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` rather than from
`CategoryTheory.ShortComplex.mapHomologyIso`.

The hypotheses on the slice sites are stated in the quantified form `∀ V : C, …` rather than at
the members of the family, because they are needed for the exactness of restriction to *every*
slice. The two exactness properties are installed as local instances below;
`SheafOfModules.overFunctor` is a `def`, so instance search does not find the additivity of a
pushforward through it, and `SheafOfModules.instAdditiveOverFunctor` is the instance that
covers that.

A `Stacks 08JJ` attribute is attached, in the **suffixed** form, and it claims a step of the
proof rather than any assertion of the tag. Stacks 08JJ reduces two of its four assertions —
that the canonical map `K ⟶ (K^∨)^∨` is an isomorphism, and that the canonical map
`M ⊗^L_O K^∨ ⟶ RSheafHom_O(K, M)` is an isomorphism — to the corresponding statements over a
covering of each object of the site, and the reduction it uses is exactly the statement below.
Neither of those two assertions is proved here; the precedent for tagging a proof step under a
suffix is `@[stacks 063H "the Nakayama and shrinking step of the proof only: …"]` at
`StacksFrontier/AlgebraicGeometry/QuasiRegular/StalkGenerators.lean:312`, and
`@[stacks 08JJ "step (5) of the proof only: …"]` at
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorDualSheafHom.lean:521`.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
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

section

attribute [local instance] LocalCokernel.overFunctor_preservesFiniteLimits

/-- Restriction of sheaves of modules to the slice site over `V` preserves finite colimits. -/
local instance derivedLocalityPreservesFiniteColimits (V : C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{w} R V) :=
  LocalCokernel.overFunctor_preservesFiniteColimits V

/-- **Invertibility in the derived category of sheaves of modules is local on the site.** Let
`V : ι → C` be a family of objects covering the final object of the site. A morphism of
`D(Mod(R))` whose image under restriction to the slice site over each `V i` is an isomorphism
is itself an isomorphism. -/
@[stacks 08JJ "the locality step of the proof only: invertibility of a morphism of `D(Mod(O))`
may be checked after restriction to the slices over a family of objects covering the final
object. Stacks 08JJ uses this reduction twice, for the bidual map `K ⟶ (K^∨)^∨` and for the
canonical map `M ⊗^L_O K^∨ ⟶ RSheafHom_O(K, M)`; neither of those maps is shown to be an
isomorphism here, and none of the tag's four assertions is proved here."]
theorem isIso_of_coversTop_mapDerivedCategory {ι : Type*} {V : ι → C} (hV : J.CoversTop V)
    {K L : DerivedCategory (SheafOfModules.{w} R)} (f : K ⟶ L)
    (hf : ∀ i, IsIso ((SheafOfModules.overFunctor.{w} R (V i)).mapDerivedCategory.map f)) :
    IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hV _ fun i => ?_
  exact ((SheafOfModules.overFunctor.{w} R (V i)).isIso_mapDerivedCategory_map_iff f).1
    (hf i) n

/-- **Invertibility in the derived category of sheaves of modules, as a local criterion.** A
morphism of `D(Mod(R))` is an isomorphism exactly when its restriction to the slice site over
each member of a family of objects covering the final object is one. -/
theorem isIso_mapDerivedCategory_iff_of_coversTop {ι : Type*} {V : ι → C}
    (hV : J.CoversTop V) {K L : DerivedCategory (SheafOfModules.{w} R)} (f : K ⟶ L) :
    IsIso f ↔
      ∀ i, IsIso ((SheafOfModules.overFunctor.{w} R (V i)).mapDerivedCategory.map f) :=
  ⟨fun hf i => by
      have := hf
      exact Functor.map_isIso _ _,
    isIso_of_coversTop_mapDerivedCategory hV f⟩

end

end Stacks.SheafOfModules

end
