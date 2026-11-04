module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ColimitsHigherDirect.CohomologyOfOpen
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Sections
public import StacksFrontier.AlgebraicGeometry.InverseSection.TensorPowerSection

/-!
# Cohomology over an open of a scheme detects isomorphy on the open subscheme

Let `X` be a scheme and `U ⊆ X` an open. [Stacks, Tag 01E1] identifies the cohomology
`H^p(U, -)` of modules on `X` over the open `U` with the cohomology over the whole of the open
subscheme `U` of their restrictions, naturally in the module. This file reads that comparison in
the vocabulary of `Hfunctor`, the cohomology functor of [Stacks, Tag 01E3], and draws the
consequence that is used to detect isomorphy: a morphism of modules which becomes an
isomorphism after restriction to `U` induces an isomorphism on `H^p(U, -)`.

Chaining that with `StacksTag09NE.isIso_restrict_iff_over` and
`StacksTag09NE.isIso_over_iff_app` turns a purely *sectionwise* hypothesis -- bijectivity of
`Γ(W, ℱ) ⟶ Γ(W, 𝒢)` for every open `W ⊆ U` -- into an isomorphism on cohomology over `U`.
That is the shape in which the trivialization clause of [Stacks, Tag 01CY] is available, so this
is the bridge by which a sectionwise trivialization becomes a cohomological isomorphism.

## Main definitions

* `Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso`: **[Stacks, Tag 01E1] in the
  `Hfunctor` vocabulary**, as a natural isomorphism
  `H^p(U, -) ≅ (- |_U) ⋙ H^p(U_{open subscheme}, -)`.

## Main results

* `Stacks.Cohomology.SchemeOpenRestriction.isIso_hfunctor_map_of_isIso_restrict`: a morphism
  whose restriction to the open subscheme `U` is an isomorphism induces an isomorphism on
  cohomology over `U`.
* `Stacks.Cohomology.SchemeOpenRestriction.isIso_hfunctor_map_of_isIso_app`: the same from
  sectionwise isomorphy over every open contained in `U`.
* `Stacks.Cohomology.SchemeOpenRestriction.isIso_hfunctor_map_of_bijective_app`: the same from
  sectionwise *bijectivity*, which is how such a hypothesis is usually produced.

## Implementation notes

Four spellings of the same data meet here and none of them is found from another by instance
search. `AlgebraicGeometry.cohomologyOverNatIsoRestriction` is stated for a
`CategoryTheory.SheafedSpace RingCat` through `RingedSpaceModuleAdjunction.OXSh`,
`RingedSpaceModuleAdjunction.OUSh` and `RingedSpaceModuleAdjunction.restMod`, while `Hfunctor`
and `AlgebraicGeometry.Scheme.Modules.restrictFunctor` are stated for a scheme through
`AlgebraicGeometry.Scheme.ringCatSheaf`.  Two bridges cross the gap:
`Stacks.Cohomology.HigherDirectImage.asRingSheafedSpace` presents a scheme's underlying ringed
space as a sheafed space of (not necessarily commutative) rings, and
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` is an
*equality* of the two restriction functors, so the comparison is obtained by rewriting and no
`eqToHom` survives into the statement. The remaining identifications --
`Hfunctor R U p` with the right derived functor of module-valued sections followed by the
forgetful functor, and `X.ringCatSheaf` with `OXSh (asRingSheafedSpace X.toRingedSpace)` -- hold
definitionally and are crossed in term position, exactly as in
`Stacks.LocalCohomology.hgroupRestrictIso`, which is this comparison objectwise and without
naturality.

**Isomorphy is carried as an explicit hypothesis and never as an instance.** In the categories
of sheaves of modules on a scheme instance search does not recover the sheaf of rings from a
morphism's type, so even `IsIso (Fn.map f)` from `IsIso f` is not found; the explicit-argument
restatements of `StacksFrontier/AlgebraicGeometry/InverseSection/TensorPowerSection.lean` are used
instead, and `CategoryTheory.NatIso.isIso_map_iff` transports along the comparison without any
search at all.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.Cohomology.SchemeOpenRestriction

/-- **[Stacks, Tag 01E1] in the `Hfunctor` vocabulary.** The cohomology over an open `U` of a
scheme `X` of modules on `X` is, naturally in the module, the cohomology over the whole of the
open subscheme `U` of their restrictions.

This is `AlgebraicGeometry.cohomologyOverNatIsoRestriction` read through the equality of the
scheme-level and ringed-space-level restriction functors; it is
`Stacks.LocalCohomology.hgroupRestrictIso` with the naturality retained. -/
noncomputable def hfunctorRestrictNatIso (X : Scheme.{u}) (U : X.Opens) (p : ℕ) :
    Hfunctor X.ringCatSheaf U p ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Hfunctor (U : Scheme).ringCatSheaf ⊤ p := by
  rw [Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction]
  exact AlgebraicGeometry.cohomologyOverNatIsoRestriction
    (asRingSheafedSpace X.toRingedSpace) U p

/-- **A morphism of modules whose restriction to an open subscheme `U` is an isomorphism induces
an isomorphism on the cohomology over the open `U`.** Both sides of the comparison
`hfunctorRestrictNatIso` carry the morphism to isomorphic maps, and the right-hand side is the
image of the restriction under a functor. -/
theorem isIso_hfunctor_map_of_isIso_restrict {X : Scheme.{u}} (U : X.Opens) (p : ℕ)
    {F G : X.Modules} (φ : F ⟶ G)
    (h : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) :
    IsIso ((Hfunctor X.ringCatSheaf U p).map φ) :=
  (NatIso.isIso_map_iff (hfunctorRestrictNatIso X U p) φ).mpr
    (Stacks.InverseSection.isIso_map (Hfunctor (U : Scheme).ringCatSheaf ⊤ p) h)

/-- **A morphism of modules which is an isomorphism on sections over every open contained in `U`
induces an isomorphism on the cohomology over `U`.** The hypothesis is turned into isomorphy of
the restriction to the open subscheme by [Stacks, Tag 09NE]. -/
theorem isIso_hfunctor_map_of_isIso_app {X : Scheme.{u}} (U : X.Opens) (p : ℕ)
    {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ W : X.Opens, W ≤ U → IsIso (φ.app W)) :
    IsIso ((Hfunctor X.ringCatSheaf U p).map φ) :=
  isIso_hfunctor_map_of_isIso_restrict U p φ
    ((StacksTag09NE.isIso_restrict_iff_over φ U).mpr
      ((StacksTag09NE.isIso_over_iff_app φ U).mpr h))

/-- **A morphism of modules which is bijective on sections over every open contained in `U`
induces an isomorphism on the cohomology over `U`.** A bijective map of abelian groups is an
isomorphism, so this is `isIso_hfunctor_map_of_isIso_app`. -/
theorem isIso_hfunctor_map_of_bijective_app {X : Scheme.{u}} (U : X.Opens) (p : ℕ)
    {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun t : F.val.obj (op W) => φ.val.app (op W) t) :
    IsIso ((Hfunctor X.ringCatSheaf U p).map φ) := by
  refine isIso_hfunctor_map_of_isIso_app U p φ fun W hW => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact h W hW

end Stacks.Cohomology.SchemeOpenRestriction

end
