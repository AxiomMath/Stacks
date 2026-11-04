module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility in `D(𝒪_X)` is local on an open cover of the space

Let `(X, 𝒪_X)` be a ringed space and let `U : ι → Opens X` be a family of opens covering `X`.
A morphism of the unbounded derived category `D(𝒪_X)` whose derived pullback along the inclusion
`j_{U_i} : (U_i, 𝒪_X|_{U_i}) ⟶ (X, 𝒪_X)` of each member is invertible is itself invertible.

This is the step of the source's localization arguments which goes *back* from the cover to the
space.  Its companion, which goes from the space to the cover, is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_derivedPullback_map_projectionFormulaMap`.

The route is the one the library already uses one level down.  Invertibility in the derived
category is invertibility of every homology map (Mathlib's `DerivedCategory.isIso_iff`);
restriction `j_U^*` to an open subspace is exact, so the homology maps of the restricted
morphism are the restrictions of the homology maps
(`CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff`), and the derived pullback along
`j_U` *is* that restriction
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`); and a morphism of
sheaves of modules invertible after restriction to each member of an open cover is invertible,
because invertibility of such a morphism is detected on the stalks
(`ExtensionByZeroModules.isIso_of_stalk_isIso`) and the restriction to an open `U` sees exactly
the stalks inside `U`
(`Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_stalk_of_isIso_jStar_map`).

## Main results

* `ExtensionByZeroModules.isIso_of_isIso_jStar_map`: invertibility of a morphism of sheaves of
  modules is local on an open cover, in the restriction spelling `j_U^*`.
* `Stacks.Cohomology.DerivedOpenImmersion.isIso_of_isIso_derivedPullback_ofRestrict`:
  **invertibility in `D(𝒪_X)` is local on an open cover of the space**, in the derived pullback
  spelling.

## Implementation notes

*The cover is given pointwise.* The hypothesis is `∀ x, ∃ i, x ∈ U i` rather than
`iSup U = ⊤`; `Stacks.Cohomology.DerivedOpenImmersion.isIso_of_isIso_derivedPullback_iSup`
records the version with the lattice-theoretic form, the two being interchangeable by
`TopologicalSpace.Opens.mem_iSup`.

*The model of the derived categories is the standard one*, as it is in
`OpenImmersionRestriction.lean`, from which the identification of derived pullback along the
inclusion of an open subspace with restriction is read;
`CategoryTheory.HasDerivedCategory` carries the localized category as data, so a statement at
one model does not transport to another.

Nothing is tagged: the Stacks project does not state this locality as a result of its own, and
the statement is an input to the localization arguments of [Stacks, Tag 08EU] and
[Stacks, Tag 08I9] rather than a clause of either.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace ExtensionByZeroModules

variable {Z : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

/-- **Invertibility of a morphism of sheaves of modules is local on an open cover.**  If the
opens `U i` cover `Z` and the restriction `j_{U_i}^*φ` of `φ` to each of them is invertible,
then `φ` is invertible.

Invertibility is detected on the stalks, by `ExtensionByZeroModules.isIso_of_stalk_isIso`, and
every point of `Z` lies in some `U i`, whose restriction sees that stalk. -/
theorem isIso_of_isIso_jStar_map {ι : Type*} (U : ι → Opens Z)
    (hU : ∀ z : Z, ∃ i, z ∈ U i) {M N : SheafOfModules.{u} O} (φ : M ⟶ N)
    (h : ∀ i, IsIso ((jStar (U i) O).map φ)) : IsIso φ := by
  refine isIso_of_stalk_isIso O φ fun z => ?_
  obtain ⟨i, hi⟩ := hU z
  exact Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_stalk_of_isIso_jStar_map O (U i) φ
    (h i) z hi

end ExtensionByZeroModules

namespace Stacks.Cohomology.DerivedOpenImmersion

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] preservesFiniteLimits_jStar preservesFiniteColimits_jStar

variable (X : RingedSpace.{u, u})

/-- **Invertibility in the unbounded derived category of a ringed space is local on an open
cover of the space.**  If the opens `U i` cover `X` and the derived pullback of `a` along the
inclusion of each `U i` is invertible, then `a` is invertible.

No hypothesis is placed on the complexes: they are arbitrary objects of `D(𝒪_X)`. -/
theorem isIso_of_isIso_derivedPullback_ofRestrict {ι : Type*} (U : ι → Opens X.carrier)
    (hU : ∀ x : X.carrier, ∃ i, x ∈ U i)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (a : K ⟶ L)
    (h : ∀ i, IsIso ((derivedPullback (X.ofRestrict (U i).isOpenEmbedding) :
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
        DerivedCategory (SheafOfModules.{u} (resRing (U i) (structureSheafRing X)))).map a)) :
    IsIso a := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine ExtensionByZeroModules.isIso_of_isIso_jStar_map (structureSheafRing X) U hU _ fun i => ?_
  have h₁ : IsIso ((jStar (U i) (structureSheafRing X)).mapDerivedCategory.map a) :=
    (NatIso.isIso_map_iff (derivedPullbackOpenRestrictionIso X (U i)) a).1 (h i)
  exact ((jStar (U i) (structureSheafRing X)).isIso_mapDerivedCategory_map_iff a).1 h₁ n

/-- **Invertibility in `D(𝒪_X)` is local on an open cover**, with the cover given as a supremum.
This is `isIso_of_isIso_derivedPullback_ofRestrict` with the hypothesis in the form
`⨆ i, U i = ⊤`. -/
theorem isIso_of_isIso_derivedPullback_iSup {ι : Type*} (U : ι → Opens X.carrier)
    (hU : ⨆ i, U i = ⊤)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (a : K ⟶ L)
    (h : ∀ i, IsIso ((derivedPullback (X.ofRestrict (U i).isOpenEmbedding) :
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
        DerivedCategory (SheafOfModules.{u} (resRing (U i) (structureSheafRing X)))).map a)) :
    IsIso a :=
  isIso_of_isIso_derivedPullback_ofRestrict X U
    (fun x => by
      have hx : x ∈ (⨆ i, U i : Opens X.carrier) := by rw [hU]; trivial
      simpa using hx) a h

end Stacks.Cohomology.DerivedOpenImmersion

end
