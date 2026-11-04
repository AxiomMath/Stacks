module

public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictOpenExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedClauseThree

/-!
# What clause (3) of Stacks 0FPG pins down about the cohomology sheaves

Clause (3) of Stacks 0FPG presents an object of `D(𝒪_X)` by a complex `E` which, on each member
`U` of an open covering, is quasi-isomorphic to a single invertible module `L` placed in a single
degree `n`. This file reads that data on the **cohomology sheaves of `E`**, which is where the
converse implication `(3) ⟹ (2)` starts: the degrees attached to two members of the covering have
to agree on the overlap, and the invariant that forces them to is the cohomology of `E` itself,
which does not depend on the member.

## Main results

* `Stacks.Cohomology.InvertibleDerived.isZero_restrictModules_homology_of_ne`: **off the local
  degree the cohomology vanishes.** For `k ≠ n` the restriction of `H^k(E)` to `U` is a zero
  object.
* `Stacks.Cohomology.InvertibleDerived.nonempty_restrictModules_homology_iso`: **in the local
  degree the cohomology is the module.** The restriction of `H^n(E)` to `U` is isomorphic to `L`.

Together these say that the local datum `(n, L)` of clause (3) is determined by `E`: `n` is the
only degree in which `H^k(E)` survives on `U`, and `L` is `H^n(E)|_U`. That is the step the
converse needs before it can split `X` into the opens `X_n` on which the degree is `n`, and it is
what makes the splitting well defined.

## Implementation notes

Both statements are the same two steps. A quasi-isomorphism induces an isomorphism on homology in
every degree (`quasiIsoAt_iff_isIso_homologyMap` at
`QuasiIso.quasiIsoAt`), and restriction to an open subspace is exact
(`AlgebraicGeometry.RingedSpace.preservesFiniteLimits_restrictModules` and its colimit twin), so
it commutes with the homology of complexes by
`StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso`. The homology of a single
complex is the module in its own degree (`HomologicalComplex.homologyFunctorSingleIso`) and zero
elsewhere, the complex being strictly bounded on both sides by that degree
(`CochainComplex.isZero_of_isGE` and `CochainComplex.isZero_of_isLE`).

No local-ring hypothesis appears here. The local rings enter the converse one step later, through
`not_subsingleton_sections_of_isLocalRing_stalk`, when the vanishing above has to be turned into
a contradiction with the invertibility of `L`.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open StrictlyPerfect Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.InvertibleDerived

variable {X : RingedSpace.{u, u}}

/-- The homology of a quasi-isomorphic complex, read through the restriction functor: the `k`-th
homology of the restriction of `E` to `U` is the restriction of the `k`-th homology of `E`, and a
quasi-isomorphism out of a single complex computes it. -/
public def restrictModulesHomologyIso (E : CochainComplex (Mod X.sheaf) ℤ)
    (U : Opens X.carrier) (k : ℤ) :
    (HomologicalComplex.homologyFunctor (OXMod.{u, u} (X.restrict U.isOpenEmbedding))
        (ComplexShape.up ℤ) k).obj
      (((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≅
      (restrictModules X U).obj
        ((HomologicalComplex.homologyFunctor (OXMod.{u, u} X) (ComplexShape.up ℤ) k).obj E) :=
  (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
    (restrictModules X U) (ComplexShape.up ℤ) k).app E

/-- **Off the local degree of clause (3) the cohomology of `E` vanishes.** If a single complex
carrying a module in degree `n` is quasi-isomorphic to the restriction of `E` to `U`, then for
every `k ≠ n` the restriction of `H^k(E)` to `U` is a zero object. -/
public theorem isZero_restrictModules_homology_of_ne (E : CochainComplex (Mod X.sheaf) ℤ)
    {U : Opens X.carrier} {n : ℤ} {L : OXMod.{u, u} (X.restrict U.isOpenEmbedding)}
    (f : (CochainComplex.singleFunctor _ n).obj L ⟶
      ((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)
    [QuasiIso f] {k : ℤ} (hk : k ≠ n) :
    IsZero ((restrictModules X U).obj
      ((HomologicalComplex.homologyFunctor (OXMod.{u, u} X) (ComplexShape.up ℤ) k).obj E)) := by
  have : IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) k).map f) :=
    (quasiIsoAt_iff_isIso_homologyMap f k).mp (QuasiIso.quasiIsoAt (f := f) k)
  have h0 : IsZero ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) k).obj
      ((CochainComplex.singleFunctor _ n).obj L)) := by
    rcases lt_or_gt_of_ne hk with h | h
    · exact CochainComplex.isZero_of_isGE ((CochainComplex.singleFunctor _ n).obj L) n k h
    · exact CochainComplex.isZero_of_isLE ((CochainComplex.singleFunctor _ n).obj L) n k h
  refine IsZero.of_iso ?_ (restrictModulesHomologyIso E U k).symm
  exact h0.of_iso (asIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) k).map f)).symm

/-- **In the local degree of clause (3) the cohomology of `E` is the module.** If a single complex
carrying `L` in degree `n` is quasi-isomorphic to the restriction of `E` to `U`, then the
restriction of `H^n(E)` to `U` is isomorphic to `L`. -/
public theorem nonempty_restrictModules_homology_iso (E : CochainComplex (Mod X.sheaf) ℤ)
    {U : Opens X.carrier} {n : ℤ} {L : OXMod.{u, u} (X.restrict U.isOpenEmbedding)}
    (f : (CochainComplex.singleFunctor _ n).obj L ⟶
      ((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)
    [QuasiIso f] :
    Nonempty ((restrictModules X U).obj
      ((HomologicalComplex.homologyFunctor (OXMod.{u, u} X) (ComplexShape.up ℤ) n).obj E) ≅ L) := by
  have : IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).map f) :=
    (quasiIsoAt_iff_isIso_homologyMap f n).mp (QuasiIso.quasiIsoAt (f := f) n)
  exact ⟨(restrictModulesHomologyIso E U n).symm ≪≫
    (asIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).map f)).symm ≪≫
    (HomologicalComplex.homologyFunctorSingleIso
      (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) (ComplexShape.up ℤ) n).app L⟩

end Stacks.Cohomology.InvertibleDerived

end
