module

public import StacksFrontier.CategoryTheory.FiberedCategory.ProductProjection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFibrewiseCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriekAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.UliftFreeCoverGenerators
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModules
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek along the projection `Δ × C ⟶ C`

Let `C` be a site. Stacks 09D0 presents a simplicial sheaf on `C` as a sheaf on `Δ × C` for the
topology inherited from `C` along the projection `π : Δ × C ⥤ C`, which is a fibred category
whose fibre over an object `U` is a copy of `Δ` carrying the chaotic topology. That projection is
therefore an instance of the standing data of Stacks 08P8, and the derived lower shriek
`Lπ_! : D(Ab(Δ × C)) ⥤ D(Ab(C))` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ProjectionLowerShriek.lean` is the
`Lπ_!` in which Stacks 09D2 is stated. This file assembles the situation and records the step of
the proof of Stacks 09D2 that descends a statement about `Lπ_!` to the fibres `Δ × U`.

## Main definitions

* `Stacks.SimplicialModules.simplicialSituation`: the fibred-category situation of Stacks 08P8
  for the projection `π : Δ × C ⥤ C` of a site `C` carrying a structure sheaf.

## Main results

* `Stacks.SimplicialModules.simplicialSituation_topology`: the topology of the situation on
  `Δ × C` is the topology inherited from `C` along the second projection, which is the topology
  in which Stacks 09D1 takes the sheaf condition on a simplicial module.
* `Stacks.SimplicialModules.isSheaf_simplicialModule`: consequently the underlying abelian
  presheaf of a simplicial `A_•`-module is an abelian sheaf for the situation, so `Lπ_!` applies
  to it.
* `Stacks.SimplicialModules.isIso_derivedLowerShriekHomology_map_of_fibrewise_unconditional`:
  **the reduction of Stacks 09D2 to the fibre categories**, with no hypothesis. `L_nπ_!` inverts
  a morphism of abelian sheaves on `Δ × C` that induces an isomorphism on the homology of the
  fibre over every object of `C`.
* `Stacks.SimplicialModules.isIso_derivedLowerShriekHomology_map_of_fibrewise`: the same
  reduction with the two acyclicity statements of Stacks 08PJ taken as arguments.

## Scope of the tag attribute

The source proves Stacks 09D2 in four steps: `Lπ_!` commutes with colimits, so it is enough to
treat bounded above complexes; such a complex is quasi-isomorphic to one with flat terms
(Modules on Sites, Lemma 18.28.8), so it is enough to treat a flat `A_•`-module `F`, for which
the derived tensor product is the ordinary one; by Stacks 08PJ and 08PI the cohomology sheaves of
both sides are then computed fibrewise, so it is enough to treat the restriction of `F` to the
fibre categories `Δ × U`; and there the statement is Stacks 08RX.

What is proved here is the third step, and only that: the descent to the fibres. It is **not**
the lemma. In particular the statement below mentions neither a simplicial sheaf of rings, nor
the derived tensor product `- ⊗^L_{A_•} B_•`, nor the hypothesis that `Lπ_!A_• ⟶ Lπ_!B_•` be
invertible; and the conclusion is drawn in a single degree `n`, in the form in which Stacks 08PJ
is available here, not in the unbounded derived category. The three other steps are open: the
library has no derived tensor product for simplicial modules, no flat resolution of Modules on
Sites, Lemma 18.28.8 for `Δ × C`, and of Stacks 08RX only the step treating the generators
`j_{U!}O_U` (`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_extensionByZero`) and the case of a
module in cohomological degree zero
(`Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_single`).

## Implementation notes

The hypotheses of Stacks 08PJ — the acyclicity statement of Stacks 07AC for `π_!`, the acyclicity
of the sheafified canonical presentation, and the resulting pointwise left derived functor — are
discharged rather than carried: `StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ProjectionLowerShriekAcyclic.lean` proves Stacks 0D6X along the
projection of a fibred category, hence `FibredCategorySituation.abelianLowerShriekAcyclic` and
the instance giving `Lπ_!`, and `StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/UliftFreeCoverGenerators.lean` proves
`FibredCategorySituation.abelianLowerShriekGeneratorsAcyclic`, from which the acyclicity of the
sheafified canonical presentation follows by
`uliftFreeCoverLowerShriekAcyclic_of_generatorsAcyclic`. So the reduction below is unconditional.

The site is taken with its morphisms in the universe of its objects. Stacks 08PJ is available
only in that generality — `Δ` contributes nothing to either universe, `SimplexCategory` being a
`Type` with `Type`-valued homs — and a structure sheaf is part of the standing data of
Stacks 08P8 even though lower shriek on abelian sheaves does not use it.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sites.FibredCategory

namespace Stacks.SimplicialModules

universe w u r

attribute [local instance] HasDerivedCategory.standard

/-- **The projection `π : Δ × C ⥤ C` as the standing data of Stacks 08P8.** The simplicial site
`Δ × C` of Stacks 09D0 is fibred over `C` by the second projection, so it is a fibred category
over the underlying site of the ringed site `B`; the structure sheaf plays no role in lower
shriek on abelian sheaves. -/
def simplicialSituation (B : AlgebraicGeometry.RingedSite.{u, u, w}) :
    FibredCategorySituation.{u, u, u, u, w} where
  base := B
  C := SimplexCategory × B.C
  p := CategoryTheory.Prod.snd SimplexCategory B.C

/-- The topology of the situation is the topology that `Δ × C` inherits from `C` along the second
projection, which is the one in which Stacks 09D1 takes the sheaf condition on a simplicial
module. -/
theorem simplicialSituation_topology (B : AlgebraicGeometry.RingedSite.{u, u, w}) :
    (simplicialSituation B).topology =
      (CategoryTheory.Prod.snd SimplexCategory B.C).inheritedTopology B.J :=
  rfl

/-- **A simplicial module is an abelian sheaf on the simplicial site.** The underlying abelian
presheaf of a simplicial `A_•`-module of Stacks 09D1 is a sheaf for the topology of the
situation, so derived lower shriek along `π` applies to it. -/
theorem isSheaf_simplicialModule (B : AlgebraicGeometry.RingedSite.{u, u, w})
    (A : SimplicialObject (Sheaf B.J RingCat.{r}))
    (M : SimplicialModule.{max w u, u, u, r} B.J A) :
    Presheaf.IsSheaf (simplicialSituation B).topology M.obj.presheaf :=
  M.property

variable (B : AlgebraicGeometry.RingedSite.{u, u, w})
  [((simplicialSituation B).abelianLowerShriekOnHomotopy ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (simplicialSituation B).topology AddCommGrpCat.{max w u}) (ComplexShape.up ℤ))]

/-- **The reduction of Stacks 09D2 to the fibre categories.** Let `C` be a site and let
`π : Δ × C ⥤ C` be the projection. A morphism `a` of abelian sheaves on `Δ × C` which induces an
isomorphism on the degree `n` homology of the fibre over every object of `C` is inverted by
`L_nπ_!`.

This is the step of the proof of Stacks 09D2 which, both sides of the asserted identity being
sheaves, computes their cohomology sheaves by the procedure of Stacks 08PI and so reduces the
lemma to the restriction of the coefficients to the fibre categories `Δ × U`, where the source
appeals to Stacks 08RX. It is not the lemma: the derived tensor product, the flat resolution and
Stacks 08RX itself do not appear. See the scope paragraph of the module docstring.

The two acyclicity statements of Stacks 08PJ are taken as arguments here;
`isIso_derivedLowerShriekHomology_map_of_fibrewise_unconditional` is the same reduction with
both discharged. -/
@[stacks 09D2 "the reduction to the fibre categories Δ × U"]
theorem isIso_derivedLowerShriekHomology_map_of_fibrewise
    (h : (simplicialSituation B).AbelianLowerShriekAcyclic)
    (hcov : (simplicialSituation B).UliftFreeCoverLowerShriekAcyclic) (n : ℕ)
    {F G : Sheaf (simplicialSituation B).topology AddCommGrpCat.{max w u}} (a : F ⟶ G)
    (ha : ∀ U : B.Cᵒᵖ, IsIso (((fiberHomologyPresheafFunctor (simplicialSituation B) n).map
      ((sheafToPresheaf (simplicialSituation B).topology
        AddCommGrpCat.{max w u}).map a)).app U)) :
    IsIso (((simplicialSituation B).derivedAbelianLowerShriekHomology n).map a) :=
  FibredCategorySituation.isIso_derivedAbelianLowerShriekHomology_map_of_fibrewise
    (simplicialSituation B) h hcov n a ha

/-- **The reduction of Stacks 09D2 to the fibre categories**, with no hypothesis. Let `C` be a
site and let `π : Δ × C ⥤ C` be the projection. A morphism `a` of abelian sheaves on `Δ × C`
which induces an isomorphism on the degree `n` homology of the fibre over every object of `C` is
inverted by `L_nπ_!`.

Both acyclicity statements of Stacks 08PJ are discharged rather than carried:
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ProjectionLowerShriekAcyclic.lean` proves Stacks 0D6X along the projection of a fibred category,
hence `FibredCategorySituation.abelianLowerShriekAcyclic` and the instance giving `Lπ_!`, and
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/UliftFreeCoverGenerators.lean` proves
`FibredCategorySituation.abelianLowerShriekGeneratorsAcyclic`, from which the acyclicity of the
sheafified canonical presentation follows by
`uliftFreeCoverLowerShriekAcyclic_of_generatorsAcyclic`.

It is still not the lemma, for the reasons in the scope paragraph of the module docstring. -/
@[stacks 09D2 "the reduction to the fibre categories Δ × U"]
theorem isIso_derivedLowerShriekHomology_map_of_fibrewise_unconditional (n : ℕ)
    {F G : Sheaf (simplicialSituation B).topology AddCommGrpCat.{max w u}} (a : F ⟶ G)
    (ha : ∀ U : B.Cᵒᵖ, IsIso (((fiberHomologyPresheafFunctor (simplicialSituation B) n).map
      ((sheafToPresheaf (simplicialSituation B).topology
        AddCommGrpCat.{max w u}).map a)).app U)) :
    IsIso (((simplicialSituation B).derivedAbelianLowerShriekHomology n).map a) :=
  FibredCategorySituation.isIso_derivedAbelianLowerShriekHomology_map_of_fibrewise
    (simplicialSituation B) (simplicialSituation B).abelianLowerShriekAcyclic
    ((simplicialSituation B).uliftFreeCoverLowerShriekAcyclic_of_generatorsAcyclic
      (FibredCategorySituation.abelianLowerShriekGeneratorsAcyclic (simplicialSituation B))) n a ha

end Stacks.SimplicialModules

end
