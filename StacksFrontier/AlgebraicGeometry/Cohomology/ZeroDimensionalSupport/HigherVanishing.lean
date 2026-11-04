module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Flasque
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.FlasqueComplexDerivedSections
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the higher cohomology of a coherent module with zero-dimensional support

Let `X` be a locally Noetherian scheme and let `ℱ` be a coherent `𝒪_X`-module whose support has
dimension at most zero. Then `Hⁱ(X, ℱ) = 0` for every `i > 0`.

Together with
`AlgebraicGeometry.nonempty_generatingSections_of_support_dim_le_zero`, which is the global
generation of `ℱ`, this completes [Stacks, Tag 0B3J].

## Main results

* `AlgebraicGeometry.isZero_hgroup_of_support_dim_le_zero`: the vanishing over an arbitrary open
  subset of `X`.
* `AlgebraicGeometry.isZero_hgroup_top_of_support_dim_le_zero`: **the vanishing clause of
  [Stacks, Tag 0B3J]**, `Hⁱ(X, ℱ) = 0` for `i > 0`.

## Implementation notes

The source deduces the vanishing from `ℱ = i_*𝒢` for `𝒢` coherent on the scheme-theoretic
support `Z` of `ℱ`, the fact that a locally Noetherian scheme of dimension zero is a disjoint
union of spectra of Artinian local rings ([Stacks, Tag 0AAX]), Serre vanishing on those affines
([Stacks, Tag 01XB]), and the invariance of cohomology under an affine pushforward
([Stacks, Tag 089W]). The route here replaces that chain by flasqueness: the support of `ℱ` is a
discrete closed subset, so `ℱ` is flasque
(`AlgebraicGeometry.isFlasque_of_support_dim_le_zero`), and a flasque sheaf of modules has
vanishing higher derived sections over every open ([Stacks, Tag 09SY] through
[Stacks, Tag 015C], as `Stacks.Cech.Flasque.isZero_rightDerived_evaluation_of_isFlasque`). What
remains is the change of spelling from the module-valued derived sections to the
abelian-group-valued `Hgroup`, and that is
`Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup`
([Stacks, Tag 01F1]).

The vanishing is obtained over every open subset of `X`, not only over `X` itself: flasqueness
is a statement about all opens and costs nothing extra. The tagged form is the one the source
states.

## References

* [Stacks Project, Tag 0B3J](https://stacks.math.columbia.edu/tag/0B3J)
* [Stacks Project, Tag 09SY](https://stacks.math.columbia.edu/tag/09SY)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The higher cohomology of a coherent module with zero-dimensional support vanishes on every
open subset.** Such a module is flasque, and a flasque sheaf of modules is acyclic for sections
over any open. -/
theorem isZero_hgroup_of_support_dim_le_zero
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (SheafOfModules.supp F) ≤ 0)
    (U : X.Opens) (i : ℕ) (hi : 0 < i) :
    IsZero (Hgroup X.ringCatSheaf U i F) :=
  (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      X.ringCatSheaf U i F).1
    (Stacks.Cech.Flasque.isZero_rightDerived_evaluation_of_isFlasque (TopCat.of X)
      X.ringCatSheaf U F (isFlasque_of_support_dim_le_zero F hF) i hi)

/-- **[Stacks, Tag 0B3J], the vanishing clause.** For `X` a locally Noetherian scheme and `ℱ` a
coherent `𝒪_X`-module whose support has dimension at most zero, `Hⁱ(X, ℱ) = 0` for every
`i > 0`.

The global generation clause of the same tag is
`AlgebraicGeometry.nonempty_generatingSections_of_support_dim_le_zero`. -/
@[stacks 0B3J "vanishing"]
theorem isZero_hgroup_top_of_support_dim_le_zero
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (SheafOfModules.supp F) ≤ 0)
    (i : ℕ) (hi : 0 < i) :
    IsZero (Hgroup X.ringCatSheaf ⊤ i F) :=
  isZero_hgroup_of_support_dim_le_zero F hF ⊤ i hi

end AlgebraicGeometry

end
