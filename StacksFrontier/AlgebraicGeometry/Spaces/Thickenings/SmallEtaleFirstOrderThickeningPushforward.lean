module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealOrderIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.Deformation.ToposThickening.FirstOrderThickeningOfKernel

/-!
# A first order thickening of algebraic spaces is a first order thickening of ringed topoi

The declarations of this file are independent of the module
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleFirstOrderThickening`,
which treats related material in its own terms.

Let `Z ⊆ X` be a first order thickening of algebraic spaces over a scheme `S` (Stacks 05ZK,
part (2)), with inclusion `i : Z ⟶ X`. The morphism of small étale ringed topoi of `i`
(Stacks 03G8) is a first order thickening of ringed topoi in the sense of Stacks 08MB: its
direct image of sheaves of sets is an equivalence (the topological invariance of the étale site,
Stacks 05ZM, with full faithfulness Stacks 04E5), its structure map `𝒪_X ⟶ i_*𝒪_Z` is
surjective (Stacks 03MB for a closed immersion), and its kernel, the defining ideal of `Z`, has
square zero.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_smallEtalePushforward_subspaceInclusion_of_isThickening`:
  the direct
  image of sheaves of sets along the inclusion of a thickening is an equivalence.
* `AlgebraicGeometry.Space.smallEtaleFirstOrderThickening`: the first order thickening of ringed
  topoi attached to a first order thickening of algebraic spaces.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The direct image of sheaves of sets along the inclusion of a thickening is an
equivalence**, at the universe of the structure rings: it is fully faithful for a closed
immersion (Stacks 04E5) and essentially surjective for a thickening (Stacks 05ZM). -/
theorem isEquivalence_smallEtalePushforward_subspaceInclusion_of_isThickening
    (hZ : IsThickening B S hS X Z.1) :
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.IsEquivalence :=
  have hff := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2
  have := hff.full
  have := hff.faithful
  have := essSurj_smallEtalePushforward_of_isThickening B S hS Z hZ
  { }

/-- **A first order thickening of algebraic spaces is a first order thickening of small étale
ringed topoi.** -/
noncomputable def smallEtaleFirstOrderThickening (hZ : IsFirstOrderThickening B S hS X Z.1) :
    Deformation.ToposThickening.FirstOrderThickening
      (X := smallEtaleRingedTopos B S hS ⟨Z.1.toFunctor, Z.2.1⟩)
      (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)) :=
  Deformation.ToposThickening.FirstOrderThickening.ofSquareZeroKernel
    (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z))
    (isEquivalence_smallEtalePushforward_subspaceInclusion_of_isThickening B S hS Z hZ.1)
    (by
      have h := isLocallySurjective_structureSharp B S hS (subspaceInclusion B S hS X Z) Z.2.2
      rw [← forgetCommRingSheaf_map_fSharp] at h
      exact ⟨fun {_} x => h.imageSieve_mem x⟩)
    (fun U a b ha hb => by
      have ha' : a ∈ definingIdealAt B S hS X Z U := by
        rw [definingIdealAt_eq_ker_fSharp]; exact ha
      have hb' : b ∈ definingIdealAt B S hS X Z U := by
        rw [definingIdealAt_eq_ker_fSharp]; exact hb
      obtain ⟨_, hpow⟩ := hZ
      have hsq := hpow U.unop
      rw [Submodule.pow_succ, Submodule.pow_one] at hsq
      exact (Submodule.eq_bot_iff _).1 hsq _ (Ideal.mul_mem_mul ha' hb'))

end AlgebraicGeometry.Space

end
