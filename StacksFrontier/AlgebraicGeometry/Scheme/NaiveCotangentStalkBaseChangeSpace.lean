module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeComparison
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence

/-!
# The stalk of the canonical map of a tower of sheaves of rings on a space

`Stacks.SheafOfModules.spaceBaseChangeNaiveCotangentMap` is the canonical map
`NL_{B/A} ⊗_B C ⟶ NL_{C/A}` of Stacks 0E1Y for a tower `A ⟶ B ⟶ C` of sheaves of commutative
rings on a topological space, and it is the spelling in which the comparison map of a square of
schemes (`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison`) is built.  This file
records that it is the canonical map of the topology of opens, and restates in that spelling the
two degreewise descriptions of its stalk proved in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeComparison`.

## Main results

* `Stacks.NaiveCotangentStalkBaseChange.spaceBaseChangeNaiveCotangentMap_eq` and
  `spaceBaseChangeNaiveCotangentMap_f`: the canonical map of a tower of sheaves of rings on a
  space is the canonical map of the topology of opens, as a map of complexes and degreewise.
* `Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_spaceBaseChangeNaiveCotangentMap`
  and `stalkLegZeroLinear_spaceBaseChangeNaiveCotangentMap`: **the stalk of the canonical map of
  Stacks 0E1Y**, in the spelling the comparison map of a square of schemes is built from.

## Implementation notes

`spaceBaseChangeNaiveCotangentMap` is a reducible abbreviation of
`Stacks.SheafOfModules.baseChangeNaiveCotangentMap` on the topology of opens, so the two
spellings differ by a single delta step and `spaceBaseChangeNaiveCotangentMap_eq` is `rfl`.  What
makes that `rfl` worth recording is that it cannot be stated in the ambient instance
environment.

`CategoryTheory.Sheaf.hasWeakSheafifyCommRingCat`, `hasSheafifyAddCommGrpCat` and
`wEqualsLocallyBijectiveAddCommGrpCat` are declared for an arbitrary site, so wherever they are
in scope they take precedence over the instances Mathlib provides directly for a small site, and
three of the four instance arguments of `baseChangeNaiveCotangentMap` change accordingly.  They
reach sheafification through an essentially small model of the site, hence through a choice of
left adjoint, so reducing a term that mentions them unfolds `Classical.indefiniteDescription`,
and a *proposition* about such a term is already beyond the heartbeat budget — which is why the
equation below, and not its proof, is the obstruction.  The topology of opens of a space is
itself small, so Mathlib's direct instances apply to it, and the `attribute [local instance]`
block demotes the arbitrary-site ones for this file alone so that they do.  The two instance
sets are definitionally equal for free, all three classes being `Prop`-valued; that is why these
restatements need no bridging beyond rewriting along `spaceBaseChangeNaiveCotangentMap_f`.

The rewrite is what keeps the two restatements shallow.  Discharging either of them by applying
the corresponding result of the clean spelling directly makes the unifier descend through the
whole term, which exhausts the recursion depth in degree `0`; rewriting the map first leaves a
goal that matches syntactically.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the canonical map.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules
open scoped ChangeOfRings

universe u

noncomputable section

namespace Stacks.NaiveCotangentStalkBaseChange

open Stacks.SheafOfModules Stacks.NaiveCotangentAffineStalkLegs
open Stacks.RelativeDifferentialStalk (algebraStalk)

attribute [local instance 1]
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C) (z : T)

/-! ### The canonical map of a tower of sheaves of rings on a space -/

/-- **The canonical map of Stacks 0E1Y for a tower of sheaves of rings on a space is the
canonical map of the topology of opens.** -/
theorem spaceBaseChangeNaiveCotangentMap_eq :
    spaceBaseChangeNaiveCotangentMap A B C a b =
      baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b :=
  rfl

/-- **The canonical map of Stacks 0E1Y for a tower of sheaves of rings on a space is the
canonical map of the topology of opens**, in each degree. -/
theorem spaceBaseChangeNaiveCotangentMap_f (i : ℤ) :
    (spaceBaseChangeNaiveCotangentMap A B C a b).f i =
      (baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b).f i :=
  congrArg (fun h => HomologicalComplex.Hom.f h i)
    (spaceBaseChangeNaiveCotangentMap_eq A B C a b)

/-! ### The stalk of the canonical map -/

/-- **The stalk of the canonical map of Stacks 0E1Y in degree `-1`**, for the canonical map
written as `Stacks.SheafOfModules.spaceBaseChangeNaiveCotangentMap`. -/
theorem stalkLegNegOneLinear_spaceBaseChangeNaiveCotangentMap
    (ξ : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((spaceBaseChangeNaiveCotangentComplex A B C a b).X (-1)))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 A)) z
    letI := algebraStalk b.hom z
    letI := algebraStalk (𝟙 A ≫ (a ≫ b)).hom z
    letI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A A C (a ≫ b)
      (𝟙 A ≫ (a ≫ b)) (𝟙 A) z rfl
    letI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareTarget A B C a
      (𝟙 A ≫ (a ≫ b)) b z (Category.id_comp (a ≫ b)).symm
    stalkLegNegOneLinear A C (a ≫ b) z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceBaseChangeNaiveCotangentMap A B C a b).f (-1))).hom ξ) =
      (NaiveCotangent.nlExtensionBaseChangeMap
          (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
            (Category.id_comp (a ≫ b)).symm)).f₁
        (stalkBaseChangeAddEquivNegOne A B C a b z ξ) := by
  rw [spaceBaseChangeNaiveCotangentMap_f]
  exact stalkLegNegOneLinear_baseChangeNaiveCotangentMap A B C a b z ξ

/-- **The stalk of the canonical map of Stacks 0E1Y in degree `0`**, for the canonical map
written as `Stacks.SheafOfModules.spaceBaseChangeNaiveCotangentMap`. -/
theorem stalkLegZeroLinear_spaceBaseChangeNaiveCotangentMap
    (ξ : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((spaceBaseChangeNaiveCotangentComplex A B C a b).X 0))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 A)) z
    letI := algebraStalk b.hom z
    letI := algebraStalk (𝟙 A ≫ (a ≫ b)).hom z
    letI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A A C (a ≫ b)
      (𝟙 A ≫ (a ≫ b)) (𝟙 A) z rfl
    letI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareTarget A B C a
      (𝟙 A ≫ (a ≫ b)) b z (Category.id_comp (a ≫ b)).symm
    stalkLegZeroLinear A C (a ≫ b) z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceBaseChangeNaiveCotangentMap A B C a b).f 0)).hom ξ) =
      (NaiveCotangent.nlExtensionBaseChangeMap
          (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
            (Category.id_comp (a ≫ b)).symm)).f₀
        (stalkBaseChangeAddEquivZero A B C a b z ξ) := by
  rw [spaceBaseChangeNaiveCotangentMap_f]
  exact stalkLegZeroLinear_baseChangeNaiveCotangentMap A B C a b z ξ

end Stacks.NaiveCotangentStalkBaseChange

end

end
