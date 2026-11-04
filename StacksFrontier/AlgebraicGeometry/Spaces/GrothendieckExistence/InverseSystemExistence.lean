module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ExistenceNeighbourhoodStages
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.Existence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedCoheratorGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
/-!
# From an existence neighbourhood to the algebraization data of Situation 0CX4

Situation [Stacks, Tag 0CX4] has two forms, `AlgebraicGeometry.Space.FlatSheafExistenceSituation`
and `AlgebraicGeometry.Space.InverseSystemExistenceSituation`; every situation in the second form
comes from one in the first.

Given an object `K` of `D(𝒪_X)` with compatible maps `πₙ : K ⟶ Fₙ` and an open subspace `W ⊆ X`
with the three conclusions of [Stacks, Tag 0CX9], the module `H = H⁰(K)`, the inclusion
`j : W ⟶ X`, and the identifications `βₙ : H|_{Xₙ} ≅ Fₙ` induced by the `πₙ` satisfy: `W` contains
the closed fibre, `H|_W` is of finite presentation, and the `βₙ` are compatible with the `φₙ`.

All names below are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `FlatSheafExistenceSituation.toInverseSystemExistenceSituation`: the second form of a situation
  given in the first.

## Main results

* `InverseSystemExistenceSituation.exists_eq_toInverseSystemExistenceSituation`: every situation
  in the second form comes from one in the first.
* `FlatSheafExistenceSituation.exists_algebraizationData_of_isExistenceNeighbourhood`: the
  algebraization data of an existence neighbourhood, in the second form.

## References

* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
* [Stacks Project, Tag 0CX4](https://stacks.math.columbia.edu/tag/0CX4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- **Situation 0CX4 in the form of `AlgebraicGeometry.Space.InverseSystemExistenceSituation`**:
the same rings, space, modules and isomorphisms. Separatedness over the affine base `Spec A` is
separatedness of the space over the terminal presheaf. -/
abbrev toInverseSystemExistenceSituation : InverseSystemExistenceSituation.{u} where
  system := D.system
  transition_surjective := D.transition_surjective
  transition_locallyNilpotent := D.transition_locallyNilpotent
  B := D.B
  containsLimitBase := D.containsLimitBase
  containsBaseAt := D.containsBaseAt
  X := D.X
  separated := (isSeparatedOver_iff_isSeparated_of_isTerminal _ _ _
    (isTerminal_yoneda_obj_base _ _ _) D.X.hom.hom).2 D.separated
  finitePresentation := D.finitePresentation
  closedSpaceProjection := D.isClosedImmersion_closedImmersion
  sheaf n := ⟨D.F n, D.isQuasicoherentOnSite_F n⟩
  finitePresentation_sheaf := D.finitelyPresented
  flat_sheaf := D.flat
  closed_support n := (D.properSupport n).1
  locallyOfFiniteType n := isLocallyOfFiniteType_spaceBaseProjection_of_isFinitePresentation _ _ _
    _ _ D.finitePresentation n
  properSupport n := (D.properSupport n).2
  φ := D.φ

/-- **The algebraization data of an existence neighbourhood.** In Situation 0CX4, let `K` be an
object of `D(𝒪_X)` with maps `πₙ : K ⟶ Fₙ` compatible with the transition maps of the system, and
let `W ⊆ X` be an open subspace with the three conclusions of Stacks 0CX9. Then `H = H⁰(K)`, the
inclusion `j : W ⟶ X`, and the comparisons `βₙ : H|_{Xₙ} ≅ Fₙ` induced by the `πₙ` satisfy: `W`
contains the points of `X₀`, `H|_W` is of finite presentation, and the `βₙ` are isomorphisms
compatible with the `φₙ`. Stated for the situation in the form
`AlgebraicGeometry.Space.InverseSystemExistenceSituation`. -/
theorem exists_algebraizationData_of_isExistenceNeighbourhood
    {K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    {π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n)}
    (hπ : ∀ n : ℕ, π (n + 1) ≫ D.derivedSystem.map (homOfLE (Nat.le_succ n)).op = π n)
    {W : Subfunctor D.X.left.1} {hW : IsOpenSubspace D.B D.S D.containsLimitBase W}
    (hN : D.IsExistenceNeighbourhood K π W hW) :
    ∃ (H : Modules.{u, u} D.toInverseSystemExistenceSituation.B
        (limitBase D.toInverseSystemExistenceSituation.system)
        D.toInverseSystemExistenceSituation.containsLimitBase
        D.toInverseSystemExistenceSituation.X.left.1 D.toInverseSystemExistenceSituation.X.left.2)
      (W' : AlgebraicSpaces D.toInverseSystemExistenceSituation.B
        (limitBase D.toInverseSystemExistenceSituation.system)
        D.toInverseSystemExistenceSituation.containsLimitBase)
      (j : W' ⟶ D.toInverseSystemExistenceSituation.X.left)
      (_ : IsOpenImmersion D.toInverseSystemExistenceSituation.B
        (limitBase D.toInverseSystemExistenceSituation.system)
        D.toInverseSystemExistenceSituation.containsLimitBase j.hom),
      Set.range (pointsMap D.toInverseSystemExistenceSituation.B
        (limitBase D.toInverseSystemExistenceSituation.system)
        D.toInverseSystemExistenceSituation.containsLimitBase
        (spaceAt D.toInverseSystemExistenceSituation.system D.toInverseSystemExistenceSituation.B
          D.toInverseSystemExistenceSituation.containsLimitBase
          D.toInverseSystemExistenceSituation.containsBaseAt
          D.toInverseSystemExistenceSituation.X 0).1
        (spaceProjection D.toInverseSystemExistenceSituation.system
          D.toInverseSystemExistenceSituation.B
          D.toInverseSystemExistenceSituation.containsLimitBase
          D.toInverseSystemExistenceSituation.containsBaseAt
          D.toInverseSystemExistenceSituation.X 0).hom) ⊆
        Set.range (pointsMap D.toInverseSystemExistenceSituation.B
          (limitBase D.toInverseSystemExistenceSituation.system)
          D.toInverseSystemExistenceSituation.containsLimitBase W'.1 j.hom) ∧
      ((modulePullback D.toInverseSystemExistenceSituation.B
        (limitBase D.toInverseSystemExistenceSituation.system)
        D.toInverseSystemExistenceSituation.containsLimitBase j).obj H).IsFinitePresentationOnSite ∧
      ∃ β : ∀ n : ℕ, (modulePullback D.toInverseSystemExistenceSituation.B
          (limitBase D.toInverseSystemExistenceSituation.system)
          D.toInverseSystemExistenceSituation.containsLimitBase
          (spaceProjection D.toInverseSystemExistenceSituation.system
            D.toInverseSystemExistenceSituation.B
            D.toInverseSystemExistenceSituation.containsLimitBase
            D.toInverseSystemExistenceSituation.containsBaseAt
            D.toInverseSystemExistenceSituation.X n)).obj H ≅
            (D.toInverseSystemExistenceSituation.sheaf n).obj,
        ∀ n : ℕ,
          ModulePullbackCompatible
            (transitionSpace D.toInverseSystemExistenceSituation.system
              D.toInverseSystemExistenceSituation.B
              D.toInverseSystemExistenceSituation.containsLimitBase
              D.toInverseSystemExistenceSituation.containsBaseAt
              D.toInverseSystemExistenceSituation.X n)
            (spaceProjection D.toInverseSystemExistenceSituation.system
              D.toInverseSystemExistenceSituation.B
              D.toInverseSystemExistenceSituation.containsLimitBase
              D.toInverseSystemExistenceSituation.containsBaseAt
              D.toInverseSystemExistenceSituation.X (n + 1))
            (spaceProjection D.toInverseSystemExistenceSituation.system
              D.toInverseSystemExistenceSituation.B
              D.toInverseSystemExistenceSituation.containsLimitBase
              D.toInverseSystemExistenceSituation.containsBaseAt
              D.toInverseSystemExistenceSituation.X n)
            (transitionSpace_spaceProjection D.toInverseSystemExistenceSituation.system
              D.toInverseSystemExistenceSituation.B
              D.toInverseSystemExistenceSituation.containsLimitBase
              D.toInverseSystemExistenceSituation.containsBaseAt
              D.toInverseSystemExistenceSituation.X n)
            H (D.toInverseSystemExistenceSituation.φ n) (β (n + 1)).hom (β n).hom :=
  ⟨(spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj K,
    openSubspaceSpace D.B D.S D.containsLimitBase W hW,
    openSubspaceHom D.B D.S D.containsLimitBase W hW, hW.2,
    D.range_closedImmersion_zero.le.trans hN.subset_range, hN.isFinitePresentation,
    fun n => @asIso _ _ _ _ (D.stageComparison K π n) (hN.isIso_stageComparison_stage D n),
    fun n => D.stageComparison_compatible K π hπ n⟩

end FlatSheafExistenceSituation

namespace InverseSystemExistenceSituation

/-- **Every situation in the form `AlgebraicGeometry.Space.InverseSystemExistenceSituation` comes
from one in the form `AlgebraicGeometry.Space.FlatSheafExistenceSituation`.** -/
theorem exists_eq_toInverseSystemExistenceSituation (s : InverseSystemExistenceSituation.{u}) :
    ∃ D : FlatSheafExistenceSituation.{u}, D.toInverseSystemExistenceSituation = s := by
  refine ⟨{ system := s.system, transition_surjective := s.transition_surjective
            transition_locallyNilpotent := s.transition_locallyNilpotent, B := s.B
            containsLimitBase := s.containsLimitBase, containsBaseAt := s.containsBaseAt
            X := s.X, separated := isSeparated_of_isSeparatedOver _ _ _ s.separated _
            finitePresentation := s.finitePresentation, F := fun n => (s.sheaf n).obj
            finitelyPresented := s.finitePresentation_sheaf, flat := s.flat_sheaf
            properSupport := fun n => ⟨s.closed_support n, s.properSupport n⟩, φ := s.φ }, ?_⟩
  cases s
  rfl

end InverseSystemExistenceSituation

end AlgebraicGeometry.Space

end
