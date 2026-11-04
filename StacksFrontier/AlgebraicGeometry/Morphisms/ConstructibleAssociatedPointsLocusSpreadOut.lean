module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BaseChangeFiberMap

/-!
# Local constructibility of the fibrewise associated-point locus from spreading out

Let `f : X ⟶ Y` be a morphism of schemes, let `F` be an `𝒪_X`-module and let `U ⊆ X` be an
open subscheme. This file shows that the locus

`E = {y : Y | Ass(F_y) ⊆ U_y}`

is locally constructible on a locally Noetherian base, provided that on every irreducible closed
subset `Z ⊆ Y` with generic point `η` the condition defining `E` is constant on a nonempty open
part of `Z`, with value its value at `η`.

## Main results

* `Stacks.Divisors.isLocallyConstructible_setOf_associatedPoints_fiber_subset_of_spreadOut`:
  the locus is locally constructible on a locally Noetherian base, given the two spreading
  implications separately.
* `Stacks.Divisors.isLocallyConstructible_associatedPoints_fiber_subset_of_spreadOut`: the
  same conclusion for a morphism of finite presentation and a module of finite presentation,
  from a single two-sided spreading hypothesis.

## Implementation notes

The spreading hypothesis and `IsLocallyNoetherian Y` stand in for Stacks 05KN, Stacks 05KP and
the limit argument of the source. The second result carries the hypotheses of the source on
`(f, F, U)`, although its proof does not use them.

## References

* [Stacks Project, Tag 05KN](https://stacks.math.columbia.edu/tag/05KN)
* [Stacks Project, Tag 05KP](https://stacks.math.columbia.edu/tag/05KP)
* [Stacks Project, Tag 05KQ](https://stacks.math.columbia.edu/tag/05KQ)
* [Stacks Project, Tag 05KR](https://stacks.math.columbia.edu/tag/05KR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- A morphism that is surjective on stalks induces an isomorphism on residue fields. -/
instance isIso_residueFieldMap_of_surjectiveOnStalks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : IsIso (f.residueFieldMap x) :=
  AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks f x

section BaseChangeFiber

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (z : Y')

/-- The fibre of the inverse image of an open subscheme under the projection of a base change
is the inverse image, under the induced morphism of fibres, of the fibre of that open
subscheme. -/
theorem preimage_baseChangeFiberMap_eq (U : X.Opens) :
    (pullback.snd f g).fiberι z ⁻¹' (pullback.fst f g ⁻¹' (U : Set X)) =
      baseChangeFiberMap f g z ⁻¹' (f.fiberι (g z) ⁻¹' (U : Set X)) := by
  ext x
  have h : pullback.fst f g ((pullback.snd f g).fiberι z x) =
      f.fiberι (g z) (baseChangeFiberMap f g z x) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, baseChangeFiberMap_comp_fiberι]
  simp only [Set.mem_preimage, h]

end BaseChangeFiber

end AlgebraicGeometry

namespace Stacks.Divisors

variable {X Y : Scheme.{u}}

/-- The locus where the associated points of the fibre of `F` lie in `U` is locally
constructible on a locally Noetherian base, provided that on every irreducible closed subset
`Z` of the base both membership and non-membership of the generic point in the locus spread to
a nonempty open part of `Z`. -/
theorem isLocallyConstructible_setOf_associatedPoints_fiber_subset_of_spreadOut
    (f : X ⟶ Y) [IsLocallyNoetherian Y] (F : X.Modules) (U : X.Opens)
    (hmem : ∀ (Z : Set Y) (η : Y), IsIrreducible Z → IsClosed Z → IsGenericPoint η Z →
      associatedPoints ((Scheme.Modules.pullback (f.fiberι η)).obj F) ⊆
          f.fiberι η ⁻¹' (U : Set X) →
      ∃ V : Set Y, IsOpen V ∧ (V ∩ Z).Nonempty ∧ ∀ y ∈ V ∩ Z,
        associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
          f.fiberι y ⁻¹' (U : Set X))
    (hnmem : ∀ (Z : Set Y) (η : Y), IsIrreducible Z → IsClosed Z → IsGenericPoint η Z →
      ¬ associatedPoints ((Scheme.Modules.pullback (f.fiberι η)).obj F) ⊆
          f.fiberι η ⁻¹' (U : Set X) →
      ∃ V : Set Y, IsOpen V ∧ (V ∩ Z).Nonempty ∧ ∀ y ∈ V ∩ Z,
        ¬ associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
          f.fiberι y ⁻¹' (U : Set X)) :
    IsLocallyConstructible
      {y : Y | associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
        f.fiberι y ⁻¹' (U : Set X)} := by
  refine isLocallyConstructible_of_isGenericPoint_dichotomy hmem fun Z η hZ hZc hη hηE => ?_
  obtain ⟨V, hVo, hVne, hV⟩ := hnmem Z η hZ hZc hη hηE
  exact ⟨V, hVo, hVne, Set.disjoint_left.2 hV⟩

/-- For a morphism of finite presentation to a locally Noetherian scheme, a quasi-coherent module
of finite presentation and an open subscheme that is quasi-compact over the base, the locus of
points of the base over which all associated points of the fibre lie in the open subscheme is
locally constructible, provided that the defining condition is constant on a nonempty open part
of every irreducible closed subset of the base, with value its value at the generic point. -/
theorem isLocallyConstructible_associatedPoints_fiber_subset_of_spreadOut
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [IsLocallyNoetherian Y]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (U : X.Opens) [QuasiCompact (U.ι ≫ f)]
    (hspread : ∀ (Z : Set Y) (η : Y), IsIrreducible Z → IsClosed Z → IsGenericPoint η Z →
      ∃ V : Set Y, IsOpen V ∧ (V ∩ Z).Nonempty ∧ ∀ y ∈ V ∩ Z,
        (associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
            f.fiberι y ⁻¹' (U : Set X) ↔
          associatedPoints ((Scheme.Modules.pullback (f.fiberι η)).obj F) ⊆
            f.fiberι η ⁻¹' (U : Set X))) :
    IsLocallyConstructible
      {y : Y | associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
        f.fiberι y ⁻¹' (U : Set X)} := by
  refine isLocallyConstructible_setOf_associatedPoints_fiber_subset_of_spreadOut f F U
    (fun Z η hZ hZc hη hηE => ?_) (fun Z η hZ hZc hη hηE => ?_) <;>
  obtain ⟨V, hVo, hVne, hV⟩ := hspread Z η hZ hZc hη <;>
  refine ⟨V, hVo, hVne, fun y hy => ?_⟩
  · exact (hV y hy).2 hηE
  · exact fun hyE => hηE ((hV y hy).1 hyE)

end Stacks.Divisors
