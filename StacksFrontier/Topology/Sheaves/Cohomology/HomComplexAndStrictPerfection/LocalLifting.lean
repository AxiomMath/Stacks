module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.LocalNullHomotopyOverSlices
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs

import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectCone

/-!
# Local lifting through a cohomological isomorphism

Let `X` be a ringed space, let `E` be a strictly perfect complex of `𝒪_X`-modules concentrated
in degrees `≥ a`, and let `f : G ⟶ F` be a morphism of complexes of `𝒪_X`-modules which is an
isomorphism on cohomology in every degree above `a` and an epimorphism on cohomology in degree
`a`. Then any `α : E ⟶ F` lifts through `f`, up to homotopy, on a neighbourhood of every point
of `X`. This is [Stacks, Tag 08C8].

## Main results

* `Stacks.Cohomology.exists_local_lift_homotopy`: the local lifts and their homotopies.

## Implementation notes

Restriction to an open is the degreewise application of
`SheafOfModules.overFunctor (StrictlyPerfect.structureSheafOfRings X) U`, which is the form in
which [Stacks, Tag 08C7] states its conclusion. Surjectivity of the cohomology sheaf map is
expressed by `Epi` and equality up to homotopy by the existence of a `Homotopy`.

All universes coincide, as they must for `StrictlyPerfect.OXMod` to exist: the ring universe
and the space universe of the ringed space have to agree, and `StrictlyPerfect.OXMod` fixes the
module universe to the same one. Because they agree, the sheafification typeclasses making
complexes of `𝒪_X`-modules have cohomology sheaves are found automatically.

## References

* [Stacks Project, Tag 08C8](https://stacks.math.columbia.edu/tag/08C8)
* [Stacks Project, Tag 08C7](https://stacks.math.columbia.edu/tag/08C7)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open StrictlyPerfect

namespace Stacks.Cohomology

universe u

variable {X : RingedSpace.{u, u}}
variable {E F G : CochainComplex (OXMod.{u, u} X) ℤ}

/-- A map from a strictly perfect complex lifts locally up to homotopy through a map that is
cohomologically an isomorphism above the lower bound and surjective at the lower bound. -/
theorem exists_local_lift_homotopy (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : IsStrictlyPerfect E) (hEa : ∀ j : ℤ, j < a → IsZero (E.X j))
    (hf_gt : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_a : Epi (HomologicalComplex.homologyMap f a)) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ β : ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E ⟶
          ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G,
        Nonempty (Homotopy
          (β ≫ ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)
          (((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α)) := by
  have hcone := AlgebraicGeometry.RingedSpace.isZero_homology_mappingCone f a hf_gt hf_a
  intro x
  obtain ⟨U, hx, hzero⟩ := RingedSpace.exists_local_homotopy_zero_of_isZero_homology
    (α := α ≫ CochainComplex.mappingCone.inr f) a hE hEa hcone x
  let COpen := SheafOfModules.{u} ((structureSheafOfRings X).over U)
  let : HasFiniteBiproducts COpen := HasFiniteBiproducts.of_hasFiniteProducts
  let : HasBinaryBiproducts COpen := hasBinaryBiproducts_of_finite_biproducts _
  let R := SheafOfModules.overFunctor (structureSheafOfRings X) U
  let RHC := R.mapHomologicalComplex (ComplexShape.up ℤ)
  let Q := HomotopyCategory.quotient COpen (ComplexShape.up ℤ)
  let fOpen := RHC.map f
  let αOpen := RHC.map α
  let ιOpen := CochainComplex.mappingCone.inr fOpen
  let coneIso := CochainComplex.mappingCone.mapHomologicalComplexIso f R
  have hnull : Q.map (RHC.map α ≫ RHC.map (CochainComplex.mappingCone.inr f)) = 0 := by
    rw [← Functor.map_comp]
    exact (HomotopyCategory.quotient_map_eq_zero_iff _).2 hzero
  have hconeInr : RHC.map (CochainComplex.mappingCone.inr f) ≫ coneIso.hom = ιOpen :=
    CochainComplex.mappingCone.map_inr (H := R) (φ := f)
  have hchain : αOpen ≫ ιOpen =
      (RHC.map α ≫ RHC.map (CochainComplex.mappingCone.inr f)) ≫ coneIso.hom := by
    dsimp only [αOpen]
    rw [← hconeInr, Category.assoc]
  have hcomp : Q.map αOpen ≫ Q.map ιOpen = 0 := by
    rw [← Functor.map_comp, hchain, Functor.map_comp, hnull, zero_comp]
  let T := CochainComplex.mappingCone.triangleh fOpen
  have hT : T ∈ distTriang (HomotopyCategory COpen (ComplexShape.up ℤ)) :=
    HomotopyCategory.mappingCone_triangleh_distinguished fOpen
  obtain ⟨βq, hβq⟩ :=
    CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂ T hT (Q.map αOpen) hcomp
  obtain ⟨β, hβ⟩ := Q.map_surjective βq
  change RHC.obj E ⟶ RHC.obj G at β
  have hdiff : Q.map (β ≫ fOpen - αOpen) = 0 := by
    rw [Functor.map_sub, Functor.map_comp, sub_eq_zero]
    exact (congrArg (· ≫ Q.map fOpen) hβ).trans hβq.symm
  obtain ⟨H⟩ := (HomotopyCategory.quotient_map_eq_zero_iff _).1 hdiff
  exact ⟨U, hx, β, ⟨Homotopy.equivSubZero.symm H⟩⟩

end Stacks.Cohomology

end
