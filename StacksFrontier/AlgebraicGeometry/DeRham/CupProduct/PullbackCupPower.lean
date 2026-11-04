module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackEvenDegreeRing
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismComposition

/-!
# Pullback of cup powers in de Rham cohomology

A family of additive maps of de Rham cohomology which preserves the unit and the cup product
carries the cup powers `ξ^t` (`AlgebraicGeometry.SheafOfModules.deRhamCohomologyPow`,
`ξ^0 = 1`, `ξ^{t+1} = ξ ∪ ξ^t`) of a class to the cup powers of its image. In particular the
pullback of de Rham cohomology along a commutative square of schemes (Section 0FL6) does, by the
multiplicativity of pullback (Section 0FM1).

## Main results

* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyPow_map`: `P(ξ^t) = P(ξ)^t`.
* `Stacks.DeRhamBaseChange.deRhamPullbackSquare_deRhamCohomologyPow`: `g'^*(ξ^t) = (g'^*ξ)^t`.

## References

* [Stacks Project, Section 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Section 0FM1](https://stacks.math.columbia.edu/tag/0FM1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  {B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ)}
  {D : DeRhamDifferential B}
  {X' : RingedSpace.{u, u}} {A' : TopCat.Sheaf CommRingCat.{u} X'.carrier}
  {φ' : A' ⟶ X'.sheaf}
  {B' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X'.carrier) (moduleOfDifferentials.{u, u, u} φ')}
  {D' : DeRhamDifferential B'}

/-- **A family of additive maps of de Rham cohomology preserving the unit and the cup product
preserves cup powers**: `P(ξ^t) = P(ξ)^t`. -/
theorem deRhamCohomologyPow_map
    (P : ∀ m : ℤ, deRhamCohomology B D m →+ deRhamCohomology B' D' m)
    (hone : P 0 (deRhamOneClass B D) = deRhamOneClass B' D')
    (hmul : ∀ (m n : ℤ) (x : deRhamCohomology B D m) (y : deRhamCohomology B D n),
      P (m + n) (deRhamCohomologyCup B D m n x y) =
        deRhamCohomologyCup B' D' m n (P m x) (P n y))
    (d : ℕ) (ξ : deRhamCohomology B D (d : ℤ)) (t : ℕ) :
    P _ (deRhamCohomologyPow B D d ξ t) = deRhamCohomologyPow B' D' d (P _ ξ) t := by
  induction t with
  | zero => exact hone
  | succ t ih =>
    rw [deRhamCohomologyPow_succ, deRhamCohomologyPow_succ, reindexDeRhamCohomology_apply, hmul,
      ih]

end AlgebraicGeometry.SheafOfModules

namespace Stacks.DeRhamBaseChange

open _root_.AlgebraicGeometry

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- **Pullback of de Rham cohomology preserves cup powers**: `g'^*(ξ^t) = (g'^*ξ)^t`. -/
theorem deRhamPullbackSquare_deRhamCohomologyPow (d : ℕ)
    (ξ : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) (d : ℤ))
    (t : ℕ) :
    deRhamPullbackSquare g' f' f g w _
        (AlgebraicGeometry.SheafOfModules.deRhamCohomologyPow _ _ d ξ t) =
      AlgebraicGeometry.SheafOfModules.deRhamCohomologyPow _ _ d
        (deRhamPullbackSquare g' f' f g w _ ξ) t :=
  AlgebraicGeometry.SheafOfModules.deRhamCohomologyPow_map (deRhamPullbackSquare g' f' f g w)
    (deRhamPullbackSquare_one g' f' f g w) (deRhamPullbackSquare_cup g' f' f g w) d ξ t

end Stacks.DeRhamBaseChange
