module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.IdealPowerCohomologyFinite
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.MittagLefflerCriteria

/-!
# The boundary maps of the ideal-power sequences of a coherent adic system

For a coherent adic system `(F_n)` on the open `U`, the short exact sequences

`0 → Iⁿ⁺¹ F_(n+1) → F_(n+1) → F_n → 0`

of `Stacks.Algebraization.idealPowerShortComplex` have in degree zero a boundary map

`δₙ : H⁰(U, F_n) ⟶ H¹(U, Iⁿ⁺¹ F_(n+1))`

whose kernel is exactly the image of the transition `H⁰(U, F_(n+1)) → H⁰(U, F_n)`.

## Main definitions

* `Stacks.Algebraization.topCohomologyFunctor`: `Hᵖ(U, -)` as a functor to modules over
  `𝒪_U(⊤)`.

## Main results

* `Stacks.Algebraization.exists_boundary_sections`: the boundary map in degree zero, with its
  kernel identified as the image of the transition map.

## References

* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
* [Stacks Project, Tag 0EJS](https://stacks.math.columbia.edu/tag/0EJS)
* [Stacks Project, Tag 0GYK](https://stacks.math.columbia.edu/tag/0GYK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- `Hᵖ(U, -)` as a functor to modules over `𝒪_U(⊤)` in its `RingCat` spelling: the `p`-th right
derived functor of evaluation at the top open. -/
abbrev topCohomologyFunctor (p : ℕ) :
    _root_.SheafOfModules.{u} S.U.toScheme.ringCatSheaf ⥤
      ModuleCat.{u} (S.U.toScheme.ringCatSheaf.obj.obj (op (⊤ : S.U.toScheme.Opens))) :=
  (_root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf
    (op (⊤ : S.U.toScheme.Opens))).rightDerived p

/-- **The boundary maps of the ideal-power sequences.** The short exact sequence
`0 → Iⁿ⁺¹ F_(n+1) → F_(n+1) → F_n → 0` has a boundary map
`H⁰(U, F_n) ⟶ H¹(U, Iⁿ⁺¹ F_(n+1))` whose kernel is the image of the transition map
`H⁰(U, F_(n+1)) → H⁰(U, F_n)`. -/
theorem exists_boundary_sections (n : ℕ) :
    ∃ δ : (topCohomologyFunctor S 0).obj (F.obj.obj (op n)) ⟶
        (topCohomologyFunctor S 1).obj (idealPowerSub S F n).toSheafOfModules,
      LinearMap.range ((topCohomologyFunctor S 0).map
          (F.obj.map (homOfLE (Nat.le_succ n)).op)).hom = LinearMap.ker δ.hom := by
  obtain ⟨_, δ, hδ, _⟩ :=
    Stacks.Cohomology.InverseSystems.exists_connecting_maps S.U.toScheme.ringCatSheaf 0
  obtain ⟨e, he⟩ := F.property.2.2 n
  have hse := idealPowerShortComplex_shortExact S F n
  let φ := (topCohomologyFunctor S 0).mapIso e
  refine ⟨φ.inv ≫ δ hse, ?_⟩
  have hcomp : (topCohomologyFunctor S 0).map (F.obj.map (homOfLE (Nat.le_succ n)).op) =
      (topCohomologyFunctor S 0).map (cokernel.π (idealPowerSub S F n).ι) ≫ φ.hom :=
    (congrArg (topCohomologyFunctor S 0).map he).symm.trans
      ((topCohomologyFunctor S 0).map_comp _ _)
  exact (congrArg (fun g ↦ LinearMap.range (ModuleCat.Hom.hom g)) hcomp).trans
    ((LinearMap.range_comp _ _).trans (((congrArg (Submodule.map φ.hom.hom) (hδ hse)).trans
      (Submodule.map_equiv_eq_comap_symm φ.toLinearEquiv _)).trans (LinearMap.ker_comp _ _).symm))

end Stacks.Algebraization

end
