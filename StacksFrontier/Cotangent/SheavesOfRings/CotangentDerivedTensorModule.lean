module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentFlatTerms
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product of the cotangent complex of a morphism of sheaves of rings

Let `C` be a site, let `f : 𝒜 ⟶ ℬ` be a morphism of sheaves of commutative rings on `C` and let
`ℱ` be a sheaf of `ℬ`-modules. The first term `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` of the Atiyah triangle of
[Stacks, Tag 09DH] is the ordinary total tensor product of the cotangent complex with `ℱ` placed
in degree zero: the cotangent complex is K-flat.

## Main results

* `CategoryTheory.Sheaf.isFlat_cotangentComplex_X`: the terms of the cotangent complex of a
  morphism of sheaves of rings are flat.
* `CategoryTheory.Sheaf.isKFlat_cotangentComplex`: the cotangent complex of a morphism of
  sheaves of rings is K-flat.
* `CategoryTheory.Sheaf.cotangentComplexDerivedTensorIso`: `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` is the ordinary
  total tensor product of `L_{ℬ/𝒜}` with `ℱ[0]`, as an object of `D(ℬ)`.

## References

* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the Atiyah triangle,
  whose first term this is.
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ), a bounded above complex
  of flat modules is K-flat.
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU), the derived tensor
  product on a ringed site and its K-flat comparisons.
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS), the cotangent complex of
  a morphism of sheaves of rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct derivedTensorProductFunctor)

universe u

namespace CategoryTheory.Sheaf

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-- The cotangent complex of a morphism of sheaves of rings is strictly `≤ 0`. -/
theorem isStrictlyLE_cotangentComplex :
    (cotangentComplex.{u, u, u} J f).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi => cotangentComplex_isZero_pos.{u, u, u} J f i hi

/-- The terms of the cotangent complex of a morphism of sheaves of rings are flat. -/
theorem isFlat_cotangentComplex_X (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := B)
      ((cotangentComplex.{u, u, u} J f).X i) := by
  rcases lt_or_ge 0 i with hi | hi
  · exact Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero
      (Y := ⟨C, J, B⟩) _ (cotangentComplex_isZero_pos.{u, u, u} J f i hi)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso B
      (cotangentComplex_degreeIso.{u, u, u} J f n).symm
      (isFlat_cotangentSimplicialModule_obj.{u, u, u} J f n)

/-- The cotangent complex of a morphism of sheaves of rings is K-flat. -/
theorem isKFlat_cotangentComplex :
    Stacks.SheafOfModules.IsKFlat B (cotangentComplex.{u, u, u} J f) :=
  Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat B (cotangentComplex.{u, u, u} J f)
    ⟨0, isStrictlyLE_cotangentComplex J f⟩ (isFlat_cotangentComplex_X J f)

/-- `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` is the ordinary total tensor product of the cotangent complex with `ℱ`
placed in cohomological degree zero, as an object of `D(ℬ)`. -/
def cotangentComplexDerivedTensorIso
    (F : Stacks.DerivedTensor.RingedSite.Modules B) :
    ((derivedTensorProductFunctor B).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
            (ComplexShape.up ℤ) 0).obj F)) ≅
      DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex B).obj
            (cotangentComplex.{u, u, u} J f)).obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
            (ComplexShape.up ℤ) 0).obj F)) :=
  (canonicalDerivedTensorProduct B).comparisonLeft _ _ (isKFlat_cotangentComplex J f)

end CategoryTheory.Sheaf

end
