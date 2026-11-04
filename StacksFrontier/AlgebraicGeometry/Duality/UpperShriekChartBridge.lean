module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekChartModels
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativePerfection
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso

/-!
# The chart description of `f^!𝒪_Y` from the upper shriek charts of `f^!`

`Stacks.Duality.HasUpperShriekCharts f K L` says that over affine opens `U ⊆ f⁻¹(V)` every model
of `K` on `V` is carried to a model of `L` on `U` by an algebraic upper shriek, which is the shape
of [Stacks, Tag 0BV2] for `L = f^!K`. At `K = 𝒪_Y`, modelled on `V` by `Γ(Y, V)` in degree zero,
this gives `Stacks.Duality.IsShriekOfStructureSheafOnCharts f L`, the chart description from
which [Stacks, Tag 0E9T] is proved.

The two predicates read the derived categories at different models (`HasUpperShriekCharts` at the
locally small model of `D(𝒪_X)` and the standard model of `D(𝒪_U)`, the chart description the
other way round); the comparison equivalences of the models carry one to the other.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)

/-- **The chart description of `L` from its upper shriek charts at the structure sheaf.** If `L`
has upper shriek charts over `𝒪_Y`, then over every point of `X` an affine chart `U` over an
affine `V` exhibits `L|_U` as the associated sheaf of the algebraic upper shriek of `Γ(Y, V)`. -/
theorem isShriekOfStructureSheafOnCharts_of_hasUpperShriekCharts
    (L : DerivedCategory X.left.Modules)
    (h : HasUpperShriekCharts f.left
      ((DerivedCategory.singleFunctor Y.left.Modules 0).obj
        (SheafOfModules.unit Y.left.ringCatSheaf)) L) :
    letI := HasDerivedCategory.standard X.left.Modules
    IsShriekOfStructureSheafOnCharts f L := by
  intro x
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y.left) (x := f.left.base x) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X.left) (x := x) (U := f.left ⁻¹ᵁ V) hxV
  obtain ⟨p, hp⟩ := h U hU V hV hUV _ (isTildeModelOnAnyModel_unit V hV)
  refine ⟨U, hU, V, hV, hUV, hxU, p, ?_⟩
  let := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme
  obtain ⟨e⟩ := hp
  exact ⟨(Stacks.Injectives.mapDerivedCategoryObjIso X.left.Modules
      (Scheme.Modules.restrictFunctor U.ι) L) ≪≫
    ((Stacks.Injectives.mapDerivedCategoryTargetModelIso U.toScheme.Modules
      (Scheme.Modules.restrictFunctor U.ι)).app L).symm ≪≫
    (Stacks.Injectives.grothendieckModelEquiv U.toScheme.Modules).functor.mapIso e ≪≫
    (Stacks.Injectives.mapDerivedCategoryTargetModelIso U.toScheme.Modules
      (hd₁ := HasDerivedCategory.standard (ModuleCat.{u} Γ(X.left, U)))
      (tilde.functor Γ(X.left, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom)).app _⟩

end Stacks.Duality
