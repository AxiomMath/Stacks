module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Components
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusZeroVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic

/-!
# A regular model with an inseparable component: the two components have genus zero

The two components `(ker jC₁) ≅ ℙ¹_k` and `(ker jE) ≅ ℙ¹_κ` of the special fibre of the model of
`Stacks.Models.InseparableModel` have `H¹(𝒪) = 0`, hence genus zero over any base field.

The general input is that `H¹(𝐏¹_F, 𝒪) = 0` for a field `F`, so the first cohomology of the
structure sheaf vanishes, as an abelian group, on every scheme `Y` isomorphic to `𝐏¹_F`. The
genus of `Y` over a field `L` is the `L`-dimension of that group for the `L`-structure given by a
morphism `Y ⟶ Spec L`, so it is zero for every such morphism, whether or not `L` is `F`. The
closed subscheme cut out by the kernel of a closed immersion of `𝐏¹_F` is isomorphic to `𝐏¹_F`.

## Main results

* `Stacks.Curves.isZero_rightDerived_evaluation_unit_one_of_iso_projectiveLine`:
  `H¹(Y, 𝒪_Y) = 0` for `Y ≅ 𝐏¹_F`.
* `Stacks.Curves.genus_eq_zero_of_iso_projectiveLine`: `genus (Y ⟶ Spec L) = 0` for
  `Y ≅ 𝐏¹_F` and any field `L`.
* `Stacks.Curves.genus_eq_zero_of_isClosedImmersion_projectiveLine`: the same for the image of a
  closed immersion of `𝐏¹_F`.
* `Stacks.Models.InseparableModel.genus_eq_zero_of_eq_ker_jC₁`
* `Stacks.Models.InseparableModel.genus_eq_zero_of_eq_ker_jE`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

namespace Stacks.Curves

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **`H¹(Y, 𝒪_Y) = 0` for a scheme `Y` isomorphic to the projective line over a field**, as the
first right derived functor of evaluation on the whole space. -/
theorem isZero_rightDerived_evaluation_unit_one_of_iso_projectiveLine {F : Type u} [Field F]
    {Y : Scheme.{u}} (e : Y ≅ AlgebraicGeometry.Proj (polyGrading F 1)) :
    IsZero
      (((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).rightDerived 1).obj
        (SheafOfModules.unit Y.ringCatSheaf)) := by
  have : IsProper (projToSpecCoeff F 1) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := F) 1
  have hg : genus (e.hom ≫ projToSpecCoeff F 1) = 0 :=
    (genus_comp_iso_eq F (projToSpecCoeff F 1) e).trans (genus_projToSpecCoeff_one F)
  exact isZero_rightDerived_evaluation_unit_one_of_genus_eq_zero F _ hg

/-- **A scheme isomorphic to the projective line over a field has genus zero over every field**:
the `L`-structure is irrelevant, because the group `H¹(Y, 𝒪_Y)` itself is zero. -/
theorem genus_eq_zero_of_iso_projectiveLine {F : Type u} [Field F] {Y : Scheme.{u}}
    (e : Y ≅ AlgebraicGeometry.Proj (polyGrading F 1)) {L : Type u} [Field L]
    (f : Y ⟶ Spec (.of L)) : genus f = 0 := by
  have h := isZero_rightDerived_evaluation_unit_one_of_iso_projectiveLine e
  have h0 := ModuleCat.subsingleton_of_isZero h
  have hs : Subsingleton (cohomologyOverField L f (SheafOfModules.unit Y.ringCatSheaf) 1) := h0
  rw [genus_eq_finrank_structureSheafCohomology,
    (structureSheafCohomologyIsoCohomologyOverField L f 1).toLinearEquiv.finrank_eq]
  exact Module.finrank_zero_of_subsingleton

/-- **The image of a closed immersion of the projective line over a field has genus zero over
every field.** -/
theorem genus_eq_zero_of_isClosedImmersion_projectiveLine {F : Type u} [Field F]
    {X : Scheme.{u}} (j : AlgebraicGeometry.Proj (polyGrading F 1) ⟶ X) [IsClosedImmersion j]
    {L : Type u} [Field L] (f : j.ker.subscheme ⟶ Spec (.of L)) : genus f = 0 :=
  genus_eq_zero_of_iso_projectiveLine (asIso j.toImage).symm f

end Stacks.Curves

namespace Stacks.Models.InseparableModel

/-- The strict transform has genus zero, over any field. -/
theorem genus_eq_zero_of_eq_ker_jC₁ {I : XR.IdealSheafData} (hI : I = jC₁.ker) {L : Type}
    [Field L] (f : I.subscheme ⟶ Spec (.of L)) : genus f = 0 := by
  subst hI
  exact Stacks.Curves.genus_eq_zero_of_isClosedImmersion_projectiveLine jC₁ f

/-- The exceptional curve has genus zero, over any field. -/
theorem genus_eq_zero_of_eq_ker_jE {I : XR.IdealSheafData} (hI : I = jE.ker) {L : Type}
    [Field L] (f : I.subscheme ⟶ Spec (.of L)) : genus f = 0 := by
  subst hI
  exact Stacks.Curves.genus_eq_zero_of_isClosedImmersion_projectiveLine jE f

end Stacks.Models.InseparableModel
