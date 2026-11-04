module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedClauseThreeToTwo
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedTensorRestrictScalars
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorRestrictScalars

/-!
# Invertibility over a factor from a local tensor identification

Let `𝒪_X = ∏ 𝒪_n` be a product decomposition of the structure sheaf of a ringed space and let
`H`, `H'` be `𝒪_n`-modules. If on every member of an open covering the restriction of
`H ⊗_{𝒪_X} H'` (both read as `𝒪_X`-modules) is the restriction of the factor `𝒪_n`, then `H` is
an invertible `𝒪_n`-module.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite TopologicalSpace StrictlyPerfect Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.InvertibleDerived

variable {X : RingedSpace.{u, u}}

/-- Modules whose restrictions to an open subspace are isomorphic have isomorphic restrictions to
the slice site over that open. -/
public def overIsoOfRestrictIso (V : Opens X.carrier) {A B : Mod X.sheaf}
    (e : (restrictModules X V).obj A ≅ (restrictModules X V).obj B) : A.over V ≅ B.over V :=
  haveI := AlgebraicGeometry.RingedSpace.overToRestricted_isEquivalence X V
  (AlgebraicGeometry.RingedSpace.overToRestricted X V).preimageIso e

namespace ProductDecomposition

/-- The projection `𝒪_X → 𝒪_n` onto a factor, over the slice site of `W`, is locally surjective:
it is surjective on sections. -/
public instance isLocallySurjective_projOver (D : ProductDecomposition X) (n : ℤ)
    (W : Opens X.carrier) : Sheaf.IsLocallySurjective (D.projOver n W) :=
  CategoryTheory.Presheaf.isLocallySurjective_of_surjective _ (D.projOver n W).hom fun V =>
    Stacks.SheafOfModules.RingSheafProductFactor.surjective_projRing_app D.productPresentation n
      (op V.unop.left)

/-- Reading `𝒪_n`-modules as `𝒪_X`-modules is fully faithful on the slice site over `W`. -/
public def fullyFaithfulRestrictScalarsProjOver (D : ProductDecomposition X) (n : ℤ)
    (W : Opens X.carrier) :
    (SheafOfModules.restrictScalars.{u} (D.projOver n W)).FullyFaithful :=
  Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective (D.projOver n W)

/-- Restricting to the slice site commutes with reading `𝒪_n`-modules as `𝒪_X`-modules. -/
public def overToOXModIso (D : ProductDecomposition X) (n : ℤ) (W : Opens X.carrier)
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :
    ((D.toOXMod n).obj A).over W ≅
      (SheafOfModules.restrictScalars (D.projOver n W)).obj (A.over W) :=
  Iso.refl _

end ProductDecomposition

/-- **A left factor of an invertible tensor product is invertible.** -/
public theorem isInvertibleModule_left_of_tensorObj {S : Sheaf (Opens.grothendieckTopology
      X.carrier) CommRingCat.{u}}
    (H H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S))
    (h : letI := SheafOfModules.monoidalCategorySheafTensor S
      Stacks.SheafOfModules.Tensor.IsInvertibleModule S
        (H ⊗ H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S))) :
    Stacks.SheafOfModules.Tensor.IsInvertibleModule S H := by
  let := SheafOfModules.monoidalCategorySheafTensor S
  have key := Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := S.obj) (hO := (Stacks.SheafOfModules.Tensor.ringSheaf S).property)
  obtain ⟨G, ⟨e⟩⟩ :=
    (key (H ⊗ H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S))).mp h
  exact (key H).mpr
    ⟨(H' ⊗ G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S)),
      ⟨(α_ H H' G).symm ≪≫ e⟩⟩

/-- **Invertibility over a factor from a local tensor identification.** Let `H`, `H'` be modules
over the `n`-th factor of a product decomposition of `𝒪_X`. If on every member of an open
covering the restriction of `H ⊗_{𝒪_X} H'` is the restriction of `𝒪_n`, all read as
`𝒪_X`-modules, then `H` is invertible over `𝒪_n`. -/
public theorem isInvertibleModule_of_restrict_tensorObj_iso (D : ProductDecomposition X) (n : ℤ)
    (H H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (V : X.carrier → Opens X.carrier) (hxV : ∀ x, x ∈ V x)
    (e : ∀ x, letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
      Nonempty ((restrictModules X (V x)).obj
          ((D.toOXMod n).obj H ⊗ (D.toOXMod n).obj H' : Mod X.sheaf) ≅
        (restrictModules X (V x)).obj ((D.toOXMod n).obj (SheafOfModules.unit _)))) :
    Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) H := by
  let := SheafOfModules.monoidalCategorySheafTensor X.sheaf
  let := SheafOfModules.monoidalCategorySheafTensor (D.factor n)
  refine isInvertibleModule_left_of_tensorObj H H' ?_
  have hcov : (Opens.grothendieckTopology X.carrier).CoversTop V :=
    (Opens.coversTop_iff _ _).mpr (IsOpenCover.mk (top_le_iff.mp fun x _ =>
      Opens.mem_iSup.mpr ⟨x, hxV x⟩))
  refine Stacks.SheafOfModules.isInvertible_of_coversTop_nonempty_iso_unit _ _ _ hcov fun x => ?_
  obtain ⟨ex⟩ := e x
  let e1 : (restrictModules X (V x)).obj ((D.toOXMod n).obj (H ⊗ H')) ≅
      (restrictModules X (V x)).obj ((D.toOXMod n).obj (SheafOfModules.unit _)) :=
    (restrictModules X (V x)).mapIso (D.tensorObjIsoToOXMod n H H').symm ≪≫ ex
  exact ⟨(D.fullyFaithfulRestrictScalarsProjOver n (V x)).preimageIso
    (overIsoOfRestrictIso (V x) e1)⟩

end Stacks.Cohomology.InvertibleDerived

end
