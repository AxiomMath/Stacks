module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.ScalarTwist
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.SpecFieldFiniteSums

/-!
# Perfect complexes on the spectrum of a field concentrated in degree zero

Let `k` be a field. A perfect object `V` of `D(𝒪_{Spec k})` concentrated in degree zero whose
cohomology sheaf `H^0(V)` is quasi-coherent of finite type is a finite direct sum of copies of
`𝒪_{Spec k}[0]` in `D_perf(𝒪_{Spec k})`: this is
`AlgebraicGeometry.exists_iso_biproduct_singleFunctor_unit_of_isGE_of_isLE` read in the full
subcategory of perfect objects, whose inclusion is fully faithful and preserves finite biproducts.
It produces the decompositions `V ≅ ⨁ 𝒪_{Spec k}[0]` that
`AlgebraicGeometry.twistApply_comm` takes as input ([Stacks, Section 0G07]).

## Main results

* `AlgebraicGeometry.exists_iso_biproduct_perfectUnitSpecField`: the decomposition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k]

/-- **A perfect complex on `Spec k` concentrated in degree zero, with `H^0` quasi-coherent of
finite type, is a finite direct sum of copies of `𝒪_{Spec k}[0]` in `D_perf(𝒪_{Spec k})`.** -/
theorem exists_iso_biproduct_perfectUnitSpecField (V : PerfectDerivedCategory (Spec (.of k)))
    [V.obj.IsGE 0] [V.obj.IsLE 0]
    [((DerivedCategory.homologyFunctor (Spec (.of k)).Modules 0).obj V.obj).IsQuasicoherent]
    [((DerivedCategory.homologyFunctor (Spec (.of k)).Modules 0).obj V.obj).IsFiniteType] :
    ∃ n : ℕ, Nonempty (V ≅ ⨁ fun _ : Fin n => (perfectUnitSpecField (k := k))) := by
  obtain ⟨n, ⟨e⟩⟩ := exists_iso_biproduct_singleFunctor_unit_of_isGE_of_isLE V.obj 0
  exact ⟨n, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
    (e ≪≫ ((ObjectProperty.ι _).mapBiproduct fun _ : Fin n => perfectUnitSpecField (k := k)).symm)⟩⟩

end AlgebraicGeometry

end
