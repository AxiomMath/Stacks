module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniAffineSpaceChart
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniChartFunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember

/-!
# The function field of the parameter space of a Bertini situation

In the standing situation of the Bertini theorems the parameter space over the base field is the
affine space `𝔸^r_k = 𝔸(ι; Spec k)` on the basis index set `ι` of the linear system. It is the
spectrum of the polynomial ring `k[xᵢ : i ∈ ι]`, hence integral, and its function field — the
residue field `κ(η)` at its generic point `η` — is a fraction field of that polynomial ring,
generated over `k` by the images of the coordinates: `κ(η) = k(x₁, …, x_r)`.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.parameterBaseΓEquiv` identifies `k[xᵢ : i ∈ ι]` with the ring of
  global functions of `𝔸^r_k`.
* `Stacks.Bertini.FamilyDivisors.parameterBaseFunctionFieldAlgebra` is the resulting algebra
  structure of `κ(η)` over `k[xᵢ]`, and
  `Stacks.Bertini.FamilyDivisors.parameterBaseFunctionFieldBaseAlgebra` the one over `k`.

## Main results

* `Stacks.Bertini.FamilyDivisors.isIntegral_parameterBase`: `𝔸^r_k` is integral.
* `Stacks.Bertini.FamilyDivisors.isFractionRing_parameterBase`: `κ(η)` is a fraction field of
  `k[xᵢ : i ∈ ι]`.
* `Stacks.Bertini.FamilyDivisors.adjoin_range_coord_parameterBase_eq_top`: `κ(η)` is generated
  over `k` as a field by the images of the coordinates, which is the statement
  `κ(η) = k(x₁, …, x_r)`.

## References

* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, v})

/-- The parameter space over the base field is integral. -/
instance isIntegral_parameterBase : IsIntegral D.parameterBase :=
  IsIntegral.of_isIso (AffineSpace.SpecIso D.basisIndex (.of D.k)).inv

/-- The open `⊤` of the parameter space over the base field is nonempty. -/
instance nonempty_top_parameterBase : Nonempty (⊤ : D.parameterBase.Opens) :=
  ⟨⟨Classical.arbitrary _, trivial⟩⟩

/-- The ring of global functions on the parameter space over the base field is the polynomial
ring in the parameters. -/
def parameterBaseΓEquiv : MvPolynomial D.basisIndex D.k ≃+* Γ(D.parameterBase, ⊤) :=
  (MvPolynomial.mapEquiv D.basisIndex
      (Scheme.ΓSpecIso (.of D.k)).symm.commRingCatIsoToRingEquiv).trans
    (AffineSpace.ΓIso D.basisIndex (Spec (.of D.k))).symm.commRingCatIsoToRingEquiv

/-- Under `AffineSpace.ΓIso`, the identification `k[xᵢ] ≃+* Γ(𝔸^r_k, ⊤)` is the map induced on
coefficients by `Γ(Spec k, ⊤) ≅ k`. -/
private theorem ΓIso_hom_parameterBaseΓEquiv (p : MvPolynomial D.basisIndex D.k) :
    (AffineSpace.ΓIso D.basisIndex (Spec (.of D.k))).hom (D.parameterBaseΓEquiv p) =
      MvPolynomial.map ((Scheme.ΓSpecIso (.of D.k)).inv).hom p := by
  change (AffineSpace.ΓIso D.basisIndex (Spec (.of D.k))).hom
      ((AffineSpace.ΓIso D.basisIndex (Spec (.of D.k))).inv
        (MvPolynomial.map ((Scheme.ΓSpecIso (.of D.k)).inv).hom p)) = _
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

/-- The identification of `k[xᵢ]` with the functions on `𝔸^r_k` carries the variable `xᵢ` to the
`i`-th coordinate function. -/
theorem parameterBaseΓEquiv_X (i : D.basisIndex) :
    D.parameterBaseΓEquiv (MvPolynomial.X i) = AffineSpace.coord (Spec (.of D.k)) i := by
  refine (ConcreteCategory.bijective_of_isIso
    (AffineSpace.ΓIso D.basisIndex (Spec (.of D.k))).hom).1 ?_
  rw [AffineSpace.ΓIso_hom_coord, ΓIso_hom_parameterBaseΓEquiv, MvPolynomial.map_X]

/-- The identification of `k[xᵢ]` with the functions on `𝔸^r_k` carries a constant to the
corresponding function pulled back from `Spec k`. -/
theorem parameterBaseΓEquiv_C (a : D.k) :
    D.parameterBaseΓEquiv (MvPolynomial.C a) =
      (D.parameterBase ↘ Spec (.of D.k)).appTop ((Scheme.ΓSpecIso (.of D.k)).inv a) := by
  refine (ConcreteCategory.bijective_of_isIso
    (AffineSpace.ΓIso D.basisIndex (Spec (.of D.k))).hom).1 ?_
  rw [AffineSpace.ΓIso_hom_appTop, ΓIso_hom_parameterBaseΓEquiv, MvPolynomial.map_C]

/-- The algebra structure of the function field `κ(η)` of `𝔸^r_k` over the polynomial ring in the
parameters: the germ at the generic point, read through
`Stacks.Bertini.FamilyDivisors.parameterBaseΓEquiv`. -/
@[instance_reducible]
def parameterBaseFunctionFieldAlgebra :
    Algebra (MvPolynomial D.basisIndex D.k) D.parameterBase.functionField :=
  ((algebraMap Γ(D.parameterBase, ⊤) D.parameterBase.functionField).comp
    D.parameterBaseΓEquiv.toRingHom).toAlgebra

/-- The function field `κ(η)` of the parameter space `𝔸^r_k` is a fraction field of the
polynomial ring in the parameters. -/
@[stacks 0G4F "the residue field at the generic point of the parameter space"]
theorem isFractionRing_parameterBase :
    letI := D.parameterBaseFunctionFieldAlgebra
    IsFractionRing (MvPolynomial D.basisIndex D.k) D.parameterBase.functionField := by
  have := functionField_isFractionRing_of_isAffineOpen D.parameterBase ⊤ (isAffineOpen_top _)
  exact (IsFractionRing.isFractionRing_iff_of_base_ringEquiv
    (S := D.parameterBase.functionField) D.parameterBaseΓEquiv.symm).mp this

/-- The algebra structure of `κ(η)` over the base field `k`, through the constants of the
polynomial ring in the parameters. -/
@[instance_reducible]
def parameterBaseFunctionFieldBaseAlgebra : Algebra D.k D.parameterBase.functionField :=
  letI := D.parameterBaseFunctionFieldAlgebra
  (((algebraMap (MvPolynomial D.basisIndex D.k) D.parameterBase.functionField)).comp
    (MvPolynomial.C : D.k →+* MvPolynomial D.basisIndex D.k)).toAlgebra

/-- The residue field `κ(η)` at the generic point of `𝔸^r_k` is generated over `k` as a field by
the images of the coordinates. -/
@[stacks 0G4F "the generic point of the parameter space generates the residue field"]
theorem adjoin_range_coord_parameterBase_eq_top :
    letI := D.parameterBaseFunctionFieldAlgebra
    letI := D.parameterBaseFunctionFieldBaseAlgebra
    IntermediateField.adjoin D.k
      (Set.range fun i : D.basisIndex =>
        algebraMap (MvPolynomial D.basisIndex D.k) D.parameterBase.functionField
          (MvPolynomial.X i)) = ⊤ := by
  let := D.parameterBaseFunctionFieldAlgebra
  let := D.parameterBaseFunctionFieldBaseAlgebra
  have := D.isFractionRing_parameterBase
  have : IsScalarTower D.k (MvPolynomial D.basisIndex D.k) D.parameterBase.functionField :=
    .of_algebraMap_eq fun _ ↦ rfl
  exact Algebra.adjoin_range_algebraMap_X_eq_top D.k D.parameterBase.functionField

end Stacks.Bertini.FamilyDivisors

end
