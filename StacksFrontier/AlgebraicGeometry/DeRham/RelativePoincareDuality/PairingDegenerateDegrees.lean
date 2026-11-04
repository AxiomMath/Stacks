module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PairingIsoCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# The relative Hodge pairings in degrees without forms

When `Ω^p_{X/S}` and `Ω^q_{X/S}` both vanish, the pairing
`Rf_*Ω^p ⊗^L Rf_*Ω^q[n] ⟶ 𝒪_S` of [Stacks, Tag 0G8I] is a pairing between zero objects, and it is
perfect. For `f` smooth of relative dimension `n` this is the case for `p < 0` and for `p > n`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfectDerivedPairing_relativeHodgePairing_of_isZero`
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi (TensorHomAdjunction)

universe u

/-- An object of the derived category of a ringed space which is a zero object is perfect. -/
theorem Stacks.Cohomology.PerfectTriangulatedSubcategory.isPerfect_of_isZero
    {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)} (hK : IsZero K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect K :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso ((isZero_zero _).iso hK)
    Stacks.Cohomology.PerfectTriangulatedSubcategory.isPerfect_zero

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `Rf_*` carries zero objects to zero objects: it is a right adjoint. -/
theorem isZero_derivedPushforward_of_isZero {K : DerivedCategory X.Modules} (hK : IsZero K) :
    IsZero ((Stacks.Duality.derivedPushforward f).obj K) := by
  rw [IsZero.iff_id_eq_zero]
  exact ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
    f.toLRSHom.toShHom).homEquiv _ _).symm.injective (hK.eq_of_tgt _ _)

/-- A zero sheaf of forms gives a zero object in degree zero. -/
theorem isZero_formsInDegreeZero {a : ℤ} (ha : IsZero (relativeDifferentialForms f a)) :
    IsZero (formsInDegreeZero f a) :=
  Functor.map_isZero _ (Functor.map_isZero _ ha)

/-- **The pairings in the degrees where both sheaves of forms vanish are perfect**: they are
pairings between zero objects. This covers the degrees `p < 0` and `p > n` of
[Stacks, Tag 0G8I] for `f` smooth of relative dimension `n`. -/
theorem isPerfectDerivedPairing_relativeHodgePairing_of_isZero (DY : DerivedTensorHomAdjunction S)
    (n p q : ℤ) (h : p + q = n)
    (t : (Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f n)⟦n⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj)
    (hp : IsZero (relativeDifferentialForms f p)) (hq : IsZero (relativeDifferentialForms f q)) :
    IsPerfectDerivedPairing DY (f.relativeHodgePairing n p q h t) := by
  have h₁ := isZero_derivedPushforward_of_isZero f (isZero_formsInDegreeZero f hp)
  have h₂ := isZero_derivedPushforward_of_isZero f
    (Functor.map_isZero (shiftFunctor _ n) (isZero_formsInDegreeZero f hq))
  refine ⟨Stacks.Cohomology.PerfectTriangulatedSubcategory.isPerfect_of_isZero h₁,
    Stacks.Cohomology.PerfectTriangulatedSubcategory.isPerfect_of_isZero h₂, ?_⟩
  · exact isIso_of_source_target_iso_zero _ h₁.isoZero
      (TensorHomAdjunction.isZero_obj_obj_of_isZero DY h₂ _).isoZero

end AlgebraicGeometry.Scheme.Hom
