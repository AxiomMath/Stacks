module

public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.SmoothAtAttaching
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.SmoothRationalPoint

/-!
# A rational tail is geometrically integral over its field of global functions

Let `X` be a proper one-dimensional nodal curve over a field `k` with `H⁰(X, 𝒪_X) = k`, and let
`C ⊆ X` be a rational tail meeting the closure of its complement in the point `x`. The field
`k' = H⁰(C, 𝒪_C)` maps isomorphically onto `κ(x)`, so `x` is a `k'`-rational point of `C`. The
point `x` is a node of `X`, so the local ring of `X` there is reduced with two minimal primes and
delta invariant one, and the local ring of `C` at `x`, its quotient by the minimal prime
belonging to `C`, is a discrete valuation ring. A rational point with regular local ring is a
smooth point, so `C` is geometrically integral over `k'`. Moreover `k'/k` is finite separable,
being the residue field extension at a node.

These are the two facts about `C` that the decomposition of `C_K` for a field extension `K/k`
uses: `C_K = C ×_{k'} Spec(k' ⊗_k K)` and `k' ⊗_k K` is a finite product of fields.

## Main results

* `Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail`: a rational tail is
  one-dimensional.
* `Stacks.Curves.isRegularLocalRing_stalk_attachingPoint`: the local ring of a rational tail at
  its attaching point is regular.
* `Stacks.Curves.geometricallyIntegral_toSpecΓ_of_isRationalTail`: a rational tail is
  geometrically integral over its field of global functions.
* `Stacks.Curves.isSeparable_globalSections_of_isRationalTail`: that field is a separable
  extension of `k`.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0E3I](https://stacks.math.columbia.edu/tag/0E3I)
* [Stacks Project, Tag 0CDW](https://stacks.math.columbia.edu/tag/0CDW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **A rational tail is one-dimensional.** Its support is an irreducible component of the
equidimensional one-dimensional curve `X`. -/
theorem topologicalKrullDim_subscheme_eq_one_of_isRationalTail
    (hdim : topologicalKrullDim X = 1) (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    topologicalKrullDim C.subscheme = 1 := by
  have hCrange : (Set.range C.subschemeι : Set X) = (C.support : Set X) := C.range_subschemeι
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (C.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hCrange)).isHomeomorph).trans
    (topologicalKrullDim_irreducibleComponent_eq_one (X ↘ Spec (.of k))
      (equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim)
      hdim (C.support : Set X) hC.support_mem_irreducibleComponents)

omit [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] in
/-- **The local ring of a rational tail at its attaching point is the quotient of the local ring
of `X` by the minimal prime of the tail.** The stalk map of the closed immersion is surjective
with kernel the stalk of the ideal sheaf. -/
theorem nonempty_ringEquiv_stalk_attachingPoint {C : X.IdealSheafData}
    (hC : IsRationalTail k X C) :
    Nonempty ((X.presheaf.stalk (C.subschemeι hC.attachingPoint) ⧸
        IdealSheafData.stalk C (C.subschemeι hC.attachingPoint)) ≃+*
      C.subscheme.presheaf.stalk hC.attachingPoint) := by
  have hker : RingHom.ker (C.subschemeι.stalkMap hC.attachingPoint).hom =
      IdealSheafData.stalk C (C.subschemeι hC.attachingPoint) := by
    rw [← IdealSheafData.stalk_ker_of_isClosedImmersion C.subschemeι hC.attachingPoint,
      Scheme.IdealSheafData.ker_subschemeι]
  rw [← hker]
  exact ⟨RingHom.quotientKerEquivOfSurjective (C.subschemeι.stalkMap_surjective _)⟩

/-- **The local ring of a rational tail at its attaching point is one-dimensional.** It is the
quotient of the local ring of `X` by a minimal prime which is not the maximal ideal, since that
local ring has two minimal primes, so it is not a field; and it is at most one-dimensional as
the tail is. -/
theorem ringKrullDim_stalk_attachingPoint_eq_one
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    ringKrullDim (C.subscheme.presheaf.stalk hC.attachingPoint) = 1 := by
  have hmin := stalk_mem_minimalPrimes_of_isRationalTail hC
  have hne : IdealSheafData.stalk C (C.subschemeι hC.attachingPoint) ≠
      IsLocalRing.maximalIdeal _ :=
    ne_maximalIdeal_of_mem_minimalPrimes_of_one_lt_encard hmin (by
      rw [encard_minimalPrimes_stalk_attachingPoint_eq_two k X hdim hnodal C hC]
      decide)
  have : (IdealSheafData.stalk C (C.subschemeι hC.attachingPoint)).IsPrime := hmin.1.1
  obtain ⟨e⟩ := nonempty_ringEquiv_stalk_attachingPoint k X hC
  have hone : 1 ≤ ringKrullDim (X.presheaf.stalk (C.subschemeι hC.attachingPoint) ⧸
      IdealSheafData.stalk C (C.subschemeι hC.attachingPoint)) := by
    have hnk : ¬ Ring.KrullDimLE 0 (X.presheaf.stalk (C.subschemeι hC.attachingPoint) ⧸
        IdealSheafData.stalk C (C.subschemeι hC.attachingPoint)) := fun _ =>
      hne (IsLocalRing.eq_maximalIdeal ((Ideal.Quotient.maximal_ideal_iff_isField_quotient
        _).mpr Ring.KrullDimLE.isField_of_isDomain))
    rw [Ring.krullDimLE_iff] at hnk
    exact (WithBot.one_le_iff_pos _).2 (lt_of_not_ge hnk)
  rw [ringKrullDim_eq_of_ringEquiv e] at hone
  refine le_antisymm ?_ hone
  rw [← topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C hC]
  exact ringKrullDim_stalk_le_topologicalKrullDim _

/-- **The local ring of a rational tail at its attaching point is regular.** The local ring of
`X` at the attaching point is reduced with delta invariant one and exactly two minimal primes,
and the quotient of such a ring by a minimal prime is a discrete valuation ring once it is
one-dimensional (`Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one`);
the local ring of the tail is that quotient. -/
theorem isRegularLocalRing_stalk_attachingPoint
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    IsRegularLocalRing (C.subscheme.presheaf.stalk hC.attachingPoint) := by
  let y := C.subschemeι hC.attachingPoint
  obtain ⟨hred, hδ, -⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hdim y (isNode_attachingPoint k X hdim hnodal C hC)
  have htwo := encard_minimalPrimes_stalk_attachingPoint_eq_two k X hdim hnodal C hC
  have := hred
  have : IsNagataRing (X.presheaf.stalk y) :=
    isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) _
  have hmin := stalk_mem_minimalPrimes_of_isRationalTail hC
  have : (IdealSheafData.stalk C y).IsPrime := hmin.1.1
  obtain ⟨e⟩ := nonempty_ringEquiv_stalk_attachingPoint k X hC
  have hdimq : ringKrullDim (X.presheaf.stalk y ⧸ IdealSheafData.stalk C y) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact ringKrullDim_stalk_attachingPoint_eq_one k X hdim hnodal C hC
  obtain ⟨a, b, hab, hset⟩ := Set.encard_eq_two.mp htwo
  have ha : a ∈ minimalPrimes (X.presheaf.stalk y) := by
    rw [hset]
    exact Set.mem_insert _ _
  have hb : b ∈ minimalPrimes (X.presheaf.stalk y) := by
    rw [hset]
    exact Set.mem_insert_of_mem _ rfl
  have hfin : (minimalPrimes (X.presheaf.stalk y)).Finite :=
    Set.encard_ne_top_iff.mp (by rw [htwo]; decide)
  have hab' : (⟨a, ha⟩ : minimalPrimes (X.presheaf.stalk y)) ≠ ⟨b, hb⟩ :=
    fun h => hab (Subtype.ext_iff.mp h)
  obtain ⟨hdom, hdvr⟩ :=
    Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one
      (X.presheaf.stalk y) inferInstance hfin hab' hδ ⟨_, hmin⟩ hdimq
  have := hdom
  have : IsLocalRing (X.presheaf.stalk y ⧸ IdealSheafData.stalk C y) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsRegularLocalRing (X.presheaf.stalk y ⧸ IdealSheafData.stalk C y) :=
    ((isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one _ hdimq).out 3 1).mp hdvr
  exact IsRegularLocalRing.of_ringEquiv e

/-- **A rational tail is geometrically integral over its field of global functions.** The
global functions map isomorphically onto the residue field at the attaching point, where the
local ring is regular (`Stacks.Curves.isRegularLocalRing_stalk_attachingPoint`), so
`AlgebraicGeometry.geometricallyIntegral_toSpecΓ_of_isRegularLocalRing` applies. -/
theorem geometricallyIntegral_toSpecΓ_of_isRationalTail
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    letI : IsIntegral C.subscheme := hC.isIntegral
    letI : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
    GeometricallyIntegral C.subscheme.toSpecΓ := by
  have : IsIntegral C.subscheme := hC.isIntegral
  have : IsIso (C.subscheme.Γevaluation hC.attachingPoint) := hC.isIso_Γevaluation_attachingPoint
  exact geometricallyIntegral_toSpecΓ_of_isRegularLocalRing (C.subschemeι ≫ (X ↘ Spec (.of k)))
    hC.attachingPoint (isRegularLocalRing_stalk_attachingPoint k X hdim hnodal C hC)

/-- **The field of global functions of a rational tail is a separable extension of `k`.** It is
isomorphic over `k` to the residue field of `C` at the attaching point, which the closed
immersion identifies with the residue field of `X` there, and that is a finite separable
extension of `k` because the attaching point is a node
(`Stacks.Curves.isFiniteSeparable_residueField_attachingPoint`). -/
theorem isSeparable_globalSections_of_isRationalTail
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    letI : IsIntegral C.subscheme := hC.isIntegral
    letI : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
    letI : Algebra k Γ(C.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    Algebra.IsSeparable k Γ(C.subscheme, ⊤) := by
  have : IsIntegral C.subscheme := hC.isIntegral
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  let algC : Algebra k Γ(C.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  let x := hC.attachingPoint
  let y := C.subschemeι x
  obtain ⟨hfin, hsep⟩ := isFiniteSeparable_residueField_attachingPoint k X hdim hnodal C hC
  let algX : Algebra k (X.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫ X.Γevaluation y).hom.toAlgebra
  have : Module.Finite k (X.residueField y) := hfin
  have : Algebra.IsSeparableExtension k (X.residueField y) := hsep
  have : Algebra.IsAlgebraic k (X.residueField y) := Algebra.IsAlgebraic.of_finite k _
  have : Algebra.IsSeparable k (X.residueField y) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.isSeparable_of_isSeparableExtension_of_isAlgebraic
      k _
  have : IsIso (C.subscheme.Γevaluation x) := hC.isIso_Γevaluation_attachingPoint
  let algCx : Algebra k (C.subscheme.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop ≫
      C.subscheme.Γevaluation x).hom.toAlgebra
  let eψ : X.residueField y ≃ₐ[k] C.subscheme.residueField x :=
    AlgEquiv.ofBijective
      { toRingHom := (C.subschemeι.residueFieldMap x).hom
        commutes' := fun r => by
          simp only [algX, algCx, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp,
            RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop]
          exact Scheme.Γevaluation_naturality_apply C.subschemeι x _ }
      (bijective_residueFieldMap_of_isClosedImmersion C.subschemeι x)
  have : Algebra.IsSeparable k (C.subscheme.residueField x) :=
    Algebra.IsSeparable.of_algHom k _ eψ.symm.toAlgHom
  let eΓ : Γ(C.subscheme, ⊤) →ₐ[k] C.subscheme.residueField x :=
    { toRingHom := (C.subscheme.Γevaluation x).hom
      commutes' := fun r => rfl }
  exact Algebra.IsSeparable.of_algHom k _ eΓ

end Stacks.Curves

end
