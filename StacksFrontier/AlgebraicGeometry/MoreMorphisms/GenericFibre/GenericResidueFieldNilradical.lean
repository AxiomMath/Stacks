module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.ResidueField
public import StacksFrontier.RingTheory.Ideal.NilradicalQuotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The residue field at the generic point, as a fraction field of a reduced section ring

Let `X` be an irreducible scheme, `ξ` its generic point and `U` an affine open containing `ξ`.
Mathlib's `AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen` presents the function
field of `X` as a fraction field of `Γ(X, U)` — but only for an *integral* `X`, and an
irreducible scheme need not be reduced. What survives without reducedness is the statement about
the residue field: `κ(ξ)` is a fraction field of `Γ(X, U)` modulo its *nilradical*.

The missing step is that the prime of `Γ(X, U)` corresponding to `ξ` is the nilradical. A point
of `Spec R` is generic exactly when its prime is the nilradical, since the closure of a point is
the zero locus of its prime; and `ξ` corresponds to the generic point of `Spec Γ(X, U)` because
`Spec Γ(X, U) → X` is an open immersion onto `U`, which carries generic point to generic point.

This is what the generic-fibre stage of [Stacks, Tag 0G4F] needs: there `X` is the universal
divisor `H_univ`, which the tag's hypotheses make irreducible but not reduced.

## Main results

* `PrimeSpectrum.isGenericPoint_iff_asIdeal_eq_nilradical`: a point of `Spec R` is generic
  exactly when its prime is the nilradical.
* `AlgebraicGeometry.IsAffineOpen.primeIdealOf_genericPoint_eq_nilradical`: on an affine open
  containing the generic point of an irreducible scheme, the corresponding prime is the
  nilradical.
* `AlgebraicGeometry.IsAffineOpen.exists_isFractionRing_residueField_genericPoint`:
  **`κ(ξ)` is a fraction field of `Γ(X, U) ⧸ √0`**, with the structure map evaluation at `ξ`.

## Implementation notes

The algebra structure on `κ(ξ)` over `Γ(X, U) ⧸ √0` is existentially quantified and pinned by
the compatibility clause `algebraMap _ _ (mk a) = X.evaluation U ξ _ a`, rather than recorded as
an instance: it depends on `U` and on the membership `ξ ∈ U`, neither of which can be inferred.
It is obtained from `AlgebraicGeometry.IsAffineOpen.residueFieldQuotientAlgebra` by transport
along `Ideal.quotEquivOfEq`, so `IsFractionRing` transports with
`IsFractionRing.isFractionRing_iff_of_base_ringEquiv`.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

/-- **A point of `Spec R` is generic exactly when its prime is the nilradical.** The closure of
`{p}` is the zero locus of `p`, which is everything exactly when `p` consists of nilpotents; and
a prime always contains the nilradical. -/
theorem PrimeSpectrum.isGenericPoint_iff_asIdeal_eq_nilradical {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) : IsGenericPoint p Set.univ ↔ p.asIdeal = nilradical R := by
  rw [IsGenericPoint, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    PrimeSpectrum.vanishingIdeal_singleton, PrimeSpectrum.zeroLocus_eq_univ_iff,
    SetLike.coe_subset_coe]
  exact ⟨fun h => le_antisymm h (nilradical_le_prime _), fun h => h.le⟩

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens} (hU : IsAffineOpen U)
  (hx : genericPoint X ∈ U)

/-- **On an affine open containing the generic point of an irreducible scheme the corresponding
prime is the nilradical.** The open immersion `Spec Γ(X, U) → X` carries the generic point to the
generic point, and the prime corresponding to `ξ` is its unique preimage. -/
theorem primeIdealOf_genericPoint_eq_nilradical :
    (hU.primeIdealOf ⟨genericPoint X, hx⟩).asIdeal = nilradical Γ(X, U) := by
  have : Nonempty U := ⟨⟨genericPoint X, hx⟩⟩
  have : IrreducibleSpace U.toScheme := (Scheme.Hom.isOpenEmbedding U.ι).irreducibleSpace
  have : IsAffine U.toScheme := hU
  have hirr : IrreducibleSpace (Spec Γ(X, U)) :=
    (Scheme.homeoOfIso hU.isoSpec).irreducibleSpace_iff.mp ‹IrreducibleSpace U.toScheme›
  have : IrreducibleSpace (PrimeSpectrum Γ(X, U)) := by convert! hirr
  have := hirr
  have heq : hU.primeIdealOf ⟨genericPoint X, hx⟩ = genericPoint (Spec Γ(X, U)) :=
    (Scheme.Hom.isOpenEmbedding hU.fromSpec).injective
      ((hU.fromSpec_primeIdealOf ⟨genericPoint X, hx⟩).trans
        (genericPoint_eq_of_isOpenImmersion hU.fromSpec).symm)
  rw [heq]
  exact (PrimeSpectrum.isGenericPoint_iff_asIdeal_eq_nilradical _).mp (genericPoint_spec _)

include hU in
/-- **The residue field at the generic point of an irreducible scheme is a fraction field of the
reduced ring of any affine open containing it.** The structure map is evaluation at the generic
point, which pins the algebra structure.

No reducedness is assumed: this is the form of
`AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen` available for an irreducible
scheme that is not integral. -/
@[ega "I 7.1.5" "more general"]
theorem exists_isFractionRing_residueField_genericPoint :
    ∃ _ : Algebra (Γ(X, U) ⧸ nilradical Γ(X, U)) (X.residueField (genericPoint X)),
      IsFractionRing (Γ(X, U) ⧸ nilradical Γ(X, U)) (X.residueField (genericPoint X)) ∧
        ∀ a : Γ(X, U),
          algebraMap (Γ(X, U) ⧸ nilradical Γ(X, U)) (X.residueField (genericPoint X))
              (Ideal.Quotient.mk _ a) = X.evaluation U (genericPoint X) hx a := by
  let := hU.residueFieldQuotientAlgebra (genericPoint X) hx
  have hfr := hU.isFractionRing_residueField (genericPoint X) hx
  let e : (Γ(X, U) ⧸ (hU.primeIdealOf ⟨genericPoint X, hx⟩).asIdeal) ≃+*
      (Γ(X, U) ⧸ nilradical Γ(X, U)) :=
    Ideal.quotEquivOfEq (hU.primeIdealOf_genericPoint_eq_nilradical hx)
  refine ⟨((algebraMap (Γ(X, U) ⧸ (hU.primeIdealOf ⟨genericPoint X, hx⟩).asIdeal)
      (X.residueField (genericPoint X))).comp e.symm.toRingHom).toAlgebra,
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv
      (S := X.residueField (genericPoint X)) e).mp hfr, fun a => ?_⟩
  show algebraMap (Γ(X, U) ⧸ (hU.primeIdealOf ⟨genericPoint X, hx⟩).asIdeal)
      (X.residueField (genericPoint X)) (e.symm (Ideal.Quotient.mk _ a)) = _
  rw [show e.symm (Ideal.Quotient.mk (nilradical Γ(X, U)) a) = Ideal.Quotient.mk _ a from rfl]
  exact hU.algebraMap_residueFieldQuotientAlgebra_mk (genericPoint X) hx a

end AlgebraicGeometry.IsAffineOpen

end
