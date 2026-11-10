module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniChartAlgebra
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleLocal
public import StacksFrontier.RingTheory.GeometricallyIntegral.GenericPointIrreducible

/-!
# The fraction field of the reduced chart ring of the Bertini situation

In the Bertini situation, with the structure morphism of `X` geometrically irreducible over `k`,
let `U` be a trivializing affine chart. The chart ring `Γ(U, ⊤)`, its reduction `Γ(U, ⊤) ⧸ √0`
and the fraction field `Frac(Γ(U, ⊤) ⧸ √0)` are geometrically irreducible over `k`.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.reducedChartFractionRing`: the fraction field `Frac(Γ(U,⊤) ⧸ √0)`
  of the reduced chart ring.

## Main results

* `Stacks.Bertini.FamilyDivisors.Hypotheses.isGeometricallyIrreducible_chartRing`: the chart ring
  is geometrically irreducible over `k`.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.isGeometricallyIrreducible_reducedChartRing`: the
  reduced chart ring is geometrically irreducible over `k`.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.isGeometricallyIrreducible_reducedChartFractionRing`:
  the fraction field of the reduced chart ring is geometrically irreducible over `k`.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
* [Stacks Project, Tag 038G](https://stacks.math.columbia.edu/tag/038G)
* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

/-- Geometric irreducibility of `A` over `k` transports along an equality of the structural ring
maps. -/
theorem Algebra.isGeometricallyIrreducible_of_ringHom_eq {k A : Type u} [Field k] [CommRing A]
    {φ ψ : k →+* A} (hφψ : φ = ψ)
    (h : letI := φ.toAlgebra; Algebra.IsGeometricallyIrreducible k A) :
    letI := ψ.toAlgebra
    Algebra.IsGeometricallyIrreducible k A := by
  subst hφψ
  exact h

namespace Stacks.Bertini.FamilyDivisors

variable {D : FamilyDivisors.{u, v}}

/-- The fraction field of the reduced chart ring `Γ(U, ⊤) ⧸ √0`. -/
abbrev reducedChartFractionRing (U : D.X.Opens) : Type u :=
  FractionRing (reducedChartRing U)

/-- The structural maps `k → Γ(U, ⊤) ⧸ √0 → Frac(Γ(U, ⊤) ⧸ √0)` form a scalar tower. -/
theorem isScalarTower_reducedChartFractionRing (U : D.X.Opens) :
    letI := reducedChartAlgebra U
    IsScalarTower D.k (reducedChartRing U) (reducedChartFractionRing U) :=
  let := reducedChartAlgebra U
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

namespace Hypotheses

variable (h : D.Hypotheses)

include h

/-- The chart ring `Γ(U, ⊤)` of a trivializing affine chart is geometrically irreducible
over `k`. -/
@[stacks 0G4F "hypothesis (2) read on a trivializing affine chart"]
theorem isGeometricallyIrreducible_chartRing (c : D.Chart) :
    letI := chartAlgebra c.U
    Algebra.IsGeometricallyIrreducible D.k Γ(c.U.toScheme, ⊤) := by
  have := h.geometricallyIrreducible
  have hgi : GeometricallyIrreducible (c.U.ι ≫ D.toBase) :=
    geometricallyIrreducible_open D.k D.toBase c.U c.nonempty
  have h2 := ((geometricallyIrreducible_tfae_local D.k (c.U.ι ≫ D.toBase)).out 1 2).mp hgi
  have h3 := h2.2 ⟨⊤, isAffineOpen_top c.U.toScheme⟩
    ⟨⟨(Nonempty.some c.nonempty), trivial⟩⟩
  refine Algebra.isGeometricallyIrreducible_of_ringHom_eq ?_ h3
  change ((Scheme.ΓSpecIso (.of D.k)).inv ≫
    (c.U.ι ≫ D.toBase).appLE ⊤ ⊤ (by simp)).hom = chartRingHom c.U
  have happ : (c.U.ι ≫ D.toBase).appLE (⊤ : (Spec (.of D.k)).Opens) ⊤ (by simp) =
      (c.U.ι ≫ D.toBase).appTop := Scheme.Hom.appLE_eq_app _
  rw [happ]
  rfl

/-- The reduced chart ring `Γ(U, ⊤) ⧸ √0` of a trivializing affine chart is geometrically
irreducible over `k`. -/
@[stacks 0G4F "hypothesis (2) read on the reduced ring of a trivializing affine chart"]
theorem isGeometricallyIrreducible_reducedChartRing (c : D.Chart) :
    letI := reducedChartAlgebra c.U
    Algebra.IsGeometricallyIrreducible D.k (reducedChartRing c.U) := by
  let := chartAlgebra c.U
  refine Algebra.isGeometricallyIrreducible_of_ringHom_eq (φ := (Ideal.Quotient.mk _).comp
    (algebraMap D.k Γ(c.U.toScheme, ⊤))) rfl ?_
  exact (Algebra.isGeometricallyIrreducible_iff_quotient_of_le_nilradical D.k
    Γ(c.U.toScheme, ⊤) _ le_rfl).mp (h.isGeometricallyIrreducible_chartRing c)

/-- The fraction field of the reduced chart ring of a trivializing affine chart is geometrically
irreducible over `k`. -/
@[stacks 0G4F "hypothesis (2) as geometric irreducibility of the chart's fraction field"]
theorem isGeometricallyIrreducible_reducedChartFractionRing (c : D.Chart) :
    letI := reducedChartAlgebra c.U
    Algebra.IsGeometricallyIrreducible D.k (reducedChartFractionRing c.U) := by
  let := reducedChartAlgebra c.U
  have := h.isDomain_reducedChartRing c
  have := isScalarTower_reducedChartFractionRing (D := D) c.U
  exact (Algebra.isGeometricallyIrreducible_iff_isFractionRing D.k (reducedChartRing c.U)
    (reducedChartFractionRing c.U)).mp (h.isGeometricallyIrreducible_reducedChartRing c)

end Hypotheses

end Stacks.Bertini.FamilyDivisors

end
