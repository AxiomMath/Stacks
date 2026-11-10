module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldNilradical
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniUniversalFamilyDominance

/-!
# The residue field of the universal divisor at its generic point

Let `H_univ` be the universal divisor of a family of divisors and `ξ` its generic point. The
residue field `κ(ξ)` is a fraction field of the chart ring
`Stacks.Bertini.FamilyDivisors.reducedChartDivisorRing` of the universal divisor over the reduced
chart ring, with structure map sending the reduction of a section over the chart to its value at
`ξ`.

## Main results

* `Stacks.Bertini.FamilyDivisors.nonempty_chartDivisorOpen`: the part
  `Stacks.Bertini.FamilyDivisors.chartDivisorOpen` of `H_univ` over a chart is nonempty when the
  chart ring of the universal divisor is nontrivial.
* `Stacks.Bertini.FamilyDivisors.genericPoint_mem_chartDivisorOpen`: if moreover `H_univ` is
  irreducible, that part contains `ξ`.
* `Stacks.Bertini.FamilyDivisors.isFractionRing_residueField_chartDivisorRing`: `κ(ξ)` is a
  fraction field of the chart ring of the universal divisor over a given chart on which that ring
  is a domain.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.exists_chart_isFractionRing_residueField`: under the
  hypotheses of the family, there is a chart over which `κ(ξ)` is a fraction field of the chart
  ring of the universal divisor.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, v}) (c : D.Chart)

/-- The part of `H_univ` over a chart is nonempty when the chart ring of the universal divisor
over the reduced chart ring is nontrivial. -/
theorem nonempty_chartDivisorOpen [Nontrivial (reducedChartDivisorRing c)] :
    Nonempty (D.chartDivisorOpen c.U).toScheme := by
  have hnt : Nontrivial (chartDivisorRing c) :=
    (surjective_reducedChartDivisorReduction c).nontrivial
  obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
  have : Nontrivial Γ(D.universalDivisorScheme, D.chartDivisorOpen c.U) :=
    ⟨(D.chartSubschemeΓEquiv c.U c.triv).symm x, (D.chartSubschemeΓEquiv c.U c.triv).symm y,
      fun hc ↦ hxy ((D.chartSubschemeΓEquiv c.U c.triv).symm.injective hc)⟩
  exact Nonempty.map
    (Scheme.homeoOfIso (D.isAffineOpen_chartDivisorOpen c.U).isoSpec).symm inferInstance

/-- If `H_univ` is irreducible, its generic point lies in the part of `H_univ` over every chart
on which the chart ring of the universal divisor is nontrivial. -/
theorem genericPoint_mem_chartDivisorOpen [IrreducibleSpace D.universalDivisorScheme]
    [Nontrivial (reducedChartDivisorRing c)] :
    genericPoint D.universalDivisorScheme ∈ D.chartDivisorOpen c.U :=
  ((genericPoint_spec D.universalDivisorScheme).mem_open_set_iff
      (D.chartDivisorOpen c.U).isOpen).mpr
    (by simpa using D.nonempty_chartDivisorOpen c)

variable {D}

/-- If `H_univ` is irreducible and the chart ring of the universal divisor over the chart `c` is
a domain, the residue field of `H_univ` at its generic point is a fraction field of that ring, with
structure map sending the reduction of a section `a` over the chart to the value of `a` at the
generic point. -/
theorem isFractionRing_residueField_chartDivisorRing (c : D.Chart)
    [IrreducibleSpace D.universalDivisorScheme] [IsDomain (reducedChartDivisorRing c)] :
    ∃ _ : Algebra (reducedChartDivisorRing c)
        (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme)),
      IsFractionRing (reducedChartDivisorRing c)
          (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme)) ∧
        ∀ a : Γ(D.universalDivisorScheme, D.chartDivisorOpen c.U),
          algebraMap (reducedChartDivisorRing c)
              (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))
              (reducedChartDivisorReduction c (D.chartSubschemeΓEquiv c.U c.triv a)) =
            D.universalDivisorScheme.evaluation (D.chartDivisorOpen c.U)
              (genericPoint D.universalDivisorScheme)
              (D.genericPoint_mem_chartDivisorOpen c) a := by
  have : IsReduced (reducedChartDivisorRing c) := isReduced_of_noZeroDivisors
  obtain ⟨_, hfr, hcomp⟩ :=
    (D.isAffineOpen_chartDivisorOpen c.U).exists_isFractionRing_residueField_genericPoint
      (D.genericPoint_mem_chartDivisorOpen c)
  let e : (Γ(D.universalDivisorScheme, D.chartDivisorOpen c.U) ⧸
        nilradical Γ(D.universalDivisorScheme, D.chartDivisorOpen c.U)) ≃+*
      reducedChartDivisorRing c :=
    (D.chartSubschemeΓEquiv c.U c.triv).quotientNilradical.trans
      (nilradicalQuotEquivReducedChartDivisorRing c)
  refine ⟨_, (IsFractionRing.isFractionRing_iff_of_base_ringEquiv
    (S := D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme)) e).mp
      hfr, fun a ↦ ?_⟩
  change algebraMap (Γ(D.universalDivisorScheme, D.chartDivisorOpen c.U) ⧸
      nilradical Γ(D.universalDivisorScheme, D.chartDivisorOpen c.U)) _
    (e.symm (e (Ideal.Quotient.mk _ a))) = _
  rw [e.symm_apply_apply]
  exact hcomp a

namespace Hypotheses

variable (h : D.Hypotheses)

include h

/-- Under the hypotheses of the family, `H_univ` is irreducible and there is a chart `c`, whose
part of `H_univ` contains the generic point, such that the residue field of `H_univ` at its
generic point is a fraction field of the chart ring of the universal divisor over `c`, with
structure map sending the reduction of a section `a` over the chart to the value of `a` at the
generic point. -/
@[stacks 0G4F "the residue field of the universal divisor at its generic point"]
theorem exists_chart_isFractionRing_residueField :
    haveI := h.irreducibleSpace_universalDivisorScheme
    ∃ (c : D.Chart) (hξ : genericPoint D.universalDivisorScheme ∈ D.chartDivisorOpen c.U),
      ∃ _ : Algebra (reducedChartDivisorRing c)
          (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme)),
        IsFractionRing (reducedChartDivisorRing c)
            (D.universalDivisorScheme.residueField
              (genericPoint D.universalDivisorScheme)) ∧
          ∀ a : Γ(D.universalDivisorScheme, D.chartDivisorOpen c.U),
            algebraMap (reducedChartDivisorRing c)
                (D.universalDivisorScheme.residueField (genericPoint D.universalDivisorScheme))
                (reducedChartDivisorReduction c (D.chartSubschemeΓEquiv c.U c.triv a)) =
              D.universalDivisorScheme.evaluation (D.chartDivisorOpen c.U)
                (genericPoint D.universalDivisorScheme) hξ a := by
  have := h.irreducibleSpace_universalDivisorScheme
  obtain ⟨c, m, b, b', hbb', hb'b, hrest⟩ := h.exists_chart_substitution
  let := reducedChartAlgebra c.U
  obtain ⟨g, w, hg, hw, hcodim⟩ := hrest
  have := h.isDomain_reducedChartRing c
  have := h.isDomain_reducedChartDivisorRing c b b' hbb' hb'b g w hg hw
  exact ⟨c, D.genericPoint_mem_chartDivisorOpen c, isFractionRing_residueField_chartDivisorRing c⟩

end Hypotheses

end Stacks.Bertini.FamilyDivisors

end
