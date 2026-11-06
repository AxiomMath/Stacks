module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniChartGenericFibre

/-!
# The chart ring of the universal divisor and its reduction

The ring of `H_univ` over a trivializing affine chart is `Γ(U, ⊤)[xⱼ]/(∑ⱼ xⱼ fⱼ)`
(`Stacks.Bertini.FamilyDivisors.chartSubschemeΓEquiv`), and the reduced chart ring
`Stacks.Bertini.FamilyDivisors.reducedChartDivisorRing` is `(Γ(U, ⊤) ⧸ √0)[xⱼ]/(∑ⱼ xⱼ f̄ⱼ)`.
Reducing the coefficients maps the first onto the second with kernel contained in the nilradical,
so the two rings have the same reduction; when the second is reduced, it is that reduction.

## Main results

* `MvPolynomial.ker_map_quotientMk_le_nilradical`: the kernel of reducing the coefficients
  consists of nilpotents.
* `MvPolynomial.ker_quotientMapQuotientMk_le_nilradical` and
  `MvPolynomial.quotientMapQuotientMk_surjective`: the induced map of quotients is surjective with
  kernel in the nilradical.
* `Stacks.Bertini.FamilyDivisors.exists_surjective_ker_le_nilradical_reducedChartDivisorRing`:
  the reduced chart ring of the universal divisor is the reduction of its chart ring.
* `Stacks.Bertini.FamilyDivisors.ker_reducedChartDivisorReduction` and
  `Stacks.Bertini.FamilyDivisors.nilradicalQuotEquivReducedChartDivisorRing`: once the target is
  itself reduced the kernel is *exactly* the nilradical, so the comparison map is the
  isomorphism of the reduction of the chart ring with the reduced one.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

/-- **The kernel of reducing the coefficients of a polynomial consists of nilpotents**, when the
ideal killed in the base does. -/
theorem MvPolynomial.ker_map_quotientMk_le_nilradical {A : Type*} [CommRing A] {σ : Type*}
    {I : Ideal A} (hI : I ≤ nilradical A) :
    RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) :
        MvPolynomial σ A →+* MvPolynomial σ (A ⧸ I)) ≤
      nilradical (MvPolynomial σ A) := by
  intro p hp
  rw [mem_nilradical, MvPolynomial.isNilpotent_iff]
  intro i
  refine mem_nilradical.mp (hI (Ideal.Quotient.eq_zero_iff_mem.mp ?_))
  rw [← MvPolynomial.coeff_map, RingHom.mem_ker.mp hp, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply]

/-- **Reducing the coefficients of a quotient of a polynomial ring.** -/
def MvPolynomial.quotientMapQuotientMk {A : Type*} [CommRing A] {σ : Type*} (I : Ideal A)
    (J : Ideal (MvPolynomial σ A)) :
    (MvPolynomial σ A ⧸ J) →+*
      (MvPolynomial σ (A ⧸ I) ⧸ J.map (MvPolynomial.map (Ideal.Quotient.mk I))) :=
  Ideal.quotientMap _ (MvPolynomial.map (Ideal.Quotient.mk I)) Ideal.le_comap_map

/-- Reducing the coefficients of a quotient of a polynomial ring is surjective. -/
theorem MvPolynomial.quotientMapQuotientMk_surjective {A : Type*} [CommRing A] {σ : Type*}
    (I : Ideal A) (J : Ideal (MvPolynomial σ A)) :
    Function.Surjective (MvPolynomial.quotientMapQuotientMk I J) := by
  intro z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective q
  exact ⟨Ideal.Quotient.mk J p, rfl⟩

/-- **Reducing the coefficients of a quotient of a polynomial ring has nilpotent kernel**, when
the ideal killed in the base consists of nilpotents. -/
theorem MvPolynomial.ker_quotientMapQuotientMk_le_nilradical {A : Type*} [CommRing A] {σ : Type*}
    {I : Ideal A} (hI : I ≤ nilradical A) (J : Ideal (MvPolynomial σ A)) :
    RingHom.ker (MvPolynomial.quotientMapQuotientMk I J) ≤ nilradical (MvPolynomial σ A ⧸ J) := by
  intro z hz
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [RingHom.mem_ker, MvPolynomial.quotientMapQuotientMk, Ideal.quotientMap_mk,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap.symm,
    Ideal.comap_map_of_surjective _
      (MvPolynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
  rw [mem_nilradical, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
  exact (mem_nilradical.mp (MvPolynomial.ker_map_quotientMk_le_nilradical hI hb)).map
    (Ideal.Quotient.mk J)

namespace Stacks.Bertini.FamilyDivisors

variable {D : FamilyDivisors.{u, v}}

/-- The chart ring of the universal divisor over a chart, as
`Stacks.Bertini.FamilyDivisors.chartSubschemeΓEquiv` presents the ring of `H_univ` there. -/
abbrev chartDivisorRing (c : D.Chart) : Type u :=
  MvPolynomial D.basisIndex Γ(c.U.toScheme, ⊤) ⧸
    Ideal.span {Algebra.universalLinearForm (D.chartEquationIndex c.U c.triv)}

/-- Reducing the coefficients carries the local equation of the universal divisor to the local
equation over the reduced chart ring. -/
theorem map_span_universalLinearForm_chartEquationIndex (c : D.Chart) :
    Ideal.map (MvPolynomial.map (Ideal.Quotient.mk (nilradical Γ(c.U.toScheme, ⊤))))
        (Ideal.span {Algebra.universalLinearForm (D.chartEquationIndex c.U c.triv)}) =
      Ideal.span {Algebra.universalLinearForm (reducedChartEquation c)} := by
  rw [Ideal.map_span, Set.image_singleton, Algebra.map_universalLinearForm]
  rfl

/-- **Reducing the coefficients of the chart ring of the universal divisor**: the comparison of
the ring `Stacks.Bertini.FamilyDivisors.chartDivisorRing` of `H_univ` over a chart with the ring
`Stacks.Bertini.FamilyDivisors.reducedChartDivisorRing` over the reduced chart ring. -/
def reducedChartDivisorReduction (c : D.Chart) :
    chartDivisorRing c →+* reducedChartDivisorRing c :=
  (Ideal.quotEquivOfEq (map_span_universalLinearForm_chartEquationIndex c)).toRingHom.comp
    (MvPolynomial.quotientMapQuotientMk _ _)

/-- `reducedChartDivisorReduction` reduces the coefficients of a representative. -/
@[simp]
theorem reducedChartDivisorReduction_mk (c : D.Chart)
    (p : MvPolynomial D.basisIndex Γ(c.U.toScheme, ⊤)) :
    reducedChartDivisorReduction c (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _
        (MvPolynomial.map (Ideal.Quotient.mk (nilradical Γ(c.U.toScheme, ⊤))) p) :=
  rfl

/-- The comparison of the chart ring with the reduced chart ring is surjective. -/
theorem surjective_reducedChartDivisorReduction (c : D.Chart) :
    Function.Surjective (reducedChartDivisorReduction c) :=
  (Ideal.quotEquivOfEq
      (map_span_universalLinearForm_chartEquationIndex c)).surjective.comp
    (MvPolynomial.quotientMapQuotientMk_surjective _ _)

/-- The kernel of the comparison of the chart ring with the reduced chart ring consists of
nilpotents. -/
theorem ker_reducedChartDivisorReduction_le (c : D.Chart) :
    RingHom.ker (reducedChartDivisorReduction c) ≤ nilradical (chartDivisorRing c) :=
  (RingHom.ker_equiv_comp _ _).le.trans
    (MvPolynomial.ker_quotientMapQuotientMk_le_nilradical le_rfl _)

/-- **The reduced chart ring of the universal divisor is the reduction of its chart ring**: there
is a surjection from the chart ring onto the reduced chart ring with kernel inside the
nilradical. -/
@[stacks 0G4F "the reduced chart ring of the universal divisor as the reduction of its chart ring"]
theorem exists_surjective_ker_le_nilradical_reducedChartDivisorRing (c : D.Chart) :
    ∃ Φ : chartDivisorRing c →+* reducedChartDivisorRing c,
      Function.Surjective Φ ∧ RingHom.ker Φ ≤ nilradical (chartDivisorRing c) :=
  ⟨reducedChartDivisorReduction c, surjective_reducedChartDivisorReduction c,
    ker_reducedChartDivisorReduction_le c⟩

/-- When the reduced chart ring is reduced, the kernel of the surjection
`Stacks.Bertini.FamilyDivisors.reducedChartDivisorReduction` is exactly the nilradical of the
chart ring. -/
theorem ker_reducedChartDivisorReduction (c : D.Chart)
    [IsReduced (reducedChartDivisorRing c)] :
    RingHom.ker (reducedChartDivisorReduction c) = nilradical (chartDivisorRing c) := by
  refine le_antisymm (ker_reducedChartDivisorReduction_le c) fun z hz ↦ ?_
  rw [RingHom.mem_ker]
  exact ((mem_nilradical.mp hz).map (reducedChartDivisorReduction c)).eq_zero

/-- **The reduction of the chart ring of the universal divisor, as a ring**: the quotient of
`Γ(H_univ, chart)` by its nilradical is the ring `A[xⱼ]/(∑ⱼ xⱼ f̄ⱼ)` over the reduced chart
ring. -/
def nilradicalQuotEquivReducedChartDivisorRing (c : D.Chart)
    [IsReduced (reducedChartDivisorRing c)] :
    (chartDivisorRing c ⧸ nilradical (chartDivisorRing c)) ≃+* reducedChartDivisorRing c :=
  (Ideal.quotEquivOfEq (ker_reducedChartDivisorReduction c).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_reducedChartDivisorReduction c))

/-- `nilradicalQuotEquivReducedChartDivisorRing` sends the class of `z` to its image under
`reducedChartDivisorReduction`. -/
@[simp]
theorem nilradicalQuotEquivReducedChartDivisorRing_mk (c : D.Chart)
    [IsReduced (reducedChartDivisorRing c)] (z : chartDivisorRing c) :
    nilradicalQuotEquivReducedChartDivisorRing c (Ideal.Quotient.mk _ z) =
      reducedChartDivisorReduction c z :=
  rfl

end Stacks.Bertini.FamilyDivisors

end
