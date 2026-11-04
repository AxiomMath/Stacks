module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.Polynomial.Monic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Spreading out a polynomial over the function field

Let `Y` be an integral scheme. The function field `R(Y)` is the stalk of `Y` at its generic
point, so every element of `R(Y)` is the germ of a section over some nonempty open of `Y`, and
finitely many elements are germs of sections over one nonempty open. Consequently a polynomial
with coefficients in `R(Y)` is, after shrinking to a nonempty open `U ⊆ Y`, a polynomial with
coefficients in `Γ(Y, U)`; a monic polynomial stays monic, of the same degree, because the germ
map of an integral scheme is injective.

This is the step in the fourth part of the proof of Stacks 02TT in which the monic irreducible
polynomial `P(T) ∈ R(Y)[T]` cutting out the generic fibre of a prime cycle is replaced by a
polynomial with coefficients in `Γ(V, 𝒪_Y)` for a nonempty open `V ⊆ Y`.

## Main definitions

* `Stacks.Chow.germFunctionField` — the germ at the generic point, as a ring map from the
  sections over an open containing it to the function field.

## Main results

* `Stacks.Chow.genericPoint_mem_iff_nonempty` — on an irreducible scheme, an open contains the
  generic point exactly when it is nonempty.
* `Stacks.Chow.exists_forall_germFunctionField_eq` — a finite family of elements of `R(Y)` is a
  family of germs of sections over one nonempty open.
* `Stacks.Chow.exists_opens_polynomial_map_eq` — **spreading out a polynomial**: a polynomial
  over `R(Y)` is the image of a polynomial over `Γ(Y, U)` for some nonempty open `U`.
* `Stacks.Chow.exists_opens_monic_polynomial_map_eq` — **spreading out a monic polynomial**: the
  spread-out polynomial can be taken monic of the same degree.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 01RT](https://stacks.math.columbia.edu/tag/01RT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **On an irreducible scheme an open contains the generic point exactly when it is
nonempty.** -/
@[ega "I 7.1.10" "partial"]
theorem genericPoint_mem_iff_nonempty (Y : Scheme.{u}) [IrreducibleSpace Y] (U : Y.Opens) :
    genericPoint ↥Y ∈ U ↔ (U : Set ↥Y).Nonempty := by
  refine ⟨fun h => ⟨_, h⟩, fun hne => ?_⟩
  obtain ⟨y, hy⟩ := hne
  by_contra h
  have hc : closure ({genericPoint ↥Y} : Set ↥Y) ⊆ ((U : Set ↥Y))ᶜ :=
    closure_minimal (Set.singleton_subset_iff.2 h) U.isOpen.isClosed_compl
  have hg : closure ({genericPoint ↥Y} : Set ↥Y) = Set.univ := genericPoint_spec ↥Y
  rw [hg] at hc
  exact hc (Set.mem_univ y) hy

/-- The germ at the generic point of an irreducible scheme, as a ring map from the sections over
an open containing the generic point into the function field. -/
def germFunctionField (Y : Scheme.{u}) [IrreducibleSpace Y] {U : Y.Opens}
    (hU : genericPoint ↥Y ∈ U) : Γ(Y, U) ⟶ Y.functionField :=
  Y.presheaf.germ U (genericPoint ↥Y) hU

/-- `Stacks.Chow.germFunctionField` is Mathlib's `AlgebraicGeometry.Scheme.germToFunctionField`,
whose hypothesis that the open be nonempty is here the equivalent one that it contain the generic
point. -/
theorem germFunctionField_eq_germToFunctionField (Y : Scheme.{u}) [IrreducibleSpace Y]
    {U : Y.Opens} (hU : genericPoint ↥Y ∈ U) :
    germFunctionField Y hU =
      @Scheme.germToFunctionField Y _ U ⟨⟨genericPoint ↥Y, hU⟩⟩ :=
  rfl

/-- **The germ at the generic point of an integral scheme is injective.** -/
theorem germFunctionField_injective (Y : Scheme.{u}) [IsIntegral Y] {U : Y.Opens}
    (hU : genericPoint ↥Y ∈ U) :
    Function.Injective (germFunctionField Y hU).hom :=
  @Scheme.germToFunctionField_injective Y _ U ⟨⟨genericPoint ↥Y, hU⟩⟩

/-! ### Spreading out finitely many elements of the function field -/

/-- **A finite family of elements of the function field consists of germs of sections over a
single nonempty open.** The function field is the stalk at the generic point, so each element is
the germ of a section over some open containing the generic point; intersecting finitely many
such opens leaves an open which still contains it. -/
theorem exists_forall_germFunctionField_eq (Y : Scheme.{u}) [IrreducibleSpace Y] {m : ℕ}
    (c : Fin m → ↑Y.functionField) :
    ∃ (U : Y.Opens) (hU : genericPoint ↥Y ∈ U) (s : Fin m → ↑Γ(Y, U)),
      ∀ i, (germFunctionField Y hU).hom (s i) = c i := by
  induction m with
  | zero => exact ⟨⊤, trivial, Fin.elim0, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨U, hU, s, hs⟩ := ih (fun i => c i.castSucc)
    obtain ⟨V, hV, t, ht⟩ :=
      Y.presheaf.germ_exist (x := genericPoint ↥Y) (c (Fin.last m))
    refine ⟨U ⊓ V, ⟨hU, hV⟩,
      Fin.snoc (fun i => (Y.presheaf.map (homOfLE inf_le_left).op).hom (s i))
        ((Y.presheaf.map (homOfLE inf_le_right).op).hom t), ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_)
    · rw [Fin.snoc_last]
      exact (Y.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V))
        (genericPoint ↥Y) ⟨hU, hV⟩ t).trans ht
    · rw [Fin.snoc_castSucc]
      exact (Y.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U))
        (genericPoint ↥Y) ⟨hU, hV⟩ (s i)).trans (hs i)

/-! ### Spreading out a polynomial -/

/-- **Spreading out a polynomial over the function field.** A polynomial with coefficients in
`R(Y)` is the image of a polynomial with coefficients in the sections over some nonempty open of
`Y` — here, over an open containing the generic point, which by
`Stacks.Chow.genericPoint_mem_iff_nonempty` is the same thing. -/
theorem exists_opens_polynomial_map_eq (Y : Scheme.{u}) [IrreducibleSpace Y]
    (p : Polynomial ↑Y.functionField) :
    ∃ (U : Y.Opens) (hU : genericPoint ↥Y ∈ U) (q : Polynomial ↑Γ(Y, U)),
      q.map (germFunctionField Y hU).hom = p := by
  obtain ⟨U, hU, s, hs⟩ := exists_forall_germFunctionField_eq Y
    (fun i : Fin (p.natDegree + 1) => p.coeff i)
  refine ⟨U, hU, ∑ i : Fin (p.natDegree + 1), Polynomial.C (s i) * Polynomial.X ^ (i : ℕ), ?_⟩
  calc (∑ i : Fin (p.natDegree + 1), Polynomial.C (s i) * Polynomial.X ^ (i : ℕ)).map
          (germFunctionField Y hU).hom
      = ∑ i : Fin (p.natDegree + 1), Polynomial.C (p.coeff i) * Polynomial.X ^ (i : ℕ) := by
        rw [Polynomial.map_sum]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hs i]
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.C (p.coeff i) * Polynomial.X ^ i :=
        Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (p.coeff i) * Polynomial.X ^ i) _
    _ = p := p.as_sum_range_C_mul_X_pow.symm

/-- **Spreading out a monic polynomial over the function field.** The polynomial over the
sections of a nonempty open can be taken monic of the same degree: the germ map of an integral
scheme is injective, so it neither lowers the degree nor moves the leading coefficient away
from `1`. -/
theorem exists_opens_monic_polynomial_map_eq (Y : Scheme.{u}) [IsIntegral Y]
    {p : Polynomial ↑Y.functionField} (hp : p.Monic) :
    ∃ (U : Y.Opens) (hU : genericPoint ↥Y ∈ U) (q : Polynomial ↑Γ(Y, U)),
      q.Monic ∧ q.natDegree = p.natDegree ∧ q.map (germFunctionField Y hU).hom = p := by
  obtain ⟨U, hU, q, hq⟩ := exists_opens_polynomial_map_eq Y p
  have hinj := germFunctionField_injective Y hU
  have hdeg : q.natDegree = p.natDegree := by
    rw [← hq, Polynomial.natDegree_map_eq_of_injective hinj]
  refine ⟨U, hU, q, Polynomial.monic_of_injective hinj (hq ▸ hp), hdeg, hq⟩

end Stacks.Chow

end
