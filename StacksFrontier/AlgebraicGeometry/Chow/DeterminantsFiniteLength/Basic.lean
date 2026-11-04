module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The determinant of a finite length module

Let `R` be a local ring with residue field `κ`, and let `M` be an `R`-module of finite
length `l`. A sequence `e : Fin l → M` is *admissible* when the maximal ideal times each
entry lies in the span of the preceding entries. The *determinant* of `M` is the
`κ`-vector space on the admissible `l`-tuples in `M` modulo three families of relations: a
dependent entry gives zero, replacing an entry by a unit multiple of it modulo the earlier
entries scales the symbol by the residue of that unit, and two adjacent entries may be
exchanged at the cost of a sign.

## Main definitions

* `Module.FiniteLength.moduleLength` is the length of a module as a natural number.
* `Module.FiniteLength.spanBefore` is the span of the entries strictly preceding an index.
* `Module.FiniteLength.IsAdmissibleSequence` is admissibility of a finite sequence.
* `Module.FiniteLength.AdmissibleSequence` is the type of admissible tuples whose length is
  the length of the module.
* `Module.FiniteLength.DeterminantRelation` is the three families of relations.
* `Module.FiniteLength.determinant` is the resulting quotient vector space over the
  residue field.
* `Module.FiniteLength.symbol` is the class of an admissible sequence in the determinant.

## Main results

* `Module.FiniteLength.symbol_eq_zero_of_mem_spanBefore` is the dependent-entry relation.
* `Module.FiniteLength.symbol_unitChange` is the unit-change relation.
* `Module.FiniteLength.symbol_swap` is the adjacent-transposition relation.

## Implementation notes

Symbols freely generate the finitely supported module `DeterminantFree`, and `determinant`
is its quotient by `determinantRelations`, the span of the relations. Although the
construction is meaningful for every module after totalizing the length with `ENat.toNat`,
the intended applications assume that `M` has finite length, in which case `moduleLength`
is its ordinary length.

## References

* [Stacks Project, Tag 02P6](https://stacks.math.columbia.edu/tag/02P6)
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength

universe u v

/-- The ordinary natural-number value of the length of an `R`-module. -/
public abbrev moduleLength (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] : ℕ :=
  (Module.length R M).toNat

/-- The submodule spanned by the entries of `e` strictly preceding `i`. -/
public abbrev spanBefore {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] {n : ℕ} (e : Fin n → M) (i : Fin n) : Submodule R M :=
  Submodule.span R (e '' Set.Iio i)

/-- **Stacks Project, Tag 02P6.** A finite sequence in a module over a local ring is
admissible if the maximal ideal times each entry is contained in the span of the preceding
entries. -/
@[stacks 02P6 "admissible sequences"]
public def IsAdmissibleSequence {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} (e : Fin n → M) : Prop :=
  ∀ i r, r ∈ IsLocalRing.maximalIdeal R → r • e i ∈ spanBefore (R := R) e i

/-- **Stacks Project, Tag 02P6.** The symbols used to generate the determinant: admissible
sequences whose length is the length of the module. -/
@[stacks 02P6 "symbols"]
public abbrev AdmissibleSequence (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] :=
  {e : Fin (moduleLength R M) → M // IsAdmissibleSequence (R := R) e}

/-- The free vector space over the residue field on the admissible symbols. -/
public abbrev DeterminantFree (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] :=
  AdmissibleSequence R M →₀ IsLocalRing.ResidueField R

/-- **Stacks Project, Tag 02P6.** The three families of admissible relations: a dependent
entry gives zero, replacing an entry up to a unit and earlier entries scales by the residue
of that unit, and two adjacent entries may be exchanged with a sign when the later entry
satisfies the stronger admissibility condition. -/
@[stacks 02P6 "admissible relations"]
public inductive DeterminantRelation {R : Type u} {M : Type v} [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] : DeterminantFree R M → Prop
  | dependent (e : AdmissibleSequence R M) (a : Fin (moduleLength R M))
      (ha : e.1 a ∈ spanBefore (R := R) e.1 a) :
      DeterminantRelation (Finsupp.single e 1)
  | unitChange (e : AdmissibleSequence R M) (a : Fin (moduleLength R M))
      (unit : Rˣ) (replacement x : M)
      (ha : e.1 a = (unit : R) • replacement + x)
      (hx : x ∈ spanBefore (R := R) e.1 a)
      (hreplacement : IsAdmissibleSequence (R := R) (Function.update e.1 a replacement)) :
      DeterminantRelation
        (Finsupp.single e 1 -
          IsLocalRing.residue R unit •
            Finsupp.single ⟨Function.update e.1 a replacement, hreplacement⟩ 1)
  | swap (e : AdmissibleSequence R M) (a b : Fin (moduleLength R M))
      (hba : b.val + 1 = a.val)
      (ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
        r • e.1 a ∈ spanBefore (R := R) e.1 b)
      (hswap : IsAdmissibleSequence (R := R)
        (Function.update (Function.update e.1 b (e.1 a)) a (e.1 b))) :
      DeterminantRelation
        (Finsupp.single e 1 +
          Finsupp.single
            ⟨Function.update (Function.update e.1 b (e.1 a)) a (e.1 b), hswap⟩ 1)

/-- The subspace of the free vector space generated by all admissible relations. -/
public def determinantRelations (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] :
    Submodule (IsLocalRing.ResidueField R) (DeterminantFree R M) :=
  Submodule.span (IsLocalRing.ResidueField R) {z | DeterminantRelation z}

/-- **Stacks Project, Tag 02P6.** The determinant of a finite-length module over a local
ring, as a vector space over the residue field. -/
@[stacks 02P6 "the determinant"]
public abbrev determinant (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] :=
  DeterminantFree R M ⧸ determinantRelations R M

/-- The class in the determinant represented by an admissible sequence. -/
public def symbol {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (e : AdmissibleSequence R M) : determinant R M :=
  Submodule.Quotient.mk (Finsupp.single e 1)

/-- The class of an admissible relation in the determinant is zero. -/
private theorem mk_eq_zero_of_determinantRelation {R : Type u} {M : Type v} [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] {z : DeterminantFree R M}
    (h : DeterminantRelation z) : (Submodule.Quotient.mk z : determinant R M) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span h)

/-- A symbol having an entry in the span of its predecessors is zero. -/
@[simp]
public theorem symbol_eq_zero_of_mem_spanBefore {R : Type u} {M : Type v} [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M]
    (e : AdmissibleSequence R M) (a : Fin (moduleLength R M))
    (ha : e.1 a ∈ spanBefore (R := R) e.1 a) :
    symbol e = 0 :=
  mk_eq_zero_of_determinantRelation (.dependent e a ha)

/-- Replacing an entry modulo its predecessors by a unit multiple scales its symbol by the
image of that unit in the residue field. -/
public theorem symbol_unitChange {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (e : AdmissibleSequence R M) (a : Fin (moduleLength R M))
    (unit : Rˣ) (replacement x : M)
    (ha : e.1 a = (unit : R) • replacement + x)
    (hx : x ∈ spanBefore (R := R) e.1 a)
    (hreplacement : IsAdmissibleSequence (R := R) (Function.update e.1 a replacement)) :
    symbol e = IsLocalRing.residue R unit •
      symbol ⟨Function.update e.1 a replacement, hreplacement⟩ :=
  sub_eq_zero.1
    (mk_eq_zero_of_determinantRelation (.unitChange e a unit replacement x ha hx hreplacement))

/-- Exchanging two adjacent entries changes the sign when the later entry is admissible
already with respect to the entries preceding the earlier one. -/
public theorem symbol_swap {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (e : AdmissibleSequence R M) (a b : Fin (moduleLength R M))
    (hba : b.val + 1 = a.val)
    (ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
      r • e.1 a ∈ spanBefore (R := R) e.1 b)
    (hswap : IsAdmissibleSequence (R := R)
      (Function.update (Function.update e.1 b (e.1 a)) a (e.1 b))) :
    symbol e = -symbol
      ⟨Function.update (Function.update e.1 b (e.1 a)) a (e.1 b), hswap⟩ :=
  eq_neg_of_add_eq_zero_left (mk_eq_zero_of_determinantRelation (.swap e a b hba ha hswap))

end Module.FiniteLength

end
