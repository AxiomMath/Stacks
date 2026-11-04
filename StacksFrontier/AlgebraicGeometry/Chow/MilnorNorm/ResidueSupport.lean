module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FullExactness

/-!
# A class has a nonvanishing residue at only finitely many closed points of `A¹_k`

Let `k` be a field. This file proves that for every `x ∈ K^M_*(RatFunc k)` there is a **finite**
set of polynomials outside which every residue of `x` vanishes
(`Stacks.Chow.exists_finset_forall_monicIrreducibleResidue_eq_zero`).

`StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.DegreeFiltration` bounds the *degree* of the
points that can contribute, which is not enough: over an infinite field there are infinitely many
monic irreducible polynomials of each degree. What is true is that a point contributes only if it
divides the numerator or the denominator of one of the finitely many entries of a symbol
expression of `x`, and a nonzero polynomial has only finitely many monic irreducible divisors
(`Stacks.Chow.finite_monicIrreducibleDvd_of_ne_zero`).

This is what lets a class with a prescribed residue at one point be corrected, one point at a
time, into a class with that residue and no other — the statement the norm map of a simple
extension is defined from.

## Finitely many monic irreducible divisors

By induction on a bound for the degree. A nonzero constant has none, for degree reasons. If `f`
has a monic irreducible divisor `χ₀`, write `f = χ₀ g`; then `g` is nonzero of strictly smaller
degree, `χ₀` being of positive degree, and any monic irreducible divisor of `f` other than `χ₀`
divides `g` — a monic irreducible is prime, and two associated monic polynomials are equal. So
the divisors of `f` lie in `{χ₀}` together with those of `g`.

## Main definitions

* `Stacks.Chow.monicIrreducibleDvd` — the monic irreducible divisors of a polynomial.

## Main results

* `Stacks.Chow.natDegree_pos_of_monic_irreducible` — a monic irreducible has positive degree.
* `Stacks.Chow.finite_monicIrreducibleDvd_of_ne_zero` — **a nonzero polynomial has finitely many
  monic irreducible divisors.**
* `Stacks.Chow.milnorKSymbol_mul_mem_milnorKNotDvdFiltration` — multiplying by a symbol of a
  polynomial not divisible by `p` respects the subgroup generated away from `p`.
* `Stacks.Chow.milnorKSymbolProd_mem_milnorKNotDvdFiltration_of_forall` — a symbol whose entries
  have numerator and denominator prime to `p` lies there.
* `Stacks.Chow.exists_finset_forall_monicIrreducibleResidue_eq_zero` — **a class has a
  nonvanishing residue at only finitely many closed points.**

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

variable {k : Type u} [Field k]

/-! ### The monic irreducible divisors of a polynomial -/

/-- A monic irreducible polynomial has positive degree: a monic polynomial of degree zero is `1`,
which is a unit. -/
theorem natDegree_pos_of_monic_irreducible {χ : Polynomial k} (hm : χ.Monic)
    (hi : Irreducible χ) : 0 < χ.natDegree :=
  natDegree_pos_of_monic_ne_one hm fun h ↦ hi.not_isUnit (h ▸ isUnit_one)

/-- The set of monic irreducible divisors of a polynomial. -/
def monicIrreducibleDvd (f : Polynomial k) : Set (Polynomial k) :=
  {χ | χ.Monic ∧ Irreducible χ ∧ χ ∣ f}

/-- The inductive step: a monic irreducible divisor of `χ₀ g` is either `χ₀` or a divisor of
`g`. A monic irreducible is prime, and two associated monic polynomials are equal. -/
theorem monicIrreducibleDvd_subset_insert {f χ₀ g : Polynomial k} (hm₀ : χ₀.Monic)
    (hi₀ : Irreducible χ₀) (hfg : f = χ₀ * g) :
    monicIrreducibleDvd f ⊆ insert χ₀ (monicIrreducibleDvd g) := by
  rintro χ ⟨hm, hi, hdvd⟩
  rw [hfg] at hdvd
  rcases (UniqueFactorizationMonoid.irreducible_iff_prime.mp hi).2.2 _ _ hdvd with h₀ | hg
  · exact Set.mem_insert_iff.mpr (Or.inl
      (Polynomial.eq_of_monic_of_associated hm hm₀ (hi.associated_of_dvd hi₀ h₀)))
  · exact Set.mem_insert_of_mem _ ⟨hm, hi, hg⟩

/-- **A nonzero polynomial has only finitely many monic irreducible divisors**, by induction on a
bound for its degree. -/
theorem finite_monicIrreducibleDvd :
    ∀ (n : ℕ) (f : Polynomial k), f ≠ 0 → f.natDegree ≤ n → (monicIrreducibleDvd f).Finite := by
  intro n
  induction n with
  | zero =>
      intro f hf hfn
      refine Set.Finite.subset Set.finite_empty ?_
      rintro χ ⟨hm, hi, hdvd⟩
      have hle := Polynomial.natDegree_le_of_dvd hdvd hf
      have hpos := natDegree_pos_of_monic_irreducible hm hi
      omega
  | succ n ih =>
      intro f hf hfn
      rcases Set.eq_empty_or_nonempty (monicIrreducibleDvd f) with hempty | ⟨χ₀, hχ₀⟩
      · rw [hempty]; exact Set.finite_empty
      obtain ⟨g, rfl⟩ := hχ₀.2.2
      have hg : g ≠ 0 := fun h ↦ hf (by rw [h, mul_zero])
      have hdeg : g.natDegree ≤ n := by
        have hsum : (χ₀ * g).natDegree = χ₀.natDegree + g.natDegree :=
          Polynomial.natDegree_mul hχ₀.1.ne_zero hg
        have hpos := natDegree_pos_of_monic_irreducible hχ₀.1 hχ₀.2.1
        omega
      exact Set.Finite.subset ((ih g hg hdeg).insert χ₀)
        (monicIrreducibleDvd_subset_insert hχ₀.1 hχ₀.2.1 rfl)

/-- A nonzero polynomial has only finitely many monic irreducible divisors. -/
theorem finite_monicIrreducibleDvd_of_ne_zero {f : Polynomial k} (hf : f ≠ 0) :
    (monicIrreducibleDvd f).Finite :=
  finite_monicIrreducibleDvd f.natDegree f hf le_rfl

/-- A unit of `RatFunc k` has nonzero numerator and denominator. -/
private theorem num_ne_zero_and_denom_ne_zero (u : (RatFunc k)ˣ) :
    (u : RatFunc k).num ≠ 0 ∧ (u : RatFunc k).denom ≠ 0 :=
  ⟨RatFunc.num_ne_zero u.ne_zero, RatFunc.denom_ne_zero (u : RatFunc k)⟩

/-- A monic irreducible outside the finite set of monic irreducible divisors of `q ≠ 0` does not
divide `q`. -/
private theorem not_dvd_of_notMem_toFinset {q p : Polynomial k} (hq : q ≠ 0) (hm : p.Monic)
    (hi : Irreducible p) (hp : p ∉ (finite_monicIrreducibleDvd_of_ne_zero hq).toFinset) :
    ¬p ∣ q :=
  fun hdvd ↦ hp ((finite_monicIrreducibleDvd_of_ne_zero hq).mem_toFinset.mpr ⟨hm, hi, hdvd⟩)

/-! ### Symbols generated away from a point -/

/-- **Multiplying by the symbol of a polynomial not divisible by `p` respects the subgroup
generated away from `p`.** -/
theorem milnorKSymbol_mul_mem_milnorKNotDvdFiltration {p : Polynomial k} {v : (RatFunc k)ˣ}
    (hv : v ∈ polyUnitsNotDvd k p) {x : MilnorKRing (RatFunc k)}
    (hx : x ∈ milnorKNotDvdFiltration k p) :
    milnorKSymbol (RatFunc k) v * x ∈ milnorKNotDvdFiltration k p := by
  refine milnorKNotDvdFiltration_le (H := AddSubgroup.comap
    (AddMonoidHom.mulLeft (milnorKSymbol (RatFunc k) v)) (milnorKNotDvdFiltration k p)) ?_ hx
  intro l hl
  change milnorKSymbol (RatFunc k) v * milnorKSymbolProd (RatFunc k) l ∈
    milnorKNotDvdFiltration k p
  rw [← milnorKSymbolProd_cons]
  refine milnorKSymbolProd_mem_milnorKNotDvdFiltration fun w hw ↦ ?_
  rcases List.mem_cons.mp hw with rfl | hwl
  · exact hv
  · exact hl w hwl

/-- **A symbol whose entries have numerator and denominator prime to `p` lies in the subgroup
generated away from `p`.** Each entry is the ratio of its numerator and its denominator, so its
symbol is a difference of two symbols of polynomials prime to `p`. -/
theorem milnorKSymbolProd_mem_milnorKNotDvdFiltration_of_forall {p : Polynomial k}
    {l : List (RatFunc k)ˣ}
    (hl : ∀ u ∈ l, ¬p ∣ (u : RatFunc k).num ∧ ¬p ∣ (u : RatFunc k).denom) :
    milnorKSymbolProd (RatFunc k) l ∈ milnorKNotDvdFiltration k p := by
  induction l with
  | nil => exact milnorKSymbolProd_mem_milnorKNotDvdFiltration (by simp)
  | cons u l ih =>
      have hrest := ih fun v hv ↦ hl v (List.mem_cons_of_mem u hv)
      obtain ⟨hnotnum, hnotden⟩ := hl u List.mem_cons_self
      obtain ⟨hnum, hden⟩ := num_ne_zero_and_denom_ne_zero u
      have hu : u = polyUnit hnum / polyUnit hden :=
        Units.ext (by
          rw [Units.val_div_eq_div_val, coe_polyUnit, coe_polyUnit, RatFunc.num_div_denom])
      rw [milnorKSymbolProd_cons, hu, milnorKSymbol_div, sub_mul]
      exact sub_mem
        (milnorKSymbol_mul_mem_milnorKNotDvdFiltration ⟨_, hnum, hnotnum, rfl⟩ hrest)
        (milnorKSymbol_mul_mem_milnorKNotDvdFiltration ⟨_, hden, hnotden, rfl⟩ hrest)

/-! ### The residue support of a class -/

open Classical in
/-- The numerators and denominators of the entries of a symbol have finitely many monic
irreducible divisors between them. -/
theorem exists_finset_forall_notDvd (l : List (RatFunc k)ˣ) :
    ∃ S : Finset (Polynomial k), ∀ p : Polynomial k, p.Monic → Irreducible p → p ∉ S →
      ∀ u ∈ l, ¬p ∣ (u : RatFunc k).num ∧ ¬p ∣ (u : RatFunc k).denom := by
  classical
  induction l with
  | nil => exact ⟨∅, fun p _ _ _ u hu ↦ absurd hu List.not_mem_nil⟩
  | cons u l ih =>
      obtain ⟨T, hT⟩ := ih
      obtain ⟨hnum, hden⟩ := num_ne_zero_and_denom_ne_zero u
      refine ⟨(finite_monicIrreducibleDvd_of_ne_zero hnum).toFinset ∪
        (finite_monicIrreducibleDvd_of_ne_zero hden).toFinset ∪ T, fun p hm hi hp v hv ↦ ?_⟩
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact ⟨not_dvd_of_notMem_toFinset hnum hm hi fun h ↦
            hp (Finset.mem_union_left _ (Finset.mem_union_left _ h)),
          not_dvd_of_notMem_toFinset hden hm hi fun h ↦
            hp (Finset.mem_union_left _ (Finset.mem_union_right _ h))⟩
      · exact hT p hm hi (fun h ↦ hp (Finset.mem_union_right _ h)) v hv'

open Classical in
/-- **Every class of `K^M_*(RatFunc k)` has a nonvanishing residue at only finitely many closed
points of `A¹_k`.** The condition is carried by a finite set of polynomials, which is what makes
it closed under addition. -/
theorem exists_finset_forall_monicIrreducibleResidue_eq_zero (x : MilnorKRing (RatFunc k)) :
    ∃ S : Finset (Polynomial k), ∀ (d : ℕ) (ψ : MonicIrreducibleOfDegree k d),
      poly ψ ∉ S → monicIrreducibleResidue ψ x = 0 := by
  classical
  refine mem_of_forall_milnorKSymbolProd_mem
    (H := { carrier := {y | ∃ S : Finset (Polynomial k), ∀ (d : ℕ)
              (ψ : MonicIrreducibleOfDegree k d),
              poly ψ ∉ S → monicIrreducibleResidue ψ y = 0}
            zero_mem' := ⟨∅, fun _ _ _ ↦ map_zero _⟩
            add_mem' := by
              rintro y z ⟨S, hS⟩ ⟨T, hT⟩
              exact ⟨S ∪ T, fun d ψ hψ ↦ by
                rw [map_add, hS d ψ fun h ↦ hψ (Finset.mem_union_left T h),
                  hT d ψ fun h ↦ hψ (Finset.mem_union_right S h), add_zero]⟩
            neg_mem' := by
              rintro y ⟨S, hS⟩
              exact ⟨S, fun d ψ hψ ↦ by rw [map_neg, hS d ψ hψ, neg_zero]⟩ })
    (fun l ↦ ?_) x
  obtain ⟨S, hS⟩ := exists_finset_forall_notDvd l
  exact ⟨S, fun d ψ hψ ↦ monicIrreducibleResidue_eq_zero_of_mem_milnorKNotDvdFiltration ψ
    (milnorKSymbolProd_mem_milnorKNotDvdFiltration_of_forall
      (hS (poly ψ) (monic ψ) (irreducible ψ) hψ))⟩

end Stacks.Chow

end
