module

public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.DegreeOne

/-!
# A Koszul-regular generating sequence is as short as any generating family

Let `R` be a commutative ring and let `f₁, …, f_m` be a Koszul-regular sequence generating a
proper ideal `J`. Then every family `g₁, …, g_k` generating `J` has `m ≤ k`.

This is the commutative-algebra input that makes the rank function `r` of [Stacks, Tag 0BQZ] —
the minimal number of generators of a Koszul-regular sheaf of ideals needed near a point — equal
to the length of a local Koszul-regular generating sequence at the points of the support.

## Main results

* `Koszul.length_le_of_span_eq`: `m ≤ k`.

## Implementation notes

A Koszul-regular sequence is `H₁`-regular, hence quasi-regular by [Stacks, Tag 062I], and in
degree one quasi-regularity says that a relation `∑ aᵢ fᵢ ∈ J²` has every coefficient in `J`
(`RingTheory.Sequence.IsQuasiRegular.coeff_mem_Jid`). Writing `f = B g` and `g = C f` gives
`(B C - 1) f = 0`, so `B C ≡ 1` modulo `J`. Over the nonzero ring `R ⧸ J` the matrix `B` then
defines a surjection `(R ⧸ J)ᵏ → (R ⧸ J)ᵐ`, split by `C`, and the rank condition gives `m ≤ k`.

## References

* [Stacks Project, Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ)
* [Stacks Project, Tag 062I](https://stacks.math.columbia.edu/tag/062I)
-/

@[expose] public section

universe u

namespace Koszul

variable {R : Type u} [CommRing R]

/-- **A Koszul-regular sequence generating a proper ideal is as short as any generating family
of that ideal.** -/
theorem length_le_of_span_eq {m k : ℕ} (f : Fin m → R) (g : Fin k → R)
    (hf : IsKoszulRegular f) (hJ : Ideal.span (Set.range f) ≠ ⊤)
    (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) : m ≤ k := by
  classical
  have hq : RingTheory.Sequence.IsQuasiRegular R (List.ofFn f) :=
    isQuasiRegular_of_isH1RegularOn ((isH1RegularOn_self_iff f).2 hf.isH1Regular)
  have hmem : ∀ {a b : ℕ} (u : Fin a → R) (v : Fin b → R),
      Ideal.span (Set.range u) = Ideal.span (Set.range v) →
        ∀ i, ∃ c : Fin b → R, ∑ j, c j • v j = u i := fun u v h i =>
    (Submodule.mem_span_range_iff_exists_fun R).1
      (show u i ∈ Ideal.span (Set.range v) from h ▸ Ideal.subset_span (Set.mem_range_self i))
  choose B hB using hmem f g hfg
  choose C hC using hmem g f hfg.symm
  set J := Ideal.span (Set.range f)
  -- `B C ≡ 1` modulo `J`.
  have hBC : ∀ i l, (∑ j, B i j * C j l) - (if i = l then 1 else 0) ∈ J := by
    intro i l
    have hrel : ∑ l, ((∑ j, B i j * C j l) - (if i = l then 1 else 0)) * f l = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_mul]
      rw [Finset.sum_comm]
      have : ∀ j, ∑ l, B i j * C j l * f l = B i j * g j := fun j => by
        rw [← hC j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul, mul_assoc]
      rw [Finset.sum_congr rfl fun j _ => this j, ← hB i]
      simp
    exact hq.coeff_mem_Jid _ (by rw [hrel]; exact Submodule.zero_mem _) l
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  have hBC' : (Matrix.of B).map (Ideal.Quotient.mk J) * (Matrix.of C).map (Ideal.Quotient.mk J) =
      1 := by
    ext i l
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply, ← map_mul,
      ← map_sum]
    rw [Ideal.Quotient.eq.2 (hBC i l)]
    split_ifs <;> simp
  generalize (Matrix.of B).map (Ideal.Quotient.mk J) = B' at hBC'
  generalize (Matrix.of C).map (Ideal.Quotient.mk J) = C' at hBC'
  exact le_of_fin_surjective (R ⧸ J) (Matrix.toLin' B') fun z =>
    ⟨C'.mulVec z, by simp [Matrix.mulVec_mulVec, hBC']⟩

end Koszul
