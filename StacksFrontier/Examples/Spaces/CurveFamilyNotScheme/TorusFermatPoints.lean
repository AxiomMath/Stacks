module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.TorusRing

/-!
# The affine Fermat curve on the torus has uncountably many points

Let `k` be an uncountable algebraically closed field. The affine curve
`1 + x ^ 3 + y ^ 3 = 0` in the torus `x y ≠ 0`, with coordinate ring
`k[x, y][1 / (x y)] ⧸ (1 + x ^ 3 + y ^ 3)`, has uncountably many maximal ideals: for every
`c ∈ k` with `c ≠ 0` and `1 + c ^ 3 ≠ 0` there is a cube root `d` of `-(1 + c ^ 3)`, and `(c, d)`
is a point of the curve; distinct `c` give distinct points.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.not_countable_setOf_isMaximal_torusFermatRing`: the
  maximal ideals of the coordinate ring are not countable.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

variable (k : Type u) [Field k]

/-- The coordinate ring `k[x, y][1 / (x y)] ⧸ (1 + x ^ 3 + y ^ 3)` of the affine Fermat curve in
the torus. -/
abbrev torusFermatRing : Type u := torusRing k ⧸ Ideal.span {torusFermat k}

variable {k}

/-- Evaluation of the torus ring at a point `(c, d)` with `c d ≠ 0`. -/
def torusEval (c d : k) (h : c * d ≠ 0) : torusRing k →+* k :=
  IsLocalization.Away.lift (X 0 * X 1 : MvPolynomial (Fin 2) k)
    (g := (MvPolynomial.aeval ![c, d]).toRingHom) (by simpa using h.isUnit)

theorem torusEval_algebraMap (c d : k) (h : c * d ≠ 0) (p : MvPolynomial (Fin 2) k) :
    torusEval c d h (algebraMap _ (torusRing k) p) = MvPolynomial.aeval ![c, d] p :=
  IsLocalization.Away.lift_eq _ _ p

/-- Evaluation at a point `(c, d)` of the affine Fermat curve, as a homomorphism out of its
coordinate ring. -/
def torusFermatEval (c d : k) (h : c * d ≠ 0) (hF : 1 + c ^ 3 + d ^ 3 = 0) :
    torusFermatRing k →+* k :=
  Ideal.Quotient.lift _ (torusEval c d h) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, torusFermat, torusEval_algebraMap]
    simp [hF]

theorem torusFermatEval_surjective (c d : k) (h : c * d ≠ 0) (hF : 1 + c ^ 3 + d ^ 3 = 0) :
    Function.Surjective (torusFermatEval c d h hF) := fun a =>
  ⟨Ideal.Quotient.mk _ (algebraMap _ (torusRing k) (C a : MvPolynomial (Fin 2) k)), by
    rw [torusFermatEval, Ideal.Quotient.lift_mk, torusEval_algebraMap]
    simp⟩

/-- **The affine Fermat curve in the torus has uncountably many points** over an uncountable
algebraically closed field: its coordinate ring has an uncountable set of maximal ideals. -/
theorem not_countable_setOf_isMaximal_torusFermatRing [IsAlgClosed k] [Uncountable k] :
    ¬ {M : Ideal (torusFermatRing k) | M.IsMaximal}.Countable := by
  classical
  set S : Set k := {c | c ≠ 0 ∧ 1 + c ^ 3 ≠ 0}
  have hScofin : (Sᶜ).Finite := by
    have hsub : Sᶜ ⊆ {0} ∪ ((Polynomial.X ^ 3 + 1 : Polynomial k).roots.toFinset : Set k) := by
      intro c hc
      simp only [S, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_not] at hc
      rcases hc with hc | hc
      · exact Or.inl hc
      · right
        have hne : (Polynomial.X ^ 3 + 1 : Polynomial k) ≠ 0 :=
          Polynomial.X_pow_add_C_ne_zero (by norm_num) 1
        simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne,
          Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one]
        rw [add_comm]
        exact hc
    exact ((Set.finite_singleton 0).union (Finset.finite_toSet _)).subset hsub
  have hS : ¬ S.Countable := by
    intro hc
    have huniv := hc.union hScofin.countable
    rw [Set.union_compl_self] at huniv
    exact not_countable (Set.countable_univ_iff.mp huniv)
  -- a cube root of `-(1 + c ^ 3)` for every `c ∈ S`
  have hroot : ∀ c ∈ S, ∃ d : k, d ^ 3 = -(1 + c ^ 3) := fun c _ =>
    IsAlgClosed.exists_pow_nat_eq _ (by norm_num)
  choose! d hd using hroot
  have hd0 : ∀ c ∈ S, c * d c ≠ 0 := fun c hc => by
    refine mul_ne_zero hc.1 fun h => hc.2 ?_
    have := hd c hc
    rw [h] at this
    linear_combination this
  have hF : ∀ c ∈ S, 1 + c ^ 3 + d c ^ 3 = 0 := fun c hc => by
    rw [hd c hc]
    ring
  let M : k → Ideal (torusFermatRing k) := fun c =>
    if hc : c ∈ S then RingHom.ker (torusFermatEval c (d c) (hd0 c hc) (hF c hc)) else ⊥
  have hMmax : ∀ c ∈ S, (M c).IsMaximal := fun c hc => by
    simp only [M, hc, ↓reduceDIte]
    exact RingHom.ker_isMaximal_of_surjective _ (torusFermatEval_surjective _ _ _ _)
  have hMinj : Set.InjOn M S := by
    intro c hc c' hc' hcc
    -- the class of `x - c` lies in the kernel at `c`, hence at `c'`
    set e : torusFermatRing k :=
      Ideal.Quotient.mk _ (algebraMap _ (torusRing k) (X 0 - C c : MvPolynomial (Fin 2) k))
    have hval : ∀ c₁ (h₁ : c₁ ∈ S), torusFermatEval c₁ (d c₁) (hd0 c₁ h₁) (hF c₁ h₁) e = c₁ - c :=
      fun c₁ h₁ => by
        rw [torusFermatEval, Ideal.Quotient.lift_mk, torusEval_algebraMap]
        simp
    have hmem : e ∈ M c := by
      simp only [M, hc, ↓reduceDIte, RingHom.mem_ker, hval c hc, sub_self]
    rw [hcc] at hmem
    simp only [M, hc', ↓reduceDIte, RingHom.mem_ker, hval c' hc'] at hmem
    exact (sub_eq_zero.mp hmem).symm
  intro hcount
  exact hS (Set.MapsTo.countable_of_injOn (fun c hc => hMmax c hc) hMinj hcount)

end Stacks.Examples.CurveFamilyNotScheme

end
