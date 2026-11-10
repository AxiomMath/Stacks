module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesGrading
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedGenerators
public import StacksFrontier.RingTheory.Filtration.IdealPowerSystemNoetherian

/-!
# The associated graded ring of an ideal of a Noetherian ring is Noetherian

Let `A` be a commutative ring and `I ⊆ A` an ideal. The associated graded ring
`Gr_I(A) = ⨁ₙ Iⁿ/Iⁿ⁺¹` is `AssociatedGraded.gradedRing I`. This file proves

`IsNoetherianRing A ⟹ IsNoetherianRing (AssociatedGraded.gradedRing I)`,

by exhibiting `Gr_I(A)` as a quotient of the graded Rees algebra `⨁ₙ Iⁿ`, whose Noetherianness
is `Stacks.RingTheory.isNoetherianRing_reesGradingDirectSum`.

## The surjection

Degreewise, `Iⁿ` is the degree-`n` part of the Rees algebra
(`Stacks.Blowup.reesGradingEquivPow`, `r ↦ monomial n r`) and `Iⁿ/Iⁿ⁺¹` receives it by
`AssociatedGraded.classOfPow`. Assembling the degreewise maps into a ring homomorphism is
`DirectSum.toSemiring`, whose two hypotheses are:

* multiplicativity, which reduces to the coefficient identity
  `(f g)_{i+j} = f_i g_j` for `f` supported in degree `i` and `g` in degree `j`
  (`AssociatedGraded.coeff_mul_reesGrading`, from `Stacks.Blowup.coe_eq_monomial` and
  `Polynomial.monomial_mul_monomial`) together with `AssociatedGraded.classOfPow_mul`;
* unitality, which is the degree-zero coefficient of `1` being `1`.

Surjectivity is a direct-sum induction: a homogeneous element of degree `n` is the class of some
`a ∈ Iⁿ`, which is the image of `monomial n a`.

## Main results

* `AssociatedGraded.reesGradingRingHom`: the ring homomorphism `⨁ₙ Iⁿ ⟶ Gr_I(A)`, with
  `reesGradingRingHom_of` computing it on a homogeneous element and
  `surjective_reesGradingRingHom`.
* `AssociatedGraded.isNoetherianRing_gradedRing`: **`Gr_I(A)` is Noetherian when `A` is.**

## Implementation notes

`AssociatedGraded.power I n` is `I ^ n • ⊤` rather than `I ^ n`, and they are equal only by
`AssociatedGraded.ring_power_eq`; `AssociatedGraded.classOfPow` is stated with `↥(I ^ n)`, so the
two spellings meet by `Subtype.ext` on the underlying element of `A` and never by a transport.
-/

@[expose] public noncomputable section

open Polynomial
open scoped DirectSum

universe u

namespace AssociatedGraded

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### The degreewise surjection off the Rees algebra -/

/-- The degree-`n` component of the surjection `⨁ₙ Iⁿ ⟶ Gr_I(A)`: the degree-`n` part of the
Rees algebra is `Iⁿ` (`Stacks.Blowup.reesGradingEquivPow`) and `AssociatedGraded.classOfPow`
takes its class. -/
def ofReesGrading (n : ℕ) : ↥(Stacks.Blowup.reesGrading I n) →+ gradedRing I :=
  (classOfPow I n).comp
    ((Stacks.Blowup.reesGradingEquivPow I n).symm.toLinearMap.toAddMonoidHom)

/-- `ofReesGrading I n f` is the class in `Iⁿ/Iⁿ⁺¹` of the element of `Iⁿ` corresponding to `f`
under `Stacks.Blowup.reesGradingEquivPow`. -/
theorem ofReesGrading_apply (n : ℕ) (f : ↥(Stacks.Blowup.reesGrading I n)) :
    ofReesGrading I n f = classOfPow I n ((Stacks.Blowup.reesGradingEquivPow I n).symm f) :=
  rfl

/-- On a homogeneous element of degree `n`, the degreewise map is the class of any element of `Iⁿ`
with the same degree-`n` coefficient. Stated this way, no statement below mentions the
graded-monoid multiplication or unit of the Rees grading, whose instance the elaborator resolves
only against an expected type. -/
theorem ofReesGrading_eq (n : ℕ) (f : ↥(Stacks.Blowup.reesGrading I n)) (a : ↥(I ^ n))
    (h : (a : A) = ((f : reesAlgebra I) : A[X]).coeff n) :
    ofReesGrading I n f = classOfPow I n a :=
  congrArg (classOfPow I n)
    (Subtype.ext ((Stacks.Blowup.coe_reesGradingEquivPow_symm I f).trans h.symm))

/-- The class of an element of `I ⁰` with value `1` is the unit of `Gr_I(A)`. -/
theorem classOfPow_eq_one (a : ↥(I ^ 0)) (ha : (a : A) = 1) : classOfPow I 0 a = 1 :=
  congrArg (DirectSum.of (fun k => piece (M := A) I k) 0)
    (congrArg (mk I 0) (Subtype.ext ha))

/-- For `f` supported in degree `i` and `g` in degree `j`, the degree-`i + j` coefficient of
`f g` is the product of the degree-`i` coefficient of `f` and the degree-`j` coefficient of
`g`: both are monomials (`Stacks.Blowup.coe_eq_monomial`) and `Polynomial.monomial_mul_monomial`
multiplies them. -/
theorem coeff_mul_reesGrading {i j : ℕ} (a : ↥(Stacks.Blowup.reesGrading I i))
    (b : ↥(Stacks.Blowup.reesGrading I j)) :
    (((a : reesAlgebra I) * (b : reesAlgebra I) : reesAlgebra I) : A[X]).coeff (i + j) =
      ((a : reesAlgebra I) : A[X]).coeff i * ((b : reesAlgebra I) : A[X]).coeff j := by
  have hcoe : (((a : reesAlgebra I) * (b : reesAlgebra I) : reesAlgebra I) : A[X]) =
      ((a : reesAlgebra I) : A[X]) * ((b : reesAlgebra I) : A[X]) := rfl
  rw [hcoe]
  conv_lhs => rw [Stacks.Blowup.coe_eq_monomial I a.2, Stacks.Blowup.coe_eq_monomial I b.2]
  rw [monomial_mul_monomial, coeff_monomial, ite_eq_left rfl]

/-! ### The ring homomorphism and its surjectivity -/

/-- The surjection `⨁ₙ Iⁿ ⟶ Gr_I(A)` of graded rings, assembled from the degreewise quotient
maps `ofReesGrading I n` by `DirectSum.toSemiring`. Its two hypotheses are proved in place, so
that the graded-monoid unit and multiplication of the Rees grading are elaborated against the
expected type rather than guessed. -/
def reesGradingRingHom :
    (⨁ n, ↥(Stacks.Blowup.reesGrading I n)) →+* gradedRing I :=
  DirectSum.toSemiring (ofReesGrading I)
    (by
      refine (ofReesGrading_eq I 0 _ ⟨1, by simp⟩ ?_).trans (classOfPow_eq_one I _ rfl)
      exact Polynomial.coeff_one_zero.symm)
    (by
      intro i j a b
      have hval : ((Stacks.Blowup.reesGradingEquivPow I i).symm a : A) *
            ((Stacks.Blowup.reesGradingEquivPow I j).symm b : A) =
          (((a : reesAlgebra I) * (b : reesAlgebra I) : reesAlgebra I) : A[X]).coeff (i + j) := by
        rw [Stacks.Blowup.coe_reesGradingEquivPow_symm,
          Stacks.Blowup.coe_reesGradingEquivPow_symm]
        exact (coeff_mul_reesGrading I a b).symm
      refine (ofReesGrading_eq I (i + j) _
        ⟨((Stacks.Blowup.reesGradingEquivPow I i).symm a : A) *
          ((Stacks.Blowup.reesGradingEquivPow I j).symm b : A),
          by
            rw [pow_add]
            exact Ideal.mul_mem_mul
              ((Stacks.Blowup.reesGradingEquivPow I i).symm a).2
              ((Stacks.Blowup.reesGradingEquivPow I j).symm b).2⟩ hval).trans ?_
      rw [ofReesGrading_apply, ofReesGrading_apply, ← classOfPow_mul I i j])

/-- On a homogeneous element `f` of degree `n`, `reesGradingRingHom I` is the degreewise map
`ofReesGrading I n`. -/
@[simp]
theorem reesGradingRingHom_of (n : ℕ) (f : ↥(Stacks.Blowup.reesGrading I n)) :
    reesGradingRingHom I (DirectSum.of _ n f) = ofReesGrading I n f :=
  DirectSum.toAddMonoid_of (ofReesGrading I) n f

/-- **The surjection is surjective**: a homogeneous element of `Gr_I(A)` of degree `n` is the
class of some `a ∈ Iⁿ`, which is the image of `monomial n a`, and every element is a finite sum
of homogeneous ones. -/
theorem surjective_reesGradingRingHom : Function.Surjective (reesGradingRingHom I) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n y =>
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      have ha : (a : A) ∈ I ^ n := by simpa only [ring_power_eq] using a.2
      refine ⟨DirectSum.of _ n (Stacks.Blowup.reesGradingEquivPow I n ⟨(a : A), ha⟩), ?_⟩
      rw [reesGradingRingHom_of]
      exact (ofReesGrading_eq I n _ ⟨(a : A), ha⟩ (by simp)).trans rfl
  | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      exact ⟨u + v, by rw [map_add, hu, hv]⟩

/-- **The associated graded ring of an ideal of a Noetherian ring is Noetherian.** It is a
quotient of the graded Rees algebra, which is Noetherian by
`Stacks.RingTheory.isNoetherianRing_reesGradingDirectSum`. -/
theorem isNoetherianRing_gradedRing [IsNoetherianRing A] : IsNoetherianRing (gradedRing I) :=
  have := Stacks.RingTheory.isNoetherianRing_reesGradingDirectSum I
  isNoetherianRing_of_surjective (⨁ n, ↥(Stacks.Blowup.reesGrading I n)) (gradedRing I)
    (reesGradingRingHom I) (surjective_reesGradingRingHom I)

end AssociatedGraded

end
