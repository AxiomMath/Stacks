module

public import StacksFrontier.Cotangent.PolynomialRetraction
public import StacksFrontier.Cotangent.Triangle.ProductDescent

/-!
# Lemma 08SI with the fundamental triangle supplied

`StacksFrontier.Cotangent.PolynomialRetraction` proves [Stacks, Tag 08SI] under the predicate
`CommAlgCat.HasFundamentalTriangleAt A B A`, the existence of a distinguished triangle on the
three vertices of the display of Tag 08QS for the tower `A → B → A`; that file is upstream of
Proposition 08QX. This file proves the predicate at every tower, from Proposition 08QX,
`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`, and states Tag 08SI under exactly the source's
hypotheses.

## Main results

* `CommAlgCat.hasFundamentalTriangleAt`: `CommAlgCat.HasFundamentalTriangleAt A B C` holds for
  every tower `A → B → C`.
* `CommAlgCat.nonempty_cotangentComplex_retraction_iso_single_unconditional`: **[Stacks, Tag
  08SI]**, in the general form — `L_{A/B}` is isomorphic in `D(A)` to `I/I²` placed in
  cohomological degree `-1`.
* `CommAlgCat.ker_mvPolynomial_int_eq_span_X`: the kernel of `ℤ[x₁, …, xₙ] → ℤ`, `xᵢ ↦ 0`, is
  `(x₁, …, xₙ)`.
* `CommAlgCat.nonempty_cotangentComplex_mvPolynomial_int_iso_single`: Tag 08SI in the source's
  own case `ℤ[x₁, …, xₙ] → ℤ`.

## References

* [Stacks Project, Tag 08SI](https://stacks.math.columbia.edu/tag/08SI)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), the fundamental
  triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

/-- **Proposition 08QX at one tower.** For every tower `A → B → C` the three vertices of the
display of Tag 08QS fit into a distinguished triangle: this is
`CommAlgCat.productFundamentalTriangle_distinguished`. -/
theorem hasFundamentalTriangleAt (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
    HasFundamentalTriangleAt A B C :=
  exists_distTriang_fundamentalVertex.{u} A B C

section Retraction

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Algebra B A]
  [IsScalarTower A B A]

/-- **Stacks Project, Tag 08SI.** Let `B` be a polynomial algebra over `A` with an augmentation
`B → A`, and let `I` be its kernel. Then `L_{A/B}` is isomorphic in `D(A)` to `I/I²` placed in
cohomological degree `-1`.

This is `CommAlgCat.nonempty_cotangentComplex_retraction_iso_single` with the fundamental
triangle of the tower `A → B → A` supplied by `CommAlgCat.hasFundamentalTriangleAt`. -/
@[stacks 08SI "the lemma for a general base ring A and a general polynomial algebra B over it \
  with an augmentation B → A (the letters A and B are swapped relative to the source): the \
  source's map Z[x_1,...,x_n] -> Z sending every x_i to 0 is the case A = Z, \
  B = Z[x_1,...,x_n], spelled out as \
  `CommAlgCat.nonempty_cotangentComplex_mvPolynomial_int_iso_single`, which also proves that \
  the kernel of that map is the source's ideal I = (x_1,...,x_n); I/I^2 is the conormal module \
  of the augmentation. NOTHING is carried: the triangle the source's \
  proof invokes is Proposition 08QX for the tower A -> B -> A, \
  `CommAlgCat.productFundamentalTriangle_distinguished`, which holds for arbitrary ring maps — \
  the triangle of Tag 08SD needs the middle map injective, whereas the augmentation B → A is \
  surjective, so it is the proposition and not Tag 08SD that applies"]
theorem nonempty_cotangentComplex_retraction_iso_single_unconditional
    (hB : Algebra.IsPolynomialAlgebra A B) :
    Nonempty (DerivedCategory.Q.obj (cotangentComplex B (CommAlgCat.of B A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} ↥(CommAlgCat.of B A)) (-1)).obj
        (ModuleCat.of ↥(CommAlgCat.of B A)
          (surjectionExtension B (CommAlgCat.of B A)
            (surjective_algebraMap_of_isScalarTower_self A B)).Cotangent)) :=
  nonempty_cotangentComplex_retraction_iso_single A B hB (hasFundamentalTriangleAt A B A)

end Retraction

section SourceCase

/-- The kernel of a ring map `ℤ[x₁, …, xₙ] → ℤ` sending every `xᵢ` to `0` is the ideal
`(x₁, …, xₙ)`. -/
theorem ker_mvPolynomial_int_eq_span_X {n : ℕ} (f : MvPolynomial (Fin n) ℤ →+* ℤ)
    (hf : ∀ i, f (MvPolynomial.X i) = 0) :
    RingHom.ker f = Ideal.span (Set.range MvPolynomial.X) := by
  have hf' : f = MvPolynomial.constantCoeff := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [MvPolynomial.constantCoeff_C]
      exact congrArg (· r) (RingHom.ext_int (f.comp MvPolynomial.C) (RingHom.id ℤ))
    · simp [hf]
  subst hf'
  ext p
  have h := MvPolynomial.mem_pow_idealOfVars_iff' 1 p
  rw [pow_one] at h
  rw [RingHom.mem_ker,
    show Ideal.span (Set.range MvPolynomial.X) = MvPolynomial.idealOfVars (Fin n) ℤ from rfl, h]
  constructor
  · intro hp x hx
    obtain rfl : x = 0 := by
      rwa [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hx
    exact (MvPolynomial.constantCoeff_eq p).symm.trans hp
  · intro hp
    exact (MvPolynomial.constantCoeff_eq p).trans (hp 0 (by simp))

/-- **Stacks Project, Tag 08SI, in the source's own case.** Let `ℤ[x₁, …, xₙ] → ℤ` be the ring
map sending every `xᵢ` to `0`, and let `I = (x₁, …, xₙ)`, which is its kernel
(`CommAlgCat.ker_mvPolynomial_int_eq_span_X`). Then `L_{ℤ/ℤ[x₁, …, xₙ]}` is isomorphic in
`D(ℤ)` to the conormal module of `ℤ[x₁, …, xₙ] → ℤ` placed in cohomological degree `-1`, and the
kernel of that map is `I`.

This is `CommAlgCat.nonempty_cotangentComplex_retraction_iso_single_unconditional` for
`A = ℤ` and `B = ℤ[x₁, …, xₙ]`. -/
theorem nonempty_cotangentComplex_mvPolynomial_int_iso_single (n : ℕ)
    [Algebra (MvPolynomial (Fin n) ℤ) ℤ]
    (hX : ∀ i, algebraMap (MvPolynomial (Fin n) ℤ) ℤ (MvPolynomial.X i) = 0) :
    Nonempty (DerivedCategory.Q.obj
        (cotangentComplex (MvPolynomial (Fin n) ℤ) (CommAlgCat.of (MvPolynomial (Fin n) ℤ) ℤ)) ≅
      (DerivedCategory.singleFunctor
          (ModuleCat.{0} ↥(CommAlgCat.of (MvPolynomial (Fin n) ℤ) ℤ)) (-1)).obj
        (ModuleCat.of ↥(CommAlgCat.of (MvPolynomial (Fin n) ℤ) ℤ)
          (surjectionExtension (MvPolynomial (Fin n) ℤ)
            (CommAlgCat.of (MvPolynomial (Fin n) ℤ) ℤ)
            (surjective_algebraMap_of_isScalarTower_self ℤ (MvPolynomial (Fin n) ℤ))).Cotangent)) ∧
      RingHom.ker (algebraMap (MvPolynomial (Fin n) ℤ) ℤ) = Ideal.span (Set.range MvPolynomial.X) :=
  ⟨by convert (nonempty_cotangentComplex_retraction_iso_single_unconditional ℤ
      (MvPolynomial (Fin n) ℤ) ⟨Fin n, ⟨AlgEquiv.refl⟩⟩) <;>
      first | rfl | exact Subsingleton.elim _ _,
    ker_mvPolynomial_int_eq_span_X _ hX⟩

end SourceCase

end CommAlgCat

end
