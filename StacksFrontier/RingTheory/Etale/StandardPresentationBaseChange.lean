module

public import StacksFrontier.RingTheory.Etale.StandardPresentationSolutions

/-!
# Pushing a standard presentation forward along a ring map

Let `P₁, …, P_n ∈ R[x₁, …, x_n]` be a system of polynomials and `φ : R ⟶ A` a ring map. Applying
`φ` to the coefficients gives the system `φ(P₁), …, φ(P_n) ∈ A[x₁, …, x_n]`, and the ring it
presents, `A[x]/(φP)`, is the base change `A ⊗_R R[x]/(P)`.

This file proves the only thing the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6) uses about that base
change, namely that it has the expected points, and it proves it *without* tensor products: a
tuple `a` in an `A`-algebra `A'` solves the pushed system `φ(P)` over `g' : A ⟶ A'` exactly when
it solves the original system `P` over the composite `g' ∘ φ`, because
`MvPolynomial.map g' ∘ MvPolynomial.map φ = MvPolynomial.map (g' ∘ φ)`. The two solution sets are
therefore the *same* set, not merely isomorphic ones
(`MvPolynomial.isSolution_map`), and transporting that along
`MvPolynomial.quotientSpanRangeHomOverEquiv` on both sides identifies the points of `A[x]/(φP)`
over `A` with the points of `R[x]/(P)` over `R` — which is the universal property of the base
change (`MvPolynomial.homOverMapCoeffEquiv`).

In the geometry of Stacks 04I6, `R = B` with `Y = Spec(B)`, `A = Γ(X, ⊤)` with `φ` the ring map
on global functions induced by `g^♯`, `R[x]/(P) = C` with `V = Spec(C)` étale over `Y`, and
`A[x]/(φP) = A ⊗_B C` with `X ×_Y V = Spec(A ⊗_B C)`. The statement below is then the assertion
that the `A'`-points of `X ×_Y V` over `X` are the `A'`-points of `V` over `Y`, i.e. the universal
property of the fibre product, read through the presentation; it is what makes the row of the
pushed system `φ(P)` over `𝒪_X` the row that cuts out `h_{X ×_Y V}`.

Nothing here needs `R[x]/(P)` to be étale over `R`, or the Jacobian of `P` to be invertible: the
identification of the points is unconditional. No `@[stacks]` tag is registered, since Stacks
04I6 asserts a 2-isomorphism of morphisms of ringed topoi together with its uniqueness and this
is one step inside its proof.

## Main results

* `MvPolynomial.isSolution_map`: solving the pushed system over `g'` is solving the original
  system over `g' ∘ φ`.
* `MvPolynomial.isSolutionMapEquiv`: the two solution sets, as the same subtype.
* `MvPolynomial.homOverMapCoeffEquiv`: the points of `A[x]/(φP)` lying over `g'` are the points
  of `R[x]/(P)` lying over `g' ∘ φ`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

universe u v w

namespace MvPolynomial

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] {A' : Type w} [CommRing A']
  {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R) (φ : R →+* A) (g : A →+* A')

/-- **Pushing the coefficients of a system forward does not change its solutions.** A tuple in
`A'` solves the system `φ(P)` over `g : A ⟶ A'` exactly when it solves `P` over the composite
`g ∘ φ`.

Both conditions say that `MvPolynomial.map (g ∘ φ) (P j)` vanishes at the tuple, the one spelled
as two successive coefficient maps and the other as their composite; `MvPolynomial.map_map`
identifies them. -/
theorem isSolution_map (a : Fin n → A') :
    IsSolution (fun j => MvPolynomial.map φ (P j)) g a ↔ IsSolution P (g.comp φ) a := by
  simp only [IsSolution, MvPolynomial.map_map]

/-- The solutions of the pushed system `φ(P)` over `g` and the solutions of `P` over `g ∘ φ` are
the same subtype of `Fin n → A'`: `MvPolynomial.isSolution_map` is an equality of predicates, so
the identification is the identity on the underlying tuples. -/
def isSolutionMapEquiv :
    {a : Fin n → A' // IsSolution (fun j => MvPolynomial.map φ (P j)) g a} ≃
      {a : Fin n → A' // IsSolution P (g.comp φ) a} :=
  Equiv.subtypeEquivRight (isSolution_map P φ g)

/-- `MvPolynomial.isSolutionMapEquiv` is the identity on the underlying tuple. -/
@[simp]
theorem isSolutionMapEquiv_apply_coe
    (a : {a : Fin n → A' // IsSolution (fun j => MvPolynomial.map φ (P j)) g a}) :
    (isSolutionMapEquiv P φ g a).1 = a.1 :=
  rfl

/-- The inverse of `MvPolynomial.isSolutionMapEquiv` is the identity on the underlying tuple. -/
@[simp]
theorem isSolutionMapEquiv_symm_apply_coe
    (a : {a : Fin n → A' // IsSolution P (g.comp φ) a}) :
    ((isSolutionMapEquiv P φ g).symm a).1 = a.1 :=
  rfl

/-- **The base change of a standard presentation has the expected points.** The ring maps
`A[x₁, …, x_n]/(φP₁, …, φP_n) ⟶ A'` lying over `g : A ⟶ A'` correspond to the ring maps
`R[x₁, …, x_n]/(P₁, …, P_n) ⟶ A'` lying over `g ∘ φ`, a point on either side going to the images
of the variables.

This is the universal property of `A ⊗_R R[x]/(P)`, obtained from the solution calculus rather
than from the tensor product: both sides are the solutions of one system of equations in `A'` by
`MvPolynomial.quotientSpanRangeHomOverEquiv`, and `MvPolynomial.isSolution_map` says those two
solution sets coincide. -/
def homOverMapCoeffEquiv :
    HomOver (fun j => MvPolynomial.map φ (P j)) g ≃ HomOver P (g.comp φ) :=
  (quotientSpanRangeHomOverEquiv g).trans
    ((isSolutionMapEquiv P φ g).trans (quotientSpanRangeHomOverEquiv (g.comp φ)).symm)

/-- The point of `R[x]/(P)` attached to a point `ψ` of the base-changed presentation sends the
class of `p ∈ R[x]` to the evaluation of `p` along `g ∘ φ` at the images under `ψ` of the
variables. -/
@[simp]
theorem homOverMapCoeffEquiv_apply_apply_mk
    (ψ : HomOver (fun j => MvPolynomial.map φ (P j)) g) (p : MvPolynomial (Fin n) R) :
    (homOverMapCoeffEquiv P φ g ψ).1
        (Ideal.Quotient.mk (Ideal.span (Set.range P)) p) =
      MvPolynomial.eval₂Hom (g.comp φ)
        (fun i => ψ.1 (Ideal.Quotient.mk
          (Ideal.span (Set.range fun j => MvPolynomial.map φ (P j))) (MvPolynomial.X i))) p :=
  homOverOfSolution_apply_mk _ _ p

/-- The point of `R[x]/(P)` attached to a point of the base-changed presentation sends each
variable where that point sends it: the identification of
`MvPolynomial.homOverMapCoeffEquiv` is the identity on the coordinates. -/
@[simp]
theorem homOverMapCoeffEquiv_apply_X
    (ψ : HomOver (fun j => MvPolynomial.map φ (P j)) g) (i : Fin n) :
    (homOverMapCoeffEquiv P φ g ψ).1
        (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)) =
      ψ.1 (Ideal.Quotient.mk
        (Ideal.span (Set.range fun j => MvPolynomial.map φ (P j))) (MvPolynomial.X i)) := by
  rw [homOverMapCoeffEquiv_apply_apply_mk, MvPolynomial.eval₂Hom_X']

end MvPolynomial

end
