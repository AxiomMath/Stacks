module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsChartSquare
public import StacksFrontier.RingTheory.Etale.DirectedColimitPresentation
public import StacksFrontier.RingTheory.Etale.DirectedColimitPresentationSupplement

/-!
# The standard-étale presentation of an étale chart of an affine algebraic space

Let `U ⟶ V` be a morphism of the big fppf site of `S` whose underlying schemes are affine and
which is étale as a morphism of the presheaves it represents. Then restriction of global
functions

`Γ(V, 𝒪) ⟶ Γ(U, 𝒪)`

is an étale ring map, and therefore has a standard-étale presentation: `Γ(U, 𝒪)` is
`Γ(V, 𝒪)[x₁, …, xₙ] ⧸ (g₁, …, gₙ)` with the Jacobian determinant of the `g` invertible.

This is the step of the proof of Stacks 07SQ in which the étale chart of the affine limit is
written ring-theoretically — the appeal the source makes to Algebra, Lemma 10.143.2
(Stacks 00U9) — and it is given here in the shape the rest of that proof consumes: the
coordinates `h₁, …, hₙ` come out as global functions on `U` killing the `g`, which is exactly
the data `AlgebraicGeometry.Space.commSq_chart_specOfGlobalFunctions` (Stacks 084U) asks for,
and the homomorphism `AlgebraicGeometry.Space.coordinateHom` they determine is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.etale_appTop_of_isEtale`: restriction of global functions along an
  étale morphism of *affine* objects of the site is an étale ring map.
* `AlgebraicGeometry.Space.exists_standardEtalePresentation_of_isEtale`: the presentation
  itself, as a ring isomorphism out of `AlgebraicGeometry.Space.presentationAlgebra`.
* `AlgebraicGeometry.Space.exists_coordinateHom_bijective_of_isEtale`: the same presentation in
  coordinates — polynomials `g`, global functions `h` on `U` with `g_λ(h) = 0`, invertible
  Jacobian determinant, and `AlgebraicGeometry.Space.coordinateHom` bijective.

## Implementation notes

*The two halves.* The passage from the presheaf-level property to the scheme-level one is
`AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda` followed by
`AlgebraicGeometry.Space.presheaf_yoneda_map_etale_iff`, which is available because étaleness of
morphisms of schemes is stable under base change. The passage from the scheme-level property to
the ring-level one is Mathlib's `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine` for the
instance `HasRingHomProperty @Etale RingHom.Etale`, which needs both schemes affine. The
ring-level presentation is `RingHom.exists_isUnit_detJacobian_of_etale`.

*Why the coordinates come out and not just the abstract isomorphism.* The square of Stacks 084U
is formed from a family of global functions on the chart killing the relations, not from an
abstract isomorphism, and `AlgebraicGeometry.Space.ringHom_comp_quotientMk_eq_eval₂Hom`
identifies the two: a homomorphism out of the presentation is evaluation at the images of the
variables, so the relations are killed because they are zero in the quotient, and
`AlgebraicGeometry.Space.coordinateHom` at that family is the presentation isomorphism itself.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MvPolynomial

universe u

namespace AlgebraicGeometry.Space

/-! ### A homomorphism out of a presentation is evaluation at the variables -/

/-- **A ring homomorphism out of a presentation is evaluation at the images of the variables.**
If `k : A[x] ⧸ (g) →+* R` restricts along the structure homomorphism to `ψ`, then `k` composed
with the quotient map is `MvPolynomial.eval₂Hom ψ h` for `h` the family of images of the classes
of the variables. Both sides are ring homomorphisms out of a polynomial ring, so they agree as
soon as they agree on the constants and on the variables. -/
theorem ringHom_comp_quotientMk_eq_eval₂Hom {A R : Type u} [CommRing A] [CommRing R] {n : ℕ}
    (g : Fin n → MvPolynomial (Fin n) A) (ψ : A →+* R) (k : presentationAlgebra g →+* R)
    (hk : k.comp (presentationStructureHom g) = ψ) :
    k.comp (Ideal.Quotient.mk (Ideal.span (Set.range g)))
      = MvPolynomial.eval₂Hom ψ
          (fun ν => k (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X ν))) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun ν => ?_)
  · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
    exact RingHom.congr_fun hk a
  · simp

/-- **The relations of a presentation are killed by the images of the variables.** -/
theorem eval₂_eq_zero_of_comp_eq {A R : Type u} [CommRing A] [CommRing R] {n : ℕ}
    (g : Fin n → MvPolynomial (Fin n) A) (ψ : A →+* R) (k : presentationAlgebra g →+* R)
    (hk : k.comp (presentationStructureHom g) = ψ) (l : Fin n) :
    MvPolynomial.eval₂ ψ
        (fun ν => k (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X ν))) (g l)
      = 0 := by
  have h0 : Ideal.Quotient.mk (Ideal.span (Set.range g)) (g l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨l, rfl⟩)
  have hz : MvPolynomial.eval₂Hom ψ
      (fun ν => k (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X ν))) (g l)
      = 0 := by
    rw [← ringHom_comp_quotientMk_eq_eval₂Hom g ψ k hk, RingHom.comp_apply, h0, map_zero]
  simpa using hz

/-- **`coordinateHom` at the images of the variables is the homomorphism one started from.**
Both lift `MvPolynomial.eval₂Hom` through the quotient map, and the quotient map is
surjective. -/
theorem coordinateHom_eq_of_comp_eq {A R : Type u} [CommRing A] [CommRing R] {n : ℕ}
    (g : Fin n → MvPolynomial (Fin n) A) (ψ : A →+* R) (k : presentationAlgebra g →+* R)
    (hk : k.comp (presentationStructureHom g) = ψ) :
    coordinateHom g ψ
        (fun ν => k (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X ν)))
        (eval₂_eq_zero_of_comp_eq g ψ k hk) = k := by
  refine RingHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (RingHom.congr_fun (ringHom_comp_quotientMk_eq_eval₂Hom g ψ k hk) p).symm

/-! ### The presentation of an étale chart -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Restriction of global functions along an étale morphism of affine objects of the site is an
étale ring map.** Étaleness of a morphism of presheaves between two representables is étaleness
of the morphism of schemes, and étaleness of morphisms of schemes is a ring-homomorphism
property, so between affine schemes it is `RingHom.Etale` of the map on global sections. -/
theorem etale_appTop_of_isEtale {U V : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (φ : U ⟶ V) (h : IsEtale B S hS (yoneda.map φ)) :
    RingHom.Etale ((BigFppfOver.toScheme B S hS).map φ).appTop.hom := by
  have _ := hU
  have _ := hV
  exact (HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale.{u})
      (f := (BigFppfOver.toScheme B S hS).map φ)).1
    ((presheaf_yoneda_map_etale_iff B S hS φ).1
      ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map φ)).1 h))

/-- **The standard-étale presentation of an étale morphism of affine objects of the site.**
There are finitely many polynomials `g₁, …, gₙ` in as many variables over `Γ(V, 𝒪)`, whose
Jacobian determinant is invertible in the quotient, and an isomorphism of the quotient with
`Γ(U, 𝒪)` carrying the structure homomorphism of the presentation to restriction of functions
along `φ`.

This is the appeal to Stacks 00U9 in the proof of Stacks 07SQ, at the étale chart of an affine
algebraic space. -/
theorem exists_standardEtalePresentation_of_isEtale {U V : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (φ : U ⟶ V) (h : IsEtale B S hS (yoneda.map φ)) :
    ∃ (n : ℕ) (g : Fin n → MvPolynomial (Fin n) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      (ε : presentationAlgebra g ≃+* Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)),
      IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g)) ∧
        ε.toRingHom.comp (presentationStructureHom g)
          = ((BigFppfOver.toScheme B S hS).map φ).appTop.hom :=
  RingHom.exists_isUnit_detJacobian_of_etale (etale_appTop_of_isEtale B S hS hU hV φ h)

/-- **The standard-étale presentation in coordinates.** For an étale morphism `φ : U ⟶ V` of
affine objects of the site there are polynomials `g₁, …, gₙ` in `n` variables over `Γ(V, 𝒪)`
with invertible Jacobian determinant and global functions `h₁, …, hₙ` on `U` with
`g_λ(h₁, …, hₙ) = 0`, such that the homomorphism `AlgebraicGeometry.Space.coordinateHom` they
determine is a bijection.

This is the data the square of Stacks 084U is formed from. -/
theorem exists_coordinateHom_bijective_of_isEtale {U V : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (φ : U ⟶ V) (hφ : IsEtale B S hS (yoneda.map φ)) :
    ∃ (n : ℕ) (g : Fin n → MvPolynomial (Fin n) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      (h : Fin n → Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
      (hrel : ∀ l, MvPolynomial.eval₂
        ((BigFppfOver.toScheme B S hS).map φ).appTop.hom h (g l) = 0),
      IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g)) ∧
        Function.Bijective (coordinateHom g
          ((BigFppfOver.toScheme B S hS).map φ).appTop.hom h hrel) := by
  obtain ⟨n, g, ε, hunit, hcomp⟩ :=
    exists_standardEtalePresentation_of_isEtale B S hS hU hV φ hφ
  refine ⟨n, g,
    fun ν => ε.toRingHom (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X ν)),
    eval₂_eq_zero_of_comp_eq g _ ε.toRingHom hcomp, hunit, ?_⟩
  rw [coordinateHom_eq_of_comp_eq g _ ε.toRingHom hcomp]
  exact ε.bijective

end AlgebraicGeometry.Space

end
