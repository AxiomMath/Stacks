module

public import StacksFrontier.RingTheory.Cotangent.StandardResolution

/-!
# A polynomial algebra read over `A[x]` through one of its variables

Let `A[ι]` be a polynomial algebra and let `i₀ : ι` be one of its variables. Sending `x` to
`X i₀` makes `A[ι]` an algebra over `A[x]`, and it is then **again a polynomial algebra**, on the
remaining variables `{i : ι // i ≠ i₀}`.

This is the first step of the route recorded in the implementation notes of
`StacksFrontier/Cotangent/ProductDecomposition.lean` for the descent of [Stacks, Tag 08SC] from the
base `A[x]` to the base `A`. There the algebra is a term `Pₙ` of the standard resolution
`P_•(C/A)` of `C` over `A`, the variable is the iterated polynomial generator of the image of `x`
in `C`, and what is wanted is condition (1) of a resolution (`CommAlgCat.IsResolution`) for
`P_•(C/A)` read over `A[x]`: every term a polynomial algebra over `A[x]`. That is exactly the
statement proved here.

## Main results

* `MvPolynomial.isPolynomialAlgebra_polynomial_of_X`: **`A[ι]`, read over `A[x]` by `x ↦ X i₀`,
  is a polynomial algebra over `A[x]`** — on `{i : ι // i ≠ i₀}`.
* `MvPolynomial.isPolynomialAlgebra_polynomial_of_algEquiv_X`: the same for any algebra presented
  as `A[ι]` by a chosen `A`-algebra equivalence, read over `A[x]` through the image of a
  variable. This is the form the route consumes, the presentation of a term of the standard
  resolution as a polynomial algebra being a chosen equivalence
  (`CommAlgCat.standardResolution_obj_isPolynomialAlgebra`).

## Implementation notes

The equivalence `A[x][{i // i ≠ i₀}] ≃ₐ[A[x]] A[ι]` is built by hand from the two evident
`aeval`s rather than assembled out of `MvPolynomial.sumAlgEquiv` and
`MvPolynomial.renameEquiv` along a splitting `{i // i ≠ i₀} ⊕ PUnit ≃ ι`. The reason is that
either way the composite has to be shown `A[x]`-linear, which is a check on `x` alone
(`Polynomial.algHom_ext`); with the `aeval`s the forward map is `A[x]`-linear by construction
and only the backward one needs the check, whereas with the chain of standard equivalences
neither is and the splitting equivalence has to be transported through all three.

Deciding `i = i₀` needs `DecidableEq ι`, which is taken classically.

## References

* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- **A polynomial algebra, read over `A[x]` by sending `x` to one of its variables, is a
polynomial algebra over `A[x]` on the remaining variables.**

The forward map `A[x][{i // i ≠ i₀}] ⟶ A[ι]` sends the variable indexed by `j` to `X j`, and is
`A[x]`-linear by construction; its inverse sends `X i₀` to the coefficient `x` and every other
`X i` to the variable indexed by `i`. -/
theorem isPolynomialAlgebra_polynomial_of_X {A : Type u} [CommRing A] {ι : Type u} (i₀ : ι) :
    letI : Algebra (Polynomial A) (MvPolynomial ι A) :=
      (Polynomial.aeval (MvPolynomial.X i₀ : MvPolynomial ι A)).toRingHom.toAlgebra
    Algebra.IsPolynomialAlgebra (Polynomial A) (MvPolynomial ι A) := by
  classical
  let : Algebra (Polynomial A) (MvPolynomial ι A) :=
    (Polynomial.aeval (MvPolynomial.X i₀ : MvPolynomial ι A)).toRingHom.toAlgebra
  have hmap : ∀ p : Polynomial A, algebraMap (Polynomial A) (MvPolynomial ι A) p =
      Polynomial.aeval (MvPolynomial.X i₀ : MvPolynomial ι A) p := fun p => by
    rw [RingHom.algebraMap_toAlgebra]; rfl
  have : IsScalarTower A (Polynomial A) (MvPolynomial ι A) :=
    IsScalarTower.of_algebraMap_eq fun a => by rw [hmap]; simp
  refine ⟨{i : ι // i ≠ i₀}, ⟨?_⟩⟩
  let f : MvPolynomial {i : ι // i ≠ i₀} (Polynomial A) →ₐ[Polynomial A] MvPolynomial ι A :=
    MvPolynomial.aeval fun j => MvPolynomial.X j.1
  let g₀ : MvPolynomial ι A →ₐ[A] MvPolynomial {i : ι // i ≠ i₀} (Polynomial A) :=
    MvPolynomial.aeval fun i =>
      if h : i = i₀ then MvPolynomial.C Polynomial.X else MvPolynomial.X ⟨i, h⟩
  have hfX : ∀ j : {i : ι // i ≠ i₀}, f (MvPolynomial.X j) = MvPolynomial.X j.1 := fun j => by
    simp [f]
  have hfC : ∀ p : Polynomial A, f (MvPolynomial.C p) =
      Polynomial.aeval (MvPolynomial.X i₀ : MvPolynomial ι A) p := fun p =>
    (f.commutes p).trans (hmap p)
  have hg : ∀ p : Polynomial A, g₀ (algebraMap (Polynomial A) (MvPolynomial ι A) p) =
      algebraMap (Polynomial A) (MvPolynomial {i : ι // i ≠ i₀} (Polynomial A)) p := by
    have key : g₀.comp (IsScalarTower.toAlgHom A (Polynomial A) (MvPolynomial ι A)) =
        IsScalarTower.toAlgHom A (Polynomial A)
          (MvPolynomial {i : ι // i ≠ i₀} (Polynomial A)) := by
      refine Polynomial.algHom_ext ?_
      change g₀ (algebraMap (Polynomial A) (MvPolynomial ι A) Polynomial.X) = _
      simp [hmap, g₀]
    exact fun p => AlgHom.congr_fun key p
  let g : MvPolynomial ι A →ₐ[Polynomial A] MvPolynomial {i : ι // i ≠ i₀} (Polynomial A) :=
    { g₀.toRingHom with commutes' := hg }
  have hgX : ∀ i : ι, g (MvPolynomial.X i) =
      if h : i = i₀ then MvPolynomial.C Polynomial.X else MvPolynomial.X ⟨i, h⟩ := fun i => by
    simp [g, g₀]
  have hgC : ∀ a : A, g (MvPolynomial.C a) = MvPolynomial.C (Polynomial.C a) := fun a => by
    simp [g, g₀]
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · refine AlgHom.toRingHom_injective (MvPolynomial.ringHom_ext ?_ ?_)
    · intro a
      change f (g (MvPolynomial.C a)) = MvPolynomial.C a
      rw [hgC, hfC]
      simp
    · intro i
      change f (g (MvPolynomial.X i)) = MvPolynomial.X i
      rw [hgX]
      by_cases h : i = i₀
      · subst h
        simp only [↓reduceDIte]
        rw [hfC]
        simp
      · rw [dite_eq_right h, hfX]
  · refine MvPolynomial.algHom_ext fun j => ?_
    change g (f (MvPolynomial.X j)) = MvPolynomial.X j
    rw [hfX, hgX, dite_eq_right j.2]

/-- **The same, for an algebra presented as a polynomial algebra by a chosen equivalence.** If
`e : A[ι] ≃ₐ[A] P` and `i₀ : ι`, then `P` read over `A[x]` by `x ↦ e (X i₀)` is a polynomial
algebra over `A[x]`.

This is the form the descent of [Stacks, Tag 08SC] consumes: `CommAlgCat.IsResolution` asks for
`Algebra.IsPolynomialAlgebra` of each term of the resolution, which is an existence statement
whose witness is such an equivalence, and the element the base `A[x]` must be sent to is the
image under it of one variable. -/
theorem isPolynomialAlgebra_polynomial_of_algEquiv_X {A P : Type u} [CommRing A] [CommRing P]
    [Algebra A P] {ι : Type u} (e : MvPolynomial ι A ≃ₐ[A] P) (i₀ : ι) :
    letI : Algebra (Polynomial A) P :=
      (Polynomial.aeval (e (MvPolynomial.X i₀))).toRingHom.toAlgebra
    Algebra.IsPolynomialAlgebra (Polynomial A) P := by
  let : Algebra (Polynomial A) (MvPolynomial ι A) :=
    (Polynomial.aeval (MvPolynomial.X i₀ : MvPolynomial ι A)).toRingHom.toAlgebra
  let : Algebra (Polynomial A) P :=
    (Polynomial.aeval (e (MvPolynomial.X i₀))).toRingHom.toAlgebra
  obtain ⟨κ, ⟨e'⟩⟩ := isPolynomialAlgebra_polynomial_of_X (A := A) i₀
  have key : e.toAlgHom.comp (Polynomial.aeval (MvPolynomial.X i₀ : MvPolynomial ι A)) =
      Polynomial.aeval (e (MvPolynomial.X i₀)) := Polynomial.algHom_ext (by simp)
  refine ⟨κ, ⟨e'.trans (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun p => ?_)⟩⟩
  change e (algebraMap (Polynomial A) (MvPolynomial ι A) p) = algebraMap (Polynomial A) P p
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
  exact AlgHom.congr_fun key p

end MvPolynomial

end
