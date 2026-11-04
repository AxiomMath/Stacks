module

public import Mathlib.Algebra.Homology.Single
public import StacksFrontier.Algebra.Homology.InternalHomComplex

/-!
# The internal Hom complex into a complex concentrated in one degree

The degree-`n` term of the internal Hom complex `Hom•(K, L)` is the product over `p : ℤ` of
`ihom (K^p) (L^{p+n})`.  When `L` is concentrated in a single degree all but one of those factors
vanish, and the product collapses onto the surviving one: in degree `-n`, for `L` concentrated in
degree `0`, the surviving factor is the one at `p = n`, so

`Hom•(K, L)^{-n} ≅ ihom (K^n) (L^0)`.

This is the identification that reads the terms of the dual of a complex off the terms of the
complex, and it is **unconditional**: it uses nothing about `K`, no boundedness, and above all no
duality pairing.  The pairing-dependent form of it, obtained by transporting along the uniqueness
of left duals, is `Stacks.SheafOfModules.Strict.homComplexUnitIsoDualSheafX`, and that route is
circular wherever the identification is wanted in order to *build* a pairing — which is the case
for the complex-level assembly of [Stacks, Tag 0FP9].

## Main results

* `CategoryTheory.MonoidalClosed.isZero_ihom_obj`: the internal hom into a zero object is zero.
* `CategoryTheory.Limits.isIso_pi_π_of_isZero`: a product almost all of whose factors are zero
  is the surviving factor, via its own projection.
* `CochainComplex.isIso_internalHomπ_of_isZero`: hence the projection out of a degree of
  `Hom•(K, L)` is an isomorphism as soon as the other factors vanish.
* `CochainComplex.internalHomXSingleIso`: the degree-`-n` term of `Hom•(K, (single 0).obj X)`
  is `ihom (K^n) X`.

## Implementation notes

`isZero_ihom_obj` goes through additivity of `ihom X` (`ihom_additive`, which holds because
`X ⊗ -` is additive and `ihom X` is its right adjoint) rather than through preservation of
limits: a right adjoint preserves the terminal object, but being a zero object is terminal *and*
initial, and the initial half is not available from the adjunction alone.

`isIso_pi_π_of_isZero` is stated for `Limits.Pi.π` rather than for a general limit cone because
that is the shape `CochainComplex.internalHomX` is built at; the inverse is the lift whose
components are the identity at `i₀` and zero elsewhere, which needs decidable equality on the
index type and so uses `Classical`.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed

universe w v u

namespace CategoryTheory.Limits

/-- **A product almost all of whose factors are zero is the surviving factor.**  If `f i` is a
zero object for every `i ≠ i₀`, the projection `∏ᶜ f ⟶ f i₀` is an isomorphism.  Its inverse is
the lift whose component at `i₀` is the identity and whose other components are zero. -/
theorem isIso_pi_π_of_isZero {A : Type u} [Category.{v} A] [HasZeroMorphisms A] {I : Type w}
    (f : I → A) [HasProduct f] (i₀ : I) (h : ∀ i, i ≠ i₀ → IsZero (f i)) :
    IsIso (Pi.π f i₀) := by
  classical
  refine ⟨Pi.lift (fun i => if hi : i = i₀ then eqToHom (by rw [hi]) else 0), ?_, ?_⟩
  · refine Pi.hom_ext _ _ fun i => ?_
    rw [Category.assoc, Pi.lift_π, Category.id_comp]
    by_cases hi : i = i₀
    · subst hi
      rw [dite_eq_left rfl, eqToHom_refl, Category.comp_id]
    · rw [dite_eq_right hi, comp_zero]
      exact ((h i hi).eq_of_tgt _ _).symm
  · rw [Pi.lift_π, dite_eq_left rfl, eqToHom_refl]

end CategoryTheory.Limits

namespace CategoryTheory.MonoidalClosed

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [MonoidalClosed A]
  [Preadditive A] [MonoidalPreadditive A]

/-- **The internal hom into a zero object is zero.**  `ihom X` is additive, being right adjoint
to the additive functor `X ⊗ -`, so it carries `𝟙 Y = 0` to `𝟙 (ihom X Y) = 0`. -/
theorem isZero_ihom_obj (X : A) {Y : A} (hY : IsZero Y) : IsZero ((ihom X).obj Y) := by
  rw [IsZero.iff_id_eq_zero] at hY ⊢
  rw [← (ihom X).map_id, hY, (ihom X).map_zero]

end CategoryTheory.MonoidalClosed

namespace CochainComplex

noncomputable section

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [MonoidalClosed A] [Preadditive A]
  [MonoidalPreadditive A] [HasProductsOfShape ℤ A]

/-- **A degree of the internal Hom complex collapses onto a single factor.**  If `L^{p+n}`
vanishes for every `p ≠ p₀`, the projection of `Hom•(K, L)^n` onto its factor at `p₀` is an
isomorphism. -/
theorem isIso_internalHomπ_of_isZero (K L : CochainComplex A ℤ) (n p₀ : ℤ)
    (h : ∀ p : ℤ, p ≠ p₀ → IsZero (L.X (p + n))) :
    IsIso (internalHomπ K L n p₀) :=
  isIso_pi_π_of_isZero _ p₀ fun p hp => isZero_ihom_obj _ (h p hp)

variable [HasZeroObject A]

/-- **The terms of the internal Hom complex into a complex concentrated in degree zero.**  For
`L = (single 0).obj X` only the factor at `p = n` of `Hom•(K, L)^{-n}` survives, so

`Hom•(K, (single 0).obj X)^{-n} ≅ ihom (K^n) X`.

This is the **unconditional** degree identification: no duality pairing between `K` and `L` is
assumed, which is what makes it usable in the construction of such a pairing. -/
def internalHomXSingleIso (K : CochainComplex A ℤ) (X : A) (n : ℤ) :
    internalHomX K ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X) (-n) ≅
      (ihom (K.X n)).obj X :=
  haveI := isIso_internalHomπ_of_isZero K
    ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X) (-n) n
    (fun p hp => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X (p + -n)
      (by omega))
  (asIso (internalHomπ K ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X) (-n) n)).trans
    ((ihom (K.X n)).mapIso
      ((((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X).XIsoOfEq
          (show n + -n = 0 by omega)).trans
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X)))

end

end CochainComplex

end
