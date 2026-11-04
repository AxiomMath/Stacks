module

public import Mathlib.RingTheory.FiniteType
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# The algebraic upper shriek functor

Let `f : R →+* A` be a homomorphism of finite type.  Writing `A` as a quotient of a polynomial
algebra `P = R[x_1, …, x_n]`, the algebraic upper shriek functor is
`f^!(K) = RHom_P(A, K ⊗_R^L P)[n] : D(R) ⥤ D(A)`.  This file records the construction: a
polynomial presentation of `f`, the derived base change it provides, and the resulting functor.

The functor depends on the presentation, and is well defined only up to isomorphism; that
independence is [Stacks, Tag 0BZJ].  Consequently every statement about `f^!` is made here for an
arbitrary presentation rather than for one chosen by `Classical.choice`, which is both stronger
and independent of Tag 0BZJ.

## Main definitions

* `Dualizing.PolynomialPresentation` — a presentation of a ring homomorphism as a quotient of a
  polynomial algebra in finitely many variables.
* `Dualizing.PolynomialPresentation.derivedExtension` — derived base change `- ⊗_R^L P` along the
  polynomial algebra of a presentation.
* `Dualizing.PolynomialPresentation.upperShriekFunctor` — the algebraic upper shriek functor
  attached to a presentation.

## Main results

* `Dualizing.nonempty_polynomialPresentation` — a homomorphism of finite type admits a polynomial
  presentation, so the construction applies to it.

## Implementation notes

A polynomial algebra is free, hence flat, over its coefficient ring, so extension of scalars along
`MvPolynomial.C` is exact and its derived functor is computed degreewise; this is what
`derivedExtension` packages.  Derived Hom along the surjection is `Dualizing.derivedHom`, the
derived coextension of scalars of [Stacks, Tag 0A70].

## References

* [Stacks Project, Tag 0BZI](https://stacks.math.columbia.edu/tag/0BZI)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable {R A : Type u} [CommRing R] [CommRing A]

/-- A presentation of `f : R →+* A` as a quotient of a polynomial algebra over `R` in finitely
many variables. -/
structure PolynomialPresentation (f : R →+* A) where
  /-- The number of polynomial variables. -/
  variableCount : ℕ
  /-- The surjection from the polynomial algebra onto the target. -/
  toRingHom : MvPolynomial (Fin variableCount) R →+* A
  /-- The surjection is a homomorphism of `R`-algebras realizing `f`. -/
  commutes : toRingHom.comp MvPolynomial.C = f
  /-- The homomorphism onto the target is surjective. -/
  surjective : Function.Surjective toRingHom

namespace PolynomialPresentation

variable {f : R →+* A}

/-- The polynomial algebra of a presentation. -/
abbrev Poly (p : PolynomialPresentation f) : Type u := MvPolynomial (Fin p.variableCount) R

/-- The structure map of the polynomial algebra of a presentation is flat, the polynomial algebra
being free over its coefficient ring. -/
theorem flat_C (p : PolynomialPresentation f) :
    (MvPolynomial.C : R →+* p.Poly).Flat :=
  RingHom.flat_algebraMap_iff.mpr inferInstance

/-- **The surjection of a polynomial presentation as a homomorphism of `R`-algebras.**  When the
presented ring map is the structure map of an `R`-algebra `A`, the surjection `P → A` of a
presentation commutes with the two structure maps — that is
`Dualizing.PolynomialPresentation.commutes` — so it is a homomorphism of `R`-algebras.

Every consumer that feeds a presentation to a statement about algebra maps needs it in this form:
`Dualizing.torIndependent_mvPolynomialBaseChange` for the Tor-independence of a presentation
square, and the perfectness criteria of [stacks 068Y] for
`Dualizing.PolynomialPresentation.isPerfectModule_of_flat`. -/
def toAlgHom [Algebra R A] (p : PolynomialPresentation (algebraMap R A)) : p.Poly →ₐ[R] A :=
  AlgHom.mk p.toRingHom fun r ↦ congrArg (· r) p.commutes

/-- The surjection of a presentation is a finite ring homomorphism. -/
theorem finite_toRingHom (p : PolynomialPresentation f) : p.toRingHom.Finite :=
  RingHom.Finite.of_surjective p.toRingHom p.surjective

/-- A homomorphism admitting a polynomial presentation is of finite type; together with
`Dualizing.nonempty_polynomialPresentation` this says that polynomial presentations exist exactly
for the finite type homomorphisms. -/
theorem finiteType (p : PolynomialPresentation f) : f.FiniteType := by
  let : Algebra R A := f.toAlgebra
  show Algebra.FiniteType R A
  exact Algebra.FiniteType.of_surjective p.toAlgHom p.surjective

/-- Derived base change `- ⊗_R^L P` along the polynomial algebra `P` of a presentation.  It is
computed degreewise because `P` is flat over `R`. -/
noncomputable def derivedExtension (p : PolynomialPresentation f) :
    DerivedCategory (ModuleCat.{max v u} R) ⥤ DerivedCategory (ModuleCat.{max v u} p.Poly) :=
  letI : Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _ p.flat_C
  (ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)).mapDerivedCategory

/-- The algebraic upper shriek functor attached to a polynomial presentation `p` of `f`:
`K ↦ RHom_P(A, K ⊗_R^L P)[n]`, where `P` is the polynomial algebra of `p` and `n` its number of
variables. -/
noncomputable def upperShriekFunctor (p : PolynomialPresentation f) :
    DerivedCategory (ModuleCat.{max v u} R) ⥤ DerivedCategory (ModuleCat.{max v u} A) :=
  p.derivedExtension.{u, v} ⋙ derivedHom.{u, v, u} p.toRingHom ⋙
    shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (p.variableCount : ℤ)

/-- The upper shriek functor of `p` sends `K` to `RHom_P(A, K ⊗_R^L P)[n]`, where `n` is the
number of variables of `p`. -/
theorem upperShriekFunctor_obj (p : PolynomialPresentation f)
    (K : DerivedCategory (ModuleCat.{max v u} R)) :
    p.upperShriekFunctor.{u, v}.obj K =
      ((derivedHom.{u, v, u} p.toRingHom).obj (p.derivedExtension.{u, v}.obj K))⟦
        (p.variableCount : ℤ)⟧ :=
  rfl

end PolynomialPresentation

/-- A homomorphism of finite type admits a polynomial presentation. -/
theorem nonempty_polynomialPresentation (f : R →+* A) (hf : f.FiniteType) :
    Nonempty (PolynomialPresentation f) := by
  let : Algebra R A := f.toAlgebra
  have : Algebra.FiniteType R A := hf
  obtain ⟨n, g, hg⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  exact ⟨n, g.toRingHom, by ext r; exact g.commutes r, hg⟩

end Dualizing

end
