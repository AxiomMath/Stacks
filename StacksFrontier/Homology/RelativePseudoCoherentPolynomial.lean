module

public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.KoszulPushforward

/-!
# Adjoining variables to a relatively pseudo-coherent algebra

Let `R → A` be a finite-type ring map and suppose `A` is pseudo-coherent relative to `R`
(Stacks 065I). Adjoining finitely many variables preserves that: `A[y₁, …, yₙ]` is again
pseudo-coherent relative to `R`.

## Main results

* `PseudoCoherence.isModuleRelativelyPseudoCoherentFrom_mvPolynomial_of_relative` is the
  statement in a fixed degree `m`.
* `PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_of_relative` is the statement
  in every degree.

## Implementation notes

Both are Stacks 067D (`PseudoCoherence.relativelyPseudoCoherent_iff_of_comp`) applied to the
tower `R → A → A[y₁, …, yₙ]`, whose top step is relatively pseudo-coherent by
`PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_self`. No separate flat
base-change argument is needed: Stacks 067D already contains the one the source uses
(Stacks 066C applied to `R[x₁, …, x_k] → R[x₁, …, x_k, y₁, …, yₙ]`).

The intended consumer is the side condition of Stacks 09VA over a base `S`, that is
`AlgebraicGeometry.Scheme.Modules.PushforwardStructureSheafPseudoCoherentOver S (𝔸ⁿ_V) _`
for an affine open `V ⊆ S`. The lemma
`AlgebraicGeometry.Scheme.Modules.pushforwardStructureSheafPseudoCoherentOver_affineSpace`
discharges that only for `V` a *standard* open of `S`, where `Γ(V, ⊤)` is a localization of
`Γ(S, ⊤)`; for an arbitrary affine open the hypothesis below is what replaces the
localization, and it is what pseudo-coherence of the base morphism supplies through
`AlgebraicGeometry.PseudoCoherent.pseudoCoherent_appLE`.

## References

* [Stacks Project, Tag 067D](https://stacks.math.columbia.edu/tag/067D)
* [Stacks Project, Tag 065I](https://stacks.math.columbia.edu/tag/065I)
-/

@[expose] public section

open CategoryTheory

universe u

namespace PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

/-- Adjoining finitely many variables to a relatively `m`-pseudo-coherent algebra, in a fixed
degree: if `A` is pseudo-coherent relative to `R`, then `A[y₁, …, yₙ]` is `m`-pseudo-coherent
relative to `R` as a module over itself, for every `m`.

The hypothesis is relative pseudo-coherence of `A` in *every* degree because that is what
Stacks 067D consumes. -/
public theorem isModuleRelativelyPseudoCoherentFrom_mvPolynomial_of_relative
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (n : ℕ)
    (hA : IsModuleRelativelyPseudoCoherent (R := R) (A := A) A) (m : ℤ) :
    IsModuleRelativelyPseudoCoherentFrom (R := R) (A := MvPolynomial (Fin n) A)
      (MvPolynomial (Fin n) A) m :=
  (relativelyPseudoCoherent_iff_of_comp (R := R) (A := A) (B := MvPolynomial (Fin n) A) hA
    _ m).1.mp (isModuleRelativelyPseudoCoherentFrom_mvPolynomial_self A n m)

/-- **Adjoining finitely many variables preserves relative pseudo-coherence.** If `A` is a
finite-type `R`-algebra that is pseudo-coherent relative to `R`, then so is `A[y₁, …, yₙ]`.

This is Stacks 067D for the tower `R → A → A[y₁, …, yₙ]`, together with
`PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_self` for its top step. -/
public theorem isModuleRelativelyPseudoCoherent_mvPolynomial_of_relative
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (n : ℕ)
    (hA : IsModuleRelativelyPseudoCoherent (R := R) (A := A) A) :
    IsModuleRelativelyPseudoCoherent (R := R) (A := MvPolynomial (Fin n) A)
      (MvPolynomial (Fin n) A) :=
  (relativelyPseudoCoherent_iff_of_comp (R := R) (A := A) (B := MvPolynomial (Fin n) A) hA
    _ 0).2.mp (isModuleRelativelyPseudoCoherent_mvPolynomial_self A n)

end PseudoCoherence

end
