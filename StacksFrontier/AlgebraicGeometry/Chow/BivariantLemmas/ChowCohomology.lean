module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import Mathlib.Algebra.DirectSum.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Chow cohomology

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a scheme
locally of finite type over `S`. The *Chow cohomology* of `X` is the graded group

  `A^*(X) = ⊕_p A^p(X)`,  where  `A^p(X) = A^p(X ⟶ X)`,

whose degree `p` part is the group of bivariant classes of degree `p` for the identity morphism
of `X`.

## Main definitions

* `Stacks.Chow.chowCohomologyComponent` — **Stacks 0B7E**, the degree `p` part `A^p(X)` of the
  Chow cohomology of `X`, namely `A^p(X ⟶ X)`.
* `Stacks.Chow.chowCohomology` — **Stacks 0B7E**, the graded group `A^*(X)`.

## Implementation notes

Both are abbreviations, so the pointwise abelian group structure on
`Stacks.Chow.BivariantClass` propagates to `A^*(X)` through the `DirectSum` instances with no
further declaration. Degrees range over `ℤ` and a class has finite support, as for the graded
group of Stacks 0FE0; `Stacks.Chow.localizedBivariantGrading` writes the same degree `p` part
out by hand.

The development is stated against a `Stacks.Chow.GysinSystem`, which is the parameter
`Stacks.Chow.BivariantClass` carries; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic` for why a datum of that kind must be a
parameter rather than quantified.

### The multiplication is not carried here

The ring structure of the graded `ℤ`-algebra `A^*(X)` is composition of bivariant classes,
`A^p(X ⟶ X) × A^q(X ⟶ X) ⟶ A^{p+q}(X ⟶ X)`. That composition is constructed in this repository,
as `Stacks.Chow.bivariantCompositeBilinear` (Stacks 0B75), but only for a Gysin system
satisfying the two cases of Stacks 02TA its Gysin naturality needs, so it is not available for an
arbitrary `Stacks.Chow.GysinSystem` and is not installed as a multiplication on the group defined
here. So the graded group is what is defined here;
`Stacks.Chow.completedBivariantComposite` is the corresponding operation on the completion of
Stacks 0FE0.

At the Gysin system of the genuine first Chern class both cases of Stacks 02TA are theorems, and
there the multiplication and the unit of `A^*(X)` are installed, by
`Stacks.Chow.chowCohomologyGradedMul` and `Stacks.Chow.chowCohomologyGradedOne` in
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ChowCohomologyRestriction`; see the
implementation notes there for what of the graded ring structure that does and does not give.

## References

* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **Stacks 0B7E.** The degree `p` part `A^p(X)` of the Chow cohomology of a scheme `X` locally
of finite type over the base: the group `A^p(X ⟶ X)` of bivariant classes of degree `p` for the
identity morphism of `X`. -/
@[stacks 0B7E "the degree p part"]
abbrev chowCohomologyComponent (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ) : Type (u + 1) :=
  BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p

/-- **Stacks 0B7E.** The Chow cohomology `A^*(X)` of a scheme `X` locally of finite type over the
base: the graded group whose degree `p` part is the group `A^p(X ⟶ X)` of bivariant classes of
degree `p` for the identity morphism of `X`. -/
@[stacks 0B7E "the graded group"]
abbrev chowCohomology (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] : Type (u + 1) :=
  DirectSum ℤ fun p ↦ chowCohomologyComponent C G sX p

end Stacks.Chow

end
