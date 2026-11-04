module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresents
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionRepresentable

/-!
# The glued relative Proj represents the functor of quadruples

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN). The functor
`F : Sch^{opp} ⟶ Sets` of the display 01NX is constructed, as
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.limFunctor`: on a quasi-compact test scheme its
value is the union over `d ≥ 1` of the sets `F_d(T)` of strict equivalence classes of quadruples,
which is `...RelativeProjQcohSheaf.F.functor`, and on a general test scheme it is the inverse
limit of those over the quasi-compact opens, which is what the source defines `F(T)` to be there;
its value on a morphism of test schemes is the pullback of a quadruple, and both functor laws are
proved. This file transports a representation of *that* functor along the canonical isomorphism of
Tag 01NZ, so that the relative homogeneous spectrum `Proj_S(A)` of Lemma 01NQ represents it.

The functor represented is `F.limFunctor` and not the raw union `F.functor`: on a test scheme
that is not quasi-compact a morphism need not factor through any single `U_d`, which is why the
source takes the inverse limit there, so `F.functor` realizes the display only on the
quasi-compact test schemes.

The representation transported is a hypothesis `hrep`, that a scheme over `S` carrying the same
projective-spectrum charts represents `F`, which is Tag 01NY. By
`...RelativeProjQcohSheaf.representableByEquiv` the two representability statements are
equivalent.

## Main results

* `...RelativeProjQcohSheaf.relativeProjRepresentableByFunctor`: `Proj_S(A)` represents the
  functor `F` of the display 01NX, given a scheme over `S` with the same projective-spectrum
  charts which represents it.
* `...RelativeProjQcohSheaf.canonicalTwistQuotientEquiv` and `exists_canonicalTwistQuotient`:
  **the universal graded-twist quotient**, that is, the same statement unwound into the quotient
  language of Section 01NS — on a quasi-compact test scheme the morphisms to `Proj_S(A)` are the
  graded-twist quotients `ψ : f^*A^{(d)} ⟶ ⨁_n L^{⊗ n}` of positive degree, modulo the
  identifications, and every one of them is the pullback of the universal one.

## References

* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Definition 01O0](https://stacks.math.columbia.edu/tag/01O0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- The relative homogeneous spectrum `Proj_S(A)` of Lemma 01NQ represents the functor `F` of
the display 01NX, through the canonical isomorphism over `S` (Stacks 01NZ,
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.existsUnique_isoOver`) with a scheme carrying the
same projective-spectrum charts which represents `F`. -/
def relativeProjRepresentableByFunctor (P : RelativeProjData A)
    (hrep : (F.limFunctor (situationAlgebra A)).RepresentableBy P.scheme) :
    (F.limFunctor (situationAlgebra A)).RepresentableBy (relativeProj A).scheme :=
  representableByEquiv A P (F.limFunctor (situationAlgebra A)) hrep

/-- The morphism to `Proj_S(A)` attached to a point of `F` is the one to the given representing
scheme followed by the canonical isomorphism. -/
@[simp]
theorem relativeProjRepresentableByFunctor_homEquiv_symm (P : RelativeProjData A)
    (hrep : (F.limFunctor (situationAlgebra A)).RepresentableBy P.scheme) {T : Scheme.{u}}
    (ξ : (F.limFunctor (situationAlgebra A)).obj (op T)) :
    (relativeProjRepresentableByFunctor A P hrep).homEquiv.symm ξ =
      hrep.homEquiv.symm ξ ≫ (canonicalIso A P).inv :=
  rfl

/-! ### The canonical graded-twist quotient on the relative Proj -/

variable (P : RelativeProjData A)
  (hrep : (F.limFunctor (situationAlgebra A)).RepresentableBy P.scheme)
  (W : Scheme.{u}) (hW : CompactSpace W)

/-- **The relative homogeneous spectrum classifies graded-twist quotients.** For a quasi-compact
test scheme `W`, the morphisms `W ⟶ Proj_S(𝒜)` correspond bijectively to the points of `F(W)`,
that is, to the graded-twist quotients over `W` of positive degree modulo the identifications of
Section 01NS and Tag 01NW: a quadruple over `W` is an invertible `𝒪_W`-module `ℒ`, a homomorphism
`ψ : f^*𝒜^{(d)} ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}` of graded algebras, and the requirement that the degree-one
component `f^*𝒜_d ⟶ ℒ` of `ψ` be **surjective**.

The bijection is `relativeProjRepresentableByFunctor` followed by
`...RelativeProjQcohSheaf.F.limEquiv`, which on a quasi-compact test scheme identifies the
inverse limit of the display 01NX with the union `F(W)` itself. -/
def canonicalTwistQuotientEquiv :
    (W ⟶ (relativeProj A).scheme) ≃ F (situationAlgebra A) W :=
  ((relativeProjRepresentableByFunctor A P hrep).homEquiv (X := W)).trans
    (F.limEquiv (situationAlgebra A) W hW)

/-- **Every graded-twist quotient over a quasi-compact test scheme is a pullback of the universal
one.** The point of `F(W)` attached to `g : W ⟶ Proj_S(𝒜)` is the pullback along `g` of the point
the identity of `Proj_S(𝒜)` is sent to, which is the universal element of the display 01NX at the
relative homogeneous spectrum. -/
theorem canonicalTwistQuotientEquiv_eq_pullback (g : W ⟶ (relativeProj A).scheme) :
    canonicalTwistQuotientEquiv A P hrep W hW g =
      F.limEquiv (situationAlgebra A) W hW
        ((F.limFunctor (situationAlgebra A)).map g.op
          ((relativeProjRepresentableByFunctor A P hrep).homEquiv
            (𝟙 (relativeProj A).scheme))) :=
  congrArg (F.limEquiv (situationAlgebra A) W hW)
    (Functor.RepresentableBy.homEquiv_eq (relativeProjRepresentableByFunctor A P hrep) g)

/-- **The graded-twist quotient of a morphism to the relative Proj, as a quadruple.** For a
quasi-compact test scheme `W` and a morphism `g : W ⟶ Proj_S(𝒜)` there are a positive degree `d`
and a quadruple of that degree over the morphism `W ⟶ S` the point of `F(W)` records whose class
is the point `g` corresponds to. -/
theorem exists_canonicalTwistQuotient (g : W ⟶ (relativeProj A).scheme) :
    ∃ (d : ℤ) (hd : 0 < d)
      (Q : Quadruple (canonicalTwistQuotientEquiv A P hrep W hW g).1 (situationAlgebra A) d),
      F.mk _ hd Q = canonicalTwistQuotientEquiv A P hrep W hW g :=
  F.exists_quadruple _

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
