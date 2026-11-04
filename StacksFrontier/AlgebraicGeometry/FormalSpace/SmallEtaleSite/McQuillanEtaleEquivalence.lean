module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallEtaleSite.EtaleCompletionEquivalence

/-!
# Stacks 0DEF: the small affine étale site of a McQuillan affine formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `X = Spf A` be a McQuillan affine
formal algebraic space over `S`, so `A` is a weakly admissible topological ring presented over
`S` by a quotient system `D` whose atlas lies in the site. **Stacks 0DEF** asserts that
`(X_{affine,étale})^{opp}` is equivalent to the category whose

1. objects are the `A`-algebras `B^∧ = lim B/JB`, for `A → B` an étale ring map and `J` running
   over the weak ideals of definition of `A`, and
2. morphisms are the continuous `A`-algebra homomorphisms.

That category is `AlgebraicGeometry.FormalSpace.EtaleCompletion`, built in
`StacksFrontier/AlgebraicGeometry/FormalSpace/SmallEtaleSite/McQuillanAffineEtale.lean`; this file
assembles the equivalence.

## Main definitions

* `AlgebraicGeometry.FormalSpace.mcQuillanAffineEtaleEquivalence`: **Stacks 0DEF**, the
  equivalence `(X_{affine,étale})^{opp} ≌ EtaleCompletion A`.

## Implementation notes

The proof is the source's: "combine Lemmas 0DEE and 0AN8". Both inputs are available in this
library as genuine equivalences, so nothing is left to do but compose them.

* Stacks 0DEE is `AlgebraicGeometry.FormalSpace.affineEtaleEquivalence`, which identifies
  `X_{affine,étale}` — the affine étale site of the reduction of `X`, in the sense of Stacks
  0DEA part (3) — with `AlgebraicGeometry.FormalSpace.AffineEtaleFormalCharts`, the category of
  the morphisms `U ⟶ X` of formal algebraic spaces with `U` an affine formal algebraic space and
  the morphism representable by algebraic spaces and étale.
* Stacks 0AN8 is `AlgebraicGeometry.FormalSpace.isEquivalence_etaleCompletionCharts`, which says
  that `AlgebraicGeometry.FormalSpace.etaleCompletionCharts`, the functor `B^∧ ↦ Spf (B^∧)` out
  of `(EtaleCompletion A)ᵒᵖ`, is an equivalence onto that same category of charts.

Composing, `X_{affine,étale} ≌ (EtaleCompletion A)ᵒᵖ`, and `CategoryTheory.Equivalence.leftOp`
turns that into `(X_{affine,étale})^{opp} ≌ EtaleCompletion A`, which is how Stacks 0DEF writes
it. That is the whole of the variance bookkeeping: `Spf` is contravariant, so Stacks 0AN8 is
realized on the opposite of the category of the algebras `B^∧` and Stacks 0DEF on the opposite
of the geometric side, and the two opposites are the same one moved across the equivalence. No
`Opposite.op`/`Opposite.unop` bridge is introduced.

The reduction datum `R` is a parameter, exactly as for Stacks 0DEE: the site
`X_{affine,étale}` of Stacks 0DEA part (3) is defined only for a formal algebraic space with a
given reduction, and such a datum exists for every affine formal algebraic space by Stacks 0AIN,
`AlgebraicGeometry.FormalSpace.nonempty_affineReductionChart`. The quotient system `D` is this
library's spelling of "`A` is a weakly admissible topological `S`-algebra", without which
`Spf A` is not defined; and `AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite` is the
condition that the chosen big fppf site contains the atlas `∐_J Spec (A ⧸ J)`, which is what
makes `Spf A` an affine formal algebraic space at all (Stacks 0AIF) and so is part of the
hypothesis that `X` is one. Neither is a hypothesis on `A` beyond the source's.

## References

* [Stacks Project, Tag 0DEF](https://stacks.math.columbia.edu/tag/0DEF)
* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- **Stacks 0DEF.** Let `S` be a scheme contained in a big fppf site `B` and let
`X = Spf A` be a McQuillan affine formal algebraic space over `S`: `A` is a weakly admissible
topological ring presented over `S` by a quotient system `D` whose atlas lies in the site. Then
`(X_{affine,étale})^{opp}` — the opposite of the affine étale site of Stacks 0DEA part (3), at
an arbitrary reduction datum of `X` — is equivalent to the category whose

1. objects are the `A`-algebras `B^∧ = lim B/JB` for an étale ring map `A → B`, the limit being
   over the weak ideals of definition `J` of `A`, and
2. morphisms are the continuous `A`-algebra homomorphisms,

which is `AlgebraicGeometry.FormalSpace.EtaleCompletion`.

This is the source's proof: combine Stacks 0DEE,
`AlgebraicGeometry.FormalSpace.affineEtaleEquivalence`, with Stacks 0AN8,
`AlgebraicGeometry.FormalSpace.isEquivalence_etaleCompletionCharts`. The first identifies
`X_{affine,étale}` with the category of the affine formal algebraic spaces representable étale
over `X`, the second identifies that category with `(EtaleCompletion A)ᵒᵖ`; taking the opposite
of the composite moves the single opposite from the algebra side, where `Spf` being
contravariant puts it, to the geometric side, where Stacks 0DEF writes it. -/
@[stacks 0DEF "the equivalence of `(X_affine,étale)^opp` with the category whose objects are \
the `A`-algebras `B^∧ = lim B/JB` for an étale ring map `A → B` (item (1)) and whose morphisms \
are the continuous `A`-algebra homomorphisms (item (2)), namely \
`AlgebraicGeometry.FormalSpace.EtaleCompletion`. It is the source's proof: Stacks 0DEE, \
`affineEtaleEquivalence`, composed with Stacks 0AN8, `isEquivalence_etaleCompletionCharts`, \
whose opposite is taken on the algebra side because `Spf` is contravariant; \
`CategoryTheory.Equivalence.leftOp` moves that one opposite to the geometric side, where the \
source writes it. The reduction datum is a parameter for the same reason as in Stacks 0DEE -- \
`X_affine,étale` of Stacks 0DEA(3) is defined only relative to one, and one exists by Stacks \
0AIN -- and the quotient system `D` with its large-site condition is this library's spelling of \
`A` being a weakly admissible topological `S`-algebra whose `Spf` is an affine formal algebraic \
space, which is the source's hypothesis on `X`"]
def mcQuillanAffineEtaleEquivalence (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) (hD : D.HasLargeSite)
    (R : Reduction B S hS (formalSpectrum D)) :
    R.AffineEtaleᵒᵖ ≌ EtaleCompletion A :=
  haveI := (isEquivalence_etaleCompletionCharts hA D hD).1
  ((affineEtaleEquivalence (isAffineFormalAlgebraicSpace_formalSpectrum hA D hD) R).trans
    (etaleCompletionCharts hA D hD).asEquivalence.symm).leftOp

end AlgebraicGeometry.FormalSpace

end
