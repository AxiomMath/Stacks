module

public import Mathlib.RingTheory.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# The essential-surjectivity clause of Stacks 0AN8, as a statement

Let `S` be a scheme contained in a big fppf site `B`. The equivalence of categories of
**Stacks 0AN8** has two halves: full faithfulness of `Spf`, which is Stacks 0AN0, and essential
surjectivity, which says that a morphism `V ⟶ Spf R` from an affine formal algebraic space over
`S` which is representable by algebraic spaces and étale is `Spf` of `R → A^∧` for an étale
`R`-algebra `A`.

The statement here asks of the quotient system `D` one thing the source does not, namely the
site condition `AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite` of Stacks 0AIF, that
the site hold the atlas `∐_J Spec (R ⧸ J)`; it asks nothing of `R` itself. See the disclosure on
`AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf'` below.

This module carries only the statement of that second half. It exists so that the statement is
available strictly below the proof
(`AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf`, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.EssentiallySurjectiveSpf`) and any result consuming
it.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf'`: the essential-surjectivity clause
  of **Stacks 0AN8**.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The essential-surjectivity clause of Stacks 0AN8.** For a McQuillan affine formal
algebraic space `Spf R` over `S`, every affine formal algebraic space `V` over `S` carrying a
morphism `V ⟶ Spf R` which is representable by algebraic spaces and étale is `Spf` of the
completion `A^∧` of an étale `R`-algebra `A`, compatibly with the morphisms to `Spf R`.

This is the half of the equivalence of categories of Stacks 0AN8 which the two declarations this
library tags with Stacks 0AN8 in the completion files,
`TopologicalRing.etale_quotientMap_weakIdealOfDefinition` and
`TopologicalRing.CompletionOver.etale_quotientMap_canonicalMap`, do not cover: those carry only
the first step of its proof and their tag comments exclude essential surjectivity by name. It is
a theorem of this library, `AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.EssentiallySurjectiveSpf`. The other half of the
equivalence, full faithfulness of `Spf`, is Stacks 0AN0 and is available as
`AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`.

The binder `_hD : D.HasLargeSite` is the one thing asked here that Stacks 0AN8 does not ask.
It is the site condition of Stacks 0AIF — that the site hold the single atlas
`∐_J Spec (R ⧸ J)` indexed by the weak ideals of definition — and it is what makes `Spf R` an
affine formal algebraic space in the sense of Stacks 0AIS at all, through
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum`. Stacks leaves it
implicit because its sites are indexed by a cutoff it is free to enlarge; see the implementation
notes of `StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum`.

It is not a consequence of `QuotientSystem B S hS R`, which asks only that each quotient
spectrum `Spec (R ⧸ J)` lie in the site; a site containing every component of a coproduct need
not contain the coproduct.

It is, however, strictly weaker than a bound `#R < B.cutoff` on the ring, which implies it by
`AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff`. That bound is a genuine restriction on a weakly admissible
ring, so stating the clause with `_hD` rather than with it is a real generalization: let `k` be
a finite field, let `I` be an index set of cardinality the cutoff, and let `R = k ⊕ k ^ I` be
the square-zero extension, topologised by the ideals `W_F = {f | f` vanishes on `F}` for the
finite `F ⊆ I`. These are closed under intersection, so the topology is linear; it is separated
because they meet in `0`; and `R` is complete, being `k` discrete times the product `k ^ I`.
Every element of `k ^ I` squares to zero, hence is topologically nilpotent, so each `W_F` is a
weak ideal of definition; an open ideal meeting `k` nontrivially contains a unit and is all of
`R`, which is not one because `1` is not topologically nilpotent. So every weak ideal of
definition has finite quotient and `R` carries a quotient system over `Spec k`, while
`#R = #k ^ #I` exceeds the cutoff. The bound on `R` is recovered from a quotient system only
under a completeness hypothesis that weak admissibility does not supply:
`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_quotientSystem` embeds `R` into the countable
product of its quotients by the powers of a *single* ideal, so it needs `IsAdic I` and
`IsAdicComplete I R`.

`_hD` is used exactly once, in
`AlgebraicGeometry.FormalSpace.exists_etale_completion_iso_of_isRepresentableEtale`, where it
feeds both `isAffineFormalAlgebraicSpace_formalSpectrum` and the `HasLargeSite` hypothesis of
Stacks 0ANM. -/
abbrev IsEssentiallySurjectiveSpf' : Prop :=
  ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem B S hS R) (_hD : D.HasLargeSite)
    (V : FppfSheaf B S hS) (v : V ⟶ formalSpectrum D),
    IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS v →
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
        (E : QuotientSystem B S hS (TopologicalRing.CompletionOver (algebraMap R A)))
        (c : ContinuousHom D E) (ε : V ≅ formalSpectrum E),
        c.toRingHom = TopologicalRing.CompletionOver.canonicalMap (algebraMap R A) ∧
          ε.hom ≫ formalSpectrumMap hR c = v

end AlgebraicGeometry.FormalSpace

end
