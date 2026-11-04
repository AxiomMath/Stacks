module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorSheaf

/-!
# The Quot functor satisfies the sheaf condition (Stacks 09TT)

In Situation 09TR a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` of a big fppf
site is given, of finite presentation, together with a quasi-coherent `𝒪_X`-module `F`.  Stacks
09TR reads the assignment

`T ↦ Quot_{F/X/B}(T) = {quotients F_T ⟶ Q with Q quasi-coherent, of finite presentation, flat`
`over T and with support proper over T}`

as a presheaf on the schemes of the big fppf site of `S`, whose value at a scheme `T` is the set
of pairs `(h, Q)` consisting of a morphism `h : T ⟶ B` and such a quotient of `F_T`; that
presheaf is `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf`.  Stacks 09TT is the
statement that it satisfies the sheaf condition.

The whole proof is already carried by the sibling Stacks 082P, in
`StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorSheaf.lean`: its reduction
`AlgebraicGeometry.Space.QuotientSituation.isSheaf_totalQuotientFunctor` is stated for the total
presheaf of an *arbitrary* pullback-stable condition on quotients, so the only thing this file
has to do is feed it the four conditions of Stacks 09TR and identify the resulting presheaf with
the one Stacks 09TR built.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.totalProperlySupportedQuotientsFunctor`: the total
  presheaf of Stacks 082P taken at the condition of Stacks 09TR — quasi-coherence, finite
  presentation, flatness over the test scheme and proper support.
* `AlgebraicGeometry.Space.QuotSituation.quotSitePresheafIsoTotal`: that presheaf is the Quot
  presheaf of Stacks 09TR.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.totalProperlySupportedQuotientsFunctor_isSheaf`: the
  total presheaf of the condition of Stacks 09TR is an fppf sheaf.
* `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf`: **Stacks 09TT**, the Quot
  presheaf of Stacks 09TR is an fppf sheaf.

## Implementation notes

**The two descriptions of a section of the Quot presheaf are the same description.**  A section
of `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf` over a scheme `T` of the site is an
`AlgebraicGeometry.Space.QuotFamilyOver`, a morphism `T ⟶ B` together with a member of
`Quot_{F/X/B}` for the test scheme it makes of `T`; a section of the total presheaf of
Stacks 082P at the condition of Stacks 09TR is an
`AlgebraicGeometry.Space.QuotientSituation.TotalQuotient`, which has the same three fields.  The
restrictions agree too, and literally rather than up to a comparison: the morphism of test
schemes `AlgebraicGeometry.Space.QuotFamilyOver.restrict` used by the one and
`AlgebraicGeometry.Space.QuotientSituation.testAtMap` used by the other are the same term, so
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheafIsoTotal` is the identity on fields and
its naturality holds by reflexivity.  No second Quot presheaf is introduced: the sheaf condition
is stated for the presheaf of Stacks 09TR and the total presheaf exists only to apply the
reduction of Stacks 082P to it.

**The topology.**  The source states the sheaf condition for the fpqc topology, which is
stronger than the fppf one because an fppf covering is an fpqc covering.  What is proved here is
the fppf statement, for `AlgebraicGeometry.BigFppfOver.topology`, and that is not a presentation
choice: this development puts no fpqc topology on the big fppf site of `S`, and the fpqc
coverings it does carry — `AlgebraicGeometry.Space.IsFpqcCovering` — are covering *families* of
algebraic spaces and not a Grothendieck topology on the site.  Two separate inputs would be
needed for the stronger statement, and neither is available here: the base `B` would have to
satisfy the sheaf condition for fpqc coverings, whereas
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf` gives only the fppf one, and the descent of
quotients would have to be assumed for fpqc coverings of a test scheme.  The hypotheses below
are stated for the same coverings as the conclusion, so a consumer who has fpqc descent of
quotients gets the fppf statement at once.

**What is assumed.**  Those hypotheses of the sibling Stacks 082P, read at the condition of
Stacks 09TR, that this development does not prove.  The inputs the Quot functor of Stacks 09TR
is built from are not among them: the pseudofunctoriality of the inverse images of Stacks 03LU is
`AlgebraicGeometry.Space.modulePushforwardCoherence` and the preservation of finite presentation
is `AlgebraicGeometry.Space.QuotientSituation.pullbackPreservesFinitePresentation`, so both are
supplied here rather than carried.  What remains are
`AlgebraicGeometry.Space.QuotientSituation.QuotientsSeparatedForCoverings` and
`AlgebraicGeometry.Space.QuotientSituation.QuotientsGlueAlongCoverings`, the descent of
quotients along a covering of a single test scheme, which Remark 08IU supplies from the descent
of quasi-coherent modules of Stacks 04W8 — of which this development carries the faithfulness
clause only.  Neither is discharged here; the fourth condition of Stacks 09TR, proper support,
adds no new hypothesis, being unconditionally stable under pullback by Stacks 0CZJ.

## References

* [Stacks Project, Tag 09TT](https://stacks.math.columbia.edu/tag/09TT)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 082P](https://stacks.math.columbia.edu/tag/082P)
* [Stacks Project, Tag 08IU](https://stacks.math.columbia.edu/tag/08IU)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-! ### The total presheaf at the condition of Stacks 09TR -/

/-- The total presheaf of Stacks 082P taken at the condition of Stacks 09TR: its value at a
scheme `T` of the big fppf site of `S` is the set of pairs `(h, Q)` consisting of a morphism
`h : T ⟶ B` and a quotient of `F_T` which is quasi-coherent, of finite presentation, flat over
`T` and has support proper over `T`.

The condition is stable under pullback of quotients by
`AlgebraicGeometry.Space.QuotSituation.quotientPullback_mem_properlySupportedQuotients`, which
is what the total presheaf of Stacks 082P asks of it. -/
def totalProperlySupportedQuotientsFunctor : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  D.totalQuotientFunctor (modulePushforwardCoherence B S hS) D.properlySupportedQuotients
    fun m K hK ↦ D.quotientPullback_mem_properlySupportedQuotients m K hK

/-- **The total presheaf at the condition of Stacks 09TR is the Quot presheaf of Stacks 09TR.**
A section of either over a scheme of the big fppf site is a morphism to `B` together with a
member of `Quot_{F/X/B}` for the test scheme it makes, and the two restrictions are the same
term: the morphism of test schemes induced by a morphism of the site is spelled the same way on
both sides. -/
def quotSitePresheafIsoTotal :
    D.quotSitePresheaf ≅ D.totalProperlySupportedQuotientsFunctor :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso
      { toFun := fun q ↦ ⟨q.toBase, q.subobject, q.mem⟩
        invFun := fun q ↦ ⟨q.hom, q.ker, q.mem⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })
    (fun _ ↦ rfl)

/-! ### The sheaf condition -/

/-- The total presheaf at the condition of Stacks 09TR satisfies the sheaf condition for the
fppf topology of the big fppf site of `S`.

This is the reduction of Stacks 082P,
`AlgebraicGeometry.Space.QuotientSituation.isSheaf_totalQuotientFunctor`, applied to the
condition of Stacks 09TR; the clause of the sheaf condition concerning the morphisms `T ⟶ B` is
proved there from the sheaf condition for the algebraic space `B`. -/
theorem totalProperlySupportedQuotientsFunctor_isSheaf
    (hsep : D.QuotientsSeparatedForCoverings D.properlySupportedQuotients)
    (hglue : D.QuotientsGlueAlongCoverings D.properlySupportedQuotients) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      D.totalProperlySupportedQuotientsFunctor :=
  D.isSheaf_totalQuotientFunctor (modulePushforwardCoherence B S hS)
    D.properlySupportedQuotients
    (fun m K hK ↦ D.quotientPullback_mem_properlySupportedQuotients m K hK)
    hsep hglue

end QuotSituation

end AlgebraicGeometry.Space

end
