module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationLifted

/-!
# Stacks 02WW, unconditionally

`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentation` proves Stacks 02WW — the
quotient sheaf `U/R` of an étale equivalence relation on an object of the big fppf site of `S`
is an algebraic space over `S`, with surjective étale quotient map, so that `(U, R, U ⟶ U/R)`
is a presentation of it — conditional on

```
IsEffectiveDescentAlongCoveringSieve B S hS
  (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)
```

and on nothing else. That proposition is a theorem:
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. This file
substitutes it, which discharges the tag.

## Main definitions

* `AlgebraicGeometry.Space.quotientPresentation_unconditional` is the presentation of `U/R` by
  `(U, R)`, and `AlgebraicGeometry.Space.uliftQuotientPresentation_unconditional` is its form
  in a larger universe.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional`: `U/R` is an algebraic
  space over `S`.
* `AlgebraicGeometry.Space.quotientMap_surjective_unconditional` and
  `AlgebraicGeometry.Space.quotientMap_etale_unconditional`: the quotient map `U ⟶ U/R` is
  surjective and étale after every representable base change.
* `AlgebraicGeometry.Space.uliftQuotientChart_surjective_unconditional` and
  `AlgebraicGeometry.Space.uliftQuotientChart_etale_unconditional`: the same two conclusions
  for the quotient sheaf formed in a larger universe, where no sheafification hypothesis is
  needed at all.

## Implementation notes

**Which descent proposition is being discharged, and which is not.** The hypothesis of Stacks
02WW in this development used to be read at the property of Stacks 02W8, that is at
`@IsSeparated ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType`, which is the standing open
assumption of `StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent` and is *not* proved.
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` mentions its property both in
its hypothesis and in its conclusion, so it is monotone in neither direction: an instance at
one property implies an instance at a smaller or a larger one in neither case, and in
particular the proposition at the property of Stacks 02W8 and the proposition at the
monomorphisms locally of finite type are two different, mutually independent statements.

What makes the tag reachable is that 02WW never needed the larger one. Its hypothesis enters
only through the three conclusions of Stacks 0265, and those are available at the smaller
property — `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_diagDescent` and its two
companions — because the chart's descent hypothesis is a consequence of the diagonal's. The
smaller property lies below the monomorphisms, where
`AlgebraicGeometry.Scheme.size_le_of_mono` pays for the passage from an affine base object to
an arbitrary one, and there the predicate is proved outright. Nothing about the site's cutoff
is used anywhere in the chain beyond
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff` and
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`; in particular `Cardinal.IsRegular` is
not used.

**Tag placement.** Stacks 02WW asserts three things of one object: that `U/R` is an algebraic
space, that `U ⟶ U/R` is étale, and that it is surjective, "in other words" that
`(U, R, U ⟶ U/R)` is a presentation. The covering set is therefore the four unlifted
declarations `isAlgebraicSpace_quotient_unconditional`,
`quotientMap_surjective_unconditional`, `quotientMap_etale_unconditional` and
`quotientPresentation_unconditional`, and the tag sits on each of them.
The kernel-pair property is *not* part of the assertion of 02WW: it is Stacks 02WV, and it
needs no descent hypothesis to begin with, so it is stated and tagged once and for all on
`AlgebraicGeometry.Space.quotientMap_isPullback` and is not restated here. The three
`ulift…` declarations restate the same mathematics for a quotient sheaf formed in a larger
universe and are left untagged rather than carrying 02WW at a second statement.

**The sheafification hypothesis.** The unlifted statements assume
`HasSheafify (BigFppfOver.topology B S hS) (Type u)`, exactly as the conditional forms do; it
is not an open mathematical assumption but the choice of universe in which the quotient
presheaf is sheafified. The `ulift…` statements have no such assumption: sheafifying into
`Type (max u v)` for `v = u + 1` is available on an essentially small site, which is what
`AlgebraicGeometry.Space.uliftQuotientChart` is for.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {R U : BigFppfOver B S hS} (s t : R ⟶ U)

section Unlifted

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **Stacks 02WW, the algebraic-space property.** The quotient sheaf of an étale equivalence
relation on an object of the big fppf site of `S` is an algebraic space over `S`.

This is `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent` with
its descent hypothesis discharged by
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. -/
@[stacks 02WW "the quotient sheaf is an algebraic space"]
theorem isAlgebraicSpace_quotient_unconditional
    [IsEtaleEquivalenceRelation (relation B S hS s t)] :
    IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj :=
  isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS s t
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

/-- **Stacks 02WW, surjectivity of the quotient map.** The canonical map `U ⟶ U/R` is
surjective after every representable base change. -/
@[stacks 02WW "the quotient map is surjective"]
theorem quotientMap_surjective_unconditional
    [IsEtaleEquivalenceRelation (relation B S hS s t)] :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (quotientMap B S hS s t) :=
  quotientMap_surjective_of_coveringSieveDescent B S hS s t
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

/-- **Stacks 02WW, étaleness of the quotient map.** The canonical map `U ⟶ U/R` is étale after
every representable base change. -/
@[stacks 02WW "the quotient map is étale"]
theorem quotientMap_etale_unconditional
    [IsEtaleEquivalenceRelation (relation B S hS s t)] :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (quotientMap B S hS s t) :=
  quotientMap_etale_of_coveringSieveDescent B S hS s t
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

/-- **Stacks 02WW, the presentation.** An étale equivalence relation presents its quotient
sheaf: `(U, R, U ⟶ U/R)` is a presentation of the algebraic space `U/R`. -/
@[stacks 02WW "the presentation"]
noncomputable def quotientPresentation_unconditional
    [IsEtaleEquivalenceRelation (relation B S hS s t)] :
    Presentation B S hS _ (isAlgebraicSpace_quotient_unconditional B S hS s t) :=
  quotientPresentation_of_coveringSieveDescent B S hS s t
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

end Unlifted

section Lifted

variable [HasSheafify (BigFppfOver.topology B S hS) (Type (max u v))]

/-- Surjectivity of the chart of the quotient sheaf formed in `Type (max u v)`, with no descent
hypothesis. This is the content of Stacks 02WW in the lifted universe; the tag sits on the
unlifted `AlgebraicGeometry.Space.quotientMap_surjective_unconditional`. -/
theorem uliftQuotientChart_surjective_unconditional
    [IsEtaleEquivalenceRelation (relation B S hS s t)] :
    (MorphismProperty.relative uliftYoneda.{v} (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (uliftQuotientChart.{u, v} B S hS s t) :=
  uliftQuotientChart_surjective_of_coveringSieveDescent B S hS s t
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

/-- Étaleness of the chart of the quotient sheaf formed in `Type (max u v)`, with no descent
hypothesis. This is the content of Stacks 02WW in the lifted universe; the tag sits on the
unlifted `AlgebraicGeometry.Space.quotientMap_etale_unconditional`. -/
theorem uliftQuotientChart_etale_unconditional
    [IsEtaleEquivalenceRelation (relation B S hS s t)] :
    (MorphismProperty.relative uliftYoneda.{v} (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (uliftQuotientChart.{u, v} B S hS s t) :=
  uliftQuotientChart_etale_of_coveringSieveDescent B S hS s t
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

/-- The presentation of the quotient sheaf formed in `Type (max u v)` by an étale equivalence
relation, with no descent hypothesis and no sheafification hypothesis in `Type u`. -/
noncomputable def uliftQuotientPresentation_unconditional
    [IsEtaleEquivalenceRelation (relation B S hS s t)] :
    EtalePresentation.{u, v} B S hS (uliftQuotientSheaf.{u, v} B S hS s t).obj :=
  uliftQuotientPresentation_of_coveringSieveDescent B S hS s t
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

end Lifted

end AlgebraicGeometry.Space

end
