module

public import StacksFrontier.AlgebraicGeometry.Groupoids.EquivalenceRelation.InvolutionGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionPresentationThickeningRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionStructureMap

/-!
# The quotient of the thickened presentation of a square-zero extension

Let `E` be a square-zero extension of the small étale structure sheaf of an algebraic space `X`
over `S` by a quasi-coherent ideal (the data of Stacks 05ZT) and `X = U/R` an étale presentation.
The chart thickenings `R' ⇉ U'` are schemes over `S` and form an étale equivalence relation. As
soon as a big fppf site `B'` contains `S`, `U'` and `R'`, the pair `R' ⇉ U'` is an étale
equivalence relation on an object of the big fppf site of `S` in `B'`, and its quotient sheaf
`X' = U'/R'` is an algebraic space over `S` (Stacks 02WW). This is the second paragraph of the
proof of Stacks 05ZT: "Thus we can define `X'` as the quotient `U'/R'`".

The site `B'` is a parameter: the thickenings need not be contained in the site `X` is defined
on (see `AlgebraicGeometry.not_contains_spec_of_cutoff_le_mk`), and an enlargement containing
them is provided by `AlgebraicGeometry.exists_isContained_containing`.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeOver`: `U'` as an object of the
  big fppf site of `S` in `B'`.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeOverMap`: `V' ⟶ U'` there.
* `AlgebraicGeometry.Space.SquareZeroExtension.thickeningRelation`: the pre-relation `R' ⇉ U'`.
* `AlgebraicGeometry.Space.SquareZeroExtension.thickeningQuotient`: `X' = U'/R'`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.isEtaleEquivalenceRelation_thickeningRelation`

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
variable {B' : BigFppfSite.{u}} (hS' : B'.Contains S)

/-- **The chart thickening `U'` as a scheme over `S` in a site `B'` containing it**, with
structure morphism `E.chartRealizedSchemeToBaseScheme U`. -/
noncomputable def chartRealizedSchemeOver (U : SmallEtale B S hS X.1)
    (hU : B'.Contains (E.chartRealizedScheme U)) : BigFppfOver B' S hS' :=
  BigFppfOver.mk B' S hS' hU (E.chartRealizedSchemeToBaseScheme U)

/-- **`V' ⟶ U'` as a morphism of the big fppf site of `S` in `B'`.** -/
noncomputable def chartRealizedSchemeOverMap {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    (hU : B'.Contains (E.chartRealizedScheme U)) (hV : B'.Contains (E.chartRealizedScheme V)) :
    E.chartRealizedSchemeOver hS' V hV ⟶ E.chartRealizedSchemeOver hS' U hU :=
  BigFppfOver.homMk B' S hS' hU _ (E.chartRealizedSchemeMap g)
    (E.chartRealizedSchemeMap_comp_chartRealizedSchemeToBaseScheme g)

/-- The underlying morphism of schemes of `chartRealizedSchemeOverMap` is
`E.chartRealizedSchemeMap g`. -/
theorem toScheme_map_chartRealizedSchemeOverMap {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    (hU : B'.Contains (E.chartRealizedScheme U)) (hV : B'.Contains (E.chartRealizedScheme V)) :
    (BigFppfOver.toScheme B' S hS').map (E.chartRealizedSchemeOverMap hS' g hU hV) =
      E.chartRealizedSchemeMap g :=
  rfl

variable (P : Presentation B S hS X.obj X.property)
  (hU : B'.Contains (E.chartRealizedScheme (presentationChart P)))
  (hR : B'.Contains (E.chartRealizedScheme (presentationRelationChart P)))

/-- **The thickened pre-relation `R' ⟶ U' ×_S U'`** of an étale presentation
(`AlgebraicGeometry.Space.relation` takes the source leg first). -/
noncomputable abbrev thickeningRelation :=
  Space.relation B' S hS' (E.chartRealizedSchemeOverMap hS' (presentationRelationSourceHom P) hU hR)
    (E.chartRealizedSchemeOverMap hS' (presentationRelationTargetHom P) hU hR)

/-- **The thickened presentation is an étale equivalence relation over `S`.** -/
instance isEtaleEquivalenceRelation_thickeningRelation :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (E.thickeningRelation hS' P hU hR) where
  isEquivalenceRelation := by
    refine Stacks.Groupoids.isEquivalenceRelation_of_left _ ?_
    simp only [Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source,
      prod.lift_fst, prod.lift_snd]
    exact (E.presentationThickeningEquivalenceRelation P).isEquivalenceRelation
  etale_source := by
    simp only [Stacks.Groupoids.PreRelation.source, prod.lift_snd]
    exact E.etale_chartRealizedSchemeMap (presentationRelationSourceHom P)
  etale_target := by
    simp only [Stacks.Groupoids.PreRelation.target, prod.lift_fst]
    exact E.etale_chartRealizedSchemeMap (presentationRelationTargetHom P)

/-- **The thickening `X' = U'/R'`**, an algebraic space over `S` in `B'` by Stacks 02WW. -/
noncomputable def thickeningQuotient : AlgebraicSpaces B' S hS' :=
  letI := hasSheafify_bigFppfOver B' S hS'
  ⟨_, isAlgebraicSpace_quotient_unconditional B' S hS'
    (E.chartRealizedSchemeOverMap hS' (presentationRelationSourceHom P) hU hR)
    (E.chartRealizedSchemeOverMap hS' (presentationRelationTargetHom P) hU hR)⟩

/-- The presentation `(U', R')` of `X' = U'/R'` (Stacks 02WW). -/
noncomputable def thickeningQuotientPresentation :
    Presentation B' S hS' (E.thickeningQuotient hS' P hU hR).obj
      (E.thickeningQuotient hS' P hU hR).property :=
  letI := hasSheafify_bigFppfOver B' S hS'
  quotientPresentation_unconditional B' S hS'
    (E.chartRealizedSchemeOverMap hS' (presentationRelationSourceHom P) hU hR)
    (E.chartRealizedSchemeOverMap hS' (presentationRelationTargetHom P) hU hR)

end AlgebraicGeometry.Space.SquareZeroExtension

end
