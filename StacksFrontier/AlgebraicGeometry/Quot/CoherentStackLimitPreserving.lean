module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitDescentHom

/-!
# `Coh_{X/Y}` is limit preserving, given the descent of flatness and of proper support

In Situation 08KB assume `Y` locally of finite presentation over `S`. For every cofiltered
system of affine schemes `T_j` of the big fppf site whose limit `T` in schemes lies in the site,
the comparison functor `colim Coh_{X/Y, T_j} ⥤ Coh_{X/Y, T}` of Artin's Axioms, Definition 07XL,
is an equivalence, as soon as the flatness and the properness of the support of a finitely
presented module on `X_T` descend to a stage of the system of base changes `X ×_Y T_j`
(`AlgebraicGeometry.Space.CoherentSituation.FlatProperSupportDescends`, the conclusion of
Stacks 08K0 and 08K2 for that system). This is the proof of Stacks 08KD with those two inputs
taken as a hypothesis.

## Main results

* `CoherentSituation.isEquivalence_colimitComparison_coherent`: the comparison functor of
  Stacks 07XL for `Coh_{X/Y}` is an equivalence at a given system.
* `CoherentSituation.isLimitPreserving_coherent_of_flatProperSupportDescends`: `Coh_{X/Y}` is
  limit preserving in the sense of Stacks 07XL, at index categories in the scheme universe, given
  `FlatProperSupportDescends` at every system.

## Implementation notes

**This file carries no tag.** The hypothesis is the conclusion of Stacks 08K0 (flatness of a
module) and Stacks 08K2 (properness of its support) for the system `X ×_Y T_k ⟶ T_k` of an
arbitrary cofiltered system of affine schemes of the site, under the chapter's convention 07SD;
see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackLimitDescentObj.lean`. Faithfulness, fullness
and essential surjectivity are the three descent conditions of
`StacksFrontier/AlgebraicGeometry/Stacks/LimitPreservingStageDescent.lean`:
`AlgebraicGeometry.Space.CoherentSituation.descentEq_coherent`,
`AlgebraicGeometry.Space.CoherentSituation.descentHom_coherent` and
`AlgebraicGeometry.Space.CoherentSituation.descentObj_coherent`.

The index universes are both the scheme universe, as in
`AlgebraicGeometry.isLimitPreservingPolarizedUnconditional`: Stacks 07XL quantifies over directed
inverse systems of affine schemes, and a directed set is small; the colimit statement of Stacks
07V7 for the system of base changes asks the index to live in the universe of the site.

## References

* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

/-- `Coh_{X/Y}` as a category fibred in groupoids over the big fppf site of `S`: the category of
Stacks 08KB, projecting an object `(T, g, F)` to the scheme `T`, with the fibred-in-groupoids
structure of Stacks 08W5. -/
def coherentCFG : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (coherentBasedCategory D.categoryData)
    D.isFiberedInGroupoids_siteProjection

/-- **The comparison functor of Stacks 07XL for `Coh_{X/Y}` is an equivalence**, at a cofiltered
system of affine schemes of the site whose limit in schemes lies in the site, when `Y` is locally
of finite presentation over `S` and flatness and proper support descend along the system of base
changes. -/
theorem isEquivalence_colimitComparison_coherent
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1)) {I : Type u}
    [Category.{u} I] [IsCofiltered I] (E : I ⥤ BigAffineFppf B S hS) (c : Cone E)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (hdesc : D.FlatProperSupportDescends E c) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    letI : (coherentSiteProjection D.categoryData).IsFibered :=
      D.isFiberedInGroupoids_siteProjection.isFibered
    (Deformation.Artin.colimitComparison (coherentSiteProjection D.categoryData)
      (E ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c)).IsEquivalence :=
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let : (coherentSiteProjection D.categoryData).IsFibered :=
    D.isFiberedInGroupoids_siteProjection.isFibered
  { faithful := D.faithful_colimitComparison_coherent B.contains_terminal E c hc
    full := Deformation.Artin.full_of_descentHom _ D.isFiberedInGroupoids_siteProjection _ _
      (D.descentHom_coherent E c hc hY)
    essSurj := Deformation.Artin.essSurj_of_descentObj _ D.isFiberedInGroupoids_siteProjection _ _
      (D.descentObj_coherent E c hc hY hdesc) }

/-- **`Coh_{X/Y}` is limit preserving, given the descent of flatness and of proper support.** In
Situation 08KB, if `Y` is locally of finite presentation over `S` and, for every cofiltered system
of affine schemes of the site whose limit in schemes lies in the site, flatness and properness of
the support of a finitely presented module descend along the system of base changes (Stacks 08K0
and 08K2 for that system), then `Coh_{X/Y}` is limit preserving in the sense of Stacks 07XL, at
index categories in the scheme universe. -/
theorem isLimitPreserving_coherent_of_flatProperSupportDescends
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    (hdesc : ∀ (I : Type u) [Category.{u} I] [IsCofiltered I] (E : I ⥤ BigAffineFppf B S hS)
      (c : Cone E), IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
        D.FlatProperSupportDescends E c) :
    Deformation.Artin.IsLimitPreserving.{u, u, u} B S hS D.coherentCFG := by
  intro I _ _ E c hc
  exact D.isEquivalence_colimitComparison_coherent hY E c hc (hdesc I E c hc)

end AlgebraicGeometry.Space.CoherentSituation

end
