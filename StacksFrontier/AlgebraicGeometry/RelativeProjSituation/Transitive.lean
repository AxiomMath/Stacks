module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Descent

/-!
# Tag 01NP in the shape of Situation 01NN

Stacks tag 01NP reads, in Situation 01NN: for affine opens `U ⊆ U' ⊆ U''` of the base, with
`A = 𝒜(U)`, `A' = 𝒜(U')` and `A'' = 𝒜(U'')`, the composition of the morphisms
`r : Proj(A) → Proj(A')` and `r' : Proj(A') → Proj(A'')` of tag 01NO *is* the morphism
`r'' : Proj(A) → Proj(A'')` of tag 01NO, and a similar statement holds for the isomorphisms
`θ` of that tag.

This file states exactly that, over `Stacks.RelativeProj.Situation` — the repository's bundled
Situation 01NN, a scheme together with a quasi-coherent, commutative, nonnegatively graded
algebra over its structure sheaf — with `𝒜(U)` read as the graded ring of local sections
`Stacks.RelativeProj.Situation.sectionRing`, graded by
`Stacks.RelativeProj.Situation.sectionRingGrading`, and `r` read as tag 01NO's morphism
`Stacks.RelativeProj.Situation.projInclusionMap`.

## Main results

* `Stacks.RelativeProj.Situation.projInclusionMap_trans`: **tag 01NP in the source's shape.**
  The two tag-01NO morphisms of a chain of three nested affine opens compose to the tag-01NO
  morphism of the outer inclusion.
* `Stacks.RelativeProj.Situation.twistMap_gradedSectionRestriction_trans`: **the similar
  statement for the isomorphisms `θ`.** The two tag-01NO comparison isomorphisms of a chain of
  three nested affine opens compose, on sections of the twisting sheaves in every degree over
  every open, to the comparison isomorphism of the outer inclusion.
* `Stacks.RelativeProj.Situation.projInclusionMap_and_twistMap_trans`: **both assertions of tag
  01NP as one statement.** The conjunction of the previous two, under the tag's own hypotheses on
  the chain of three affine opens.

## Implementation notes

The composition law itself is not reproved here: it is
`Stacks.RelativeProj.Situation.projInclusionMap_comp`, which states the same equation with the
two sides exchanged and is proved there from functoriality of restriction of homogeneous
sections together with `AlgebraicGeometry.Proj.map_comp`. What this file adds is the source's
own orientation — the *composition* of `r` and `r'` on the left, `r''` on the right — and the
source's own naming of the three opens, so that tag 01NP has a statement in Situation 01NN to
be attached to.

Two further formalizations of Situation 01NN carry a composition law of their own, and neither
is bridged to this one, so neither is used here: over
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` the law is
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.projInclusionMap_comp`, and over
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` — a family of graded rings indexed by the
affine opens of the base, not a sheaf — it is
`Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_comp_of_le_opens`.

The twist half of the tag is stated on sections rather than as an equation between morphisms of
sheaves of modules, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/RelativeProj/Twist/Functorial.lean`:
`Stacks.ProjTwistComparison.twistMap` is an adjoint transpose, so `θ` for the outer inclusion and
the composite of the two `θ`'s live over the inverse-image functors of `r''` and of `r ≫ r'`,
which are equal only through `Stacks.RelativeProj.Situation.projInclusionMap_trans`; on sections
no such transport is needed. For the same reason the identity is stated at a point of the chart
over `U`: the comparison attached to `r''` lands in the sections over the preimage of an open
under `r''`, and the composite in the sections over its two-step preimage, and those two opens
are equal only through `Stacks.RelativeProj.Situation.gradedSectionRestriction_comp`.

Both tag-01NO comparisons are isomorphisms, by
`Stacks.RelativeProj.Situation.isIso_twistMap_gradedSectionRestriction`, so the identity below is
an identity of isomorphisms; no separate statement that the composite is invertible is recorded,
since that is the tag-01NO statement for the outer inclusion.

## References

* [Stacks Project, Tag 01NP](https://stacks.math.columbia.edu/tag/01NP)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjTwistComparison

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-- **Stacks Project, Tag 01NP.** In Situation 01NN, let `U ⊆ U' ⊆ U''` be affine opens of the
base and put `A = 𝒜(U)`, `A' = 𝒜(U')`, `A'' = 𝒜(U'')` for the graded rings of local sections.
The composition of the tag-01NO morphisms `r : Proj A ⟶ Proj A'` and `r' : Proj A' ⟶ Proj A''`
is the tag-01NO morphism `r'' : Proj A ⟶ Proj A''` of the inclusion `U ⊆ U''`.

This is `Stacks.RelativeProj.Situation.projInclusionMap_comp` read in the source's
orientation. -/
public theorem projInclusionMap_trans (U U' U'' : s.base.Opens) (hUU' : U ≤ U')
    (hU'U'' : U' ≤ U'') (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hU'' : IsAffineOpen U'') :
    projInclusionMap s U U' hUU' hU hU' ≫ projInclusionMap s U' U'' hU'U'' hU' hU'' =
      projInclusionMap s U U'' (hUU'.trans hU'U'') hU hU'' :=
  (projInclusionMap_comp s U U' U'' hUU' hU'U'' hU hU' hU'').symm

/-- **Stacks Project, Tag 01NP.** In Situation 01NN, let `U ⊆ U' ⊆ U''` be affine opens of the
base. The composition of the tag-01NO comparison isomorphisms
`θ : r^* 𝒪_{Proj A'}(n) ⟶ 𝒪_{Proj A}(n)` and `θ' : r'^* 𝒪_{Proj A''}(n) ⟶ 𝒪_{Proj A'}(n)` is the
tag-01NO comparison isomorphism `θ'' : r''^* 𝒪_{Proj A''}(n) ⟶ 𝒪_{Proj A}(n)` of the inclusion
`U ⊆ U''`: on a section of `𝒪_{Proj A''}(n)` over an open `V`, at a point of `Proj A` lying over
`V`, the two read the same degree-`n` fraction.

This is the twist half of the tag, "a similar statement holds for the isomorphisms `θ`". -/
public theorem twistMap_gradedSectionRestriction_trans (U U' U'' : s.base.Opens) (hUU' : U ≤ U')
    (hU'U'' : U' ≤ U'') (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
    (n : ℤ) (V : Opens (ProjectiveSpectrum.top (s.sectionRingGrading U'')))
    (a : moduleSections (s.sectionRingGrading U'')
      (twistGrading (S := s.sectionRing U'') (s.sectionRingGrading U'') n) V)
    (y : V.comap (ProjectiveSpectrum.comap
      (gradedSectionRestriction s U U'' (hUU'.trans hU'U''))
      (irrelevant_le_map_gradedSectionRestriction s U U'' (hUU'.trans hU'U'') hU hU''))) :
    (sectionsMap (gradedSectionRestriction s U U'' (hUU'.trans hU'U''))
        (irrelevant_le_map_gradedSectionRestriction s U U'' (hUU'.trans hU'U'') hU hU'')
        n V a).1 y
      = (sectionsMap (gradedSectionRestriction s U U' hUU')
          (irrelevant_le_map_gradedSectionRestriction s U U' hUU' hU hU') n
          (V.comap (ProjectiveSpectrum.comap (gradedSectionRestriction s U' U'' hU'U'')
            (irrelevant_le_map_gradedSectionRestriction s U' U'' hU'U'' hU' hU'')))
          (sectionsMap (gradedSectionRestriction s U' U'' hU'U'')
            (irrelevant_le_map_gradedSectionRestriction s U' U'' hU'U'' hU' hU'') n V a)).1
          ⟨y.1, mem_comap_comap_of_eq_comp (gradedSectionRestriction s U' U'' hU'U'')
            (irrelevant_le_map_gradedSectionRestriction s U' U'' hU'U'' hU' hU'')
            (gradedSectionRestriction s U U' hUU')
            (irrelevant_le_map_gradedSectionRestriction s U U' hUU' hU hU')
            (irrelevant_le_map_gradedSectionRestriction s U U'' (hUU'.trans hU'U'') hU hU'')
            (gradedSectionRestriction_comp s U U' U'' hUU' hU'U'') y.2⟩ :=
  sectionsMap_apply_eq_comp (gradedSectionRestriction s U' U'' hU'U'')
    (irrelevant_le_map_gradedSectionRestriction s U' U'' hU'U'' hU' hU'')
    (gradedSectionRestriction s U U' hUU')
    (irrelevant_le_map_gradedSectionRestriction s U U' hUU' hU hU') n
    (irrelevant_le_map_gradedSectionRestriction s U U'' (hUU'.trans hU'U'') hU hU'')
    (gradedSectionRestriction_comp s U U' U'' hUU' hU'U'') V a y

/-- **Stacks Project, Tag 01NP, both of its assertions as one statement.** In Situation 01NN, let
`U ⊆ U' ⊆ U''` be affine opens of the base and put `A = 𝒜(U)`, `A' = 𝒜(U')`, `A'' = 𝒜(U'')` for
the graded rings of local sections. Then:

* the composition of the tag-01NO morphisms `r : Proj A ⟶ Proj A'` and `r' : Proj A' ⟶ Proj A''`
  is the tag-01NO morphism `r'' : Proj A ⟶ Proj A''` of the inclusion `U ⊆ U''`;
* the similar statement holds for the tag-01NO comparison isomorphisms `θ`: for every degree `n`,
  every open `V` of `Proj A''`, every section `a` of `𝒪_{Proj A''}(n)` over `V` and every point of
  `Proj A` lying over `V`, the composite of `θ` and `θ'` and the comparison `θ''` of the outer
  inclusion read the same degree-`n` fraction.

The two conjuncts are `Stacks.RelativeProj.Situation.projInclusionMap_trans` and
`Stacks.RelativeProj.Situation.twistMap_gradedSectionRestriction_trans`. -/
@[stacks 01NP "both assertions of the tag as one statement, in the shape of Situation 01NN: the
composition law for the tag-01NO morphisms r, and the similar law for the comparison
isomorphisms θ"]
public theorem projInclusionMap_and_twistMap_trans (U U' U'' : s.base.Opens) (hUU' : U ≤ U')
    (hU'U'' : U' ≤ U'') (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hU'' : IsAffineOpen U'') :
    (projInclusionMap s U U' hUU' hU hU' ≫ projInclusionMap s U' U'' hU'U'' hU' hU'' =
        projInclusionMap s U U'' (hUU'.trans hU'U'') hU hU'') ∧
      ∀ (n : ℤ) (V : Opens (ProjectiveSpectrum.top (s.sectionRingGrading U'')))
          (a : moduleSections (s.sectionRingGrading U'')
            (twistGrading (S := s.sectionRing U'') (s.sectionRingGrading U'') n) V)
          (y : V.comap (ProjectiveSpectrum.comap
            (gradedSectionRestriction s U U'' (hUU'.trans hU'U''))
            (irrelevant_le_map_gradedSectionRestriction s U U'' (hUU'.trans hU'U'') hU hU''))),
        (sectionsMap (gradedSectionRestriction s U U'' (hUU'.trans hU'U''))
            (irrelevant_le_map_gradedSectionRestriction s U U'' (hUU'.trans hU'U'') hU hU'')
            n V a).1 y
          = (sectionsMap (gradedSectionRestriction s U U' hUU')
              (irrelevant_le_map_gradedSectionRestriction s U U' hUU' hU hU') n
              (V.comap (ProjectiveSpectrum.comap (gradedSectionRestriction s U' U'' hU'U'')
                (irrelevant_le_map_gradedSectionRestriction s U' U'' hU'U'' hU' hU'')))
              (sectionsMap (gradedSectionRestriction s U' U'' hU'U'')
                (irrelevant_le_map_gradedSectionRestriction s U' U'' hU'U'' hU' hU'') n V a)).1
              ⟨y.1, mem_comap_comap_of_eq_comp (gradedSectionRestriction s U' U'' hU'U'')
                (irrelevant_le_map_gradedSectionRestriction s U' U'' hU'U'' hU' hU'')
                (gradedSectionRestriction s U U' hUU')
                (irrelevant_le_map_gradedSectionRestriction s U U' hUU' hU hU')
                (irrelevant_le_map_gradedSectionRestriction s U U'' (hUU'.trans hU'U'') hU hU'')
                (gradedSectionRestriction_comp s U U' U'' hUU' hU'U'') y.2⟩ :=
  ⟨projInclusionMap_trans s U U' U'' hUU' hU'U'' hU hU' hU'',
    twistMap_gradedSectionRestriction_trans s U U' U'' hUU' hU'U'' hU hU' hU''⟩

end Stacks.RelativeProj.Situation

end
