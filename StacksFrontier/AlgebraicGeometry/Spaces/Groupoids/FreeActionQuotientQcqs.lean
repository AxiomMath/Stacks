module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteFreeActionSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The quotient by a free action of a finite group is quasi-compact and quasi-separated

Let `S` be a scheme, let `V` be an object of a big fppf site over `S` and let a finite group
`G` act freely on `V` over `S`, so that the quotient `V/G` is an algebraic space over `S` by
[Stacks, Tag 071S]. If the scheme underlying `V` is quasi-compact, so is `V/G`; if it is
quasi-separated, then `V/G` is quasi-separated in the absolute sense of [Stacks, Tag 03BS]
part (3).

## Main results

* `AlgebraicGeometry.Space.quasiCompact_actionRelationSource`: the source map of the graph
  relation of an action of a finite group is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_actionQuotient_of_compactSpace`: the quotient
  of an object with quasi-compact underlying scheme by a free action of a finite group is a
  quasi-compact algebraic space.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_actionQuotient_of_quasiSeparatedSpace`:
  the quotient of an object with quasi-separated underlying scheme by a free action of a
  finite group is a quasi-separated algebraic space.

## References

* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- **The source map of the graph relation of an action of a finite group is quasi-compact.** -/
theorem quasiCompact_actionRelationSource {S : Scheme.{u}} (U : Over S) (G : Type v)
    [Group G] [Finite G] [Small.{u} G] :
    QuasiCompact (actionRelationSource U G).left := by
  have _ : Finite (Shrink.{u} G) := Finite.of_equiv G (equivShrink.{u} G)
  have _ : MorphismProperty.RespectsIso (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ _ _ => inferInstance
  refine property_left_of_sigmaDesc (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) G
    (actionRelationSource U G) ?_
  refine quasiCompact_sigmaDesc_of_finite _ fun i => ?_
  have h : (Sigma.ι (fun _ : G => U) ((equivShrink.{u} G).symm i) ≫
      actionRelationSource U G).left = 𝟙 U.left := by
    rw [show Sigma.ι (fun _ : G => U) ((equivShrink.{u} G).symm i) ≫
      actionRelationSource U G = 𝟙 U from by simp [actionRelationSource]]
    rfl
  rw [h]
  infer_instance

section FreeFiniteAction

variable (G : Type v) [Group G] [Finite G] [Small.{u} G] (B : BigFppfSite.{u})
  (S : Scheme.{u}) (hS : B.Contains S)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (V : BigFppfOver B S hS) (a : G →* Aut (underlyingOver B hS V))
  (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **The source projection of the kernel pair of the chart of a free quotient is
quasi-compact**, read inside the site. -/
theorem quasiCompact_toScheme_map_siteActionRelationSource :
    QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (siteActionRelationSource G B hS V
        (contains_actionRelationScheme_of_actsFreely G B S hS V a ha))) :=
  quasiCompact_actionRelationSource (underlyingOver B hS V) G

omit [Finite G] in
include ha in
/-- **The quotient of a quasi-compact object by a free action of a finite group is a
quasi-compact algebraic space.** -/
theorem isQuasiCompactSpace_actionQuotient_of_compactSpace
    (hV : CompactSpace ((BigFppfOver.toScheme B S hS).obj V)) :
    IsQuasiCompactSpace B S hS (actionQuotient G B hS V a) :=
  have _ := isEtaleEquivalenceRelation_relation_of_actsFreely G B S hS V a ha
  IsQuasiCompactSpace.of_surjective_etale B S hS
    (surjective_presheaf_freeActionQuotientMap G B S hS V a ha)
    (quotientMap_etale_unconditional B S hS _ _)
    (isQuasiCompactSpace_yoneda_obj B S hS hV)

include ha in
/-- **The quotient of a quasi-separated object by a free action of a finite group is a
quasi-separated algebraic space**, quasi-separatedness being the absolute notion of
[Stacks, Tag 03BS] part (3). -/
theorem isAbsolutelyQuasiSeparated_actionQuotient_of_quasiSeparatedSpace
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hV : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj V)) :
    IsAbsolutelyQuasiSeparated B S hS hZ (actionQuotient G B hS V a) := by
  have _ := isEtaleEquivalenceRelation_relation_of_actsFreely G B S hS V a ha
  have hU : QuasiSeparated (B.inclusion.map V.hom ≫ terminal.from S) := by
    have h := (quasiSeparatedSpace_iff_quasiSeparated
      ((BigFppfOver.toScheme B S hS).obj V)).mp hV
    rwa [terminal.hom_ext (terminal.from ((BigFppfOver.toScheme B S hS).obj V))
      (B.inclusion.map V.hom ≫ terminal.from S)] at h
  exact isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection B S hS hZ
    (isAlgebraicSpace_actionQuotient_of_actsFreelyOnNonemptyPoints G B hS V a ha)
    (surjective_presheaf_freeActionQuotientMap G B S hS V a ha)
    (quotientMap_etale_unconditional B S hS _ _) hU
    (isPullback_freeActionQuotientMap G B S hS V a ha)
    (quasiCompact_toScheme_map_siteActionRelationSource G B S hS V a ha)

end FreeFiniteAction

end AlgebraicGeometry.Space

end
