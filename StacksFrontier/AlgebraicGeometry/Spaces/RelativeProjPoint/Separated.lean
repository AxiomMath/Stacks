module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure morphism of the relative Proj of an algebraic space is separated

In Situation 0849 let `π : Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of Stacks 084C,
that is, the functor `F` of Stacks 084A
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor`) with its morphism to `X`
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjπ`). This file proves Stacks 084E:
`π` is separated, with no hypothesis on `𝒜`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.isSeparated_relativeProjπ`: **Stacks 084E.**

## Implementation notes

The proof is the source's. Choose a surjective étale scheme chart `g : U ⟶ X`, which `X` has by
definition of an algebraic space. The second assertion of Stacks 084B
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints`) is a cartesian square
identifying `U ×_X Proj_X(𝒜)` with the scheme-level relative Proj `Proj_U(g^*𝒜)` of Stacks 01NQ,
where `g^*𝒜` is the restriction of `𝒜` to `U`
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints_algebra`); that restriction
is a quasi-coherent graded algebra on the scheme `U` by its construction from `𝒜`, so no
hypothesis on it is needed. The structure morphism of `Proj_U(g^*𝒜)` is separated by the case of
schemes, Stacks 01NQ / 01O2
(`Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase`), and separatedness
descends along the chart by the implication (5) ⇒ (1) of Stacks 03KM
(`AlgebraicGeometry.Space.isSeparated_of_etaleChart`).

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 084E](https://stacks.math.columbia.edu/tag/084E)
* [Stacks Project, Tag 01O2](https://stacks.math.columbia.edu/tag/01O2)
* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
-/

@[expose] public section

universe u m

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for separatedness of the chart's relative Proj (`infer_instance` in `hmap`)
/-- **Stacks 084E.** In Situation 0849 the structure morphism `π : Proj_X(𝒜) ⟶ X` of the
relative homogeneous spectrum is separated.

There is no hypothesis on the graded algebra, exactly as in the source. Over a surjective étale
scheme chart `g : U ⟶ X` the base change of `π` is the scheme-level relative Proj of the
restriction `g^*𝒜` (Stacks 084B), whose structure morphism is separated (Stacks 01O2), and
separatedness descends along the chart (Stacks 03KM). -/
@[stacks 084E, ega "II 8.14.1" "more general"]
theorem isSeparated_relativeProjπ :
    IsSeparated s.site s.base s.containsBase s.relativeProjπ := by
  obtain ⟨U, g, hsurj, hetale⟩ := s.space.property.exists_atlas
  refine isSeparated_of_etaleChart _ _ _ s.isAlgebraicSpace_relativeProjFunctor hsurj hetale ?_
  let d := s.relativeProjPoints
  have hmap : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map (d.fibreHom U g)) := by
    rw [d.fibreHom_comp U g]
    have := Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase (d.algebra U g)
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (d.algebra U g))
    infer_instance
  have hyon : IsSeparated s.site s.base s.containsBase (yoneda.map (d.fibreHom U g)) :=
    (isSeparated_yoneda_map_iff _ _ _ (d.fibreHom U g)).2 hmap
  have hstable : ((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  refine MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf.diagonal)
    (IsPullback.of_horiz_isIso (fst := ((d.isPullback U g).isoIsPullback _ _
      (IsPullback.of_hasPullback s.relativeProjπ g)).inv) (g := 𝟙 (yoneda.obj U)) ⟨?_⟩) hyon
  rw [Category.comp_id]
  exact IsPullback.isoIsPullback_inv_snd _ _ (d.isPullback U g)
    (IsPullback.of_hasPullback s.relativeProjπ g)

end RelativeProjSituation

end AlgebraicGeometry.Space

end
