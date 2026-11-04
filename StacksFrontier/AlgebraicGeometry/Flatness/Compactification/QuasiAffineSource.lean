module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProjectiveSpaceImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# Compactification of a quasi-affine scheme over a quasi-compact quasi-separated base

Let `S` be a quasi-compact and quasi-separated scheme and let `f : X ⟶ S` be a separated
morphism of finite type whose source is quasi-affine. Then `X` admits a compactification over
`S`: a quasi-compact open immersion into a scheme proper over `S`.

The general statement, Nagata's compactification theorem, drops the hypothesis that `X` is
quasi-affine; its proof passes from the quasi-affine case treated here to a general source by a
gluing argument along a finite affine covering with dense intersections, and from a Noetherian
base to a quasi-compact quasi-separated one by Noetherian approximation.

## Main results

* `AlgebraicGeometry.exists_quasiCompact_compactificationOf_of_isImmersion_isProper`: a
  quasi-compact immersion into a scheme proper over the base yields a compactification of its
  source.
* `AlgebraicGeometry.exists_quasiCompact_compactificationOf_of_isQuasiAffine`: the
  quasi-affine case of Nagata's compactification theorem.

## Implementation notes

Compactifiability is expressed, as in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications`, by the existence of an
object of `AlgebraicGeometry.CompactificationOf` whose open immersion is quasi-compact.

A quasi-affine source locally of finite type over `S` immerses into relative projective space
`ℙⁿ_S` over `S` (`AlgebraicGeometry.exists_immersion_projectiveSpace`), and `ℙⁿ_S` is proper
over `S` (`AlgebraicGeometry.ProjectiveSpace.instIsProperOver`). An immersion is an open
immersion onto its scheme-theoretic image once it is quasi-compact, and that image is a closed
subscheme of `ℙⁿ_S`, hence again proper over `S`; so the scheme-theoretic closure of the
immersion is the required compactification. Quasi-compactness of the immersion is automatic
here: a quasi-affine scheme is quasi-compact, and `ℙⁿ_S` is quasi-separated because it is
separated over the quasi-separated scheme `S`.

Mathlib expresses a finite type morphism by the two typeclasses `LocallyOfFiniteType` and
`QuasiCompact`; both are hypotheses below even though quasi-compactness of `f`, like its
separatedness, already follows from quasi-affineness of `X` and quasi-separatedness of `S`.

## References

* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A quasi-compact immersion into a scheme proper over `S` compactifies its source: the
scheme-theoretic image of the immersion is proper over `S` and the source is open in it. -/
theorem exists_quasiCompact_compactificationOf_of_isImmersion_isProper
    {X Y S : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ S)
    [IsImmersion i] [QuasiCompact i] [IsProper p] :
    ∃ j : CompactificationOf (Over.mk (i ≫ p)), QuasiCompact j.immersion := by
  let obj : StructuredArrow (Over.mk (i ≫ p)) (𝟭 (Over S)) :=
    StructuredArrow.mk (Over.homMk i.toImage (by
      show i.toImage ≫ (i.imageι ≫ p) = i ≫ p
      rw [← Category.assoc, Scheme.Hom.toImage_imageι]) :
        Over.mk (i ≫ p) ⟶ Over.mk (i.imageι ≫ p))
  exact ⟨⟨obj, inferInstanceAs (IsOpenImmersion i.toImage),
    inferInstanceAs (IsProper (i.imageι ≫ p))⟩, inferInstanceAs (QuasiCompact i.toImage)⟩

/-- **Nagata compactification for a quasi-affine source (Stacks Project, Tag 0F41).** A
separated morphism of finite type from a quasi-affine scheme to a quasi-compact and
quasi-separated scheme admits a compactification: a quasi-compact open immersion into a scheme
proper over the base.

The source statement has no quasi-affineness hypothesis; this is the case of its proof in which
the source immerses into relative projective space directly, with no gluing along a covering. -/
@[stacks 0F41 "the case of a quasi-affine source",
  sga "4½ Arcata 4.5.3" "special case",
  sga "4½ Th_finitude 2.8" "more general",
  sga "7 XIII 2.1.6" "2.1.6 c), special case"]
theorem exists_quasiCompact_compactificationOf_of_isQuasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [X.IsQuasiAffine] :
    ∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion := by
  obtain ⟨n, i, _, hif⟩ := exists_immersion_projectiveSpace f
  have : QuasiSeparatedSpace (ProjectiveSpace n S) :=
    quasiSeparatedSpace_of_quasiSeparated (ProjectiveSpace n S ↘ S)
  rw [← hif]
  exact exists_quasiCompact_compactificationOf_of_isImmersion_isProper i
    (ProjectiveSpace n S ↘ S)

end AlgebraicGeometry
