module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.MorphismDescentData

/-!
# Stacks 08K1 for an inverse system bounded by the cutoff

Stacks 08K1 (`AlgebraicGeometry.Space.MorphismDescentData.exists_isProper_mapAt`) is proved in
Situation 084W under the chapter's standing convention of Section 70.2,
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`: the limit of the affine charts of the
base changes of the stages over a fixed stage lies in the site. This file shows that an inverse
system bounded by the cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`) satisfies the
convention, and reads Stacks 08K1 for such a system with the base changes written as
`CategoryTheory.Limits.pullback.map`.

The convention asks only that every limit of the charts have size below the cutoff. A chart over
the stage `i` is a base change of a later stage along an affine test object, so the uniform bound
of `AlgebraicGeometry.Space.BaseChangeSizeBounded` bounds all of them by one cardinal `μ` below
the cutoff, and the slice over `i` has fewer objects than the cutoff by
`AlgebraicGeometry.mk_over_lt_of_mk_hom_le`; the limit of a cofiltered diagram of affine schemes
of size at most `μ` with fewer stages than the cutoff has size below the cutoff
(`AlgebraicGeometry.Scheme.size_lt_of_isLimit_of_isAffine_of_size_le`). No condition on the
cofinality of the cutoff enters.

## Main results

* `AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_isCutoffBoundedSystem`: an inverse
  system bounded by the cutoff satisfies the convention of Section 70.2.
* `AlgebraicGeometry.Space.exists_isProper_pullbackMap_of_isCutoffBoundedSystem`: Stacks 08K1 for
  an inverse system bounded by the cutoff, with `f_i = B_i ×_{B₀} f₀` written as a
  `CategoryTheory.Limits.pullback.map`.

Nothing here is registered.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An inverse system bounded by the cutoff satisfies the chapter's convention.** For a
cofiltered inverse system `D` with fewer stages than the cutoff, its hom types bounded by one
cardinal below the cutoff and uniformly bounded base changes
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), every limit of the affine charts of the base
changes of the stages over a stage `i` along an affine test object lies in the site
(`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`): the charts are bounded by the cardinal
of `AlgebraicGeometry.Space.BaseChangeSizeBounded`, and the slice over `i` is below the cutoff. -/
theorem siteContainsBaseChangeLimits_of_isCutoffBoundedSystem {J : Type u} [Category.{u} J]
    [IsCofiltered J] {D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hD : IsCutoffBoundedSystem B S hS D) : SiteContainsBaseChangeLimits B S hS D := by
  obtain ⟨hJ, ⟨ν, hν, hhom⟩, hb⟩ := hD
  intro i Z g W hW
  let C : AffineChartSystem B S hS i D Z g := ⟨W, hW⟩
  obtain ⟨μ, hμ, hsize⟩ := hb i _ g
  intro c hc
  exact Scheme.size_lt_of_isLimit_of_isAffine_of_size_le B.aleph0_lt_cutoff
    (underlyingDiagram C.siteDiagram) C.isAffine_obj
    (mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hJ hν hhom i) hμ
    (fun j => hsize j _ (C.stageMap j) (C.baseMap j) (C.isPullback j)) hc

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 08K1 for an inverse system bounded by the cutoff.** Let `(B_i)` be a directed
inverse system of algebraic spaces over `S` with affine transition morphisms, bounded by the
cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), let `i₀` be an index and let
`f₀ : X₀ ⟶ Y₀` be a morphism of algebraic spaces over `B_{i₀}`, with `B_{i₀}`, `X₀` and `Y₀`
quasi-compact and quasi-separated. If `f₀` is locally of finite type and its base change
`f : B ×_{B_{i₀}} X₀ ⟶ B ×_{B_{i₀}} Y₀` to the limit `B = lim B_i` is proper, then its base change
`f_i` to some stage `i ≥ i₀` is proper.

This is `AlgebraicGeometry.Space.MorphismDescentData.exists_isProper_mapAt` for the data of
Situation 084W built from these, its convention supplied by
`AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_isCutoffBoundedSystem`; its
`AlgebraicGeometry.Space.MorphismDescentSituation.mapAt` and
`AlgebraicGeometry.Space.MorphismDescentSituation.mapLimit` are the
`CategoryTheory.Limits.pullback.map` of the statement. -/
theorem exists_isProper_pullbackMap_of_isCutoffBoundedSystem {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : IsCutoffBoundedSystem B S hS D)
    (hDalg : ∀ i : I, IsAlgebraicSpace B S hS (D.obj (op i)))
    (haff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B S hS (D.map g))
    (i₀ : I) {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : X₀ ⟶ D.obj (op i₀))
    (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀) (hf₀ : f₀ ≫ b = a)
    (hX₀ : IsAlgebraicSpace B S hS X₀) (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hqc : IsQuasiCompactSpace B S hS (D.obj (op i₀)))
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (D.obj (op i₀)))
    (hX₀qc : IsQuasiCompactSpace B S hS X₀) (hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀)
    (hY₀qc : IsQuasiCompactSpace B S hS Y₀) (hY₀qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₀)
    (hf : IsProper B S hS (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀
      (𝟙 _) (by simp) (by simp [hf₀])))
    (hlft : IsLocallyOfFiniteType B S hS f₀) :
    ∃ (i : I) (hi : i₀ ≤ i), IsProper B S hS (pullback.map (D.map (homOfLE hi).op) a
      (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])) := by
  let M : MorphismDescentData B S hS hZ I :=
    { base := D
      base_isAlgebraicSpace := hDalg
      transition_affine := haff
      initial := i₀
      source₀ := X₀
      target₀ := Y₀
      sourceToBase := a
      targetToBase := b
      map₀ := f₀
      map₀_over := hf₀
      source₀_isAlgebraicSpace := hX₀
      target₀_isAlgebraicSpace := hY₀
      base₀_quasiCompact := hqc
      base₀_quasiSeparated := hqs
      source₀_quasiCompact := hX₀qc
      source₀_quasiSeparated := hX₀qs
      target₀_quasiCompact := hY₀qc
      target₀_quasiSeparated := hY₀qs }
  have : Nonempty I := ⟨i₀⟩
  have hconv : SiteContainsBaseChangeLimits B S hS M.base :=
    siteContainsBaseChangeLimits_of_isCutoffBoundedSystem B S hS hD
  exact M.exists_isProper_mapAt hconv hf hlft

end AlgebraicGeometry.Space

end
