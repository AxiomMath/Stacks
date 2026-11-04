module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraQuasicoherenceCriterion

/-!
# Reduction of the equivalence of Stacks 08AI to three statements about its adjunction

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝒜 = f_*𝒪_Y`.  The **first assertion of Stacks 08AI** is that
`ℱ ↦ f_*ℱ` is an equivalence from the quasi-coherent `𝒪_Y`-modules onto the quasi-coherent
`𝒜`-modules.  This file reduces it to three statements about the adjunction

`𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢  ⊣  ℱ ↦ f_*ℱ`

of `AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction`, namely that the left adjoint
preserves quasi-coherence and that the unit and the counit are invertible at quasi-coherent
modules.  It is the reduction that the scheme-level case of the tag, Stacks 01SB, is assembled
from —
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward` —
transposed to the small étale sites.

The three statements are proved, for every affine morphism, in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineDirectImageEquivalence.lean`, where the reduction
below is applied to give `AlgebraicGeometry.Space.isEquivalence_affineQuasicoherentDirectImage`.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDirectImagePullback` — the candidate quasi-inverse,
  restricted to the quasi-coherent subcategories.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_quasicoherentDirectImage` — the reduction: the functor
  `AlgebraicGeometry.Space.quasicoherentDirectImage` of the tag is an equivalence as soon as the
  left adjoint preserves quasi-coherence and the unit and counit of the adjunction are invertible
  at quasi-coherent modules.
* `AlgebraicGeometry.Space.affineDirectImageEquivalence_of_isIso_unit_counit` — the same, in the
  form `AlgebraicGeometry.Space.AffineDirectImageEquivalence`, the statement of the tag's first
  assertion: for an affine morphism the preservation hypothesis of the functor is discharged by
  `AlgebraicGeometry.Space.directImagePreservesQuasicoherence`, so the three statements below are
  all that the tag's first assertion needs.

## Implementation notes

### How the three statements are obtained

All three have the same base case:
`AlgebraicGeometry.Space.directImageAlgebraPullbackFreeIso` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback_free`
(`StacksFrontier/AlgebraicGeometry/Spaces/DirectImageAlgebraPullbackFree.lean`) compute the left
adjoint on a free `𝒜`-module — it is the free `𝒪_Y`-module on the same type, and so
quasi-coherent — for an arbitrary index type and with no hypothesis on `f`.

* `hL`, that `𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢` carries quasi-coherent `𝒜`-modules to quasi-coherent
  `𝒪_Y`-modules, needs no Beck–Chevalley comparison and nothing local on `X`: as in the
  scheme-level `Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules`,
  the argument is global on the base.
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback_of_extendScalars`
  (`StacksFrontier/AlgebraicGeometry/Spaces/DirectImageAlgebraPullbackQuasicoherent.lean`) deduces
  `hL` for an affine morphism from `AlgebraicGeometry.Space.ExtendScalarsPreservesQuasicoherence`,
  that extension of scalars along `f♯ : 𝒪_X ⟶ 𝒜` — read back as a functor to `𝒪_X`-modules, where
  it is `𝒢 ↦ 𝒜 ⊗_{𝒪_X} 𝒢` — preserves quasi-coherence.  That statement is clause (5) of Stacks
  03M1 once the two constructions of the tensor product are identified, by
  `AlgebraicGeometry.Space.restrictScalarsExtendScalarsIsoTensorModule`
  (`StacksFrontier/AlgebraicGeometry/Spaces/DirectImageAlgebraExtendScalarsTensor.lean`).  The result
  is `AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback`, which is what
  `AlgebraicGeometry.Space.affineDirectImageEquivalence_of_isIso_unit_counit` below takes for its
  `hL`.
* `hunit` and `hcounit`, that the unit and the counit are invertible at quasi-coherent modules.
  For an affine morphism with **representable target** they follow from the base case by a
  colimit argument over a presentation, as in the scheme-level case of the tag: the unit is
  invertible at `𝒜` and the counit at `𝒪_Y`
  (`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_unit` and
  `AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_counit_app_unit`, for an
  arbitrary morphism of algebraic spaces), direct image along an affine morphism with
  representable target preserves the colimit of a diagram of quasi-coherent modules
  (`AlgebraicGeometry.Space.preservesColimit_modulePushforward_of_schemeTarget`, and over `𝒜`
  `AlgebraicGeometry.Space.preservesColimit_moduleDirectImage_of_schemeTarget`), and so the unit
  and the counit are invertible at free modules and at presentations
  (`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_free`,
  `...counit_app_free`, `...unit_app_of_presentation` and `...counit_app_of_presentation`).  The
  representable target is needed because preservation of a colimit is not local on the base.

  For a general target the statements are local on the affine étale charts `V` of `X`
  (`AlgebraicGeometry.Space.isIso_of_isIso_over_affineCharts`), the slice at such a chart carries
  a global presentation
  (`AlgebraicGeometry.Space.hasGlobalPresentation_over_affine_chart_directImageAlgebra`), and the
  base change `f' : V ×_X Y ⟶ V` has a representable target.  What carries the statement from `f'`
  to `f` is the compatibility of the adjunction with restriction to the chart, proved in
  `StacksFrontier/AlgebraicGeometry/Spaces/AffineDirectImageEquivalence.lean` on the level of sites:
  the square of sites formed by base change and étale postcomposition satisfies Beck–Chevalley
  (`AlgebraicGeometry.Space.isIso_chartSquareMate`), so by
  `StacksFrontier/CategoryTheory/Sites/Modules/PushforwardBaseChangeSquare.lean` restriction to the
  chart commutes with direct image.  The results are
  `AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_of_isAffineHom`
  and `...counit_app_of_isAffineHom`.

  Direct image is left exact (`AlgebraicGeometry.Space.preservesFiniteLimits_modulePushforward`),
  so only colimits are at stake.  The almost-cocontinuity criterion for right exactness
  (`AlgebraicGeometry.Space.preservesFiniteColimits_modulePushforward_of_isAlmostCocontinuous`)
  does not apply to affine morphisms: its hypothesis holds for closed immersions and for integral
  universally injective morphisms
  (`StacksFrontier/AlgebraicGeometry/Spaces/ChartBaseChangeAlmostCocontinuous.lean`), but for
  `f : X ⊔ X ⟶ X` the two components of `V ×_X (X ⊔ X)` are a covering that no covering of `V`
  refines.  Nor does the abelian-sheaf form of Stacks 04C2
  (`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms`), which is about
  *integral* morphisms: direct image along an affine morphism is not exact on abelian sheaves.

### The shape of the statements

The three hypotheses are binders of the theorem rather than a named `Prop`, which is the shape of
the scheme-level reduction they transpose.  They are stated about the adjunction's own unit and
counit, so that discharging them says something about `f_*` and not about some other functor of
the same type: `AlgebraicGeometry.Space.quasicoherentDirectImage_comp_ι` identifies the functor
of the conclusion with `AlgebraicGeometry.Space.moduleDirectImage`, and
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` has that functor as its right
adjoint.

## References

* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hL : ∀ G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      G.IsQuasicoherentOnSite →
        ((directImageAlgebraPullback B S hS f).obj G).IsQuasicoherentOnSite)

/-- **The candidate quasi-inverse of Stacks 08AI on the quasi-coherent subcategories.**  If
`𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢` preserves quasi-coherence, it restricts to a functor from the
quasi-coherent `𝒜`-modules to the quasi-coherent `𝒪_Y`-modules. -/
noncomputable def quasicoherentDirectImagePullback :
    (SheafOfModules.isQuasicoherentOnSite
        (structureRingSheafDirectImage B S hS f)).FullSubcategory ⥤
      QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ directImageAlgebraPullback B S hS f)
    fun G ↦ hL G.obj G.property

variable (hqc : DirectImagePreservesQuasicoherence B S hS f)

/-- The unit of the adjunction of Stacks 03D4, at quasi-coherent modules, as an isomorphism of
functors between the quasi-coherent subcategories. -/
noncomputable def quasicoherentDirectImageUnitIso
    (hunit : ∀ G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      G.IsQuasicoherentOnSite →
        IsIso ((directImageAlgebraPullbackAdjunction B S hS f).unit.app G)) :
    𝟭 _ ≅ quasicoherentDirectImagePullback B S hS f hL ⋙
      quasicoherentDirectImage B S hS f hqc :=
  NatIso.ofComponents
    (fun G ↦ ObjectProperty.isoMk _ (@asIso _ _ _ _ _ (hunit G.obj G.property)))
    fun φ ↦ ObjectProperty.hom_ext _
      ((directImageAlgebraPullbackAdjunction B S hS f).unit.naturality φ.hom)

/-- The counit of the adjunction of Stacks 03D4, at quasi-coherent modules, as an isomorphism of
functors between the quasi-coherent subcategories. -/
noncomputable def quasicoherentDirectImageCounitIso
    (hcounit : ∀ M : Modules.{u, u} B S hS Y.1 Y.2, M.IsQuasicoherentOnSite →
      IsIso ((directImageAlgebraPullbackAdjunction B S hS f).counit.app M)) :
    quasicoherentDirectImage B S hS f hqc ⋙
      quasicoherentDirectImagePullback B S hS f hL ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ (@asIso _ _ _ _ _ (hcounit M.obj M.property)))
    fun φ ↦ ObjectProperty.hom_ext _
      ((directImageAlgebraPullbackAdjunction B S hS f).counit.naturality φ.hom)

include hL in
/-- **Reduction of the first assertion of Stacks 08AI.**  The functor `ℱ ↦ f_*ℱ` from the
quasi-coherent `𝒪_Y`-modules to the quasi-coherent `𝒜`-modules is an equivalence of categories
as soon as the left adjoint `𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢` of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` preserves quasi-coherence and the
unit and counit of that adjunction are invertible at quasi-coherent modules.

For an affine morphism all three hypotheses hold: `hL` is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback`
(`StacksFrontier/AlgebraicGeometry/Spaces/DirectImageAlgebraExtendScalarsTensor.lean`), and `hunit`
and `hcounit` are
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_of_isAffineHom` and
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_counit_app_of_isAffineHom`
(`StacksFrontier/AlgebraicGeometry/Spaces/AffineDirectImageEquivalence.lean`). -/
theorem isEquivalence_quasicoherentDirectImage
    (hunit : ∀ G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      G.IsQuasicoherentOnSite →
        IsIso ((directImageAlgebraPullbackAdjunction B S hS f).unit.app G))
    (hcounit : ∀ M : Modules.{u, u} B S hS Y.1 Y.2, M.IsQuasicoherentOnSite →
      IsIso ((directImageAlgebraPullbackAdjunction B S hS f).counit.app M)) :
    (quasicoherentDirectImage B S hS f hqc).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (quasicoherentDirectImage B S hS f hqc)
    (quasicoherentDirectImagePullback B S hS f hL)
    (quasicoherentDirectImageCounitIso B S hS f hL hqc hcounit).symm
    (quasicoherentDirectImageUnitIso B S hS f hL hqc hunit).symm).isEquivalence_functor

include hL in
/-- **Reduction of the first assertion of Stacks 08AI, in the shape of its statement.**  For an
affine morphism of algebraic spaces,
`AlgebraicGeometry.Space.AffineDirectImageEquivalence` holds as soon as the left adjoint of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` preserves quasi-coherence and the
unit and counit of that adjunction are invertible at quasi-coherent modules.

The existential in that statement — that direct image over `𝒜` preserves quasi-coherence — needs
no hypothesis: it is `AlgebraicGeometry.Space.directImagePreservesQuasicoherence`, the second
assertion of the tag.  So the three hypotheses below are all that the tag's first assertion
needs. -/
theorem affineDirectImageEquivalence_of_isIso_unit_counit (hf : IsAffineHom B S hS f.hom)
    (hunit : ∀ G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      G.IsQuasicoherentOnSite →
        IsIso ((directImageAlgebraPullbackAdjunction B S hS f).unit.app G))
    (hcounit : ∀ M : Modules.{u, u} B S hS Y.1 Y.2, M.IsQuasicoherentOnSite →
      IsIso ((directImageAlgebraPullbackAdjunction B S hS f).counit.app M)) :
    AffineDirectImageEquivalence B S hS f :=
  ⟨directImagePreservesQuasicoherence B S hS f hf,
    isEquivalence_quasicoherentDirectImage B S hS f hL
      (directImagePreservesQuasicoherence B S hS f hf) hunit hcounit⟩

end AlgebraicGeometry.Space

end
