module

public import StacksFrontier.AlgebraicGeometry.Blowup.Separation
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Flat
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus

/-!
# Flattening the strict transform of a scheme by a blowup

Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be of finite type and
quasi-separated and let `U ⊆ S` be a quasi-compact open. Then there is a `U`-admissible blowup
`S' ⟶ S` along which the strict transform of `X` becomes flat over `S'`.

What turns the module statement into a statement about schemes is that the strict transform of
`𝒪_X` is the direct image, along the closed immersion of the strict transform of `X` into
`X ×_S S'`, of the structure sheaf of that strict transform: flatness of the one over the blowup
is flatness of the other.

## Main definitions

* `AlgebraicGeometry.strictTransformSheafComapUnitIso`: the strict transform of `𝒪_X` along the
  blowup of `X` in the inverse image `I·𝒪_X` is the structure sheaf of that blowup.

## Main results

* `AlgebraicGeometry.flat_strictTransformToBlowUp_iff`: the strict transform of `X` is flat over
  the blowup of `S` in `I` exactly when the strict transform of `𝒪_X` is flat over it.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform`: flatness of the strict
  transform of `X` from the chart predicate `AlgebraicGeometry.AffineChartFlatteningCentre`, the
  gluing step of the proof of [Stacks, Tag 081R]. The tag itself is proved in full as
  `exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform_of_flat`: the same
  conclusion unconditionally when `f` is already flat.

## Implementation notes

The bridge `AlgebraicGeometry.flat_strictTransformToBlowUp_iff` composes four facts. By
[Stacks, Tag 080E] the strict transform of `X` along the blowup of `S` in `I` is the blowup of
`X` in `I·𝒪_X`, and the strict transform of `𝒪_X` is the direct image along that closed
immersion of the strict transform of `𝒪_X` relative to `I·𝒪_X`
(`AlgebraicGeometry.strictTransformSheafBlowUpIso`). That inner strict transform is the
structure sheaf of the blowup of `X` in `I·𝒪_X`, because the identity of `X` is flat and so
[Stacks, Tag 080F] part (2) makes the defining quotient map invertible. Flatness over a base
passes between a quasi-coherent module and its direct image along an affine morphism by
[Stacks, Tag 0FLM], and flatness of the structure sheaf read as a module over itself
([Stacks, Tag 08KT]) is flatness of the morphism ([Stacks, Tag 02N3]) by
`AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt`. The leftover isomorphism of the two
presentations of the strict transform is cancelled on the left, an isomorphism being flat.

**What the carried hypothesis costs.** `AlgebraicGeometry.AffineChartFlatteningCentre f 𝒪_X U`
is the affine case of the flatness assertion of [Stacks, Tag 0815] for the structure sheaf; by
the bridge above it is the conclusion below, read on the affine charts of `f`. It is
satisfiable, and the source's own proof is what satisfies it: on a chart `W ⟶ V` of affine opens
[Stacks, Tag 04II] (`AlgebraicGeometry.exists_immersion_affineSpace`) immerses `W` over `V`
into a relative affine space, `AlgebraicGeometry.Scheme.Hom.liftCoborder` factors that immersion
as a closed immersion `i` into an open `V'` of the affine space, `V' ⟶ V` is locally of finite
presentation, and `i_*𝒪_W` is a quasi-coherent `𝒪_{V'}`-module of finite type which is of finite
presentation and flat over `V ∩ U`. So all five hypotheses of [Stacks, Tag 0815] hold for the
data `i_*𝒪_W / V' / V`, and [Stacks, Tag 080G]
(`AlgebraicGeometry.strictTransformSheafPushforwardIso`) carries the flatness it produces back
to the strict transform of `𝒪_W`. That chain is the only place hypothesis (2) of the source —
`X_U ⟶ U` flat and locally of finite presentation — is used, which is why it is not assumed
below. On the region where no blowup is needed the hypothesis is unconditional,
`AlgebraicGeometry.AffineChartFlatteningCentre.of_isFlatOver`, whence
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform_of_flat`.

**Finite presentation.** The source concludes as well that the strict transform is of finite
presentation over `S'`. That assertion is recovered from flatness by [Stacks, Tag 081N] once a
retrocompact scheme-theoretically dense open of the blowup is available; this is done in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFinitePresentationFromFlat`,
where the chart predicate is also produced from hypothesis (2) and [Stacks, Tag 081R] is proved in
full as
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`.

The strict transform of `X` is `AlgebraicGeometry.strictTransformToBlowUp`, the closed immersion
of `Stacks.StrictTransform.scheme` into `X ×_S S'` followed by the projection to the blowup,
which is the spelling [Stacks, Tag 081S] and [Stacks, Tag 081T] consume.

## References

* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
* [Stacks Project, Tag 080G](https://stacks.math.columbia.edu/tag/080G)
* [Stacks Project, Tag 081N](https://stacks.math.columbia.edu/tag/081N)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : S.IdealSheafData)

/-- The structure sheaf of `X`, read as a module over itself, is flat over the base exactly when
the morphism is flat. -/
private theorem isFlatOver_unitModule_iff_flat {X Y : Scheme.{u}} (g : X ⟶ Y) :
    IsFlatOver g.toLRSHom.toShHom X.unitModule ↔ Flat g :=
  (forall_congr' fun z ↦ isFlatOverAt_unit_iff_isFlatAt g z).trans (Flat.iff_flat_stalkMap g).symm

/-- The structure sheaf of `X`, read as a module over itself, is flat over `X` at every point:
the identity is a flat morphism. -/
theorem isFlatOverAt_unitModule_id (x : X) :
    IsFlatOverAt (Scheme.Hom.toLRSHom (𝟙 X : X ⟶ X)).toShHom X.unitModule x :=
  (isFlatOver_unitModule_iff_flat (𝟙 X)).mpr inferInstance x

/-- **The strict transform of `𝒪_X` along the blowup of `X` in `I·𝒪_X` is the structure sheaf of
that blowup.** The identity of `X` is flat, so by [Stacks, Tag 080F] part (2) the quotient map
defining the strict transform is invertible, and the pullback of `𝒪_X` along the projection of
the base change `X ×_X X'` is the structure sheaf of `X ×_X X'`. -/
def strictTransformSheafComapUnitIso :
    Stacks.StrictTransform.sheaf (𝟙 X : X ⟶ X) (blowUpToBase (I.comap f))
        (exceptionalIdeal (I.comap f)) X.unitModule ≅
      (Stacks.StrictTransform.baseChange (𝟙 X : X ⟶ X) (blowUpToBase (I.comap f))).unitModule :=
  haveI : IsIso (Stacks.StrictTransform.π (𝟙 X : X ⟶ X) (blowUpToBase (I.comap f))
      (exceptionalIdeal (I.comap f)) X.unitModule) :=
    isIso_strictTransformSheaf_quotient_of_flat_at_exceptional (𝟙 X : X ⟶ X) (I.comap f)
      X.unitModule fun x _ ↦ isFlatOverAt_unitModule_id x
  (asIso (Stacks.StrictTransform.π (𝟙 X : X ⟶ X) (blowUpToBase (I.comap f))
      (exceptionalIdeal (I.comap f)) X.unitModule)).symm ≪≫
    Scheme.Modules.pullbackUnitIso (pullback.fst (𝟙 X : X ⟶ X) (blowUpToBase (I.comap f)))

/-- The closed immersion of [Stacks, Tag 080E] followed by the projection to the blowup is the
structure morphism of the strict transform, up to the identification of the two presentations of
it. -/
theorem strictTransformBlowUpι_comp_snd :
    strictTransformBlowUpι f I ≫ pullback.snd f (blowUpToBase I) =
      (strictTransformBlowUpComapIso f I).hom ≫ strictTransformToBlowUp f I :=
  Category.assoc _ _ _

/-- **The strict transform of a scheme is flat over the blowup exactly when the strict transform
of its structure sheaf is.** The strict transform of `X` is a closed subscheme of `X ×_S S'`, so
flatness over `S'` of the structure sheaf of the one is flatness over `S'` of its direct image
on the other, which is the strict transform of `𝒪_X`. -/
theorem flat_strictTransformToBlowUp_iff :
    Flat (strictTransformToBlowUp f I) ↔
      IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) X.unitModule) := by
  have _ : (Stacks.StrictTransform.sheaf (𝟙 X : X ⟶ X) (blowUpToBase (I.comap f))
      (exceptionalIdeal (I.comap f)) X.unitModule).IsQuasicoherent := inferInstance
  have h1 : IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) X.unitModule) ↔
      IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
        ((Scheme.Modules.pushforward (strictTransformBlowUpι f I)).obj
          (Stacks.StrictTransform.sheaf (𝟙 X : X ⟶ X) (blowUpToBase (I.comap f))
            (exceptionalIdeal (I.comap f)) X.unitModule)) :=
    isFlatOver_iff_of_moduleIso _ (strictTransformSheafBlowUpIso f I X.unitModule)
  have h2 := isFlatOver_pushforward_iff (strictTransformBlowUpι f I)
    (pullback.snd f (blowUpToBase I))
    (Stacks.StrictTransform.sheaf (𝟙 X : X ⟶ X) (blowUpToBase (I.comap f))
      (exceptionalIdeal (I.comap f)) X.unitModule)
  have h3 := isFlatOver_iff_of_moduleIso
    (strictTransformBlowUpι f I ≫ pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
    (strictTransformSheafComapUnitIso f I)
  have h4 := isFlatOver_unitModule_iff_flat
    (strictTransformBlowUpι f I ≫ pullback.snd f (blowUpToBase I))
  have h5 : Flat (strictTransformBlowUpι f I ≫ pullback.snd f (blowUpToBase I)) ↔
      Flat (strictTransformToBlowUp f I) := by
    rw [strictTransformBlowUpι_comp_snd f I]
    have _ : IsOpenImmersion (strictTransformBlowUpComapIso f I).hom :=
      IsOpenImmersion.of_isIso _
    have _ : IsOpenImmersion (strictTransformBlowUpComapIso f I).inv :=
      IsOpenImmersion.of_isIso _
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have _ := h
      have hc : (strictTransformBlowUpComapIso f I).inv ≫
          (strictTransformBlowUpComapIso f I).hom ≫ strictTransformToBlowUp f I =
            strictTransformToBlowUp f I := by
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      rw [← hc]
      infer_instance
    · have _ := h
      infer_instance
  exact h5.symm.trans (h4.symm.trans (h3.symm.trans (h2.trans h1.symm)))

/-- **Flatness of the strict transform from the affine charts.** Let `S` be a quasi-compact and
quasi-separated scheme, let `f : X ⟶ S` be of finite type and quasi-separated and let `U ⊆ S` be
a quasi-compact open. If `AlgebraicGeometry.AffineChartFlatteningCentre` holds for the structure
sheaf of `X`, there is a centre `I` on `S`, finitely presented and supported away from `U`,
exhibiting the blowup of `S` in `I` as a `U`-admissible blowup, such that the strict transform of
`X` along that blowup is flat over it.

The chart predicate gives the centre and the flatness of the strict transform of `𝒪_X`, and
`AlgebraicGeometry.flat_strictTransformToBlowUp_iff` reads that as flatness of the strict
transform of `X`. This is the gluing step of the proof of [Stacks, Tag 081R]; the tag itself,
under exactly the source's hypotheses and with both clauses of its conclusion, is
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`.
-/
theorem exists_isAdmissibleBlowup_flat_strictTransform [CompactSpace S] [QuasiSeparatedSpace S]
    [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f] (U : S.Opens)
    (hU : IsCompact (U : Set S)) (H : AffineChartFlatteningCentre f X.unitModule U) :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
        Disjoint (U : Set S) (I.support : Set S) ∧
          Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
            Flat (strictTransformToBlowUp f I) := by
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨I, hfp, hdisj, hadm, hflat⟩ :=
    AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver f X.unitModule U hU H
  exact ⟨I, hfp, hdisj, hadm, (flat_strictTransformToBlowUp_iff f I).mpr hflat⟩

/-- A morphism which is already flat needs no blowup: on every affine chart the unit ideal serves
as a centre, because the strict transform of a module flat over the base is flat over the blowup
for any centre at all.

This exhibits the hypothesis of
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform` on the whole region where the
conclusion is not in doubt. -/
theorem exists_isAdmissibleBlowup_flat_strictTransform_of_flat [CompactSpace S]
    [QuasiSeparatedSpace S] [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (U : S.Opens) (hU : IsCompact (U : Set S)) :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
        Disjoint (U : Set S) (I.support : Set S) ∧
          Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
            Flat (strictTransformToBlowUp f I) :=
  exists_isAdmissibleBlowup_flat_strictTransform f U hU
    (AffineChartFlatteningCentre.of_isFlatOver f X.unitModule U
      ((isFlatOver_unitModule_iff_flat f).mpr inferInstance))

end AlgebraicGeometry

end
