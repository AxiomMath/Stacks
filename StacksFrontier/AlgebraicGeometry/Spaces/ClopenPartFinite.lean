module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparatedFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleClopenPartFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence

/-!
# Finiteness of the open-and-closed piece of Stacks 082H over the base

`StacksFrontier/AlgebraicGeometry/Spaces/EtaleClopenPartUniversallyClosed.lean` proves the
conclusion of Stacks 082H with its finiteness clause weakened to universal closedness, and
`StacksFrontier/AlgebraicGeometry/Spaces/ClopenPartRepresentable.lean` reduces the missing clause
to one hypothesis: that the kernel pair of the atlas of the piece is affine with finite locally
free projections. This file discharges that hypothesis and draws the finiteness.

The source's step is "since `f` is separated, `V ⟶ U` is separated and `R` is closed in
`Z₁ ×_U Z₁`; since `Z₁ ⟶ U` is finite, the projections `s, t : R ⟶ Z₁` are finite". It is
carried out here for the kernel pair of `z : h_{Z₁} ⟶ P` rather than of its factorisation
through the piece, which is the same thing because the inclusion of the piece is a
monomorphism (`CategoryTheory.IsPullback.of_comp_mono`), and for the separatedness of
`k : P ⟶ h_{Zu}` rather than of `V ⟶ U`, which is what makes no separatedness of the piece
itself necessary. The relation `R` is then the fibre product of the relative diagonal of `k`
with `Z₁ ×_{Zu} Z₁ ⟶ P ×_{Zu} P`, so separatedness of `k` makes `R ⟶ Z₁ ×_{Zu} Z₁` a closed
immersion; `Z₁ ×_{Zu} Z₁` is affine and finite over `Z₁`, so `R` is affine and the projections
are finite, and being also étale they are finite locally free.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_closedImmersion_selfPullback_of_isSeparated`: the self-fibre
  product of a chart of a presheaf separated over an object of the site is represented by an
  object of the site with a closed immersion into the self-fibre product of the base morphism,
  compatibly with the two projections.
* `AlgebraicGeometry.Space.exists_affine_finiteLocallyFree_kernelPair_of_isSeparated`: for an
  étale chart finite over an affine object of the site over which the target is separated, that
  representing object is affine and the two projections are finite locally free. This is the
  hypothesis `hker` of
  `AlgebraicGeometry.Space.exists_iso_yoneda_of_isEtale_comp_mono_of_affine_kernelPair`.
* `AlgebraicGeometry.Space.isClopen_range_pointsMap_of_isEtale_of_isFinite_map`: the image on
  points of the chart is open and closed, with the finiteness hypothesis in the form used here.
* `AlgebraicGeometry.Space.exists_iso_yoneda_lift_range_of_isSeparated_of_isFinite`: the
  open-and-closed piece of Stacks 082H is representable by an affine object of the site, with
  no hypothesis on its kernel pair.
* `AlgebraicGeometry.Space.isFinite_of_affine_surjectiveEtale_atlas_of_isFinite`: a morphism to
  an affine object of the site which is locally of finite type and admits a surjective étale
  atlas finite over the target, from a presheaf identified with an affine object of the site,
  is finite.
* `AlgebraicGeometry.Space.isFinite_ι_openSubspaceOfPoints_range_comp_of_isFinite`: the
  finiteness clause of Stacks 082H for the piece cut out by the image of `|Z₁|`.
* `AlgebraicGeometry.Space.exists_clopen_part_isFinite_of_isEtale_of_isFinite`: the conclusion
  of Stacks 082H with its finiteness clause, deduced from an étale `z : h_{Z₁} ⟶ P` which is
  finite over a separated affine base together with the two conditions on the fibre. This is
  `AlgebraicGeometry.Space.exists_clopen_part_universallyClosed_of_isEtale_of_isFinite` with
  universal closedness replaced by finiteness.

## Implementation notes

The cartesian square identifying the relation is the existing
`Stacks.Spaces.isPullback_selfPullback_diagonal`, and the passage from it to a representing
object of the site is the one already performed, for quasi-compactness instead of affineness,
by `AlgebraicGeometry.Space.exists_compactSpace_selfPullback_of_isSeparated_to_affine`. What
`AlgebraicGeometry.Space.exists_closedImmersion_selfPullback_of_isSeparated` adds to that
statement is the closed immersion itself and its compatibility with the two projections, which
is what identifies the two projections of the relation with morphisms of the site; affineness
of the chart is not needed for it and is not assumed.

Finiteness of the two projections of the self-fibre product of `Z₁ ⟶ Zu` is base change
stability of `AlgebraicGeometry.IsFinite` applied to the image of the cartesian square under
`AlgebraicGeometry.BigFppfOver.toScheme`, which preserves fibre products; affineness of `Z₁`
is not a hypothesis anywhere, since a scheme finite over an affine scheme is affine.

The two properties of the atlas that the finiteness needs — flatness and surjectivity of the
underlying morphism of schemes — are read off the étaleness and the point surjectivity of the
factorisation through the piece, transported along the representing isomorphism by
`CategoryTheory.MorphismProperty.RespectsIso.postcomp` and then turned into properties of a
morphism of the site by `CategoryTheory.MorphismProperty.of_relative_map`. The
`CategoryTheory.MorphismProperty.RespectsIso` instance that the transport needs is the one for
the *relative* property, `CategoryTheory.MorphismProperty.relative_respectsIso`, which instance
search does find; at the toolchain of this development it does *not* find the one for the bare
`AlgebraicGeometry.Etale`, and every use of that here is inside the imported
`AlgebraicGeometry.Space.isEtale_of_comp_mono` and
`AlgebraicGeometry.Space.presheafEtale_of_isEtale_yoneda`, which supply it explicitly from
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`.

`CategoryTheory.MorphismProperty.of_relative_map` does not determine the functor from its
expected type, so the relative property is established as a named hypothesis about
`yoneda.map π₀` before being pushed down to `π₀`; stating it the other way round leaves the
functor a metavariable and the elaboration fails with a stuck `Category` instance problem.

Nothing here carries the tag 082H. What Stacks 082H asserts and this does not is the
*existence*, after an étale base change of the target, of the affine object `Z₁` étale onto `P`
and finite over the base. That is the first three paragraphs of the source proof — the
reduction to an affine base by Decent Spaces 0AC6 and 0AC7, the choice of the affine chart with
Properties of Spaces 03IJ, and the splitting by More on Morphisms 02LN at the level of
algebraic spaces. The other files of this cone number the paragraphs differently and call the
same gap "steps 1 to 5"; what is meant is the same thing, namely everything up to and including
the production of `Z₁`.

No hypothesis of any statement here is an existential, and the hypothesis which packages the
finiteness is on the morphism `ζ : Z₁ ⟶ Zu` of the site whose image is `z ≫ k`, out of `Z₁`,
while the finiteness concluded is of `V.ι ≫ k`, out of the image of `|Z₁|` — different
morphisms with different sources, since the factorisation of `z` through the image is
surjective on points but not an isomorphism. The one statement whose hypotheses do contain part
of a *neighbouring* conclusion is
`AlgebraicGeometry.Space.isFinite_of_affine_surjectiveEtale_atlas_of_isFinite`, which takes the
representability of the piece as data (`hV₀`, `e`, `π₀`, `hπ₀`) rather than as an existential;
that is deliberate — it is the Skolemised conclusion of
`AlgebraicGeometry.Space.exists_iso_yoneda_lift_range_of_isSeparated_of_isFinite`, proved
earlier in this file from hypotheses that mention no representability, and discharged against it
inside `AlgebraicGeometry.Space.isFinite_ι_openSubspaceOfPoints_range_comp_of_isFinite`.
Representability is in any case strictly weaker than the finiteness concluded, which comes from
the atlas and the finite-type hypothesis; the imported
`AlgebraicGeometry.Space.isFinite_of_iso_yoneda_of_flat_surjective_atlas` is stated the same way
and for the same reason.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.Spaces

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The relation of a chart as a closed subscheme of the relation of the base -/

/-- **The relation of a chart of a separated morphism is a closed subscheme of the relation of
the base.** Let `f : X ⟶ h_{Y₀}` be a separated morphism of presheaves on the big fppf site of
`S` and let `φ : h_T ⟶ X` be any morphism from a representable presheaf, with `τ : T ⟶ Y₀` the
morphism of the site underlying `φ ≫ f`. Then the self-fibre product `h_T ×_X h_T` is
represented by an object `R` of the site carrying a closed immersion `ρ : R ⟶ T ×_{Y₀} T`, by
an isomorphism which carries the two projections of the fibre product to the images of
`ρ ≫ pr₁` and `ρ ≫ pr₂`.

The relation is the fibre product of the relative diagonal of `f` with the canonical morphism
`h_{T ×_{Y₀} T} ⟶ X ×_{h_{Y₀}} X`, which is
`Stacks.Spaces.isPullback_selfPullback_diagonal` composed with
`CategoryTheory.Limits.PreservesPullback.iso` for the Yoneda embedding; separatedness of `f`
is by definition (Stacks 03HL) representability of the relative diagonal with closed-immersion
represented base changes, so applying it to that morphism produces `R` and `ρ`.

This strengthens
`AlgebraicGeometry.Space.exists_compactSpace_selfPullback_of_isSeparated_to_affine`, which
records only quasi-compactness of `R` and nothing about the projections. Neither affineness of
`T` nor of `Y₀` is used. -/
theorem exists_closedImmersion_selfPullback_of_isSeparated
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ T : BigFppfOver B S hS}
    {f : X ⟶ yoneda.obj Y₀} (hf : IsSeparated B S hS f) (φ : yoneda.obj T ⟶ X)
    (τ : T ⟶ Y₀) (hτ : φ ≫ f = yoneda.map τ) :
    ∃ (R : BigFppfOver B S hS) (ρ : R ⟶ pullback τ τ) (e : pullback φ φ ≅ yoneda.obj R),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ρ) ∧
      e.hom ≫ yoneda.map (ρ ≫ pullback.fst τ τ) = pullback.fst φ φ ∧
      e.hom ≫ yoneda.map (ρ ≫ pullback.snd τ τ) = pullback.snd φ φ := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have sq1 := isPullback_selfPullback_diagonal f φ hτ
  set isoP := PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) τ τ with hisoP
  have hgc : (pullback.fst (yoneda.map τ) (yoneda.map τ) ≫ φ) ≫ f =
      (pullback.snd (yoneda.map τ) (yoneda.map τ) ≫ φ) ≫ f := by
    rw [Category.assoc, Category.assoc, hτ, pullback.condition]
  set g : yoneda.obj (pullback τ τ) ⟶ pullback f f :=
    isoP.hom ≫ pullback.lift (pullback.fst (yoneda.map τ) (yoneda.map τ) ≫ φ)
      (pullback.snd (yoneda.map τ) (yoneda.map τ) ≫ φ) hgc with hg
  have sq2 : IsPullback (pullback.fst φ φ ≫ φ)
      (pullback.lift (pullback.fst φ φ) (pullback.snd φ φ)
        (by rw [← hτ, ← Category.assoc, ← Category.assoc, pullback.condition]) ≫ isoP.inv)
      (pullback.diagonal f) g :=
    isPullback_of_iso_right (by simpa [hg] using sq1)
  refine ⟨hf.rep.pullback g, hf.rep.snd g,
    sq2.isoIsPullback _ _ (hf.rep.isPullback g), hf.property_snd g, ?_, ?_⟩
  · rw [Functor.map_comp, ← Category.assoc,
      sq2.isoIsPullback_hom_snd _ _ (hf.rep.isPullback g), Category.assoc, hisoP,
      PreservesPullback.iso_inv_fst, pullback.lift_fst]
  · rw [Functor.map_comp, ← Category.assoc,
      sq2.isoIsPullback_hom_snd _ _ (hf.rep.isPullback g), Category.assoc, hisoP,
      PreservesPullback.iso_inv_snd, pullback.lift_snd]

/-- **The kernel pair of an étale chart finite over an affine base is affine with finite locally
free projections.** Let `f : X ⟶ h_{Y₀}` be separated with `Y₀` affine, let `φ : h_T ⟶ X` be
étale, and let the morphism `τ : T ⟶ Y₀` of the site underlying `φ ≫ f` be finite. Then the
kernel pair of `φ` is given by two morphisms `p, q : R ⟶ T` of the site with `R` affine and both
`p` and `q` finite locally free.

This is the hypothesis `hker` of
`AlgebraicGeometry.Space.exists_iso_yoneda_of_isEtale_comp_mono_of_affine_kernelPair`, and the
step "since `f` is separated, `R` is closed in `Z₁ ×_U Z₁`; since `Z₁ ⟶ U` is finite, the
projections are finite" of the proof of Stacks 082H.

The representing object and the closed immersion `ρ : R ⟶ T ×_{Y₀} T` are
`AlgebraicGeometry.Space.exists_closedImmersion_selfPullback_of_isSeparated`, and the two
projections are `ρ ≫ pr₁` and `ρ ≫ pr₂`. Affineness of `T` is not assumed: a scheme finite over
an affine scheme is affine, hence so is `T ×_{Y₀} T`, hence so is its closed subscheme `R`.
Finiteness of the two projections of `T ×_{Y₀} T` is base change stability of
`AlgebraicGeometry.IsFinite`; composing with the closed immersion, which is finite, gives
finiteness of `p` and `q`. They are étale as base changes of `φ`, so
`AlgebraicGeometry.isFiniteLocallyFree_of_etale_of_isFinite` applies. -/
theorem exists_affine_finiteLocallyFree_kernelPair_of_isSeparated
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ T : BigFppfOver B S hS}
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    {f : X ⟶ yoneda.obj Y₀} (hf : IsSeparated B S hS f)
    (φ : yoneda.obj T ⟶ X) (hφ : IsEtale B S hS φ)
    (τ : T ⟶ Y₀) (hτ : φ ≫ f = yoneda.map τ)
    (hτfin : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map τ)) :
    ∃ (R : BigFppfOver B S hS) (p q : R ⟶ T),
      IsPullback (yoneda.map p) (yoneda.map q) φ φ ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj R) ∧
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map p) ∧
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map q) := by
  have _ := hY₀
  have _ := hτfin
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map τ)
  obtain ⟨R, ρ, e, hci, hefst, hesnd⟩ :=
    exists_closedImmersion_selfPullback_of_isSeparated B S hS hf φ τ hτ
  have _ := hci
  have hmapped := (IsPullback.of_hasPullback τ τ).map (BigFppfOver.toScheme B S hS)
  have hsq : IsPullback (yoneda.map (ρ ≫ pullback.fst τ τ))
      (yoneda.map (ρ ≫ pullback.snd τ τ)) φ φ := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ e.symm ?_ ?_
    · refine (cancel_epi e.hom).mp ?_
      rw [← Category.assoc, ← Category.assoc, hefst, hesnd, pullback.condition]
    · rw [Iso.symm_hom, ← hefst, Iso.inv_hom_id_assoc]
    · rw [Iso.symm_hom, ← hesnd, Iso.inv_hom_id_assoc]
  have hφrel : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ :=
    presheafEtale_of_isEtale_yoneda B S hS φ hφ
  have hst : MorphismProperty.IsStableUnderBaseChange
      ((MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have key : ∀ a b : pullback τ τ ⟶ T,
      IsPullback ((BigFppfOver.toScheme B S hS).map b) ((BigFppfOver.toScheme B S hS).map a)
        ((BigFppfOver.toScheme B S hS).map τ) ((BigFppfOver.toScheme B S hS).map τ) →
      IsPullback (yoneda.map (ρ ≫ b)) (yoneda.map (ρ ≫ a)) φ φ →
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map (ρ ≫ a)) := by
    intro a b hs hsq'
    have _ : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map a) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hs hτfin
    have _ : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (ρ ≫ a)) :=
      (MorphismProperty.of_relative_map (hst.of_isPullback hsq' hφrel) :
        MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS) (ρ ≫ a))
    have _ : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map (ρ ≫ a)) := by
      rw [Functor.map_comp]
      exact MorphismProperty.comp_mem _ _ _ inferInstance ‹_›
    exact isFiniteLocallyFree_of_etale_of_isFinite _
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback τ τ)) :=
    IsAffine.of_isPullback hmapped
  exact ⟨R, ρ ≫ pullback.fst τ τ, ρ ≫ pullback.snd τ τ, hsq,
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map ρ),
    key _ _ hmapped.flip hsq.flip, key _ _ hmapped hsq⟩

/-! ### The image of the points of the chart is open and closed -/

/-- **The image on points of an étale morphism finite over a representable base is open and
closed.** This is
`AlgebraicGeometry.Space.isClopen_range_pointsMap_of_isEtale_of_isFinite` with its finiteness
hypothesis in the form the rest of this file uses it: finiteness of the morphism `ζ : Z₁ ⟶ Zu`
of the site whose image is `z ≫ k`. The transport is
`CategoryTheory.MorphismProperty.relative_map` followed by
`AlgebraicGeometry.Space.isFinite_of_presheaf_isFinite`. -/
theorem isClopen_range_pointsMap_of_isEtale_of_isFinite_map
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {Zu Z₁ : BigFppfOver B S hS}
    (k : P ⟶ yoneda.obj Zu) (hk : IsSeparated B S hS k)
    (z : yoneda.obj Z₁ ⟶ P) (hze : IsEtale B S hS z)
    (ζ : Z₁ ⟶ Zu) (hζ : z ≫ k = yoneda.map ζ)
    (hζfin : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map ζ)) :
    _root_.IsClopen (Set.range (pointsMap B S hS (yoneda.obj Z₁) z)) := by
  have hinvIm : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have hzk : IsFinite B S hS (z ≫ k) := by
    rw [hζ]
    exact isFinite_of_presheaf_isFinite B S hS _ (MorphismProperty.relative_map
      (P := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (F := yoneda) hζfin)
  exact isClopen_range_pointsMap_of_isEtale_of_isFinite B S hS
    (isAlgebraicSpace_yoneda B S hS Z₁) hP (isAlgebraicSpace_yoneda B S hS Zu) z k hze hzk hk

/-! ### Representability of the piece, with no hypothesis on its kernel pair -/

/-- **The open-and-closed piece of Stacks 082H is representable by an affine object of the
site.** Let `P` be an algebraic space over `S` separated over an affine object `Zu` of the site
through `k`, let `z : h_{Z₁} ⟶ P` be étale with `ζ : Z₁ ⟶ Zu` the morphism of the site
underlying `z ≫ k` finite.  Openness of the image of `|Z₁|` in `|P|` is not assumed: it is
derived, by `AlgebraicGeometry.Space.isClopen_range_pointsMap_of_isEtale_of_isFinite_map`.
Then the open
subspace of `P` cut out by that image is representable by an object of the site with affine
underlying scheme, by an isomorphism carrying the factorisation of `z` to a morphism of the
site.

This is `AlgebraicGeometry.Space.exists_iso_yoneda_lift_openSubspaceOfPoints_range` with its
hypothesis on the kernel pair discharged by
`AlgebraicGeometry.Space.exists_affine_finiteLocallyFree_kernelPair_of_isSeparated`. The kernel
pair computed there is that of `z`, and the one asked for is that of the factorisation of `z`
through the subspace; they agree because the inclusion of the subspace is a monomorphism, which
is `CategoryTheory.IsPullback.of_comp_mono`. Affineness of `Z₁` is not assumed: `Z₁` is finite
over the affine `Zu`. -/
theorem exists_iso_yoneda_lift_range_of_isSeparated_of_isFinite
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {Zu Z₁ : BigFppfOver B S hS}
    (hZu : IsAffine ((BigFppfOver.toScheme B S hS).obj Zu))
    (k : P ⟶ yoneda.obj Zu) (hk : IsSeparated B S hS k)
    (z : yoneda.obj Z₁ ⟶ P) (hze : IsEtale B S hS z)
    (ζ : Z₁ ⟶ Zu) (hζ : z ≫ k = yoneda.map ζ)
    (hζfin : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map ζ)) :
    ∃ (V₀ : BigFppfOver B S hS) (π₀ : Z₁ ⟶ V₀)
      (e : (openSubspaceOfPoints B S hS P
        (Set.range (pointsMap B S hS (yoneda.obj Z₁) z))).toFunctor ≅ yoneda.obj V₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₀) ∧
        Subfunctor.lift z (range_le_openSubspaceOfPoints_range_pointsMap z) ≫ e.hom =
          yoneda.map π₀ := by
  have _ := hZu
  have _ := hζfin
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z₁) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map ζ)
  have hopen : _root_.IsOpen (Set.range (pointsMap B S hS (yoneda.obj Z₁) z)) :=
    (isClopen_range_pointsMap_of_isEtale_of_isFinite_map B S hS hP k hk z hze ζ hζ hζfin).2
  obtain ⟨R, p, q, hsq, hRaff, hpFLF, hqFLF⟩ :=
    exists_affine_finiteLocallyFree_kernelPair_of_isSeparated B S hS hZu hk z hze ζ hζ hζfin
  refine exists_iso_yoneda_lift_openSubspaceOfPoints_range B S hS hP z hze hopen
    ⟨R, p, q, ?_, hRaff, hpFLF, hqFLF⟩
  refine IsPullback.of_comp_mono (m := (openSubspaceOfPoints B S hS P
    (Set.range (pointsMap B S hS (yoneda.obj Z₁) z))).ι) ?_ ?_
  · refine (cancel_mono (openSubspaceOfPoints B S hS P
      (Set.range (pointsMap B S hS (yoneda.obj Z₁) z))).ι).mp ?_
    rw [Category.assoc, Category.assoc, Subfunctor.lift_ι]
    exact hsq.w
  · rw [Subfunctor.lift_ι]
    exact hsq

/-! ### The finiteness clause -/

/-- **A morphism to an affine object of the site with a surjective étale atlas finite over the
target is finite.** Let `kV : V ⟶ h_{Zu}` be locally of finite type with `Zu` affine, let
`l : h_{Z₁} ⟶ V` be étale and surjective in the relatively representable sense with
`ζ : Z₁ ⟶ Zu` the morphism of the site underlying `l ≫ kV` finite, and let `V` be isomorphic to
`h_{V₀}` with `V₀` affine by an isomorphism carrying `l` to a morphism of the site. Then `kV` is
a finite morphism of algebraic spaces over `S`.

This is `AlgebraicGeometry.Space.isFinite_of_iso_yoneda_of_flat_surjective_atlas` with its
flatness and surjectivity hypotheses read off `l`: the morphism of the site to which the
isomorphism carries `l` has the same relatively representable properties as `l` by
`CategoryTheory.MorphismProperty.RespectsIso.postcomp`, and
`CategoryTheory.MorphismProperty.of_relative_map` turns them into properties of the underlying
morphism of schemes, flatness following from étaleness. The morphism `V₀ ⟶ Zu` through which
`kV` factors is the preimage under Yoneda of `e.inv ≫ kV`, and its composite with the atlas is
`ζ` by faithfulness. -/
theorem isFinite_of_affine_surjectiveEtale_atlas_of_isFinite
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Zu Z₁ V₀ : BigFppfOver B S hS}
    (hZu : IsAffine ((BigFppfOver.toScheme B S hS).obj Zu))
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (kV : V ⟶ yoneda.obj Zu) (l : yoneda.obj Z₁ ⟶ V)
    (hlE : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf l)
    (hlS : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf l)
    (ζ : Z₁ ⟶ Zu) (hζ : l ≫ kV = yoneda.map ζ)
    (hζfin : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map ζ))
    (e : V ≅ yoneda.obj V₀) (π₀ : Z₁ ⟶ V₀) (hπ₀ : l ≫ e.hom = yoneda.map π₀)
    (hft : IsLocallyOfFiniteType B S hS kV) :
    IsFinite B S hS kV := by
  obtain ⟨j, hj⟩ : ∃ j : V₀ ⟶ Zu, yoneda.map j = e.inv ≫ kV :=
    ⟨yoneda.preimage _, Functor.map_preimage _ _⟩
  have hcomm : kV ≫ (Iso.refl (yoneda.obj Zu)).hom = e.hom ≫ yoneda.map j := by
    rw [hj, Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  have hπj : π₀ ≫ j = ζ := by
    refine (yoneda (C := BigFppfOver B S hS)).map_injective ?_
    rw [Functor.map_comp, ← hπ₀, hj, Category.assoc, Iso.hom_inv_id_assoc, hζ]
  have hπ : ∀ {P : MorphismProperty Scheme.{u}},
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf l →
      MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS) π₀ := fun h =>
    MorphismProperty.of_relative_map (by
      rw [← hπ₀]
      exact MorphismProperty.RespectsIso.postcomp _ e.hom _ h)
  have hEt := hπ hlE
  have hSu := hπ hlS
  have _ : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map π₀) := hEt
  refine isFinite_of_iso_yoneda_of_flat_surjective_atlas B S hS kV π₀ j hV₀ hZu
    inferInstance hSu ?_ e (Iso.refl _) hcomm hft
  rw [hπj]
  exact hζfin

/-- **The finiteness clause of Stacks 082H.** Let `P` be an algebraic space over `S` separated
over an affine object `Zu` of the site through `k`, let `z : h_{Z₁} ⟶ P` be étale with `z ≫ k`
the image of a finite morphism `ζ : Z₁ ⟶ Zu` of the site.  Openness of the image of `|Z₁|` in
`|P|` is derived rather than assumed, as above.  If `k` is locally of finite type then the
composite of `k` with the inclusion of
the open subspace cut out by that image is a finite morphism of algebraic spaces over `S`.

This is `AlgebraicGeometry.Space.isFinite_of_affine_surjectiveEtale_atlas_of_isFinite` applied
to the factorisation of `z` through the subspace, which is étale by
`AlgebraicGeometry.Space.isEtale_of_comp_mono` and surjective on points by
`AlgebraicGeometry.Space.isSurjective_lift_openSubspaceOfPoints_range` — point surjectivity
being the relatively representable notion by Tag 03H5 — and representable by an affine object
of the site by
`AlgebraicGeometry.Space.exists_iso_yoneda_lift_range_of_isSeparated_of_isFinite`. The subspace
is locally of finite type over `P` because its inclusion is étale, so the composite is locally
of finite type over `Zu`.

It is the clause that `StacksFrontier/AlgebraicGeometry/Spaces/EtaleClopenPartUniversallyClosed.lean`
leaves open, where it appears weakened to universal closedness. -/
theorem isFinite_ι_openSubspaceOfPoints_range_comp_of_isFinite
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {Zu Z₁ : BigFppfOver B S hS}
    (hZu : IsAffine ((BigFppfOver.toScheme B S hS).obj Zu))
    (k : P ⟶ yoneda.obj Zu) (hk : IsSeparated B S hS k)
    (hft : IsLocallyOfFiniteType B S hS k)
    (z : yoneda.obj Z₁ ⟶ P) (hze : IsEtale B S hS z)
    (ζ : Z₁ ⟶ Zu) (hζ : z ≫ k = yoneda.map ζ)
    (hζfin : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map ζ)) :
    IsFinite B S hS ((openSubspaceOfPoints B S hS P
      (Set.range (pointsMap B S hS (yoneda.obj Z₁) z))).ι ≫ k) := by
  have hopen : _root_.IsOpen (Set.range (pointsMap B S hS (yoneda.obj Z₁) z)) :=
    (isClopen_range_pointsMap_of_isEtale_of_isFinite_map B S hS hP k hk z hze ζ hζ hζfin).2
  obtain ⟨V₀, π₀, e, hV₀, hπ₀⟩ := exists_iso_yoneda_lift_range_of_isSeparated_of_isFinite
    B S hS hP hZu k hk z hze ζ hζ hζfin
  have hVs : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS (yoneda.obj Z₁) z))) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hP _ hopen
  have hlE : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (Subfunctor.lift z (range_le_openSubspaceOfPoints_range_pointsMap z)) :=
    presheafEtale_of_isEtale_yoneda B S hS _ (isEtale_of_comp_mono B S hS _
      (openSubspaceOfPoints B S hS P
        (Set.range (pointsMap B S hS (yoneda.obj Z₁) z))).ι
      (by rw [Subfunctor.lift_ι]; exact hze))
  have hlS := (presheafSurjective_iff_isSurjective_yoneda B S hS
    (openSubspaceOfPoints B S hS P
      (Set.range (pointsMap B S hS (yoneda.obj Z₁) z))).toFunctor hVs.1 Z₁
    (Subfunctor.lift z (range_le_openSubspaceOfPoints_range_pointsMap z))).mpr
    (isSurjective_lift_openSubspaceOfPoints_range B S hS z)
  refine isFinite_of_affine_surjectiveEtale_atlas_of_isFinite B S hS hZu hV₀ _ _ hlE hlS ζ ?_
    hζfin e π₀ hπ₀ ?_
  · rw [← Category.assoc, Subfunctor.lift_ι]
    exact hζ
  · exact isLocallyOfFiniteType_comp' B S hS _ k hP (isAlgebraicSpace_yoneda B S hS Zu)
      (isLocallyOfFiniteType_of_isEtale' B S hS _ (isEtale_ι_of_isOpenSubspace hVs)) hft

/-! ### The conclusion of Stacks 082H with its finiteness clause -/

/-- **The conclusion of Stacks 082H with its finiteness clause.** Let `P` be an algebraic space
over `S` with two morphisms `k₁ : P ⟶ h_{Zu}` and `k₂ : P ⟶ Zx` — in the application to Stacks
082H the two projections of `U ×_Y X` — with `Zu` an affine object of the site, let `u` be a
point of `|Zu|` and `x` finitely many points of `|Zx|`. Suppose `z : h_{Z₁} ⟶ P` is étale, the
morphism `ζ : Z₁ ⟶ Zu` of the site underlying `z ≫ k₁` is finite, `k₁` is separated and locally
of finite type, every point of `|Z₁|` over `u` maps to one of the `x i`, and no point of `|P|`
outside the image of `|Z₁|` which lies over `u` does. Then `P` decomposes into two
subfunctors which are open and closed subspaces, locally cover `P`, are locally disjoint, satisfy
the two conditions on the fibre in the exact shape Stacks 082H states them, and the second of
which is **finite** over the base.

This is `AlgebraicGeometry.Space.exists_clopen_part_universallyClosed_of_isEtale_of_isFinite`
with universal closedness of `V.ι ≫ k₁` replaced by finiteness, which is
`AlgebraicGeometry.Space.isFinite_ι_openSubspaceOfPoints_range_comp_of_isFinite`; the base is
required to be an affine object of the site rather than an arbitrary algebraic space, which is
the situation the first three steps of the source proof arrange.

What Stacks 082H asserts and this does not is the existence of such a `z` after an étale base
change of `Y`; see the module documentation. -/
theorem exists_clopen_part_isFinite_of_isEtale_of_isFinite
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {P Zx : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {Zu Z₁ : BigFppfOver B S hS}
    (hZu : IsAffine ((BigFppfOver.toScheme B S hS).obj Zu))
    (k₁ : P ⟶ yoneda.obj Zu) (k₂ : P ⟶ Zx) (hk : IsSeparated B S hS k₁)
    (hft : IsLocallyOfFiniteType B S hS k₁)
    (u : points B S hS (yoneda.obj Zu)) {n : ℕ} (x : Fin n → points B S hS Zx)
    (z : yoneda.obj Z₁ ⟶ P) (hze : IsEtale B S hS z)
    (ζ : Z₁ ⟶ Zu) (hζ : z ≫ k₁ = yoneda.map ζ)
    (hζfin : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map ζ))
    (hVpts : ∀ w : points B S hS (yoneda.obj Z₁),
      pointsMap B S hS (yoneda.obj Z₁) (z ≫ k₁) w = u →
        ∃ i, pointsMap B S hS (yoneda.obj Z₁) (z ≫ k₂) w = x i)
    (hWpts : ∀ p : points B S hS P, p ∉ Set.range (pointsMap B S hS (yoneda.obj Z₁) z) →
      pointsMap B S hS P k₁ p = u → ∀ i, pointsMap B S hS P k₂ p ≠ x i) :
    ∃ W V : Subfunctor P,
      IsOpenSubspace B S hS W ∧ IsClosedSubspace B S hS W ∧
      IsOpenSubspace B S hS V ∧ IsClosedSubspace B S hS V ∧
      (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W ⊓ V = (⊥ : Subfunctor P).sheafify (BigFppfOver.topology B S hS) ∧
      IsFinite B S hS (V.ι ≫ k₁) ∧
      (∀ v : points B S hS V.toFunctor,
        pointsMap B S hS V.toFunctor (V.ι ≫ k₁) v = u →
          ∃ i, pointsMap B S hS V.toFunctor (V.ι ≫ k₂) v = x i) ∧
      (∀ w : points B S hS W.toFunctor,
        pointsMap B S hS W.toFunctor (W.ι ≫ k₁) w = u →
          ∀ i, pointsMap B S hS W.toFunctor (W.ι ≫ k₂) w ≠ x i) := by
  have hclopen : _root_.IsClopen (Set.range (pointsMap B S hS (yoneda.obj Z₁) z)) :=
    isClopen_range_pointsMap_of_isEtale_of_isFinite_map B S hS hP k₁ hk z hze ζ hζ hζfin
  have hTo : _root_.IsOpen (Set.range (pointsMap B S hS (yoneda.obj Z₁) z)) := hclopen.2
  have hTc : _root_.IsClosed (Set.range (pointsMap B S hS (yoneda.obj Z₁) z)) := hclopen.1
  refine ⟨openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS (yoneda.obj Z₁) z))ᶜ,
    openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS (yoneda.obj Z₁) z)),
    isOpenSubspace_openSubspaceOfPoints B S hS hP _ hTc.isOpen_compl,
    isClosedSubspace_openSubspaceOfPoints B S hS hP _ hTc.isOpen_compl hTo.isClosed_compl,
    isOpenSubspace_openSubspaceOfPoints B S hS hP _ hTo,
    isClosedSubspace_openSubspaceOfPoints B S hS hP _ hTo hTc,
    sheafify_sup_openSubspaceOfPoints_eq_top B S hS _ hTo hTc,
    inf_openSubspaceOfPoints_eq_sheafify_bot B S hS _,
    isFinite_ι_openSubspaceOfPoints_range_comp_of_isFinite B S hS hP hZu k₁ hk hft z hze ζ hζ
      hζfin, ?_, ?_⟩
  · intro v hv
    rw [pointsMap_comp_apply] at hv ⊢
    obtain ⟨w₁, hw₁⟩ := (range_pointsMap_ι_openSubspaceOfPoints B S hS _).le ⟨v, rfl⟩
    rw [← hw₁, ← pointsMap_comp_apply] at hv
    obtain ⟨i, hi⟩ := hVpts w₁ hv
    exact ⟨i, by rw [← hw₁, ← pointsMap_comp_apply]; exact hi⟩
  · intro w hw i
    rw [pointsMap_comp_apply] at hw ⊢
    exact hWpts _ ((range_pointsMap_ι_openSubspaceOfPoints B S hS _).le ⟨w, rfl⟩) hw i

end AlgebraicGeometry.Space

end
