module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibre.FibreGeneralization
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReducedLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.Topology.Specialization.Constructible

/-!
# Openness of the geometrically reduced fibre locus

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is flat, proper and
of finite presentation. Then the set of points of `|Y|` at which the fibre of `f` is
geometrically reduced is open in `|Y|` (Stacks 0E0C).

The locus is étale locally constructible (Stacks 0E0A). A locally constructible subset of a
scheme which is stable under generalization is open, because an affine open of a scheme is a
spectral space and there a constructible set stable under generalization is open
(Stacks 0542). Transporting that along an étale atlas turns étale local constructibility plus
chart-wise stability under generalization into openness, so it remains to see that the inverse
image of the locus on every étale scheme chart `h_U ⟶ Y` is stable under generalization.

On such a chart the locus is that of the base change `P ⟶ h_U` of `f`, by Stacks 0E09, and on a
surjective étale chart `h_A ⟶ P` it is the locus of points of `U` over which the scheme
morphism `A ⟶ U` has geometrically reduced fibre. Let `v' ⤳ v` be a specialization in `U` with
geometrically reduced fibre over `v`, and let `a'` be a point of `A` over `v'`. As `P ⟶ h_U` is
proper, hence closed, the image of `a'` in `|P|` specializes to a point lying over `v`; as `P`
is decent, that specialization lifts along the chart to a specialization `a'' ⤳ a₀` in `A` with
`a''` and `a'` over the same point of `|P|` and `a₀` over `v`. Flatness of `A ⟶ U` and
`AlgebraicGeometry.isGeometricallyReducedAt_fiber_of_specializes` make the fibre over `v'`
geometrically reduced at `a''`, and the two étale projections of `A ×_P A` carry this to `a'`.

## Main results

* `AlgebraicGeometry.Space.isOpen_geometricallyReducedFibreLocus`: **Stacks 0E0C**.
* `AlgebraicGeometry.Space.stableUnderGeneralization_preimage_geometricallyReducedFibreLocus`:
  for a flat proper morphism locally of finite presentation, the inverse image of the locus on
  every étale scheme chart of the target is stable under generalization.
* `AlgebraicGeometry.isOpen_of_isLocallyConstructible_of_stableUnderGeneralization`: a locally
  constructible subset of a scheme stable under generalization is open.
* `AlgebraicGeometry.Space.isOpen_of_isEtaleLocallyConstructible_of_chart_generalization`: an
  étale locally constructible subset of the points of an algebraic space whose inverse image
  on every étale scheme chart is stable under generalization is open.
* `AlgebraicGeometry.Space.isOpen_geometricallyReducedFibreLocus_of_chart_generalization`: the
  geometrically reduced fibre locus is open as soon as its inverse image on every étale scheme
  chart of the target is stable under generalization.

## Implementation notes

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance and is
made a local instance here, as in
`StacksFrontier/AlgebraicGeometry/Spaces/ConstructiblePoints.lean`; the openness asserted by
Stacks 0E0C is for that topology on `|Y|`.

The source proves stability under generalization by reducing to a Noetherian base: it writes
the affine base as a limit of affine schemes of finite type over `ℤ`, descends the flat proper
morphism to one of them (Stacks 07SK, 08K0, 08K1) and, over a discrete valuation ring, applies
Stacks 0E0B. Here the Noetherian approximation is carried out on the étale scheme charts only,
pointwise, where it is a statement about rings: the specialization is lifted to the chart first,
using that `f` is closed and its source decent, and the remaining question is the scheme-level
`AlgebraicGeometry.isGeometricallyReducedAt_fiber_of_specializes`. No algebraic space is
descended along a limit, so no size condition on the inverse system enters.

## References

* [Stacks Project, Tag 0E0A](https://stacks.math.columbia.edu/tag/0E0A)
* [Stacks Project, Tag 0E0B](https://stacks.math.columbia.edu/tag/0E0B)
* [Stacks Project, Tag 0E0C](https://stacks.math.columbia.edu/tag/0E0C)
* [Stacks Project, Tag 0E09](https://stacks.math.columbia.edu/tag/0E09)
* [Stacks Project, Tag 0542](https://stacks.math.columbia.edu/tag/0542)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- A locally constructible subset of a scheme which is stable under generalization is open.

Openness is local on an affine open cover, and an affine open of a scheme is a spectral space
in which a constructible set stable under generalization is open. -/
@[ega "IV 12.0.2" "more general", ega "IV 7.9.10" "partial"]
theorem isOpen_of_isLocallyConstructible_of_stableUnderGeneralization
    {T : Scheme.{u}} {E : Set T} (hE : Topology.IsLocallyConstructible E)
    (hgen : StableUnderGeneralization E) : IsOpen E := by
  have hcover : TopologicalSpace.IsOpenCover (fun U : T.affineOpens ↦ U.1) :=
    iSup_affineOpens_eq_top T
  apply hcover.isOpen_iff_coe_preimage.mpr
  intro U
  let : PrespectralSpace (U.1 : Set T) :=
    U.1.2.isOpenEmbedding_subtypeVal.prespectralSpace
  let : QuasiSober (U.1 : Set T) := U.1.2.isOpenEmbedding_subtypeVal.quasiSober
  let : CompactSpace (U.1 : Set T) := isCompact_iff_compactSpace.mp U.2.isCompact
  let : QuasiSeparatedSpace (U.1 : Set T) := @quasiSeparatedSpace_of_isAffine _ U.2
  let : SpectralSpace (U.1 : Set T) := ⟨⟩
  have hcon := (AlgebraicGeometry.isLocallyConstructible_iff_forall_affineOpens E).mp hE U
  exact hcon.isOpen_of_stableUnderGeneralization
    (hgen.preimage U.1.2.isOpenEmbedding_subtypeVal.continuous)

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An étale locally constructible subset of the points of an algebraic space is open as soon
as its inverse image on every étale scheme chart is stable under generalization.

On a surjective étale chart the inverse image is locally constructible and stable under
generalization, hence open by
`AlgebraicGeometry.isOpen_of_isLocallyConstructible_of_stableUnderGeneralization` read through
clause (1) of Stacks 03BX; the chart is open on points by clause (3) and surjective, so the
set is the image of that open inverse image. -/
theorem isOpen_of_isEtaleLocallyConstructible_of_chart_generalization
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
    (E : Set (points B S hS Y)) (hE : IsEtaleLocallyConstructible B S hS Y E)
    (hgen : ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ Y), IsEtale B S hS a →
      StableUnderGeneralization (pointsMap B S hS (yoneda.obj U) a ⁻¹' E)) :
    IsOpen E := by
  obtain ⟨U, a, haSurj, haEtale⟩ := hY.exists_atlas
  have haEt : IsEtale B S hS a := isEtale_of_presheaf_etale B S hS haEtale
  set q := pointsMap B S hS (yoneda.obj U) a with hq
  have hpre : IsOpen (q ⁻¹' E) := by
    refine (schemePointsHomeomorph B S hS U).symm.isOpen_preimage.mp ?_
    exact isOpen_of_isLocallyConstructible_of_stableUnderGeneralization
      (((schemePointsHomeomorph B S hS U).symm.isLocallyConstructible_preimage_iff _).mpr
        (hE U a haEt))
      ((hgen U a haEt).preimage (schemePointsHomeomorph B S hS U).symm.continuous)
  have hsurj : Function.Surjective q :=
    (surjective_iff_surjective_pointsMap B S hS Y hY U a).mp haSurj
  have hopen : IsOpenMap q := isOpenMap_pointsMap_of_etale B S hS hY U a haEtale
  simpa only [Set.image_preimage_eq _ hsurj] using hopen _ hpre

/-- The geometrically reduced fibre locus of a quasi-compact morphism of algebraic spaces which
is locally of finite presentation is open as soon as its inverse image on every étale scheme
chart of the target is stable under generalization.

The locus is étale locally constructible by Stacks 0E0A, so this is
`AlgebraicGeometry.Space.isOpen_of_isEtaleLocallyConstructible_of_chart_generalization`. It is
the part of Stacks 0E0C that uses neither flatness nor properness of the morphism. -/
theorem isOpen_geometricallyReducedFibreLocus_of_chart_generalization
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqc : IsQuasiCompact B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hgen : ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ Y), IsEtale B S hS a →
      StableUnderGeneralization (pointsMap B S hS (yoneda.obj U) a ⁻¹'
        geometricallyReducedFibreLocus B S hS f hX hY)) :
    IsOpen (geometricallyReducedFibreLocus B S hS f hX hY) :=
  isOpen_of_isEtaleLocallyConstructible_of_chart_generalization B S hS Y hY _
    (isEtaleLocallyConstructible_geometricallyReducedFibreLocus B S hS f hX hY hqc hfp) hgen

/-- **The geometrically reduced fibre locus on an étale chart is stable under generalization**
when the morphism is flat and proper and locally of finite presentation.

Base change to the chart `h_U ⟶ Y` turns the inverse image of the locus into the locus of the
base change `P ⟶ h_U`, a flat proper morphism, by Stacks 0E09; on a surjective étale chart
`h_A ⟶ P` it is the scheme-level geometrically reduced fibre locus of `g : A ⟶ U`. Let
`v' ⤳ v` in `U` with the fibre of `g` over `v` geometrically reduced, and let `a'` be a point of
`A` over `v'`. Its image in `|P|` specializes to a point over `v`, `P ⟶ h_U` being closed; that
specialization lifts along the chart, `P` being decent, to `a'' ⤳ a₀` with `a''` and `a'` over
the same point of `|P|` and `g a₀ = v`. The fibre of `g` over `v'` is geometrically reduced at
`a''` by `AlgebraicGeometry.isGeometricallyReducedAt_fiber_of_specializes`,
and so at `a'`, the two being the images of one point of `A ×_P A` under two étale maps. -/
theorem stableUnderGeneralization_preimage_geometricallyReducedFibreLocus
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hflat : IsFlat B S hS f) (hproper : IsProper B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ Y) (ha : IsEtale B S hS a) :
    StableUnderGeneralization (pointsMap B S hS (yoneda.obj U) a ⁻¹'
      geometricallyReducedFibreLocus B S hS f hX hY) := by
  classical
  have haE := (isEtale_iff_presheaf_of_yoneda B S hS a).mp ha
  have hU := isAlgebraicSpace_yoneda B S hS U
  have hP := isAlgebraicSpace_pullback B S hS f a hX hU hY
  set f' := pullback.snd f a with hf'
  have hsqP : IsPullback (pullback.snd f a) (pullback.fst f a) a f :=
    (IsPullback.of_hasPullback f a).flip
  have hflat' : IsFlat B S hS f' := isFlat_of_isPullback B S hS hsqP haE hflat
  have hlfp' : IsLocallyOfFinitePresentation B S hS f' :=
    holdsOnEveryEtaleChart_of_isPullback B S hS hsqP haE hlfp
  have hproper' : IsProper B S hS f' :=
    isProper_of_isPullback B S hS hP hX hU hY (IsPullback.of_hasPullback f a) hproper
  rw [← geometricallyReducedFibreLocus_pullback B S hS f a hX hY hU]
  -- a surjective étale chart of the base change
  obtain ⟨A, i, hiS', hiE'⟩ := hP.exists_atlas
  have hiE : IsEtale B S hS i := isEtale_of_presheaf_etale B S hS hiE'
  have hiS : IsSurjective B S hS i :=
    (surjective_iff_surjective_pointsMap B S hS _ hP A i).mp hiS'
  obtain ⟨hAU, hh⟩ : ∃ hAU : A ⟶ U, yoneda.map hAU = i ≫ f' :=
    ⟨yoneda.preimage (i ≫ f'), yoneda.map_preimage _⟩
  set g := (BigFppfOver.toScheme B S hS).map hAU with hg
  rw [geometricallyReducedFibreLocus_eq_preimage_chart B S hS f' hP i hAU hiE hiS hh]
  refine StableUnderGeneralization.preimage ?_ (schemePointsHomeomorph B S hS U).continuous
  -- the scheme-level statement on `U`
  have hsq : yoneda.map hAU ≫ 𝟙 (yoneda.obj U) = i ≫ f' := by rw [Category.comp_id, hh]
  have : Flat g := hflat' A U i (𝟙 _) hAU hiE' (presheaf_etale_id B S hS U) hsq
  have : LocallyOfFinitePresentation g :=
    hlfp' A U i (𝟙 _) hAU hiE' (presheaf_etale_id B S hS U) hsq
  set eA := schemePointsHomeomorph B S hS A with heA
  set eU := schemePointsHomeomorph B S hS U with heU
  have hpts : ∀ z : points B S hS (yoneda.obj A),
      eU (pointsMap B S hS _ f' (pointsMap B S hS (yoneda.obj A) i z)) = g (eA z) := by
    intro z
    rw [← pointsMap_comp_apply, ← hh]
    exact pointsToScheme_pointsMap B S hS _ _
  have hclosed : IsClosedMap (fun x => eU (pointsMap B S hS _ f' x)) :=
    eU.isClosedMap.comp (isClosed_of_universallyClosed B S hS hU f' hproper'.2.2)
  have hPdec : IsDecentSpace B S hS (pullback f a) :=
    isDecentSpace_source_of_isQuasiSeparated B S hS hP hU f'
      (isQuasiSeparated_of_isSeparated B S hS hproper'.1) (isDecentSpace_yoneda B S hS U)
  intro v v' hvv' hv
  change GeometricallyReduced (g.fiberToSpecResidueField v) at hv
  show GeometricallyReduced (g.fiberToSpecResidueField v')
  rw [geometricallyReduced_iff_forall_isGeometricallyReducedAt]
  intro z
  set a' := g.fiberι v' z with ha'
  have hga' : g a' = v' := (g.fiberHomeo v' z).2
  set x' := pointsMap B S hS (yoneda.obj A) i (eA.symm a') with hx'
  -- `x'` specializes to a point over `v`
  obtain ⟨p, hpcl, hpv⟩ : ∃ p ∈ closure {x'}, eU (pointsMap B S hS _ f' p) = v := by
    have hcl := hclosed _ (isClosed_closure (s := {x'}))
    have hmem : v' ∈ (fun x => eU (pointsMap B S hS _ f' x)) '' closure {x'} :=
      ⟨x', subset_closure rfl, by
        show eU (pointsMap B S hS _ f' x') = v'
        rw [hx', hpts, Homeomorph.apply_symm_apply, hga']⟩
    exact hvv'.mem_closed hcl hmem
  obtain ⟨p₀, rfl⟩ := hiS p
  obtain ⟨p'', hp''p₀, hp''⟩ := generalizingMap_pointsMap_of_isDecentSpace B S hS _ hP
    hPdec A i hiE' ((specializes_iff_mem_closure).mpr hpcl)
  set a'' := eA p'' with ha''
  have hga'' : g a'' = v' := by
    rw [ha'', ← hpts, hp'', hx', hpts, Homeomorph.apply_symm_apply, hga']
  have hga₀ : g (eA p₀) = v := by rw [← hpts]; exact hpv
  -- geometric reducedness at `a''`
  set z'' : g.fiber v' := (g.fiberHomeo v').symm ⟨a'', hga''⟩ with hz''
  have hred'' : _root_.AlgebraicGeometry.IsGeometricallyReducedAt
      (g.fiberToSpecResidueField v') z'' := by
    refine isGeometricallyReducedAt_fiber_of_specializes g z''
      (x := eA p₀) ?_ (by rw [hga₀]; exact hv)
    rw [hz'', Scheme.Hom.fiberι_fiberHomeo_symm]
    exact hp''p₀.map eA.continuous
  -- transfer along the self-intersection of the chart
  let hrep := hiE'.rep
  let R := hrep.pullback i
  have hsqR : IsPullback (yoneda.map (hrep.fst' i)) (yoneda.map (hrep.snd i)) i i :=
    hrep.isPullback' i
  obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS hsqR p'' (eA.symm a')
    (by rw [hp'', hx'])
  have hE₂ : Etale ((BigFppfOver.toScheme B S hS).map (hrep.snd i)) :=
    hiE'.property_snd i
  have hE₁ : Etale ((BigFppfOver.toScheme B S hS).map (hrep.fst' i)) :=
    hiE'.property i _ _ hsqR.flip
  have hRw : hrep.fst' i ≫ hAU = hrep.snd i ≫ hAU := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hh, ← Category.assoc, ← Category.assoc, hsqR.w]
  set gR := (BigFppfOver.toScheme B S hS).map (hrep.snd i ≫ hAU) with hgR
  have he₁ : (BigFppfOver.toScheme B S hS).map (hrep.fst' i) ≫ g = gR := by
    rw [hgR, ← hRw, Functor.map_comp]
  have he₂ : (BigFppfOver.toScheme B S hS).map (hrep.snd i) ≫ g = gR := by
    rw [hgR, Functor.map_comp]
  set eR := schemePointsHomeomorph B S hS R with heR
  have hr₁ : (BigFppfOver.toScheme B S hS).map (hrep.fst' i) (eR w) = a'' := by
    rw [ha'', ← hw₁]
    exact (pointsToScheme_pointsMap B S hS _ _).symm
  have hr₂ : (BigFppfOver.toScheme B S hS).map (hrep.snd i) (eR w) = a' := by
    rw [show a' = eA (eA.symm a') by rw [Homeomorph.apply_symm_apply], ← hw₂]
    exact (pointsToScheme_pointsMap B S hS _ _).symm
  have hgRw : gR (eR w) = v' := by rw [← he₂, Scheme.Hom.comp_apply, hr₂, hga']
  set zR : gR.fiber v' := (gR.fiberHomeo v').symm ⟨eR w, hgRw⟩ with hzR
  have hredR : _root_.AlgebraicGeometry.IsGeometricallyReducedAt
      (gR.fiberToSpecResidueField v') zR :=
    (isGeometricallyReducedAt_fiber_iff_of_etale _ he₁ v' zR z'' (by
      rw [hz'', hzR, Scheme.Hom.fiberι_fiberHomeo_symm, Scheme.Hom.fiberι_fiberHomeo_symm]
      exact hr₁.symm)).mpr hred''
  exact (isGeometricallyReducedAt_fiber_iff_of_etale _ he₂ v' zR z (by
    rw [hzR, Scheme.Hom.fiberι_fiberHomeo_symm]
    exact hr₂.symm)).mp hredR

/-- **Stacks 0E0C.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is flat,
proper and of finite presentation. Then the set of points of `|Y|` at which the fibre of `f` is
geometrically reduced is open in `|Y|`.

The locus is étale locally constructible, Stacks 0E0A, and on every étale scheme chart its
inverse image is stable under generalization,
`AlgebraicGeometry.Space.stableUnderGeneralization_preimage_geometricallyReducedFibreLocus`;
so `AlgebraicGeometry.Space.isOpen_geometricallyReducedFibreLocus_of_chart_generalization`
applies. -/
@[stacks 0E0C, ega "IV 12.2.4" "more general"]
theorem isOpen_geometricallyReducedFibreLocus
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hflat : IsFlat B S hS f) (hproper : IsProper B S hS f)
    (hfp : IsFinitePresentation B S hS f) :
    IsOpen (geometricallyReducedFibreLocus B S hS f hX hY) :=
  isOpen_geometricallyReducedFibreLocus_of_chart_generalization B S hS f hX hY hfp.2.1 hfp.1
    (fun U a ha => stableUnderGeneralization_preimage_geometricallyReducedFibreLocus B S hS f
      hX hY hflat hproper hfp.1 U a ha)

end Space

end AlgebraicGeometry

end
