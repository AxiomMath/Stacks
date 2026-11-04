module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.StructureSheafProjectiveSections
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatteningBlowupFromAffineCase
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.RaynaudGrusonInduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus

/-!
# The affine case of Stacks 0815, from the Raynaud–Gruson induction

`AlgebraicGeometry.FinitePresentationHasAffineChartFlatteningCentre` is the affine case of the
flatness assertion of [Stacks, Tag 0815] for the structure sheaf: for every datum `f : X ⟶ S`
and quasi-compact open `U ⊆ S` to which 0815 applies, and for every affine open `V ⊆ S` and
affine open `W ⊆ f⁻¹(V)`, a flattening centre on `V` for `𝒪_W` avoiding `V ∩ U`.

`AlgebraicGeometry.hasFlatteningCentre_of_genericFibreFreeBlowup` already proves the *global*
flatness assertion for an arbitrary quasi-coherent module of finite type, so the affine case is
obtained by reading it on one chart. That is what this file does, and it is the easy direction of
the inter-derivability the module documentation of
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartDescent` records: a global centre
restricts to a chart, whereas assembling chart centres into a global one is the whole of
[Stacks, Tag 0814].

## Main results

* `AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre_of_genericFibreFreeBlowup`:
  **the affine case of the flatness assertion of [Stacks, Tag 0815]**, from the conclusion of
  [Stacks, Tag 0811] in the form the induction consumes it. That form is supplied by
  `AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup` in
  `StacksFrontier/AlgebraicGeometry/Flatness/Flattening/GenericFibreFreeBlowup0811.lean`, where the
  hypothesis-free versions of both statements below live.
* `AlgebraicGeometry.finitePresentationHasFlatteningBlowup_of_genericFibreFreeBlowup`:
  **[Stacks, Tag 0815] for the structure sheaf**, from the same, through
  `AlgebraicGeometry.finitePresentationHasFlatteningBlowup_of_affineChartFlatteningCentre`.

## Implementation notes

The module on the chart is the pullback of `𝒪_X` along the inclusion of the affine open `W`,
which is the structure sheaf of `W` (`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`); so it
is of finite presentation by `AlgebraicGeometry.Scheme.unitModule_isFinitePresentation`, and
flat over `V ∩ U` because `f` is flat over `U` — flatness of the structure sheaf over the base
being flatness of the morphism (`AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt`) and the
chart square `W ⟶ X`, `V ⟶ S` being étale
(`AlgebraicGeometry.isFlatOverAt_pullback_of_etale_square`).

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0814](https://stacks.math.columbia.edu/tag/0814)
* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The structure sheaf pulled back twice is the structure sheaf. -/
private def pullbackPullbackUnitIso {X Y Z : Scheme.{u}} (g : Y ⟶ X) (k : Z ⟶ Y) :
    (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj X.unitModule) ≅
      Z.unitModule :=
  (Scheme.Modules.pullback k).mapIso (Scheme.Modules.pullbackUnitIso g) ≪≫
    Scheme.Modules.pullbackUnitIso k

/-- A module isomorphic to the structure sheaf is of finite presentation. -/
private theorem isFinitePresentation_of_iso_unitModule {Z : Scheme.{u}} {M : Z.Modules}
    (e : M ≅ Z.unitModule) : M.IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation Z.ringCatSheaf).prop_of_iso e.symm inferInstance

/-- **The affine case of the flatness assertion of [Stacks, Tag 0815]**, from the conclusion of
[Stacks, Tag 0811] in the form the induction consumes it. On the chart `W ⟶ V` the module is the
structure sheaf of `W`, and
`AlgebraicGeometry.hasFlatteningCentre_of_genericFibreFreeBlowup` — the Raynaud–Gruson induction
— supplies the centre. -/
theorem finitePresentationHasAffineChartFlatteningCentre_of_genericFibreFreeBlowup
    (H : FinitePresentationHasGenericFibreFreeBlowup.{u}) :
    FinitePresentationHasAffineChartFlatteningCentre.{u} := by
  intro X S f U _ _ _ _ hU hflat V W hVW
  have _ : IsAffine V.1.toScheme := V.2
  have _ : IsAffine W.1.toScheme := W.2
  have _ : CompactSpace V.1.toScheme := isCompact_iff_compactSpace.mp V.2.isCompact
  have _ : QuasiSeparatedSpace V.1.toScheme := quasiSeparatedSpace_of_quasiSeparated V.1.ι
  have _ : CompactSpace W.1.toScheme := isCompact_iff_compactSpace.mp W.2.isCompact
  have _ : ((Scheme.Modules.pullback W.1.ι).obj X.unitModule).IsFinitePresentation :=
    isFinitePresentation_of_iso_unitModule (Scheme.Modules.pullbackUnitIso W.1.ι)
  have _ : X.unitModule.IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (Scheme.unitModule X)
  have _ : ((Scheme.Modules.pullback W.1.ι).obj X.unitModule).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType W.1.ι.toLRSHom.toShHom X.unitModule
  have _ : ((Scheme.Modules.pullback W.1.ι).obj X.unitModule).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      W.1.ι.toLRSHom.toShHom X.unitModule
      (inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) X.unitModule))
  have hres : Flat (f ∣_ U) := by rwa [← Scheme.Hom.resLE_eq_morphismRestrict]
  have hflatU : IsFlatOver (f ∣_ U).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj X.unitModule) := fun z ↦
    (isFlatOverAt_iff_of_moduleIso (f ∣_ U).toLRSHom.toShHom
        (Scheme.Modules.pullbackUnitIso (f ⁻¹ᵁ U).ι) z).mpr
      ((isFlatOverAt_unit_iff_isFlatAt (f ∣_ U) z).mpr
        ((Flat.iff_flat_stalkMap (f ∣_ U)).mp hres z))
  have hcomm : W.1.ι ≫ f = f.resLE V.1 W.1 hVW ≫ V.1.ι :=
    (Scheme.Hom.resLE_comp_ι f hVW).symm
  have hGflat : IsFlatOver ((f.resLE V.1 W.1 hVW) ∣_ (V.1.ι ⁻¹ᵁ U)).toLRSHom.toShHom
      ((Scheme.Modules.pullback
          ((f.resLE V.1 W.1 hVW) ⁻¹ᵁ (V.1.ι ⁻¹ᵁ U)).ι).obj
        ((Scheme.Modules.pullback W.1.ι).obj X.unitModule)) := by
    apply isFlatOver_restrict_of_flatOnPreimage (f.resLE V.1 W.1 hVW) _ (V.1.ι ⁻¹ᵁ U)
    intro y hy
    refine isFlatOverAt_pullback_of_etale_square f (f.resLE V.1 W.1 hVW) W.1.ι V.1.ι
      X.unitModule hcomm y ?_
    refine isFlatOverAt_of_open_restriction f X.unitModule U (W.1.ι y) ?_ hflatU
    have hy' : V.1.ι ((f.resLE V.1 W.1 hVW) y) ∈ U := hy
    rwa [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply] at hy'
  exact hasFlatteningCentre_of_genericFibreFreeBlowup H (f.resLE V.1 W.1 hVW)
    ((Scheme.Modules.pullback W.1.ι).obj X.unitModule) (V.1.ι ⁻¹ᵁ U)
    (isCompact_preimage_ι_of_quasiSeparatedSpace U V.1 hU V.2.isCompact)
    (isFinitePresentation_of_iso_unitModule
      (pullbackPullbackUnitIso W.1.ι ((f.resLE V.1 W.1 hVW) ⁻¹ᵁ (V.1.ι ⁻¹ᵁ U)).ι)) hGflat

/-- **The affine case of the flatness assertion of [Stacks, Tag 0815] for an arbitrary
quasi-coherent module**, from the conclusion of [Stacks, Tag 0811] in the form the induction
consumes it.

This is `AlgebraicGeometry.FinitePresentationHasAffineChartFlatteningCentre` at a single datum
and for an arbitrary quasi-coherent module in place of the structure sheaf. That generality is
what the reduction of a morphism locally of finite type to one of finite presentation consumes:
it applies the affine case not to the given morphism but to a scheme of finite presentation over
the base containing a chart as a closed subscheme, and not to the structure sheaf but to the
direct image of a module along that closed immersion. See
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_isQuasiAffine`.

For a module the route is shorter than for the structure sheaf: the Raynaud–Gruson induction
`AlgebraicGeometry.hasFlatteningCentre_of_genericFibreFreeBlowup` proves the *global* flatness
assertion for `G` itself, and `AlgebraicGeometry.AffineChartFlatteningCentre.of_centre`
restricts a global centre to the charts, so no chart datum has to be assembled. The four
hypotheses `AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses` carries are
exactly the four the induction asks for, read through the identification of the restriction of a
module to an open with its pullback
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`). -/
theorem affineChartFlatteningCentreUnderSourceHypotheses_of_genericFibreFreeBlowup
    (H : FinitePresentationHasGenericFibreFreeBlowup.{u}) {T Y : Scheme.{u}} [CompactSpace T]
    [QuasiSeparatedSpace T] [CompactSpace Y] (p : Y ⟶ T) (G : Y.Modules) [G.IsQuasicoherent]
    (A : T.Opens) (hA : IsCompact (A : Set T)) :
    AffineChartFlatteningCentreUnderSourceHypotheses p G A := by
  intro _ _ hGfp hGflat
  have hGfp' : ((Scheme.Modules.pullback (p ⁻¹ᵁ A).ι).obj G).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (p ⁻¹ᵁ A).ι).app G) hGfp
  have hGflat' : IsFlatOver (p ∣_ A).toLRSHom.toShHom
      ((Scheme.Modules.pullback (p ⁻¹ᵁ A).ι).obj G) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isFlatOver_iff_of_moduleIso _
      ((Scheme.Modules.restrictFunctorIsoPullback (p ⁻¹ᵁ A).ι).app G)).mp hGflat
  obtain ⟨I, hIfp, hIdisj, hIflat⟩ :=
    hasFlatteningCentre_of_genericFibreFreeBlowup H p G A hA hGfp' hGflat'
  exact AffineChartFlatteningCentre.of_centre p G A I hIfp hIdisj hIflat

/-- **[Stacks, Tag 0815] for the structure sheaf**, from the conclusion of [Stacks, Tag 0811] in
the form the induction consumes it. -/
theorem finitePresentationHasFlatteningBlowup_of_genericFibreFreeBlowup
    (H : FinitePresentationHasGenericFibreFreeBlowup.{u}) :
    FinitePresentationHasFlatteningBlowup.{u} :=
  finitePresentationHasFlatteningBlowup_of_affineChartFlatteningCentre
    (finitePresentationHasAffineChartFlatteningCentre_of_genericFibreFreeBlowup H)

/-- **The affine case of the flatness assertion of [Stacks, Tag 0815]**, from the flattening
input of the Raynaud–Gruson induction.

The hypothesis is strictly more than [Stacks, Tag 0811] concludes — that tag is proved outright,
and `AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre` gives this conclusion
with nothing granted — so this records the sharper reduction rather than an outstanding
dependency. -/
theorem finitePresentationHasAffineChartFlatteningCentre_of_genericFibreFlatteningBlowup
    (H : FinitePresentationHasGenericFibreFlatteningBlowup.{u}) :
    FinitePresentationHasAffineChartFlatteningCentre.{u} :=
  finitePresentationHasAffineChartFlatteningCentre_of_genericFibreFreeBlowup
    (finitePresentationHasGenericFibreFreeBlowup_of_genericFibreFlatteningBlowup H)

/-- **[Stacks, Tag 0815] for the structure sheaf**, from the flattening input of the
Raynaud–Gruson induction.

As above, the hypothesis is strictly more than [Stacks, Tag 0811] concludes, and
`AlgebraicGeometry.finitePresentationHasFlatteningBlowup` gives this conclusion with nothing
granted. -/
theorem finitePresentationHasFlatteningBlowup_of_genericFibreFlatteningBlowup
    (H : FinitePresentationHasGenericFibreFlatteningBlowup.{u}) :
    FinitePresentationHasFlatteningBlowup.{u} :=
  finitePresentationHasFlatteningBlowup_of_affineChartFlatteningCentre
    (finitePresentationHasAffineChartFlatteningCentre_of_genericFibreFlatteningBlowup H)

end AlgebraicGeometry

end
