module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectRepresentedChartStalks
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectEssSurjAffineChart
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentZariskiSchemeHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.RepresentedAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentHomDescentAssembly

/-!
# Stacks 0DKQ, (1) ⇔ (2), at a represented chart

This file proves `AlgebraicGeometry.Space.RelativelyPerfectRepresentedChart`, the input of the
affine case of the essential surjectivity in Stacks 0DKW: for `f = h_g ≫ b : h_T ⟶ Y` flat and
locally of finite presentation with `b` étale, `ε^*E₀` is `Y`-perfect exactly when `E₀` is
`T'`-perfect in the sense of schemes (for `E₀ ∈ D_QCoh(𝒪_T)` in the direction (1) ⇒ (2)).

* Pseudo-coherence crosses `ε^*` by Stacks 08HE
  (`AlgebraicGeometry.Space.isPseudoCoherent_zariskiEtaleDerived_iff`).
* The Tor clause is read stalkwise on both sides.  On the scheme, it is a local uniform bound on
  the Tor amplitude of the stalks `E₀_y` over `𝒪_{T', g(y)}`
  (`AlgebraicGeometry.Space.exists_relStalkTorAmp_of_locallyHasFiniteTorDimension`); on the
  space, a local uniform bound on the geometric stalks (Stacks 0DJJ).  On an affine chart
  `Spec A ⟶ T` over `Spec R ⟶ T'` both are the Tor amplitudes of the localisations of a tilde
  model of the restriction of `E₀` (Stacks 06Z0, 04KF, 05VL, 0B67); the étale `b` is invisible
  at the geometric stalks (Stacks 05V5, 04NG).  One direction reads the bound off the
  quasi-compact charts, the other glues the charts along the family of their étale inclusions
  (`AlgebraicGeometry.Space.locallyHasFiniteTorDimension_of_isEtale_family`).  The comparison of
  the Zariski and small étale Tor dimensions of Stacks 0DK7 is not used.

The corollary
`AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectColimit_of_comparison` is
Stacks 0DKW from full faithfulness and the comparison `Φ` of the derived pullbacks only, and
`Space.RelativeDescentSituation.relativelyPerfectColimit_of_homotopyPullbackCoherence` is Stacks
0DKW from the single internal input `RepresentedHomotopyPullbackCoherence`.

Nothing here is registered.  For a general square of étale scheme charts the library states the
two implications as
`AlgebraicGeometry.Space.isPerfectRelativeTo_chartObject_of_isPerfectRelativeToCanonical` and
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_isPerfectRelativeTo_chartObject` in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/RelativeSchemeCharts.lean`, through
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_representedZariskiDerivedPullback_iff`;
Stacks 0DKQ itself is registered on
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_tfae_chartDiagram`.

## References

* [Stacks Project, Tag 0DKQ](https://stacks.math.columbia.edu/tag/0DKQ)
* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Space

/-! ### Pseudo-coherence across `ε^*` -/

section PseudoCoherence

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Pseudo-coherence crosses `ε^*`** (Stacks 08HE, both directions, read on the represented
algebraic space): `ε^*E₀` is pseudo-coherent on the small étale site of `h_T` exactly when `E₀` is
pseudo-coherent on the scheme underlying `T`. -/
theorem isPseudoCoherent_zariskiEtaleDerived_iff (T : BigFppfOver B S hS)
    (E₀ : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))) :
    (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).IsPseudoCoherent
        ((zariskiEtaleDerived B S hS T).obj E₀) ↔
      RingedSpace.IsPseudoCoherent (X := ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace) E₀ :=
  ⟨fun h => isPseudoCoherent_of_representedDerivedAssociatedModule B S hS T E₀ h,
    fun h => (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m =>
      isPseudoCoherentFrom_representedDerivedAssociatedModule B S hS T E₀ m
        ((RingedSpace.isPseudoCoherent_iff_forall E₀).1 h m)⟩

end PseudoCoherence

/-! ### Quasi-coherence of a pseudo-coherent object -/

section Quasicoherent

attribute [local instance 10000] HasDerivedCategory.standard

/-- A pseudo-coherent object of `D(𝒪_X)` on a scheme has quasi-coherent cohomology sheaves
(`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`), in the spelling of the
cohomology sheaves of `AlgebraicGeometry.Space.RelativelyPerfectRepresentedChart`. -/
theorem isQuasicoherent_homology_of_isPseudoCoherent_structureSheafRing (X : Scheme.{u})
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      i).obj E).IsQuasicoherent :=
  isQuasicoherentDerived_of_isPseudoCoherent X E hE i

end Quasicoherent

/-! ### The Tor clause across `ε^*` -/

section Tor

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {T T' : BigFppfOver B S hS} {Y : AlgebraicSpaces B S hS}

/-- **The Tor clause, from the space to the scheme** (the Tor half of (1) ⇒ (2) of Stacks 0DKQ at
a represented chart).  For `b : h_{T'} ⟶ Y` étale and `E₀ ∈ D_QCoh(𝒪_T)`, if `ε^*E₀`, read over
`(h_g ≫ b)⁻¹𝒪_Y`, locally has finite Tor dimension, then `E₀`, read over `g⁻¹𝒪_{T'}`, locally has
finite Tor dimension: on every affine chart of `g` one interval bounds the stalks
(`AlgebraicGeometry.Space.exists_relStalkTorAmp_representedAffineChartPiece`). -/
theorem locallyHasFiniteTorDimension_of_hasLocallyFiniteTorDimensionAlong_represented
    (g : T ⟶ T') (b : yoneda.obj T' ⟶ Y.1) (hb : IsEtale B S hS b)
    (E₀ : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)))
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
        E₀).IsQuasicoherent)
    (hE : HasLocallyFiniteTorDimensionAlong
      (ObjectProperty.homMk (yoneda.map g ≫ b) :
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      ((zariskiEtaleDerived B S hS T).obj E₀)) :
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage ((BigFppfOver.toScheme B S hS).obj T').toRingedSpace
        ((BigFppfOver.toScheme B S hS).map g).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _)
      ((Scheme.Hom.derivedScalarRestriction ((BigFppfOver.toScheme B S hS).map g)).obj E₀) := by
  refine locallyHasFiniteTorDimension_of_forall_exists_relStalkTorAmp _ E₀ fun x => ?_
  obtain ⟨c, hx, -⟩ := exists_representedAffineChartPiece g
    (N := (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens)) (x := x) trivial
  obtain ⟨a₀, b₀, h⟩ := exists_relStalkTorAmp_representedAffineChartPiece c b hb E₀ hE₀ hE
  refine ⟨((BigFppfOver.toScheme B S hS).map c.α).opensRange, hx, a₀, b₀, fun y hy => ?_⟩
  obtain ⟨q, rfl⟩ := hy
  exact h q

/-- The étale inclusions of the affine charts of a family of affine charts of `g`, one through
each point, cover the small étale site of `h_T`. -/
theorem coversTop_representedAffineChartPiece (g : T ⟶ T')
    (c : (BigFppfOver.toScheme B S hS).obj T → RepresentedAffineChartPiece g)
    (hc : ∀ x, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (c x).α)) :
    (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).J.CoversTop
      (fun p : Σ x, (smallEtaleRingedSite B S hS
          (yoneda.obj (specFppfOver B S hS (c x).hA (c x).gA))
          (isAlgebraicSpace_yoneda B S hS _)).C =>
        (smallEtaleRingedSitePostcomp B S hS (representedSpaceMap B S hS (c p.1).α)
          (isEtale_yoneda_map_of_isOpenImmersion (c p.1).α)).obj p.2) := by
  intro U
  refine (SmallEtale.topology B S hS (yoneda.obj T)).superset_covering ?_
    (SmallEtale.coversTop_of_jointlySurjective B S hS (yoneda.obj T)
      (fun x => (smallEtalePostcomp B S hS (representedSpaceMap B S hS (c x).α)
        (isEtale_yoneda_map_of_isOpenImmersion (c x).α)).obj
          (idEtaleChart B S hS (specFppfOver B S hS (c x).hA (c x).gA))) (fun p => ?_) U)
  · rintro Z k ⟨x, ⟨m⟩⟩
    exact ⟨⟨x, idEtaleChart B S hS _⟩, ⟨m⟩⟩
  · obtain ⟨y, rfl⟩ := (pointsEquivScheme B S hS T).symm.surjective p
    obtain ⟨q, hq⟩ := hc y
    refine ⟨y, (pointsEquivScheme B S hS (specFppfOver B S hS (c y).hA (c y).gA)).symm q, ?_⟩
    show pointsMap B S hS (yoneda.obj (specFppfOver B S hS (c y).hA (c y).gA))
      (𝟙 _ ≫ yoneda.map (c y).α)
      ((pointsEquivScheme B S hS (specFppfOver B S hS (c y).hA (c y).gA)).symm q) = _
    rw [Category.id_comp, ChartBranch.pointsEquivScheme_symm_pointsMap, hq]

end Tor

section TorGlue

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {T T' : BigFppfOver B S hS} {Y : AlgebraicSpaces B S hS}

/-- **The Tor clause, from the scheme to the space** (the Tor half of (2) ⇒ (1) of Stacks 0DKQ at
a represented chart).  For `b : h_{T'} ⟶ Y` étale and `E₀ ∈ D_QCoh(𝒪_T)`, if `E₀`, read over
`g⁻¹𝒪_{T'}`, locally has finite Tor dimension, then so does `ε^*E₀`, read over
`(h_g ≫ b)⁻¹𝒪_Y`.  Every point has an affine chart of `g` inside a neighbourhood carrying one
interval; there the geometric stalks of the pullback of `ε^*E₀` are bounded by it
(`AlgebraicGeometry.Space.geometricStalkTorAmplitude_representedAffineChartPiece`), and the
charts cover `h_T` (`AlgebraicGeometry.Space.coversTop_representedAffineChartPiece`), along which
the Tor clause descends
(`AlgebraicGeometry.Space.locallyHasFiniteTorDimension_of_isEtale_family`). -/
theorem hasLocallyFiniteTorDimensionAlong_of_locallyHasFiniteTorDimension_represented
    (g : T ⟶ T') (b : yoneda.obj T' ⟶ Y.1) (hb : IsEtale B S hS b)
    (E₀ : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)))
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
        E₀).IsQuasicoherent)
    (hZ : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage ((BigFppfOver.toScheme B S hS).obj T').toRingedSpace
        ((BigFppfOver.toScheme B S hS).map g).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _)
      ((Scheme.Hom.derivedScalarRestriction ((BigFppfOver.toScheme B S hS).map g)).obj E₀)) :
    HasLocallyFiniteTorDimensionAlong
      (ObjectProperty.homMk (yoneda.map g ≫ b) :
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      ((zariskiEtaleDerived B S hS T).obj E₀) := by
  choose N hxN a₀ b₀ hN using exists_relStalkTorAmp_of_locallyHasFiniteTorDimension _ E₀ hZ
  choose c hxc hcN using fun x => exists_representedAffineChartPiece g (hxN x)
  refine locallyHasFiniteTorDimension_of_isEtale_family
    (fun x => representedSpaceMap B S hS (c x).α)
    (fun x => isEtale_yoneda_map_of_isOpenImmersion (c x).α)
    (coversTop_representedAffineChartPiece g c hxc) _ _ fun x => ?_
  refine (locallyHasFiniteTorDimension_derivedScalarRestriction_iff B S hS _ _ _).2 fun U =>
    ⟨⊤, GrothendieckTopology.top_mem _ _, fun V k _ => ⟨a₀ x, b₀ x, fun ū _ => ?_⟩⟩
  exact geometricStalkTorAmplitude_representedAffineChartPiece (c x) b hb E₀ hE₀ (a₀ x) (b₀ x)
    (fun q => hN x _ (hcN x ⟨q, rfl⟩)) ū

end TorGlue

/-! ### Stacks 0DKQ, (1) ⇔ (2), at a represented chart -/

section Main

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 6000] preadditive_smallEtaleModules_model

attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DKQ, (1) ⇔ (2), at a represented chart**
(`AlgebraicGeometry.Space.RelativelyPerfectRepresentedChart`).  Let `f = h_g ≫ b : h_T ⟶ Y` be
flat and locally of finite presentation, with `b : h_{T'} ⟶ Y` étale and `g : T ⟶ T'` flat and
locally of finite presentation on underlying schemes.  For `E₀ ∈ D_QCoh(𝒪_T)`, if `ε^*E₀` is
`Y`-perfect then `E₀` is `T'`-perfect; and every `T'`-perfect `E₀` has `ε^*E₀` `Y`-perfect.

Pseudo-coherence crosses `ε^*` by Stacks 08HE
(`AlgebraicGeometry.Space.isPseudoCoherent_zariskiEtaleDerived_iff`); the Tor clause is read
stalkwise on affine charts of `g`
(`locallyHasFiniteTorDimension_of_hasLocallyFiniteTorDimensionAlong_represented` and
`hasLocallyFiniteTorDimensionAlong_of_locallyHasFiniteTorDimension_represented`); in the
direction (2) ⇒ (1) quasi-coherence of `E₀` comes from its pseudo-coherence.

Unregistered.  For a general square of étale scheme charts the two implications are
`AlgebraicGeometry.Space.isPerfectRelativeTo_chartObject_of_isPerfectRelativeToCanonical` and
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_isPerfectRelativeTo_chartObject`;
Stacks 0DKQ itself is registered on
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_tfae_chartDiagram`. -/
theorem relativelyPerfectRepresentedChart : RelativelyPerfectRepresentedChart B S hS := by
  intro T T' Y g b f hb hgf hfl hlfp _ _ E₀
  subst hgf
  exact ⟨fun hE₀ hE => ⟨(isPseudoCoherent_zariskiEtaleDerived_iff B S hS T E₀).1 hE.1,
      locallyHasFiniteTorDimension_of_hasLocallyFiniteTorDimensionAlong_represented g b hb E₀
        hE₀ hE.2⟩,
    fun hE => ⟨(isPseudoCoherent_zariskiEtaleDerived_iff B S hS T E₀).2 hE.1,
      hasLocallyFiniteTorDimensionAlong_of_locallyHasFiniteTorDimension_represented g b hb E₀
        (isQuasicoherent_homology_of_isPseudoCoherent_structureSheafRing _ E₀ hE.1) hE.2⟩⟩

namespace RelativeDescentSituation

attribute [local instance] isDirected_laterIndex

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation B S hS hZ I)

/-- **Stacks 0DKW from full faithfulness and the comparison of the Zariski and the small étale
derived pullbacks.**
`AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectColimit_of_representedChart`
with Stacks 0DKQ at represented charts discharged
(`AlgebraicGeometry.Space.relativelyPerfectRepresentedChart`).  The inputs left are full
faithfulness of every situation (`hff`, clauses (4), (5) of Stacks 0DKW, from Stacks 0DKV, proved
by `AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectFullyFaithful_proved`) and
the comparison `Φ`. -/
theorem relativelyPerfectColimit_of_comparison {P : DerivedPullbackComposition B S hS}
    (Φ : RepresentedDerivedPullbackComparison B S hS P)
    (hff : ∀ D' : RelativeDescentSituation B S hS hZ I, D'.RelativelyPerfectFullyFaithful) :
    D.RelativelyPerfectColimit :=
  D.relativelyPerfectColimit_of_representedChart Φ (relativelyPerfectRepresentedChart B S hS) hff

/-- **Stacks 0DKW from the underived compatibility of `h^*ε^* ≅ ε^*r^*` with the compositors**
(`hcoh : AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence B S hS`), its only input,
itself proved by `AlgebraicGeometry.Space.representedHomotopyPullbackCoherence`: the comparison is
`AlgebraicGeometry.Space.representedDerivedPullbackComparisonCanonical hcoh`, and full
faithfulness is
`RelativeDescentSituation.relativelyPerfectFullyFaithful_of_homotopyPullbackCoherence`. -/
theorem relativelyPerfectColimit_of_homotopyPullbackCoherence
    (hcoh : RepresentedHomotopyPullbackCoherence B S hS) : D.RelativelyPerfectColimit :=
  D.relativelyPerfectColimit_of_comparison (representedDerivedPullbackComparisonCanonical hcoh)
    fun D' => D'.relativelyPerfectFullyFaithful_of_homotopyPullbackCoherence hcoh

end RelativeDescentSituation

end Main

end AlgebraicGeometry.Space

end
