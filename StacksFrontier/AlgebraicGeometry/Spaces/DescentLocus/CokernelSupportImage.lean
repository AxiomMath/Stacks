module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealZerothSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingStratificationFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ConstructibleSets
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedProperSupportUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteIff
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators

/-!
# The image of the support of a cokernel

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and `φ : E ⟶ F` a map of
quasi-coherent `𝒪_X`-modules with `F` of finite type. Write `C = |f|(Supp(Coker φ)) ⊆ |Y|`.
This file proves three facts about `C`.

* For every morphism `g : Y' ⟶ Y` of algebraic spaces, the pullback of `φ` to `X ×_Y Y'` is an
  epimorphism exactly when the image of `|Y'|` misses `C`. This is the pointwise form of
  Stacks 09TP,
  `AlgebraicGeometry.Space.ModuleMapSituation.isSurjectiveAt_iff_range_pointsMap_subset`, for an
  arbitrary algebraic space `Y'` and the categorical fibre product, with the same proof.
* If `f` is universally closed, `C` is closed (Stacks 0CZG).
* If `f` is quasi-compact and locally of finite presentation, `E` is of finite type and `F` of
  finite presentation, then `C` is étale locally constructible. Indeed `Coker φ` is of finite
  presentation (Stacks 0H98), so the closed subspace `Z₀ ⊆ X` cut out by its zeroth Fitting
  ideal has a finitely presented inclusion (Stacks 0CZ5, 084Q) and point set `Supp(Coker φ)`
  (Stacks 0CZ6); Chevalley's theorem for algebraic spaces (Stacks 0ECX), applied to all of
  `|Z₀|` along `Z₀ ⟶ X ⟶ Y`, makes `C` étale locally constructible.

## Main results

* `AlgebraicGeometry.Space.epi_modulePullback_map_iff_isZero_cokernel`
* `AlgebraicGeometry.Space.epi_modulePullback_fst_map_iff_range_subset`
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_cokernel`
* `AlgebraicGeometry.Space.isClosed_image_supportOfSheaf_cokernel`
* `AlgebraicGeometry.Space.isEtaleLocallyConstructible_image_supportOfSheaf_cokernel`

## References

* [Stacks Project, Tag 09TP](https://stacks.math.columbia.edu/tag/09TP)
* [Stacks Project, Tag 0CZ6](https://stacks.math.columbia.edu/tag/0CZ6)
* [Stacks Project, Tag 0ECX](https://stacks.math.columbia.edu/tag/0ECX)
* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The pullback of a map of modules along a morphism of algebraic spaces is an epimorphism
exactly when the pullback of its cokernel vanishes: pullback is a left adjoint, so it preserves
cokernels. -/
theorem epi_modulePullback_map_iff_isZero_cokernel {X' X : AlgebraicSpaces B S hS}
    (g : X' ⟶ X) {E F : Modules.{u, u} B S hS X.1 X.2} (φ : E ⟶ F) :
    Epi ((modulePullback B S hS g).map φ) ↔
      IsZero ((modulePullback B S hS g).obj (cokernel φ)) := by
  have hadj := modulePullbackAdjunction B S hS g
  have := hadj.isLeftAdjoint
  have hpc : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS g) :=
    hadj.leftAdjoint_preservesColimits
  rw [Preadditive.epi_iff_isZero_cokernel]
  exact (PreservesCokernel.iso (modulePullback B S hS g) φ).isZero_iff.symm

/-- **The pointwise form of Stacks 09TP along an arbitrary base change.** Let `f : X ⟶ Y` and
`g : Y' ⟶ Y` be morphisms of algebraic spaces and `φ : E ⟶ F` a map of quasi-coherent
`𝒪_X`-modules with `F` of finite type. The pullback of `φ` along the projection
`X ×_Y Y' ⟶ X` is an epimorphism exactly when the image of `|Y'|` in `|Y|` misses
`|f|(Supp(Coker φ))`. -/
theorem epi_modulePullback_fst_map_iff_range_subset {X Y Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) {E F : Modules.{u, u} B S hS X.1 X.2}
    [E.IsQuasicoherentOnSite] [F.IsQuasicoherentOnSite]
    (hF : SheafOfModules.IsFiniteTypeOnSite F) (φ : E ⟶ F) :
    Epi ((modulePullback B S hS (pullback.fst f g)).map φ) ↔
      Set.range (pointsMap B S hS Y'.1 g.hom) ⊆
        (pointsMap B S hS X.1 f.hom ''
          supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
            (cokernel φ : Modules.{u, u} B S hS X.1 X.2)))ᶜ := by
  have hsq := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g)
  rw [epi_modulePullback_map_iff_isZero_cokernel,
    ← supportOfSheaf_eq_empty_iff_isZero B S hS _ _,
    supportOfSheaf_modulePullback_eq B S hS _ _
      (isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 φ)
      (isFiniteTypeOnSite_cokernel_of_isFiniteTypeOnSite B S hS X.1 X.2 φ hF)]
  refine ⟨?_, fun h => ?_⟩
  · rintro h b ⟨s, rfl⟩ ⟨x, hxZ, hxb⟩
    obtain ⟨w, hwx, -⟩ := exists_points_of_isPullback B S hS hsq x s hxb
    exact Set.eq_empty_iff_forall_notMem.1 h w (by rwa [Set.mem_preimage, hwx])
  · exact Set.eq_empty_iff_forall_notMem.2 fun w hw =>
      h ⟨pointsMap B S hS _ (pullback.snd f g).hom w, rfl⟩
        ⟨pointsMap B S hS _ (pullback.fst f g).hom w, hw, pointsMap_apply_comm B S hS hsq.w w⟩

/-- **Stacks 0H98 on an algebraic space.** The cokernel of a map from a module of finite type
to a module of finite presentation on the small étale site of an algebraic space is of finite
presentation. -/
theorem isFinitePresentationOnSite_cokernel {X : AlgebraicSpaces B S hS}
    {E F : Modules.{u, u} B S hS X.1 X.2} (φ : E ⟶ F)
    (hE : SheafOfModules.IsFiniteTypeOnSite E) (hF : SheafOfModules.IsFinitePresentationOnSite F) :
    SheafOfModules.IsFinitePresentationOnSite (cokernel φ) := by
  have : F.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation F).1 hF
  have : E.IsFiniteType := Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite E hE
  exact (SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation _).2
    (Stacks.SheafOfModules.LocalCokernel.isFinitePresentation_cokernel
      (smallEtaleRingedSite B S hS X.1 X.2) φ)

/-- **Stacks 0CZG for a cokernel.** If `f` is universally closed and `F` is of finite type,
the image `|f|(Supp(Coker φ))` is closed in `|Y|`. -/
theorem isClosed_image_supportOfSheaf_cokernel {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : UniversallyClosed B S hS f.hom) {E F : Modules.{u, u} B S hS X.1 X.2}
    (hF : SheafOfModules.IsFiniteTypeOnSite F) (φ : E ⟶ F) :
    IsClosed (pointsMap B S hS X.1 f.hom ''
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        (cokernel φ : Modules.{u, u} B S hS X.1 X.2))) := by
  have := isFiniteTypeOnSite_cokernel_of_isFiniteTypeOnSite B S hS X.1 X.2 φ hF
  exact isClosed_image_of_universallyClosed B S hS X.2 Y.2 f.hom hf _
    (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 (cokernel φ))

/-- **The image of the support of a cokernel is étale locally constructible.** If `f` is
quasi-compact and locally of finite presentation, `E` and `F` are quasi-coherent, `E` is of
finite type and `F` of finite presentation, then `|f|(Supp(Coker φ))` is étale locally
constructible in `|Y|`.

`Supp(Coker φ)` is the point set of the closed subspace `Z₀` cut out by the zeroth Fitting ideal
of `Coker φ` (Stacks 0CZ6), whose inclusion is of finite presentation because `Coker φ` is
(Stacks 0H98, 0CZ5, 084Q); Chevalley's theorem (Stacks 0ECX) applies to all of `|Z₀|` along the
quasi-compact, locally finitely presented composite `Z₀ ⟶ X ⟶ Y`. -/
theorem isEtaleLocallyConstructible_image_supportOfSheaf_cokernel
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hqc : IsQuasiCompact B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) {E F : Modules.{u, u} B S hS X.1 X.2}
    [E.IsQuasicoherentOnSite] [F.IsQuasicoherentOnSite]
    (hE : SheafOfModules.IsFiniteTypeOnSite E) (hF : SheafOfModules.IsFinitePresentationOnSite F)
    (φ : E ⟶ F) :
    IsEtaleLocallyConstructible B S hS Y.1 (pointsMap B S hS X.1 f.hom ''
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        (cokernel φ : Modules.{u, u} B S hS X.1 X.2))) := by
  have hQqc := isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 φ
  have hQfp := isFinitePresentationOnSite_cokernel φ hE hF
  obtain ⟨Z, hZ, -⟩ :=
    exists_fittingClosedSubspaces_of_isFiniteTypeOnSite B S hS X (cokernel φ) hQqc inferInstance
  have hι := isFinitePresentation_ι_of_definingIdealSheaf_eq_fittingIdeal_zero B S hS X
    (cokernel φ) hQqc hQfp (Z 0) (hZ 0)
  have hrange := (range_pointsMap_schemeTheoreticSupport_eq_supportOfSheaf B S hS X
    (cokernel φ) (Z 0) (hZ 0)).2.1
  have hcomp_qc : IsQuasiCompact B S hS ((Z 0).1.ι ≫ f.hom) :=
    IsQuasiCompact.comp B S hS X.2 Y.2 (isQuasiCompact_of_isClosedImmersion' B S hS (Z 0).2.2)
      hqc
  have hcomp_lfp : IsLocallyOfFinitePresentation B S hS ((Z 0).1.ι ≫ f.hom) :=
    isLocallyOfFinitePresentation_comp B S hS (Z 0).2.1 X.2 Y.2 _ _ hι.1 hlfp
  have huniv : IsEtaleLocallyConstructible B S hS (Z 0).1.toFunctor Set.univ := by
    intro U g _
    rw [Set.preimage_univ]
    exact Topology.IsLocallyConstructible.univ
  have h := isEtaleLocallyConstructible_image B S hS (Z 0).2.1 Y.2 ((Z 0).1.ι ≫ f.hom)
    hcomp_qc hcomp_lfp Set.univ huniv
  have himage : pointsMap B S hS (Z 0).1.toFunctor ((Z 0).1.ι ≫ f.hom) '' Set.univ =
      pointsMap B S hS X.1 f.hom ''
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
          (cokernel φ : Modules.{u, u} B S hS X.1 X.2)) := by
    rw [← hrange, Set.image_univ, pointsMap_comp, Set.range_comp]
  rwa [himage] at h

end AlgebraicGeometry.Space
