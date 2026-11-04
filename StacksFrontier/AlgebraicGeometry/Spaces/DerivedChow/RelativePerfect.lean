module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseBaseChangeTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.RelativePseudoCoherentPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeAbsoluteChartDictionary
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BoundedBelowCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedHomBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatSingleDegreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeFibrewiseBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardAffineConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPushforwardSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackCompAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso
public import StacksFrontier.Homology.Perfect.BaseChange
public import StacksFrontier.Homology.Perfect.Saturation
import StacksCore.Tactic.StacksAttribute

/-!
# Relative perfectness from perfect derived sections against perfect objects

Let `X` be an algebraic space separated, of finite presentation and flat over a ring `A`, and
`K ∈ D_QCoh(𝒪_X)` such that `RΓ(X, E ⊗^𝐋 K)` is perfect over `A` for every perfect `E`. Stacks
0GFL says that `K` is `Spec(A)`-perfect. Under these hypotheses `K` and its derived pullbacks to
affine base changes of `X`, in particular to its fibres, are locally bounded below.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_isZero_homology_representedAffineDerivedSections`: for `U`
  affine, a morphism `𝒪_U ⟶ N[q]` vanishes when `Hᵠ(RΓ(U, N)) = 0`.
* `AlgebraicGeometry.Space.isLocallyBoundedBelow_of_isPerfect_derivedSections_tensor`: `K` is
  locally bounded below.
* `isLocallyBoundedBelow_smallEtaleDerivedModulePullback_of_isPerfect_derivedSections_tensor`:
  the derived pullback of `K` to an affine base change `X ×_T T'` is locally bounded below.
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_isPerfect_derivedSections_tensor`:
  Stacks 0GFL for `K ∈ D(𝒪_X)` with quasi-coherent cohomology.
* `QuasicoherentDerivedCategory.isPerfectRelativeToCanonical_of_isPerfect_derivedSections`:
  **Stacks 0GFL**, for `K` an object of `D_QCoh(𝒪_X)`.

## References

* [Stacks Project, Tag 0GFL](https://stacks.math.columbia.edu/tag/0GFL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space.DerivedChow

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  SmallEtale.instHasSheafifyOver SmallEtale.instWEqualsLocallyBijectiveOver

section Affine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Morphisms out of the structure sheaf of an affine space are detected in one degree.** For
`U` affine and `N ∈ D(𝒪_U)` with `Hᵠ(RΓ(U, N)) = 0`, every morphism `𝒪_U ⟶ N[q]` is zero. -/
theorem eq_zero_of_isZero_homology_representedAffineDerivedSections (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (N : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
    {q : ℤ} (hN : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((representedAffineDerivedSections B S hS U).obj N)))
    (g : (DerivedCategory.singleFunctor _ 0).obj
      (structureModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) ⟶ N⟦q⟧) : g = 0 := by
  set adj := representedAffineDerivedAdjunction B S hS U
  set i := representedAffineDerivedAssociatedSingleUnitIso B S hS U 0
  have hz : IsZero ((DerivedCategory.homologyFunctor _ 0).obj
      ((representedAffineDerivedSections B S hS U).obj (N⟦q⟧))) :=
    hN.of_iso ((DerivedCategory.homologyFunctor _ 0).mapIso
        (((representedAffineDerivedSections B S hS U).commShiftIso q).app N) ≪≫
      ((DerivedCategory.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).app _)
  have h0 : adj.homEquiv _ _ (i.hom ≫ g) = 0 :=
    (DerivedCategory.homologyFromSingleAddEquiv _ _ 0).map_eq_zero_iff.1 (hz.eq_of_tgt _ _)
  have h1 : i.hom ≫ g = 0 := by
    rw [← (adj.homEquiv _ _).symm_apply_apply (i.hom ≫ g), h0, Adjunction.homEquiv_counit,
      Functor.map_zero, Limits.zero_comp]
  simpa using congrArg (i.inv ≫ ·) h1

end Affine

/-- A perfect object of `D(R)` is bounded below. -/
theorem _root_.StacksDraft.Perfect.IsPerfect.exists_isGE {R : Type u} [Ring R]
    {K : DerivedCategory (ModuleCat.{u} R)} (hK : StacksDraft.Perfect.IsPerfect K) :
    ∃ a : ℤ, K.IsGE a := by
  obtain ⟨P, a, b, hPa, -, -, -, ⟨e⟩⟩ := hK
  exact ⟨a, DerivedCategory.TStructure.t.isGE_of_iso e.symm a⟩

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A finitely presented space over an affine scheme is quasi-compact and quasi-separated. -/
private theorem qcqs_of_isFinitePresentation_of_isAffine {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] {X : AlgebraicSpaces B S hS}
    {f : X ⟶ representedSpace T} (hfp : IsFinitePresentation B S hS f.hom) :
    IsQuasiCompactSpace B S hS X.1 ∧ IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1 :=
  have h := isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_yoneda_of_isAffine
    (B := B) (S := S) (hS := hS) (U := T)
  qcqs_of_isFinitePresentation B S hS B.contains_terminal X.2 (isAlgebraicSpace_yoneda B S hS _)
    h.1 h.2 hfp

/-- An object of `D(𝒪_X)` which is `≥ b` is locally bounded below. -/
private theorem isLocallyBoundedBelow_of_isGE {X : AlgebraicSpaces B S hS}
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) {b : ℤ} (hb : K.IsGE b) :
    IsLocallyBoundedBelow X K :=
  isLocallyBoundedBelow_of_isZero_homology X K b fun i hi =>
    DerivedCategory.isZero_of_isGE K b i hi

/-- **Derived pullbacks to affine base changes are bounded below.** Let `f : X ⟶ T` be flat and
of finite presentation with `T` affine, let `X' = X ×_T T'` for an affine `T'`, and let
`K ∈ D_QCoh(𝒪_X)` be such that `RΓ(T, Rf_*(E ⊗^𝐋 K))` is perfect for every perfect `E`. Then
the derived pullback of `K` to `X'` is locally bounded below. -/
theorem isLocallyBoundedBelow_smallEtaleDerivedModulePullback_of_isPerfect_derivedSections_tensor
    {T T' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ representedSpace T} {ι : Y ⟶ X}
    {f' : Y ⟶ representedSpace T'} {g : T' ⟶ T}
    (sq : IsPullback ι.hom f'.hom f.hom (yoneda.map g))
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hK : QcohDerived B S hS X K)
    (h : ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E →
        StacksDraft.Perfect.IsPerfect
          ((representedAffineDerivedSections B S hS T).obj
            ((derivedModulePushforward B S hS f).obj
              (((smallEtaleDerivedTensor B S hS X).obj E).obj K)))) :
    IsLocallyBoundedBelow Y ((smallEtaleDerivedModulePullback B S hS ι).obj K) := by
  have sqA : IsPullback ι f' f (representedSpaceMap B S hS g) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq
  have hgaff : IsAffineHom B S hS (representedSpaceMap B S hS g).hom :=
    isAffineHom_of_presheaf ((presheaf_yoneda_map_iff B S hS
      (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance g).mpr
      (_root_.AlgebraicGeometry.isAffineHom_of_isAffine _))
  have hιaff : IsAffineHom B S hS ι.hom := isAffineHom_of_isPullback' B S hS sq.flip hgaff
  have hιqc := isQuasiCompact_of_isAffineHom_hom ι hιaff
  have hιqs := isQuasiSeparated_of_isAffineHom_hom ι hιaff
  have hfp' : IsFinitePresentation B S hS f'.hom :=
    isFinitePresentation_of_isPullback B S hS Y.2 X.2 (isAlgebraicSpace_yoneda B S hS T')
      (isAlgebraicSpace_yoneda B S hS T) sq hfp
  obtain ⟨hqc, hqs⟩ := qcqs_of_isFinitePresentation_of_isAffine hfp
  obtain ⟨hYqc, hYqs⟩ := qcqs_of_isFinitePresentation_of_isAffine hfp'
  have adj := smallEtaleDerivedModuleAdjunction B S hS ι
  obtain ⟨G, hG, hgen⟩ := exists_isPerfect_generator X hqc hqs
  have hGY := isPerfect_smallEtaleDerivedModulePullback ι G hG
  have hgenY : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2,
      (∀ n : ℤ, Subsingleton (((smallEtaleDerivedModulePullback B S hS ι).obj G)⟦n⟧ ⟶ E.obj)) →
        IsZero E.obj := fun E hE =>
    isZero_of_isZero_derivedModulePushforward_of_isAffineHom B S hS ι hιaff E.obj E.property
      ((hgen ⟨(derivedModulePushforward B S hS ι).obj E.obj,
        qcohDerived_derivedModulePushforward_obj B S hS ι hιqc hιqs E.obj E.property⟩).2 fun n =>
          (adj.homEquiv _ _).subsingleton_congr.1
            (((((smallEtaleDerivedModulePullback B S hS ι).commShiftIso n).app G).homCongr
              (Iso.refl _)).subsingleton_congr.2 (hE n)))
  have hGd := isPerfect_smallEtaleDerivedDual B S hS X G hG
  have hGdq := derivedCategoryB_of_isPerfect B S hS X _ hGd
  set H := ((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X G)).obj K
  have hHq : QcohDerived B S hS X H := qcohDerived_smallEtaleDerivedTensor_obj B S hS X _ _ hGdq hK
  obtain ⟨a, ha⟩ := (StacksDraft.Perfect.isPerfect_derivedExtensionScalars
    (representedAffineCommRingCatHom B S hS g).hom _ (h _ hGd)).exists_isGE
  set KY := (smallEtaleDerivedModulePullback B S hS ι).obj K
  have hKYq : QcohDerived B S hS Y KY :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ ι K hK
  set N := (smallEtaleDerivedModulePullback B S hS ι).obj H
  have hNq : QcohDerived B S hS Y N :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ ι H hHq
  have hfN := qcohDerived_derivedModulePushforward_obj B S hS f' hfp'.2.1 hfp'.2.2 N hNq
  have := isIso_smallEtaleProjectionFormulaMap B S hS ι hιqc hιqs KY hKYq _ hGdq
  let e₁ : ((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X G)).obj
        ((derivedModulePushforward B S hS ι).obj KY) ≅
      (derivedModulePushforward B S hS ι).obj N :=
    (smallEtaleDerivedTensorProduct B S hS X).braiding _ _ ≪≫
      asIso (smallEtaleProjectionFormulaMap B S hS ι KY (smallEtaleDerivedDual B S hS X G)) ≪≫
      (derivedModulePushforward B S hS ι).mapIso
        (((smallEtaleDerivedPullbackTensorIso ι).app (K, smallEtaleDerivedDual B S hS X G)).symm ≪≫
          (smallEtaleDerivedModulePullback B S hS ι).mapIso
            ((smallEtaleDerivedTensorProduct B S hS X).braiding _ _))
  let e₂ : (derivedModulePushforward B S hS f).obj ((derivedModulePushforward B S hS ι).obj N) ≅
      (derivedModulePushforward B S hS (representedSpaceMap B S hS g)).obj
        ((derivedModulePushforward B S hS f').obj N) :=
    (smallEtaleDerivedPushforwardCompIsoToposHom B S hS ι f).app N ≪≫
      eqToIso (congrArg (fun φ => (derivedModulePushforward B S hS φ).obj N) sqA.w) ≪≫
      ((smallEtaleDerivedPushforwardCompIsoToposHom B S hS f'
        (representedSpaceMap B S hS g)).app N).symm
  obtain ⟨e₃⟩ := nonempty_representedAffineDerivedSections_representedSpaceMap_iso g
    (isQuasiCompact_of_isAffineHom_hom _ hgaff) (isQuasiSeparated_of_isAffineHom_hom _ hgaff) _ hfN
  have hbc := isIso_affineBaseDerivedSectionsBaseChangeMap B S hS g f f' ι sqA
    hfp.2.1 hfp.2.2 (torIndependent_of_isFlat_left f (representedSpaceMap B S hS g) hfl) H hHq
  have := Functor.isGE_obj_mapDerivedCategory
    (ModuleCat.restrictScalars.{u} ((B.inclusion.map g.left).app ⊤).hom) _ a ha
  have hbd : ((representedAffineDerivedSections B S hS T).obj
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X G)).obj
          ((derivedModulePushforward B S hS ι).obj KY)))).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso
      ((ModuleCat.restrictScalars.{u}
          ((B.inclusion.map g.left).app ⊤).hom).mapDerivedCategory.mapIso
        (@asIso _ _ _ _ (affineBaseDerivedSectionsBaseChangeMap B S hS g f f' ι sqA.w H) hbc) ≪≫
        e₃.symm ≪≫ ((representedAffineDerivedSections B S hS T).mapIso
          ((derivedModulePushforward B S hS f).mapIso e₁ ≪≫ e₂)).symm) a
  have hout := (tfae_isGE_of_isPerfect_generator Y hYqc hYqs _ hGY hgenY ⟨KY, hKYq⟩).out 3 1
  obtain ⟨b, hb⟩ := hout.1 ⟨a - 1, fun i hi =>
    (adj.homEquiv _ _).subsingleton_congr.2
      ((Iso.homCongr (Iso.refl G)
        (((derivedModulePushforward B S hS ι).commShiftIso i).app KY)).subsingleton_congr.2
        ((subsingleton_hom_shift_iff_isZero_homology_tensorDual X G hG _ i).2
          ((isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff_derivedModulePushforward f _
            i).2 fun φ => eq_zero_of_isZero_homology_representedAffineDerivedSections T _
              (DerivedCategory.isZero_of_isGE _ a i (by omega)) φ)))⟩
  exact isLocallyBoundedBelow_of_isGE KY hb

end BaseChange

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))

/-- **`K` is bounded below.** Let `X` be an algebraic space of finite presentation over a ring
`A` and `K ∈ D_QCoh(𝒪_X)` such that `RΓ(X, E ⊗^𝐋 K)` is perfect in `D(A)` for every perfect
`E`. Then `K` is locally bounded below. -/
theorem isLocallyBoundedBelow_of_isPerfect_derivedSections_tensor
    {X : AlgebraicSpaces B (Spec (CommRingCat.of A)) hA}
    (hfp : IsFinitePresentation B _ hA (toBase B _ hA X).hom)
    (K : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2)) (hK : QcohDerived B _ hA X K)
    (h : ∀ E : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2),
      (smallEtaleRingedSite B _ hA X.1 X.2).IsPerfect E →
        StacksDraft.Perfect.IsPerfect
          ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
            ((derivedModulePushforward B _ hA (toBase B _ hA X)).obj
              (((smallEtaleDerivedTensor B _ hA X).obj E).obj K)))) :
    IsLocallyBoundedBelow X K := by
  obtain ⟨hqc, hqs⟩ := qcqs_of_isFinitePresentation_of_isAffine (f := toBase B _ hA X) hfp
  obtain ⟨G, hG, hgen⟩ := exists_isPerfect_generator X hqc hqs
  obtain ⟨a, ha⟩ := (h _ (isPerfect_smallEtaleDerivedDual B _ hA X G hG)).exists_isGE
  have hout := (tfae_isGE_of_isPerfect_generator X hqc hqs G hG (fun E hE => (hgen E).2 hE)
    ⟨K, hK⟩).out 5 1
  obtain ⟨b, hb⟩ := hout.1 ⟨a - 1, fun i hi =>
      (isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff_derivedModulePushforward
        (toBase B _ hA X) _ i).2 fun g =>
          eq_zero_of_isZero_homology_representedAffineDerivedSections (baseSiteObj B _ hA) _
            (DerivedCategory.isZero_of_isGE _ a i (by lia)) g⟩
  exact isLocallyBoundedBelow_of_isGE K hb

attribute [local instance] AlgebraicGeometry.Space.sheafTensor_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.sheafTensor_obj_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_inverseImageRingedSite_over
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective

/-- **Stacks 0GFL.** Let `A` be a ring and `X` an algebraic space separated, of finite
presentation and flat over `A`. Let `K ∈ D_QCoh(𝒪_X)`. If `RΓ(X, E ⊗^𝐋 K)` is perfect in `D(A)`
for every perfect `E ∈ D(𝒪_X)`, then `K` is `Spec(A)`-perfect. -/
theorem isPerfectRelativeToCanonical_of_isPerfect_derivedSections_tensor
    {X : AlgebraicSpaces B (Spec (CommRingCat.of A)) hA}
    (hsep : IsSeparated B _ hA (toBase B _ hA X).hom)
    (hfp : IsFinitePresentation B _ hA (toBase B _ hA X).hom)
    (hfl : IsFlat B _ hA (toBase B _ hA X).hom)
    (K : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2)) (hK : QcohDerived B _ hA X K)
    (h : ∀ E : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2),
      (smallEtaleRingedSite B _ hA X.1 X.2).IsPerfect E →
        StacksDraft.Perfect.IsPerfect
          ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
            ((derivedModulePushforward B _ hA (toBase B _ hA X)).obj
              (((smallEtaleDerivedTensor B _ hA X).obj E).obj K)))) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B _ hA (toBase B _ hA X) hfl hfp.1 K := by
  have hpc := (isRelativelyPseudoCoherent_iff_isPseudoCoherent B _ hA (toBase B _ hA X) hfl hfp.1
    ⟨K, hK⟩).1 (isRelativelyPseudoCoherent_of_isPseudoCoherent_derivedSections_tensor_perfect B hA
      hsep hfp K hK fun E hE => StacksDraft.Perfect.isPseudoCoherent_of_isPerfect _ (h E hE))
  refine (isPerfectRelativeToCanonical_iff_isLocallyBoundedBelow (T := baseSiteObj B _ hA)
    (toBase B _ hA X) hfl hfp.1 K hpc).2
      ⟨isLocallyBoundedBelow_of_isPerfect_derivedSections_tensor B hA hfp K hK h, fun s => ?_⟩
  exact isLocallyBoundedBelow_smallEtaleDerivedModulePullback_of_isPerfect_derivedSections_tensor
    (T' := (residueFieldValuedPoint B _ hA (baseSiteObj B _ hA) s).siteObject B _ hA
      (yoneda.obj (baseSiteObj B _ hA)))
    (f' := ObjectProperty.homMk (pullback.snd _ _))
    (g := (residueFieldValuedPoint B _ hA (baseSiteObj B _ hA) s).value)
    (by
      rw [← yonedaEquiv_symm_residueFieldValuedPoint_value]
      exact IsPullback.of_hasPullback _ _)
    hfl hfp K hK h

/-- Let `A` be a ring and `X` an algebraic space separated, of finite presentation and flat over
`A`. Let `K ∈ D_QCoh(𝒪_X)`. If `RΓ(X, E ⊗^𝐋 K)` is perfect in `D(A)` for every perfect
`E ∈ D(𝒪_X)`, then `K` is `Spec(A)`-perfect.

Here `K` is an object of the full subcategory `D_QCoh(𝒪_X)` of `D(𝒪_X)` (Stacks 071X), and
`RΓ(X, -)` with values in `D(A)` is `RΓ(Spec A, Rf_*(-))` for the structure morphism
`f : X ⟶ Spec A`. -/
@[stacks 0GFL]
theorem QuasicoherentDerivedCategory.isPerfectRelativeToCanonical_of_isPerfect_derivedSections
    {X : AlgebraicSpaces B (Spec (CommRingCat.of A)) hA}
    (hsep : IsSeparated B _ hA (toBase B _ hA X).hom)
    (hfp : IsFinitePresentation B _ hA (toBase B _ hA X).hom)
    (hfl : IsFlat B _ hA (toBase B _ hA X).hom)
    (K : QuasicoherentDerivedCategory.{u, u} B _ hA X.1 X.2)
    (h : ∀ E : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2),
      (smallEtaleRingedSite B _ hA X.1 X.2).IsPerfect E →
        StacksDraft.Perfect.IsPerfect
          ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
            ((derivedModulePushforward B _ hA (toBase B _ hA X)).obj
              (((smallEtaleDerivedTensor B _ hA X).obj E).obj K.obj)))) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B _ hA (toBase B _ hA X) hfl hfp.1 K.obj :=
  isPerfectRelativeToCanonical_of_isPerfect_derivedSections_tensor B hA hsep hfp hfl K.obj
    K.property h

end AlgebraicGeometry.Space

end
