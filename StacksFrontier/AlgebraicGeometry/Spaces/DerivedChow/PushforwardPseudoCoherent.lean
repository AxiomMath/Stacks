module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FlatAndRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardTensorInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceTwistModule
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaSquare

/-!
# Pseudo-coherence of `Rq_*(Lp^*K ⊗^𝐋 E)` for a datum of the derived Chow lemma

Let `A` be a ring, `X` an algebraic space separated and of finite presentation over `A`, and
`K ∈ D_QCoh(𝒪_X)` such that `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent in `D(A)` for every
pseudo-coherent `E`. For a datum `(n, Z, V, E)` of Stacks 0CTR, with projections
`p : X ×_A ℙⁿ_A ⟶ X` and `q : X ×_A ℙⁿ_A ⟶ ℙⁿ_A`, the object `Rq_*(Lp^*K ⊗^𝐋 E)` of
`D(𝒪_{ℙⁿ_A})` is pseudo-coherent. This is the first half of the proof of Stacks 0CTT: by
Stacks 08IN, `RΓ(ℙⁿ_A, Rq_*(Lp^*K ⊗^𝐋 E) ⊗^𝐋 𝒪(d)) = RΓ(X, K ⊗^𝐋 Rp_*(E ⊗^𝐋 Lq^*𝒪(d)))`,
`Rp_*(E ⊗^𝐋 Lq^*𝒪(d))` is pseudo-coherent by Stacks 0CTN, and Stacks 0CSG (5) ⟹ (1) concludes.

## Main results

* `AlgebraicGeometry.Space.DerivedChow.isPullback_product`: `X ×_S ℙⁿ_S` is the fibre product.
* `AlgebraicGeometry.Space.DerivedChowDatum.isPseudoCoherent_derivedPushforward_productSnd`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open AlgebraicGeometry.Space.DerivedChow

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  SmallEtale.instHasSheafifyOver SmallEtale.instWEqualsLocallyBijectiveOver

namespace DerivedChow

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `X ×_S ℙⁿ_S` is the fibre product of `X ⟶ S` and `ℙⁿ_S ⟶ S`. -/
theorem isPullback_product (X : AlgebraicSpaces B S hS) (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) :
    IsPullback (productFst X n hP) (productSnd X n hP) (toBase B S hS X)
      (schemeSpaceMap (projectiveSpaceSiteObjToBase B S hS n hP)) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

variable (B S hS) in
/-- The structure morphism `ℙⁿ_S ⟶ S` is proper, flat and of finite presentation. -/
theorem isProper_isFlat_isFinitePresentation_projectiveSpace (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) :
    IsProper B S hS (schemeSpaceMap (projectiveSpaceSiteObjToBase B S hS n hP)).hom ∧
      IsFlat B S hS (schemeSpaceMap (projectiveSpaceSiteObjToBase B S hS n hP)).hom ∧
      IsFinitePresentation B S hS
        (schemeSpaceMap (projectiveSpaceSiteObjToBase B S hS n hP)).hom := by
  have e : (BigFppfOver.toScheme B S hS).map (projectiveSpaceSiteObjToBase B S hS n hP) =
      projectiveSpaceOver n S ↘ S := rfl
  have hpr : _root_.AlgebraicGeometry.IsProper (projectiveSpaceOver n S ↘ S) :=
    projectiveSpaceOver.isProper n S
  have hfl : Flat (projectiveSpaceOver n S ↘ S) := flat_projectiveSpaceOver n S
  have hsm : Smooth (projectiveSpaceOver n S ↘ S) := projectiveSpaceOver.smooth n S
  have hfp : FinitePresentation (projectiveSpaceOver n S ↘ S) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  refine ⟨isProper_yoneda_map B S hS _ (e ▸ hpr), isFlat_yoneda_map B S hS _ (e ▸ hfl),
    isFinitePresentation_yoneda_map B S hS _ (e ▸ hfp)⟩

/-- The projection `p : X ×_S ℙⁿ_S ⟶ X` is proper, flat and of finite presentation. -/
theorem isProper_isFlat_isFinitePresentation_productFst (X : AlgebraicSpaces B S hS) (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) :
    IsProper B S hS (productFst X n hP).hom ∧ IsFlat B S hS (productFst X n hP).hom ∧
      IsFinitePresentation B S hS (productFst X n hP).hom := by
  obtain ⟨hpr, hfl, hfp⟩ := isProper_isFlat_isFinitePresentation_projectiveSpace B S hS n hP
  have sq := isPullback_product X n hP
  have := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  refine ⟨(isProper_isStableUnderBaseChange B S hS).of_isPullback sq.flip hpr,
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq.flip hfl,
    MorphismProperty.of_isPullback (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
      IsLocallyOfFinitePresentation B S hS f.hom) sq.flip hfp.1,
    isQuasiCompact_of_isPullback_of_isFinitePresentation sq.flip hfp,
    isQuasiSeparated_of_isPullback_of_isFinitePresentation sq.flip hfp⟩

/-- The projection `q : X ×_S ℙⁿ_S ⟶ ℙⁿ_S` is quasi-compact and quasi-separated when `X` is of
finite presentation over `S`. -/
theorem isQuasiCompact_isQuasiSeparated_productSnd (X : AlgebraicSpaces B S hS) (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S))
    (hfp : IsFinitePresentation B S hS (toBase B S hS X).hom) :
    IsQuasiCompact B S hS (productSnd X n hP).hom ∧
      IsQuasiSeparated B S hS (productSnd X n hP).hom :=
  ⟨isQuasiCompact_of_isPullback_of_isFinitePresentation (isPullback_product X n hP) hfp,
    isQuasiSeparated_of_isPullback_of_isFinitePresentation (isPullback_product X n hP) hfp⟩

end DerivedChow

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))

/-- **`Rq_*(Lp^*K ⊗^𝐋 E)` is pseudo-coherent** for a datum `(n, Z, V, E)` of Stacks 0CTR on `X`
separated and of finite presentation over `A`, when `RΓ(X, E' ⊗^𝐋 K)` is pseudo-coherent in
`D(A)` for every pseudo-coherent `E'`. This is the first half of the proof of Stacks 0CTT. -/
theorem DerivedChowDatum.isPseudoCoherent_derivedPushforward_productSnd
    {X : AlgebraicSpaces B (Spec (CommRingCat.of A)) hA}
    (hfp : IsFinitePresentation B _ hA (toBase B _ hA X).hom)
    (K : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2)) (hK : QcohDerived B _ hA X K)
    (h : ∀ E : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2),
      (smallEtaleRingedSite B _ hA X.1 X.2).IsPseudoCoherent E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
            ((derivedModulePushforward B _ hA (toBase B _ hA X)).obj
              (((smallEtaleDerivedTensor B _ hA X).obj E).obj K))))
    {x : points B _ hA X.1} (D : DerivedChowDatum X x) :
    (smallEtaleRingedSite B _ hA (schemeSpace (projectiveSpaceSiteObj B _ hA D.n D.contains)).1
      (schemeSpace (projectiveSpaceSiteObj B _ hA D.n D.contains)).2).IsPseudoCoherent
      ((derivedModulePushforward B _ hA (productSnd X D.n D.contains)).obj
        (((smallEtaleDerivedTensor B _ hA (product B _ hA X D.n D.contains)).obj
          ((smallEtaleDerivedModulePullback B _ hA (productFst X D.n D.contains)).obj K)).obj
            D.E)) := by
  have sq := isPullback_product X D.n D.contains
  obtain ⟨hppr, hpfl, hpfp⟩ := isProper_isFlat_isFinitePresentation_productFst X D.n D.contains
  obtain ⟨hqqc, hqqs⟩ := isQuasiCompact_isQuasiSeparated_productSnd X D.n D.contains hfp
  have hEq := derivedCategoryB_of_isPseudoCoherent_unconditional B _ hA _ _ D.E
    D.isPseudoCoherent_E
  have hLK := derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
    (productFst X D.n D.contains) K hK
  have hM := qcohDerived_derivedModulePushforward_obj B _ hA (productSnd X D.n D.contains)
    hqqc hqqs _ (qcohDerived_smallEtaleDerivedTensor (product B _ hA X D.n D.contains) _ _ hLK hEq)
  refine isPseudoCoherent_of_isPseudoCoherent_twist_projectiveSpace B hA D.n D.contains
    _ hM fun d => ?_
  obtain ⟨et⟩ := nonempty_projectiveSpaceSiteTwist_iso B hA D.n D.contains d
  have hinv := isInvertibleModule_projectiveSpaceSiteTwistModule B hA D.n D.contains d
  have hLq := isQuasicoherentOnSite_of_isInvertibleModule _ _ hinv
  have htw : QcohDerived B _ hA _ (projectiveSpaceSiteTwist B hA D.n D.contains d) :=
    (QcohDerived B _ hA _).prop_of_iso et.symm
      (derivedCategoryB_singleFunctor_obj B _ hA _ _ _ hLq)
  obtain ⟨e⟩ := nonempty_derivedModulePushforward_projectionFormula_square_iso
    (productFst X D.n D.contains) (productSnd X D.n D.contains)
    (schemeSpaceMap (projectiveSpaceSiteObjToBase B _ hA D.n D.contains)) (toBase B _ hA X)
    sq.w.symm hpfp.2.1 hpfp.2.2 hqqc hqqs K hK D.E hEq _ htw
  have hE' := isPseudoCoherent_derivedModulePushforward_tensor_single_of_isInvertible
    (productFst X D.n D.contains) hpfl hppr hpfp (productSnd X D.n D.contains)
    (projectiveSpaceSiteTwistModule B hA D.n D.contains d) hinv
    (isFlat_projectiveSpaceSiteTwistModule B hA D.n D.contains d) D.E D.isPseudoCoherent_E
  have hE'' : (smallEtaleRingedSite B _ hA X.1 X.2).IsPseudoCoherent
      ((derivedModulePushforward B _ hA (productFst X D.n D.contains)).obj
        (((smallEtaleDerivedTensor B _ hA (product B _ hA X D.n D.contains)).obj D.E).obj
          ((smallEtaleDerivedModulePullback B _ hA (productSnd X D.n D.contains)).obj
            (projectiveSpaceSiteTwist B hA D.n D.contains d)))) :=
    (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m =>
      RingedSite.isPseudoCoherentFrom_of_iso _ m
        ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 hE' m)
        ((derivedModulePushforward B _ hA (productFst X D.n D.contains)).mapIso
          (((smallEtaleDerivedTensor B _ hA (product B _ hA X D.n D.contains)).obj D.E).mapIso
            ((smallEtaleDerivedModulePullback B _ hA (productSnd X D.n D.contains)).mapIso et)))
  exact (h _ hE'').ofIso
    ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).mapIso e.symm)

end AlgebraicGeometry.Space

end
