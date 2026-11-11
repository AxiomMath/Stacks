module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectPushforwardNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatNoetherianProductModel
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceTwistPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceQuotientFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceStructureQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealAffineChartFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset

/-!
# The derived direct image of a perfect object with support proper over the base

Let `f : X ⟶ Y` be a flat morphism of finite presentation of algebraic spaces with `Y` affine,
let `ℱ` be an `𝒪_X`-module of finite presentation whose support is proper over `Y`, and let `P`
be a perfect object of `D(𝒪_X)` whose cohomology sheaves are supported in the support of `ℱ`.
Then `Rf_*P` is pseudo-coherent.

The proof is by Noetherian approximation. `Y` is the spectrum of a ring `A` of the site; viewing
`X` over `Spec A`, the pair `(X, ℱ)` is the base change of a pair `(X₀, ℱ₀)` over an affine
Noetherian `Y₀` with `X₀` flat and of finite presentation over `Y₀`
(`AlgebraicGeometry.Space.exists_flatNoetherianProductModel`), and the support of `P` lies in
the inverse image of the support of `ℱ₀`, a closed subset of `|X₀|` proper over `Y₀`. That case
is `AlgebraicGeometry.Space.isPseudoCoherent_derivedModulePushforward_of_noetherianModel`.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherent_relocalizeDerivedFunctor_obj`: the relocalization of
  derived categories preserves pseudo-coherence.
* `AlgebraicGeometry.Space.cohomologySupportedOn_relocalizeDerivedFunctor_obj`: and supports.
* `AlgebraicGeometry.Space.isPseudoCoherent_derivedModulePushforward_of_isAffineSpace`: the
  statement above.
* `AlgebraicGeometry.Space.isPseudoCoherent_derivedModulePushforward_of_isProper_closedSubspace`:
  the case of a perfect object supported on a closed subspace `W ⊆ X` of finite presentation
  which is proper over `Y`, through the module `𝒪_W = 𝒪_X / 𝓘_W`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

section Relocalize

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) (X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B T hT X)

/-- **The relocalization of derived categories preserves pseudo-coherence.** -/
theorem isPseudoCoherent_relocalizeDerivedFunctor_obj
    [HasDerivedCategory (Modules.{u, u} B T hT X hX)]
    [HasDerivedCategory (Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX))]
    (K : DerivedCategory (Modules.{u, u} B T hT X hX))
    (hK : (smallEtaleRingedSite B T hT X hX).IsPseudoCoherent K) :
    (smallEtaleRingedSite B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX)).IsPseudoCoherent
      ((relocalizeDerivedFunctor B hT hS g X hX).obj K) :=
  (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m =>
    RingedSite.isPseudoCoherentFrom_mapDerivedCategory_pushforwardEquivalenceOfIsIso
      (X := smallEtaleRingedSite B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX))
      (Y := smallEtaleRingedSite B T hT X hX)
      (SmallEtale.relocalize B hT hS g X hX).symm
      (hfun := inferInstanceAs ((SmallEtale.relocalize B hT hS g X hX).inverse.IsContinuous
        (SmallEtale.topology B S hS _) (SmallEtale.topology B T hT X)))
      (hinv := inferInstanceAs ((SmallEtale.relocalize B hT hS g X hX).functor.IsContinuous
        (SmallEtale.topology B T hT X) (SmallEtale.topology B S hS _)))
      (Stacks.SheafOfModules.reindexBackSharp (J' := SmallEtale.topology B T hT X)
        (SmallEtale.relocalize B hT hS g X hX) (relocalizeRingSheaf B hT hS g X hX))
      (hρ := isIso_reindexBackSharp_relocalize B hT hS g X hX) K m
      ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 hK m)

/-- The support of the `𝒪_{Λ X}`-module attached to an `𝒪_X`-module `F` is the image of the
support of `F`. -/
theorem supportOfSheaf_relocalizeModulesEquivalence_functor_obj (F : Modules.{u, u} B T hT X hX) :
    supportOfSheaf B S hS _ ((SheafOfModules.toSheaf _).obj
        ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj F)) =
      pointsRelocalize B T S hT hS g X ''
        supportOfSheaf B T hT X ((SheafOfModules.toSheaf _).obj F) := by
  rw [supportOfSheaf_relocalize_eq_image B hT hS g hX,
    ← toSheaf_relocalizeModulesEquivalence_inverse_obj]
  congr 1
  exact supportOfSheaf_eq_of_isoSheaf B T hT X hX ((SheafOfModules.toSheaf _).mapIso
    ((relocalizeModulesEquivalence B hT hS g X hX).unitIso.app F).symm)

end Relocalize

attribute [local instance] HasDerivedCategory.standard

section RelocalizeSupport

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) (X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B T hT X)

/-- **The relocalization of derived categories and supports.** If `K ∈ D(𝒪_X)` is supported on
`Z ⊆ |X|`, then its image in `D(𝒪_{Λ X})` is supported on the image of `Z` in `|Λ X|`. -/
theorem cohomologySupportedOn_relocalizeDerivedFunctor_obj (Z : Set (points B T hT X))
    (K : DerivedCategory (Modules.{u, u} B T hT X hX))
    (hK : CohomologySupportedOn B T hT X hX Z K) :
    CohomologySupportedOn B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX)
      (pointsRelocalize B T S hT hS g X '' Z)
      ((relocalizeDerivedFunctor B hT hS g X hX).obj K) := by
  intro i
  refine (supportOfSheaf_eq_of_iso B S hS ⟨_, isAlgebraicSpace_relocalize' B hT hS g X hX⟩
    (((relocalizeModulesEquivalence B hT hS g X hX).functor.mapDerivedCategoryHomologyFunctorIso
      i).app K)).trans_subset ?_
  exact (le_of_eq (supportOfSheaf_relocalizeModulesEquivalence_functor_obj B hT hS g X hX _)).trans
    (Set.image_mono (hK i))

end RelocalizeSupport

section SpecBase

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}

/-- **The direct image of a perfect object with support in a module of proper support, over the
spectrum of a ring.** Let `f : X ⟶ Spec A` be flat and of finite presentation, `ℱ` an
`𝒪_X`-module of finite presentation with support proper over `Spec A`, and `P` a perfect object
of `D(𝒪_X)` supported on the support of `ℱ`. Then `Rf_*P` is pseudo-coherent. -/
theorem isPseudoCoherent_derivedModulePushforward_of_specBase
    {X : AlgebraicSpaces B (Spec (.of A)) hA} (f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA))))
    (hf : IsFinitePresentation B (Spec (.of A)) hA f.hom)
    (hfl : IsFlat B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hF : F.IsFinitePresentation)
    (hsupp : HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (Over.mk (𝟙 (B.obj hA)))).2
      f.hom (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ hA hf.1)
      ((SheafOfModules.toSheaf _).obj F))
    (P : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X.1 X.2))
    (hP : (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).IsPerfect P)
    (hPs : CohomologySupportedOn B (Spec (.of A)) hA X.1 X.2
      (supportOfSheaf B (Spec (.of A)) hA X.1 ((SheafOfModules.toSheaf _).obj F)) P) :
    (smallEtaleRingedSite B (Spec (.of A)) hA (schemeSpace (Over.mk (𝟙 (B.obj hA)))).1
        (schemeSpace (Over.mk (𝟙 (B.obj hA)))).2).IsPseudoCoherent
      ((derivedModulePushforward B (Spec (.of A)) hA f).obj P) := by
  obtain ⟨A₀, _, _, _, hA₀, g, hg, Y₀, y, X₀, f₀, hf₀, F₀, a, hY₀a, hY₀N, hfl₀, hF₀fp, hF₀q, -,
    hF₀supp, hpb, ⟨eF⟩⟩ := exists_flatNoetherianProductModel B X.2 f.hom hf hfl F hF hsupp
  let bh := relocalizeBaseHom B hA hA₀ g
  let y₁ := bh ≫ schemeSpaceMap y
  have hst : relocalizeHom B hA hA₀ g f ≫ bh =
      ObjectProperty.homMk (OverShriek.viewStructureMap g X.1) :=
    ObjectProperty.hom_ext _ (relocalizeHom_comp_relocalizeBaseHom B hA hA₀ g X.2 f)
  have hsq₀ : IsPullback (𝟙 _) (relocalizeHom B hA hA₀ g f)
      (ObjectProperty.homMk (OverShriek.viewStructureMap g X.1)) bh :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hst]⟩
  have sq₁ : IsPullback a (relocalizeHom B hA hA₀ g f) f₀ y₁ := by
    simpa only [Category.id_comp] using hsq₀.paste_horiz hpb
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A₀)) hA₀).obj (Over.mk g)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  have hY₁ : IsAffineSpace B (Spec (.of A₀)) hA₀
      (relocalizeSpace B hA hA₀ g (schemeSpace (Over.mk (𝟙 (B.obj hA))))).1 :=
    (isAffineSpace_yoneda B _ hA₀ (Over.mk g) inferInstance).of_iso
      ((ObjectProperty.ι _).mapIso (asIso bh).symm)
  have hY₀ : IsAffineSpace B (Spec (.of A₀)) hA₀ (schemeSpace Y₀).1 :=
    isAffineSpace_yoneda B _ hA₀ Y₀ hY₀a
  obtain ⟨hcl₀, hp₀⟩ := hF₀supp
  have hF₀ft := isFiniteTypeOnSite_of_isFinitePresentation F₀ hF₀fp
  -- the relocalization of `P` is supported on the inverse image of the support of `F₀`
  have hρP : CohomologySupportedOn B _ hA₀ _ (relocalizeSpace B hA hA₀ g X).2
      (pointsMap B _ hA₀ (relocalizeSpace B hA hA₀ g X).1 a.hom ⁻¹'
        supportOfSheaf B _ hA₀ X₀.1 ((SheafOfModules.toSheaf _).obj F₀))
      ((relocalizeDerivedFunctor B hA hA₀ g X.1 X.2).obj P) := by
    intro i
    refine ((cohomologySupportedOn_relocalizeDerivedFunctor_obj B hA hA₀ g X.1 X.2 _ P hPs) i).trans
      (le_of_eq ?_)
    rw [← supportOfSheaf_relocalizeModulesEquivalence_functor_obj,
      supportOfSheaf_eq_of_iso B _ hA₀ (relocalizeSpace B hA hA₀ g X) eF,
      supportOfSheaf_modulePullback_eq B _ hA₀ a F₀ hF₀q hF₀ft]
  have hpc := isPseudoCoherent_derivedModulePushforward_of_noetherianModel hY₀N hY₀ hY₁ f₀ hf₀
    hfl₀ _ hcl₀ hp₀ y₁ (relocalizeHom B hA hA₀ g f) a sq₁ _
    (isPerfect_relocalizeDerivedFunctor_obj B hA hA₀ g X.1 X.2 P hP) hρP
  -- back to `Spec A`
  have h₁ := (smallEtaleRingedSite B _ hA₀ _ _).isPseudoCoherentObject.prop_of_iso
    (relocalizeDerivedPushforwardObjIso B hA hA₀ g f P).symm hpc
  exact (smallEtaleRingedSite B _ hA _ _).isPseudoCoherentObject.prop_of_iso
    ((relocalizeInverseEquivalence B hA hA₀ g _ _).unitIso.app _).symm
    (isPseudoCoherent_relocalizeInverse_obj B hA hA₀ g _ _ _ h₁)

end SpecBase

section SchemeBase

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A : Type u} [CommRing A]
  {hA : B.Contains (Spec (.of A))}

/-- **The direct image of a perfect object with support in a module of proper support, over the
spectrum of a ring of the site.** Let `f : X ⟶ h_{(Spec A, g)}` be flat and of finite
presentation, `ℱ` an `𝒪_X`-module of finite presentation with support proper over
`h_{(Spec A, g)}`, and `P` a perfect object of `D(𝒪_X)` supported on the support of `ℱ`. Then
`Rf_*P` is pseudo-coherent. -/
theorem isPseudoCoherent_derivedModulePushforward_of_schemeBase (g : B.obj hA ⟶ B.obj hS)
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace (Over.mk g))
    (hf : IsFinitePresentation B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsFinitePresentation)
    (hsupp : HasProperSupport B S hS X.2 (schemeSpace (Over.mk g)).2 f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj F))
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
    (hPs : CohomologySupportedOn B S hS X.1 X.2
      (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) P) :
    (smallEtaleRingedSite B S hS (schemeSpace (Over.mk g)).1
        (schemeSpace (Over.mk g)).2).IsPseudoCoherent
      ((derivedModulePushforward B S hS f).obj P) := by
  obtain ⟨XT, e, he⟩ := exists_relocalizeSpace_iso B hA hS g X f
  have hft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1
  have hfT := (isFinitePresentation_iff_of_relocalizeSpace_iso e he).1 hf
  have hflT := (isFlat_iff_of_relocalizeSpace_iso e he).1 hfl
  have hftT := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ hA hfT.1
  let fT := toFinalHom B hA XT
  let bh := relocalizeBaseHom B hA hS g
  have : IsIso bh.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map bh))
  have sq : IsPullback e.hom (relocalizeHom B hA hS g fT) f bh :=
    IsPullback.of_horiz_isIso ⟨he⟩
  let E := relocalizeModulesEquivalence B hA hS g XT.1 XT.2
  -- the module on `X_T`
  let F' := (modulePullback B S hS e.hom).obj F
  have hFq := isQuasicoherentOnSite_of_isFinitePresentation F hF
  have hFft := isFiniteTypeOnSite_of_isFinitePresentation F hF
  have hF'fp : F'.IsFinitePresentation := isFinitePresentation_modulePullback e.hom F hF
  let FT := E.inverse.obj F'
  have hFTfp : FT.IsFinitePresentation :=
    isFinitePresentation_relocalizeModulesEquivalence_inverse B hA hS g XT.1 XT.2 _ hF'fp
  have hlftrel : IsLocallyOfFiniteType B S hS (relocalizeHom B hA hS g fT).hom :=
    (isLocallyOfFiniteType_relocalize_iff B _ hA S hS g fT.hom).2 hftT
  have hF'supp : HasProperSupport B S hS (relocalizeSpace B hA hS g XT).2
      (relocalizeSpace B hA hS g (schemeSpace (Over.mk (𝟙 (B.obj hA))))).2
      (relocalizeHom B hA hS g fT).hom hlftrel ((SheafOfModules.toSheaf _).obj F') :=
    ⟨isClosed_supportOfSheaf_modulePullback B S hS e.hom F hFft,
      isProperOver_supportOfSheaf_modulePullback B S hS sq hft F hFq hFft hsupp.2⟩
  have hFTsupp : HasProperSupport B _ hA XT.2 (schemeSpace (Over.mk (𝟙 (B.obj hA)))).2 fT.hom
      hftT ((SheafOfModules.toSheaf _).obj FT) :=
    (hasProperSupport_relocalizeModulesEquivalence_inverse_iff B hA hS g XT.2
      (schemeSpace (Over.mk (𝟙 (B.obj hA)))).2 fT.hom hftT F').2 hF'supp
  -- the perfect object on `X_T`
  let PT := (relocalizeInverse B hA hS g XT.1 XT.2).obj
    ((smallEtaleDerivedModulePullback B S hS e.hom).obj P)
  have hPT : (smallEtaleRingedSite B _ hA XT.1 XT.2).IsPerfect PT :=
    isPerfect_relocalizeModulesEquivalence_inverse_mapDerivedCategory_obj B hA hS g XT.1 XT.2 _
      (isPerfect_smallEtaleDerivedModulePullback e.hom P hP)
  have hPTs : CohomologySupportedOn B _ hA XT.1 XT.2
      (supportOfSheaf B _ hA XT.1 ((SheafOfModules.toSheaf _).obj FT)) PT := by
    have h₀ := cohomologySupportedOn_smallEtaleDerivedModulePullback e.hom P hPs
    rw [← supportOfSheaf_modulePullback_eq B S hS e.hom F hFq hFft] at h₀
    have h₁ := cohomologySupportedOn_relocalizeInverse_obj B hA hS g XT.1 XT.2 _ _ h₀
    rwa [← supportOfSheaf_relocalize B hA hS g XT.2] at h₁
  have hT := isPseudoCoherent_derivedModulePushforward_of_specBase fT hfT hflT FT hFTfp hFTsupp
    PT hPT hPTs
  -- back to `S`
  have hρ := isPseudoCoherent_relocalizeDerivedFunctor_obj B hA hS g _ _ _ hT
  have h₁ := (smallEtaleRingedSite B S hS _ _).isPseudoCoherentObject.prop_of_iso
    (relocalizeDerivedPushforwardObjIso B hA hS g fT PT ≪≫
      (derivedModulePushforward B S hS (relocalizeHom B hA hS g fT)).mapIso
        ((relocalizeInverseEquivalence B hA hS g XT.1 XT.2).counitIso.app _)) hρ
  have hiso := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f bh
    (relocalizeHom B hA hS g fT) e.hom sq (isEtale_of_isIso B S hS bh.hom)
    (Functor.relativelyRepresentable.of_isIso yoneda bh.hom) P
  exact isPseudoCoherent_of_smallEtaleDerivedModulePullback_iso (asIso bh) _
    ((smallEtaleRingedSite B S hS _ _).isPseudoCoherentObject.prop_of_iso
      (@asIso _ _ _ _ _ hiso).symm h₁)

end SchemeBase

section Main

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The derived direct image of a perfect object supported in a module of proper support is
pseudo-coherent.** Let `f : X ⟶ Y` be a flat morphism of finite presentation of algebraic spaces
with `Y` affine, let `ℱ` be an `𝒪_X`-module of finite presentation with support proper over `Y`,
and let `P` be a perfect object of `D(𝒪_X)` whose cohomology sheaves are supported in the
support of `ℱ`. Then `Rf_*P` is pseudo-coherent. -/
theorem isPseudoCoherent_derivedModulePushforward_of_isAffineSpace {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsFinitePresentation)
    (hsupp : HasProperSupport B S hS X.2 Y.2 f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj F))
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
    (hPs : CohomologySupportedOn B S hS X.1 X.2
      (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) P) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent
      ((derivedModulePushforward B S hS f).obj P) := by
  obtain ⟨V, hV, ⟨i⟩⟩ := hY
  let W := (BigFppfOver.toScheme B S hS).obj V
  have hA : B.Contains (Spec (.of Γ(W, ⊤))) :=
    lt_of_eq_of_lt (Scheme.size_congr W.isoSpec).symm V.left.property
  let g : B.obj hA ⟶ B.obj hS := (ObjectProperty.isoMk _ W.isoSpec.symm).hom ≫ V.hom
  -- `Y ≅ h_{(Spec Γ(V), g)}`
  let j : schemeSpace (Over.mk g) ≅ Y :=
    (schemeSpaceFunctor B S hS).mapIso (Over.isoMk (ObjectProperty.isoMk _ W.isoSpec.symm) rfl) ≪≫
      (ObjectProperty.isoMk _ i).symm
  have sq : IsPullback (𝟙 X) (f ≫ j.inv) f j.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hf' : IsFinitePresentation B S hS (f ≫ j.inv).hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hf
  have := isFlat_isStableUnderBaseChange B S hS
  have hfl' : IsFlat B S hS (f ≫ j.inv).hom :=
    MorphismProperty.of_isPullback (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (φ : F ⟶ G) =>
      IsFlat B S hS φ.hom) sq hfl
  have hft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1
  have hFq := isQuasicoherentOnSite_of_isFinitePresentation F hF
  have hFft := isFiniteTypeOnSite_of_isFinitePresentation F hF
  let F' := (modulePullback B S hS (𝟙 X)).obj F
  have hsuppF' : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F') =
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
    rw [supportOfSheaf_modulePullback_eq B S hS (𝟙 X) F hFq hFft]
    change pointsMap B S hS X.1 (𝟙 X.1) ⁻¹' _ = _
    rw [pointsMap_id, Set.preimage_id]
  have hsupp' : HasProperSupport B S hS X.2 (schemeSpace (Over.mk g)).2 (f ≫ j.inv).hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf'.1)
      ((SheafOfModules.toSheaf _).obj F') :=
    ⟨isClosed_supportOfSheaf_modulePullback B S hS (𝟙 X) F hFft,
      isProperOver_supportOfSheaf_modulePullback B S hS sq hft F hFq hFft hsupp.2⟩
  have h := isPseudoCoherent_derivedModulePushforward_of_schemeBase g (f ≫ j.inv) hf' hfl' F'
    (isFinitePresentation_modulePullback (𝟙 X) F hF) hsupp' P hP (hsuppF' ▸ hPs)
  have hiso := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f j.hom (f ≫ j.inv) (𝟙 X)
    sq (isEtale_of_isIso B S hS j.hom.hom)
    (Functor.relativelyRepresentable.of_isIso yoneda j.hom.hom) P
  refine isPseudoCoherent_of_smallEtaleDerivedModulePullback_iso j _
    ((smallEtaleRingedSite B S hS _ _).isPseudoCoherentObject.prop_of_iso
      (@asIso _ _ _ _ _ hiso).symm ?_)
  exact (smallEtaleRingedSite B S hS _ _).isPseudoCoherentObject.prop_of_iso
    ((derivedModulePushforward B S hS (f ≫ j.inv)).mapIso
      ((smallEtaleDerivedModulePullbackIdentityIso B S hS X).app P).symm) h

/-- **The derived direct image of a perfect object supported on a closed subspace proper over the
base is pseudo-coherent.** Let `f : X ⟶ Y` be a flat morphism of finite presentation of algebraic
spaces with `Y` affine, let `W ⊆ X` be a closed subspace of finite presentation over `X` such
that `W ⟶ Y` is proper, and let `P` be a perfect object of `D(𝒪_X)` supported on `|W|`. Then
`Rf_*P` is pseudo-coherent. -/
theorem isPseudoCoherent_derivedModulePushforward_of_isProper_closedSubspace
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hY : IsAffineSpace B S hS Y.1)
    (W : ClosedSubspaces B S hS X.1) (hW : IsFinitePresentation B S hS W.1.ι)
    (hWp : IsProper B S hS (W.1.ι ≫ f.hom))
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
    (hPs : CohomologySupportedOn B S hS X.1 X.2
      (Set.range (pointsMap B S hS W.1.toFunctor W.1.ι)) P) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent
      ((derivedModulePushforward B S hS f).obj P) := by
  have hft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1
  -- the module `𝒪_W = 𝒪_X / 𝓘_W`
  let F : Modules.{u, u} B S hS X.1 X.2 := cokernel (definingIdealSheaf B S hS X W).ι
  have hI : SheafOfModules.IsFiniteTypeOnSite (definingIdealSheaf B S hS X W).toSheafOfModules :=
    kernelIdealSheaf_eq_definingIdealSheaf B S hS X W ▸
      isFiniteTypeOnSite_kernelIdealSheaf_of_isFinitePresentation B S hS
        (subspaceInclusion B S hS X W) W.2.2 hW
  have hF : F.IsFinitePresentation :=
    SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' F
      (isFinitePresentationOnSite_cokernel_definingIdealSheaf B S hS X W hI)
  have hsuppF := supportOfSheaf_cokernel_definingIdealSheaf B S hS X W
  have hcl := isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 W.1.ι W.2.2
  have hsupp : HasProperSupport B S hS X.2 Y.2 f.hom hft ((SheafOfModules.toSheaf _).obj F) :=
    (congrArg (fun T => ∃ hT : IsClosed T, IsProperOver B S hS X.2 Y.2 f.hom hft T hT)
      hsuppF).mpr ⟨hcl, (isProper_reducedClosedSubspace_iff_exists B S hS X.2 Y.2 f.hom hft _
        hcl).2 ⟨W.1, W.2, rfl, hWp⟩⟩
  exact isPseudoCoherent_derivedModulePushforward_of_isAffineSpace f hf hfl hY F hF hsupp P hP
    (hsuppF ▸ hPs)

end Main

end AlgebraicGeometry.Space

end
