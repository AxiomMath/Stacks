module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffinePushforwardPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforward
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero

/-!
# Finite Tor dimension of the derived direct image along a perfect morphism

Let `f : X ⟶ yoneda.obj U` be a perfect morphism (Stacks 06BZ) from a quasi-compact and
quasi-separated algebraic space to the algebraic space represented by an object `U` of the big fppf
site with affine underlying scheme, and let `E` be a perfect object of `D(𝒪_X)`.  Then the derived
sections `RΓ(U, Rf_*E)` have finite Tor dimension over `Γ(U)`.  This is the Tor-dimension half of
the proof of Stacks 08EV, which Stacks 0E4U applies.

The source proves it by the projection formula.  Here it is proved by the induction principle of
Stacks 08GP: for an affine source it is
`Space.exists_hasTorAmplitudeCanonical_representedAffineDerivedSections_derivedPushforward`,
transported along an isomorphism with a representable; and the property passes across an
elementary distinguished square by the relative Mayer–Vietoris triangle of Stacks 08JK read
through `RΓ(U, -)`, and Stacks 0655.

## Main definitions

* `AlgebraicGeometry.Space.PreservesFiniteTorDimensionSections`: the direct image along `g` carries
  K-injective complexes representing perfect objects to complexes whose derived sections over `U`
  have finite Tor dimension.
* `AlgebraicGeometry.Space.modulePushforwardIsoEtaleModulePullbackOfIso`: along an isomorphism the
  direct image is the étale pullback along the inverse.

## Main results

* `StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_obj₁`,
  `StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_obj₂`,
  `StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_biprod`: finite Tor dimension in
  distinguished triangles (Stacks 0655).
* `AlgebraicGeometry.Space.isPerfect_comp_of_isEtale`: a perfect morphism precomposed with an
  étale morphism is perfect.
* `AlgebraicGeometry.Space.preservesFiniteTorDimensionSections_of_isPerfect`: the statement above.

## References

* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08JK](https://stacks.math.columbia.edu/tag/08JK)
* [Stacks Project, Tag 0655](https://stacks.math.columbia.edu/tag/0655)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated
open CategoryTheory.PushforwardMayerVietoris

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

/-! ### Finite Tor dimension in distinguished triangles -/

namespace StacksDraft.TorAmplitude

variable {R : Type u} [CommRing R]

attribute [local instance 10000] HasDerivedCategory.standard

/-- Finite Tor dimension only depends on the isomorphism class in `D(R)`. -/
theorem hasFiniteTorDimensionCanonical_of_iso {K L : DerivedCategory (ModuleCat.{u} R)}
    (e : K ≅ L) (h : HasFiniteTorDimensionCanonical R K) : HasFiniteTorDimensionCanonical R L := by
  obtain ⟨a, b, hab⟩ := (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical R K).1 h
  exact (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical R L).2
    ⟨a, b, AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b hab⟩

/-- Tor amplitude in an interval gives Tor amplitude in every larger interval. -/
theorem hasTorAmplitudeCanonical_mono' {K : DerivedCategory (ModuleCat.{u} R)} {a b a' b' : ℤ}
    (h : HasTorAmplitudeCanonical R K a b) (ha : a' ≤ a) (hb : b ≤ b') :
    HasTorAmplitudeCanonical R K a' b' :=
  (hasTorAmplitudeIn_canonical_iff R K a' b').1 fun M i hi =>
    (hasTorAmplitudeIn_canonical_iff R K a b).2 h M i (by omega)

/-- Two objects of finite Tor dimension have Tor amplitude in a common interval. -/
private theorem exists_hasTorAmplitudeCanonical_pair {K L : DerivedCategory (ModuleCat.{u} R)}
    (hK : HasFiniteTorDimensionCanonical R K) (hL : HasFiniteTorDimensionCanonical R L) :
    ∃ a b : ℤ, HasTorAmplitudeCanonical R K a b ∧ HasTorAmplitudeCanonical R L a b := by
  obtain ⟨a₁, b₁, h₁⟩ :=
    (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical R _).1 hK
  obtain ⟨a₂, b₂, h₂⟩ :=
    (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical R _).1 hL
  exact ⟨min a₁ a₂, max b₁ b₂, hasTorAmplitudeCanonical_mono' h₁ (by omega) (by omega),
    hasTorAmplitudeCanonical_mono' h₂ (by omega) (by omega)⟩

/-- **The first vertex of a distinguished triangle has finite Tor dimension when the other two
have** (Stacks 0655 (3)). -/
theorem hasFiniteTorDimensionCanonical_obj₁ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₂ : HasFiniteTorDimensionCanonical R T.obj₂)
    (h₃ : HasFiniteTorDimensionCanonical R T.obj₃) : HasFiniteTorDimensionCanonical R T.obj₁ := by
  obtain ⟨a, b, h₂, h₃⟩ := exists_hasTorAmplitudeCanonical_pair h₂ h₃
  exact (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical R _).2
    ⟨a - 1 + 1, b + 1, (hasTorAmplitudeIn_canonical_iff R _ _ _).1
    (Stacks.TorAmplitudeTriangle.hasTorAmplitudeIn_obj₁_of_obj₂_obj₃ _ T hT (a - 1) b
      ((hasTorAmplitudeIn_canonical_iff R _ _ _).2
        (hasTorAmplitudeCanonical_mono' h₂ (by omega) (by omega)))
      ((hasTorAmplitudeIn_canonical_iff R _ _ _).2
        (hasTorAmplitudeCanonical_mono' h₃ (by omega) (by omega))))⟩

/-- **The middle vertex of a distinguished triangle has finite Tor dimension when the other two
have** (Stacks 0655 (2)). -/
theorem hasFiniteTorDimensionCanonical_obj₂ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₁ : HasFiniteTorDimensionCanonical R T.obj₁)
    (h₃ : HasFiniteTorDimensionCanonical R T.obj₃) : HasFiniteTorDimensionCanonical R T.obj₂ := by
  obtain ⟨a, b, h₁, h₃⟩ := exists_hasTorAmplitudeCanonical_pair h₁ h₃
  exact (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical R _).2
    ⟨_, _, (hasTorAmplitudeIn_canonical_iff R _ _ _).1
    (Stacks.TorAmplitudeTriangle.hasTorAmplitudeIn_obj₂_of_obj₁_obj₃ _ T hT _ _
      ((hasTorAmplitudeIn_canonical_iff R _ _ _).2 h₁)
      ((hasTorAmplitudeIn_canonical_iff R _ _ _).2 h₃))⟩

/-- **A direct sum of two objects of finite Tor dimension has finite Tor dimension**
(Stacks 0655 (2) on the split triangle). -/
theorem hasFiniteTorDimensionCanonical_biprod {X Y : DerivedCategory (ModuleCat.{u} R)}
    [HasBinaryBiproduct X Y] (hX : HasFiniteTorDimensionCanonical R X)
    (hY : HasFiniteTorDimensionCanonical R Y) :
    HasFiniteTorDimensionCanonical R (X ⊞ Y) :=
  hasFiniteTorDimensionCanonical_obj₂ _ (binaryBiproductTriangle_distinguished X Y) hX hY

end StacksDraft.TorAmplitude

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- The direct image along `g` carries every K-injective complex representing a perfect object to
a complex whose derived sections over the affine `U` have finite Tor dimension over `Γ(U)`. -/
def PreservesFiniteTorDimensionSections {W : AlgebraicSpaces B S hS}
    (g : W ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) : Prop :=
  letI := additive_modulePushforward B S hS g
  ∀ I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ, I.IsKInjective →
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect (DerivedCategory.Q.obj I) →
    StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      ((representedAffineDerivedSections B S hS U).obj (DerivedCategory.Q.obj
        (((modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))

/-! ### The Mayer–Vietoris step -/

section MayerVietoris

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

include hsq in
/-- **The Mayer–Vietoris step.**  Let `(U₀ ⊆ W, V → W)` be an elementary distinguished square and
`g : W ⟶ yoneda.obj U` a morphism.  If the direct images along `U₀ ⟶ yoneda.obj U`,
`V ⟶ yoneda.obj U` and `U₀ ×_W V ⟶ yoneda.obj U` preserve finite Tor dimension of the derived
sections of perfect objects, so does the direct image along `g`: the relative Mayer–Vietoris
triangle of Stacks 08JK, read through `RΓ(U, -)`, and Stacks 0655. -/
theorem preservesFiniteTorDimensionSections_of_isElementaryDistinguishedSquare
    (g : W ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
    (hU : PreservesFiniteTorDimensionSections B S hS U (edsOpenHom B S hS hsq ≫ g))
    (hV : PreservesFiniteTorDimensionSections B S hS U (edsEtaleHom B S hS hsq ≫ g))
    (hP : PreservesFiniteTorDimensionSections B S hS U (edsInterHom B S hS hsq ≫ g)) :
    PreservesFiniteTorDimensionSections B S hS U g := by
  intro I hI hperf
  let := additive_modulePushforward B S hS g
  obtain ⟨δ, hT⟩ := mem_distTriang_unitBiprod_of_natural_shortExact
    (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (zero_edsRestrictPushMayerVietorisLowerShriek B S hS hsq)
    (shortExact_edsRestrictPushMayerVietorisLowerShriek B S hS hsq) I
  have := hasRightDerivedFunctor_modulePushforward B S hS g
  let RF := ((modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
  let α := ((modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS g) RF α
  let Γ := representedAffineDerivedSections B S hS U
  have key : ∀ (Z : AlgebraicSpaces B S hS) (j : Z ⟶ W) (hj : IsEtale B S hS j.hom),
      PreservesFiniteTorDimensionSections B S hS U (j ≫ g) →
      StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        (Γ.obj (RF.obj (DerivedCategory.Q.obj
          (((etaleModulePullback.{u, u} B S hS j hj ⋙
            modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) := by
    intro Z j hj hZ
    let := additive_modulePushforward B S hS (j ≫ g)
    let := additive_modulePushforward B S hS j
    let J := ((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
    have hJ : CochainComplex.IsKInjective J :=
      isKInjective_etaleModulePullback_of_isEtale B S hS j hj I hI
    let e₁ : ((etaleModulePullback.{u, u} B S hS j hj ⋙
        modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ≅
        ((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j))
        (ComplexShape.up ℤ)).app I).symm
    have hK := isKInjective_modulePushforward_of_isEtale B S hS j hj J hJ
    obtain ⟨e₂⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS g RF α _ hK
    let e₃ : ((modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≅
        ((modulePushforward B S hS (j ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
      (Functor.mapHomologicalComplexCompIso (modulePushforwardCompIso B S hS j g)
        (ComplexShape.up ℤ)).app J
    have hJperf : (smallEtaleRingedSite B S hS Z.1 Z.2).IsPerfect (DerivedCategory.Q.obj J) :=
      RingedSite.IsPerfect.of_iso _ (isPerfect_etaleModulePullback B S hS W j hj _ hperf)
        ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryFactors.app I)
    exact StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_of_iso
      (Γ.mapIso (RF.mapIso (DerivedCategory.Q.mapIso e₁) ≪≫ e₂ ≪≫
        DerivedCategory.Q.mapIso e₃)).symm (hZ J hJ hJperf)
  have hT' := Γ.map_distinguished _ (RF.map_distinguished _ hT)
  have h₂ := StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_obj₂ _
    (Γ.map_distinguished _ (RF.map_distinguished _ (binaryBiproductTriangle_distinguished
        (DerivedCategory.Q.obj (((edsRestrictPushOpen B S hS hsq).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))
        (DerivedCategory.Q.obj (((edsRestrictPushEtale B S hS hsq).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)))))
    (key _ _ (isEtale_edsOpenHom B S hS hsq) hU) (key _ _ (isEtale_edsEtaleHom B S hS hsq) hV)
  have h₁ := StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_obj₁ _ hT' h₂
    (key _ _ (isEtale_edsInterHom B S hS hsq) hP)
  obtain ⟨e⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS g RF α I hI
  exact StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_of_iso (Γ.mapIso e) h₁

end MayerVietoris

/-! ### The affine case -/

section Affine

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for presheaves on the big fppf site in the étale chart composition
/-- A perfect morphism precomposed with an étale morphism is perfect: an étale chart of the source
followed by the étale morphism is an étale chart of the target of the étale morphism. -/
theorem isPerfect_comp_of_isEtale {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {j : F ⟶ G}
    {f : G ⟶ H} (hj : IsEtale B S hS j) (hf : IsPerfect B S hS f) : IsPerfect B S hS (j ≫ f) :=
  fun U V a b h ha hb hcomm => hf U V (a ≫ j) b h (hj U a ha) hb (by simpa using hcomm)

/-- **Along an isomorphism of algebraic spaces the direct image is the étale pullback along the
inverse.**  Étale pullback along an isomorphism is an equivalence, with quasi-inverse the étale
pullback along the inverse, and its right adjoint is therefore that quasi-inverse. -/
def modulePushforwardIsoEtaleModulePullbackOfIso {Y Y' : AlgebraicSpaces B S hS} (κ : Y ⟶ Y')
    (ι : Y' ⟶ Y) (hκι : κ ≫ ι = 𝟙 Y) (hικ : ι ≫ κ = 𝟙 Y') (hκ : IsEtale B S hS κ.hom)
    (hι : IsEtale B S hS ι.hom) :
    modulePushforward B S hS κ ≅ etaleModulePullback.{u, u} B S hS ι hι :=
  have hid : IsEtale B S hS (𝟙 Y : Y ⟶ Y).hom := isEtale_of_isIso B S hS (𝟙 Y.1)
  have hid' : IsEtale B S hS (𝟙 Y' : Y' ⟶ Y').hom := isEtale_of_isIso B S hS (𝟙 Y'.1)
  have hικ' : IsEtale B S hS (ι ≫ κ : Y' ⟶ Y').hom := isEtale_comp B S hS hι hκ
  have hκι' : IsEtale B S hS (κ ≫ ι : Y ⟶ Y).hom := isEtale_comp B S hS hκ hι
  let eq : Modules.{u, u} B S hS Y'.1 Y'.2 ≌ Modules.{u, u} B S hS Y.1 Y.2 :=
    CategoryTheory.Equivalence.mk (etaleModulePullback.{u, u} B S hS κ hκ)
      (etaleModulePullback.{u, u} B S hS ι hι)
      ((etaleModulePullbackIdIso B S hS hid').symm ≪≫
        eqToIso (etaleModulePullback_congr B S hS hid' hικ' hικ.symm) ≪≫
        (etaleModulePullbackCompIso B S hS ι κ hι hκ hικ').symm)
      (etaleModulePullbackCompIso B S hS κ ι hκ hι hκι' ≪≫
        eqToIso (etaleModulePullback_congr B S hS hκι' hid hκι) ≪≫
        etaleModulePullbackIdIso B S hS hid)
  (etaleModulePullbackAdjunction B S hS κ hκ).rightAdjointUniq eq.toAdjunction

variable {U}

/-- **The affine case of the Tor-dimension estimate**: the direct image along a perfect morphism
from an affine algebraic space to `yoneda.obj U` preserves finite Tor dimension of derived
sections of perfect objects. -/
theorem preservesFiniteTorDimensionSections_of_isAffineSpace {Y : AlgebraicSpaces B S hS}
    (hY : IsAffineSpace B S hS Y.1)
    (m : Y ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
    (hm : IsPerfect B S hS m.hom) : PreservesFiniteTorDimensionSections B S hS U m := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hY
  let Y' : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let κ : Y ⟶ Y' := ObjectProperty.homMk e.hom
  let ι : Y' ⟶ Y := ObjectProperty.homMk e.inv
  have hκι : κ ≫ ι = 𝟙 Y := ObjectProperty.hom_ext _ e.hom_inv_id
  have hικ : ι ≫ κ = 𝟙 Y' := ObjectProperty.hom_ext _ e.inv_hom_id
  have hκ : IsEtale B S hS κ.hom := isEtale_of_isIso B S hS e.hom
  have hι : IsEtale B S hS ι.hom := isEtale_of_isIso B S hS e.inv
  let gT : T ⟶ U := yoneda.preimage (e.inv ≫ m.hom)
  have ht : representedSpaceMap B S hS gT = ι ≫ m :=
    ObjectProperty.hom_ext _ (by
      simp only [schemeSpaceMap_hom, Functor.map_preimage, ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.homMk_hom, gT, ι])
  have hm' : m = κ ≫ representedSpaceMap B S hS gT := by
    rw [ht, ← Category.assoc, hκι, Category.id_comp]
  have htp : IsPerfect B S hS (representedSpaceMap B S hS gT).hom := by
    rw [ht]
    exact isPerfect_comp_of_isEtale B S hS hι hm
  rw [hm']
  let := additive_modulePushforward B S hS (κ ≫ representedSpaceMap B S hS gT)
  let := additive_modulePushforward B S hS (representedSpaceMap B S hS gT)
  let := additive_modulePushforward B S hS κ
  intro I hI hperf
  let J := ((modulePushforward B S hS κ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hJ : CochainComplex.IsKInjective J :=
    isKInjective_modulePushforward_of_isEtale B S hS κ hκ I hI
  let eκ := modulePushforwardIsoEtaleModulePullbackOfIso B S hS κ ι hκι hικ hκ hι
  have : (etaleModulePullback.{u, u} B S hS ι hι).Additive :=
    etaleModulePullback_additive B S hS _ _
  have : PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS ι hι) :=
    preservesFiniteLimits_etaleModulePullback B S hS _ _
  have : PreservesFiniteColimits (etaleModulePullback.{u, u} B S hS ι hι) :=
    preservesFiniteColimits_etaleModulePullback B S hS _ _
  have hJperf : (smallEtaleRingedSite B S hS Y'.1 Y'.2).IsPerfect (DerivedCategory.Q.obj J) :=
    RingedSite.IsPerfect.of_iso _ (isPerfect_etaleModulePullback B S hS Y ι hι _ hperf)
      ((etaleModulePullback.{u, u} B S hS ι hι).mapDerivedCategoryFactors.app I ≪≫
        DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex eκ (ComplexShape.up ℤ)).symm.app I))
  have := hasRightDerivedFunctor_modulePushforward B S hS (representedSpaceMap B S hS gT)
  obtain ⟨eR⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS
    (representedSpaceMap B S hS gT)
    (Stacks.DerivedFunctor.totalRightDerived
      (modulePushforward B S hS (representedSpaceMap B S hS gT)))
    (Functor.totalRightDerivedUnit _ _ _) J hJ
  have hbase :=
    exists_hasTorAmplitudeCanonical_representedAffineDerivedSections_derivedPushforward B S hS gT
      htp _ hJperf
  have hfin : StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      ((representedAffineDerivedSections B S hS U).obj
        ((Stacks.DerivedFunctor.totalRightDerived
          (modulePushforward B S hS (representedSpaceMap B S hS gT))).obj
            (DerivedCategory.Q.obj J))) :=
    (StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
      _ _).2 hbase
  refine StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_of_iso
    ((representedAffineDerivedSections B S hS U).mapIso (eR ≪≫ DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (modulePushforwardCompIso B S hS κ
        (representedSpaceMap B S hS gT)) (ComplexShape.up ℤ)).app I))) hfin

end Affine

/-! ### The induction -/

/-- **The Tor-dimension half of Stacks 08EV over an affine base, for algebraic spaces.**  Let `f`
be a perfect morphism from a quasi-compact and quasi-separated algebraic space `X` to the affine
`yoneda.obj U`.  For every perfect object `E` of `D(𝒪_X)`, the derived sections over `U` of
`Rf_*E` have finite Tor dimension over `Γ(U)`.

This is the induction principle of Stacks 08GP: the affine case is
`AlgebraicGeometry.Space.preservesFiniteTorDimensionSections_of_isAffineSpace`, and the property
passes across elementary distinguished squares by the relative Mayer–Vietoris triangle,
`AlgebraicGeometry.Space.preservesFiniteTorDimensionSections_of_isElementaryDistinguishedSquare`.
-/
theorem preservesFiniteTorDimensionSections_of_isPerfect (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
    (hf : IsPerfect B S hS f.hom)
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    PreservesFiniteTorDimensionSections B S hS U f := by
  have key := qcqs_induction_on_self B S hS hZ X hqc hqs
    (fun Z z => IsEtale B S hS z → ∀ hZ' : IsAlgebraicSpace B S hS Z,
      PreservesFiniteTorDimensionSections B S hS U
        ((ObjectProperty.homMk z : (⟨Z, hZ'⟩ : AlgebraicSpaces B S hS) ⟶ X) ≫ f))
    (fun V hV _ hV' => preservesFiniteTorDimensionSections_of_isAffineSpace B S hS hV _
      (isPerfect_comp_of_isEtale B S hS V.2 hf))
    (fun W V U₀ f₀ hf₀ hsq _ _ _ _ hPU hPV hPP _ hW' => by
      refine preservesFiniteTorDimensionSections_of_isElementaryDistinguishedSquare B S hS U hsq _
        ?_ ?_ ?_
      · have e : edsOpenHom B S hS hsq ≫ (ObjectProperty.homMk W.1.hom.hom ≫ f) =
            ObjectProperty.homMk (U₀.ι ≫ W.1.hom.hom) ≫ f :=
          ObjectProperty.hom_ext _ (by
            simp only [ObjectProperty.FullSubcategory.comp_hom]; rfl)
        rw [e]
        exact hPU (isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq) W.2) _
      · have e : edsEtaleHom B S hS hsq ≫ (ObjectProperty.homMk W.1.hom.hom ≫ f) =
            ObjectProperty.homMk V.1.hom.hom ≫ f :=
          ObjectProperty.hom_ext _ (by
            simp only [ObjectProperty.FullSubcategory.comp_hom, ← hf₀]; rfl)
        rw [e]
        exact hPV V.2 _
      · have e : edsInterHom B S hS hsq ≫ (ObjectProperty.homMk W.1.hom.hom ≫ f) =
            ObjectProperty.homMk (pullback.fst U₀.ι f₀ ≫ U₀.ι ≫ W.1.hom.hom) ≫ f :=
          ObjectProperty.hom_ext _ (by
            simp only [ObjectProperty.FullSubcategory.comp_hom]; rfl)
        rw [e]
        have hint : IsEtale B S hS (pullback.fst U₀.ι f₀ ≫ U₀.ι) := isEtale_edsInterHom B S hS hsq
        exact hPP (by simpa only [Category.assoc] using isEtale_comp B S hS hint W.2) _)
  have e : (ObjectProperty.homMk (𝟙 X.1) : X ⟶ X) ≫ f = f :=
    ObjectProperty.hom_ext _ (by simp)
  have h := key (isEtale_of_isIso B S hS _) X.2
  rwa [e] at h

end AlgebraicGeometry.Space

end
