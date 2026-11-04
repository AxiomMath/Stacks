module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.Datum
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineHomToStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSectionsLocalModels
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelocalizeRelativePerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeAffineTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPushforwardSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChange

/-!
# Perfect direct images over an affine target, read over the spectrum of a ring

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `Y` affine, read over `Spec A`
as in `AlgebraicGeometry.Space.exists_relocalizeSpec_of_isAffineSpace`: `Y ≅ h_{(Spec A, g)}`,
`X ≅ Λ X_A`, and `f` the lower-shriek extension of the structure morphism of `X_A`. If
`Rf_*(E ⊗^L K)` is perfect for every perfect `E` on `X`, then `RΓ(X_A, E_A ⊗^L K_A)` is a perfect
complex of `A`-modules for every perfect `E_A` on `X_A`, where `K_A` corresponds to `K`.

## Main results

* `AlgebraicGeometry.Space.DerivedChow.toBase_eq_toFinalHom`
* `AlgebraicGeometry.Space.isPerfect_derivedSections_tensor_relocalize`
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_relocalizeSpec`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
-- No global `HasDerivedCategory` instance applies to modules on small étale sites, which are not
-- `SmallCategory`; at low priority the standard model chooses nothing where a global one exists
-- (`D(A)` is taken at the standard model explicitly below).
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

/-- The structure morphism of an algebraic space over `Spec A` to the base is the morphism to the
final object `h_{Spec A}`. -/
theorem DerivedChow.toBase_eq_toFinalHom {B : BigFppfSite.{u}} {A : Type u} [CommRing A]
    {hA : B.Contains (Spec (.of A))} (XA : AlgebraicSpaces B (Spec (.of A)) hA) :
    DerivedChow.toBase B _ hA XA = toFinalHom B hA XA :=
  ObjectProperty.hom_ext _ ((isTerminal_yoneda_obj_base B _ hA).hom_ext _ _)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))} {g : B.obj hA ⟶ B.obj hS}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {eY : Y ≅ schemeSpace (Over.mk g)}
  {XA : AlgebraicSpaces B (Spec (.of A)) hA} {e : relocalizeSpace B hA hS g XA ≅ X}

/-- Moving an isomorphism across a commuting square: `a ≫ f ≫ i.hom = t ≫ c` gives
`a ≫ f = t ≫ c ≫ i.inv`. -/
private theorem comp_eq_comp_comp_inv_of_comp_eq {C : Type*} [Category C] {P Q R T U : C}
    {a : P ⟶ Q} {f : Q ⟶ R} {i : R ≅ U} {t : P ⟶ T} {c : T ⟶ U}
    (h : a ≫ f ≫ i.hom = t ≫ c) : a ≫ f = t ≫ c ≫ i.inv := by
  rw [← cancel_mono i.hom]
  simpa using h

/-- **Perfect direct images give perfect derived sections over `Spec A`.** In the situation of
`AlgebraicGeometry.Space.exists_relocalizeSpec_of_isAffineSpace`, let `K ∈ D(𝒪_X)` with
`Rf_*(E ⊗^L K)` perfect for every perfect `E` on `X`, and let `K_A ∈ D(𝒪_{X_A})` correspond to
`K` through `Λ X_A ≅ X`. Then `RΓ(X_A, E_A ⊗^L K_A)` is perfect in `D(A)` for every perfect
`E_A` on `X_A`. -/
theorem isPerfect_derivedSections_tensor_relocalize
    (he : e.hom ≫ f ≫ eY.hom =
      relocalizeHom B hA hS g (toFinalHom B hA XA) ≫ relocalizeBaseHom B hA hS g)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (h : ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E →
        (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
          ((derivedModulePushforward B S hS f).obj
            (((smallEtaleDerivedTensor B S hS X).obj E).obj K)))
    (EA : DerivedCategory (Modules.{u, u} B _ hA XA.1 XA.2))
    (hEA : (smallEtaleRingedSite B _ hA XA.1 XA.2).IsPerfect EA) :
    @StacksDraft.Perfect.IsPerfect _ _ (HasDerivedCategory.standard _)
      ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
        ((derivedModulePushforward B _ hA (DerivedChow.toBase B _ hA XA)).obj
          (((smallEtaleDerivedTensor B _ hA XA).obj EA).obj
            ((relocalizeDerivedEquivalence B hA hS g XA.1 XA.2).inverse.obj
              ((smallEtaleDerivedModulePullback B S hS e.hom).obj K))))) := by
  refine isPerfect_representedAffineDerivedSections_obj B _ hA (baseSiteObj B _ hA) _ ?_
  rw [DerivedChow.toBase_eq_toFinalHom]
  let ρ := relocalizeDerivedEquivalence B hA hS g XA.1 XA.2
  let tf := relocalizeHom B hA hS g (toFinalHom B hA XA)
  let b := relocalizeBaseHom B hA hS g ≫ eY.inv
  have : IsIso b.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map b))
  have sq : IsPullback e.hom tf f b :=
    IsPullback.of_horiz_isIso ⟨comp_eq_comp_comp_inv_of_comp_eq he⟩
  have hbe : IsEtale B S hS b.hom := isEtale_of_isIso B S hS b.hom
  let E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
    (smallEtaleDerivedModulePullback B S hS e.inv).obj
      ((relocalizeDerivedFunctor B hA hS g XA.1 XA.2).obj EA)
  have hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E :=
    isPerfect_smallEtaleDerivedModulePullback e.inv _
      (isPerfect_relocalizeDerivedFunctor_obj B hA hS g XA.1 XA.2 EA hEA)
  have hEe : (smallEtaleDerivedModulePullback B S hS e.hom).obj E ≅
      (relocalizeDerivedFunctor B hA hS g XA.1 XA.2).obj EA :=
    ((smallEtaleDerivedModulePullbackCompIso B S hS e.hom e.inv).app _) ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS e.hom_inv_id).app _ ≪≫
      (smallEtaleDerivedModulePullbackIdIso B S hS _).app _
  have hiso := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f b tf e.hom sq hbe
    (Functor.relativelyRepresentable.of_isIso yoneda b.hom)
    (((smallEtaleDerivedTensor B S hS X).obj E).obj K)
  have hP := isPerfect_smallEtaleDerivedModulePullback b _ (h E hE)
  refine (isPerfect_relocalizeDerivedFunctor_obj_iff B hA hS g _ _ _).1 ?_
  refine isPerfect_of_iso B S hS hP ?_
  exact @asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B S hS f b tf e.hom sq.w
      (((smallEtaleDerivedTensor B S hS X).obj E).obj K)) hiso ≪≫
    (derivedModulePushforward B S hS tf).mapIso
      ((smallEtaleDerivedPullbackTensorIso e.hom).app (E, K) ≪≫
        ((smallEtaleDerivedTensor B S hS _).mapIso hEe).app _ ≪≫
        ((smallEtaleDerivedTensor B S hS _).obj _).mapIso (ρ.counitIso.app _).symm ≪≫
        (relocalizeDerivedTensorObjIso B hA hS g XA.1 XA.2 EA _).symm) ≪≫
    (relocalizeDerivedPushforwardObjIso B hA hS g (toFinalHom B hA XA) _).symm

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  sheafTensor_additive_inverseImageRingedSite_over
  sheafTensor_obj_additive_inverseImageRingedSite_over
  hasMapBifunctor_sheafTensor_inverseImageRingedSite_over
  sheafTensor_additive_relocalizeHom sheafTensor_obj_additive_relocalizeHom
  hasMapBifunctor_sheafTensor_relocalizeHom

/-- **Relative perfectness over an affine target, read over `Spec A`.** In the situation of
`AlgebraicGeometry.Space.exists_relocalizeSpec_of_isAffineSpace`, let `f` be flat and locally of
finite presentation and `K ∈ D_QCoh(𝒪_X)`. If the object `K_A` of `D(𝒪_{X_A})` corresponding
to `K` through `Λ X_A ≅ X` is `Spec A`-perfect, then `K` is `Y`-perfect. -/
theorem isPerfectRelativeToCanonical_of_relocalizeSpec
    (he : e.hom ≫ f ≫ eY.hom =
      relocalizeHom B hA hS g (toFinalHom B hA XA) ≫ relocalizeBaseHom B hA hS g)
    (hfl : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hK : QcohDerived B S hS X K)
    (hflA : IsFlat B _ hA (DerivedChow.toBase B _ hA XA).hom)
    (hlfpA : IsLocallyOfFinitePresentation B _ hA (DerivedChow.toBase B _ hA XA).hom)
    (hKA : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B _ hA (DerivedChow.toBase B _ hA XA)
      hflA hlfpA ((relocalizeDerivedEquivalence B hA hS g XA.1 XA.2).inverse.obj
        ((smallEtaleDerivedModulePullback B S hS e.hom).obj K))) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp K := by
  let ρ := relocalizeDerivedEquivalence B hA hS g XA.1 XA.2
  let b := relocalizeBaseHom B hA hS g ≫ eY.inv
  have : IsIso b.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map b))
  have : IsIso e.hom.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map e.hom))
  have hw : e.hom ≫ f = relocalizeHom B hA hS g (toFinalHom B hA XA) ≫ b :=
    comp_eq_comp_comp_inv_of_comp_eq he
  rw [← DerivedChow.toBase_eq_toFinalHom] at hw
  have hQ : QcohDerived B _ hA XA
      (ρ.inverse.obj ((smallEtaleDerivedModulePullback B S hS e.hom).obj K)) :=
    (qcohDerived_relocalizeDerivedFunctor_obj_iff B hA hS g XA.2 _).1
      ((QcohDerived B S hS _).prop_of_iso (ρ.counitIso.app _).symm
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ e.hom K hK))
  have hT := isPerfectRelativeToCanonical_relocalizeDerivedFunctor_obj B hA hS g
    (DerivedChow.toBase B _ hA XA) hflA hlfpA _ hQ hKA
  exact isPerfectRelativeToCanonical_of_isEtale_of_isSurjective e.hom
    (relocalizeHom B hA hS g (DerivedChow.toBase B _ hA XA)) f b hfl hlfp _ _
    (isEtale_of_isIso B S hS e.hom.hom) (isSurjective_of_isIso B S hS e.hom.hom)
    (isEtale_of_isIso B S hS b.hom) hw K
    (isPerfectRelativeToCanonical_of_iso _ _ _ (ρ.counitIso.app _) hT)

end AlgebraicGeometry.Space

end
