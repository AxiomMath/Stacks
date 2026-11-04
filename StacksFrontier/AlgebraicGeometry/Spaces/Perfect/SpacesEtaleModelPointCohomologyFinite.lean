module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperBaseRingCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointPerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitudeSupplement

/-!
# The direct image of a perfect object along a proper morphism has finite cohomology

Let `T` be an affine object of the big fppf site of a scheme `S` with `R = Γ(T, 𝒪_T)`
Noetherian, and `f : X ⟶ T` a proper morphism of algebraic spaces, read as the morphism
`(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` of the spaces-étale model. For a perfect object `E` of the
model every cohomology module of `Rf_*E`, read in `D(R)`, is a finite `R`-module. With
`isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_moduleFinite_homology` this makes
`Rf_*E` perfect over the point when `f` is moreover flat: the Noetherian case of the proof of
Stacks 0CTM.

Transported to `𝒪_X`-modules and read in `D(R)`, `Rf_*` is a right derived functor of global
sections read as `R`-modules
(`AlgebraicGeometry.Space.isRightDerivedFunctor_pointModulesTransport`), so it is exact and on a
single coherent module its cohomology is the cohomology `Hⁿ(X, 𝓕)`, finite by Stacks 08AS over `T`
(`AlgebraicGeometry.Space.moduleFinite_rightDerived_baseRingGlobalSectionsModule_of_isProper`).
The image of `E` in `D(𝒪_X)` is bounded (it has finite Tor amplitude) and pseudo-coherent, so its
cohomology sheaves are coherent on the locally Noetherian `X` (Stacks 08IK); the finite modules
over a Noetherian ring form a Serre subcategory, and a dévissage along the canonical truncations
concludes.

## Main results

* `isSerreClass_moduleFinite`: finite modules over a Noetherian ring form a Serre subcategory.
* `isRightDerivedFunctor_pointModulesTransport`: `Rf_*`, transported to `𝒪_X`-modules and read in
  `D(R)`, is a right derived functor of global sections read as `R`-modules.
* `moduleFinite_homology_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper`: for `f`
  proper over a Noetherian affine `T` and `E` perfect, every cohomology module of `Rf_*E` is
  finite.
* `isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper_of_isNoetherianRing`: for
  `f` proper and flat over a Noetherian affine `T`, `Rf_*E` is perfect over the point.

## References

* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance] hasCoproducts_derivedCategory_modules
-- `D(R)` is the standard model, the one `AlgebraicGeometry.Space.pointDerivedEquiv` lands in.

/-! ### Finite modules over a Noetherian ring -/

/-- **Finite modules over a Noetherian ring form a Serre subcategory**: submodules and quotients
of finite modules are finite, and so is an extension of finite modules. -/
theorem isSerreClass_moduleFinite (R : Type u) [CommRing R] [IsNoetherianRing R] :
    ObjectProperty.IsSerreClass
      (fun M : ModuleCat.{u} R => Module.Finite R M : ObjectProperty (ModuleCat.{u} R)) where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _, inferInstance⟩
  prop_of_mono {X Y} f _ hY := by
    have : Module.Finite R Y := hY
    exact Module.Finite.of_injective f.hom ((ModuleCat.mono_iff_injective f).1 ‹_›)
  prop_of_epi {X Y} f _ hX := by
    have : Module.Finite R X := hX
    exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).1 ‹_›)
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have : Module.Finite R S.X₁ := h₁
    have : Module.Finite R S.X₃ := h₃
    have hex : Function.Exact S.f.hom S.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact
    have hker : LinearMap.ker S.g.hom ≤ LinearMap.range S.f.hom := fun x hx =>
      (hex x).1 hx
    have : _root_.IsNoetherian R (LinearMap.ker S.g.hom) := isNoetherian_of_le hker
    have : Module.Finite R (S.X₂ ⧸ LinearMap.ker S.g.hom) :=
      Module.Finite.equiv S.g.hom.quotKerEquivRange.symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker S.g.hom)

/-! ### `Rf_*` read in `D(R)` as a right derived functor of global sections -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}
  {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)

/-- Direct image to the point followed by the `R`-module at the point is global sections of the
corresponding `𝒪_X`-module read as an `R`-module
(`AlgebraicGeometry.Space.pushforwardToBaseRingIso`). -/
def pushforwardPointModulesIso :
    (spacesEtaleModelModulesEquiv B S hS X).inverse ⋙
        (spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos ⋙
          (baseRingPointModulesEquiv (R := R)).functor ≅
      baseRingGlobalSectionsModule B S hS X φ :=
  Functor.isoWhiskerLeft (spacesEtaleModelModulesEquiv B S hS X).inverse
      (pushforwardToBaseRingIso B S hS X φ) ≪≫
    Functor.isoWhiskerRight (spacesEtaleModelModulesEquiv B S hS X).counitIso
      (baseRingGlobalSectionsModule B S hS X φ)

section Transport

variable (Rf : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules ⥤
    DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules)
  (αf : (spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos.mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)

/-- The unit exhibiting `Rf_*`, transported to `𝒪_X`-modules and read in `D(R)`, as a right
derived functor of global sections read as `R`-modules. -/
def pointModulesTransportUnit :
    (baseRingGlobalSectionsModule B S hS X φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ ((spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategory ⋙
        Rf ⋙ (baseRingPointModulesEquiv (R := R)).functor.mapDerivedCategory) :=
  Functor.whiskerRight (mapHomotopyCategoryIsoOfIso
      (pushforwardPointModulesIso B S hS φ).symm).hom DerivedCategory.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl _)
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((spacesEtaleModelModulesEquiv B S hS X).inverse.mapHomotopyCategory
      (ComplexShape.up ℤ))
      (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl _)
          (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
        Functor.whiskerLeft
          ((spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos.mapHomotopyCategory
            (ComplexShape.up ℤ))
          (baseRingPointModulesEquiv (R := R)).functor.mapDerivedCategoryFactorsh.inv ≫
        Functor.whiskerRight αf (baseRingPointModulesEquiv (R := R)).functor.mapDerivedCategory) ≫
    Functor.whiskerRight
      (spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategoryFactorsh.inv
      (Rf ⋙ (baseRingPointModulesEquiv (R := R)).functor.mapDerivedCategory)

variable [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
      (spacesEtaleModelRingedTopos B S hS X).Modules (ComplexShape.up ℤ))]

include αf in
/-- The transported unit is invertible at every K-injective complex of `𝒪_X`-modules: there it is
the unit of `Rf_*` at the K-injective complex `E⁻¹(I)` up to isomorphisms. -/
theorem isIso_pointModulesTransportUnit_app (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hI : I.IsKInjective) :
    IsIso ((pointModulesTransportUnit B S hS φ Rf αf).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  have hEI : CochainComplex.IsKInjective
      (((spacesEtaleModelModulesEquiv B S hS X).inverse.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    have := hI
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact
      (spacesEtaleModelModulesEquiv B S hS X).inverse
      (spacesEtaleModelModulesEquiv B S hS X).functor
      (spacesEtaleModelModulesEquiv B S hS X).toAdjunction I
  have hf : IsIso (αf.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((spacesEtaleModelModulesEquiv B S hS X).inverse.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I))) := by
    obtain ⟨Rs⟩ := Stacks.Injectives.exists_functorial_quasiIso_isKInjective.{u}
      (spacesEtaleModelRingedTopos B S hS X).Modules
    exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      ((spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos.mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun K ↦ ⟨Rs.functor.obj K, Rs.inclusion.app K, Rs.isKInjective K, Rs.quasiIso K⟩)).2
        DerivedCategory.Qh Rf αf _ hEI
  have : IsIso (αf.app (((spacesEtaleModelModulesEquiv B S hS X).inverse.mapHomotopyCategory
      (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := hf
  simp only [pointModulesTransportUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

include αf in
/-- **`Rf_*`, transported to `𝒪_X`-modules and read in `D(R)`, is a right derived functor of
global sections read as `R`-modules.** -/
theorem isRightDerivedFunctor_pointModulesTransport :
    ((spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategory ⋙
        Rf ⋙ (baseRingPointModulesEquiv (R := R)).functor.mapDerivedCategory).IsRightDerivedFunctor
      (pointModulesTransportUnit B S hS φ Rf αf)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) := by
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    isGrothendieckAbelian_modules B S hS X.1 X.2
  exact Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ DerivedCategory.Qh _ _ fun I hI ↦ isIso_pointModulesTransportUnit_app B S hS φ Rf αf I hI

end Transport

/-! ### Finiteness of the cohomology of `Rf_*E` -/

section Finite

variable {T : BigFppfOver B S hS}

/-- **The cohomology of `Rf_*E` is finite for `f` proper over a Noetherian affine `T` and `E`
perfect**, for any right derived functor `Rf_*` of the direct image to the point. Let `T` be
affine with `R = Γ(T, 𝒪_T)` Noetherian and `f : X ⟶ T` proper, read as the morphism
`(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` of the spaces-étale model, and let `E` be a perfect object of
the model. Then every cohomology module of `Rf_*E`, read in `D(R)`, is finite.

The image `K` of `E` in `D(𝒪_X)` is bounded with coherent cohomology sheaves (Stacks 08IK on the
locally Noetherian `X`); `Rf_*` read in `D(R)` is an exact functor computing `Hⁿ(X, 𝓕)` on a
coherent `𝓕` placed in one degree, which is finite (Stacks 08AS over `T`); and the objects it
carries to objects with finite cohomology form a triangulated subcategory, which contains `K` by
dévissage along the canonical truncations. -/
theorem moduleFinite_homology_rightDerived_spacesEtaleModelToBaseRing_of_isProper
    (hZ : B.Contains (⊤_ Scheme.{u})) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    [IsNoetherianRing (baseRing B S hS T)] (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (Rf : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules ⥤
      DerivedCategory (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).Modules)
    (αf : (spacesEtaleModelToBaseRing B S hS X
        (baseRingHomOfMap f)).pushforwardTopos.mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
      (spacesEtaleModelRingedTopos B S hS X).Modules (ComplexShape.up ℤ))]
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) (i : ℤ) :
    Module.Finite (baseRing B S hS T)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing B S hS T)) i).obj
        ((pointDerivedEquiv (R := baseRing B S hS T)).functor.obj (Rf.obj E))) := by
  let φ := baseRingHomOfMap f
  let Ee := spacesEtaleModelModulesEquiv B S hS X
  let P := (baseRingPointModulesEquiv (R := baseRing B S hS T)).functor
  let Φ := Ee.inverse.mapDerivedCategory ⋙ Rf ⋙ P.mapDerivedCategory
  let β := pointModulesTransportUnit B S hS φ Rf αf
  have := isGrothendieckAbelian_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  have := isRightDerivedFunctor_pointModulesTransport B S hS φ Rf αf
  let _ := Functor.IsRightDerivedFunctor.commShift Φ β
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
  have : Φ.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor _ Φ β
  have hcomp := isIso_pointModulesTransportUnit_app B S hS φ Rf αf
  -- finite modules form a weak Serre subcategory
  let Q : ObjectProperty (ModuleCat.{u} (baseRing B S hS T)) :=
    fun M => Module.Finite (baseRing B S hS T) M
  have := isSerreClass_moduleFinite (baseRing B S hS T)
  have hQ : WeakSerre.IsWeakSerre Q := WeakSerre.isWeakSerre_of_isWeakSerreClass Q
  have : Q.IsClosedUnderIsomorphisms := hQ.isClosedUnderIsomorphisms
  -- the objects carried by `Φ` to objects with finite cohomology
  let Pd := (DerivedCategoryB.derivedCategoryB Q).inverseImage Φ
  have := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms Q hQ
  have := DerivedCategoryB.derivedCategoryB_isTriangulated Q hQ
  have hPdiso : Pd.IsClosedUnderIsomorphisms := inferInstance
  have : Pd.IsStableUnderShift ℤ := by
    have := DerivedCategoryB.derivedCategoryB_isStableUnderShift Q hQ
    refine ⟨fun a ↦ ⟨fun K hK ↦ ?_⟩⟩
    exact (DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms Q hQ).of_iso
      ((Φ.commShiftIso a).app K).symm ((DerivedCategoryB.derivedCategoryB Q).le_shift a _ hK)
  have : Pd.IsTriangulatedClosed₂ := by
    refine ObjectProperty.IsTriangulatedClosed₂.mk' (fun Tr hTr h₁ h₃ ↦ ?_)
    exact (DerivedCategoryB.derivedCategoryB Q).ext_of_isTriangulatedClosed₂ (Φ.mapTriangle.obj Tr)
      (Φ.map_distinguished Tr hTr) h₁ h₃
  -- the image of `E` in `D(𝒪_X)`: bounded, with coherent cohomology
  let K := Ee.functor.mapDerivedCategory.obj E
  have hXqcqs := qcqs_of_isFinitePresentation_schemeSpace hZ f hT hfp
  obtain ⟨a, b, hab, hamp⟩ := exists_hasTorAmplitude_of_isPerfect_spacesEtaleModel B S hS X
    hXqcqs.1 E hE
  have hKGE : K.IsGE a := isGE_mapDerivedCategory_spacesEtaleModelModulesEquiv B S hS X E a
    (Stacks.SheafOfModules.DerivedTensorProduct.isGE_of_hasTorAmplitude
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, u + 1}
        (spacesEtaleModelRingedTopos B S hS X).toRingedSite) E hamp)
  have hKLE : K.IsLE b := isLE_mapDerivedCategory_spacesEtaleModelModulesEquiv B S hS X E b
    (Stacks.SheafOfModules.DerivedTensorProduct.isLE_of_hasTorAmplitude
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, u + 1}
        (spacesEtaleModelRingedTopos B S hS X).toRingedSite) E hamp)
  have hXN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 (schemeSpace T).2 f.hom hf.2.1.1
      (hasEtaleLocalProperty_isLocallyNoetherian_schemeSpace B S hS hT)
  obtain ⟨L, hL, ⟨eL⟩⟩ := RingedSite.isPseudoCoherent_of_isPerfect_univ _
    (isPerfect_spacesEtaleModelModulesEquiv_functor B S hS X E hE)
  have hcoh : ∀ q : ℤ, IsCoherent B S hS X.1 X.2
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj K) := fun q ↦
    (isCoherent_iff_isCoherentOnSite B S hS X.1 X.2 _).2
      (isCoherentOnSite_homology_of_isPseudoCoherentFrom_of_lt B S hS X.1 X.2 hXN K (q - 1) q
        ⟨L, hL (q - 1), ⟨eL⟩⟩ (by omega))
  -- a coherent module placed in degree zero is carried to an object with finite cohomology
  have hsingle : ∀ q : ℤ, Pd ((DerivedCategory.singleFunctor _ 0).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj K)) := by
    intro q n
    refine Stacks.SmallDerivedCategory.prop_homologyFunctor_obj_singleFunctor_obj
      (baseRingGlobalSectionsModule B S hS X φ) Φ β hcomp Q _ (fun p ↦ ?_) 0 n
    rcases lt_or_ge p 0 with hp | hp
    · exact Q.prop_of_iso
        ((ModuleCat.isZero_of_subsingleton (ModuleCat.of (baseRing B S hS T) PUnit)).isoZero.trans
          (Functor.isZero_rightDerivedPlus_of_neg _ _ p hp).isoZero.symm)
        (show Module.Finite (baseRing B S hS T) PUnit.{u + 1} from inferInstance)
    · lift p to ℕ using hp
      exact Q.prop_of_iso
        (CategoryTheory.rightDerivedPlusObjIso (baseRingGlobalSectionsModule B S hS X φ) _ p).symm
        (moduleFinite_rightDerived_baseRingGlobalSectionsModule_of_isProper B S hS hT f hf _
          (hcoh q) p)
  have hK : Pd K := by
    refine Pd.prop_of_isGE_of_isLE a (b - a).toNat K hKGE ?_ fun q _ _ ↦ hsingle q
    have hn : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
    rw [hn]
    exact DerivedCategory.TStructure.t.isLE_of_le K b (a + (b - a)) (by omega)
  -- back to the model
  let Eq := Stacks.DerivedGlueing.mapDerivedCategoryEquivalence Ee.functor Ee.inverse
    Ee.unitIso Ee.counitIso
  have e : Φ.obj K ≅ P.mapDerivedCategory.obj (Rf.obj E) :=
    P.mapDerivedCategory.mapIso (Rf.mapIso (Eq.unitIso.app E).symm)
  exact Q.prop_of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing B S hS T)) i).mapIso e) (hK i)

/-- **The cohomology of `Rf_*E` is finite for `f` proper over a Noetherian affine `T` and `E`
perfect**, for the chosen derived direct image `derivedPushforward`. -/
theorem moduleFinite_homology_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper
    (hZ : B.Contains (⊤_ Scheme.{u})) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    [IsNoetherianRing (baseRing B S hS T)] (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) (i : ℤ) :
    Module.Finite (baseRing B S hS T)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing B S hS T)) i).obj
        ((pointDerivedEquiv (R := baseRing B S hS T)).functor.obj
          ((derivedPushforward
            (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E))) :=
  moduleFinite_homology_rightDerived_spacesEtaleModelToBaseRing_of_isProper B S hS hZ hT f hf hfp _
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
      (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))) E hE i

/-- **The Noetherian case of Stacks 0CTM on the point.** Let `T` be affine with `R = Γ(T, 𝒪_T)`
Noetherian and `f : X ⟶ T` proper and flat, read as the morphism
`(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` of the spaces-étale model. Then `Rf_*E` is perfect over the
punctual ringed topos for every perfect `E`: it has finite Tor amplitude, and its cohomology
modules are finite (Stacks 066E). -/
theorem isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper_of_isNoetherianRing
    (hZ : B.Contains (⊤_ Scheme.{u})) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    [IsNoetherianRing (baseRing B S hS T)] (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) :
    (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite.IsPerfect
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E) := by
  have hXqcqs := qcqs_of_isFinitePresentation_schemeSpace hZ f hT hfp
  exact isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_moduleFinite_homology B S hS hZ
    hXqcqs.1 hXqcqs.2 f hflat hT E hE
    (moduleFinite_homology_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper B S hS hZ hT
      f hf hfp E hE)

/-- **`RΓ(X, E)` is pseudo-coherent over a Noetherian ring** `R = Γ(T, 𝒪_T)`, for `T` affine,
`f : X ⟶ T` proper and of finite presentation and `E` perfect, read in `D(R)`: it is bounded
above and its cohomology modules are finite (Stacks 066E). This is the input of the Noetherian
approximation step of Stacks 0A1P, where it is base changed to the limit ring (Stacks 0650). -/
theorem isPseudoCoherent_pointDerivedEquiv_derivedPushforward_of_isProper_of_isNoetherianRing
    (hZ : B.Contains (⊤_ Scheme.{u})) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    [IsNoetherianRing (baseRing B S hS T)] (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((pointDerivedEquiv (R := baseRing B S hS T)).functor.obj
        ((derivedPushforward
          (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E)) := by
  have hXqcqs := qcqs_of_isFinitePresentation_schemeSpace hZ f hT hfp
  obtain ⟨c, hc⟩ := exists_isLE_derivedPushforward_spacesEtaleModelToBaseRing_of_isPerfect B S hS
    hZ hXqcqs.1 hXqcqs.2 (baseRingHomOfMap f) E hE
  refine ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology _ 0
    (baseRing B S hS T)).2.1).2 ⟨⟨c, fun i hi => ?_⟩,
      moduleFinite_homology_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper B S hS hZ hT
        f hf hfp E hE⟩
  exact ((baseRingPointModulesEquiv (R := baseRing B S hS T)).functor.map_isZero
    ((DerivedCategory.isLE_iff _ c).1 hc i hi)).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (baseRingPointModulesEquiv (R := baseRing B S hS T)).functor i).app _)

end Finite

end AlgebraicGeometry.Space

end
