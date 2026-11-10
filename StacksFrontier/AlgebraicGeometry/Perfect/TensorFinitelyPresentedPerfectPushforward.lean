module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectPushforwardDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPushforwardBaseChange
import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.TensorFlat
import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange
import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.Basic
import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedComplexInduction
import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect
import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforwardBaseChange
import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
import StacksFrontier.Homology.KFlat.Pullback
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness of the derived pushforward of a tensor product with a finitely presented complex

Let `f : X ⟶ S` be a morphism of finite presentation, `E` a perfect object of `D(𝒪_X)` and `𝒢^•`
a bounded complex of finitely presented `𝒪_X`-modules, flat over `S`, with support proper over
`S`. Then `Rf_*(E ⊗^L 𝒢^•)` is perfect and its formation commutes with arbitrary base change
([Stacks, Tag 0A1H]).

## Main results

* `AlgebraicGeometry.isPerfect_derivedPushforward_tensor_of_noetherianModel`: perfectness when the
  data are the base change of data over a Noetherian base, by [Stacks, Tag 0DJQ] there and
  [Stacks, Tag 0A1D] along the base change.

## References

* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings StrictlyPerfect.structureModule
  Stacks.SheafOfModules.Tensor.ringSheaf
  TopCat.Presheaf.IsSheaf TopCat.Sheaf

/-- Perfectness of an object of `D(𝒪_S)` on a scheme is invariant under isomorphism. -/
theorem isPerfect_of_iso_scheme {S : Scheme.{u}} {K L : DerivedCategory S.Modules} (e : K ≅ L)
    (h : RingedSpace.IsPerfect (X := S.toRingedSpace) K) :
    RingedSpace.IsPerfect (X := S.toRingedSpace) L :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := S.toRingedSpace) e h

namespace FlatProperSupportFinitelyPresented

/-- **Over a locally Noetherian scheme the hypothesis of [Stacks, Tag 0A1H] on `𝒢^•` is the
hypothesis of [Stacks, Tag 0DJQ]**: finitely presented modules are coherent there
([Stacks, Tag 01XZ]). -/
theorem flatProperSupportComplex {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFinitePresentation f]
    [IsLocallyNoetherian X] {G : CochainComplex X.Modules ℤ}
    (hG : FlatProperSupportFinitelyPresented f G) :
    Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G where
  bounded := hG.bounded
  isCoherent i :=
    (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isFinitePresentation (G.X i)).2
      (hG.isFinitePresentation i)
  isFlatOver := hG.isFlatOver
  properSupport := hG.properSupport

end FlatProperSupportFinitelyPresented

/-- **Perfectness from a Noetherian model.** Let `f₀ : X₀ ⟶ S₀` be of finite presentation over a
Noetherian `S₀`, `E₀` perfect on `X₀` and `𝒢₀^•` a bounded complex of finitely presented
`𝒪_{X₀}`-modules, flat over `S₀`, with support proper over `S₀`. If `f : X ⟶ S` is a base change
of `f₀` along which `E₀` and `𝒢₀^•` pull back to `E` and `𝒢^•`, then `Rf_*(E ⊗^L 𝒢^•)` is
perfect: it is `Lg^*Rf₀_*(E₀ ⊗^L 𝒢₀^•)` by [Stacks, Tag 0A1D], and `Rf₀_*(E₀ ⊗^L 𝒢₀^•)` is
perfect by [Stacks, Tag 0DJQ]. -/
theorem isPerfect_derivedPushforward_tensor_of_noetherianModel
    {X S X₀ S₀ : Scheme.{u}} (f : X ⟶ S) (f₀ : X₀ ⟶ S₀) (g : S ⟶ S₀) (g' : X ⟶ X₀)
    (hsq : IsPullback g' f f₀ g) [IsNoetherian S₀] (hf₀ : FinitePresentation f₀)
    (E₀ : DerivedCategory X₀.Modules) (hE₀ : RingedSpace.IsPerfect (X := X₀.toRingedSpace) E₀)
    (G₀ : CochainComplex X₀.Modules ℤ)
    (hG₀ : letI : LocallyOfFinitePresentation f₀ := hf₀.locallyOfFinitePresentation
      FlatProperSupportFinitelyPresented f₀ G₀)
    (E : DerivedCategory X.Modules) (eE : (derivedPullback g'.toLRSHom.toShHom).obj E₀ ≅ E)
    (G : CochainComplex X.Modules ℤ)
    (eG : (pullbackComplex g'.toLRSHom.toShHom).obj G₀ ≅ G) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) := by
  let : LocallyOfFinitePresentation f₀ := hf₀.locallyOfFinitePresentation
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian f₀
  have hbc := isIso_tensorFlatBaseChangeMap_of_isPullback f₀ g f g' hsq hf₀.quasiCompact
    hf₀.quasiSeparated (comp_toShHom_of_comm hsq.w) E₀
    (fun n => PerfectApproximation.isQuasicoherent_homology_of_isPerfect X₀ E₀ hE₀ n) G₀
    hG₀.minus hG₀.isQuasicoherent hG₀.isFlatOver
  have h₀ :=
    Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor_of_isPerfect f₀
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X₀.sheaf) E₀ G₀ hE₀
      hG₀.flatProperSupportComplex
  have h₁ : RingedSpace.IsPerfect (X := S.toRingedSpace) ((derivedPullback g.toLRSHom.toShHom).obj
      ((derivedPushforward f₀.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X₀.sheaf).obj E₀).obj (DerivedCategory.Q.obj G₀)))) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback g.toLRSHom.toShHom _ h₀
  let e₁ := @asIso _ _ _ _ (tensorFlatBaseChangeMap f₀ g f g' (comp_toShHom_of_comm hsq.w) E₀ G₀)
    hbc
  let e₂ : (derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E₀)).obj
          (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G₀))) ≅
      (derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G)) :=
    (derivedPushforward f.toLRSHom.toShHom).mapIso
      (((derivedTensorProductFunctor X.sheaf).mapIso eE).app _ ≪≫
        ((derivedTensorProductFunctor X.sheaf).obj E).mapIso (DerivedCategory.Q.mapIso eG))
  exact isPerfect_of_iso_scheme (e₁ ≪≫ e₂) h₁

/-- **A finitely presented module flat over `S` with support proper over `S`, placed in degree
zero, satisfies the hypothesis of [Stacks, Tag 0A1H] on `𝒢^•`.** -/
theorem flatProperSupportFinitelyPresented_singleDegreeComplex' {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (M : X.Modules) (hfp : M.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom M)
    (hsupp : ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp M ⊆ (Z : Set X)) :
    FlatProperSupportFinitelyPresented f (ProperFlatBaseChange.singleDegreeComplex M) where
  bounded := ⟨0, 0, inferInstance, inferInstance⟩
  isFinitePresentation := ProperFlatBaseChange.isFinitePresentation_singleDegreeComplex M hfp
  isFlatOver := ProperFlatBaseChange.isFlatOver_singleDegreeComplex f M hflat
  properSupport := by
    obtain ⟨Z, hZ, hMZ⟩ := hsupp
    refine ⟨Z, hZ, fun i => ?_⟩
    by_cases hi : i = 0
    · subst hi
      rwa [SheafOfModules.supp_eq_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M)]
    · rw [Stacks.AlgebraicGeometry.ConfinedDevissage.supp_eq_empty_of_isZero _
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)]
      exact Set.empty_subset _

/-! ### Locality on the base -/

/-- **Perfectness is local on the base.** An object of `D(𝒪_S)` whose derived pullback to every
affine open of `S` is perfect is perfect. -/
theorem isPerfect_of_forall_isAffineOpen {S : Scheme.{u}} (K : DerivedCategory S.Modules)
    (h : ∀ W : S.Opens, IsAffineOpen W → RingedSpace.IsPerfect (X := W.toScheme.toRingedSpace)
      ((derivedPullback W.ι.toLRSHom.toShHom).obj K)) :
    RingedSpace.IsPerfect (X := S.toRingedSpace) K := by
  refine (PerfectApproximation.isPerfect_standard_iff K).2
    (Stacks.Duality.OpenImmersion.isPerfect_of_forall_exists_isPerfect_derivedRestrict _
      fun y => ?_)
  obtain ⟨W₀, hW, hyW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show y ∈ (⊤ : S.Opens) from trivial)
  let W : S.Opens := W₀
  have e :=
    Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward.derivedRestrictIsoStandardPullback
      W.ι K
  exact ⟨W, W.ι, inferInstance, ⟨y, hyW⟩, rfl,
    @Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso W.toScheme.toRingedSpace
      (Scheme.Modules.hasDerivedCategory _) _ _ e.symm
      ((PerfectApproximation.isPerfect_standard_iff _).1 (h W hW))⟩

/-- The support of the pullback of a finitely presented module is the preimage of its support. -/
theorem supp_pullback_of_isFinitePresentation {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    [M.IsFinitePresentation] :
    SheafOfModules.supp ((Scheme.Modules.pullback g).obj M) = g ⁻¹' SheafOfModules.supp M := by
  have : M.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation M
      inferInstance).2
  exact Stacks.Modules.supp_pullback g M

section BaseChange

attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

namespace FlatProperSupportFinitelyPresented

/-- **The hypothesis of [Stacks, Tag 0A1H] on `𝒢^•` is stable under base change**: pullback
preserves finite presentation, flatness over the base ([Stacks, Tag 01U8]) and properness of the
support ([Stacks, Tag 0CYP]). -/
theorem pullback {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f g) [LocallyOfFinitePresentation f]
    {G : CochainComplex X.Modules ℤ} (hG : FlatProperSupportFinitelyPresented f G) :
    letI : LocallyOfFinitePresentation f' := MorphismProperty.of_isPullback hsq inferInstance
    FlatProperSupportFinitelyPresented f' ((pullbackComplex g'.toLRSHom.toShHom).obj G) := by
  let : LocallyOfFinitePresentation f' := MorphismProperty.of_isPullback hsq inferInstance
  obtain ⟨a, b, ha, hb⟩ := hG.bounded
  obtain ⟨Z, hZ, hsub⟩ := hG.properSupport
  refine ⟨⟨a, b, ?_, ?_⟩, fun i => ?_, fun i => ?_, ⟨Z.preimage g'.continuous,
    isProperOver_preimage_baseChange g' f' f g hsq Z hZ, fun i => ?_⟩⟩
  · exact (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi =>
      Functor.map_isZero (Scheme.Modules.pullback g') (G.isZero_of_isStrictlyGE a i hi)
  · exact (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
      Functor.map_isZero (Scheme.Modules.pullback g') (G.isZero_of_isStrictlyLE b i hi)
  · exact @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ g'.toLRSHom.toShHom
      (G.X i) (hG.isFinitePresentation i)
  · exact @modulePullback_isFlatOver _ _ _ _ _ _ _ _ hsq (G.X i) (hG.isQuasicoherent i)
      (hG.isFlatOver i)
  · change SheafOfModules.supp ((Scheme.Modules.pullback g').obj (G.X i)) ⊆ _
    rw [@supp_pullback_of_isFinitePresentation _ _ g' (G.X i) (hG.isFinitePresentation i)]
    exact fun x hx => hsub i hx

end FlatProperSupportFinitelyPresented

end BaseChange

section SingleDegree

attribute [local implicit_reducible] CategoryTheory.sheafCompose
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

/-- **Reduction to a single module.** Let `𝒢^•` satisfy the hypothesis of [Stacks, Tag 0A1H].
If `Rf_*(E ⊗^L ℳ)` is perfect for every finitely presented `𝒪_X`-module `ℳ` flat over `S` with
support proper over `S`, placed in degree zero, then `Rf_*(E ⊗^L 𝒢^•)` is perfect: the functor
`Rf_*(E ⊗^L -)` is triangulated, so this follows by induction on the stupid truncations of the
bounded complex `𝒢^•`. -/
theorem isPerfect_derivedPushforward_tensor_of_singleDegree {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (E : DerivedCategory X.Modules)
    (G : CochainComplex X.Modules ℤ) (hG : FlatProperSupportFinitelyPresented f G)
    (hsingle : ∀ M : X.Modules, M.IsFinitePresentation → IsFlatOver f.toLRSHom.toShHom M →
      (∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp M ⊆ (Z : Set X)) →
      RingedSpace.IsPerfect (X := S.toRingedSpace)
        ((derivedPushforward f.toLRSHom.toShHom).obj
          (((derivedTensorProductFunctor X.sheaf).obj E).obj
            (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex M))))) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) := by
  let F := (derivedTensorProductFunctor X.sheaf).obj E ⋙ derivedPushforward f.toLRSHom.toShHom
  let : (derivedPushforward f.toLRSHom.toShHom).CommShift ℤ :=
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
      f.toLRSHom.toShHom).rightAdjointCommShift ℤ
  let : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
      f.toLRSHom.toShHom).CommShift ℤ :=
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
      f.toLRSHom.toShHom).commShift_of_leftAdjoint ℤ
  have : (derivedPushforward f.toLRSHom.toShHom).IsTriangulated :=
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
      f.toLRSHom.toShHom).isTriangulated_rightAdjoint
  let : ((derivedTensorProductFunctor X.sheaf).obj E).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).commShift_right _
  have : ((derivedTensorProductFunctor X.sheaf).obj E).IsTriangulated :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).exact_right _
  let : F.CommShift ℤ := Functor.CommShift.comp _ _
  have : F.IsTriangulated := inferInstance
  change RingedSpace.IsPerfect (X := S.toRingedSpace) (F.obj (DerivedCategory.Q.obj G))
  obtain ⟨a, b, ha, hb⟩ := hG.bounded
  refine Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex
    (fun A => RingedSpace.IsPerfect (X := S.toRingedSpace) (F.obj A))
    (fun e h => isPerfect_of_iso_scheme (F.mapIso e) h)
    (fun A hA => RingedSpace.isPerfect_of_isZero (X := S.toRingedSpace) (F.map_isZero hA))
    (fun T hT h₁ h₃ => ?_) G ?_ (fun i => ?_)
  · exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished
      (X := S.toRingedSpace) _
      (F.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hT)) h₁ h₃
  · refine (Set.finite_Icc a b).subset fun i hi => ⟨?_, ?_⟩ <;> by_contra! h
    · exact hi (G.isZero_of_isStrictlyGE a i h)
    · exact hi (G.isZero_of_isStrictlyLE b i h)
  · obtain ⟨Z, hZ, hsub⟩ := hG.properSupport
    have h₀ := hsingle (G.X i) (hG.isFinitePresentation i) (hG.isFlatOver i) ⟨Z, hZ, hsub i⟩
    have e : F.obj ((DerivedCategory.singleFunctor X.Modules 0).obj (G.X i))⟦-i⟧ ≅
        F.obj ((DerivedCategory.singleFunctor X.Modules i).obj (G.X i)) :=
      (F.commShiftIso (-i)).symm.app _ ≪≫
        F.mapIso (((DerivedCategory.singleFunctors X.Modules).shiftIso (-i) i 0
          (by omega)).app (G.X i))
    exact isPerfect_of_iso_scheme e
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift (X := S.toRingedSpace) h₀ (-i))

end SingleDegree

end AlgebraicGeometry

end
