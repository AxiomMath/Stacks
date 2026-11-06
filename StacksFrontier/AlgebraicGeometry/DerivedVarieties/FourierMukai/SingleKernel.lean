module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BoundedCoherentConditions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleAcyclic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.CanonicalSheafCertificate
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces

/-!
# The Fourier-Mukai functor of a module flat over the source, on modules

Let `S` be a scheme, let `X` and `Y` be schemes over `S` with `Y ⟶ S` flat, and let `𝒦` be an
`𝒪_{X ×_S Y}`-module flat over `X`. For an `𝒪_X`-module `ℱ` placed in degree zero, the
Fourier-Mukai functor with kernel `𝒦` is computed by the underived formula:

* `L pr_1^*(ℱ[0]) = (pr_1^*ℱ)[0]`, since `pr₁` is flat;
* `(pr_1^*ℱ)[0] ⊗^𝐋 𝒦[0] = (pr_1^*ℱ ⊗ 𝒦)[0]`: the left side is bounded below by `0` because
  `𝒦` has Tor amplitude `[0, 0]` over `pr_1^{-1}𝒪_X`, bounded above by `0` by right
  t-exactness, and in degree `0` the canonical map to the ordinary tensor product is an
  isomorphism;
* `R pr_{2,*}(𝒢[0]) = (pr_{2,*}𝒢)[0]` whenever `R^q pr_{2,*}𝒢 = 0` for `q > 0`.

## Main definitions

* `AlgebraicGeometry.fourierMukaiPullbackSingleIso`: `L pr_1^*(-[0]) ≅ (pr_1^* -)[0]`.
* `AlgebraicGeometry.fourierMukaiTensorSingleNatTrans`: the canonical map
  `𝒢[0] ⊗^𝐋 𝒦[0] ⟶ (𝒢 ⊗ 𝒦)[0]`.
* `AlgebraicGeometry.fourierMukaiPushforwardSingleUnit`: the canonical map
  `(pr_{2,*} 𝒢)[0] ⟶ R pr_{2,*}(𝒢[0])`.
* `AlgebraicGeometry.fourierMukaiSingleIso`: the resulting natural isomorphism
  `Φ_𝒦(ℱ[0]) ≅ pr_{2,*}(pr_1^*ℱ ⊗ 𝒦)[0]`, along any functor into `Mod(𝒪_X)` whose values have
  integrand without higher direct images.

## References

* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 0G00](https://stacks.math.columbia.edu/tag/0G00)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-! ### The derived pullback of a module along a flat first projection -/

/-- **`L pr_1^*(ℱ[0]) ≅ (pr_1^*ℱ)[0]` for a flat first projection**, naturally in `ℱ`. -/
def fourierMukaiPullbackSingleIso (hflat : AlgebraicGeometry.IsFlat (fourierMukaiFst f g)) :
    DerivedCategory.singleFunctor X.Modules 0 ⋙ fourierMukaiPullback f g ≅
      modulePullback (fourierMukaiFst f g) ⋙
        DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0 :=
  Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQh _ 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.singleFunctor _ 0)
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackComparisonIsoOfIsFlat _ hflat) ≪≫
    Stacks.DerivedFunctor.mapSingleQhIso (modulePullback (fourierMukaiFst f g)) 0


/-! ### The derived tensor product with a module flat over `X` -/

section Tensor

variable (K : (Limits.pullback f g).Modules)

/-- `- ⊗ 𝒦` on modules over `X ×_S Y`, in the spelling of the derived tensor product. -/
abbrev fourierMukaiModuleTensor :
    (Limits.pullback f g).Modules ⥤ (Limits.pullback f g).Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Limits.pullback f g).toRingedSpace).presheaf,
    ((Limits.pullback f g).toRingedSpace).IsSheaf⟩).flip.obj K

/-- **The canonical map `𝒢[0] ⊗^𝐋 𝒦[0] ⟶ (𝒢 ⊗ 𝒦)[0]`** on `X ×_S Y`, natural in `𝒢`. -/
abbrev fourierMukaiTensorSingleNatTrans :
    DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0 ⋙
        fourierMukaiTensor f g ((DerivedCategory.singleFunctor _ 0).obj K) ⟶
      fourierMukaiModuleTensor f g K ⋙ DerivedCategory.singleFunctor _ 0 :=
  Stacks.DerivedTensor.RingedSite.tensorSingleNatTrans (Limits.pullback f g).toRingedSpace.sheaf
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _) K

/-- A module on `X ×_S Y`, placed in degree zero, is flat over `X` in each degree when it is flat
over `X`. -/
lemma isFlatOver_single_X (hK : IsFlatOver (Limits.pullback.fst f g).toLRSHom.toShHom K)
    (i : ℤ) : IsFlatOver (Limits.pullback.fst f g).toLRSHom.toShHom
      (((CochainComplex.singleFunctor (Limits.pullback f g).Modules 0).obj K).X i) := by
  by_cases hi : i = 0
  · subst hi
    exact (isFlatOver_iff_of_iso _ (HomologicalComplex.singleObjXSelf _ 0 K)).2 hK
  · exact isFlatOver_of_isZero _ _ (HomologicalComplex.isZero_single_obj_X _ 0 K i hi)

section FiniteType

variable [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType g] [QuasiCompact g]

omit [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g]
  [QuasiCompact g] in
/-- **A module flat over `X` has Tor amplitude `[0, 0]` over `pr_1^{-1}𝒪_X`.** -/
lemma hasTorAmplitude_single_of_isFlatOver
    (hK : IsFlatOver (Limits.pullback.fst f g).toLRSHom.toShHom K) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude
      (RingedSpace.inverseImage X.toRingedSpace (Limits.pullback.fst f g).base)
      ((Scheme.Hom.derivedScalarRestriction (Limits.pullback.fst f g)).obj
        ((DerivedCategory.singleFunctor _ 0).obj K)) 0 0 :=
  hasTorAmplitude_of_flatOver_representative f g _
    ((CochainComplex.singleFunctor (Limits.pullback f g).Modules 0).obj K)
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app K).symm 0 0 inferInstance inferInstance
    (isFlatOver_single_X f g K hK)

omit [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g]
  [QuasiCompact g] in
/-- **For `𝒦` flat over `X` and `pr₁` flat, `(pr_1^*ℱ)[0] ⊗^𝐋 𝒦[0] ⟶ (pr_1^*ℱ ⊗ 𝒦)[0]` is an
isomorphism.** The source has no cohomology below degree `0` because `𝒦` has Tor amplitude
`[0, 0]` over `pr_1^{-1}𝒪_X` and `L pr_1^*(ℱ[0]) = (pr_1^*ℱ)[0]`, none above degree `0` by right
t-exactness, and in degree `0` the map is the identification `H⁰(A ⊗^𝐋 B) = A ⊗ B`. -/
theorem isIso_fourierMukaiTensorSingleNatTrans_app
    (hflat : AlgebraicGeometry.IsFlat (fourierMukaiFst f g))
    (hK : IsFlatOver (Limits.pullback.fst f g).toLRSHom.toShHom K) (A : X.Modules) :
    IsIso ((fourierMukaiTensorSingleNatTrans f g K).app
      ((modulePullback (fourierMukaiFst f g)).obj A)) := by
  set N : (Limits.pullback f g).Modules := (modulePullback (fourierMukaiFst f g)).obj A
  have hGE : ((fourierMukaiTensor f g ((DerivedCategory.singleFunctor _ 0).obj K)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)).IsGE 0 := by
    have h := isGE_fourierMukaiTensor_of_hasTorAmplitude f g _ 0 0
      (hasTorAmplitude_single_of_isFlatOver f g K hK)
      ((DerivedCategory.singleFunctor X.Modules 0).obj A) 0 inferInstance
    have h' : ((fourierMukaiTensor f g ((DerivedCategory.singleFunctor _ 0).obj K)).obj
        ((fourierMukaiPullback f g).obj ((DerivedCategory.singleFunctor X.Modules 0).obj A))).IsGE
          0 := h
    let e : (fourierMukaiTensor f g ((DerivedCategory.singleFunctor _ 0).obj K)).obj
        ((fourierMukaiPullback f g).obj ((DerivedCategory.singleFunctor X.Modules 0).obj A)) ≅
        (fourierMukaiTensor f g ((DerivedCategory.singleFunctor _ 0).obj K)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N) :=
      (fourierMukaiTensor f g _).mapIso ((fourierMukaiPullbackSingleIso f g hflat).app A)
    exact DerivedCategory.TStructure.t.isGE_of_iso e 0
  have hLE : ((fourierMukaiTensor f g ((DerivedCategory.singleFunctor _ 0).obj K)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE (0 + 0) :=
    have i₁ : ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj N).IsLE 0 :=
      inferInstance
    have i₂ : ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj K).IsLE 0 :=
      inferInstance
    @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor _ _ _
      (Limits.pullback f g).toRingedSpace.sheaf _ _ _ _ _ _ _ _ 0 0 i₁ i₂
  rw [DerivedCategory.isIso_iff]
  intro n
  dsimp only [Functor.comp_obj]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact IsZero.isIso (DerivedCategory.isZero_of_isGE _ 0 n hn)
      (DerivedCategory.isZero_of_isGE _ 0 n hn) _
  · exact Stacks.DerivedTensor.RingedSite.isIso_homologyMap_tensorSingleNatTrans_app _ _ K N
  · exact IsZero.isIso (DerivedCategory.isZero_of_isLE _ (0 + 0) n (by omega))
      (DerivedCategory.isZero_of_isLE _ 0 n hn) _

end FiniteType

end Tensor

/-! ### The derived direct image of a module without higher direct images

This section is stated in the spelling of the derived direct image of ringed spaces. -/

section Pushforward

variable {Z W : RingedSpace.{u, u}} (p : Z ⟶ W)

/-- `R p_*` commutes with the shift. -/
local instance commShift_singleKernelPushforward : (derivedPushforward p).CommShift ℤ :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift p

/-- `R p_*` is exact. -/
local instance isTriangulated_singleKernelPushforward : (derivedPushforward p).IsTriangulated :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated p

/-- **The canonical map `(p_*𝒢)[0] ⟶ R p_*(𝒢[0])`**, natural in `𝒢`. -/
def derivedPushforwardSingleUnit :
    modulePushforward p ⋙ DerivedCategory.singleFunctor _ 0 ⟶
      DerivedCategory.singleFunctor _ 0 ⋙ derivedPushforward p :=
  Stacks.DerivedFunctor.singleUnit (modulePushforward p) (derivedPushforward p)
    (derivedPushforwardUnit p)

/-- **`(p_*𝒢)[0] ≅ R p_*(𝒢[0])` when `𝒢` has no higher direct images.** -/
theorem isIso_derivedPushforwardSingleUnit_app
    (M : SheafOfModules.{u} (structureSheafRing Z))
    (hM : ∀ n : ℕ, 0 < n → IsZero (((modulePushforward p).rightDerived n).obj M)) :
    IsIso ((derivedPushforwardSingleUnit p).app M) := by
  have := modulePushforward_isRightAdjoint p
  have := SheafOfModules.isGrothendieckAbelianU.{u} (structureSheafRing Z)
  exact Stacks.DerivedFunctor.isIso_singleUnit_app _ _ _
    (fun M => Stacks.SmallDerivedCategory.isGE_obj_of_isGE _ _ (derivedPushforwardUnit p)
      (isIso_derivedPushforwardUnit_app_of_isKInjective p) _ 0 inferInstance)
    (exists_quasiIso_isKInjective _) M hM

end Pushforward

/-! ### The Fourier-Mukai functor of a module flat over `X`, on modules -/

section Assembly

variable [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType g] [QuasiCompact g]
  (K : (Limits.pullback f g).Modules)

/-- **`Φ_𝒦(ℱ[0]) ≅ pr_{2,*}(pr_1^*ℱ ⊗ 𝒦)[0]`**, naturally in `ℱ`, for `𝒦` flat over `X` and
`pr₁` flat, along any functor `E` into `Mod(𝒪_X)` whose values have integrand
`pr_1^*E(c) ⊗ 𝒦` without higher direct images along `pr₂`. -/
def fourierMukaiSingleIso (hflat : AlgebraicGeometry.IsFlat (fourierMukaiFst f g))
    (hK : IsFlatOver (Limits.pullback.fst f g).toLRSHom.toShHom K)
    {C : Type*} [Category* C] (E : C ⥤ X.Modules)
    (hE : ∀ (c : C) (n : ℕ), 0 < n → IsZero
      (((modulePushforward (Limits.pullback.snd f g).toLRSHom.toShHom).rightDerived n).obj
        ((fourierMukaiModuleTensor f g K).obj
          ((modulePullback (fourierMukaiFst f g)).obj (E.obj c))))) :
    E ⋙ DerivedCategory.singleFunctor X.Modules 0 ⋙
        fourierMukai f g ((DerivedCategory.singleFunctor _ 0).obj K) ≅
      E ⋙ modulePullback (fourierMukaiFst f g) ⋙ fourierMukaiModuleTensor f g K ⋙
        modulePushforward (Limits.pullback.snd f g).toLRSHom.toShHom ⋙
          DerivedCategory.singleFunctor Y.Modules 0 :=
  have : IsIso (Functor.whiskerLeft (E ⋙ modulePullback (fourierMukaiFst f g))
      (fourierMukaiTensorSingleNatTrans f g K)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      (fun c => isIso_fourierMukaiTensorSingleNatTrans_app f g K hflat hK (E.obj c))
  have : IsIso (Functor.whiskerLeft
      (E ⋙ modulePullback (fourierMukaiFst f g) ⋙ fourierMukaiModuleTensor f g K)
      (derivedPushforwardSingleUnit (Limits.pullback.snd f g).toLRSHom.toShHom)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      (fun c => isIso_derivedPushforwardSingleUnit_app _ _ (hE c))
  Functor.isoWhiskerLeft E (Functor.isoWhiskerRight (fourierMukaiPullbackSingleIso f g hflat)
      (fourierMukaiTensor f g ((DerivedCategory.singleFunctor _ 0).obj K) ⋙
        fourierMukaiPushforward f g)) ≪≫
    Functor.isoWhiskerRight (asIso (Functor.whiskerLeft
      (E ⋙ modulePullback (fourierMukaiFst f g)) (fourierMukaiTensorSingleNatTrans f g K)))
      (fourierMukaiPushforward f g) ≪≫
    (asIso (Functor.whiskerLeft
      (E ⋙ modulePullback (fourierMukaiFst f g) ⋙ fourierMukaiModuleTensor f g K)
      (derivedPushforwardSingleUnit (Limits.pullback.snd f g).toLRSHom.toShHom))).symm

end Assembly

/-- `- ⊗ 𝒦` in the spelling of the derived tensor product is `- ⊗ 𝒦` in the spelling of the
projection formula. -/
def fourierMukaiModuleTensorIso (K : (Limits.pullback f g).Modules) :
    fourierMukaiModuleTensor f g K ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((Limits.pullback f g).toRingedSpace).presheaf,
          ((Limits.pullback f g).toRingedSpace).IsSheaf⟩).flip.obj (K)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm)

end AlgebraicGeometry

end
