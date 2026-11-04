module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LeftAdjoint
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RightAdjoint

/-!
# The kernels of the adjoints of a Fourier-Mukai functor

Let `S` be a scheme, `f : X ⟶ S` and `g : Y ⟶ S`, and `K` a perfect object of
`D_QCoh(𝒪_{X ×_S Y})` with Fourier-Mukai functor `Φ_K`. [Stacks, Tag 0FYW] gives a right adjoint
of `Φ_K` with kernel `(Y ×_S X → X ×_S Y)^* R𝓗om(K, a(𝒪_Y))`, `a` the right adjoint of
`Rpr_{2,*}`, and [Stacks, Tag 0FYX] a left adjoint with kernel
`(Y ×_S X → X ×_S Y)^*(K^∨ ⊗ᴸ Lpr_2^*ω^•_{Y/S})`. [Stacks, Tag 0FYY] (3) and (4) name the kernels

`K' = (Y ×_S X → X ×_S Y)^*(Lpr_1^*ω^•_{X/S} ⊗ᴸ K^∨)` and
`K'' = (Y ×_S X → X ×_S Y)^*(Lpr_2^*ω^•_{Y/S} ⊗ᴸ K^∨)`

and assert that, for a Gorenstein factor, they are perfect. This file provides:

* the identification `R𝓗om(K, a(𝒪_Y)) ≅ Lpr_1^*ω^•_{X/S} ⊗ᴸ K^∨` for `f` proper, flat and of
  finite presentation (`Stacks.Duality.dualKernelIso`): `a(𝒪_Y) = Lpr_1^*ω^•_{X/S}` because the
  relative dualizing complex commutes with base change ([Stacks, Tag 0B6S]), and
  `R𝓗om(K, -) ≅ - ⊗ᴸ K^∨` for perfect `K` ([Stacks, Tag 08DQ]); this is the step of the source's
  proof of (3);
* the adjunction `Φ_K ⊣ Φ_{K'_{0FYW}}` on `D_QCoh` for a perfect `K` and `f` proper, flat and of
  finite presentation (`AlgebraicGeometry.fourierMukaiRightAdjunction`), assembled from the
  natural bijection of [Stacks, Tag 0FYW];
* the kernels `K'` and `K''` (`AlgebraicGeometry.fourierMukaiRightAdjointKernelDualizingFirst`,
  `AlgebraicGeometry.fourierMukaiLeftAdjointKernelDualizingFirst`), their identification with the
  kernels of [Stacks, Tag 0FYW] and [Stacks, Tag 0FYX], and their perfectness for a Gorenstein
  factor over a Noetherian base.

Perfectness is read off from duality: an object of `D_QCoh` with a dual is perfect
(`Stacks.Duality.isPerfect_of_exactPairing_quasiCoherent`, [Stacks, Tag 0FPD]), and
`Lσ^*(Lp^*ω ⊗ᴸ K^∨)` has one when `ω` is invertible, which `ω^•_{X/S}` is for a Gorenstein
morphism ([Stacks, Tag 0C08],
`Stacks.Duality.isInvertible_twistedInverseImage_unit_of_isGorenstein`).

## Implementation notes

As in [Stacks, Tag 0FYW] and [Stacks, Tag 0FYX], the kernels are computed at the locally small
model, where the right adjoint `a` exists, and read at the standard model of
`AlgebraicGeometry.quasiCoherentFourierMukai` along
`Stacks.Duality.StandardModel.quasiCoherentModelEquiv`.

## References

* [Stacks Project, Tag 0FYY](https://stacks.math.columbia.edu/tag/0FYY)
* [Stacks Project, Tag 0FYW](https://stacks.math.columbia.edu/tag/0FYW)
* [Stacks Project, Tag 0FYX](https://stacks.math.columbia.edu/tag/0FYX)
* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0C08](https://stacks.math.columbia.edu/tag/0C08)
* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Duality

/-- **A dualizable object of `D_QCoh(𝒪_X)` is perfect.** An exact pairing in `D_QCoh(𝒪_X)` is
carried by the monoidal inclusion into `D(𝒪_X)`, and re-seated to the monoidal structure of
[Stacks, Tag 0FPB]; there an object with a left dual is perfect ([Stacks, Tag 0FPD]). -/
theorem isPerfect_of_exactPairing_quasiCoherent {X : Scheme.{u}}
    (M N : quasiCoherentDerivedCategory X) [ExactPairing M N] :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) M.obj := by
  let := Scheme.Modules.canonicalDerivedMonoidal X
  have p₁ : ExactPairing M.obj N.obj := ExactPairing.map (ObjectProperty.ι _) M N
  have p₂ := @exactPairingOfReseat _ _ (Scheme.Modules.derivedMonoidal X) _ _
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf) M.obj N.obj p₁
  exact Stacks.Cohomology.LeftDualPerfect.isPerfect_of_exactPairing X.toRingedSpace M.obj N.obj p₂

/-- **The derived pullback of a dualizable object of `D_QCoh` is perfect**: `Lσ^*` is monoidal,
so it carries an exact pairing to an exact pairing. -/
theorem isPerfect_quasiCoherentDerivedPullback'_of_exactPairing {P P' : Scheme.{u}} (σ : P' ⟶ P)
    (A B : quasiCoherentDerivedCategory P) [ExactPairing A B] :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := P'.toRingedSpace)
      ((quasiCoherentDerivedPullback' σ).obj A).obj :=
  let := ExactPairing.map (quasiCoherentDerivedPullback' σ) A B
  isPerfect_of_exactPairing_quasiCoherent _ ((quasiCoherentDerivedPullback' σ).obj B)

/-- **`Lσ^*(Lp^*ω ⊗ᴸ K^∨)` is perfect** for an invertible `ω` and a perfect `K`: `Lp^*ω` is
dualizable, `K^∨` has `K` as a dual, and a tensor product of dualizable objects is dualizable. -/
theorem isPerfect_quasiCoherentDerivedPullback'_tensor_perfectDual {P P' Q : Scheme.{u}}
    (σ : P' ⟶ P) (p : P ⟶ Q) (ω : quasiCoherentDerivedCategory Q) (hω : IsInvertible ω)
    (K : quasiCoherentDerivedCategory P)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := P.toRingedSpace) K.obj) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := P'.toRingedSpace)
      ((quasiCoherentDerivedPullback' σ).obj
        ((quasiCoherentDerivedPullback' p).obj ω ⊗ perfectDual K hK)).obj := by
  obtain ⟨ω', ⟨e⟩⟩ := hω.exists_exactPairing
  have := ExactPairing.map (quasiCoherentDerivedPullback' p) ω ω'
  have := exactPairingPerfectDual K hK
  have : ExactPairing (perfectDual K hK) K := BraidedCategory.exactPairing_swap K _
  exact isPerfect_quasiCoherentDerivedPullback'_of_exactPairing σ _
    (K ⊗ (quasiCoherentDerivedPullback' p).obj ω')

/-- **`Lσ^*(K^∨ ⊗ᴸ Lp^*ω)` is perfect** for an invertible `ω` and a perfect `K`. -/
theorem isPerfect_quasiCoherentDerivedPullback'_perfectDual_tensor {P P' Q : Scheme.{u}}
    (σ : P' ⟶ P) (p : P ⟶ Q) (ω : quasiCoherentDerivedCategory Q) (hω : IsInvertible ω)
    (K : quasiCoherentDerivedCategory P)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := P.toRingedSpace) K.obj) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := P'.toRingedSpace)
      ((quasiCoherentDerivedPullback' σ).obj
        (perfectDual K hK ⊗ (quasiCoherentDerivedPullback' p).obj ω)).obj :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    ((ObjectProperty.ι _).mapIso ((quasiCoherentDerivedPullback' σ).mapIso (β_ _ _)))
    (isPerfect_quasiCoherentDerivedPullback'_tensor_perfectDual σ p ω hω K hK)

/-- **An object read at the standard model is perfect when it is at the locally small model.** -/
theorem isPerfect_quasiCoherentModelEquiv_inverse_obj {P : Scheme.{u}}
    (A : quasiCoherentDerivedCategory P)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := P.toRingedSpace) A.obj) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect P.toRingedSpace
      (HasDerivedCategory.standard _)
      ((StandardModel.quasiCoherentModelEquiv P).inverse.obj A).obj :=
  (isPerfect_modelEquiv_functor_obj_iff P.toRingedSpace (HasDerivedCategory.standard P.Modules)
      (Scheme.Modules.hasDerivedCategory P) _).1
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      ((ObjectProperty.ι _).mapIso ((StandardModel.quasiCoherentModelEquiv P).counitIso.app A)).symm
      hA)

section DualKernel

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace (pullback f g : Scheme.{u})] [QuasiSeparatedSpace (pullback f g : Scheme.{u})]
  [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

/-- The relative dualizing complex `ω^•_{X/S} = a_f(𝒪_S)` pulled back to `X ×_S Y` along the
first projection. -/
abbrev pulledBackDualizingComplexFst : quasiCoherentDerivedCategory (pullback f g) :=
  (quasiCoherentDerivedPullback' (pullback.fst f g)).obj
    ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj (𝟙_ _))

/-- **`a(𝒪_Y) = Lpr_1^*ω^•_{X/S}`** for `f` proper, flat and of finite presentation, `a` the right
adjoint of `Rpr_{2,*}`: the base change map of [Stacks, Tag 0AA6] at `𝒪_S`, invertible by
[Stacks, Tag 0AAB], followed by `a` of `Lg^*𝒪_S ≅ 𝒪_Y`. This is the formation of the relative
dualizing complex commuting with base change ([Stacks, Tag 0B6S]). -/
def pulledBackDualizingComplexFstIsoTwistedUnit :
    pulledBackDualizingComplexFst f g ≅ twistedUnit f g := by
  have sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
    (torIndependent_of_flat_left f g)
  haveI := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat sq
    (DerivedPushforward.derivedStructureSheaf S)
  exact eqToIso (by
      dsimp only [pulledBackDualizingComplexFst]
      rw [tensorUnit_quasiCoherentDerivedCategory]
      rfl) ≪≫
    asIso ((twistedInverseImageBaseChangeMap (pullback.fst f g) (pullback.snd f g) f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq).app
        (DerivedPushforward.derivedStructureSheaf S)) ≪≫
    (twistedInverseImage (pullback.snd f g) _).mapIso
      (eqToIso (by rw [tensorUnit_quasiCoherentDerivedCategory]) ≪≫
        (Functor.Monoidal.εIso (quasiCoherentDerivedPullback' g)).symm)

/-- **`R𝓗om(K, a(𝒪_Y)) ≅ Lpr_1^*ω^•_{X/S} ⊗ᴸ K^∨`** for a perfect `K` and `f` proper, flat and of
finite presentation: `R𝓗om(K, -)` and `- ⊗ᴸ K^∨` are both right adjoint to `- ⊗ᴸ K`
([Stacks, Tag 08J8] and [Stacks, Tag 08DQ]), and `a(𝒪_Y) = Lpr_1^*ω^•_{X/S}`
(`pulledBackDualizingComplexFstIsoTwistedUnit`). -/
def dualKernelIso (K : quasiCoherentDerivedCategory (pullback f g))
    (hpc : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (pullback f g).toRingedSpace) K.obj) :
    dualKernel f g K hpc ≅ pulledBackDualizingComplexFst f g ⊗ perfectDual K hK :=
  letI := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  letI := exactPairingDerivedDualLocallySmall K.obj hK
  ObjectProperty.isoMk _
    (((InternalHom.tensorRightSheafHomAdjunction K.obj).rightAdjointUniq
        (tensorRightAdjunction K.obj (Stacks.SheafOfModules.derivedDual (pullback f g).sheaf
          K.obj))).app (twistedUnit f g).obj ≪≫
      (MonoidalCategory.tensorRight _).mapIso ((ObjectProperty.ι _).mapIso
        (pulledBackDualizingComplexFstIsoTwistedUnit f g).symm))

end DualKernel

end Stacks.Duality

namespace AlgebraicGeometry

section RightAdjointKernel

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

/-- Perfect objects are pseudo-coherent, at the standard model. -/
theorem isPseudoCoherent_of_isPerfect_standard {Z : Scheme.{u}}
    (E : @DerivedCategory Z.Modules _ _ (HasDerivedCategory.standard _))
    (hE : @Stacks.Cohomology.PerfectComplexes.IsPerfect Z.toRingedSpace
      (HasDerivedCategory.standard _) E) :
    @RingedSpace.IsPseudoCoherent Z.toRingedSpace (HasDerivedCategory.standard _) E :=
  let : HasDerivedCategory (StrictlyPerfect.OXMod.{u, u} Z.toRingedSpace) :=
    HasDerivedCategory.standard _
  Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect E hE

/-- **The kernel `K' = (Y ×_S X → X ×_S Y)^*(Lpr_1^*ω^•_{X/S} ⊗ᴸ K^∨)` of [Stacks, Tag 0FYY] (3)
at the locally small model**, for a perfect `K`, in `D_QCoh(𝒪_{Y ×_S X})`. -/
def fourierMukaiRightAdjointKernelDualizingFirstLocallySmall
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    Stacks.Duality.quasiCoherentDerivedCategory (pullback g f) :=
  haveI : QuasiCompact f := (fourierMukaiRightAdjoint_instances f g).1
  haveI : QuasiSeparated f := (fourierMukaiRightAdjoint_instances f g).2.1
  haveI : QuasiCompact g := (fourierMukaiRightAdjoint_instances f g).2.2.1
  haveI : QuasiSeparated g := (fourierMukaiRightAdjoint_instances f g).2.2.2.1
  haveI : CompactSpace (pullback f g : Scheme.{u}) :=
    (fourierMukaiRightAdjoint_instances f g).2.2.2.2.1
  haveI : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
    (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.1
  haveI : CompactSpace (pullback g f : Scheme.{u}) :=
    (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.2.1
  haveI : QuasiSeparatedSpace (pullback g f : Scheme.{u}) :=
    (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.2.2
  (Stacks.Duality.quasiCoherentDerivedPullback' (pullbackSymmetry g f).hom).obj
    (Stacks.Duality.pulledBackDualizingComplexFst f g ⊗
      Stacks.Duality.perfectDual
        ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback f g)).functor.obj ⟨K, hK⟩)
        ((Stacks.Duality.isPerfect_modelEquiv_functor_obj_iff (pullback f g).toRingedSpace
          (HasDerivedCategory.standard (pullback f g).Modules)
          (Scheme.Modules.hasDerivedCategory (pullback f g)) K).2 hperf))

/-- **The kernel `K' = (Y ×_S X → X ×_S Y)^*(Lpr_1^*ω^•_{X/S} ⊗ᴸ K^∨)` of [Stacks, Tag 0FYY] (3)**,
at the standard model. -/
def fourierMukaiRightAdjointKernelDualizingFirst
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    @DerivedCategory (pullback g f).Modules _ _ (HasDerivedCategory.standard _) :=
  ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback g f)).inverse.obj
    (fourierMukaiRightAdjointKernelDualizingFirstLocallySmall f g K hK hperf)).obj

/-- **The kernel of [Stacks, Tag 0FYW] is the kernel of [Stacks, Tag 0FYY] (3)** for a perfect
`K` and `f` proper, flat and of finite presentation:
`R𝓗om(K, a(𝒪_Y)) ≅ Lpr_1^*ω^•_{X/S} ⊗ᴸ K^∨` (`Stacks.Duality.dualKernelIso`). -/
def fourierMukaiRightAdjointKernelIsoDualizingFirst
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    haveI : QuasiCompact f := (fourierMukaiRightAdjoint_instances f g).1
    haveI : QuasiSeparated f := (fourierMukaiRightAdjoint_instances f g).2.1
    haveI : QuasiCompact g := (fourierMukaiRightAdjoint_instances f g).2.2.1
    haveI : QuasiSeparated g := (fourierMukaiRightAdjoint_instances f g).2.2.2.1
    haveI : CompactSpace (pullback f g : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.1
    haveI : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.1
    haveI : CompactSpace (pullback g f : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.2.1
    haveI : QuasiSeparatedSpace (pullback g f : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.2.2
    @Iso (@DerivedCategory (pullback g f).Modules _ _ (HasDerivedCategory.standard _)) _
      (fourierMukaiRightAdjointKernel f g K hK (isPseudoCoherent_of_isPerfect_standard K hperf))
      (fourierMukaiRightAdjointKernelDualizingFirst f g K hK hperf) :=
  haveI : QuasiCompact f := (fourierMukaiRightAdjoint_instances f g).1
  haveI : QuasiSeparated f := (fourierMukaiRightAdjoint_instances f g).2.1
  haveI : QuasiCompact g := (fourierMukaiRightAdjoint_instances f g).2.2.1
  haveI : QuasiSeparated g := (fourierMukaiRightAdjoint_instances f g).2.2.2.1
  haveI : CompactSpace (pullback f g : Scheme.{u}) :=
    (fourierMukaiRightAdjoint_instances f g).2.2.2.2.1
  haveI : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
    (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.1
  haveI : CompactSpace (pullback g f : Scheme.{u}) :=
    (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.2.1
  haveI : QuasiSeparatedSpace (pullback g f : Scheme.{u}) :=
    (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.2.2
  (ObjectProperty.ι _).mapIso
    ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback g f)).inverse.mapIso
      ((Stacks.Duality.quasiCoherentDerivedPullback' (pullbackSymmetry g f).hom).mapIso
        (Stacks.Duality.dualKernelIso f g _ _
          ((Stacks.Duality.isPerfect_modelEquiv_functor_obj_iff (pullback f g).toRingedSpace
          (HasDerivedCategory.standard (pullback f g).Modules)
          (Scheme.Modules.hasDerivedCategory (pullback f g)) K).2 hperf))))

/-- **The right adjoint of a Fourier-Mukai functor with perfect kernel**, from
[Stacks, Tag 0FYW]: for `f : X ⟶ S` proper, flat and of finite presentation and `K` perfect, the
canonical map `Hom_X(M, Φ'(N)) ⟶ Hom_Y(Φ(M), N)` of [Stacks, Tag 0FYW] is bijective for all `M`
and `N` and natural in both, so `Φ'` is right adjoint to `Φ` on `D_QCoh`. -/
def fourierMukaiRightAdjunction
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    haveI : QuasiCompact f := (fourierMukaiRightAdjoint_instances f g).1
    haveI : QuasiSeparated f := (fourierMukaiRightAdjoint_instances f g).2.1
    haveI : QuasiCompact g := (fourierMukaiRightAdjoint_instances f g).2.2.1
    haveI : QuasiSeparated g := (fourierMukaiRightAdjoint_instances f g).2.2.2.1
    haveI : CompactSpace (pullback f g : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.1
    haveI : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.1
    haveI : CompactSpace (pullback g f : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.2.1
    haveI : QuasiSeparatedSpace (pullback g f : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.2.2
    quasiCoherentFourierMukai f g K hK ⊣
      fourierMukaiRightAdjoint f g K hK (isPseudoCoherent_of_isPerfect_standard K hperf) := by
  obtain ⟨_, _, _, _, _, _, _, _⟩ := fourierMukaiRightAdjoint_instances f g
  let hpc := isPseudoCoherent_of_isPerfect_standard K hperf
  let c := fourierMukaiRightAdjointComparison f g K hK hpc
  have hb : ∀ M N, Function.Bijective (c M N) := fun M N =>
    bijective_fourierMukaiRightAdjointComparison_of_isPerfect_of_flat f g K hK hpc hperf M N
  exact Adjunction.mkOfHomEquiv
    { homEquiv := fun M N => (Equiv.ofBijective (c M N) (hb M N)).symm
      homEquiv_naturality_left_symm := fun {M' M N} m v =>
        fourierMukaiRightAdjointComparison_naturality_left f g K hK hpc m N v
      homEquiv_naturality_right := fun {M N N'} w n =>
        (hb M N').1 ((Equiv.ofBijective_apply_symm_apply (c M N') (hb M N') (w ≫ n)).trans
          ((congrArg (· ≫ n) (Equiv.ofBijective_apply_symm_apply (c M N) (hb M N) w)).symm.trans
            (fourierMukaiRightAdjointComparison_naturality_right f g K hK hpc M n _).symm)) }

end RightAdjointKernel

section RightAdjointKernelGorenstein

variable {S X Y : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) (g : Y ⟶ S)
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [IsProper f] [Flat f]

/-- **The kernel `K'` of [Stacks, Tag 0FYY] (3) is perfect** for `f` moreover Gorenstein over a
Noetherian `S`: `ω^•_{X/S}` is invertible ([Stacks, Tag 0C08]). -/
theorem isPerfect_fourierMukaiRightAdjointKernelDualizingFirst
    (hfib : ∀ s : S, IsLocallyNoetherian (f.fiber s)) (hG : f.IsGorenstein hfib)
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback g f).toRingedSpace
      (HasDerivedCategory.standard _)
      (fourierMukaiRightAdjointKernelDualizingFirst f g K hK hperf) := by
  obtain ⟨_, _, _, _, _, _, _, _⟩ := fourierMukaiRightAdjoint_instances f g
  exact Stacks.Duality.isPerfect_quasiCoherentModelEquiv_inverse_obj _
    (Stacks.Duality.isPerfect_quasiCoherentDerivedPullback'_tensor_perfectDual _ _ _
      (Stacks.Duality.isInvertible_twistedInverseImage_unit_of_isGorenstein f hfib hG) _ _)

/-- **The kernel of [Stacks, Tag 0FYW] is perfect** for a perfect `K` and `f` proper, flat and
Gorenstein over a Noetherian `S`: it is isomorphic to `Lσ^*(Lpr_1^*ω^•_{X/S} ⊗ᴸ K^∨)`
(`Stacks.Duality.dualKernelIso`), which is perfect, `ω^•_{X/S}` being invertible. -/
theorem isPerfect_fourierMukaiRightAdjointKernel_of_isGorenstein
    (hfib : ∀ s : S, IsLocallyNoetherian (f.fiber s)) (hG : f.IsGorenstein hfib)
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    haveI : QuasiCompact f := (fourierMukaiRightAdjoint_instances f g).1
    haveI : QuasiSeparated f := (fourierMukaiRightAdjoint_instances f g).2.1
    haveI : QuasiCompact g := (fourierMukaiRightAdjoint_instances f g).2.2.1
    haveI : QuasiSeparated g := (fourierMukaiRightAdjoint_instances f g).2.2.2.1
    haveI : CompactSpace (pullback f g : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.1
    haveI : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.1
    haveI : CompactSpace (pullback g f : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.2.1
    haveI : QuasiSeparatedSpace (pullback g f : Scheme.{u}) :=
      (fourierMukaiRightAdjoint_instances f g).2.2.2.2.2.2.2
    @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback g f).toRingedSpace
      (HasDerivedCategory.standard _)
      (fourierMukaiRightAdjointKernel f g K hK
        (isPseudoCoherent_of_isPerfect_standard K hperf)) := by
  obtain ⟨_, _, _, _, _, _, _, _⟩ := fourierMukaiRightAdjoint_instances f g
  have hKL := (Stacks.Duality.isPerfect_modelEquiv_functor_obj_iff (pullback f g).toRingedSpace
    (HasDerivedCategory.standard (pullback f g).Modules)
    (Scheme.Modules.hasDerivedCategory (pullback f g)) K).2 hperf
  exact Stacks.Duality.isPerfect_quasiCoherentModelEquiv_inverse_obj _
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      ((ObjectProperty.ι _).mapIso
        ((Stacks.Duality.quasiCoherentDerivedPullback' (pullbackSymmetry g f).hom).mapIso
          (Stacks.Duality.dualKernelIso f g _ _ hKL))).symm
      (Stacks.Duality.isPerfect_quasiCoherentDerivedPullback'_tensor_perfectDual _ _ _
        (Stacks.Duality.isInvertible_twistedInverseImage_unit_of_isGorenstein f hfib hG) _ hKL))

end RightAdjointKernelGorenstein

section LeftAdjointKernel

variable {S X Y : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) (g : Y ⟶ S)
  [LocallyOfFiniteType f] [QuasiCompact f] [IsProper g] [Flat g]

/-- **The kernel `K'` of [Stacks, Tag 0FYX] is perfect**, `ω^•_{Y/S}` being invertible for a
Gorenstein `g` ([Stacks, Tag 0C08]). -/
theorem isPerfect_fourierMukaiLeftAdjointKernel
    (hfib : ∀ s : S, IsLocallyNoetherian (g.fiber s)) (hG : g.IsGorenstein hfib)
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback g f).toRingedSpace
      (HasDerivedCategory.standard _) (fourierMukaiLeftAdjointKernel f g K hK hperf) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := fourierMukaiLeftAdjoint_instances f g
  exact Stacks.Duality.isPerfect_quasiCoherentModelEquiv_inverse_obj _
    (Stacks.Duality.isPerfect_quasiCoherentDerivedPullback'_perfectDual_tensor _ _ _
      (Stacks.Duality.isInvertible_twistedInverseImage_unit_of_isGorenstein g hfib hG) _ _)

/-- **The kernel `K'' = (Y ×_S X → X ×_S Y)^*(Lpr_2^*ω^•_{Y/S} ⊗ᴸ K^∨)` of
[Stacks, Tag 0FYY] (4)**, at the standard model: the kernel `fourierMukaiLeftAdjointKernel` of
[Stacks, Tag 0FYX] with its two tensor factors in the order of [Stacks, Tag 0FYY]. -/
def fourierMukaiLeftAdjointKernelDualizingFirst
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    @DerivedCategory (pullback g f).Modules _ _ (HasDerivedCategory.standard _) :=
  haveI : QuasiSeparatedSpace S := (fourierMukaiLeftAdjoint_instances f g).1
  haveI : CompactSpace X := (fourierMukaiLeftAdjoint_instances f g).2.1
  haveI : QuasiSeparatedSpace X := (fourierMukaiLeftAdjoint_instances f g).2.2.1
  haveI : QuasiSeparated f := (fourierMukaiLeftAdjoint_instances f g).2.2.2.1
  haveI : CompactSpace Y := (fourierMukaiLeftAdjoint_instances f g).2.2.2.2.1
  haveI : QuasiSeparatedSpace Y := (fourierMukaiLeftAdjoint_instances f g).2.2.2.2.2.1
  haveI : LocallyOfFinitePresentation g := (fourierMukaiLeftAdjoint_instances f g).2.2.2.2.2.2.1
  haveI : CompactSpace (pullback f g : Scheme.{u}) :=
    (fourierMukaiLeftAdjoint_instances f g).2.2.2.2.2.2.2.1
  haveI : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
    (fourierMukaiLeftAdjoint_instances f g).2.2.2.2.2.2.2.2.1
  ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback g f)).inverse.obj
    ((Stacks.Duality.quasiCoherentDerivedPullback' (pullbackSymmetry g f).hom).obj
      (Stacks.Duality.pulledBackDualizingComplex f g ⊗
        Stacks.Duality.perfectDual
          ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback f g)).functor.obj
            ⟨K, hK⟩)
          ((Stacks.Duality.isPerfect_modelEquiv_functor_obj_iff (pullback f g).toRingedSpace
            (HasDerivedCategory.standard (pullback f g).Modules)
            (Scheme.Modules.hasDerivedCategory (pullback f g)) K).2 hperf)))).obj

/-- The two orders of the tensor factors of the kernel of [Stacks, Tag 0FYX] give isomorphic
kernels, by the symmetry of the derived tensor product. -/
def fourierMukaiLeftAdjointKernelIsoDualizingFirst
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    @Iso (@DerivedCategory (pullback g f).Modules _ _ (HasDerivedCategory.standard _)) _
      (fourierMukaiLeftAdjointKernel f g K hK hperf)
      (fourierMukaiLeftAdjointKernelDualizingFirst f g K hK hperf) :=
  haveI : QuasiSeparatedSpace S := (fourierMukaiLeftAdjoint_instances f g).1
  haveI : CompactSpace X := (fourierMukaiLeftAdjoint_instances f g).2.1
  haveI : QuasiSeparatedSpace X := (fourierMukaiLeftAdjoint_instances f g).2.2.1
  haveI : QuasiSeparated f := (fourierMukaiLeftAdjoint_instances f g).2.2.2.1
  haveI : CompactSpace Y := (fourierMukaiLeftAdjoint_instances f g).2.2.2.2.1
  haveI : QuasiSeparatedSpace Y := (fourierMukaiLeftAdjoint_instances f g).2.2.2.2.2.1
  haveI : LocallyOfFinitePresentation g := (fourierMukaiLeftAdjoint_instances f g).2.2.2.2.2.2.1
  haveI : CompactSpace (pullback f g : Scheme.{u}) :=
    (fourierMukaiLeftAdjoint_instances f g).2.2.2.2.2.2.2.1
  haveI : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
    (fourierMukaiLeftAdjoint_instances f g).2.2.2.2.2.2.2.2.1
  (ObjectProperty.ι _).mapIso
    ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback g f)).inverse.mapIso
      ((Stacks.Duality.quasiCoherentDerivedPullback' (pullbackSymmetry g f).hom).mapIso
        (β_ _ _)))

/-- **The kernel `K''` of [Stacks, Tag 0FYY] (4) is perfect** for a Gorenstein `g`. -/
theorem isPerfect_fourierMukaiLeftAdjointKernelDualizingFirst
    (hfib : ∀ s : S, IsLocallyNoetherian (g.fiber s)) (hG : g.IsGorenstein hfib)
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback g f).toRingedSpace
      (HasDerivedCategory.standard _)
      (fourierMukaiLeftAdjointKernelDualizingFirst f g K hK hperf) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := fourierMukaiLeftAdjoint_instances f g
  exact Stacks.Duality.isPerfect_quasiCoherentModelEquiv_inverse_obj _
    (Stacks.Duality.isPerfect_quasiCoherentDerivedPullback'_tensor_perfectDual _ _ _
      (Stacks.Duality.isInvertible_twistedInverseImage_unit_of_isGorenstein g hfib hG) _ _)

end LeftAdjointKernel

end AlgebraicGeometry

end
