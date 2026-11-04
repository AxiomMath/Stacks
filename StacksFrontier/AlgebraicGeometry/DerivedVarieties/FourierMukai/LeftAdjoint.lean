module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LocallySmallModel
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.ProperDualizingInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentCompactDualizable
import StacksCore.Tactic.StacksAttribute

/-!
# The left adjoint of a Fourier-Mukai transform

Let `S` be a Noetherian scheme, let `g : Y ⟶ S` be flat, proper and Gorenstein, and let
`f : X ⟶ S` be of finite type. Let `ω^•_{Y/S}` be the relative dualizing complex of `Y` over `S`,
let `K` be a perfect object of `D_QCoh(𝒪_{X ×_S Y})` with Fourier-Mukai transform
`Φ : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, put

`K' = (Y ×_S X → X ×_S Y)^*(K^∨ ⊗ᴸ Lpr_2^*ω^•_{Y/S})  ∈ D_QCoh(𝒪_{Y ×_S X})`

and let `Φ' : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` be the Fourier-Mukai transform with kernel `K'`. Then
there is a canonical isomorphism `Hom_Y(N, Φ(M)) ≅ Hom_X(Φ'(N), M)`, functorial in `M` and `N`:
`Φ'` is left adjoint to `Φ`. This is [Stacks, Tag 0FYX].

## The proof

It is the content of the source's argument, read directly rather than through the right-adjoint
statement [Stacks, Tag 0FYW] with the roles of `X` and `Y` exchanged. Write `p, q` for the two
projections of `P = X ×_S Y` and `a_p` for the right adjoint of `Rp_*`. Then

* `a_p(M) ≅ Lp^*M ⊗ᴸ Lq^*ω^•_{Y/S}` (`Stacks.Duality.twistedInverseImageFstIso`): `p` is a base
  change of `g`, so it is proper, flat and of finite presentation and `a_p(M) ≅ Lp^*M ⊗ a_p(𝒪_X)`
  ([Stacks, Tag 0E4K]), and formation of the relative dualizing complex commutes with base change
  ([Stacks, Tag 0B6S], i.e. [Stacks, Tag 0AAB]);
* `ω^•_{Y/S}` is invertible ([Stacks, Tag 0C08]), hence so is `W = Lq^*ω^•_{Y/S}`
  (`Stacks.Duality.isInvertible_twistedInverseImage_unit_of_isGorenstein`);
* `K` is perfect, so `- ⊗ K^∨` is left adjoint to `- ⊗ K`.

Composing `Lq^* ⊣ Rq_*`, `- ⊗ K^∨ ⊣ - ⊗ K`, `- ⊗ W ⊣ - ⊗ W⁻¹` and `Rp_* ⊣ a_p` gives
`Rp_*(Lq^*(-) ⊗ K^∨ ⊗ W) ⊣ Rq_*(Lp^*(-) ⊗ K)`
(`Stacks.Duality.fourierMukaiLeftAdjunctionLocallySmall`),
and the left adjoint is the Fourier-Mukai transform of `K'` read on `X ×_S Y`
(`Stacks.Duality.fourierMukaiLocallySmallSymmetryIso`).

## The two models of the derived category

`Φ` and `Φ'` are the library's Fourier-Mukai functors
`AlgebraicGeometry.quasiCoherentFourierMukai`, built at the standard model
`HasDerivedCategory.standard`; the right adjoint `a_p` exists at the locally small model. The
adjunction is proved at the locally small model and carried to the standard one along the
comparison `Stacks.Duality.StandardModel.quasiCoherentModelEquiv`, with which the Fourier-Mukai
functors commute (`AlgebraicGeometry.quasiCoherentFourierMukaiModelEquivIso`).
Accordingly the kernel `K'` is computed at the locally small model — its derived dual, derived
tensor product and derived pullbacks are those of `D_QCoh` there — and read at the standard model
along the same comparison (`AlgebraicGeometry.fourierMukaiLeftAdjointKernel`).

## Main definitions

* `AlgebraicGeometry.fourierMukaiLeftAdjointKernel` — the kernel `K'`.
* `AlgebraicGeometry.fourierMukaiLeftAdjunction` — **[Stacks, Tag 0FYX]**, the adjunction
  `Φ' ⊣ Φ`.

## References

* [Stacks Project, Tag 0FYX](https://stacks.math.columbia.edu/tag/0FYX)
* [Stacks Project, Tag 0FYW](https://stacks.math.columbia.edu/tag/0FYW)
* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
* [Stacks Project, Tag 0C08](https://stacks.math.columbia.edu/tag/0C08)
* [Stacks Project, Tag 0E4K](https://stacks.math.columbia.edu/tag/0E4K)
* [Stacks Project, Tag 0AAB](https://stacks.math.columbia.edu/tag/0AAB)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) (g : Y ⟶ S)
  [LocallyOfFiniteType f] [QuasiCompact f] [IsProper g] [Flat g]

/-- The finiteness properties of the schemes and morphisms of [Stacks, Tag 0FYX] that follow from
its hypotheses. -/
theorem fourierMukaiLeftAdjoint_instances :
    QuasiSeparatedSpace S ∧ CompactSpace X ∧ QuasiSeparatedSpace X ∧ QuasiSeparated f ∧
      CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ LocallyOfFinitePresentation g ∧
      CompactSpace (pullback f g : Scheme.{u}) ∧ QuasiSeparatedSpace (pullback f g : Scheme.{u}) ∧
      CompactSpace (pullback g f : Scheme.{u}) ∧
      QuasiSeparatedSpace (pullback g f : Scheme.{u}) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace X := inferInstance
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  have : LocallyOfFinitePresentation g := inferInstance
  have : CompactSpace (pullback f g : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f g)
  have : CompactSpace (pullback g f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd g f)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance,
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst f g), inferInstance,
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd g f)⟩

/-- **The kernel `K'` at the locally small model**: `σ^*(K^∨ ⊗ᴸ Lq^*ω^•_{Y/S})` in
`D_QCoh(𝒪_{Y ×_S X})`, where `σ : Y ×_S X ⟶ X ×_S Y` exchanges the factors, `q` is the second
projection of `X ×_S Y`, `K^∨ = R𝓗om(K, 𝒪)` is the derived dual and `ω^•_{Y/S} = a_g(𝒪_S)`. -/
def fourierMukaiLeftAdjointKernelLocallySmall
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    Stacks.Duality.quasiCoherentDerivedCategory (pullback g f) :=
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
  (Stacks.Duality.quasiCoherentDerivedPullback' (pullbackSymmetry g f).hom).obj
    (Stacks.Duality.perfectDual
      ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback f g)).functor.obj ⟨K, hK⟩)
      ((Stacks.Duality.isPerfect_modelEquiv_functor_obj_iff (pullback f g).toRingedSpace
        (HasDerivedCategory.standard (pullback f g).Modules)
        (Scheme.Modules.hasDerivedCategory (pullback f g)) K).2 hperf) ⊗
      Stacks.Duality.pulledBackDualizingComplex f g)

/-- **The kernel `K' = (Y ×_S X → X ×_S Y)^*(K^∨ ⊗ᴸ Lpr_2^*ω^•_{Y/S})` of [Stacks, Tag 0FYX]**, an
object of `D(𝒪_{Y ×_S X})` at the standard model. It is
`AlgebraicGeometry.fourierMukaiLeftAdjointKernelLocallySmall` read along the comparison of the two
models of `D_QCoh(𝒪_{Y ×_S X})`. -/
def fourierMukaiLeftAdjointKernel
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    @DerivedCategory (pullback g f).Modules _ _ (HasDerivedCategory.standard _) :=
  ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback g f)).inverse.obj
    (fourierMukaiLeftAdjointKernelLocallySmall f g K hK hperf)).obj

/-- The kernel `K'` lies in `D_QCoh(𝒪_{Y ×_S X})`. -/
theorem isQuasicoherent_homology_fourierMukaiLeftAdjointKernel
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) (j : ℤ) :
    ((@DerivedCategory.homologyFunctor (pullback g f).Modules _ _
      (HasDerivedCategory.standard _) j).obj
        (fourierMukaiLeftAdjointKernel f g K hK hperf)).IsQuasicoherent :=
  ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback g f)).inverse.obj
    (fourierMukaiLeftAdjointKernelLocallySmall f g K hK hperf)).property j

/-- **[Stacks, Tag 0FYX].** Let `S` be a Noetherian scheme, `g : Y ⟶ S` a flat proper Gorenstein
morphism and `f : X ⟶ S` a morphism of finite type. Let `K` be a perfect object of
`D_QCoh(𝒪_{X ×_S Y})`, `Φ : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` its Fourier-Mukai transform, and `Φ'`
the Fourier-Mukai transform `D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` of
`K' = (Y ×_S X → X ×_S Y)^*(K^∨ ⊗ᴸ Lpr_2^*ω^•_{Y/S})`
(`AlgebraicGeometry.fourierMukaiLeftAdjointKernel`). Then `Φ'` is left adjoint to `Φ`: there is a
canonical bijection `Hom_Y(N, Φ(M)) ≃ Hom_X(Φ'(N), M)`, natural in `M ∈ D_QCoh(𝒪_X)` and
`N ∈ D_QCoh(𝒪_Y)` (`CategoryTheory.Adjunction.homEquiv`).

The hypothesis `hfib`, that the fibres of `g` are locally Noetherian, is part of the definition
`AlgebraicGeometry.Scheme.Hom.IsGorenstein` of a Gorenstein morphism; it holds for every `g` of
finite type. The quasi-separatedness of `f`, which the Fourier-Mukai transform `Φ` asks for, is a
consequence of the hypotheses (`AlgebraicGeometry.fourierMukaiLeftAdjoint_instances`). -/
@[stacks 0FYX]
def fourierMukaiLeftAdjunction (hfib : ∀ s : S, IsLocallyNoetherian (g.fiber s))
    (hG : g.IsGorenstein hfib)
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) :
    haveI : QuasiSeparated f := (fourierMukaiLeftAdjoint_instances f g).2.2.2.1
    quasiCoherentFourierMukai g f (fourierMukaiLeftAdjointKernel f g K hK hperf)
        (isQuasicoherent_homology_fourierMukaiLeftAdjointKernel f g K hK hperf) ⊣
      quasiCoherentFourierMukai f g K hK := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := fourierMukaiLeftAdjoint_instances f g
  let eX := Stacks.Duality.StandardModel.quasiCoherentModelEquiv X
  let eY := Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y
  let eP' := Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback g f)
  let KL := (Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback f g)).functor.obj
    ⟨K, hK⟩
  have hKL : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (pullback f g).toRingedSpace)
      KL.obj :=
    (Stacks.Duality.isPerfect_modelEquiv_functor_obj_iff (pullback f g).toRingedSpace
      (HasDerivedCategory.standard (pullback f g).Modules)
      (Scheme.Modules.hasDerivedCategory (pullback f g)) K).2 hperf
  let A := Stacks.Duality.perfectDual KL hKL ⊗ Stacks.Duality.pulledBackDualizingComplex f g
  have hω := Stacks.Duality.isInvertible_twistedInverseImage_unit_of_isGorenstein g hfib hG
  let adjL := Stacks.Duality.fourierMukaiLeftAdjunctionLocallySmall f g hω KL hKL
  -- the transported kernel of `Φ'` is `K'` again
  let c : eP'.functor.obj (eP'.inverse.obj
        (fourierMukaiLeftAdjointKernelLocallySmall f g K hK hperf)) ≅
      (Stacks.Duality.quasiCoherentDerivedPullback' (pullbackSymmetry g f).hom).obj A :=
    eP'.counitIso.app _
  let isoΦ := quasiCoherentFourierMukaiModelEquivIso f g K hK
  let isoΨ := quasiCoherentFourierMukaiModelEquivIso g f
      (fourierMukaiLeftAdjointKernel f g K hK hperf)
      (isQuasicoherent_homology_fourierMukaiLeftAdjointKernel f g K hK hperf) ≪≫
    Functor.isoWhiskerLeft eY.functor
      (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
          ((tensoringRight _).mapIso c) _) ≪≫
        Stacks.Duality.fourierMukaiLocallySmallSymmetryIso f g A)
  exact (eY.toAdjunction.comp (adjL.comp eX.symm.toAdjunction)).ofNatIsoLeft
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight isoΨ.symm eX.inverse ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eX.unitIso.symm ≪≫
        Functor.rightUnitor _) |>.ofNatIsoRight
    (Functor.isoWhiskerRight isoΦ.symm eY.inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ eY.unitIso.symm ≪≫ Functor.rightUnitor _)

end AlgebraicGeometry

end
