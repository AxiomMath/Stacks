module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.AdjointKernels
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.CompositionIso
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ConvolutionPerfectGeneral
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.PerfectPreservationCriteria
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# Fourier-Mukai functors between perfect derived categories

Let `S` be a Noetherian scheme and let `X`, `Y`, `Z` be proper and flat over `S`. This file
proves [Stacks, Tag 0FYY]:

1. a perfect `K` on `X ×_S Y` gives a Fourier-Mukai functor
   `Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`;
2. for perfect `K` on `X ×_S Y` and `K'` on `Y ×_S Z`, the composite `Φ_{K'} ∘ Φ_K` is
   `Φ_{K''}` for the convolution `K'' = R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K')` of
   [Stacks, Tag 0FYS], which is perfect;
3. if `X ⟶ S` is Gorenstein, `Φ_{K'} : D_perf(𝒪_Y) ⥤ D_perf(𝒪_X)` is right adjoint to `Φ_K`, for
   `K'` the pullback of `Lpr_1^*ω^•_{X/S} ⊗^𝐋 K^∨` along `Y ×_S X ⟶ X ×_S Y`;
4. if `Y ⟶ S` is Gorenstein, `Φ_{K''} : D_perf(𝒪_Y) ⥤ D_perf(𝒪_X)` is left adjoint to `Φ_K`, for
   `K''` the pullback of `Lpr_2^*ω^•_{Y/S} ⊗^𝐋 K^∨` along `Y ×_S X ⟶ X ×_S Y`.

## Main definitions

* `AlgebraicGeometry.perfectFourierMukaiOfProperFlat` — **[Stacks, Tag 0FYY] (1)**, the functor
  `Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` of a perfect kernel.
* `AlgebraicGeometry.perfectFourierMukaiOfProperFlatComp` — **[Stacks, Tag 0FYY] (2)**, the
  natural isomorphism `Φ_{K'} ∘ Φ_K ≅ Φ_{K''}` of functors `D_perf(𝒪_X) ⥤ D_perf(𝒪_Z)`.
* `AlgebraicGeometry.perfectFourierMukaiOfProperFlatRightAdjunction` —
  **[Stacks, Tag 0FYY] (3)**, `Φ_K ⊣ Φ_{K'}`.
* `AlgebraicGeometry.perfectFourierMukaiOfProperFlatLeftAdjunction` —
  **[Stacks, Tag 0FYY] (4)**, `Φ_{K''} ⊣ Φ_K`.

## Implementation notes

*Hypotheses of (1) and (2).* `Φ_K` carries perfect objects to perfect objects as soon as
`f : X ⟶ S` is flat, proper and of finite presentation
(`AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation`,
[Stacks, Tag 0FYT] part (3), of which part (4), the route of the source's proof, is the case of a
Noetherian `S`). Over a Noetherian `S` a proper `f` is of finite presentation, so the source's
hypotheses imply this. For the composition the middle factor `g : Y ⟶ S` is flat, proper and of
finite presentation (perfectness of the convolution by [Stacks, Tag 0B91] (1), as in the source's
proof via [Stacks, Tag 0B6F], and flatness of `g` for [Stacks, Tag 0FYS]), `X` is flat over `S`
(so `X` and `Z` are Tor independent over `S`, the remaining hypothesis of [Stacks, Tag 0FYS]), and
`h : Z ⟶ S` is quasi-compact and quasi-separated. (3) and (4) are stated at the source's
hypotheses.

*The kernel.* A perfect kernel is taken as an object of the full subcategory
`D_perf(𝒪_{X ×_S Y})`, i.e. a complex together with the proof that it is perfect.

*Equality of functors.* The source writes (2) as an equality; both sides are built from derived
functors, determined up to unique isomorphism, so the faithful rendering is a natural isomorphism.
It is the natural isomorphism of [Stacks, Tag 0FYS] on `D_QCoh`
(`AlgebraicGeometry.quasiCoherentFourierMukaiCompNatIso`) read on perfect objects, which have
quasi-coherent cohomology sheaves.

*The adjunctions.* (3) is the source's argument: [Stacks, Tag 0FYW] gives the right adjoint on
`D_QCoh` with kernel `(Y ×_S X → X ×_S Y)^* R𝓗om(K, a(𝒪_Y))`
(`AlgebraicGeometry.fourierMukaiRightAdjunction`), and that kernel is
`(Y ×_S X → X ×_S Y)^*(Lpr_1^*ω^•_{X/S} ⊗^𝐋 K^∨)` (`Stacks.Duality.dualKernelIso`, by
[Stacks, Tag 0B6S] and [Stacks, Tag 08DQ]), which is perfect because `ω^•_{X/S}` is invertible
for a Gorenstein `X ⟶ S` ([Stacks, Tag 0C08]). (4) is the same with [Stacks, Tag 0FYX]
(`AlgebraicGeometry.fourierMukaiLeftAdjunction`), whose kernel has its two tensor factors in the
other order (`AlgebraicGeometry.fourierMukaiLeftAdjointKernelIsoDualizingFirst`). Both adjunctions
on `D_QCoh` restrict to `D_perf` (`AlgebraicGeometry.perfectFourierMukaiOfProperFlatAdjunction`).
The relative dualizing complex `ω^•_{X/S}` is `a_f(𝒪_S)`, `a_f` the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` ([Stacks, Tag 0A9E]), as in the source's proof
([Stacks, Tag 0A9Y], [Stacks, Tag 0B6S]).

## References

* [Stacks Project, Tag 0FYY](https://stacks.math.columbia.edu/tag/0FYY)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0FYT](https://stacks.math.columbia.edu/tag/0FYT)
* [Stacks Project, Tag 0FYW](https://stacks.math.columbia.edu/tag/0FYW)
* [Stacks Project, Tag 0FYX](https://stacks.math.columbia.edu/tag/0FYX)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- **[Stacks, Tag 0FYY] (1).** For `f : X ⟶ S` flat, proper and of finite presentation and `K`
a perfect object of `D(𝒪_{X ×_S Y})`, the Fourier-Mukai functor `Φ_K` restricts to a functor
`Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`.

This holds when `S` is Noetherian and `X`, `Y` are proper and flat over `S`, the source's
situation: a proper morphism to a Noetherian scheme is of finite presentation. -/
@[stacks 0FYY "(1): the Fourier-Mukai functor D_perf(O_X) -> D_perf(O_Y) of a perfect kernel, for \
  X flat, proper and of finite presentation over S, which the source's S Noetherian and X, Y \
  proper flat over S imply"]
def perfectFourierMukaiOfProperFlat [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (K : PerfectDerivedCategory (pullback f g)) :
    PerfectDerivedCategory X ⥤ PerfectDerivedCategory Y :=
  fourierMukaiOn f g K.obj _ _ fun E =>
    isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation f g K.obj K.property
      E.obj E.property

/-- The functor `Φ_K` on perfect complexes is `Φ_K` on underlying objects. -/
theorem perfectFourierMukaiOfProperFlat_obj_obj [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f] (K : PerfectDerivedCategory (pullback f g))
    (E : PerfectDerivedCategory X) :
    ((perfectFourierMukaiOfProperFlat f g K).obj E).obj = (fourierMukai f g K.obj).obj E.obj :=
  rfl

/-- **[Stacks, Tag 0FYY] (2).** Let `f : X ⟶ S` and `g : Y ⟶ S` be flat, proper and of finite
presentation and let `h : Z ⟶ S` be quasi-compact and quasi-separated. For perfect `K` on
`X ×_S Y` and `K'` on `Y ×_S Z`, the composite `Φ_{K'} ∘ Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Z)` is
`Φ_{K''}`, where `K'' = R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K')` is the convolution of
[Stacks, Tag 0FYS], perfect on `X ×_S Z` (`isPerfect_fourierMukaiConvolution_triple`).

The source's equality of functors is rendered as a natural isomorphism; it is the one of
[Stacks, Tag 0FYS], `quasiCoherentFourierMukaiCompNatIso`, on perfect objects. The hypotheses hold
when `S` is Noetherian and `X`, `Y`, `Z` are proper and flat over `S`. -/
@[stacks 0FYY "(2): Phi_{K'} o Phi_K = Phi_{K''} on D_perf with K'' the convolution of Lemma 0FYS, \
  as a natural isomorphism; for X, Y flat, proper and of finite presentation over S and Z \
  quasi-compact quasi-separated over S, which the source's S Noetherian and X, Y, Z proper flat \
  over S imply", no_expose]
def perfectFourierMukaiOfProperFlatComp [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [Flat g] [IsProper g] [LocallyOfFinitePresentation g] [QuasiCompact h] [QuasiSeparated h]
    (K : PerfectDerivedCategory (pullback f g)) (K' : PerfectDerivedCategory (pullback g h)) :
    perfectFourierMukaiOfProperFlat f g K ⋙ perfectFourierMukaiOfProperFlat g h K' ≅
      perfectFourierMukaiOfProperFlat f h
        ⟨fourierMukaiConvolution f g h K.obj K'.obj,
          isPerfect_fourierMukaiConvolution_triple f g h K.property K'.property⟩ :=
  let qc := fun {W : Scheme.{u}} (E : PerfectDerivedCategory W) =>
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect W E.obj E.property
  let e := quasiCoherentFourierMukaiCompNatIso f g h (torIndependent_of_flat_left f h) (qc K)
    (qc K')
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((ObjectProperty.ι _).mapIso (e.app ⟨M.obj, qc M⟩)))
    (fun {M N} v => ObjectProperty.hom_ext _
      ((ObjectProperty.ι _).congr_map (e.hom.naturality (X := ⟨M.obj, qc M⟩)
        (Y := ⟨N.obj, qc N⟩) (ObjectProperty.homMk v.hom))))

/-- **Isomorphic kernels give isomorphic Fourier-Mukai functors on `D_perf`**: `Φ_K` depends on `K`
only through the functor `- ⊗^𝐋 K`, which is functorial in `K`. -/
def perfectFourierMukaiOfProperFlatCongr [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    {K K' : PerfectDerivedCategory (pullback f g)} (e : K.obj ≅ K'.obj) :
    perfectFourierMukaiOfProperFlat f g K ≅ perfectFourierMukaiOfProperFlat f g K' :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((fourierMukaiPushforward f g).mapIso
      (((@Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor _ _ _
        (pullback f g).sheaf _ _ (HasDerivedCategory.standard _) _ _ _).flip.mapIso e).app
        ((fourierMukaiPullback f g).obj M.obj))))
    (fun {M N} v => ObjectProperty.hom_ext _ (by
      change (fourierMukaiPushforward f g).map _ ≫ (fourierMukaiPushforward f g).map _ =
        (fourierMukaiPushforward f g).map _ ≫ (fourierMukaiPushforward f g).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact ((@Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor _ _ _
        (pullback f g).sheaf _ _ (HasDerivedCategory.standard _) _ _ _).flip.map e.hom).naturality
        ((fourierMukaiPullback f g).map v.hom)))

/-- Perfect objects have quasi-coherent cohomology sheaves, so `D_perf(𝒪_X)` sits inside
`D_QCoh(𝒪_X)`. -/
abbrev perfectToQuasicoherent (X : Scheme.{u}) :
    PerfectDerivedCategory X ⥤ QuasicoherentDerivedCategory X :=
  ObjectProperty.ιOfLE fun E hE =>
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect X E hE

/-- **An adjunction on `D_QCoh` restricts to `D_perf`.** If the Fourier-Mukai functors of a
perfect `K` on `X ×_S Y` and a perfect `K'` on `Y ×_S X` are adjoint on the quasi-coherent derived
categories, they are adjoint on the perfect ones. -/
def perfectFourierMukaiOfProperFlatAdjunction [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f] [Flat g] [IsProper g] [LocallyOfFinitePresentation g]
    (K : PerfectDerivedCategory (pullback f g)) (K' : PerfectDerivedCategory (pullback g f))
    (adj : quasiCoherentFourierMukai f g K.obj
        (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K.obj K.property) ⊣
      quasiCoherentFourierMukai g f K'.obj
        (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K'.obj K'.property)) :
    perfectFourierMukaiOfProperFlat f g K ⊣ perfectFourierMukaiOfProperFlat g f K' :=
  adj.restrictFullyFaithful (iC := perfectToQuasicoherent X) (iD := perfectToQuasicoherent Y)
    (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _)
    (Iso.refl _) (Iso.refl _)

section Adjoints

variable [IsNoetherian S] [IsProper f] [Flat f] [IsProper g] [Flat g]

/-- **[Stacks, Tag 0FYY] (3).** Let `S` be Noetherian, let `X` and `Y` be proper and flat over
`S`, let `X ⟶ S` be Gorenstein, and let `K` be a perfect object of `D(𝒪_{X ×_S Y})`. Then
`Φ_{K'} : D_perf(𝒪_Y) ⥤ D_perf(𝒪_X)` is right adjoint to `Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`, where
`K'`, an object of `D_perf(𝒪_{Y ×_S X})`, is the pullback of `Lpr_1^*ω^•_{X/S} ⊗^𝐋 K^∨` by
`Y ×_S X ⟶ X ×_S Y` (`AlgebraicGeometry.fourierMukaiRightAdjointKernelDualizingFirst`, perfect by
`AlgebraicGeometry.isPerfect_fourierMukaiRightAdjointKernelDualizingFirst`).

Gorensteinness `AlgebraicGeometry.Scheme.Hom.IsGorenstein` is stated for a morphism with locally
Noetherian fibres; the fibres of `f`, a morphism of finite type, are locally Noetherian, and `hG`
is read at that proof. The `haveI` lines of the statement record that `X` and `Y` are
quasi-compact and quasi-separated, which the kernel's construction asks for and the hypotheses
imply. -/
@[stacks 0FYY "(3): for X -> S Gorenstein, Phi_{K'} : D_perf(O_Y) -> D_perf(O_X) is right adjoint \
  to Phi_K, K' the pullback of Lpr_1^* omega_{X/S} (x)^L K^dual by Y x_S X -> X x_S Y"]
def perfectFourierMukaiOfProperFlatRightAdjunction
    (hG : f.IsGorenstein fun s =>
      LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s))
    (K : PerfectDerivedCategory (pullback f g)) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
    perfectFourierMukaiOfProperFlat f g K ⊣ perfectFourierMukaiOfProperFlat g f
      ⟨fourierMukaiRightAdjointKernelDualizingFirst f g K.obj
          (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K.obj K.property)
          K.property,
        isPerfect_fourierMukaiRightAdjointKernelDualizingFirst f g _ hG K.obj
          (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K.obj K.property)
          K.property⟩ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  obtain ⟨_, _, _, _, _, _, _, _⟩ := fourierMukaiRightAdjoint_instances f g
  have hK := PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K.obj K.property
  exact (perfectFourierMukaiOfProperFlatAdjunction f g K
    ⟨_, isPerfect_fourierMukaiRightAdjointKernel_of_isGorenstein f g _ hG K.obj hK K.property⟩
    (fourierMukaiRightAdjunction f g K.obj hK K.property)).ofNatIsoRight
    (perfectFourierMukaiOfProperFlatCongr g f
      (fourierMukaiRightAdjointKernelIsoDualizingFirst f g K.obj hK K.property))

/-- **[Stacks, Tag 0FYY] (4).** Let `S` be Noetherian, let `X` and `Y` be proper and flat over
`S`, let `Y ⟶ S` be Gorenstein, and let `K` be a perfect object of `D(𝒪_{X ×_S Y})`. Then
`Φ_{K''} : D_perf(𝒪_Y) ⥤ D_perf(𝒪_X)` is left adjoint to `Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`, where
`K''`, an object of `D_perf(𝒪_{Y ×_S X})`, is the pullback of `Lpr_2^*ω^•_{Y/S} ⊗^𝐋 K^∨` by
`Y ×_S X ⟶ X ×_S Y` (`AlgebraicGeometry.fourierMukaiLeftAdjointKernelDualizingFirst`, perfect by
`AlgebraicGeometry.isPerfect_fourierMukaiLeftAdjointKernelDualizingFirst`).

Gorensteinness `AlgebraicGeometry.Scheme.Hom.IsGorenstein` is stated for a morphism with locally
Noetherian fibres; the fibres of `g`, a morphism of finite type, are locally Noetherian, and `hG`
is read at that proof. -/
@[stacks 0FYY "(4): for Y -> S Gorenstein, Phi_{K''} : D_perf(O_Y) -> D_perf(O_X) is left adjoint \
  to Phi_K, K'' the pullback of Lpr_2^* omega_{Y/S} (x)^L K^dual by Y x_S X -> X x_S Y"]
def perfectFourierMukaiOfProperFlatLeftAdjunction
    (hG : g.IsGorenstein fun s =>
      LocallyOfFiniteType.isLocallyNoetherian (g.fiberToSpecResidueField s))
    (K : PerfectDerivedCategory (pullback f g)) :
    perfectFourierMukaiOfProperFlat g f
        ⟨fourierMukaiLeftAdjointKernelDualizingFirst f g K.obj
            (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K.obj K.property)
            K.property,
          isPerfect_fourierMukaiLeftAdjointKernelDualizingFirst f g _ hG K.obj
            (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K.obj K.property)
            K.property⟩ ⊣
      perfectFourierMukaiOfProperFlat f g K := by
  have hK := PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K.obj K.property
  exact (perfectFourierMukaiOfProperFlatAdjunction g f
    ⟨_, isPerfect_fourierMukaiLeftAdjointKernel f g _ hG K.obj hK K.property⟩ K
    (fourierMukaiLeftAdjunction f g _ hG K.obj hK K.property)).ofNatIsoLeft
    (perfectFourierMukaiOfProperFlatCongr g f
      (fourierMukaiLeftAdjointKernelIsoDualizingFirst f g K.obj hK K.property))

end Adjoints

end AlgebraicGeometry

end
