module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RightAdjointLocallySmall
import StacksCore.Tactic.StacksAttribute

/-!
# The right adjoint of a Fourier-Mukai transform with pseudo-coherent kernel

[Stacks, Tag 0FYW]: let `X ⟶ S` and `Y ⟶ S` be morphisms of quasi-compact quasi-separated
schemes, `Φ : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` the Fourier-Mukai functor of a pseudo-coherent kernel
`K ∈ D_QCoh(𝒪_{X ×_S Y})`, `a` the right adjoint of `Rpr_{2,*}` ([Stacks, Tag 0A9E]),
`K' = (Y ×_S X → X ×_S Y)^* R𝓗om(K, a(𝒪_Y))` and `Φ'` its Fourier-Mukai transform. There is a
canonical map `Hom_X(M, Φ'(N)) ⟶ Hom_Y(Φ(M), N)`, functorial in `M` and `N`, which is an
isomorphism if `N` is perfect, or if `K` is perfect and `X ⟶ S` is proper, flat and of finite
presentation.

## Main definitions

* `AlgebraicGeometry.fourierMukaiRightAdjointKernel`: the kernel `K'`.
* `AlgebraicGeometry.fourierMukaiRightAdjoint`: the transform `Φ'`.
* `AlgebraicGeometry.fourierMukaiRightAdjointComparison`: the canonical map.

## Main results

* `AlgebraicGeometry.fourierMukaiRightAdjointComparison_spec`: **[Stacks, Tag 0FYW]**.

## Implementation notes

*The two models.* The Fourier-Mukai functor `AlgebraicGeometry.quasiCoherentFourierMukai` is
built at the standard model `HasDerivedCategory.standard` of the derived categories, while the
right adjoint `a` of [Stacks, Tag 0A9E] is constructed at the locally small model, the only one at
which `D_QCoh` has the direct sums Brown representability needs. The kernel
`R𝓗om(K, a(𝒪_Y))` is formed at the locally small model, with the derived internal Hom
`Stacks.Duality.InternalHom.derivedSheafHom` (the derived internal Hom of [Stacks, Tag 08DH] read
at that model), and is read back at the standard model along
`Stacks.Duality.StandardModel.quasiCoherentModelEquiv`, as is the dual kernel of
[Stacks, Tag 0FYX] (`AlgebraicGeometry.fourierMukaiLeftAdjointKernel`). The canonical map is the
map `Stacks.Duality.rightAdjointComparison` of the locally small model, read along the same
comparison and the identification of the Fourier-Mukai functors at the two models
(`AlgebraicGeometry.quasiCoherentFourierMukaiModelEquivIso`,
`Stacks.Duality.fourierMukaiLocallySmallSymmetryIso`).

## References

* [Stacks Project, Tag 0FYW](https://stacks.math.columbia.edu/tag/0FYW)
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

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

omit [CompactSpace S] in
/-- The finiteness properties of the morphisms and fibre products of [Stacks, Tag 0FYW] that follow
from its hypotheses: `X`, `Y` and `S` are quasi-compact and quasi-separated. -/
theorem fourierMukaiRightAdjoint_instances :
    QuasiCompact f ∧ QuasiSeparated f ∧ QuasiCompact g ∧ QuasiSeparated g ∧
      CompactSpace (pullback f g : Scheme.{u}) ∧ QuasiSeparatedSpace (pullback f g : Scheme.{u}) ∧
      CompactSpace (pullback g f : Scheme.{u}) ∧
      QuasiSeparatedSpace (pullback g f : Scheme.{u}) := by
  have : QuasiCompact f := inferInstance
  have : QuasiCompact g := inferInstance
  have : QuasiSeparated f := inferInstance
  have : QuasiSeparated g := inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f g),
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst f g),
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd g f),
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst g f)⟩

/-- **Pseudo-coherence does not depend on the model**, read along the comparison
`AlgebraicGeometry.Scheme.Modules.derivedModelEquiv`. -/
theorem isPseudoCoherent_derivedModelEquiv_functor_obj {Z : Scheme.{u}}
    (E : @DerivedCategory Z.Modules _ _ (HasDerivedCategory.standard _))
    (hE : @RingedSpace.IsPseudoCoherent Z.toRingedSpace (HasDerivedCategory.standard _) E) :
    RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace)
      ((Scheme.Modules.derivedModelEquiv Z).functor.obj E) :=
  @RingedSpace.IsPseudoCoherent.of_iso Z.toRingedSpace (Scheme.Modules.hasDerivedCategory Z) _ _
    ((PerfectApproximation.isPseudoCoherent_standard_iff E).1 hE)
    ((Scheme.Modules.schemeModulesComparisonFunctorIso Z).app E)

section Construction

variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
  [CompactSpace (pullback f g : Scheme.{u})] [QuasiSeparatedSpace (pullback f g : Scheme.{u})]
  [CompactSpace (pullback g f : Scheme.{u})] [QuasiSeparatedSpace (pullback g f : Scheme.{u})]
  (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
  (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
    (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
  (hpc : @RingedSpace.IsPseudoCoherent (pullback f g).toRingedSpace
    (HasDerivedCategory.standard _) K)

/-- The kernel `K`, read at the locally small model. -/
abbrev rightAdjointKernelLocallySmall :
    Stacks.Duality.quasiCoherentDerivedCategory (pullback f g) :=
  (Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback f g)).functor.obj ⟨K, hK⟩

omit [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g]
  [QuasiSeparated g] [CompactSpace (pullback f g : Scheme.{u})]
  [QuasiSeparatedSpace (pullback f g : Scheme.{u})] [CompactSpace (pullback g f : Scheme.{u})]
  [QuasiSeparatedSpace (pullback g f : Scheme.{u})] in
include hpc in
/-- The kernel `rightAdjointKernelLocallySmall f g K hK` is pseudo-coherent. -/
theorem isPseudoCoherent_rightAdjointKernelLocallySmall :
    RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace)
      (rightAdjointKernelLocallySmall f g K hK).obj :=
  isPseudoCoherent_derivedModelEquiv_functor_obj K hpc

/-- **The kernel `K' = (Y ×_S X → X ×_S Y)^* R𝓗om(K, a(𝒪_Y))` at the locally small model**, an
object of `D_QCoh(𝒪_{Y ×_S X})`, where `a` is the right adjoint of `Rpr_{2,*}`
([Stacks, Tag 0A9E]), `R𝓗om` the derived internal Hom and `K` is pseudo-coherent. -/
def fourierMukaiRightAdjointKernelLocallySmall :
    Stacks.Duality.quasiCoherentDerivedCategory (pullback g f) :=
  (Stacks.Duality.quasiCoherentDerivedPullback' (pullbackSymmetry g f).hom).obj
    (Stacks.Duality.dualKernel f g (rightAdjointKernelLocallySmall f g K hK)
      (isPseudoCoherent_rightAdjointKernelLocallySmall f g K hK hpc))

/-- **The kernel `K' = (Y ×_S X → X ×_S Y)^* R𝓗om(K, a(𝒪_Y))` of [Stacks, Tag 0FYW]**, an object
of `D(𝒪_{Y ×_S X})` at the standard model: `fourierMukaiRightAdjointKernelLocallySmall` read
along the comparison of the two models of `D_QCoh(𝒪_{Y ×_S X})`. -/
def fourierMukaiRightAdjointKernel :
    @DerivedCategory (pullback g f).Modules _ _ (HasDerivedCategory.standard _) :=
  ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback g f)).inverse.obj
    (fourierMukaiRightAdjointKernelLocallySmall f g K hK hpc)).obj

omit [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] [QuasiSeparatedSpace X]
  [QuasiCompact g] [QuasiSeparated g] [CompactSpace (pullback g f : Scheme.{u})]
  [QuasiSeparatedSpace (pullback g f : Scheme.{u})] in
/-- **The kernel `K'` lies in `D_QCoh(𝒪_{Y ×_S X})`** ([Stacks, Tag 0A6H], `K` being
pseudo-coherent and `a(𝒪_Y)` in `D⁺_QCoh` by [Stacks, Tag 0A9I]). -/
theorem isQuasicoherent_homology_fourierMukaiRightAdjointKernel (j : ℤ) :
    ((@DerivedCategory.homologyFunctor (pullback g f).Modules _ _
      (HasDerivedCategory.standard _) j).obj
        (fourierMukaiRightAdjointKernel f g K hK hpc)).IsQuasicoherent :=
  ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback g f)).inverse.obj
    (fourierMukaiRightAdjointKernelLocallySmall f g K hK hpc)).property j

/-- `D_QCoh(𝒪_Z)` at the standard model, in the spelling of the comparison
`Stacks.Duality.StandardModel.quasiCoherentModelEquiv` of the two models. -/
abbrev StdQCoh (Z : Scheme.{u}) : Type (u + 1) :=
  @Stacks.Duality.quasiCoherentDerivedCategory Z (HasDerivedCategory.standard Z.Modules)

/-- `Φ : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, the Fourier-Mukai transform with kernel `K`
(`AlgebraicGeometry.quasiCoherentFourierMukai`, [Stacks, Tag 0FYQ]). -/
abbrev fourierMukaiTransform : StdQCoh X ⥤ StdQCoh Y :=
  quasiCoherentFourierMukai f g K hK

/-- `Φ' : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`, the Fourier-Mukai transform with kernel `K'`
(`AlgebraicGeometry.quasiCoherentFourierMukai`, [Stacks, Tag 0FYQ]). -/
abbrev fourierMukaiRightAdjoint : StdQCoh Y ⥤ StdQCoh X :=
  quasiCoherentFourierMukai g f (fourierMukaiRightAdjointKernel f g K hK hpc)
    (isQuasicoherent_homology_fourierMukaiRightAdjointKernel f g K hK hpc)

/-- `Φ` read at the locally small model. -/
def fourierMukaiTransformModelIso :
    fourierMukaiTransform f g K hK ⋙
        (Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).functor ≅
      (Stacks.Duality.StandardModel.quasiCoherentModelEquiv X).functor ⋙
        Stacks.Duality.fourierMukaiLocallySmall f g (rightAdjointKernelLocallySmall f g K hK) :=
  quasiCoherentFourierMukaiModelEquivIso f g K hK

/-- `Φ'` read at the locally small model is the transform `N ↦ Rp_*(Lq^*N ⊗ᴸ R𝓗om(K, a(𝒪_Y)))`
computed on `X ×_S Y`. -/
def fourierMukaiRightAdjointModelIso :
    fourierMukaiRightAdjoint f g K hK hpc ⋙
        (Stacks.Duality.StandardModel.quasiCoherentModelEquiv X).functor ≅
      (Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).functor ⋙
        Stacks.Duality.fourierMukaiDualLocallySmall f g
          (Stacks.Duality.dualKernel f g (rightAdjointKernelLocallySmall f g K hK)
            (isPseudoCoherent_rightAdjointKernelLocallySmall f g K hK hpc)) :=
  quasiCoherentFourierMukaiModelEquivIso g f (fourierMukaiRightAdjointKernel f g K hK hpc)
      (isQuasicoherent_homology_fourierMukaiRightAdjointKernel f g K hK hpc) ≪≫
    Functor.isoWhiskerLeft (Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).functor
      (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
          ((MonoidalCategory.tensoringRight _).mapIso
            ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback g f)).counitIso.app
              (fourierMukaiRightAdjointKernelLocallySmall f g K hK hpc))) _) ≪≫
        Stacks.Duality.fourierMukaiLocallySmallSymmetryIso f g _)

/-- **The canonical map of [Stacks, Tag 0FYW]**, `Hom_X(M, Φ'(N)) ⟶ Hom_Y(Φ(M), N)`, for `M` in
`D_QCoh(𝒪_X)` and `N` in `D_QCoh(𝒪_Y)`: the map
`Stacks.Duality.rightAdjointComparison` of the locally small model (the adjunction
`Lpr_1^* ⊣ Rpr_{1,*}`, the map `Lpr_2^*N ⊗ᴸ R𝓗om(K, a(𝒪_Y)) ⟶ R𝓗om(K, a(N))` composed of the
maps of [Stacks, Tag 0BYS] and [Stacks, Tag 0A9S], the tensor–internal-Hom adjunction and
`Rpr_{2,*} ⊣ a`), read along the comparison of the two models. -/
def fourierMukaiRightAdjointComparison (M : StdQCoh X) (N : StdQCoh Y)
    (v : M ⟶ (fourierMukaiRightAdjoint f g K hK hpc).obj N) :
    (fourierMukaiTransform f g K hK).obj M ⟶ N :=
  (Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).fullyFaithfulFunctor.preimage
    ((fourierMukaiTransformModelIso f g K hK).hom.app M ≫
      Stacks.Duality.rightAdjointComparison f g (rightAdjointKernelLocallySmall f g K hK)
        (isPseudoCoherent_rightAdjointKernelLocallySmall f g K hK hpc)
        ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv X).functor.obj M)
        ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).functor.obj N)
        ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv X).functor.map v ≫
          (fourierMukaiRightAdjointModelIso f g K hK hpc).hom.app N))

omit [CompactSpace S] [QuasiSeparatedSpace S] [QuasiSeparatedSpace X]
  [CompactSpace (pullback g f : Scheme.{u})] [QuasiSeparatedSpace (pullback g f : Scheme.{u})] in
/-- The canonical map is natural in `M`. -/
theorem fourierMukaiRightAdjointComparison_naturality_left
    {M M' : StdQCoh X} (m : M' ⟶ M) (N : StdQCoh Y)
    (v : M ⟶ (fourierMukaiRightAdjoint f g K hK hpc).obj N) :
    fourierMukaiRightAdjointComparison f g K hK hpc M' N (m ≫ v) =
      (fourierMukaiTransform f g K hK).map m ≫
        fourierMukaiRightAdjointComparison f g K hK hpc M N v := by
  have h₂ : (fourierMukaiTransformModelIso f g K hK).hom.app M' ≫
      (Stacks.Duality.fourierMukaiLocallySmall f g (rightAdjointKernelLocallySmall f g K hK)).map
        ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv X).functor.map m) =
      (Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).functor.map
        ((fourierMukaiTransform f g K hK).map m) ≫
        (fourierMukaiTransformModelIso f g K hK).hom.app M :=
    ((fourierMukaiTransformModelIso f g K hK).hom.naturality m).symm
  dsimp only [fourierMukaiRightAdjointComparison]
  rw [Functor.map_comp, Category.assoc, Stacks.Duality.rightAdjointComparison_naturality_left,
    ← Category.assoc, h₂, Category.assoc, Functor.FullyFaithful.preimage_comp,
    Functor.FullyFaithful.preimage_map]

omit [CompactSpace S] [QuasiSeparatedSpace S] [QuasiSeparatedSpace X]
  [CompactSpace (pullback g f : Scheme.{u})] [QuasiSeparatedSpace (pullback g f : Scheme.{u})] in
/-- The canonical map is natural in `N`. -/
theorem fourierMukaiRightAdjointComparison_naturality_right
    (M : StdQCoh X) {N N' : StdQCoh Y} (n : N ⟶ N')
    (v : M ⟶ (fourierMukaiRightAdjoint f g K hK hpc).obj N) :
    fourierMukaiRightAdjointComparison f g K hK hpc M N'
        (v ≫ (fourierMukaiRightAdjoint f g K hK hpc).map n) =
      fourierMukaiRightAdjointComparison f g K hK hpc M N v ≫ n := by
  have h₂ : (Stacks.Duality.StandardModel.quasiCoherentModelEquiv X).functor.map
        ((fourierMukaiRightAdjoint f g K hK hpc).map n) ≫
        (fourierMukaiRightAdjointModelIso f g K hK hpc).hom.app N' =
      (fourierMukaiRightAdjointModelIso f g K hK hpc).hom.app N ≫
        (Stacks.Duality.fourierMukaiDualLocallySmall f g
          (Stacks.Duality.dualKernel f g (rightAdjointKernelLocallySmall f g K hK)
            (isPseudoCoherent_rightAdjointKernelLocallySmall f g K hK hpc))).map
          ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).functor.map n) :=
    (fourierMukaiRightAdjointModelIso f g K hK hpc).hom.naturality n
  dsimp only [fourierMukaiRightAdjointComparison]
  rw [Functor.map_comp, Category.assoc, h₂, ← Category.assoc,
    Stacks.Duality.rightAdjointComparison_naturality_right, ← Category.assoc,
    Functor.FullyFaithful.preimage_comp, Functor.FullyFaithful.preimage_map]

omit [CompactSpace S] [QuasiSeparatedSpace S] [QuasiSeparatedSpace X]
  [CompactSpace (pullback g f : Scheme.{u})] [QuasiSeparatedSpace (pullback g f : Scheme.{u})] in
/-- The canonical map is bijective as soon as its locally small form is. -/
theorem bijective_fourierMukaiRightAdjointComparison (M : StdQCoh X) (N : StdQCoh Y)
    (hb : Function.Bijective (Stacks.Duality.rightAdjointComparison f g
        (rightAdjointKernelLocallySmall f g K hK)
        (isPseudoCoherent_rightAdjointKernelLocallySmall f g K hK hpc)
        ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv X).functor.obj M)
        ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).functor.obj N))) :
    Function.Bijective (fourierMukaiRightAdjointComparison f g K hK hpc M N) := by
  let eX := Stacks.Duality.StandardModel.quasiCoherentModelEquiv X
  let eY := Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y
  let e₁ : (M ⟶ (fourierMukaiRightAdjoint f g K hK hpc).obj N) ≃
      (eX.functor.obj M ⟶ (Stacks.Duality.fourierMukaiDualLocallySmall f g
          (Stacks.Duality.dualKernel f g (rightAdjointKernelLocallySmall f g K hK)
            (isPseudoCoherent_rightAdjointKernelLocallySmall f g K hK hpc))).obj
        (eY.functor.obj N)) :=
    eX.fullyFaithfulFunctor.homEquiv.trans
      ((Iso.refl _).homCongr ((fourierMukaiRightAdjointModelIso f g K hK hpc).app N))
  let e₂ : ((Stacks.Duality.fourierMukaiLocallySmall f g
        (rightAdjointKernelLocallySmall f g K hK)).obj (eX.functor.obj M) ⟶ eY.functor.obj N) ≃
      ((fourierMukaiTransform f g K hK).obj M ⟶ N) :=
    (((fourierMukaiTransformModelIso f g K hK).app M).homCongr (Iso.refl _)).symm.trans
      eY.fullyFaithfulFunctor.homEquiv.symm
  convert e₂.bijective.comp (hb.comp e₁.bijective) using 1
  funext v
  simp [fourierMukaiRightAdjointComparison, e₁, e₂, Iso.homCongr_apply, eX, eY]

/-- The comparison equivalence of the two models preserves perfect objects. -/
private theorem isPerfect_quasiCoherentModelEquiv_functor_obj {Z : Scheme.{u}} (E : StdQCoh Z)
    (hE : @Stacks.Cohomology.PerfectComplexes.IsPerfect Z.toRingedSpace
      (HasDerivedCategory.standard _) E.obj) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z.toRingedSpace)
      ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv Z).functor.obj E).obj :=
  (Stacks.Duality.isPerfect_modelEquiv_functor_obj_iff Z.toRingedSpace
    (HasDerivedCategory.standard Z.Modules) (Scheme.Modules.hasDerivedCategory Z) E.obj).2 hE

omit [CompactSpace S] [QuasiSeparatedSpace S] [QuasiSeparatedSpace X]
  [CompactSpace (pullback g f : Scheme.{u})] [QuasiSeparatedSpace (pullback g f : Scheme.{u})] in
/-- The canonical map is bijective as soon as the pairing `γ` of the locally small model is
invertible. -/
private theorem bijective_fourierMukaiRightAdjointComparison_of_isIso (M : StdQCoh X)
    (N : StdQCoh Y)
    [IsIso (Stacks.Duality.dualKernelPairing f g (rightAdjointKernelLocallySmall f g K hK)
      (isPseudoCoherent_rightAdjointKernelLocallySmall f g K hK hpc)
      ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).functor.obj N))] :
    Function.Bijective (fourierMukaiRightAdjointComparison f g K hK hpc M N) :=
  bijective_fourierMukaiRightAdjointComparison f g K hK hpc M N
    (Stacks.Duality.bijective_rightAdjointComparison_of_isIso f g _ _ _ _)

omit [CompactSpace S] [QuasiSeparatedSpace S] [QuasiSeparatedSpace X]
  [CompactSpace (pullback g f : Scheme.{u})] [QuasiSeparatedSpace (pullback g f : Scheme.{u})] in
/-- **The canonical map is bijective for perfect `N`.** -/
theorem bijective_fourierMukaiRightAdjointComparison_of_isPerfect (M : StdQCoh X) (N : StdQCoh Y)
    (hN : @Stacks.Cohomology.PerfectComplexes.IsPerfect Y.toRingedSpace
      (HasDerivedCategory.standard _) N.obj) :
    Function.Bijective (fourierMukaiRightAdjointComparison f g K hK hpc M N) := by
  have := Stacks.Duality.isIso_dualKernelPairing_of_isPerfect f g
    (rightAdjointKernelLocallySmall f g K hK)
    (isPseudoCoherent_rightAdjointKernelLocallySmall f g K hK hpc) _
    (isPerfect_quasiCoherentModelEquiv_functor_obj N hN)
  exact bijective_fourierMukaiRightAdjointComparison_of_isIso f g K hK hpc M N

omit [CompactSpace S] [QuasiSeparatedSpace S] [QuasiSeparatedSpace X]
  [CompactSpace (pullback g f : Scheme.{u})] [QuasiSeparatedSpace (pullback g f : Scheme.{u})] in
/-- **The canonical map is bijective for a perfect kernel and `X ⟶ S` proper, flat and of finite
presentation.** -/
theorem bijective_fourierMukaiRightAdjointComparison_of_isPerfect_of_flat [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f]
    (hKp : @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
      (HasDerivedCategory.standard _) K) (M : StdQCoh X) (N : StdQCoh Y) :
    Function.Bijective (fourierMukaiRightAdjointComparison f g K hK hpc M N) := by
  have := Stacks.Duality.isIso_dualKernelPairing_of_isPerfect_of_flat f g
    (rightAdjointKernelLocallySmall f g K hK)
    (isPseudoCoherent_rightAdjointKernelLocallySmall f g K hK hpc)
    (isPerfect_quasiCoherentModelEquiv_functor_obj ⟨K, hK⟩ hKp)
    ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).functor.obj N)
  exact bijective_fourierMukaiRightAdjointComparison_of_isIso f g K hK hpc M N

end Construction

omit [CompactSpace S] in
/-- **[Stacks, Tag 0FYW].** Let `X ⟶ S` and `Y ⟶ S` be morphisms of quasi-compact and
quasi-separated schemes. Let `Φ : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` be the Fourier-Mukai functor of a
pseudo-coherent kernel `K ∈ D_QCoh(𝒪_{X ×_S Y})` (`AlgebraicGeometry.fourierMukaiTransform`),
let `a : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_{X ×_S Y})` be the right adjoint of `Rpr_{2,*}`
([Stacks, Tag 0A9E]), let `K' = (Y ×_S X → X ×_S Y)^* R𝓗om(K, a(𝒪_Y))`
(`AlgebraicGeometry.fourierMukaiRightAdjointKernel`) and let `Φ' : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` be
its Fourier-Mukai transform (`AlgebraicGeometry.fourierMukaiRightAdjoint`). Then:
* `K'` lies in `D_QCoh(𝒪_{Y ×_S X})`;
* the canonical map `Hom_X(M, Φ'(N)) ⟶ Hom_Y(Φ(M), N)`
  (`AlgebraicGeometry.fourierMukaiRightAdjointComparison`) is functorial in `M ∈ D_QCoh(𝒪_X)` and
  `N ∈ D_QCoh(𝒪_Y)`;
* it is an isomorphism if (1) `N` is perfect, or (2) `K` is perfect and `X ⟶ S` is proper, flat
  and of finite presentation.

The quasi-compactness and quasi-separatedness of the morphisms and of the two fibre products, which
the constructions ask for, follow from the hypotheses
(`AlgebraicGeometry.fourierMukaiRightAdjoint_instances`). -/
@[stacks 0FYW]
theorem fourierMukaiRightAdjointComparison_spec
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent)
    (hpc : @RingedSpace.IsPseudoCoherent (pullback f g).toRingedSpace
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
    (∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback g f).Modules _ _
        (HasDerivedCategory.standard _) j).obj
          (fourierMukaiRightAdjointKernel f g K hK hpc)).IsQuasicoherent) ∧
    (∀ {M M' : StdQCoh X} (m : M' ⟶ M) (N : StdQCoh Y)
        (v : M ⟶ (fourierMukaiRightAdjoint f g K hK hpc).obj N),
      fourierMukaiRightAdjointComparison f g K hK hpc M' N (m ≫ v) =
        (fourierMukaiTransform f g K hK).map m ≫
          fourierMukaiRightAdjointComparison f g K hK hpc M N v) ∧
    (∀ (M : StdQCoh X) {N N' : StdQCoh Y} (n : N ⟶ N')
        (v : M ⟶ (fourierMukaiRightAdjoint f g K hK hpc).obj N),
      fourierMukaiRightAdjointComparison f g K hK hpc M N'
          (v ≫ (fourierMukaiRightAdjoint f g K hK hpc).map n) =
        fourierMukaiRightAdjointComparison f g K hK hpc M N v ≫ n) ∧
    (∀ (M : StdQCoh X) (N : StdQCoh Y),
      @Stacks.Cohomology.PerfectComplexes.IsPerfect Y.toRingedSpace
        (HasDerivedCategory.standard _) N.obj →
      Function.Bijective (fourierMukaiRightAdjointComparison f g K hK hpc M N)) ∧
    (IsProper f → Flat f → LocallyOfFinitePresentation f →
      @Stacks.Cohomology.PerfectComplexes.IsPerfect (pullback f g).toRingedSpace
        (HasDerivedCategory.standard _) K →
      ∀ (M : StdQCoh X) (N : StdQCoh Y),
        Function.Bijective (fourierMukaiRightAdjointComparison f g K hK hpc M N)) := by
  obtain ⟨_, _, _, _, _, _, _, _⟩ := fourierMukaiRightAdjoint_instances f g
  exact ⟨isQuasicoherent_homology_fourierMukaiRightAdjointKernel f g K hK hpc,
    fourierMukaiRightAdjointComparison_naturality_left f g K hK hpc,
    fourierMukaiRightAdjointComparison_naturality_right f g K hK hpc,
    bijective_fourierMukaiRightAdjointComparison_of_isPerfect f g K hK hpc,
    fun _ _ _ hKp M N =>
      bijective_fourierMukaiRightAdjointComparison_of_isPerfect_of_flat f g K hK hpc hKp M N⟩

end AlgebraicGeometry

end
