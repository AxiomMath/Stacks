module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.CompositionIso
public import
  StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange

/-!
# Base change of Fourier-Mukai kernels along arbitrary cartesian squares

Let `s : S₁ ⟶ S` be a morphism of schemes and let `hX`, `hY`, `hZ` be cartesian squares
exhibiting `f₁ : X₁ ⟶ S₁`, `g₁ : Y₁ ⟶ S₁`, `h₁ : Z₁ ⟶ S₁` as base changes of
`f : X ⟶ S`, `g : Y ⟶ S`, `h : Z ⟶ S` along `s`. This file proves that derived pullback along
the comparisons `X₁ ×_{S₁} Y₁ ⟶ X ×_S Y` carries the diagonal kernel of `X/S` to that of
`X₁/S₁` and the convolution of [Stacks, Tag 0FYS] to the convolution of the pulled-back kernels.

## Main definitions

* `AlgebraicGeometry.baseChangePullbackMap` — the comparison `X₁ ×_{S₁} Y₁ ⟶ X ×_S Y` attached
  to two commutative squares over the same `s`.

## Main results

* `AlgebraicGeometry.diagonalKernelBaseChangeIsoOfIsPullback` — the diagonal kernel commutes
  with base change.
* `AlgebraicGeometry.convolutionBaseChangeIsoOfIsPullback` — the convolution kernel commutes with
  base change.
* `AlgebraicGeometry.isRelativeEquivalenceKernel_dpull_baseChangePullbackMap` — the kernel of a
  relative equivalence stays one along an arbitrary pair of cartesian squares, and
  `AlgebraicGeometry.isRelativeEquivalenceKernel_derivedPullback_of_iso` its case of
  isomorphisms of the two families.

## References

* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0G0G](https://stacks.math.columbia.edu/tag/0G0G)
* [Stacks Project, Tag 0G0K](https://stacks.math.columbia.edu/tag/0G0K)
* [Stacks Project, Tag 0CTA](https://stacks.math.columbia.edu/tag/0CTA)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 00M3](https://stacks.math.columbia.edu/tag/00M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Base change of fibre products: the cartesian squares -/

section Geometry

universe v' u'

variable {C : Type u'} [Category.{v'} C] [HasPullbacks C]

section
variable {S S₁ X Y X₁ Y₁ : C} {f : X ⟶ S} {g : Y ⟶ S} {s : S₁ ⟶ S}
  {cX : X₁ ⟶ X} {f₁ : X₁ ⟶ S₁} {cY : Y₁ ⟶ Y} {g₁ : Y₁ ⟶ S₁}

/-- The comparison `X₁ ×_{S₁} Y₁ ⟶ X ×_S Y` induced by two commutative squares over the same
`s : S₁ ⟶ S`; when the squares are cartesian it is the comparison from the fibre product of two
base changes to the original fibre product. -/
def baseChangePullbackMap (hX : CommSq cX f₁ f s) (hY : CommSq cY g₁ g s) :
    pullback f₁ g₁ ⟶ pullback f g :=
  pullback.map f₁ g₁ f g cX cY s hX.w.symm hY.w.symm

/-- The comparison `X₁ ×_{S₁} Y₁ ⟶ X ×_S Y` followed by the first projection to `X` is the first
projection to `X₁` followed by `cX`. -/
@[reassoc (attr := simp)]
lemma baseChangePullbackMap_fst (hX : CommSq cX f₁ f s) (hY : CommSq cY g₁ g s) :
    baseChangePullbackMap hX hY ≫ pullback.fst f g = pullback.fst f₁ g₁ ≫ cX :=
  pullback.lift_fst _ _ _

/-- The comparison `X₁ ×_{S₁} Y₁ ⟶ X ×_S Y` followed by the second projection to `Y` is the
second projection to `Y₁` followed by `cY`. -/
@[reassoc (attr := simp)]
lemma baseChangePullbackMap_snd (hX : CommSq cX f₁ f s) (hY : CommSq cY g₁ g s) :
    baseChangePullbackMap hX hY ≫ pullback.snd f g = pullback.snd f₁ g₁ ≫ cY :=
  pullback.lift_snd _ _ _

/-- When the three sides `cX`, `cY` and `s` of the two squares are isomorphisms, so is the
comparison morphism of the fibre products. -/
lemma isIso_baseChangePullbackMap (hX : CommSq cX f₁ f s) (hY : CommSq cY g₁ g s)
    [IsIso cX] [IsIso cY] [IsIso s] : IsIso (baseChangePullbackMap hX hY) :=
  inferInstanceAs (IsIso (pullback.map f₁ g₁ f g cX cY s hX.w.symm hY.w.symm))

/-- The first projection of a fibre product is compatible with base change. -/
lemma isPullback_baseChangePullbackMap_fst (hX : IsPullback cX f₁ f s)
    (hY : IsPullback cY g₁ g s) :
    IsPullback (baseChangePullbackMap hX.toCommSq hY.toCommSq) (pullback.fst f₁ g₁)
        (pullback.fst f g) cX := by
  refine IsPullback.of_right ?_ (baseChangePullbackMap_fst hX.toCommSq hY.toCommSq)
    (IsPullback.of_hasPullback f g).flip
  have h := ((IsPullback.of_hasPullback f₁ g₁).flip).paste_horiz hY
  rwa [baseChangePullbackMap_snd hX.toCommSq hY.toCommSq, ← hX.w] at *

/-- The second projection of a fibre product is compatible with base change. -/
lemma isPullback_baseChangePullbackMap_snd (hX : IsPullback cX f₁ f s)
    (hY : IsPullback cY g₁ g s) :
    IsPullback (baseChangePullbackMap hX.toCommSq hY.toCommSq) (pullback.snd f₁ g₁)
        (pullback.snd f g) cY := by
  refine IsPullback.of_right ?_ (baseChangePullbackMap_snd hX.toCommSq hY.toCommSq)
    (IsPullback.of_hasPullback f g)
  have h := (IsPullback.of_hasPullback f₁ g₁).paste_horiz hX
  rwa [baseChangePullbackMap_fst hX.toCommSq hY.toCommSq, ← hY.w] at *

/-- The fibre product of two base changes is the base change of the fibre product. -/
lemma isPullback_baseChangePullbackMap_base (hX : IsPullback cX f₁ f s)
    (hY : IsPullback cY g₁ g s) :
    IsPullback (baseChangePullbackMap hX.toCommSq hY.toCommSq) (pullback.fst f₁ g₁ ≫ f₁)
      (pullback.fst f g ≫ f) s :=
  (isPullback_baseChangePullbackMap_fst hX hY).paste_vert hX

/-- The fibre product of two base changes is the base change of the fibre product, with the
structure morphisms taken through the second projections. -/
lemma isPullback_baseChangePullbackMap_base' (hX : IsPullback cX f₁ f s)
    (hY : IsPullback cY g₁ g s) :
    IsPullback (baseChangePullbackMap hX.toCommSq hY.toCommSq) (pullback.snd f₁ g₁ ≫ g₁)
      (pullback.snd f g ≫ g) s :=
  (isPullback_baseChangePullbackMap_snd hX hY).paste_vert hY

/-- The diagonal is compatible with base change. -/
lemma isPullback_baseChangePullbackMap_diagonal (hX : IsPullback cX f₁ f s) :
    IsPullback cX (pullback.diagonal f₁) (pullback.diagonal f)
      (baseChangePullbackMap hX.toCommSq hX.toCommSq) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_baseChangePullbackMap_snd hX hX)
  · simpa using (IsPullback.of_id_snd (f := cX))
  · apply pullback.hom_ext <;> simp

end

end Geometry

universe u

/-! ### `pr₁₃` on the triple fibre product of schemes -/

section Triple

variable {S S₁ X Y Z X₁ Y₁ Z₁ : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {s : S₁ ⟶ S}
  {cX : X₁ ⟶ X} {f₁ : X₁ ⟶ S₁} {cY : Y₁ ⟶ Y} {g₁ : Y₁ ⟶ S₁} {cZ : Z₁ ⟶ Z} {h₁ : Z₁ ⟶ S₁}

/-- **`pr₁₃` is compatible with base change**: `pr₁₃` on `X₁ ×_{S₁} Y₁ ×_{S₁} Z₁` is the base
change of `pr₁₃` on `X ×_S Y ×_S Z` along `X₁ ×_{S₁} Z₁ ⟶ X ×_S Z`. -/
lemma isPullback_fourierMukaiPr13_baseChangePullbackMap (hX : IsPullback cX f₁ f s)
    (hY : IsPullback cY g₁ g s) (hZ : IsPullback cZ h₁ h s) :
    IsPullback
      (baseChangePullbackMap (isPullback_baseChangePullbackMap_base' hX hY).toCommSq
        hZ.toCommSq)
      (fourierMukaiPr13 f₁ g₁ h₁) (fourierMukaiPr13 f g h)
      (baseChangePullbackMap hX.toCommSq hZ.toCommSq) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_baseChangePullbackMap_snd hX hZ)
  · simpa using isPullback_baseChangePullbackMap_snd
      (isPullback_baseChangePullbackMap_base' hX hY) hZ
  · apply pullback.hom_ext <;>
      simp [reassoc_of% (fourierMukaiPr13_fst f₁ g₁ h₁),
        reassoc_of% (fourierMukaiPr13_snd f₁ g₁ h₁)]

/-- **`pr₁₃` exhibits the triple fibre product as the fibre product of `X ×_S Y` and `X ×_S Z`
over `X`.** In particular `pr₁₃` is a base change of `pr_X : X ×_S Y ⟶ X`. -/
lemma isPullback_fourierMukaiPr12_fourierMukaiPr13 (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    IsPullback (fourierMukaiPr12 f g h) (fourierMukaiPr13 f g h)
      (pullback.fst f g) (pullback.fst f h) := by
  refine IsPullback.of_bot ?_ (fourierMukaiPr13_fst f g h).symm (IsPullback.of_hasPullback f h)
  rw [fourierMukaiPr13_snd, pullback.condition (f := f) (g := g)]
  exact IsPullback.of_hasPullback _ _

end Triple

/-! ### The two base-change isomorphisms -/

section BaseChange

/-- `fourierMukaiBaseChangeMap` is the comparison of the two chosen base-change squares. -/
lemma fourierMukaiBaseChangeMap_eq_baseChangePullbackMap {S X Y S₁ : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (s : S₁ ⟶ S) : fourierMukaiBaseChangeMap f g s =
      baseChangePullbackMap (IsPullback.of_hasPullback f s).toCommSq
          (IsPullback.of_hasPullback g s).toCommSq :=
  rfl

/-- **The diagonal kernel commutes with base change**, at an arbitrary cartesian square. For
`f : X ⟶ S` separated and a cartesian square `hX` exhibiting `f₁ : X₁ ⟶ S₁` as the base change
of `f` along `s : S₁ ⟶ S`, the derived pullback of `𝒪_{Δ_{X/S}}` along
`X₁ ×_{S₁} X₁ ⟶ X ×_S X` is `𝒪_{Δ_{X₁/S₁}}`, provided `X₁ ×_{S₁} X₁` and `X` are Tor
independent over `X ×_S X` (`htor`). -/
def diagonalKernelBaseChangeIsoOfIsPullback
    {S X S₁ X₁ : Scheme.{u}} {f : X ⟶ S} {s : S₁ ⟶ S} {cX : X₁ ⟶ X} {f₁ : X₁ ⟶ S₁}
    (hX : IsPullback cX f₁ f s)
    (htor : TorIndependent (pullback.diagonal f) (baseChangePullbackMap hX.toCommSq hX.toCommSq))
    [IsSeparated f] :
    (dpull (baseChangePullbackMap hX.toCommSq hX.toCommSq)).obj (diagonalKernel f) ≅ diagonalKernel
        f₁ := by
  change (dpull _).obj ((dpush (pullback.diagonal f)).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))) ≅
    (dpush (pullback.diagonal f₁)).obj
      ((DerivedCategory.singleFunctor X₁.Modules 0).obj (SheafOfModules.unit X₁.ringCatSheaf))
  have hiso := derivedBaseChangeIsoOfTorIndependent
    (isPullback_baseChangePullbackMap_diagonal hX).flip inferInstance htor
    ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))
  exact @asIso _ _ _ _ _ hiso ≪≫
    (dpush (pullback.diagonal f₁)).mapIso
      (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso cX.toLRSHom.toShHom)

/-- **The convolution kernel commutes with base change**, at an arbitrary triple of cartesian
squares over the same `s : S₁ ⟶ S`. If `hX`, `hY`, `hZ` exhibit `f₁`, `g₁`, `h₁` as the base
changes of `f`, `g`, `h` along `s` and `g` is flat, quasi-compact and quasi-separated, then
the derived pullback along `X₁ ×_{S₁} Z₁ ⟶ X ×_S Z` of the convolution
`R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*M)` of [Stacks, Tag 0FYS] is the convolution of the
derived pullbacks of `K` and `M`, for `K`, `M` with quasi-coherent cohomology. -/
def convolutionBaseChangeIsoOfIsPullback
    {S X Y Z S₁ X₁ Y₁ Z₁ : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {s : S₁ ⟶ S}
    {cX : X₁ ⟶ X} {f₁ : X₁ ⟶ S₁} {cY : Y₁ ⟶ Y} {g₁ : Y₁ ⟶ S₁} {cZ : Z₁ ⟶ Z} {h₁ : Z₁ ⟶ S₁}
    (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) (hZ : IsPullback cZ h₁ h s)
    [QuasiCompact g] [QuasiSeparated g] [Flat g]
    {K : DerivedCategory (pullback f g).Modules} (hK : IsQCohAll K)
    {M : DerivedCategory (pullback g h).Modules} (hM : IsQCohAll M) :
    (dpull (baseChangePullbackMap hX.toCommSq hZ.toCommSq)).obj (fourierMukaiConvolution f g h K M)
        ≅
      fourierMukaiConvolution f₁ g₁ h₁
        ((dpull (baseChangePullbackMap hX.toCommSq hY.toCommSq)).obj K)
        ((dpull (baseChangePullbackMap hY.toCommSq hZ.toCommSq)).obj M) := by
  have hA1 := isPullback_fourierMukaiPr13_baseChangePullbackMap hX hY hZ
  have hsq := shHom_comp_eq hA1.w
  have h1213 := isPullback_fourierMukaiPr12_fourierMukaiPr13 f g h
  haveI : Flat (fourierMukaiPr13 f g h) := MorphismProperty.of_isPullback h1213 inferInstance
  haveI : QuasiCompact (fourierMukaiPr13 f g h) :=
    MorphismProperty.of_isPullback h1213 inferInstance
  haveI : QuasiSeparated (fourierMukaiPr13 f g h) :=
    MorphismProperty.of_isPullback h1213 inferInstance
  have htor : TorIndependent (fourierMukaiPr13 f g h)
      (baseChangePullbackMap hX.toCommSq hZ.toCommSq) :=
    torIndependent_of_flat_left _ _
  have hT : IsQCohAll (fourierMukaiConvolutionTensor f g h K M) :=
    isQCohAll_dtenR (isQCohAll_dpull _ hK) (isQCohAll_dpull _ hM)
  have h12 :
      (baseChangePullbackMap (isPullback_baseChangePullbackMap_base' hX hY).toCommSq hZ.toCommSq)
      ≫ fourierMukaiPr12 f g h =
      fourierMukaiPr12 f₁ g₁ h₁ ≫ baseChangePullbackMap hX.toCommSq hY.toCommSq :=
          baseChangePullbackMap_fst _ _
  have h23 :
      (baseChangePullbackMap (isPullback_baseChangePullbackMap_base' hX hY).toCommSq hZ.toCommSq)
      ≫ fourierMukaiPr23 f g h =
      fourierMukaiPr23 f₁ g₁ h₁ ≫ baseChangePullbackMap hY.toCommSq hZ.toCommSq := by
    apply pullback.hom_ext <;>
      simp [fourierMukaiPr23, baseChangePullbackMap, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  haveI : IsIso ((dbaseChange
      (baseChangePullbackMap (isPullback_baseChangePullbackMap_base' hX hY).toCommSq hZ.toCommSq)
      (fourierMukaiPr13 f₁ g₁ h₁)
      (fourierMukaiPr13 f g h) (baseChangePullbackMap hX.toCommSq hZ.toCommSq) hsq).app
      (fourierMukaiConvolutionTensor f g h K M)) :=
    derivedBaseChangeIsIsoOnQuasicoherent _ _ _ _ hA1 inferInstance inferInstance htor hsq _ hT
  have hbc := asIso ((dbaseChange
      (baseChangePullbackMap (isPullback_baseChangePullbackMap_base' hX hY).toCommSq hZ.toCommSq)
      (fourierMukaiPr13 f₁ g₁ h₁) (fourierMukaiPr13 f g h)
          (baseChangePullbackMap hX.toCommSq hZ.toCommSq) hsq).app
      (fourierMukaiConvolutionTensor f g h K M))
  refine hbc ≪≫
    (dpush (fourierMukaiPr13 f₁ g₁ h₁)).mapIso ?_
  refine (dpullTensorIso
        (baseChangePullbackMap (isPullback_baseChangePullbackMap_base' hX hY).toCommSq hZ.toCommSq)
      ((dpull (fourierMukaiPr23 f g h)).obj M)).app
      ((dpull (fourierMukaiPr12 f g h)).obj K) ≪≫ ?_
  exact (dtenR _ _).mapIso
      ((dpullCompIsoEq
        (baseChangePullbackMap (isPullback_baseChangePullbackMap_base' hX hY).toCommSq
          hZ.toCommSq)
        (fourierMukaiPr12 f g h) (fourierMukaiPr12 f₁ g₁ h₁)
        (baseChangePullbackMap hX.toCommSq hY.toCommSq) h12).app K) ≪≫
    ((derivedTensorProductFunctor _).flip.mapIso
      ((dpullCompIsoEq
        (baseChangePullbackMap (isPullback_baseChangePullbackMap_base' hX hY).toCommSq
          hZ.toCommSq)
        (fourierMukaiPr23 f g h) (fourierMukaiPr23 f₁ g₁ h₁)
        (baseChangePullbackMap hY.toCommSq hZ.toCommSq) h23).app M)).app _

end BaseChange

/-! ### Relative equivalences along cartesian squares -/

section RelativeEquivalence

/-- The isomorphism `𝒪_Δ ≅ K ⋆ K'` pulls back along base change to `𝒪_Δ ≅ K₁ ⋆ K'₁`. -/
private theorem nonempty_diagonalKernel_iso_convolution
    {S X Y S₁ X₁ Y₁ : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {s : S₁ ⟶ S}
    {cX : X₁ ⟶ X} {f₁ : X₁ ⟶ S₁} {cY : Y₁ ⟶ Y} {g₁ : Y₁ ⟶ S₁}
    (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s)
    (htor : TorIndependent (pullback.diagonal f) (baseChangePullbackMap hX.toCommSq hX.toCommSq))
    [IsSeparated f] [QuasiCompact g] [QuasiSeparated g] [Flat g]
    {K : DerivedCategory (pullback f g).Modules} {K' : DerivedCategory (pullback g f).Modules}
    (e : diagonalKernel f ≅ fourierMukaiConvolution f g f K K')
    (hK : IsQCohAll K) (hK' : IsQCohAll K') :
    Nonempty (diagonalKernel f₁ ≅ fourierMukaiConvolution f₁ g₁ f₁
      ((dpull (baseChangePullbackMap hX.toCommSq hY.toCommSq)).obj K)
      ((dpull (baseChangePullbackMap hY.toCommSq hX.toCommSq)).obj K')) :=
  ⟨(diagonalKernelBaseChangeIsoOfIsPullback hX htor).symm ≪≫
    (dpull (baseChangePullbackMap hX.toCommSq hX.toCommSq)).mapIso e ≪≫
    convolutionBaseChangeIsoOfIsPullback hX hY hX hK hK'⟩

/-- **A relative equivalence is stable along an arbitrary pair of cartesian squares.** If `hX`
exhibits `f₁ : X₁ ⟶ S₁` as the base change of `f` along `s` and `hY` exhibits `g₁ : Y₁ ⟶ S₁` as
the base change of `g` along the same `s`, then the derived pullback of a relative-equivalence
kernel along `X₁ ×_{S₁} Y₁ ⟶ X ×_S Y` is a relative-equivalence kernel from `X₁` to `Y₁` over
`S₁`, given the Tor independence of the two diagonal squares (`htorX`, `htorY`). This is the
content of [Stacks, Tag 0G0K] at a base change presented by cartesian squares. -/
theorem isRelativeEquivalenceKernel_dpull_baseChangePullbackMap
    {S X Y S₁ X₁ Y₁ : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {s : S₁ ⟶ S}
    {cX : X₁ ⟶ X} {f₁ : X₁ ⟶ S₁} {cY : Y₁ ⟶ Y} {g₁ : Y₁ ⟶ S₁}
    (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s)
    (htorX : TorIndependent (pullback.diagonal f) (baseChangePullbackMap hX.toCommSq hX.toCommSq))
    (htorY : TorIndependent (pullback.diagonal g) (baseChangePullbackMap hY.toCommSq hY.toCommSq))
    [IsSeparated f] [IsSeparated g] [Flat f] [Flat g]
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    {K : DerivedCategory (pullback f g).Modules}
    (hK : IsRelativeEquivalenceKernel f g K) :
    IsRelativeEquivalenceKernel f₁ g₁
        ((dpull (baseChangePullbackMap hX.toCommSq hY.toCommSq)).obj K) := by
  obtain ⟨hKperf, K', hK'perf, ⟨e₁⟩, ⟨e₂⟩⟩ := hK
  have hKq : IsQCohAll K := PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K hKperf
  have hK'q : IsQCohAll K' :=
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K' hK'perf
  refine ⟨RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K hKperf,
    (dpull (baseChangePullbackMap hY.toCommSq hX.toCommSq)).obj K',
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K' hK'perf, ?_, ?_⟩
  · exact nonempty_diagonalKernel_iso_convolution hX hY htorX e₁ hKq hK'q
  · exact nonempty_diagonalKernel_iso_convolution hY hX htorY e₂ hK'q hKq

/-- **A relative equivalence transports along isomorphisms of the two families.** If `K` is the
Fourier-Mukai kernel of a relative equivalence from `X` to `Y` over `S` and `eX : X₁ ≅ X`,
`eY : Y₁ ≅ Y` are isomorphisms, then the derived pullback of `K` along the induced isomorphism
`X₁ ×_S Y₁ ≅ X ×_S Y` is the Fourier-Mukai kernel of a relative equivalence from `X₁` to `Y₁`
over `S`, for the structure morphisms `eX.hom ≫ f` and `eY.hom ≫ g`. -/
theorem isRelativeEquivalenceKernel_derivedPullback_of_iso
    {S X Y X₁ Y₁ : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (eX : X₁ ≅ X) (eY : Y₁ ≅ Y)
    {f₁ : X₁ ⟶ S} {g₁ : Y₁ ⟶ S} (hf : eX.hom ≫ f = f₁) (hg : eY.hom ≫ g = g₁)
    [IsSeparated f] [IsSeparated g] [Flat f] [Flat g]
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    {K : DerivedCategory (pullback f g).Modules}
    (hK : IsRelativeEquivalenceKernel f g K) :
    IsRelativeEquivalenceKernel f₁ g₁
      ((dpull (pullback.map f₁ g₁ f g eX.hom eY.hom (𝟙 S)
        (by rw [Category.comp_id, hf]) (by rw [Category.comp_id, hg]))).obj K) := by
  have hX : IsPullback eX.hom f₁ f (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hf]⟩
  have hY : IsPullback eY.hom g₁ g (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hg]⟩
  have := isIso_baseChangePullbackMap hX.toCommSq hX.toCommSq
  have := isIso_baseChangePullbackMap hY.toCommSq hY.toCommSq
  exact isRelativeEquivalenceKernel_dpull_baseChangePullbackMap hX hY
    (TorIndependent.symm (torIndependent_of_flat_left _ _))
    (TorIndependent.symm (torIndependent_of_flat_left _ _)) hK

end RelativeEquivalence

end AlgebraicGeometry

end
