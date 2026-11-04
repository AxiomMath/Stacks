module

public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ConvolutionComparison
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ExactKernelEquivalence
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ExactKernels

/-!
# Convolution of kernels and composition of integral transforms

Let `R` be a commutative ring and let `X`, `Y` and `Z` be schemes over `R`.  A quasi-coherent
kernel `K` on `X ×_R Y` has the integral transform
`F_K : F ↦ pr_{2,*}(pr_1^*F ⊗_{𝒪_{X ×_R Y}} K)` of Tag 0FZB, and likewise a quasi-coherent
kernel `L` on `Y ×_R Z` has `F_L`.  This file builds the convolution
`K * L = pr_{13,*}(pr_{12}^*K ⊗_{𝒪_{X ×_R Y ×_R Z}} pr_{23}^*L)` on `X ×_R Z` and identifies
`F_L ∘ F_K` with `F_{K * L}`.

## Main definitions

* `AlgebraicGeometry.convolutionIntegrand` is `pr_{12}^*K ⊗ pr_{23}^*L` on `X ×_R Y ×_R Z`.
* `AlgebraicGeometry.convolutionKernel` is its direct image `K * L` along `pr_{13}`, as a
  quasi-coherent module on `X ×_R Z`.
* `AlgebraicGeometry.convolutionTripleIso` computes `F_L ∘ F_K`, for `F_L` left exact, as the
  direct image to `Z` of `pr_1^*(−) ⊗ pr_{12}^*K ⊗ pr_{23}^*L` on the triple fibre product.

## Main results

* `AlgebraicGeometry.isPullback_fourierMukaiPr12_pr13`: the square with sides `pr_{12}`, `pr_{13}`
  over the two projections to `X` is cartesian, so `pr_{13}` is a base change of
  `pr_1 : X ×_R Y ⟶ X` and hence of `Y ⟶ Spec R`.  This is what makes the convolution
  quasi-coherent under the source's hypotheses on `Y` alone.
* `AlgebraicGeometry.tensorLeftFunctorMiddleIso`: tensoring by `pr_{12}^*K` and then on the right
  by `pr_{23}^*L` is tensoring by the convolution integrand.
* `AlgebraicGeometry.exactLinearCoproductFunctor_comp`: the first step of the source's proof,
  that `G ∘ F` is again `R`-linear, exact and commuting with arbitrary direct sums.
* `AlgebraicGeometry.isIso_projectionFormulaMap_convolution`: the projection formula at
  `pr_{13}` holds at the modules pulled back from `X`, for `F_L` exact.
* `AlgebraicGeometry.quasicoherentIntegralTransformConvolutionIso`: **Tag 0GPC**, the
  composition formula `F_L ∘ F_K ≅ F_{K * L}` for `L` a kernel of category (2) of Tag 0FZH.
* `AlgebraicGeometry.exists_integralTransformExactKernel_iso_convolutionKernel`: for `K` and `L`
  both of category (2), the kernel Tag 0FZH attaches to `F_L ∘ F_K` is isomorphic to `K * L`.

## Implementation notes

The triple fibre product and its three projections are
`AlgebraicGeometry.fourierMukaiTripleProduct` and `AlgebraicGeometry.fourierMukaiPr12`,
`AlgebraicGeometry.fourierMukaiPr23`, `AlgebraicGeometry.fourierMukaiPr13` of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition`, where they are built
for the derived composition of Tag 0FYS; they are reused here rather than built a second time,
and the cartesian square `AlgebraicGeometry.isPullback_fourierMukaiPr12_pr23` the base-change
step needs is proved there.

The comparison is an isomorphism of functors between categories of quasi-coherent modules, so
naturality in the input module is part of the datum.  It is obtained by lifting an isomorphism
of the pullback--tensor--pushforward formulae of Tag 0FZB through the fully faithful inclusion
of the quasi-coherent modules of the target, using the comparison isomorphism of
`AlgebraicGeometry.IntegralTransformData`, exactly as the change-of-space isomorphisms of
Tag 0FZF are.

The chain of comparisons is the one of the derived statement Tag 0FYS: base change along the
cartesian square relating `pr_{12}` and `pr_{23}`, the projection formula at `pr_{23}` and the
projection formula at `pr_{13}`.  None of the three morphisms is affine in the generality of the
tag, and none of the three comparisons is invertible on all quasi-coherent modules.  The source's
proof instead computes sections over `U ×_R W` for affine opens `U ⊆ X`, `W ⊆ Z`, where the
morphisms become affine (Tags 02KG and 0FZE).  This file follows the same localisation in
`StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ConvolutionComparison`:
the composite of the first two comparisons is invertible because both of its sides carry the
Čech diagram of an affine cover of `X` to a limit, the second side by left exactness of `F_L`,
and the projection formula at `pr_{13}` is invertible at `p^*M` because it is so over each
`p^{-1}(U)`, where `M|_U` has a presentation by free modules and the right exactness of `F_L`
supplies the cokernel step.

## References

* [Stacks Project, Tag 0GPC](https://stacks.math.columbia.edu/tag/0GPC)
* [Stacks Project, Tag 0FZH](https://stacks.math.columbia.edu/tag/0FZH)
* [Stacks Project, Tag 0FZB](https://stacks.math.columbia.edu/tag/0FZB)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

/-! ### The third cartesian square of the triple fibre product -/

section Geometry

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- **The triple fibre product is the fibre product of `X ×_S Y` and `X ×_S Z` over `X`**: the
square with sides `pr_{12}`, `pr_{13}` over the two projections to `X` is cartesian.

Together with `AlgebraicGeometry.isPullback_fourierMukaiPr12_pr23` this is the third of the three
cartesian squares the triple fibre product carries.  It exhibits `pr_{13}` as a base change of
`pr_1 : X ×_S Y ⟶ X`, which is itself a base change of `g`, and that is how the properties of
`pr_{13}` are deduced from those of `g` alone below. -/
theorem isPullback_fourierMukaiPr12_pr13 :
    IsPullback (fourierMukaiPr12 f g h) (fourierMukaiPr13 f g h) (pullback.fst f g)
      (pullback.fst f h) := by
  refine (IsPullback.of_right ?_ (fourierMukaiPr13_fst f g h)
    (IsPullback.of_hasPullback f h).flip).flip
  rw [fourierMukaiPr13_snd, pullback.condition]
  exact (IsPullback.of_hasPullback (pullback.snd f g ≫ g) h).flip

/-- The first projection of `X ×_S Y` is a base change of `g`, hence quasi-compact when `g`
is. -/
instance quasiCompact_pullbackFst_of_quasiCompact_right [QuasiCompact g] :
    QuasiCompact (pullback.fst f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f g).flip inferInstance

/-- The first projection of `X ×_S Y` is a base change of `g`, hence quasi-separated when `g`
is. -/
instance quasiSeparated_pullbackFst_of_quasiSeparated_right [QuasiSeparated g] :
    QuasiSeparated (pullback.fst f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f g).flip inferInstance

/-- `pr_{13}` is quasi-compact as soon as the middle morphism `g` is, being a base change of a
base change of `g`.  This is sharper than deducing it from all three morphisms. -/
instance quasiCompact_fourierMukaiPr13_of_quasiCompact_middle [QuasiCompact g] :
    QuasiCompact (fourierMukaiPr13 f g h) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_fourierMukaiPr12_pr13 f g h) inferInstance

/-- `pr_{13}` is quasi-separated as soon as the middle morphism `g` is, being a base change of a
base change of `g`. -/
instance quasiSeparated_fourierMukaiPr13_of_quasiSeparated_middle [QuasiSeparated g] :
    QuasiSeparated (fourierMukaiPr13 f g h) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_fourierMukaiPr12_pr13 f g h) inferInstance

/-- `pr_{13}` is affine as soon as the middle morphism `g` is, being a base change of a base
change of `g`. -/
instance isAffineHom_fourierMukaiPr13_of_isAffineHom_middle [IsAffineHom g] :
    IsAffineHom (fourierMukaiPr13 f g h) :=
  have : IsAffineHom (pullback.fst f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f g).flip inferInstance
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_fourierMukaiPr12_pr13 f g h) this

/-- The second projection of `X ×_S Y` is a base change of `f`, hence affine when `f` is. -/
instance isAffineHom_pullbackSnd_of_isAffineHom_left [IsAffineHom f] :
    IsAffineHom (pullback.snd f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f g) inferInstance

/-- `pr_{23}` is affine as soon as the outer morphism `f` is, being a base change of the second
projection of `X ×_S Y` and hence of `f`. -/
instance isAffineHom_fourierMukaiPr23_of_isAffineHom_outer [IsAffineHom f] :
    IsAffineHom (fourierMukaiPr23 f g h) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_fourierMukaiPr12_pr23 f g h) inferInstance

end Geometry

/-! ### The convolution of two kernels -/

section Convolution

variable (R : Type u) [CommRing R] (X Y Z : Over (Spec (.of R)))

/-- **The integrand of the convolution**: the module
`pr_{12}^*K ⊗_{𝒪_{X ×_R Y ×_R Z}} pr_{23}^*L` on the triple fibre product. -/
def convolutionIntegrand (K : (pullback X.hom Y.hom).Modules)
    (L : (pullback Y.hom Z.hom).Modules) :
    (fourierMukaiTripleProduct X.hom Y.hom Z.hom).Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨(fourierMukaiTripleProduct X.hom Y.hom Z.hom).presheaf, Presheaf.isSheaf_of_isSheaf_comp _
      ((fourierMukaiTripleProduct X.hom Y.hom Z.hom).presheaf) (forget₂ CommRingCat RingCat)
      ((fourierMukaiTripleProduct X.hom Y.hom Z.hom).ringCatSheaf.2)⟩).obj
      (((Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom)).obj K)))).obj
    ((Scheme.Modules.pullback (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj L)

/-- The inverse image of a quasi-coherent kernel along `pr_{12}` is quasi-coherent. -/
theorem isQuasicoherent_pullback_fourierMukaiPr12 (K : (pullback X.hom Y.hom).Modules)
    (hK : K.IsQuasicoherent) :
    (((Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom)).obj K)).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pullback _ K hK

/-- The inverse image of a quasi-coherent kernel along `pr_{23}` is quasi-coherent. -/
theorem isQuasicoherent_pullback_fourierMukaiPr23 (L : (pullback Y.hom Z.hom).Modules)
    (hL : L.IsQuasicoherent) :
    (((Scheme.Modules.pullback (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj L)).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pullback _ L hL

/-- The convolution integrand of two quasi-coherent kernels is quasi-coherent, the tensor
product of two quasi-coherent modules being quasi-coherent. -/
theorem isQuasicoherent_convolutionIntegrand (K : (pullback X.hom Y.hom).Modules)
    (L : (pullback Y.hom Z.hom).Modules) (hK : K.IsQuasicoherent) (hL : L.IsQuasicoherent) :
    (convolutionIntegrand R X Y Z K L).IsQuasicoherent := by
  have hK' := isQuasicoherent_pullback_fourierMukaiPr12 R X Y Z K hK
  have hL' := isQuasicoherent_pullback_fourierMukaiPr23 R X Y Z L hL
  show ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace)).presheaf,
        (((fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace)).IsSheaf⟩).obj
      (((Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom)).obj K))).obj
      (((Scheme.Modules.pullback (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj L)))).IsQuasicoherent
  exact @AlgebraicGeometry.tensorSheaf_isQuasicoherent _ _ _ hK' hL'

variable [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]

/-- **The convolution of two quasi-coherent kernels**:
`K * L = pr_{13,*}(pr_{12}^*K ⊗ pr_{23}^*L)` on `X ×_R Z`.

It is quasi-coherent because `pr_{13}` is quasi-compact and quasi-separated, being a base change
of a base change of the middle structure morphism `Y ⟶ Spec R`; only the source's hypotheses on
`Y` are used, and nothing is assumed of `Z`. -/
def convolutionKernel (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (L : Scheme.QuasicoherentModules (pullback Y.hom Z.hom)) :
    Scheme.QuasicoherentModules (pullback X.hom Z.hom) :=
  haveI : QuasiCompact Y.hom := AlgebraicGeometry.quasiCompact_of_compactSpace Y.hom
  haveI : QuasiSeparated Y.hom :=
    AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace Y.hom
  haveI : (convolutionIntegrand R X Y Z K.obj L.obj).IsQuasicoherent :=
    isQuasicoherent_convolutionIntegrand R X Y Z K.obj L.obj K.property L.property
  ⟨(Scheme.Modules.pushforward (fourierMukaiPr13 X.hom Y.hom Z.hom)).obj
      (convolutionIntegrand R X Y Z K.obj L.obj),
    pushforward_isQuasicoherent (fourierMukaiPr13 X.hom Y.hom Z.hom)
      (convolutionIntegrand R X Y Z K.obj L.obj)⟩

/-- The underlying module of the convolution `K * L` is `pr_{13,*}(pr_{12}^*K ⊗ pr_{23}^*L)`. -/
@[simp]
theorem convolutionKernel_obj (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (L : Scheme.QuasicoherentModules (pullback Y.hom Z.hom)) :
    (convolutionKernel R X Y Z K L).obj =
      (Scheme.Modules.pushforward (fourierMukaiPr13 X.hom Y.hom Z.hom)).obj
        (convolutionIntegrand R X Y Z K.obj L.obj) := rfl

end Convolution

/-! ### Associativity and symmetry at the level of tensor functors -/

/-- **Tensoring by `A` and then on the right by `B` is tensoring by `A ⊗ B`.**

This is the tensor coherence the composition formula rests on: the composite transform tensors
the input module with `K` first and then with `L`, while the convolution tensors `K` with `L`
first, and the two agree by associativity together with the symmetry that exchanges the input
module with `B`. -/
def tensorLeftFunctorMiddleIso (P : Scheme.{u}) (A B : P.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨P.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf) (forget₂ CommRingCat RingCat)
        (P.ringCatSheaf.2)⟩).obj (A)) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(P.toRingedSpace).presheaf,
            (P.toRingedSpace).IsSheaf⟩).flip.obj (B)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨P.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf) (forget₂ CommRingCat RingCat)
          (P.ringCatSheaf.2)⟩).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨P.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf) (forget₂ CommRingCat RingCat)
          (P.ringCatSheaf.2)⟩).obj (A))).obj B))) :=
  Functor.isoWhiskerLeft
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨P.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf) (forget₂ CommRingCat RingCat)
          (P.ringCatSheaf.2)⟩).obj (A)))
      ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight (P).presheaf (P).ringCatSheaf.2
          (B))).symm ≪≫
    (Stacks.SheafOfModules.tensorLeftFunctorObjIso P.presheaf
      P.ringCatSheaf.2 B A).symm ≪≫
    Stacks.SheafOfModules.Invertible.tensorLeftFunctorCongr P.presheaf P.ringCatSheaf.2
      (tensorSheafSwap P.toRingedSpace B A)

/-! ### Composites of exact linear direct-sum-preserving functors -/

/-- **The first step of the proof of Tag 0GPC.**  Category (1) of Tag 0FZH is closed under
composition: if `F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` and `G : QCoh(𝒪_Y) ⥤ QCoh(𝒪_Z)` are `R`-linear,
exact and commute with arbitrary direct sums, so does `G ∘ F`.

This is the sentence the source opens its proof with, from which Tag 0FZH produces a kernel on
`X ×_R Z` for the composite; the content of the tag is that this kernel is the convolution. -/
theorem exactLinearCoproductFunctor_comp (R : Type u) [CommRing R]
    (X Y Z : Over (Spec (.of R)))
    (F : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory)
    (G : (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).FullSubcategory)
    (hF : exactLinearCoproductFunctor R X Y F)
    (hG : exactLinearCoproductFunctor R Y Z G) :
    exactLinearCoproductFunctor R X Z (F ⋙ G) := by
  let : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
  let : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
  let : Linear R (SheafOfModules.{u} Z.left.ringCatSheaf) := modulesLinear R Z
  obtain ⟨⟨hFa, hFl⟩, hFe, hFc⟩ := hF
  obtain ⟨⟨hGa, hGl⟩, hGe, hGc⟩ := hG
  have := hFa
  have := hGa
  have := hFl
  have := hGl
  refine ⟨⟨inferInstance, inferInstance⟩, (exactFunctor_iff _).mpr ⟨?_, ?_⟩, ?_⟩
  · exact @comp_preservesFiniteLimits _ _ _ _ _ _ F G ((exactFunctor_iff F).mp hFe).1
      ((exactFunctor_iff G).mp hGe).1
  · exact @comp_preservesFiniteColimits _ _ _ _ _ _ F G ((exactFunctor_iff F).mp hFe).2
      ((exactFunctor_iff G).mp hGe).2
  · intro I
    have := hFc I
    have := hGc I
    infer_instance


/-! ### The composition formula -/

/-- **The projection formula of Tag 0FZE in the target variable, as an isomorphism of
functors**, from its invertibility at the values of a functor. -/
def projectionFormulaTargetIsoOfFunctor {C : Type v} [Category.{w} C] {T S : Scheme.{u}}
    (h : T ⟶ S) (G : T.Modules) (F : C ⥤ S.Modules)
    (hpf : ∀ A, IsIso ((projectionFormulaTargetNatTrans h G).app (F.obj A))) :
    F ⋙ ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨S.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.presheaf) (forget₂ CommRingCat RingCat)
        (S.ringCatSheaf.2)⟩).obj (((Scheme.Modules.pushforward h).obj G))) ≅
      F ⋙ Scheme.Modules.pullback h ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨T.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (T.presheaf) (forget₂ CommRingCat RingCat)
            (T.ringCatSheaf.2)⟩).obj (G)) ⋙
          Scheme.Modules.pushforward h :=
  NatIso.ofComponents
    (fun A => @asIso _ _ _ _ ((projectionFormulaTargetNatTrans h G).app (F.obj A)) (hpf A))
    (fun φ => (projectionFormulaTargetNatTrans h G).naturality (F.map φ))

section Composition

variable (R : Type u) [CommRing R] (X Y Z : Over (Spec (.of R)))
  [CompactSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
  (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
  (L : Scheme.QuasicoherentModules (pullback Y.hom Z.hom))

omit [CompactSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] in
/-- The integrand of the first transform, pulled back to the triple fibre product, is
quasi-coherent. -/
theorem isQuasicoherent_integrand_pullback_pr12
    (M : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory) :
    ((((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(pullback X.hom Y.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
            (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj (K.obj)) ⋙
        Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom)).obj M)).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pullback _ _
    (isQuasicoherent_tensorLeftFunctor_pullback R X Y K M)

/-- **The composite of the two pullback--tensor--pushforward formulae, computed on the triple
fibre product.**  For `F_L` left exact,

`F_L(F_K(M)) ≅ (X ×_R Y ×_R Z ⟶ Z)_*(pr_1^* M ⊗ pr_{12}^*K ⊗ pr_{23}^*L)`,

naturally in the quasi-coherent module `M` on `X`.  The first step is the comparison at
`pr_{23}` (base change along the square relating `pr_{12}` and `pr_{23}` and the projection
formula at `pr_{23}`), invertible by `AlgebraicGeometry.isIso_pr23ComparisonNatTrans_app`; then
come the identification `pr_{23} ≫ pr_2 = pr_{13} ≫ pr_2` of the two routes to `Z`, the
compatibility of inverse image with the tensor product at `pr_{12}`, the identification
`pr_{12} ≫ pr_1 = pr_{13} ≫ pr_1` of the two routes to `X`, and the tensor coherence
`AlgebraicGeometry.tensorLeftFunctorMiddleIso`. -/
def convolutionTripleIso (hL : PreservesFiniteLimits (quasicoherentIntegralTransform R Y Z L)) :
    integralTransformFormula R X Y K.obj ⋙
        Scheme.Modules.pullback (pullback.fst Y.hom Z.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(pullback Y.hom Z.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback Y.hom Z.hom).presheaf)
            (forget₂ CommRingCat RingCat) ((pullback Y.hom Z.hom).ringCatSheaf.2)⟩).obj (L.obj)) ⋙
        Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom) ≅
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
        pullbackTargetFunctor (fourierMukaiPr13 X.hom Y.hom Z.hom)
          (convolutionIntegrand R X Y Z K.obj L.obj) :=
  have happ : ∀ M, IsIso ((Functor.whiskerLeft ((SheafOfModules.isQuasicoherent
      X.left.ringCatSheaf).ι ⋙ Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(pullback X.hom Y.hom).presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
          (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj
          (K.obj))) (pr23ComparisonNatTrans L.obj)).app M) :=
    fun M => isIso_pr23ComparisonNatTrans_app L hL
      ⟨_, isQuasicoherent_tensorLeftFunctor_pullback R X Y K M⟩
  @asIso _ _ _ _ (Functor.whiskerLeft ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
      Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(pullback X.hom Y.hom).presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
          (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj
          (K.obj))) (pr23ComparisonNatTrans L.obj))
      (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ happ) ≪≫
    Functor.isoWhiskerLeft
      ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(pullback X.hom Y.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
            (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj (K.obj)) ⋙
        Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace).presheaf,
            ((fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace).IsSheaf⟩).flip.obj
            (((Scheme.Modules.pullback (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj L.obj))))
      (Scheme.Modules.pushforwardComp (fourierMukaiPr23 X.hom Y.hom Z.hom)
            (pullback.snd Y.hom Z.hom) ≪≫
          Scheme.Modules.pushforwardCongr
            ((fourierMukaiPr23_snd X.hom Y.hom Z.hom).trans
              (fourierMukaiPr13_snd X.hom Y.hom Z.hom).symm) ≪≫
          (Scheme.Modules.pushforwardComp (fourierMukaiPr13 X.hom Y.hom Z.hom)
            (pullback.snd X.hom Z.hom)).symm) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
          Scheme.Modules.pullback (pullback.fst X.hom Y.hom))
        (pullbackTensorLeftIso (fourierMukaiPr12 X.hom Y.hom Z.hom) K.obj))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace).presheaf,
          ((fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace).IsSheaf⟩).flip.obj
          (((Scheme.Modules.pullback (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj L.obj))) ⋙
        Scheme.Modules.pushforward (fourierMukaiPr13 X.hom Y.hom Z.hom) ⋙
        Scheme.Modules.pushforward (pullback.snd X.hom Z.hom)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι
        (Scheme.Modules.pullbackComp (fourierMukaiPr12 X.hom Y.hom Z.hom)
            (pullback.fst X.hom Y.hom) ≪≫
          Scheme.Modules.pullbackCongr (fourierMukaiPr13_fst X.hom Y.hom Z.hom).symm ≪≫
          (Scheme.Modules.pullbackComp (fourierMukaiPr13 X.hom Y.hom Z.hom)
            (pullback.fst X.hom Z.hom)).symm))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨(fourierMukaiTripleProduct X.hom Y.hom Z.hom).presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _
            ((fourierMukaiTripleProduct X.hom Y.hom Z.hom).presheaf) (forget₂ CommRingCat RingCat)
          ((fourierMukaiTripleProduct X.hom Y.hom Z.hom).ringCatSheaf.2)⟩).obj
          (((Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom)).obj K.obj))) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace).presheaf,
            ((fourierMukaiTripleProduct X.hom Y.hom Z.hom).toRingedSpace).IsSheaf⟩).flip.obj
            (((Scheme.Modules.pullback (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj L.obj))) ⋙
        Scheme.Modules.pushforward (fourierMukaiPr13 X.hom Y.hom Z.hom) ⋙
        Scheme.Modules.pushforward (pullback.snd X.hom Z.hom)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
          Scheme.Modules.pullback (pullback.fst X.hom Z.hom) ⋙
          Scheme.Modules.pullback (fourierMukaiPr13 X.hom Y.hom Z.hom))
        (tensorLeftFunctorMiddleIso (fourierMukaiTripleProduct X.hom Y.hom Z.hom)
          ((Scheme.Modules.pullback (fourierMukaiPr12 X.hom Y.hom Z.hom)).obj K.obj)
          ((Scheme.Modules.pullback (fourierMukaiPr23 X.hom Y.hom Z.hom)).obj L.obj)))
      (Scheme.Modules.pushforward (fourierMukaiPr13 X.hom Y.hom Z.hom) ⋙
        Scheme.Modules.pushforward (pullback.snd X.hom Z.hom))

/-- The composite `F_K ⋙ F_L ⋙ ι` of the two integral transforms, followed by the inclusion of
the quasi-coherent modules, is the composite of the two pullback--tensor--pushforward formulae. -/
def integralTransformCompFormulaIso :
    quasicoherentIntegralTransform R X Y K ⋙ quasicoherentIntegralTransform R Y Z L ⋙
        (SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).ι ≅
      integralTransformFormula R X Y K.obj ⋙
        Scheme.Modules.pullback (pullback.fst Y.hom Z.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(pullback Y.hom Z.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback Y.hom Z.hom).presheaf)
            (forget₂ CommRingCat RingCat) ((pullback Y.hom Z.hom).ringCatSheaf.2)⟩).obj (L.obj)) ⋙
        Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom) :=
  Functor.isoWhiskerLeft (quasicoherentIntegralTransform R X Y K)
      (quasicoherentIntegralTransformData R Y Z L).comparison ≪≫
    Functor.isoWhiskerRight (quasicoherentIntegralTransformData R X Y K).comparison
      (Scheme.Modules.pullback (pullback.fst Y.hom Z.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(pullback Y.hom Z.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback Y.hom Z.hom).presheaf)
            (forget₂ CommRingCat RingCat) ((pullback Y.hom Z.hom).ringCatSheaf.2)⟩).obj (L.obj)) ⋙
        Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom))

attribute [local instance] isAffineHom_ι_affineOpens in
/-- **The projection formula at `pr_{13}` holds at the modules pulled back from `X`**, when `F_L`
is exact, although `pr_{13}` need not be affine.  By
`AlgebraicGeometry.isIso_projectionFormulaMap_pullback` it suffices that the target of the
projection-formula morphism, pushed forward to `Z`, be right exact on direct images from the
affine opens `U` of `X`; by `AlgebraicGeometry.convolutionTripleIso` that functor is
`F_L ∘ F_K ∘ (U ↪ X)_*`, and `F_K ∘ (U ↪ X)_*` is the integral transform of a kernel on the affine
`U ×_R Y` (Tag 0FZF), hence right exact. -/
theorem isIso_projectionFormulaMap_convolution
    (hL : exactFunctor _ _ (quasicoherentIntegralTransform R Y Z L))
    (M : Scheme.QuasicoherentModules X.left) :
    IsIso ((projectionFormulaTargetNatTrans (fourierMukaiPr13 X.hom Y.hom Z.hom)
      (convolutionIntegrand R X Y Z K.obj L.obj)).app
        ((Scheme.Modules.pullback (pullback.fst X.hom Z.hom)).obj M.obj)) := by
  have : QuasiCompact Y.hom := quasiCompact_of_compactSpace Y.hom
  have : QuasiSeparated Y.hom := QuasiSeparated.of_quasiSeparatedSpace Y.hom
  have hL₁ : PreservesFiniteLimits (quasicoherentIntegralTransform R Y Z L) :=
    ((exactFunctor_iff _).mp hL).1
  have hL₂ : PreservesFiniteColimits (quasicoherentIntegralTransform R Y Z L) :=
    ((exactFunctor_iff _).mp hL).2
  refine isIso_projectionFormulaMap_pullback (fourierMukaiPr13 X.hom Y.hom Z.hom)
    (convolutionIntegrand R X Y Z K.obj L.obj)
    (isQuasicoherent_convolutionIntegrand R X Y Z K.obj L.obj K.property L.property)
    (fun U => ?_) M.obj M.property
  let X' := sourceOver R X (U : X.left.Opens).ι
  have : IsAffine X'.left := U.2
  have : IsAffineHom (sourceOverHom R X (U : X.left.Opens).ι).left :=
    isAffineHom_ι_affineOpens U
  have hK' := preservesFiniteColimits_quasicoherentIntegralTransform R X' Y
    (sourceChangeKernel R X X' Y (sourceOverHom R X (U : X.left.Opens).ι) K)
  have hU : PreservesFiniteColimits
      (quasicoherentPushforward (U : X.left.Opens).ι ⋙ quasicoherentIntegralTransform R X Y K) :=
    @preservesFiniteColimits_of_natIso _ _ _ _ _ _
      (quasicoherentIntegralTransformSourceChangeIso' R X X' Y
        (sourceOverHom R X (U : X.left.Opens).ι) K).symm hK'
  have hcomp : PreservesFiniteColimits (quasicoherentPushforward (U : X.left.Opens).ι ⋙
      quasicoherentIntegralTransform R X Y K ⋙ quasicoherentIntegralTransform R Y Z L ⋙
        (SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).ι) :=
    comp_preservesFiniteColimits
      (quasicoherentPushforward (U : X.left.Opens).ι ⋙ quasicoherentIntegralTransform R X Y K)
      (quasicoherentIntegralTransform R Y Z L ⋙
        (SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).ι)
  exact @preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _ (Functor.isoWhiskerLeft
    (quasicoherentPushforward (U : X.left.Opens).ι)
      (integralTransformCompFormulaIso R X Y Z K L ≪≫ convolutionTripleIso R X Y Z K L hL₁))
    (hcomp.preservesFiniteColimits WalkingParallelPair)

/-- **The composition formula for the pullback--tensor--pushforward formulae of Tag 0FZB**, for
`F_L` exact: `AlgebraicGeometry.convolutionTripleIso` followed by the projection formula at
`pr_{13}` read backwards, which holds by
`AlgebraicGeometry.isIso_projectionFormulaMap_convolution`. -/
def integralTransformFormulaConvolutionIso
    (hL : exactFunctor _ _ (quasicoherentIntegralTransform R Y Z L)) :
    integralTransformFormula R X Y K.obj ⋙
        Scheme.Modules.pullback (pullback.fst Y.hom Z.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(pullback Y.hom Z.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback Y.hom Z.hom).presheaf)
            (forget₂ CommRingCat RingCat) ((pullback Y.hom Z.hom).ringCatSheaf.2)⟩).obj (L.obj)) ⋙
        Scheme.Modules.pushforward (pullback.snd Y.hom Z.hom) ≅
      integralTransformFormula R X Z (convolutionKernel R X Y Z K L).obj :=
  convolutionTripleIso R X Y Z K L ((exactFunctor_iff _).mp hL).1 ≪≫
    (Functor.isoWhiskerRight
      (projectionFormulaTargetIsoOfFunctor (fourierMukaiPr13 X.hom Y.hom Z.hom)
        (convolutionIntegrand R X Y Z K.obj L.obj)
        ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
          Scheme.Modules.pullback (pullback.fst X.hom Z.hom))
        (isIso_projectionFormulaMap_convolution R X Y Z K L hL))
      (Scheme.Modules.pushforward (pullback.snd X.hom Z.hom))).symm

/-- **Stacks Project, Tag 0GPC.**  Let `R` be a ring and let `X`, `Y`, `Z` be schemes over `R`,
with `X` quasi-compact with affine diagonal and `Y` quasi-compact and quasi-separated.  Let `K`
be a quasi-coherent kernel on `X ×_R Y` and `L` a quasi-coherent kernel on `Y ×_R Z` in
category (2) of Tag 0FZH, that is, flat over `Y` with vanishing higher direct images, so that its
integral transform `F_L : QCoh(𝒪_Y) ⥤ QCoh(𝒪_Z)` is `R`-linear, exact and commutes with direct
sums.  Then

`F_L ∘ F_K ≅ F_{pr_{13,*}(pr_{12}^*K ⊗ pr_{23}^*L)}`

as functors `QCoh(𝒪_X) ⥤ QCoh(𝒪_Z)`.

This is the source's statement for exact functors `F` and `G` with kernels `K` and `L`
(`G ∘ F ≅ F_L ∘ F_K`), in greater generality: nothing is assumed of `K`, and of `Y` only
quasi-compactness and quasi-separatedness.  That, when `K` is of category (2) as well, the
convolution is up to isomorphism the kernel of category (2) which Tag 0FZH attaches to `G ∘ F` is
`AlgebraicGeometry.exists_integralTransformExactKernel_iso_convolutionKernel`.

Exactness of `F_L` cannot be dropped.  Let `E` be an elliptic curve over a field `k` with origin
`o`, let `C = E ∖ {e}` for a point `e ≠ o`, `R = Γ(C, 𝒪_C)`, `X = E ×_k C` over `R`, `Y = Spec R`,
`Z = Spec k` the point `o` of `C`, `L = 𝒪_Z` on `Y ×_R Z = Z`, and `K = 𝒪(Δ - {o} × C)` on
`X ×_R Y = X`, with `Δ` the graph of `C ⊆ E`.  The fibre of `K` over `c ∈ C` is `𝒪_E(c - o)`,
nontrivial of degree zero for `c ≠ o`, so `Γ(X, K)`, a torsion-free `R`-module with zero generic
fibre, vanishes and `F_L(F_K(𝒪_X)) = 0`.  But `X ×_R Y ×_R Z = E`, the convolution kernel is
`K|_{E × {o}} ≅ 𝒪_E`, and `F_{K * L}(𝒪_X) = Γ(E, 𝒪_E) = k`.  Here `F_L = - ⊗_R k` is not left
exact. -/
@[stacks 0GPC "the composition formula F_L ∘ F_K ≅ F_{pr13,*(pr12^*K ⊗ pr23^*L)} as a natural \
isomorphism of functors QCoh(O_X) to QCoh(O_Z), for L a kernel of category (2) of 0FZH (so F_L is \
R-linear, exact and commutes with direct sums), K arbitrary, X quasi-compact with affine diagonal \
and Y quasi-compact and quasi-separated"]
def quasicoherentIntegralTransformConvolutionIso (hL : integralTransformExactKernel R Y Z L) :
    quasicoherentIntegralTransform R X Y K ⋙ quasicoherentIntegralTransform R Y Z L ≅
      quasicoherentIntegralTransform R X Z (convolutionKernel R X Y Z K L) :=
  ((SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
      _).preimageIso
    (integralTransformCompFormulaIso R X Y Z K L ≪≫
      integralTransformFormulaConvolutionIso R X Y Z K L
        (exactLinearCoproductFunctor_quasicoherentIntegralTransform R Y Z L hL).2.1 ≪≫
      (quasicoherentIntegralTransformData R X Z (convolutionKernel R X Y Z K L)).comparison.symm)

/-- **The convolution is the kernel of the composite, in the sense of Tag 0FZH.**  If `K` and `L`
are kernels of category (2) of Tag 0FZH, then the kernel of category (2) which Tag 0FZH attaches
to the `R`-linear exact direct-sum-preserving functor `F_L ∘ F_K` is isomorphic to the
convolution `pr_{13,*}(pr_{12}^*K ⊗ pr_{23}^*L)`: by
`AlgebraicGeometry.quasicoherentIntegralTransformConvolutionIso` both have integral transform
`F_L ∘ F_K`, and `K ↦ F_K` is fully faithful. -/
theorem exists_integralTransformExactKernel_iso_convolutionKernel
    (hK : integralTransformExactKernel R X Y K) (hL : integralTransformExactKernel R Y Z L) :
    ∃ M : Scheme.QuasicoherentModules (pullback X.hom Z.hom),
      integralTransformExactKernel R X Z M ∧ Nonempty (M ≅ convolutionKernel R X Y Z K L) ∧
        Nonempty (quasicoherentIntegralTransform R X Y K ⋙ quasicoherentIntegralTransform R Y Z L ≅
          quasicoherentIntegralTransform R X Z M) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_integralTransformExactKernel_iso R X Z
    (quasicoherentIntegralTransform R X Y K ⋙ quasicoherentIntegralTransform R Y Z L)
    (exactLinearCoproductFunctor_comp R X Y Z _ _
      (exactLinearCoproductFunctor_quasicoherentIntegralTransform R X Y K hK)
      (exactLinearCoproductFunctor_quasicoherentIntegralTransform R Y Z L hL))
  have := full_integralTransformQcohFunctor R X Z
  have := faithful_integralTransformQcohFunctor R X Z
  refine ⟨M, hM, ⟨(Functor.FullyFaithful.ofFullyFaithful
    (integralTransformQcohFunctor R X Z)).preimageIso
      (e.symm ≪≫ quasicoherentIntegralTransformConvolutionIso R X Y Z K L hL)⟩, ⟨e⟩⟩

end Composition

end AlgebraicGeometry

end
