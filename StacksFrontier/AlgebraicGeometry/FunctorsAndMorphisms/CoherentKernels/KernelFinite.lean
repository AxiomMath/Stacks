module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentKernels.KernelCoherent
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.EquivalenceOverField
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.FinitenessCriterion

/-!
# Quasi-finite support of an exact kernel is finite

Let `k` be a field and let `X` and `Y` be schemes of finite type over `k` with `X` separated. Let
`𝒦` be a coherent kernel on `X ×_k Y` satisfying the two conditions of [Stacks, Tag 0FZH]. If
the scheme-theoretic support `Z` of `𝒦` is quasi-finite over `Y` and `F_𝒦(𝒪_X)` is coherent,
then `Z` is finite over `Y`. This is the last step of the proof of [Stacks, Tag 0FZN]: `𝒦` is the
direct image of a coherent module of full support on `Z`, whose direct image to `Y` is
`pr_{2,*}𝒦 = F_𝒦(𝒪_X)` and whose higher direct images vanish, so [Stacks, Tag 0FZM] applies.

## Main results

* `AlgebraicGeometry.CoherentKernels.integralTransformIntegrandUnitIso`: the integrand of the
  structure sheaf is the kernel.
* `AlgebraicGeometry.CoherentKernels.hasFiniteSupportOver_of_locallyQuasiFinite`.

## References

* [Stacks Project, Tag 0FZN](https://stacks.math.columbia.edu/tag/0FZN)
* [Stacks Project, Tag 0FZM](https://stacks.math.columbia.edu/tag/0FZM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CoherentKernels

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k)))

/-- **The integrand of the structure sheaf is the kernel**: `pr_1^*𝒪_X ⊗ 𝒦 ≅ 𝒦`. -/
def integralTransformIntegrandUnitIso
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    (integralTransformIntegrand k X Y K).obj (⟨SheafOfModules.unit X.left.ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩ :
        (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory) ≅ K.obj := by
  let P := pullback X.hom Y.hom
  change (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨P.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf) (forget₂ CommRingCat RingCat)
        (P.ringCatSheaf.2)⟩).obj (K.obj)).obj
      (((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj
        (SheafOfModules.unit X.left.ringCatSheaf)))) ≅ K.obj
  exact Stacks.SheafOfModules.Invertible.tensorProductIso P.presheaf P.ringCatSheaf.2
      (Iso.refl K.obj) (Scheme.Modules.pullbackUnitIso (pullback.fst X.hom Y.hom)) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor P.presheaf P.ringCatSheaf.2 K.obj

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

open Stacks.AlgebraicGeometry.CoherentModuleFunctors in
/-- **A coherent kernel of [Stacks, Tag 0FZH] whose support is quasi-finite over `Y` has support
finite over `Y`**, provided `F_𝒦(𝒪_X)` is coherent. This is [Stacks, Tag 0FZM] for the support
`Z ⟶ Y`, applied to the descent of `𝒦` to `Z`. -/
theorem hasFiniteSupportOver_of_locallyQuasiFinite
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    [K.obj.IsCoherent] (hK : integralTransformExactKernel k X Y K)
    (hqf : letI : K.obj.IsQuasicoherent := K.property
      letI : K.obj.IsFiniteType := ‹K.obj.IsCoherent›.isFiniteType
      LocallyQuasiFinite ((Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι ≫
        pullback.snd X.hom Y.hom))
    (hO : letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
      ((quasicoherentIntegralTransform k X Y K).obj (⟨SheafOfModules.unit X.left.ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩ :
        (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory)).obj.IsCoherent) :
    letI : K.obj.IsQuasicoherent := K.property
    letI : K.obj.IsFiniteType := ‹K.obj.IsCoherent›.isFiniteType
    HasFiniteSupportOver k X Y K.obj := by
  let : K.obj.IsQuasicoherent := K.property
  let : K.obj.IsFiniteType := ‹K.obj.IsCoherent›.isFiniteType
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let i := (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι
  let p₂ := pullback.snd X.hom Y.hom
  have : IsNoetherian Y.left := CoherentModuleFunctors.isNoetherian_of_finiteType_over_field k Y
  have : IsNoetherian (Scheme.Modules.schemeTheoreticSupport K.obj).subscheme :=
    isNoetherian_of_locallyOfFiniteType (i ≫ p₂ ≫ Y.hom)
  have : IsLocallyNoetherian (pullback X.hom Y.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst X.hom Y.hom ≫ X.hom)
  have : LocallyQuasiFinite (i ≫ p₂) := hqf
  let K' := (Scheme.Modules.pullback i).obj K.obj
  have : K'.IsCoherent := isCoherent_pullback _ _
  let eK : (Scheme.Modules.pushforward i).obj K' ≅ K.obj :=
    Scheme.Modules.pushforwardPullbackSchemeTheoreticSupportIso K.obj
  let U : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.unit X.left.ringCatSheaf,
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩
  let e : (Scheme.Modules.pushforward i).obj K' ≅ _ :=
    eK ≪≫ (integralTransformIntegrandUnitIso k X Y K).symm
  let eO : (Scheme.Modules.pushforward (i ≫ p₂)).obj K' ≅
      ((quasicoherentIntegralTransform k X Y K).obj U).obj :=
    ((Scheme.Modules.pushforwardComp i p₂).app K').symm ≪≫
      (Scheme.Modules.pushforward p₂).mapIso e ≪≫
      ((quasicoherentIntegralTransformData k X Y K).comparison.app U).symm
  refine isFinite_of_isCoherent_pushforward_of_isZero_higherDirectImages
    (i ≫ p₂) K' (Scheme.Modules.module_on_schemeTheoreticSupport_support K.obj K' eK)
    (@Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso _ _ _ _ _ eO hO) fun q hq => ?_
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq.le
  have hn : 0 < n := by exact_mod_cast hq
  have hK' : K'.IsQuasicoherent := isQuasicoherent_of_isCoherent K'
  refine IsZero.of_iso ?_
    (Stacks.AlgebraicGeometry.ProperSupportCoherent.rightDerivedPlusPushforwardCompIso i p₂ K' n)
  refine IsZero.of_iso ?_ (Functor.mapIso _ e)
  exact IsZero.of_iso (hK.2 U n hn)
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward p₂) n).app _).symm

end AlgebraicGeometry.CoherentKernels

end
