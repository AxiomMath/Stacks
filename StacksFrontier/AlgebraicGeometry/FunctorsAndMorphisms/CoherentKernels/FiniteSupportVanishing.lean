module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentKernels.Defs
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic

/-!
# Kernels with support finite over the target

Let `k` be a field, let `X` and `Y` be schemes over `k`, and let `𝒦` be a quasi-coherent module
of finite type on `X ×_k Y` whose scheme-theoretic support `Z` is finite over `Y`. The proof of
[Stacks, Tag 0FZN] uses two facts about such a kernel, both proved here.

* For every quasi-coherent `𝒪_X`-module `ℱ`, the integrand `pr_1^*ℱ ⊗ 𝒦` is a direct image from
  `Z`, and so has no higher direct images along `pr_2`, the composite `Z ⟶ Y` being finite and
  hence affine. Together with flatness over `X` this places the kernels of category (2) of
  Tag 0FZN among the kernels of category (2) of Tag 0FZH.
* If moreover `X` and `Y` are locally of finite type over `k`, the integral transform of a
  coherent module is coherent.

## Main results

* `AlgebraicGeometry.CoherentKernels.pushforward_essImage_tensorSheaf`: along a closed immersion
  `i`, the tensor product `𝒦 ⊗ 𝒩` lies in the essential image of `i_*` as soon as `𝒦` does.
* `AlgebraicGeometry.CoherentKernels.integralTransformIntegrand_mem_essImage_pushforward`: the
  integrand `pr_1^*ℱ ⊗ 𝒦` is a direct image from the scheme-theoretic support of `𝒦`.
* `AlgebraicGeometry.CoherentKernels.isZero_rightDerived_integrand_of_hasFiniteSupportOver`:
  for `𝒦` with support finite over `Y`, `R^q pr_{2,*}(pr_1^*ℱ ⊗ 𝒦) = 0` for `q > 0`.
* `AlgebraicGeometry.CoherentKernels.integralTransformExactKernel_of_finiteFlatCoherentKernel`:
  every kernel of category (2) of Tag 0FZN satisfies the two conditions of Tag 0FZH.
* `AlgebraicGeometry.CoherentKernels.isCoherent_integralTransformFormula_of_hasFiniteSupportOver`:
  for `X` and `Y` locally of finite type over `k`, the integral transform of a coherent module by
  a kernel with support finite over `Y` is coherent.

## Implementation notes

That a function killing `𝒦` kills `𝒩 ⊗ 𝒦` is
`Stacks.AffineProjectionFormula.smul_tensorSheaf_eq_zero`, a stalkwise argument; the essential
image of direct image along a closed immersion is characterised by
`Stacks.ClosedImmersion.pushforward_essImage_iff`. The integrand is then the direct image of its
own restriction to the support, through the unit of the pullback--pushforward adjunction, and
the higher direct images along `Z ⟶ X ×_k Y ⟶ Y` are computed by
`Stacks.AlgebraicGeometry.ProperSupportCoherent.rightDerivedPushforwardCompIso`.

## References

* [Stacks Project, Tag 0FZN](https://stacks.math.columbia.edu/tag/0FZN)
* [Stacks Project, Tag 0FZH](https://stacks.math.columbia.edu/tag/0FZH)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.CoherentKernels

/-! ### Tensor products of direct images from a closed subscheme -/

/-- **A tensor product with a direct image from a closed subscheme is again one.** If `𝒦` lies in
the essential image of direct image along a closed immersion `i`, so does `𝒦 ⊗ 𝒩` for every
module `𝒩`: a function killed by `i` kills `𝒦` on every smaller open, hence kills the tensor
product. -/
theorem pushforward_essImage_tensorSheaf {W Z : Scheme.{u}} (i : W ⟶ Z) [IsClosedImmersion i]
    (K N : Z.Modules) (hK : (Scheme.Modules.pushforward i).essImage K) :
    (Scheme.Modules.pushforward i).essImage
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩).obj (K)).obj (N))) := by
  have hK' := (Stacks.ClosedImmersion.pushforward_essImage_iff i K).mp hK
  refine (Stacks.ClosedImmersion.pushforward_essImage_iff i _).mpr fun U a ha s => ?_
  refine Stacks.AffineProjectionFormula.smul_tensorSheaf_eq_zero K N U a
    (fun V hVU m => hK' V _ ?_ m) s
  have h := congrArg (fun φ => φ.hom a) (i.naturality (homOfLE hVU).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [h, ha, map_zero]

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k)))

/-- **The integrand is a direct image from the support of the kernel.** For a quasi-coherent
module `𝒦` of finite type on `X ×_k Y` and a quasi-coherent module `ℱ` on `X`, the integrand
`pr_1^*ℱ ⊗ 𝒦` lies in the essential image of direct image along the closed immersion of the
scheme-theoretic support of `𝒦`. -/
theorem integralTransformIntegrand_mem_essImage_pushforward
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    [K.obj.IsFiniteType]
    (M : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory) :
    (Scheme.Modules.pushforward (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι).essImage
      ((integralTransformIntegrand k X Y K).obj M) :=
  pushforward_essImage_tensorSheaf _ K.obj _
    ((Stacks.ClosedImmersion.pushforward_essImage_iff _ K.obj).mpr
      (Scheme.Modules.smul_eq_zero_of_subschemeι_app_eq_zero K.obj))

/-- **The integrand is the direct image of its restriction to the support of the kernel**: the
unit of the pullback--pushforward adjunction along the closed immersion of the scheme-theoretic
support of `𝒦` is an isomorphism at `pr_1^*ℱ ⊗ 𝒦`. -/
def integralTransformIntegrandSupportIso
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    [K.obj.IsFiniteType]
    (M : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory) :
    (integralTransformIntegrand k X Y K).obj M ≅
      (Scheme.Modules.pushforward (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι).obj
        ((Scheme.Modules.pullback (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι).obj
          ((integralTransformIntegrand k X Y K).obj M)) :=
  have := Stacks.ClosedImmersion.full_pushforward
    (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι
  have := Stacks.ClosedImmersion.faithful_pushforward
    (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι
  have := (Adjunction.isIso_unit_app_iff_mem_essImage (Scheme.Modules.pullbackPushforwardAdjunction
    (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι)).mpr
      (integralTransformIntegrand_mem_essImage_pushforward k X Y K M)
  asIso ((Scheme.Modules.pullbackPushforwardAdjunction
    (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι).unit.app
      ((integralTransformIntegrand k X Y K).obj M))

/-- The integrand `pr_1^*ℱ ⊗ 𝒦` of a quasi-coherent kernel is quasi-coherent. -/
theorem isQuasicoherent_integralTransformIntegrand
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (M : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory) :
    ((integralTransformIntegrand k X Y K).obj M).IsQuasicoherent := by
  have hpb : ((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj M.obj).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (pullback.fst X.hom Y.hom).toLRSHom.toShHom M.obj M.property
  change (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(pullback X.hom Y.hom).toRingedSpace.presheaf,
        (pullback X.hom Y.hom).toRingedSpace.IsSheaf⟩).obj K.obj).obj
      ((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj M.obj)).IsQuasicoherent
  exact @AlgebraicGeometry.tensorSheaf_isQuasicoherent _ K.obj _ K.property hpb

/-- The support inclusion of a kernel with support finite over `Y` is finite over `Y`. -/
private theorem isFinite_subschemeι_comp_snd (K : (pullback X.hom Y.hom).Modules)
    [K.IsQuasicoherent] [K.IsFiniteType] (hK : HasFiniteSupportOver k X Y K) :
    IsFinite ((Scheme.Modules.schemeTheoreticSupport K).subschemeι ≫ pullback.snd X.hom Y.hom) :=
  hK

/-- **The integrand of a kernel with support finite over `Y` has no higher direct images along
the second projection.** The integrand is the direct image of a quasi-coherent module on the
scheme-theoretic support `Z` of `𝒦`, so its higher direct images along `pr_2` are those along the
finite, hence affine, morphism `Z ⟶ Y`, which vanish in positive degrees. -/
theorem isZero_rightDerived_integrand_of_hasFiniteSupportOver
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    [K.obj.IsFiniteType] (hK : HasFiniteSupportOver k X Y K.obj)
    (M : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory) (q : ℕ)
    (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived q).obj
      ((integralTransformIntegrand k X Y K).obj M)) := by
  have := isFinite_subschemeι_comp_snd k X Y K.obj hK
  have := isQuasicoherent_integralTransformIntegrand k X Y K M
  refine IsZero.of_iso ?_ (((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived
    q).mapIso (integralTransformIntegrandSupportIso k X Y K M) ≪≫
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.rightDerivedPushforwardCompIso
        (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι (pullback.snd X.hom Y.hom)
        _ q).symm)
  exact Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward _ _ q hq

/-- **The kernels of Tag 0FZN satisfy the conditions of Tag 0FZH.** A coherent kernel on
`X ×_k Y` which is flat over `X` and whose support is finite over `Y` is flat over `X` and has an
integrand with no positive higher direct images along the second projection. -/
theorem integralTransformExactKernel_of_finiteFlatCoherentKernel
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (hK : finiteFlatCoherentKernel k X Y K) : integralTransformExactKernel k X Y K := by
  obtain ⟨h, hflat, hfin⟩ := hK
  have : K.obj.IsFiniteType := h.isFiniteType
  exact ⟨hflat, fun M q hq => isZero_rightDerived_integrand_of_hasFiniteSupportOver k X Y K hfin
    M q hq⟩

/-- **The integral transform of a coherent module by a kernel with support finite over `Y` is
coherent**, for `X` and `Y` locally of finite type over `k`. The product `X ×_k Y` is locally
Noetherian, so the integrand `pr_1^*ℱ ⊗ 𝒦` is coherent, and so is its restriction to the
scheme-theoretic support `Z` of `𝒦`; the integral transform is the direct image of the latter
along the finite morphism `Z ⟶ Y`, whose direct images preserve coherence. -/
theorem isCoherent_integralTransformFormula_of_hasFiniteSupportOver
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    [K.obj.IsFiniteType] (hK : HasFiniteSupportOver k X Y K.obj)
    (M : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory)
    (hM : M.obj.IsCoherent) :
    ((integralTransformFormula k X Y K.obj).obj M).IsCoherent := by
  have := isFinite_subschemeι_comp_snd k X Y K.obj hK
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : IsLocallyNoetherian (pullback X.hom Y.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst X.hom Y.hom)
  have : IsLocallyNoetherian (Scheme.Modules.schemeTheoreticSupport K.obj).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι
  have hK : K.obj.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType K.obj
  have hpb : ((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj M.obj).IsCoherent :=
    isCoherent_pullback (pullback.fst X.hom Y.hom) M.obj
  have hE : ((integralTransformIntegrand k X Y K).obj M).IsCoherent :=
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent (pullback X.hom Y.hom).toRingedSpace
      K.obj ((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj M.obj) hK hpb
  have hG : ((Scheme.Modules.pullback (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι).obj
      ((integralTransformIntegrand k X Y K).obj M)).IsCoherent :=
    isCoherent_pullback _ _
  have hP : ((Scheme.Modules.pushforward
      ((Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι ≫ pullback.snd X.hom Y.hom)).obj
        ((Scheme.Modules.pullback (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι).obj
          ((integralTransformIntegrand k X Y K).obj M))).IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite _ _
  let e : (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj
        ((integralTransformIntegrand k X Y K).obj M) ≅
      (Scheme.Modules.pushforward
        ((Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι ≫ pullback.snd X.hom Y.hom)).obj
        ((Scheme.Modules.pullback (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι).obj
          ((integralTransformIntegrand k X Y K).obj M)) :=
    (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).mapIso
      (integralTransformIntegrandSupportIso k X Y K M) ≪≫
      (Scheme.Modules.pushforwardComp (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι
        (pullback.snd X.hom Y.hom)).app
        ((Scheme.Modules.pullback (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι).obj
          ((integralTransformIntegrand k X Y K).obj M))
  exact @Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso _ _ _ _ _ e hP

end AlgebraicGeometry.CoherentKernels

end
