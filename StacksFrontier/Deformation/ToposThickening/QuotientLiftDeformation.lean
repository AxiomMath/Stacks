module

public import StacksFrontier.Deformation.ToposThickening.QuotientLiftObstructionCriterion

/-!
# The lifts of a quotient across a first order thickening of ringed topoi (Stacks 0CZV)

Let `(f, f')` be a strict morphism of first order thickenings of ringed topoi, let `ℱ'` be an
`O'`-module flat over `O_{ℬ'}`, and let `𝒦 ⊂ ℱ = i^*ℱ'` be the kernel of a quotient `ℱ ⟶ 𝒬` with
`𝒬` flat over `O_ℬ`. This file describes the lifts of the quotient attached to the maps
`π⁻¹(𝒦) ⟶ 𝒬 ⊗ f^*𝒥` extending the canonical map `I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥`.

## Main results

* `Deformation.ToposThickening.isQuotientLift_extensionKernelIn` and
  `Deformation.ToposThickening.exists_extensionKernelIn_eq_of_isQuotientLift`: the subobject cut
  out by such a map is a lift of the quotient, and every lift is of this form.
* `Deformation.ToposThickening.exists_addTorsor_quotientLift`: **the topos form of Stacks 0CZV**
  — once the obstruction of Stacks 0CZU vanishes, the lifts form a principal homogeneous space
  under `Hom_O(𝒦, 𝒬 ⊗ f^*𝒥)`, with the action of the remark.

## References

* [Stacks Project, Tag 0CZV](https://stacks.math.columbia.edu/tag/0CZV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' vS uS wS vS' uS' wS' e

namespace Deformation.ToposThickening

section QuotientLiftDeformation

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap)

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
  (K : Subobject ((pullbackModules i.toRingedToposModulesHom).obj F'))


/-- The inclusion `π⁻¹(𝒦) ⟶ ℱ'` is a monomorphism, as a pullback of the direct image of the
monomorphism `𝒦 ⟶ ℱ`, the direct image being a right adjoint. -/
instance instMonoQuotientLiftPreimageι : Mono (quotientLiftPreimageι i F' K) := by
  have : i.pushforwardModules.IsRightAdjoint :=
    ⟨_, ⟨i.pullbackAdjPushforwardModulesViaComparison⟩⟩
  exact inferInstanceAs (Mono (pullback.snd _ _))

omit [HasWeakSheafify S.J AddCommGrpCat] [S.J.WEqualsLocallyBijective AddCommGrpCat] in
include comm in
/-- The lift of `𝒦` attached to a map `d : π⁻¹(𝒦) ⟶ M` extending `c` is flat over `O_{ℬ'}`. -/
theorem isFlat_cokernel_extensionKernelIn
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    (hQ : IsFlatOverBase i f ((pushforwardModuleFunctor i.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj (cokernel K.arrow)))
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)}
    (c : (quotientLiftPreimageShortComplex i hi F' K).X₁ ⟶ M) [Epi c]
    (a' : (idealTensorFunctor hi).obj (quotientLiftPreimage i F' K) ⟶
      (idealProductSubmodule hi F').toSheafOfModules)
    (ha' : a' ≫ (idealProductSubmodule hi F').ι =
      (idealTensorFunctor hi).map (quotientLiftPreimageι i F' K) ≫ (idealAction hi).app F')
    (hac : a' ≫ c = 0) (hc : IsColimit (CokernelCofork.ofπ c hac))
    (d : ExtensionAlong (quotientLiftPreimageShortComplex i hi F' K) c) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj
        (cokernel (extensionKernelIn (quotientLiftPreimageι i F' K) d).arrow)) := by
  have hS := quotientLiftPreimageShortComplex_shortExact i hi F' K
  have h := isFlat_cokernel_of_isExtensionKernel i t f f' hi ht comm F' K hstrict hflat hQ c a'
    ha' hac hc (kernelSubobject d.val) (isExtensionKernel_kernelSubobject hS d)
  have : Mono ((kernelSubobject d.val).arrow ≫ quotientLiftPreimageι i F' K) :=
    inferInstance
  have e : cokernel ((kernelSubobject d.val).arrow ≫ quotientLiftPreimageι i F' K) ≅
      cokernel (extensionKernelIn (quotientLiftPreimageι i F' K) d).arrow :=
    (cokernelEpiComp (Subobject.underlyingIso
        ((kernelSubobject d.val).arrow ≫ quotientLiftPreimageι i F' K)).hom _).symm ≪≫
      cokernelIsoOfEq (Subobject.underlyingIso_hom_comp_eq_mk _)
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
    ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).mapIso e) h

include comm in
/-- The lift of `𝒦` attached to a map `d : π⁻¹(𝒦) ⟶ 𝒬 ⊗ f^*𝒥` extending the canonical map
`I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥` is a lift of the quotient: `ℱ'/𝒦'` is flat over `O_{ℬ'}` and `𝒦'` reduces to
`𝒦`. -/
theorem isQuotientLift_extensionKernelIn
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    (hQ : IsFlatOverBase i f ((pushforwardModuleFunctor i.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj (cokernel K.arrow)))
    (d : ExtensionAlong (quotientLiftPreimageShortComplex i hi F' K)
      (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)) :
    IsQuotientLift i f' F' K (extensionKernelIn (quotientLiftPreimageι i F' K) d) := by
  have := epi_quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K
  have hS := quotientLiftPreimageShortComplex_shortExact i hi F' K
  have h1 := isFlat_cokernel_extensionKernelIn i t f f' hi ht
    comm F' K hstrict hflat hQ _ _ (quotientLiftIdealAction_comp_ι i hi F' K)
    (quotientLiftIdealAction_comp_canonicalMap i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftCanonicalMap_isColimit i t f f' hi ht comm F' hstrict hflat K) d
  have h2 := exists_factor_extensionKernelIn (quotientLiftPreimageι i F' K) hS d
  exact (isQuotientLift_iff i f' hi F' K _).2 ⟨h1, h2⟩

include comm in
/-- Every lift of the quotient is the lift attached to a map extending the canonical map. -/
theorem exists_extensionKernelIn_eq_of_isQuotientLift
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    {K' : Subobject F'} (hK' : IsQuotientLift i f' F' K K') :
    ∃ d : ExtensionAlong (quotientLiftPreimageShortComplex i hi F' K)
        (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K),
      extensionKernelIn (quotientLiftPreimageι i F' K) d = K' := by
  have := epi_quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K
  have hS := quotientLiftPreimageShortComplex_shortExact i hi F' K
  obtain ⟨K'', hmap, hK''⟩ :=
    isExtensionKernel_of_isQuotientLift i t f f' hi ht comm F' hstrict hflat K hK'
  obtain ⟨d, hd⟩ := exists_extensionAlong_of_isExtensionKernel hS hK''
  exact ⟨d, by rwa [extensionKernelIn, kernelSubobjectIn_eq_map, hd]⟩

include comm in
/-- A lift of the quotient contains the image of `𝒦 ⊗ f^*𝒥`: the kernel of the canonical map
`I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥`, viewed in `ℱ'`, lies in every lift. -/
theorem factors_of_isQuotientLift
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    {K' : Subobject F'} (hK' : IsQuotientLift i f' F' K K') :
    K'.Factors (kernel.ι (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K) ≫
      (quotientLiftPreimageShortComplex i hi F' K).f ≫ quotientLiftPreimageι i F' K) := by
  have := epi_quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K
  obtain ⟨d, rfl⟩ := exists_extensionKernelIn_eq_of_isQuotientLift i t f f' hi ht comm F' K
    hstrict hflat hK'
  exact factors_extensionKernelIn (quotientLiftPreimageι i F' K) d

/-- The direct image along a first order thickening, on morphisms, as an isomorphism of groups:
it is fully faithful (Stacks 08M3) and additive. -/
noncomputable def pushforwardModulesHomAddEquiv
    (A₁ A₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (A₁ ⟶ A₂) ≃+ (i.pushforwardModules.obj A₁ ⟶ i.pushforwardModules.obj A₂) :=
  have ff := (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some
  have := preservesFiniteLimits_pushforwardModules hi
  have : i.pushforwardModules.Additive := Functor.additive_of_preserves_binary_products _
  AddEquiv.ofBijective i.pushforwardModules.mapAddHom
    ⟨fun _ _ h => ff.map_injective h, fun g => ⟨ff.preimage g, ff.map_preimage g⟩⟩

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- `Deformation.ToposThickening.pushforwardModulesHomAddEquiv` is the direct image on
morphisms. -/
theorem pushforwardModulesHomAddEquiv_apply
    {A₁ A₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : A₁ ⟶ A₂) :
    pushforwardModulesHomAddEquiv i hi A₁ A₂ φ = i.pushforwardModules.map φ :=
  rfl

attribute [local instance] epi_quotientLiftCanonicalMap

/-- The reduction `ℱ'/𝒦' ⟶ i_*𝒬` of a subobject `𝒦'` of `ℱ'` lying in `π⁻¹(𝒦)`: the map induced by
`ℱ' ⟶ i_*ℱ ⟶ i_*𝒬`. -/
noncomputable def liftQuotientReduction (K' : Subobject F')
    (h : (K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ⟶
      quotientLiftPreimage i F' K) (hh : h ≫ quotientLiftPreimageι i F' K = K'.arrow) :
    cokernel K'.arrow ⟶ i.pushforwardModules.obj (cokernel K.arrow) :=
  cokernel.desc _ (i.pullbackAdjPushforwardModulesViaComparison.unit.app F' ≫
    i.pushforwardModules.map (cokernel.π K.arrow)) (by
      rw [← hh, Category.assoc, ← Category.assoc (quotientLiftPreimageι i F' K),
        ← pullback.condition, Category.assoc, ← Functor.map_comp, cokernel.condition,
        Functor.map_zero, comp_zero, comp_zero])

include comm in
/-- **The lift attached to `d` is an extension of `i_*𝒬` by `i_*(𝒬 ⊗ f^*𝒥)`**: the sequence
`0 ⟶ 𝒬 ⊗ f^*𝒥 ⟶ ℱ'/𝒦' ⟶ 𝒬 ⟶ 0` of the remark's diagram (the right column) is short exact, the
first map being the inclusion `Deformation.ToposThickening.extensionInclusion`. -/
theorem extensionKernelIn_quotient_shortExact
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    (d : ExtensionAlong (quotientLiftPreimageShortComplex i hi F' K)
      (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K))
    {K₀ : Subobject F'}
    (_hK₀ : extensionKernelIn (S := quotientLiftPreimageShortComplex i hi F' K)
      (c := quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)
      (quotientLiftPreimageι i F' K) d = K₀)
    (h : (K₀ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ⟶
        quotientLiftPreimage i F' K)
    (hh : h ≫ quotientLiftPreimageι i F' K = K₀.arrow)
    (ι : i.pushforwardModules.obj ((baseIdealTensor t f ht).obj (cokernel K.arrow)) ⟶
      cokernel K₀.arrow)
    (hι : d.val ≫ ι = quotientLiftPreimageι i F' K ≫ cokernel.π K₀.arrow) [Mono ι]
    (hzero : ι ≫ liftQuotientReduction i F' K K₀ h hh = 0) :
    (ShortComplex.mk _ _ hzero).ShortExact := by
  have hp : cokernel.π K₀.arrow ≫ liftQuotientReduction i F' K K₀ h hh =
      i.pullbackAdjPushforwardModulesViaComparison.unit.app F' ≫
        i.pushforwardModules.map (cokernel.π K.arrow) := cokernel.π_desc _ _ _
  have := preservesFiniteLimits_pushforwardModules hi
  have := preservesFiniteColimits_pushforwardModules hi
  let SK := ShortComplex.mk K.arrow (cokernel.π K.arrow) (cokernel.condition _)
  have hSK : SK.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) inferInstance inferInstance
  have hRSK : (SK.map i.pushforwardModules).ShortExact := hSK.map_of_exact _
  have := hRSK.epi_g
  have := epi_pullbackAdjPushforward_unit_app hi F'
  refine ShortComplex.ShortExact.mk' ?_ inferInstance ?_
  · rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x₂ hx₂
    change x₂ ≫ liftQuotientReduction i F' K K₀ h hh = 0 at hx₂
    obtain ⟨A₁, p₁, hp₁, y, hy⟩ := surjective_up_to_refinements_of_epi
      (cokernel.π K₀.arrow) x₂
    have hy0 : (y ≫ i.pullbackAdjPushforwardModulesViaComparison.unit.app F') ≫
        i.pushforwardModules.map (cokernel.π K.arrow) = 0 := by
      rw [Category.assoc, ← hp, ← Category.assoc, ← hy, Category.assoc, hx₂, comp_zero]
    obtain ⟨A₂, p₂, hp₂, k, hk⟩ := hRSK.exact.exact_up_to_refinements _ hy0
    change p₂ ≫ y ≫ i.pullbackAdjPushforwardModulesViaComparison.unit.app F' =
      k ≫ i.pushforwardModules.map K.arrow at hk
    let l : A₂ ⟶ quotientLiftPreimage i F' K := pullback.lift k (p₂ ≫ y)
      (by rw [← hk, Category.assoc])
    have hl : l ≫ quotientLiftPreimageι i F' K = p₂ ≫ y := pullback.lift_snd _ _ _
    refine ⟨A₂, p₂ ≫ p₁, inferInstance, l ≫ d.val, ?_⟩
    change (p₂ ≫ p₁) ≫ x₂ = (l ≫ d.val) ≫ ι
    rw [Category.assoc, hy, ← Category.assoc, ← hl, Category.assoc, Category.assoc, hι]
  · have : Epi (i.pullbackAdjPushforwardModulesViaComparison.unit.app F' ≫
        i.pushforwardModules.map (cokernel.π K.arrow)) := epi_comp _ _
    rw [← hp] at this
    exact epi_of_epi (cokernel.π K₀.arrow) (liftQuotientReduction i F' K K₀ h hh)

include comm in
/-- **Every lift `𝒬'` of the quotient is an extension of `i_*𝒬` by `i_*(𝒬 ⊗ f^*𝒥)`**: for a lift
`𝒦' ⊂ ℱ'` there is a short exact sequence `0 ⟶ i_*(𝒬 ⊗ f^*𝒥) ⟶ ℱ'/𝒦' ⟶ i_*𝒬 ⟶ 0`, the right
column of the diagram of the remark of Stacks 0CZV. -/
theorem exists_shortExact_cokernel_of_isQuotientLift
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    {K' : Subobject F'} (hK' : IsQuotientLift i f' F' K K') :
    ∃ (ι : i.pushforwardModules.obj ((baseIdealTensor t f ht).obj (cokernel K.arrow)) ⟶
        cokernel K'.arrow) (p : cokernel K'.arrow ⟶ i.pushforwardModules.obj (cokernel K.arrow))
      (w : ι ≫ p = 0), (ShortComplex.mk ι p w).ShortExact := by
  have hS := quotientLiftPreimageShortComplex_shortExact i hi F' K
  obtain ⟨d, hd⟩ := exists_extensionKernelIn_eq_of_isQuotientLift i t f f' hi ht comm F' K
    hstrict hflat hK'
  obtain ⟨h, hh, -⟩ := ((isQuotientLift_iff i f' hi F' K K').1 hK').2
  obtain ⟨ι, hmono, hι, hc⟩ := exists_mono_extensionInclusion
    (S := quotientLiftPreimageShortComplex i hi F' K)
    (c := quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftPreimageι i F' K) hS d hd
  have hN : (quotientLiftPreimageShortComplex i hi F' K).f ≫ quotientLiftPreimageι i F' K =
      (idealProductSubmodule hi F').ι := pullback.lift_snd _ _ _
  have hzero : ι ≫ liftQuotientReduction i F' K K' h hh = 0 := by
    rw [← cancel_epi (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K), comp_zero,
      ← Category.assoc, hc]
    simp only [liftQuotientReduction, Category.assoc, cokernel.π_desc]
    rw [reassoc_of% hN, reassoc_of% idealProductSubmodule_unit_comp_zero hi F', zero_comp]
  exact ⟨_, _, hzero, extensionKernelIn_quotient_shortExact i t f f' hi ht comm F' K hstrict hflat
    d hd h hh _ hι hzero⟩

include comm in
/-- **The lifts of a quotient across a strict first order thickening of ringed topoi form a
principal homogeneous space under `Hom_O(𝒦, 𝒬 ⊗ f^*𝒥)`** — the topos form of Stacks 0CZV, which
the remark notes works in this generality. Here `(f, f')` is strict, `ℱ'` is flat over `O_{ℬ'}`,
`𝒦 ⊂ ℱ = i^*ℱ'` is the kernel of a quotient `𝒬 = ℱ/𝒦` flat over `O_ℬ`, and the obstruction of
Stacks 0CZU vanishes.

The action is the remark's: `φ` sends a lift `𝒦'` (with quotient `𝒬' = ℱ'/𝒦'`) to the subsheaf
`𝒦'_φ ⊂ ℱ'` of the sections `s` whose image in `ℱ` is a section `k` of `𝒦` and whose image in
`𝒬'` is `φ(k)`, read in `𝒬'` through the inclusion `𝒬 ⊗ f^*𝒥 ⊂ 𝒬'` of the remark's diagram
(`Deformation.ToposThickening.extensionInclusion`); this is
`Deformation.ToposThickening.extensionDeformation`, the kernel on `π⁻¹(𝒦)` of
`s ↦ (s mod 𝒦') - φ(π(s))`. -/
theorem exists_addTorsor_quotientLift
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    (hQ : IsFlatOverBase i f ((pushforwardModuleFunctor i.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj (cokernel K.arrow)))
    (ho : quotientLiftObstruction.{_, _, _, _, _, _, _, _, _, _, _, e} i t f f' hi ht comm F'
      hstrict hflat K = 0) :
    ∃ T : AddTorsor ((K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
        (baseIdealTensor t f ht).obj (cokernel K.arrow))
        {K' : Subobject F' // IsQuotientLift i f' F' K K'},
      ∀ (φ : (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
          (baseIdealTensor t f ht).obj (cokernel K.arrow))
        (K' : {K' : Subobject F' // IsQuotientLift i f' F' K K'}),
        (T.vadd φ K').val = extensionDeformation (S := quotientLiftPreimageShortComplex i hi F' K)
          (c := quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)
          (quotientLiftPreimageι i F' K) K'.val
          (factors_of_isQuotientLift i t f f' hi ht comm F' K hstrict hflat K'.property)
          (i.pushforwardModules.map φ) := by
  have := epi_quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K
  have hS := quotientLiftPreimageShortComplex_shortExact i hi F' K
  obtain ⟨K₁, hK₁⟩ := (quotientLiftObstruction_eq_zero_iff i t f f' hi ht comm F' hstrict hflat
    K hQ).1 ho
  obtain ⟨T, hT⟩ := exists_addTorsor_extensionKernelIn
    (S := quotientLiftPreimageShortComplex i hi F' K)
    (c := quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftPreimageι i F' K) hS
    (pushforwardModulesHomAddEquiv i hi
      (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((baseIdealTensor t f ht).obj (cokernel K.arrow)))
    (IsQuotientLift i f' F' K)
    (isQuotientLift_extensionKernelIn i t f f' hi ht comm F' K hstrict hflat hQ)
    (fun _ hK' => exists_extensionKernelIn_eq_of_isQuotientLift i t f f' hi ht comm F' K
      hstrict hflat hK') ⟨⟨K₁, hK₁⟩⟩
  exact ⟨T, fun φ K' => hT φ K' _⟩

end QuotientLiftDeformation

end Deformation.ToposThickening

end
