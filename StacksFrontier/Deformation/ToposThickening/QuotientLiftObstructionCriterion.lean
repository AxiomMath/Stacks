module

public import StacksFrontier.Deformation.ToposThickening.QuotientLiftFlatness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Deformation.ToposThickening.FinitePresentationFlatLift
import StacksCore.Tactic.StacksAttribute

/-!
# The obstruction to lifting a quotient across a first order thickening vanishes exactly on lifts

Let `(f, f')` be a strict morphism of first order thickenings of ringed topoi as in
Situation 08M7, let `ℱ'` be an `O'`-module flat over `O_{ℬ'}`, `ℱ = i^*ℱ'`, and let
`0 ⟶ 𝒦 ⟶ ℱ ⟶ 𝒬 ⟶ 0` be a quotient with `𝒬` flat over `O_ℬ`. Remark 0CZU attaches to it the
class `o ∈ Ext¹_O(𝒦, 𝒬 ⊗ f^*𝒥)` of the canonical extension
`0 ⟶ 𝒬 ⊗ f^*𝒥 ⟶ π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥) ⟶ 𝒦 ⟶ 0`
(`Deformation.ToposThickening.quotientLiftObstruction`) and claims that `o = 0` if and only if the
quotient lifts to a quotient `ℱ' ⟶ 𝒬'` flat over `O_{ℬ'}`. This file proves the claim.

## Main results

* `Deformation.ToposThickening.exists_retraction_quotientLiftExtension_iff`: the extension splits
  exactly when the canonical map `c : I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥` extends to `π⁻¹(𝒦)`.
* `Deformation.ToposThickening.isExtensionKernel_of_isQuotientLift`: a lift `𝒦'` of `𝒦` lies in
  `π⁻¹(𝒦)` and meets `I·ℱ'` exactly in the kernel of `c`, which is `I·π⁻¹(𝒦)`.
* `Deformation.ToposThickening.quotientLiftObstruction_eq_zero_iff`: **`o = 0` if and only if
  the quotient lifts.**

## How the proof goes

A splitting of the extension is a map `d : π⁻¹(𝒦) ⟶ 𝒬 ⊗ f^*𝒥` extending `c`. Its kernel `𝒦'` is
a lift: `ℱ'/𝒦'` is flat by the criterion of Stacks 08MQ
(`Deformation.ToposThickening.isFlat_cokernel_of_isExtensionKernel`). Conversely, for a lift
`𝒦'` the module `π⁻¹(𝒦)/𝒦' = I·ℱ'/(𝒦' ∩ I·ℱ')` is `𝒬 ⊗ f^*𝒥`, because `𝒦' ∩ I·ℱ' = I·𝒦'`: the
pullback of `0 ⟶ 𝒦' ⟶ ℱ' ⟶ ℱ'/𝒦' ⟶ 0` stays exact, `ℱ'/𝒦'` being flat
(`Deformation.ToposThickening.shortExact_map_pullbackModules_of_isFlat`).

## References

* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)

universe v u w v' u' vS uS wS vS' uS' wS' e

namespace Deformation.ToposThickening

/-- `Subobject.mk_factors_iff`, with the source of the factorization spelled as the source of the
monomorphism. -/
theorem mk_factors_iff_exists {𝒞 : Type*} [Category 𝒞] {A B Z : 𝒞} (h : A ⟶ B) [Mono h]
    (g : Z ⟶ B) : (Subobject.mk h).Factors g ↔ ∃ y : Z ⟶ A, y ≫ h = g :=
  Subobject.mk_factors_iff h g

section QuotientLift

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
  (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
  (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
    ((SheafOfModules.restrictScalars
      ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        f'.fSharpInverseImage)).obj F'))
  (K : Subobject ((pullbackModules i.toRingedToposModulesHom).obj F'))

/-- **The canonical extension splits exactly when `c` extends to `π⁻¹(𝒦)`**: a retraction of
`𝒬 ⊗ f^*𝒥 ⟶ π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥)` is a map `π⁻¹(𝒦) ⟶ 𝒬 ⊗ f^*𝒥` extending the canonical map
`c : I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥` and killing `i(𝒦 ⊗ f^*𝒥)`, and every map extending `c` kills
`i(𝒦 ⊗ f^*𝒥)`, which `c` does. -/
theorem exists_retraction_quotientLiftExtension_iff :
    (∃ r : (quotientLiftExtension i t f f' hi ht comm F' hstrict hflat K).X₂ ⟶
        (quotientLiftExtension i t f f' hi ht comm F' hstrict hflat K).X₁,
      (quotientLiftExtension i t f f' hi ht comm F' hstrict hflat K).f ≫ r = 𝟙 _) ↔
      ∃ d : quotientLiftPreimage i F' K ⟶
          i.pushforwardModules.obj ((baseIdealTensor t f ht).obj (cokernel K.arrow)),
        idealProductToQuotientLiftPreimage i hi F' K ≫ d =
          quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K := by
  have ff := (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some
  have : i.pushforwardModules.Full := ff.full
  have : i.pushforwardModules.Faithful := ff.faithful
  have := isIso_unit_quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K
  have := epi_quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨cokernel.π (quotientLiftKernelInclusion i t f f' hi ht comm F' hstrict hflat K) ≫
      i.pullbackAdjPushforwardModulesViaComparison.unit.app
        (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K) ≫
      i.pushforwardModules.map r, ?_⟩
    calc idealProductToQuotientLiftPreimage i hi F' K ≫
          cokernel.π (quotientLiftKernelInclusion i t f f' hi ht comm F' hstrict hflat K) ≫
          i.pullbackAdjPushforwardModulesViaComparison.unit.app
            (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K) ≫
          i.pushforwardModules.map r =
        quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K ≫
          i.pushforwardModules.map
            (quotientLiftExtensionLeft i t f f' hi ht comm F' hstrict hflat K ≫ r) := by
          rw [Functor.map_comp, pushforwardModules_map_quotientLiftExtensionLeft, ← Category.assoc,
            ← quotientLiftCanonicalMap_comp_extensionι]
          simp only [Category.assoc]
      _ = quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K := by
          rw [hr, CategoryTheory.Functor.map_id, Category.comp_id]
  · rintro ⟨d, hd⟩
    have hkd : quotientLiftKernelInclusion i t f f' hi ht comm F' hstrict hflat K ≫ d = 0 := by
      rw [Category.assoc, hd, quotientLiftKernelTensorMap_comp_canonicalMap]
    refine ⟨i.pushforwardModules.preimage (@inv _ _ _ _
      (i.pullbackAdjPushforwardModulesViaComparison.unit.app
        (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K))
      (isIso_unit_quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K) ≫
        cokernel.desc _ d hkd), ?_⟩
    apply i.pushforwardModules.map_injective
    rw [Functor.map_comp, pushforwardModules_map_quotientLiftExtensionLeft,
      Functor.map_preimage, Category.assoc, IsIso.hom_inv_id_assoc,
      CategoryTheory.Functor.map_id]
    apply (cancel_epi (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)).1
    rw [← Category.assoc, quotientLiftCanonicalMap_comp_extensionι, Category.assoc,
      cokernel.π_desc, hd, Category.comp_id]

include hstrict hflat in
/-- **A lift of the quotient is cut out by a map extending `c`** (the converse half of
Remark 0CZU): a lift `𝒦'` of `𝒦` lies in `π⁻¹(𝒦)`, maps onto `i_*𝒦`, and meets `I·ℱ'` exactly in
the kernel of `c : I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥`. Meeting `I·ℱ'` inside the kernel of `c` is
`𝒦' ∩ I·ℱ' = I·𝒦' ⊂ I·π⁻¹(𝒦)`, which uses that `ℱ'/𝒦'` is flat
(`Deformation.ToposThickening.shortExact_map_pullbackModules_of_isFlat`); containing the kernel
of `c`, which is `I·π⁻¹(𝒦)`, is `I·π⁻¹(𝒦) ⊂ 𝒦'`, because `π⁻¹(𝒦)/𝒦'` is a quotient of `I·ℱ'`,
which `I` kills. -/
theorem isExtensionKernel_of_isQuotientLift {K' : Subobject F'}
    (hK' : IsQuotientLift i f' F' K K') :
    ∃ K'' : Subobject (quotientLiftPreimage i F' K),
      (@Subobject.map _ _ _ _ (quotientLiftPreimageι i F' K)
        (mono_quotientLiftPreimageι i hi F' K)).obj K'' = K' ∧
        IsExtensionKernel (quotientLiftPreimageShortComplex i hi F' K)
          (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K) K'' := by
  have := mono_quotientLiftPreimageι i hi F' K
  obtain ⟨hflat', h, hι, hπ⟩ := (isQuotientLift_iff i f' hi F' K K').1 hK'
  have ff := (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some
  have : i.pushforwardModules.Full := ff.full
  have : i.pushforwardModules.Faithful := ff.faithful
  have : Mono h := mono_of_mono_fac hι
  have := preservesFiniteLimits_pushforwardModules hi
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj X'.O
    ((SheafOfModules.restrictScalars (Stacks.SheafOfModules.FlatSquareZero.ringMap i.fSharp)).obj
      hi.I)
  have hjι : idealProductToQuotientLiftPreimage i hi F' K ≫ quotientLiftPreimageι i F' K =
      (idealProductSubmodule hi F').ι := pullback.lift_snd _ _ _
  refine ⟨Subobject.mk h, ?_, ?_, fun Z z => ?_⟩
  · rw [Subobject.map_mk]
    exact (Subobject.mk_eq_mk_of_comm _ K'.arrow (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, hι])).trans (Subobject.mk_arrow K')
  · rw [← Subobject.underlyingIso_hom_comp_eq_mk h, Category.assoc]
    exact epi_comp _ _
  rw [mk_factors_iff_exists h]
  constructor
  · rintro ⟨y, hy⟩
    have hyK : y ≫ K'.arrow = z ≫ (idealProductSubmodule hi F').ι := by
      rw [← hι, ← Category.assoc, hy, Category.assoc, hjι]
    have hSc : (ShortComplex.mk K'.arrow (cokernel.π K'.arrow) (cokernel.condition _)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
        inferInstance inferInstance
    have hL := shortExact_map_pullbackModules_of_isFlat i t f f' hi ht comm _ hSc hstrict hflat'
    have : Mono ((pullbackModules i.toRingedToposModulesHom).map K'.arrow) := hL.mono_f
    have : Mono (i.pushforwardModules.map
      ((pullbackModules i.toRingedToposModulesHom).map K'.arrow)) := Functor.map_mono _ _
    have hnat : i.pullbackAdjPushforwardModulesViaComparison.unit.app
        (K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ≫
        i.pushforwardModules.map ((pullbackModules i.toRingedToposModulesHom).map K'.arrow) =
          K'.arrow ≫ i.pullbackAdjPushforwardModulesViaComparison.unit.app F' :=
      (i.pullbackAdjPushforwardModulesViaComparison.unit.naturality K'.arrow).symm
    have hyu : y ≫ i.pullbackAdjPushforwardModulesViaComparison.unit.app
        (K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) = 0 := by
      apply (cancel_mono (i.pushforwardModules.map
        ((pullbackModules i.toRingedToposModulesHom).map K'.arrow))).1
      rw [zero_comp, Category.assoc, hnat, ← Category.assoc, hyK, Category.assoc,
        idealProductSubmodule_unit_comp_zero, comp_zero]
    have hE := idealProductShortComplex_shortExact hi
      (K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    obtain ⟨y₁, hy₁⟩ := KernelFork.IsLimit.lift' hE.fIsKernel y hyu
    have hy₁' : y₁ ≫ (idealProductSubmodule hi _).ι = y := hy₁
    obtain ⟨Z', π', hπ', w', hw⟩ := (epi_iff_surjective_up_to_refinements _).1
      (epi_multiplicationToIdealProduct i hi
        (reducedPullbackModule i
          (K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)))
        (K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
        (i.pullbackAdjPushforwardModulesViaComparison.unit.app
          (K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)))
        (idealProductSubmodule_unit_comp_zero hi
          (K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))) hE) y₁
    have hπy : π' ≫ y = w' ≫ (idealAction hi).app
        (K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :=
      (congrArg (π' ≫ ·) hy₁'.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (idealProductSubmodule hi _).ι) hw).trans
          ((Category.assoc _ _ _).trans (congrArg (w' ≫ ·)
            (multiplicationToIdealProduct_comp_ι i hi _ _ _ _ hE)))))
    have key : π' ≫ z = w' ≫ (idealTensorFunctor hi).map h ≫
        quotientLiftIdealAction i hi F' K := by
      apply (cancel_mono (idealProductSubmodule hi F').ι).1
      rw [Category.assoc, ← hyK, ← Category.assoc, hπy, Category.assoc, Category.assoc,
        Category.assoc, quotientLiftIdealAction_comp_ι, ← Category.assoc
          ((idealTensorFunctor hi).map h), ← Functor.map_comp, hι, (idealAction hi).naturality,
        Functor.id_map]
    apply (cancel_epi π').1
    rw [comp_zero, ← Category.assoc, key, Category.assoc, Category.assoc,
      quotientLiftIdealAction_comp_canonicalMap, comp_zero, comp_zero]
  · intro hz
    have hNunit : IsIso (i.pullbackAdjPushforwardModulesViaComparison.unit.app
        (idealProductSubmodule hi F').toSheafOfModules) :=
      i.pullbackAdjPushforwardModulesViaComparison.isIso_unit_app_iff_mem_essImage.2
        (essImage_idealProductSubmodule hi F')
    have hNact : (idealAction hi).app (idealProductSubmodule hi F').toSheafOfModules = 0 :=
      idealAction_app_eq_zero hi _
    have hSq := quotientLiftPreimageShortComplex_shortExact i hi F' K
    have hepi : Epi (idealProductToQuotientLiftPreimage i hi F' K ≫ cokernel.π h) := by
      refine Preadditive.epi_of_cancel_zero _ fun {W} t ht0 => ?_
      have h₂ : idealProductToQuotientLiftPreimage i hi F' K ≫ cokernel.π h ≫ t = 0 := by
        rw [← Category.assoc, ht0]
      obtain ⟨e, he⟩ := CokernelCofork.IsColimit.desc' hSq.gIsCokernel (cokernel.π h ≫ t) h₂
      change quotientLiftPreimageπ i F' K ≫ e = cokernel.π h ≫ t at he
      have he0 : e = 0 := (cancel_epi (h ≫ quotientLiftPreimageπ i F' K)).1 (by
        rw [Category.assoc, he, ← Category.assoc, cokernel.condition, zero_comp, comp_zero])
      apply (cancel_epi (cokernel.π h)).1
      rw [comp_zero, ← he, he0, comp_zero]
    have : Epi ((idealTensorFunctor hi).map
        (idealProductToQuotientLiftPreimage i hi F' K ≫ cokernel.π h)) := Functor.map_epi _ _
    have hQact : (idealAction hi).app (cokernel h) = 0 := by
      apply (cancel_epi ((idealTensorFunctor hi).map
        (idealProductToQuotientLiftPreimage i hi F' K ≫ cokernel.π h))).1
      rw [comp_zero, (idealAction hi).naturality, hNact, zero_comp]
    have hact : (idealAction hi).app (quotientLiftPreimage i F' K) ≫ cokernel.π h = 0 := by
      rw [← Functor.id_map (cokernel.π h), ← (idealAction hi).naturality, hQact, comp_zero]
    obtain ⟨Z', π', hπ', y, hy⟩ :=
      (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
        (quotientLiftCanonicalMap_isColimit i t f f' hi ht comm F' hstrict hflat K) z).1 hz
    have h0 : (z ≫ idealProductToQuotientLiftPreimage i hi F' K) ≫ cokernel.π h = 0 := by
      apply (cancel_epi π').1
      rw [comp_zero, ← Category.assoc, ← Category.assoc, hy, Category.assoc, Category.assoc,
        ← Category.assoc (quotientLiftIdealAction i hi F' K),
        quotientLiftIdealAction_comp_idealProductToQuotientLiftPreimage, hact, comp_zero]
    exact ⟨_, (KernelFork.IsLimit.lift' (Abelian.monoIsKernelOfCokernel _
      (cokernelIsCokernel h)) _ h0).2⟩

variable [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

include hstrict hflat in
/-- **Remark 0CZU, the vanishing criterion, for ringed topoi.** Let `(f, f')` be a strict
morphism of first order thickenings of ringed topoi, `ℱ'` an `O'`-module flat over `O_{ℬ'}`,
`ℱ = i^*ℱ'`, and `ℱ ⟶ 𝒬 = ℱ/𝒦` a quotient with `𝒬` flat over `O_ℬ`. The class
`o ∈ Ext¹_O(𝒦, 𝒬 ⊗ f^*𝒥)` of the extension `0 ⟶ 𝒬 ⊗ f^*𝒥 ⟶ π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥) ⟶ 𝒦 ⟶ 0`
(`Deformation.ToposThickening.quotientLiftObstruction`) vanishes if and only if the quotient
lifts: there is `𝒦' ⊂ ℱ'` with `ℱ'/𝒦'` flat over `O_{ℬ'}` and `i^*(ℱ'/𝒦') = ℱ/𝒦`
(`Deformation.ToposThickening.IsQuotientLift`). -/
theorem quotientLiftObstruction_eq_zero_iff
    (hQ : IsFlatOverBase i f ((pushforwardModuleFunctor i.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj (cokernel K.arrow))) :
    quotientLiftObstruction.{_, _, _, _, _, _, _, _, _, _, _, e} i t f f' hi ht comm F' hstrict
        hflat K = 0 ↔
      ∃ K' : Subobject F', IsQuotientLift i f' F' K K' := by
  have := epi_quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K
  have := mono_quotientLiftPreimageι i hi F' K
  have hS := quotientLiftExtension_shortExact i t f f' hi ht comm F' hstrict hflat K
  have hSP := quotientLiftPreimageShortComplex_shortExact i hi F' K
  have h1 : quotientLiftObstruction.{_, _, _, _, _, _, _, _, _, _, _, e} i t f f' hi ht comm F'
      hstrict hflat K = 0 ↔
        ∃ r : (quotientLiftExtension i t f f' hi ht comm F' hstrict hflat K).X₂ ⟶
          (quotientLiftExtension i t f f' hi ht comm F' hstrict hflat K).X₁,
        (quotientLiftExtension i t f f' hi ht comm F' hstrict hflat K).f ≫ r = 𝟙 _ := by
    rw [← extClass_comp_mk₀_eq_zero_iff hS (𝟙 _), Abelian.Ext.comp_mk₀_id]
    rfl
  rw [h1, exists_retraction_quotientLiftExtension_iff]
  constructor
  · rintro ⟨d, hd⟩
    have hK'' := isExtensionKernel_kernelSubobject hSP (⟨d, hd⟩ :
      ExtensionAlong (quotientLiftPreimageShortComplex i hi F' K)
        (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K))
    have hfl := isFlat_cokernel_of_isExtensionKernel i t f f' hi ht comm F' K hstrict hflat hQ
      (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)
      (quotientLiftIdealAction i hi F' K) (quotientLiftIdealAction_comp_ι i hi F' K)
      (quotientLiftIdealAction_comp_canonicalMap i t f f' hi ht comm F' hstrict hflat K)
      (quotientLiftCanonicalMap_isColimit i t f f' hi ht comm F' hstrict hflat K) _ hK''
    refine ⟨Subobject.mk ((kernelSubobject d).arrow ≫ quotientLiftPreimageι i F' K),
      (isQuotientLift_iff i f' hi F' K _).2 ⟨?_, ?_⟩⟩
    · refine Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
        ((SheafOfModules.restrictScalars
          ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            f'.fSharpInverseImage)).mapIso ?_) hfl
      refine (cokernelEpiComp (Subobject.underlyingIso
        ((kernelSubobject d).arrow ≫ quotientLiftPreimageι i F' K)).hom _).symm ≪≫
        eqToIso (congrArg (fun x => cokernel x)
          (Subobject.underlyingIso_hom_comp_eq_mk
            ((kernelSubobject d).arrow ≫ quotientLiftPreimageι i F' K)))
    · refine ⟨(Subobject.underlyingIso ((kernelSubobject d).arrow ≫
        quotientLiftPreimageι i F' K)).hom ≫ (kernelSubobject d).arrow, ?_, ?_⟩
      · rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
      · rw [Category.assoc]
        have := hK''.1
        exact epi_comp _ _
  · rintro ⟨K', hK'⟩
    obtain ⟨K'', -, hK''⟩ := isExtensionKernel_of_isQuotientLift i t f f' hi ht comm F' hstrict
      hflat K hK'
    obtain ⟨d, -⟩ := exists_extensionAlong_of_isExtensionKernel hSP hK''
    exact ⟨d.val, d.property⟩

/-- **The restriction of a lifted quotient is the quotient**: for a lift `𝒦'` of `𝒦`,
`i^*(ℱ'/𝒦') ≅ ℱ/𝒦`, the pullback being right exact. -/
noncomputable def pullbackModulesCokernelIsoOfIsQuotientLift {K' : Subobject F'}
    (hK' : IsQuotientLift i f' F' K K') :
    (pullbackModules i.toRingedToposModulesHom).obj (cokernel K'.arrow) ≅ cokernel K.arrow := by
  haveI := i.pullbackAdjPushforwardModulesViaComparison.leftAdjoint_preservesColimits
  haveI : Epi ((pullbackModules i.toRingedToposModulesHom).map (cokernel.π K'.arrow)) :=
    Functor.map_epi _ _
  have h2 : Subobject.mk (kernel.ι ((pullbackModules i.toRingedToposModulesHom).map
      (cokernel.π K'.arrow))) = Subobject.mk K.arrow := hK'.2.trans (Subobject.mk_arrow K).symm
  haveI : IsIso (Subobject.ofMkLEMk (kernel.ι ((pullbackModules i.toRingedToposModulesHom).map
      (cokernel.π K'.arrow))) K.arrow h2.le) := (Subobject.isoOfMkEqMk _ _ h2).isIso_hom
  exact (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel
        ((pullbackModules i.toRingedToposModulesHom).map (cokernel.π K'.arrow))))).symm ≪≫
    eqToIso (congrArg (fun x => cokernel x)
      (Subobject.ofMkLEMk_comp (f := kernel.ι ((pullbackModules i.toRingedToposModulesHom).map
        (cokernel.π K'.arrow))) (g := K.arrow) h2.le).symm) ≪≫
    cokernelEpiComp _ _

end QuotientLift

section FinitePresentation

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
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X'.C, HasWeakSheafify (X'.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X'.C, (X'.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
  (K : Subobject ((pullbackModules i.toRingedToposModulesHom).obj F'))

omit [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}] in
/-- **Remark 0CZU, finite presentation.** If the quotient `ℱ/𝒦` is of finite presentation, so is
every lift `ℱ'/𝒦'` of it: `ℱ'/𝒦'` is flat over `O_{ℬ'}` and restricts to `ℱ/𝒦`, so Stacks 08VU
(`Deformation.ToposThickening.isFinitePresentation_iff_pullbackModules_of_isFlat`) applies. -/
theorem isFinitePresentation_cokernel_of_isQuotientLift
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    {K' : Subobject F'} (hK' : IsQuotientLift i f' F' K K')
    (hfp : (cokernel K.arrow).IsFinitePresentation) :
    (cokernel K'.arrow).IsFinitePresentation :=
  (isFinitePresentation_iff_pullbackModules_of_isFlat i t f f' hi ht comm _ hK'.1 hstrict).2
    (Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      (pullbackModulesCokernelIsoOfIsQuotientLift i f' F' K hK').symm hfp)

end FinitePresentation

end Deformation.ToposThickening

end
