module

public import Mathlib.CategoryTheory.Abelian.CommSq
public import StacksCore.CategoryTheory.Abelian.CommSq
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassification
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives
public import StacksFrontier.Topology.Sheaves.Modules.ExtensionByZero.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# The obstruction to the existence of an extension (Stacks 08L8)

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces with ideal `ℐ`,
let `ℱ` and `𝒦` be `𝒪_X`-modules and let `c : ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦` be `𝒪_X`-linear. This file
produces a class

    o(ℱ, 𝒦, c) ∈ Ext²_{𝒪_X}(ℱ, 𝒦)

which vanishes exactly when there is an extension of `𝒪_{X'}`-modules

    0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0

as in Tag 08L4 whose canonical map `c_{ℱ'}` is `c`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.extensionExistenceObstruction`: **Stacks 08L8**, the
  class `o(ℱ, 𝒦, c)` together with its vanishing criterion.
* `AlgebraicGeometry.RingedSpaceThickening.ObstructionPresentation`: the data the first two steps
  of the source proof produce — an injective embedding `𝒦 ⟶ 𝒥` with quotient `𝒬`, an extension of
  `i_* ℱ` by `i_* 𝒥` with canonical map `c ≫ (𝒦 ⟶ 𝒥)`, and the descent to `X` of its pushout
  along `i_*(𝒥 ⟶ 𝒬)` — and
  `AlgebraicGeometry.RingedSpaceThickening.ObstructionPresentation.obstruction`, the Yoneda
  product of the two degree one classes it carries.
* `AlgebraicGeometry.RingedSpaceThickening.obstructionClass`: the class `o(ℱ, 𝒦, c)` itself.
* `CategoryTheory.Abelian.pushoutShortComplex`: the pushout of a short exact sequence along a
  morphism out of its kernel object.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.exists_firstOrderExtension_of_injective`: the first
  step of the source proof — for an injective `𝒪_X`-module `𝒦` every `c` is the canonical map of
  an extension as in Tag 08L4. It is built from a flat `𝒪_{X'}`-module covering `i_* ℱ`
  (**Stacks 05NI**) by extending a map out of a subobject of the kernel across the injective and
  pushing out.
* `AlgebraicGeometry.RingedSpaceThickening.mono_idealAction_of_flat`: for a flat `𝒪_{X'}`-module
  `ℋ'` the multiplication `ℐ ⊗_{𝒪_{X'}} ℋ' ⟶ ℋ'` is injective, so `ℐ ⊗_{𝒪_{X'}} ℋ' = ℐ ℋ'`.
* `AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction_eq_of_lift`: an extension
  whose middle term receives a lift of a surjection onto `i_* ℱ` compatible with a prescribed
  map on the ideal multiple has that prescribed canonical map.
* `AlgebraicGeometry.RingedSpaceThickening.extClass_eq_zero_of_exists_extension` and
  `AlgebraicGeometry.RingedSpaceThickening.exists_extension_of_extClass_eq_zero`: the two halves
  of the third step of the source proof, stated for a fixed injective embedding of `𝒦` and the
  extension of `ℱ` by the quotient obtained from it.
* `CategoryTheory.Abelian.extClass_eq_zero_iff_exists_section`: the class of a short exact
  sequence vanishes exactly when its surjection is split.
* `CategoryTheory.Abelian.extClass_comp_eq_zero_iff`: the Yoneda product with the class of
  `0 ⟶ 𝒦 ⟶ 𝒥 ⟶ 𝒬 ⟶ 0` with `𝒥` injective is injective on `Ext¹(ℱ, 𝒬)`.
* `AlgebraicGeometry.RingedSpaceThickening.exists_obstructionPresentation`: a presentation of
  the obstruction exists, and
  `AlgebraicGeometry.RingedSpaceThickening.ObstructionPresentation.obstruction_eq_zero_iff`: its
  class vanishes exactly when an extension as in Tag 08L4 with canonical map `c` exists.
* `AlgebraicGeometry.RingedSpaceThickening.ObstructionPresentation.obstruction_eq`: the class
  does not depend on the presentation, and
  `AlgebraicGeometry.RingedSpaceThickening.obstructionClass_eq`: hence `o(ℱ, 𝒦, c)` is the class
  of every presentation.
* `AlgebraicGeometry.RingedSpaceThickening.extensionExistenceObstruction_val` and
  `AlgebraicGeometry.RingedSpaceThickening.extensionExistenceObstruction_val_eq`: the element of
  the subtype of Tag 08L8 is that class, and is the Yoneda product of any presentation.
* `CategoryTheory.Abelian.exists_yonedaExtension_descent`: an extension whose middle term lies
  in the essential image of a fully faithful exact functor is the image of an extension
  downstairs.
* `CategoryTheory.Abelian.isPushout_pushoutShortComplex` and
  `CategoryTheory.Abelian.isPushout_of_shortExact`: the middle term of the pushout sequence is a
  pushout, and a map of short exact sequences which is the identity on quotient objects exhibits
  the target as such a pushout. With
  `CategoryTheory.Abelian.f_comp_pushout_inl`,
  `CategoryTheory.Abelian.inl_pushoutShortComplex_g` and
  `CategoryTheory.Abelian.inr_pushoutShortComplex_g` these are the whole interface of the
  pushout of a short exact sequence along a map of its kernel object.

## Implementation notes

An extension as in Tag 08L4 is a `CategoryTheory.Abelian.YonedaExtension` of `i_* ℱ` by `i_* 𝒦`
and its canonical map is
`AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction`. The class is returned as a
subtype bundling the vanishing criterion, as for the obstruction of Tag 08L6; the criterion does
not pin the class down, and the source asserts only that a class with that zero locus exists.

The class is constructed as the Yoneda product `ξ_𝒟 · ξ_{0 → 𝒦 → 𝒥 → 𝒬 → 0}` of two degree one
classes carried by an `ObstructionPresentation`; `obstructionClass` is that product for a
presentation built from the injective hull of `𝒦`, and `obstruction_eq` shows the product is the
same for every presentation, so the class depends on nothing but `ℱ`, `𝒦` and `c`. In the
presentation built here `𝒦 ⟶ 𝒥` is the injective hull of `𝒦`, `𝒬` its cokernel, and `𝒟` the
descent to `X` of the pushout along `i_*(𝒥 ⟶ 𝒬)` of the extension produced by the first step for
`c` followed by `𝒦 ⟶ 𝒥`. That pushout descends because its canonical map is
`c ≫ (𝒦 ⟶ 𝒥) ≫ (𝒥 ⟶ 𝒬) = 0` by Tag 08L5 part (1), so the ideal annihilates its middle term and
Tag 08KS applies. The identification `Ext¹_{𝒪_X}(ℱ, 𝒬) = Ext²_{𝒪_X}(ℱ, 𝒦)` used in the source is
not needed as such: only that the product with `ξ_{0 → 𝒦 → 𝒥 → 𝒬 → 0}` vanishes exactly when
`ξ_𝒟` does, which is the long exact sequence together with the vanishing of `Ext¹_{𝒪_X}(ℱ, 𝒥)`
for `𝒥` injective.

Identities mixing a tensor product on `X'` with a module on `X` are proved in term mode, since
such a goal is not type-correct at the transparency at which `rw` and `simp only` match: the
spellings `structureSheafRing` and `structureSheafRing` of the structure sheaf of `X'` agree only at
default transparency. For the same reason the modules carrying a tensor product on `X'` are
declared over `structureSheafRing`, and
`AlgebraicGeometry.RingedSpaceThickening.ambientPushforward` and
`AlgebraicGeometry.RingedSpaceThickening.idealSheafModule` read a direct image and the ideal in
that spelling — without them the zero morphism out of a tensor product has no `Zero` instance.

## References

* [Stacks Project, Tag 08L8](https://stacks.math.columbia.edu/tag/08L8)
* [Stacks Project, Tag 08L6](https://stacks.math.columbia.edu/tag/08L6)
* [Stacks Project, Tag 08L5](https://stacks.math.columbia.edu/tag/08L5)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 05NI](https://stacks.math.columbia.edu/tag/05NI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules.TensorPresentations (tensorSheafMap_epi_of_epi_of_epi)

-- Local transparency setting, following the convention of the sibling files.
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor
-- Local transparency setting, following the convention of the sibling files.
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace CategoryTheory

/-- A monomorphism followed by an isomorphism is a monomorphism. -/
theorem mono_comp_iso {C : Type*} [Category C] {A B D : C} (f : A ⟶ B) (hf : Mono f) (e : B ≅ D) :
    Mono (f ≫ e.hom) := by
  have := hf
  infer_instance

end CategoryTheory

namespace CategoryTheory.Abelian

section Abstract

universe v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The pushout of a short exact sequence `S` along a morphism `a` out of its kernel object. -/
@[sga "3 III 4.1"]
noncomputable abbrev pushoutShortComplex (S : ShortComplex C) {K : C} (a : S.X₁ ⟶ K) :
    ShortComplex C :=
  ShortComplex.mk (pushout.inr S.f a) (pushout.desc S.g 0 (by simp))
    (pushout.inr_desc _ _ _)

/-- The surjection of the pushout sequence restricts to the surjection of the original. -/
theorem inl_pushoutShortComplex_g (S : ShortComplex C) {K : C} (a : S.X₁ ⟶ K) :
    pushout.inl S.f a ≫ (pushoutShortComplex S a).g = S.g :=
  pushout.inl_desc _ _ _

/-- Pushing a short exact sequence out along a morphism out of its kernel object gives a short
exact sequence, with the same quotient object. -/
@[sga "3 III 4.1" "partial"]
theorem pushoutShortComplex_shortExact {S : ShortComplex C} (hS : S.ShortExact) {K : C}
    (a : S.X₁ ⟶ K) : (pushoutShortComplex S a).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hjq := inl_pushoutShortComplex_g S a
  have hepi : Epi (pushoutShortComplex S a).g :=
    ⟨fun f g hfg => (cancel_epi S.g).1 (by rw [← hjq, Category.assoc, Category.assoc, hfg])⟩
  have hcok : IsColimit (CokernelCofork.ofπ (pushoutShortComplex S a).g
      (pushoutShortComplex S a).zero) :=
    CokernelCofork.IsColimit.ofπ' _ _ (fun {T} f hf => by
      obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel (pushout.inl S.f a ≫ f) (by
        rw [← Category.assoc, show S.f ≫ pushout.inl S.f a = a ≫ pushout.inr S.f a from
          pushout.condition, Category.assoc, hf, comp_zero])
      refine ⟨d, pushout.hom_ext ?_ ?_⟩
      · rw [← Category.assoc, hjq]
        exact hd
      · rw [← Category.assoc,
          show pushout.inr S.f a ≫ (pushoutShortComplex S a).g = 0 from pushout.inr_desc _ _ _,
          zero_comp, hf])
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ hcok
          mono_f := by dsimp only [pushoutShortComplex]; infer_instance
          epi_g := hepi }

/-- The defining square of the pushout of a short exact sequence `S` along a morphism `a` out of
its kernel object commutes. -/
theorem f_comp_pushout_inl (S : ShortComplex C) {K : C} (a : S.X₁ ⟶ K) :
    S.f ≫ pushout.inl S.f a = a ≫ pushout.inr S.f a :=
  pushout.condition

/-- The injection of the pushout sequence is killed by its surjection. -/
theorem inr_pushoutShortComplex_g (S : ShortComplex C) {K : C} (a : S.X₁ ⟶ K) :
    pushout.inr S.f a ≫ (pushoutShortComplex S a).g = 0 :=
  (pushoutShortComplex S a).zero

/-- The middle term of the pushout sequence is the pushout of the middle term of `S` and of the
target of `a` over the kernel object of `S`. -/
theorem isPushout_pushoutShortComplex (S : ShortComplex C) {K : C} (a : S.X₁ ⟶ K) :
    IsPushout S.f a (pushout.inl S.f a) (pushout.inr S.f a) :=
  IsPushout.of_hasPushout S.f a

/-- A map of two short exact sequences with the same quotient object which is the identity there
exhibits the second as the pushout of the first along the map of kernel objects: the induced map
out of the pushout is an isomorphism, by the five lemma. -/
theorem isPushout_of_shortExact {A B D A' B' : C} {f : A ⟶ B} {g : B ⟶ D} {f' : A' ⟶ B'}
    {g' : B' ⟶ D} {hfg : f ≫ g = 0} {hfg' : f' ≫ g' = 0}
    (h : (ShortComplex.mk f g hfg).ShortExact) (h' : (ShortComplex.mk f' g' hfg').ShortExact)
    (a : A ⟶ A') (b : B ⟶ B') (hf : f ≫ b = a ≫ f') (hg : b ≫ g' = g) :
    IsPushout f a b f' := by
  have hpush := pushoutShortComplex_shortExact h a
  have htl : pushout.inl f a ≫ pushout.desc b f' hf = b := pushout.inl_desc _ _ _
  have htr : pushout.inr f a ≫ pushout.desc b f' hf = f' := pushout.inr_desc _ _ _
  have htg : pushout.desc b f' hf ≫ g' =
      (pushoutShortComplex (ShortComplex.mk f g hfg) a).g := by
    refine pushout.hom_ext ?_ ?_
    · rw [← Category.assoc, htl, hg]
      exact (inl_pushoutShortComplex_g (ShortComplex.mk f g hfg) a).symm
    · rw [← Category.assoc, htr, hfg']
      exact (inr_pushoutShortComplex_g (ShortComplex.mk f g hfg) a).symm
  have hiso : IsIso (pushout.desc b f' hf) :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃
      ({ τ₁ := 𝟙 A', τ₂ := pushout.desc b f' hf, τ₃ := 𝟙 D
         comm₁₂ := (Category.id_comp f').trans htr.symm
         comm₂₃ := htg.trans (Category.comp_id _).symm } :
        pushoutShortComplex (ShortComplex.mk f g hfg) a ⟶ ShortComplex.mk f' g' hfg')
      hpush h'
  exact (isPushout_pushoutShortComplex (ShortComplex.mk f g hfg) a).of_iso
    (Iso.refl A) (Iso.refl B) (Iso.refl A') (@asIso _ _ _ _ _ hiso)
    (by simp) (by simp) (by simpa using htl) (by simpa using htr)

omit [Abelian C] in
/-- Extend a morphism into an injective object across a monomorphism whose source and target
both lie in the essential image of a fully faithful functor. -/
@[sga "4 V 0.5.2" "partial"]
theorem exists_factorThru_mono_essImage {D : Type*} [Category D] (G : C ⥤ D) [G.Full]
    [G.Faithful] {J : C} (hJ : Injective J) {A B : D} (m : A ⟶ B) (hm : Mono m)
    (a : A ⟶ G.obj J) (hA : G.essImage A) (hB : G.essImage B) :
    ∃ b : B ⟶ G.obj J, m ≫ b = a := by
  have := hJ
  obtain ⟨A₀, ⟨eA⟩⟩ := hA
  obtain ⟨B₀, ⟨eB⟩⟩ := hB
  have := hm
  have hm₀ : Mono (G.preimage (eA.hom ≫ m ≫ eB.inv)) := G.mono_of_mono_map (by
    rw [G.map_preimage]; infer_instance)
  refine ⟨eB.inv ≫ G.map (Injective.factorThru (G.preimage (eA.hom ≫ a))
    (G.preimage (eA.hom ≫ m ≫ eB.inv))), ?_⟩
  apply (cancel_epi eA.hom).1
  have h := congrArg G.map (Injective.comp_factorThru (G.preimage (eA.hom ≫ a))
    (G.preimage (eA.hom ≫ m ≫ eB.inv)))
  simpa only [G.map_comp, G.map_preimage, Category.assoc] using h

/-- A map of short exact sequences which is the identity on quotient objects, given by a
monomorphism `j` of kernel objects with cokernel the kernel object of the second sequence, is
surjective with kernel the source of `j`. -/
theorem kernelPairShortComplex_shortExact {K J Q E D F : C} {j : K ⟶ J} {q : J ⟶ Q} {f : J ⟶ E}
    {g : E ⟶ F} {f' : Q ⟶ D} {g' : D ⟶ F} {hj : j ≫ q = 0} {hf : f ≫ g = 0}
    {hf' : f' ≫ g' = 0} (hS : (ShortComplex.mk j q hj).ShortExact)
    (hT : (ShortComplex.mk f g hf).ShortExact) (hU : (ShortComplex.mk f' g' hf').ShortExact)
    (a : E ⟶ D) (ha : f ≫ a = q ≫ f') (ha' : a ≫ g' = g) :
    ∃ hz : (j ≫ f) ≫ a = 0, (ShortComplex.mk (j ≫ f) a hz).ShortExact := by
  have hz : (j ≫ f) ≫ a = 0 := by rw [Category.assoc, ha, ← Category.assoc, hj, zero_comp]
  have := hS.mono_f
  have := hS.epi_g
  have := hT.mono_f
  have := hT.epi_g
  have := hU.mono_f
  have := hU.epi_g
  have hepi : Epi a :=
    ShortComplex.epi_τ₂_of_exact_of_epi
      ({ τ₁ := q, τ₂ := a, τ₃ := 𝟙 F, comm₁₂ := ha.symm, comm₂₃ := by simpa using ha' } :
        ShortComplex.mk f g hf ⟶ ShortComplex.mk f' g' hf') hU.exact
  have hk : IsLimit (KernelFork.ofι (j ≫ f) hz) :=
    KernelFork.IsLimit.ofι' (j ≫ f) hz (fun {T} u hu => by
      have hug : u ≫ g = 0 := by rw [← ha', ← Category.assoc, hu, zero_comp]
      have hv : hT.fIsKernel.lift (KernelFork.ofι u hug) ≫ f = u :=
        hT.fIsKernel.fac _ WalkingParallelPair.zero
      have hvq : hT.fIsKernel.lift (KernelFork.ofι u hug) ≫ q = 0 := by
        apply (cancel_mono f').1
        rw [zero_comp, Category.assoc, ← ha, ← Category.assoc, hv, hu]
      have hw : hS.fIsKernel.lift (KernelFork.ofι
            (hT.fIsKernel.lift (KernelFork.ofι u hug)) hvq) ≫ j =
          hT.fIsKernel.lift (KernelFork.ofι u hug) :=
        hS.fIsKernel.fac _ WalkingParallelPair.zero
      refine ⟨hS.fIsKernel.lift (KernelFork.ofι _ hvq), ?_⟩
      rw [← Category.assoc]
      exact (congrArg (fun z => z ≫ f) hw).trans hv)
  exact ⟨hz, { exact := ShortComplex.exact_of_f_is_kernel _ hk }⟩

end Abstract

section Ext

universe v

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt C] [HasDerivedCategory C]

omit [HasDerivedCategory C] in
/-- The class of a short exact sequence vanishes exactly when its surjection is split. -/
theorem extClass_eq_zero_iff_exists_section {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 _ := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₃ S.X₃ hS
      (Abelian.Ext.mk₀ (𝟙 S.X₃)) (zero_add 1) (by simpa using h)
    obtain ⟨s, rfl⟩ := (Abelian.Ext.mk₀_bijective S.X₃ S.X₂).surjective x
    exact ⟨s, (Abelian.Ext.mk₀_bijective S.X₃ S.X₃).injective
      (by rwa [Abelian.Ext.mk₀_comp_mk₀] at hx)⟩
  · rintro ⟨s, hs⟩
    have h := congrArg (fun ξ => (Abelian.Ext.mk₀ s).comp ξ (zero_add 1)) hS.comp_extClass
    simpa only [Abelian.Ext.mk₀_comp_mk₀_assoc, hs, Abelian.Ext.mk₀_id_comp,
      Abelian.Ext.comp_zero] using h

omit [HasDerivedCategory C] in
/-- The Yoneda product of the class of an extension of `F` by `Q` with the class of a short
exact sequence `0 ⟶ K ⟶ J ⟶ Q ⟶ 0` with `J` injective vanishes exactly when the first class
does: the long exact sequence identifies `Ext¹(F, Q)` with `Ext²(F, K)`. -/
theorem extClass_comp_eq_zero_iff {K J Q W F : C} {j : K ⟶ J} {q : J ⟶ Q} {f : Q ⟶ W}
    {g : W ⟶ F} {hj : j ≫ q = 0} {hf : f ≫ g = 0}
    (hS : (ShortComplex.mk j q hj).ShortExact) (hT : (ShortComplex.mk f g hf).ShortExact)
    (hJ : Injective J) :
    (hT.extClass.comp hS.extClass (by decide) : Abelian.Ext F K 2) = 0 ↔ hT.extClass = 0 := by
  have := hJ
  constructor
  · intro h
    obtain ⟨ξ, hξ⟩ := Abelian.Ext.covariant_sequence_exact₃ F hS hT.extClass (by decide) h
    rw [Abelian.Ext.eq_zero_of_injective ξ, Abelian.Ext.zero_comp] at hξ
    exact hξ.symm
  · intro h
    rw [h, Abelian.Ext.zero_comp]

end Ext

section Descent

universe v v'

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category.{v'} D] [Abelian D]

/-- An extension of `G.obj F` by `G.obj Q` whose middle term lies in the essential image of a
fully faithful exact functor `G` is, up to an isomorphism of middle terms, the image under `G`
of an extension of `F` by `Q`. -/
theorem exists_yonedaExtension_descent (G : C ⥤ D) [G.Full] [G.Faithful]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] {F Q : C}
    (E : Abelian.YonedaExtension (G.obj F) (G.obj Q) 0) (hE : G.essImage E.Z.left) :
    ∃ (E₀ : Abelian.YonedaExtension F Q 0) (e : G.obj E₀.Z.left ≅ E.Z.left),
      G.map E₀.f ≫ e.hom = E.f ∧ e.hom ≫ E.g = G.map E₀.g := by
  obtain ⟨W, ⟨e⟩⟩ := hE
  have hfg : G.preimage (E.f ≫ e.inv) ≫ G.preimage (e.hom ≫ E.g) = 0 := by
    apply G.map_injective
    simp only [G.map_comp, G.map_preimage, Category.assoc, Iso.inv_hom_id_assoc, G.map_zero]
    exact Abelian.YonedaExtension.comp_eq_zero E
  have hmono : Mono (G.preimage (E.f ≫ e.inv)) :=
    G.mono_of_mono_map (by rw [G.map_preimage]; have := E.mono_f; infer_instance)
  have hepi : Epi (G.preimage (e.hom ≫ E.g)) :=
    G.epi_of_epi_map (by rw [G.map_preimage]; have := E.epi_g; infer_instance)
  have hmap : ((ShortComplex.mk (G.preimage (E.f ≫ e.inv))
      (G.preimage (e.hom ≫ E.g)) hfg).map G).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      ({ τ₁ := 𝟙 _, τ₂ := e.hom, τ₃ := 𝟙 _
         comm₁₂ := by simp [G.map_preimage]
         comm₂₃ := by simp [G.map_preimage] } :
        (ShortComplex.mk (G.preimage (E.f ≫ e.inv)) (G.preimage (e.hom ≫ E.g)) hfg).map G ⟶
          ShortComplex.mk E.f E.g (Abelian.YonedaExtension.comp_eq_zero E))).2
      (Abelian.YonedaExtension.shortExact E).exact
  have hSE : (ShortComplex.mk (G.preimage (E.f ≫ e.inv))
      (G.preimage (e.hom ≫ E.g)) hfg).ShortExact :=
    { exact := (ShortComplex.exact_map_iff_of_faithful _ G).1 hmap }
  refine ⟨Abelian.shortExactYonedaExtension hSE, e, ?_, ?_⟩
  · change G.map (G.preimage (E.f ≫ e.inv)) ≫ e.hom = E.f
    simp [G.map_preimage]
  · change e.hom ≫ E.g = G.map (G.preimage (e.hom ≫ E.g))
    simp [G.map_preimage]

end Descent

end CategoryTheory.Abelian

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

/-- The direct image `i_* ℱ` of an `𝒪_X`-module, read over the spelling of the structure sheaf
of `X'` which the tensor product and the ideal action are stated over. -/
noncomputable abbrev ambientPushforward (F : SheafOfModules.{u} (structureSheafRing X)) :
    SheafOfModules.{u} (structureSheafRing X') :=
  (modulePushforward i).obj F

/-- **Stacks 05NI**, read on the thickened space: every `𝒪_{X'}`-module is a quotient of a flat
`𝒪_{X'}`-module. -/
theorem exists_flat_epi (N : SheafOfModules.{u} (structureSheafRing X')) :
    ∃ (P : SheafOfModules.{u} (structureSheafRing X')) (p : P ⟶ N),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X'.sheaf) P ∧ Epi p :=
  Stacks.SheafOfModules.exists_epi_from_flat (X := X'.carrier) (O := X'.sheaf) N

/-- The ideal of a thickening acts injectively on a flat `𝒪_{X'}`-module. -/
theorem mono_idealAction_of_flat (P : SheafOfModules.{u} (structureSheafRing X'))
    (hP : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X'.sheaf) P) :
    Mono (idealAction i P) := by
  have hT : PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩).flip.obj P) := hP.1
  have hj : Mono (idealSheafι i) :=
    inferInstanceAs
      (Mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))))
  have h : Mono ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩)).map
      (((idealSheafι i), (𝟙 P)) : (_, _) ⟶ (_, _))) := by
    have hm : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩).flip.obj P).PreservesMonomorphisms :=
      CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
    exact @mono_comp _ _ _ _ _ _ (@Functor.map_mono _ _ _ _ _ hm _ _ (idealSheafι i) hj)
      _ (@IsIso.mono_of_iso _ _ _ _ _ (Functor.map_isIso _ (𝟙 P)))
  unfold idealAction Stacks.IdealTorsion.idealTensorMultiplication
  exact CategoryTheory.mono_comp_iso _ h _

/-- Tensoring the zero morphism with the identity gives the zero morphism. -/
theorem tensorSheafMap_id_zero {Y : RingedSpace.{u, u}}
    (A : SheafOfModules.{u} (structureSheafRing Y))
    (B C : SheafOfModules.{u} (structureSheafRing Y)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), (0 : B ⟶ C)) : (_, _) ⟶ (_, _))) = 0 := by
  letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
    ⟨Y.presheaf, Y.IsSheaf⟩ A
  exact (congrArg (fun z => ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).map (𝟙 A)).app B ≫ z)
    (Functor.map_zero ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj A) B C)).trans comp_zero

/-- Tensoring a vanishing composite with the identity gives a vanishing composite. -/
theorem tensorSheafMap_id_comp_eq_zero {Y : RingedSpace.{u, u}}
    (A : SheafOfModules.{u} (structureSheafRing Y))
    {B C D : SheafOfModules.{u} (structureSheafRing Y)} (f : B ⟶ C) (g : C ⟶ D)
    (h : f ≫ g = 0) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), f) : (_, _) ⟶ (_, _))) ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), g) : (_, _) ⟶ (_, _))) = 0 :=
  (tensorSheafMap_comp_right A f g).trans
    ((congrArg (fun z => ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), z) : (_, _) ⟶ (_, _)))) h).trans (tensorSheafMap_id_zero A B D))

/-- Tensoring identities on both factors acts trivially on a following morphism. -/
private theorem tensorSheafMap_id_id_comp {Y : RingedSpace.{u, u}}
    (A B : SheafOfModules.{u} (structureSheafRing Y))
    {T : SheafOfModules.{u} (structureSheafRing Y)}
    (f : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B) ⟶ T) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩)).map (((𝟙 A), (𝟙 B)) : (A, B) ⟶ (A, B))) ≫ f = f :=
  (congrArg (fun z => z ≫ f) (tensorSheafMap_id_id Y A B)).trans (Category.id_comp f)

/-- A functor preserving zero morphisms sends a vanishing composite to a vanishing composite. -/
private theorem map_comp_eq_zero_of_comp_eq_zero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (G : C ⥤ D) [G.PreservesZeroMorphisms]
    {A B E : C} {f : A ⟶ B} {g : B ⟶ E} (h : f ≫ g = 0) : G.map f ≫ G.map g = 0 := by
  rw [← G.map_comp, h, G.map_zero]

/-- A module receiving a surjection which kills the ideal action carries the zero action. -/
theorem idealAction_eq_zero_of_epi {N M : SheafOfModules.{u} (structureSheafRing X')} (π : N ⟶ M)
    (hπ : Epi π) (h : idealAction i N ≫ π = 0) : idealAction i M = 0 := by
  have := hπ
  have hepi : Epi (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (idealSheafModule i)), π) : (_, _) ⟶ (_, _)))) :=
    idealTensorFunctor_epi i π hπ
  refine (cancel_epi (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (idealSheafModule i)), π) : (_, _) ⟶ (_, _))))).1 ?_
  exact ((idealAction_naturality i π).symm.trans h).trans comp_zero.symm

/-- A submodule of a module with vanishing ideal action has vanishing ideal action. -/
theorem idealAction_eq_zero_of_mono {A B : SheafOfModules.{u} (structureSheafRing X')} (f : A ⟶ B)
    (hf : Mono f) (hB : idealAction i B = 0) : idealAction i A = 0 := by
  have := hf
  refine (cancel_mono f).1 ?_
  rw [idealAction_naturality i f, hB, comp_zero, zero_comp]

/-- The quotient of a module by the image of the ideal action carries the zero action. -/
theorem idealAction_cokernel_eq_zero {N : SheafOfModules.{u} (structureSheafRing X')}
    (t : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj (N)) ⟶ N)
    (ht : t = idealAction i N) : idealAction i (cokernel t) = 0 :=
  idealAction_eq_zero_of_epi i (cokernel.π t) inferInstance
    ((congrArg (fun z => z ≫ cokernel.π t) ht).symm.trans (cokernel.condition t))

/-- The local lifting characterisation of the canonical map of Tag 08L4 read through a lift. -/
theorem firstOrderExtensionAction_comp_lift (hi : IsFirstOrderThickening i)
    (F K : SheafOfModules.{u} (structureSheafRing X))
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    {P : SheafOfModules.{u} (structureSheafRing X')} (p : P ⟶ ambientPushforward i F)
    (l : P ⟶ E.Z.left) (hl : l ≫ E.g = p) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), p) : (_, _) ⟶ (_, _))) ≫
        (extensionTensorComparison i F ≫
            (modulePushforward i).map (firstOrderExtensionAction i F K hi E).val) ≫ E.f =
      idealAction i P ≫ l := by
  have hbase := firstOrderExtensionAction_comp i F K hi E
  have h₁ : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), l) : (_, _) ⟶ (_, _))) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), E.g) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), p) : (_, _) ⟶ (_, _))) :=
    (tensorSheafMap_comp_right _ l E.g).trans
      (congrArg (fun z => ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), z) : (_, _) ⟶ (_, _)))) hl)
  rw [idealAction_naturality i l, ← hbase, ← h₁, Category.assoc]

/-- The map `γ` of the first step of the source proof. -/
theorem exists_idealAction_factorThru_of_injective (hi : IsFirstOrderThickening i)
    (F K : SheafOfModules.{u} (structureSheafRing X)) (hK : Injective K)
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K)
    (P : SheafOfModules.{u} (structureSheafRing X')) (p : P ⟶ ambientPushforward i F)
    (hp : Epi p) (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X'.sheaf) P)
    (hzero : idealAction i P ≫ p = 0) :
    ∃ γ : kernel p ⟶ ambientPushforward i K,
      kernel.lift p (idealAction i P) hzero ≫ γ =
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (idealSheafModule i)), p) : (_, _) ⟶ (_, _))) ≫
          extensionTensorComparison i F ≫ (modulePushforward i).map c := by
  classical
  have hfull : (modulePushforward i).Full :=
    (closedQuotientOfIsThickening i hi.1).full_modulePushforward
  have hfaith : (modulePushforward i).Faithful :=
    (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
  have := hp
  have hmk : kernel.lift p (idealAction i P) hzero ≫ kernel.ι p = idealAction i P :=
    kernel.lift_ι _ _ _
  have hmono : Mono (kernel.lift p (idealAction i P) hzero) := by
    have := mono_idealAction_of_flat i P hflat
    exact mono_of_mono_fac hmk
  have htm : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (idealSheafModule i)), (kernel.ι p)) : (_, _) ⟶ (_, _))) ≫
      kernel.lift p (idealAction i P) hzero = idealAction i (kernel p) := by
    refine (cancel_mono (kernel.ι p)).1 ?_
    rw [Category.assoc, hmk, idealAction_naturality]
  have hzeroK : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (idealSheafModule i)), (kernel.ι p)) : (_, _) ⟶ (_, _))) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (idealSheafModule i)), p) : (_, _) ⟶ (_, _))) = 0 :=
    tensorSheafMap_id_comp_eq_zero (A := idealSheafModule i) (B := kernel p) (C := P)
      (D := ambientPushforward i F) (kernel.ι p) p (kernel.condition p)
  have hta : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (idealSheafModule i)), (kernel.ι p)) : (_, _) ⟶ (_, _))) ≫
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (idealSheafModule i)), p) : (_, _) ⟶ (_, _))) ≫
            extensionTensorComparison i F ≫ (modulePushforward i).map c) = 0 :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (extensionTensorComparison i F ≫
        (modulePushforward i).map c)) hzeroK).trans zero_comp)
  have key : ∀ {T S Kp J : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩)} (M' : T ⟶ S) (k : S ⟶ Kp) [Mono k]
      (R : S ⟶ J) (hR : M' ≫ R = 0)
      (H : ∀ μ : cokernel M' ⟶ cokernel (M' ≫ k), Mono μ →
        ∀ a : cokernel M' ⟶ J, ∃ b, μ ≫ b = a),
      ∃ γ : Kp ⟶ J, k ≫ γ = R := by
    intro T S Kp J M' k _ R hR H
    obtain ⟨b, hb⟩ := H _ (CategoryTheory.Abelian.mono_cokernel_map_comp M' k)
      (cokernel.desc M' R hR)
    refine ⟨cokernel.π _ ≫ b, ?_⟩
    rw [← cokernel.π_desc M' R hR, ← hb]
    simp
  refine key _ (kernel.lift p (idealAction i P) hzero) _ hta ?_
  intro μ hμ a
  exact CategoryTheory.Abelian.exists_factorThru_mono_essImage (modulePushforward i) hK μ hμ a
    (essImage_of_idealAction_eq_zero i hi.1 _
      (idealAction_eq_zero_of_mono i μ hμ (idealAction_cokernel_eq_zero i _ htm)))
    (essImage_of_idealAction_eq_zero i hi.1 _ (idealAction_cokernel_eq_zero i _ htm))

/-- An extension whose middle term receives a lift of a surjection from an arbitrary module,
compatibly with a prescribed map on the ideal multiple, has that prescribed canonical map. -/
theorem firstOrderExtensionAction_eq_of_lift (hi : IsFirstOrderThickening i)
    (F K : SheafOfModules.{u} (structureSheafRing X))
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K)
    {P : SheafOfModules.{u} (structureSheafRing X')} (p : P ⟶ ambientPushforward i F) (hp : Epi p)
    (l : P ⟶ E.Z.left) (hl : l ≫ E.g = p)
    (hc : idealAction i P ≫ l =
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (idealSheafModule i)), p) : (_, _) ⟶ (_, _))) ≫
        (extensionTensorComparison i F ≫ (modulePushforward i).map c)) ≫ E.f) :
    (firstOrderExtensionAction i F K hi E).val = c := by
  have := hp
  have hmono : Mono E.f := E.mono_f
  have hepi : Epi (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (idealSheafModule i)), p) : (_, _) ⟶ (_, _)))) :=
    idealTensorFunctor_epi i p hp
  apply extensionTensorComparison_cancel i hi.1 _ c
  rw [← cancel_epi ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (idealSheafModule i)), p) : (_, _) ⟶ (_, _))), ← cancel_mono E.f, Category.assoc,
    firstOrderExtensionAction_comp_lift i hi F K E p l hl, hc]

/-- The first step of the source proof: when `𝒦` is an injective `𝒪_X`-module, every `𝒪_X`-linear
map `c : ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦` is the canonical map of an extension as in Tag 08L4.

The extension is the pushout of `0 ⟶ 𝒥 ⟶ ℋ' ⟶ i_* ℱ ⟶ 0` along the map `𝒥 ⟶ i_* 𝒦` extending
`c`, where `ℋ'` is a flat `𝒪_{X'}`-module covering `i_* ℱ` (**Stacks 05NI**). -/
theorem exists_firstOrderExtension_of_injective (hi : IsFirstOrderThickening i)
    (F K : SheafOfModules.{u} (structureSheafRing X)) (hK : Injective K)
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K) :
    ∃ E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0,
      (firstOrderExtensionAction i F K hi E).val = c := by
  classical
  obtain ⟨P, p, hflat, hp⟩ := exists_flat_epi (ambientPushforward i F)
  have := hp
  have hzero : idealAction i P ≫ p = 0 := by
    rw [idealAction_naturality i p, idealAction_eq_zero_of_essImage i hi.1 (ambientPushforward i F)
      (Functor.obj_mem_essImage (modulePushforward i) F), comp_zero]
  obtain ⟨γ, hγ⟩ := exists_idealAction_factorThru_of_injective i hi F K hK c P p hp hflat hzero
  have hseq : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
  have hpush := CategoryTheory.Abelian.pushoutShortComplex_shortExact hseq γ
  refine ⟨CategoryTheory.Abelian.shortExactYonedaExtension hpush, ?_⟩
  refine firstOrderExtensionAction_eq_of_lift i hi F K _ c p hp
    (pushout.inl (kernel.ι p) γ)
    (CategoryTheory.Abelian.inl_pushoutShortComplex_g
      (ShortComplex.mk (kernel.ι p) p (kernel.condition p)) γ) ?_
  have hmk : kernel.lift p (idealAction i P) hzero ≫ kernel.ι p = idealAction i P :=
    kernel.lift_ι _ _ _
  calc idealAction i P ≫ pushout.inl (kernel.ι p) γ
      = (kernel.lift p (idealAction i P) hzero ≫ kernel.ι p) ≫ pushout.inl (kernel.ι p) γ :=
        congrArg (fun z => z ≫ pushout.inl (kernel.ι p) γ) hmk.symm
    _ = kernel.lift p (idealAction i P) hzero ≫
          (kernel.ι p ≫ pushout.inl (kernel.ι p) γ) := Category.assoc _ _ _
    _ = kernel.lift p (idealAction i P) hzero ≫ (γ ≫ pushout.inr (kernel.ι p) γ) :=
        congrArg (fun z => kernel.lift p (idealAction i P) hzero ≫ z) pushout.condition
    _ = (kernel.lift p (idealAction i P) hzero ≫ γ) ≫ pushout.inr (kernel.ι p) γ :=
        (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun z => z ≫ pushout.inr (kernel.ι p) γ) hγ

/-! ### Steps 2 and 3: the obstruction class -/

/-- Tag 08L6 with an injective target: a pair of maps compatible with the canonical maps of two
extensions lifts to a map of the extensions, because the obstruction lies in the vanishing group
`Ext¹_{𝒪_X}(ℱ, 𝒥)`. -/
theorem exists_extensionMap_of_injective
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hi : IsFirstOrderThickening i) (F K J : SheafOfModules.{u} (structureSheafRing X))
    (hJ : Injective J)
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    (E' : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj J) 0)
    (a : K ⟶ J)
    (ha : (firstOrderExtensionAction i F K hi E).val ≫ a =
      (firstOrderExtensionAction i F J hi E').val) :
    ∃ b : E.Z.left ⟶ E'.Z.left,
      E.f ≫ b = (modulePushforward i).map a ≫ E'.f ∧ b ≫ E'.g = E.g := by
  have := hJ
  have hcompat := ha.trans (tensorSheafMap_id_id_comp (idealSheafPullback i) F _).symm
  have ho := mapLiftingObstruction i hi F K F J E E' (𝟙 F) a hcompat
  have hzero : ho.1 = 0 := by
    have hξ := CategoryTheory.Abelian.Ext.eq_zero_of_injective
      (CategoryTheory.Abelian.Ext.homEquiv.symm ho.1)
    calc ho.1 = (CategoryTheory.Abelian.Ext.homEquiv.symm ho.1).hom :=
          (CategoryTheory.Abelian.Ext.homEquiv.apply_symm_apply ho.1).symm
      _ = 0 := by rw [hξ, CategoryTheory.Abelian.Ext.zero_hom]
  obtain ⟨b, hb, hb'⟩ := ho.2.mp hzero
  exact ⟨b, hb, by rw [hb', (modulePushforward i).map_id, Category.comp_id]⟩

/-- One half of the third step of the source proof: if an extension as in Tag 08L4 with canonical
map `c` exists, then the extension `𝒟` of `ℱ` by `𝒬` obtained by pushing out along `𝒥 ⟶ 𝒬` and
descending to `X` is split, so its class vanishes. -/
theorem extClass_eq_zero_of_exists_extension
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hi : IsFirstOrderThickening i) (F K J Q : SheafOfModules.{u} (structureSheafRing X))
    (hJ : Injective J) (j : K ⟶ J) (q : J ⟶ Q) (hjq : j ≫ q = 0)
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K)
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj J) 0)
    (hE : (firstOrderExtensionAction i F J hi E).val = c ≫ j)
    (D : CategoryTheory.Abelian.YonedaExtension F Q 0)
    (cmp : E.Z.left ⟶ (modulePushforward i).obj D.Z.left)
    (hcR : cmp ≫ (modulePushforward i).map D.g = E.g)
    (hcL : (modulePushforward i).map q ≫ (modulePushforward i).map D.f = E.f ≫ cmp)
    (E₂ : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    (hE₂ : (firstOrderExtensionAction i F K hi E₂).val = c) :
    (CategoryTheory.Abelian.YonedaExtension.shortExact D).extClass = 0 := by
  have hfull : (modulePushforward i).Full :=
    (closedQuotientOfIsThickening i hi.1).full_modulePushforward
  have hfaith : (modulePushforward i).Faithful :=
    (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
  obtain ⟨b, hb, hb'⟩ := exists_extensionMap_of_injective i hi F K J hJ E₂ E j
    (hE₂ ▸ hE.symm)
  have hz : E₂.f ≫ (b ≫ cmp) = 0 := by
    rw [← Category.assoc, hb, Category.assoc, ← hcL, ← Category.assoc,
      map_comp_eq_zero_of_comp_eq_zero _ hjq, zero_comp]
  have hgcok := (CategoryTheory.Abelian.YonedaExtension.shortExact E₂).gIsCokernel
  have hs : E₂.g ≫ hgcok.desc (CokernelCofork.ofπ (b ≫ cmp) hz) = b ≫ cmp :=
    hgcok.fac _ WalkingParallelPair.one
  have hepi : Epi E₂.g := E₂.epi_g
  have hsg : hgcok.desc (CokernelCofork.ofπ (b ≫ cmp) hz) ≫
      (modulePushforward i).map D.g = 𝟙 ((modulePushforward i).obj F) := by
    refine (cancel_epi E₂.g).1 ?_
    rw [← Category.assoc, hs, Category.assoc, hcR, hb']
    exact (Category.comp_id _).symm
  refine (CategoryTheory.Abelian.extClass_eq_zero_iff_exists_section _).2
    ⟨(modulePushforward i).preimage (hgcok.desc (CokernelCofork.ofπ (b ≫ cmp) hz)), ?_⟩
  apply (modulePushforward i).map_injective
  rw [(modulePushforward i).map_comp, Functor.map_preimage, (modulePushforward i).map_id]
  exact hsg

/-- The other half of the third step of the source proof: if the class of `𝒟` vanishes, a
splitting of `𝒟` cuts out of the middle term of `E` an extension as in Tag 08L4 with canonical
map `c`. -/
theorem exists_extension_of_extClass_eq_zero
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hi : IsFirstOrderThickening i) (F K J Q : SheafOfModules.{u} (structureSheafRing X))
    (j : K ⟶ J) (q : J ⟶ Q) (hjq : j ≫ q = 0)
    (hKJ : (ShortComplex.mk j q hjq).ShortExact)
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K)
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj J) 0)
    (hE : (firstOrderExtensionAction i F J hi E).val = c ≫ j)
    (D : CategoryTheory.Abelian.YonedaExtension F Q 0)
    (cmp : E.Z.left ⟶ (modulePushforward i).obj D.Z.left)
    (hcR : cmp ≫ (modulePushforward i).map D.g = E.g)
    (hcL : (modulePushforward i).map q ≫ (modulePushforward i).map D.f = E.f ≫ cmp)
    (hD : (CategoryTheory.Abelian.YonedaExtension.shortExact D).extClass = 0) :
    ∃ E₂ : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0,
      (firstOrderExtensionAction i F K hi E₂).val = c := by
  have hlim : PreservesFiniteLimits (modulePushforward i) :=
    preservesFiniteLimits_modulePushforward i
  have hcolim : PreservesFiniteColimits (modulePushforward i) :=
    preservesFiniteColimits_modulePushforward i hi.1
  have hmonoj : Mono j := hKJ.mono_f
  obtain ⟨s, hs⟩ := (CategoryTheory.Abelian.extClass_eq_zero_iff_exists_section _).1 hD
  obtain ⟨hzc, hcomp⟩ := CategoryTheory.Abelian.kernelPairShortComplex_shortExact
    (hKJ.map_of_exact (modulePushforward i))
    (CategoryTheory.Abelian.YonedaExtension.shortExact E)
    ((CategoryTheory.Abelian.YonedaExtension.shortExact D).map_of_exact (modulePushforward i))
    cmp hcL.symm hcR
  have hpb := CategoryTheory.Abelian.pullbackShortComplex_shortExact hcomp
    ((modulePushforward i).map s)
  refine ⟨CategoryTheory.Abelian.shortExactYonedaExtension hpb, ?_⟩
  have hv1 : (CategoryTheory.Abelian.shortExactYonedaExtension hpb).f ≫
      pullback.snd ((modulePushforward i).map s) cmp =
      (modulePushforward i).map j ≫ E.f := pullback.lift_snd _ _ _
  have hpc : pullback.fst ((modulePushforward i).map s) cmp ≫ (modulePushforward i).map s =
      pullback.snd ((modulePushforward i).map s) cmp ≫ cmp := pullback.condition
  have hsid : (modulePushforward i).map s ≫ (modulePushforward i).map D.g =
      𝟙 ((modulePushforward i).obj F) := by
    rw [← Functor.map_comp, hs, (modulePushforward i).map_id]
  have hv3 : pullback.snd ((modulePushforward i).map s) cmp ≫ E.g =
      pullback.fst ((modulePushforward i).map s) cmp :=
    (congrArg (fun z => pullback.snd ((modulePushforward i).map s) cmp ≫ z) hcR.symm).trans
      (((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (modulePushforward i).map D.g) hpc.symm).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun z => pullback.fst ((modulePushforward i).map s) cmp ≫ z)
              hsid)))).trans (Category.comp_id _))
  have hv3' : pullback.snd ((modulePushforward i).map s) cmp ≫ E.g =
      (CategoryTheory.Abelian.shortExactYonedaExtension hpb).g ≫
        (modulePushforward i).map (𝟙 F) :=
    hv3.trans ((Category.comp_id _).symm.trans
      (congrArg (fun z => (CategoryTheory.Abelian.shortExactYonedaExtension hpb).g ≫ z)
        ((modulePushforward i).map_id F).symm))
  have haction := ExtensionPair.extensionAction_naturality
    { X := X, X' := X', i := i, firstOrder := hi, F := F, K := K, G := F, L := J
      firstExtension := CategoryTheory.Abelian.shortExactYonedaExtension hpb
      secondExtension := E, quotientMap := 𝟙 F, kernelMap := j }
    { hom := pullback.snd ((modulePushforward i).map s) cmp
      kernel_commutes := hv1
      quotient_commutes := hv3' }
  refine (cancel_mono j).1 (haction.trans ?_)
  exact (tensorSheafMap_id_id_comp (idealSheafPullback i) F _).trans hE

/-! ### The presentation of the obstruction and the class it defines -/

/-- A *presentation* of the obstruction of Tag 08L8 for an `𝒪_X`-linear map
`c : ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦`: an embedding of `𝒦` into an injective `𝒪_X`-module `𝒥` with quotient
`𝒬`, an extension of `i_* ℱ` by `i_* 𝒥` as in Tag 08L4 whose canonical map is `c` followed by
`𝒦 ⟶ 𝒥`, and an extension of `ℱ` by `𝒬` identified with the pushout of the former along
`i_*(𝒥 ⟶ 𝒬)`. This is the data the source proof produces in its first two steps. -/
structure ObstructionPresentation (hi : IsFirstOrderThickening i)
    (F K : SheafOfModules.{u} (structureSheafRing X))
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K) where
  /-- An injective `𝒪_X`-module containing `𝒦`. -/
  J : SheafOfModules.{u} (structureSheafRing X)
  /-- The quotient `𝒬 = 𝒥/𝒦`. -/
  Q : SheafOfModules.{u} (structureSheafRing X)
  /-- `𝒥` is injective. -/
  injective : Injective J
  /-- The embedding `𝒦 ⟶ 𝒥`. -/
  j : K ⟶ J
  /-- The surjection `𝒥 ⟶ 𝒬`. -/
  q : J ⟶ Q
  /-- The composite `𝒦 ⟶ 𝒥 ⟶ 𝒬` vanishes. -/
  zero : j ≫ q = 0
  /-- `0 ⟶ 𝒦 ⟶ 𝒥 ⟶ 𝒬 ⟶ 0` is short exact. -/
  exact : (ShortComplex.mk j q zero).ShortExact
  /-- An extension of `i_* ℱ` by `i_* 𝒥` as in Tag 08L4. -/
  thickExtension : CategoryTheory.Abelian.YonedaExtension
    ((modulePushforward i).obj F) ((modulePushforward i).obj J) 0
  /-- Its canonical map of Tag 08L4 is `c` followed by `𝒦 ⟶ 𝒥`. -/
  action : (firstOrderExtensionAction i F J hi thickExtension).val = c ≫ j
  /-- An extension of `ℱ` by `𝒬` by `𝒪_X`-modules. -/
  quotientExtension : CategoryTheory.Abelian.YonedaExtension F Q 0
  /-- The comparison from the middle term upstairs to the direct image of the middle term
  downstairs. -/
  comparison : thickExtension.Z.left ⟶ (modulePushforward i).obj quotientExtension.Z.left
  /-- The comparison turns the direct image of `𝒥 ⟶ 𝒬 ⟶ 𝒟'` into the injection of
  `thickExtension`, which is what makes `quotientExtension` the pushout. -/
  comparison_left : (modulePushforward i).map q ≫
    (modulePushforward i).map quotientExtension.f = thickExtension.f ≫ comparison
  /-- The comparison is compatible with the two surjections onto `i_* ℱ`. -/
  comparison_right : comparison ≫ (modulePushforward i).map quotientExtension.g =
    thickExtension.g

/-- The class in `Ext²_{𝒪_X}(ℱ, 𝒦)` defined by a presentation of the obstruction: the Yoneda
product of the class of the extension of `ℱ` by `𝒬` with the class of `0 ⟶ 𝒦 ⟶ 𝒥 ⟶ 𝒬 ⟶ 0`. -/
noncomputable def ObstructionPresentation.obstruction
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    {hi : IsFirstOrderThickening i} {F K : SheafOfModules.{u} (structureSheafRing X)}
    {c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K}
    (P : ObstructionPresentation i hi F K c) : CategoryTheory.Abelian.Ext F K 2 :=
  (CategoryTheory.Abelian.YonedaExtension.shortExact P.quotientExtension).extClass.comp
    P.exact.extClass (by decide)

/-- The class of a presentation vanishes exactly when there is an extension as in Tag 08L4 with
canonical map `c`: this is the third step of the source proof. -/
theorem ObstructionPresentation.obstruction_eq_zero_iff
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    {hi : IsFirstOrderThickening i} {F K : SheafOfModules.{u} (structureSheafRing X)}
    {c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K}
    (P : ObstructionPresentation i hi F K c) :
    P.obstruction = 0 ↔ ∃ E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0,
      (firstOrderExtensionAction i F K hi E).val = c := by
  constructor
  · intro h
    exact exists_extension_of_extClass_eq_zero i hi F K P.J P.Q P.j P.q P.zero P.exact c
      P.thickExtension P.action P.quotientExtension P.comparison P.comparison_right
      P.comparison_left
      ((CategoryTheory.Abelian.extClass_comp_eq_zero_iff P.exact _ P.injective).1 h)
  · rintro ⟨E₂, hE₂⟩
    exact (CategoryTheory.Abelian.extClass_comp_eq_zero_iff P.exact _ P.injective).2
      (extClass_eq_zero_of_exists_extension i hi F K P.J P.Q P.injective P.j P.q P.zero c
        P.thickExtension P.action P.quotientExtension P.comparison P.comparison_right
        P.comparison_left E₂ hE₂)

/-- A presentation of the obstruction exists: embed `𝒦` in its injective hull, use the first step
of the source proof for `c` followed by `𝒦 ⟶ 𝒥`, push out along `i_*(𝒥 ⟶ 𝒬)` and descend the
result to `X`, which is possible because the canonical map of the pushout is
`c ≫ (𝒦 ⟶ 𝒥) ≫ (𝒥 ⟶ 𝒬) = 0` by Tag 08L5 part (1) and **Stacks 08KS**. -/
theorem exists_obstructionPresentation (hi : IsFirstOrderThickening i)
    (F K : SheafOfModules.{u} (structureSheafRing X))
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K) :
    Nonempty (ObstructionPresentation i hi F K c) := by
    classical
    have hfull : (modulePushforward i).Full :=
      (closedQuotientOfIsThickening i hi.1).full_modulePushforward
    have hfaith : (modulePushforward i).Faithful :=
      (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
    have hlim : PreservesFiniteLimits (modulePushforward i) :=
      preservesFiniteLimits_modulePushforward i
    have hcolim : PreservesFiniteColimits (modulePushforward i) :=
      preservesFiniteColimits_modulePushforward i hi.1
    have hJinj : Injective (Injective.under K) := Injective.injective_under K
    have hjmono : Mono (Injective.ι K) := Injective.ι_mono K
    have hKJ : (ShortComplex.mk (Injective.ι K) (cokernel.π (Injective.ι K))
        (cokernel.condition (Injective.ι K))).ShortExact :=
      ShortComplex.ShortExact.mk'
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hjmono inferInstance
    obtain ⟨E, hE⟩ := exists_firstOrderExtension_of_injective i hi F (Injective.under K) hJinj
      (c ≫ Injective.ι K)
    have hpush := CategoryTheory.Abelian.pushoutShortComplex_shortExact
      (CategoryTheory.Abelian.YonedaExtension.shortExact E)
      ((modulePushforward i).map (cokernel.π (Injective.ι K)))
    have hcond : E.f ≫ pushout.inl E.f
          ((modulePushforward i).map (cokernel.π (Injective.ι K))) =
        (modulePushforward i).map (cokernel.π (Injective.ι K)) ≫
          pushout.inr E.f ((modulePushforward i).map (cokernel.π (Injective.ι K))) :=
      pushout.condition
    have hquot : pushout.inl E.f
          ((modulePushforward i).map (cokernel.π (Injective.ι K))) ≫
        (CategoryTheory.Abelian.shortExactYonedaExtension hpush).g =
        E.g ≫ (modulePushforward i).map (𝟙 F) := by
      rw [(modulePushforward i).map_id, Category.comp_id]
      exact CategoryTheory.Abelian.inl_pushoutShortComplex_g
        (ShortComplex.mk E.f E.g (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E))
        ((modulePushforward i).map (cokernel.π (Injective.ι K)))
    have haction := ExtensionPair.extensionAction_naturality
      { X := X, X' := X', i := i, firstOrder := hi, F := F, K := Injective.under K, G := F
        L := cokernel (Injective.ι K), firstExtension := E
        secondExtension := CategoryTheory.Abelian.shortExactYonedaExtension hpush
        quotientMap := 𝟙 F, kernelMap := cokernel.π (Injective.ι K) }
      { hom := pushout.inl E.f ((modulePushforward i).map (cokernel.π (Injective.ι K)))
        kernel_commutes := hcond
        quotient_commutes := hquot }
    have h3 : (firstOrderExtensionAction i F (cokernel (Injective.ι K)) hi
        (CategoryTheory.Abelian.shortExactYonedaExtension hpush)).val =
        c ≫ (Injective.ι K ≫ cokernel.π (Injective.ι K)) :=
      (tensorSheafMap_id_id_comp (idealSheafPullback i) F _).symm.trans (haction.symm.trans
        ((congrArg (fun z => z ≫ cokernel.π (Injective.ι K)) hE).trans (Category.assoc _ _ _)))
    have hmapzero : (modulePushforward i).map (firstOrderExtensionAction i F
        (cokernel (Injective.ι K)) hi
        (CategoryTheory.Abelian.shortExactYonedaExtension hpush)).val = 0 := by
      rw [h3, Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero]
    obtain ⟨D, e, hef, heg⟩ := CategoryTheory.Abelian.exists_yonedaExtension_descent
      (modulePushforward i) (CategoryTheory.Abelian.shortExactYonedaExtension hpush)
      (essImage_of_extensionAction_eq_zero i hi F (cokernel (Injective.ι K)) _ hmapzero)
    have heinv : e.inv ≫ (modulePushforward i).map D.g =
        (CategoryTheory.Abelian.shortExactYonedaExtension hpush).g := by
      rw [← heg, Iso.inv_hom_id_assoc]
    have hcR : (pushout.inl E.f ((modulePushforward i).map
          (cokernel.π (Injective.ι K))) ≫ e.inv) ≫ (modulePushforward i).map D.g = E.g :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => pushout.inl E.f ((modulePushforward i).map
            (cokernel.π (Injective.ι K))) ≫ z) heinv).trans
          (CategoryTheory.Abelian.inl_pushoutShortComplex_g
            (ShortComplex.mk E.f E.g (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E))
            ((modulePushforward i).map (cokernel.π (Injective.ι K)))))
    have hfinv : (CategoryTheory.Abelian.shortExactYonedaExtension hpush).f ≫ e.inv =
        (modulePushforward i).map D.f := by
      rw [← hef, Category.assoc, e.hom_inv_id, Category.comp_id]
    have hcL : (modulePushforward i).map (cokernel.π (Injective.ι K)) ≫
          (modulePushforward i).map D.f =
        E.f ≫ (pushout.inl E.f ((modulePushforward i).map
          (cokernel.π (Injective.ι K))) ≫ e.inv) :=
      (congrArg (fun z => (modulePushforward i).map (cokernel.π (Injective.ι K)) ≫ z)
        hfinv.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ e.inv) hcond.symm).trans (Category.assoc _ _ _)))
    exact ⟨{ J := Injective.under K, Q := cokernel (Injective.ι K), injective := hJinj
             j := Injective.ι K, q := cokernel.π (Injective.ι K)
             zero := cokernel.condition (Injective.ι K), exact := hKJ
             thickExtension := E, action := hE, quotientExtension := D
             comparison := pushout.inl E.f
               ((modulePushforward i).map (cokernel.π (Injective.ι K))) ≫ e.inv
             comparison_left := hcL, comparison_right := hcR }⟩

/-- The class of a presentation does not depend on the presentation: two presentations are
compared by extending the embedding of `𝒦` across the second injective module, lifting that to a
map of the two extensions upstairs (Tag 08L6 with injective target), and descending the induced
map of pushouts to `X`; naturality of the extension class in both variables then identifies the
two Yoneda products. -/
theorem ObstructionPresentation.obstruction_eq
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    {hi : IsFirstOrderThickening i} {F K : SheafOfModules.{u} (structureSheafRing X)}
    {c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K}
    (P P' : ObstructionPresentation i hi F K c) : P.obstruction = P'.obstruction := by
  classical
  have hfull : (modulePushforward i).Full :=
    (closedQuotientOfIsThickening i hi.1).full_modulePushforward
  have hfaith : (modulePushforward i).Faithful :=
    (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
  have hlim : PreservesFiniteLimits (modulePushforward i) :=
    preservesFiniteLimits_modulePushforward i
  have hcolim : PreservesFiniteColimits (modulePushforward i) :=
    preservesFiniteColimits_modulePushforward i hi.1
  have hJ' : Injective P'.J := P'.injective
  have hjmono : Mono P.j := P.exact.mono_f
  obtain ⟨a, ha⟩ : ∃ a : P.J ⟶ P'.J, P.j ≫ a = P'.j :=
    ⟨Injective.factorThru P'.j P.j, Injective.comp_factorThru _ _⟩
  obtain ⟨d, hd⟩ : ∃ d : P.Q ⟶ P'.Q, P.q ≫ d = a ≫ P'.q :=
    ⟨P.exact.gIsCokernel.desc (CokernelCofork.ofπ (a ≫ P'.q)
        (by rw [← Category.assoc, ha, P'.zero])),
      P.exact.gIsCokernel.fac _ WalkingParallelPair.one⟩
  obtain ⟨b, hb, hb'⟩ := exists_extensionMap_of_injective i hi F P.J P'.J P'.injective
    P.thickExtension P'.thickExtension a
    ((congrArg (fun z => z ≫ a) P.action).trans
      ((Category.assoc c P.j a).trans
        ((congrArg (fun z => c ≫ z) ha).trans P'.action.symm)))
  have hs : IsPushout P.thickExtension.f ((modulePushforward i).map P.q) P.comparison
      ((modulePushforward i).map P.quotientExtension.f) :=
    CategoryTheory.Abelian.isPushout_of_shortExact
      (CategoryTheory.Abelian.YonedaExtension.shortExact P.thickExtension)
      ((CategoryTheory.Abelian.YonedaExtension.shortExact P.quotientExtension).map_of_exact
        (modulePushforward i))
      ((modulePushforward i).map P.q) P.comparison P.comparison_left.symm P.comparison_right
  obtain ⟨t, ht, htleft⟩ : ∃ t : (modulePushforward i).obj P.quotientExtension.Z.left ⟶
        (modulePushforward i).obj P'.quotientExtension.Z.left,
      P.comparison ≫ t = b ≫ P'.comparison ∧
        (modulePushforward i).map P.quotientExtension.f ≫ t =
          (modulePushforward i).map d ≫
            (modulePushforward i).map P'.quotientExtension.f := by
    refine ⟨hs.desc (b ≫ P'.comparison) ((modulePushforward i).map d ≫
      (modulePushforward i).map P'.quotientExtension.f) ?_, hs.inl_desc _ _ _,
      hs.inr_desc _ _ _⟩
    rw [← Category.assoc, hb, Category.assoc, ← P'.comparison_left, ← Category.assoc,
      ← Functor.map_comp, ← hd, Functor.map_comp, Category.assoc]
  have htright : t ≫ (modulePushforward i).map P'.quotientExtension.g =
      (modulePushforward i).map P.quotientExtension.g := by
    refine hs.hom_ext ?_ ?_
    · rw [← Category.assoc, ht, Category.assoc, P'.comparison_right, P.comparison_right, hb']
    · have hzl : (modulePushforward i).map P.quotientExtension.f ≫
          (t ≫ (modulePushforward i).map P'.quotientExtension.g) = 0 := by
        rw [← Category.assoc, htleft, Category.assoc, map_comp_eq_zero_of_comp_eq_zero _
          (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero P'.quotientExtension), comp_zero]
      exact hzl.trans (map_comp_eq_zero_of_comp_eq_zero _
        (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero P.quotientExtension)).symm
  obtain ⟨e, hel, her⟩ : ∃ e : P.quotientExtension.Z.left ⟶ P'.quotientExtension.Z.left,
      P.quotientExtension.f ≫ e = d ≫ P'.quotientExtension.f ∧
        e ≫ P'.quotientExtension.g = P.quotientExtension.g := by
    refine ⟨(modulePushforward i).preimage t, (modulePushforward i).map_injective ?_,
      (modulePushforward i).map_injective ?_⟩
    · rw [(modulePushforward i).map_comp, (modulePushforward i).map_comp, Functor.map_preimage]
      exact htleft
    · rw [(modulePushforward i).map_comp, Functor.map_preimage]
      exact htright
  have hext := (CategoryTheory.Abelian.YonedaExtension.shortExact
      P.quotientExtension).extClass_naturality
    (CategoryTheory.Abelian.YonedaExtension.shortExact P'.quotientExtension)
    { τ₁ := d, τ₂ := e, τ₃ := 𝟙 F
      comm₁₂ := hel.symm
      comm₂₃ := by simpa using her }
  have hbase := P.exact.extClass_naturality P'.exact
    { τ₁ := 𝟙 K, τ₂ := a, τ₃ := d
      comm₁₂ := by simpa using ha.symm
      comm₂₃ := hd.symm }
  dsimp only at hext hbase
  simp only [CategoryTheory.Abelian.Ext.mk₀_id_comp,
    CategoryTheory.Abelian.Ext.comp_mk₀_id] at hext hbase
  unfold ObstructionPresentation.obstruction
  rw [hbase, ← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero, hext]

/-- The obstruction class `o(ℱ, 𝒦, c) ∈ Ext²_{𝒪_X}(ℱ, 𝒦)` of Tag 08L8: the class of a
presentation of the obstruction, which by
`AlgebraicGeometry.RingedSpaceThickening.ObstructionPresentation.obstruction_eq` does not depend
on which presentation is used. -/
noncomputable def obstructionClass
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hi : IsFirstOrderThickening i) (F K : SheafOfModules.{u} (structureSheafRing X))
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K) :
    CategoryTheory.Abelian.Ext F K 2 :=
  (Classical.choice (exists_obstructionPresentation i hi F K c)).obstruction

/-- The obstruction class is the class of *every* presentation of the obstruction, so the
construction is independent of the injective embedding of `𝒦`, of the flat cover used in the
first step, and of the descent of the pushout. -/
theorem obstructionClass_eq
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hi : IsFirstOrderThickening i) (F K : SheafOfModules.{u} (structureSheafRing X))
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K)
    (P : ObstructionPresentation i hi F K c) :
    obstructionClass i hi F K c = P.obstruction :=
  ObstructionPresentation.obstruction_eq
    (P := Classical.choice (exists_obstructionPresentation i hi F K c)) (P' := P)

/-- The obstruction class vanishes exactly when there is an extension of `𝒪_{X'}`-modules as in
Tag 08L4 whose canonical map is `c`. -/
theorem obstructionClass_eq_zero_iff
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hi : IsFirstOrderThickening i) (F K : SheafOfModules.{u} (structureSheafRing X))
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K) :
    obstructionClass i hi F K c = 0 ↔
      ∃ E : CategoryTheory.Abelian.YonedaExtension
        ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0,
        (firstOrderExtensionAction i F K hi E).val = c :=
  (Classical.choice (exists_obstructionPresentation i hi F K c)).obstruction_eq_zero_iff

/-- **Stacks Project, Tag 08L8.** The obstruction `o(ℱ, 𝒦, c) ∈ Ext²_{𝒪_X}(ℱ, 𝒦)` to the
existence of an extension of `𝒪_{X'}`-modules `0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` as in Tag 08L4 whose
canonical map `c_{ℱ'}` is a prescribed `𝒪_X`-linear map `c : ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦`.

The class is `AlgebraicGeometry.RingedSpaceThickening.obstructionClass`, and the bundled property
is the content of the lemma: it vanishes exactly when such an extension exists. -/
@[stacks 08L8]
noncomputable def extensionExistenceObstruction
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hi : IsFirstOrderThickening i) (F K : SheafOfModules.{u} (structureSheafRing X))
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K) :
    { o : CategoryTheory.Abelian.zExt F K 2 //
      o = 0 ↔ ∃ E : CategoryTheory.Abelian.YonedaExtension
          ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0,
        (firstOrderExtensionAction i F K hi E).val = c } :=
  ⟨(obstructionClass i hi F K c).hom,
    (CategoryTheory.Abelian.Ext.homAddEquiv.map_eq_zero_iff
        (x := obstructionClass i hi F K c)).trans
      (obstructionClass_eq_zero_iff i hi F K c)⟩

/-- The element of the subtype of Tag 08L8 is the constructed class
`AlgebraicGeometry.RingedSpaceThickening.obstructionClass`, read as a morphism of the derived
category. -/
theorem extensionExistenceObstruction_val
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hi : IsFirstOrderThickening i) (F K : SheafOfModules.{u} (structureSheafRing X))
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K) :
    (extensionExistenceObstruction i hi F K c).val = (obstructionClass i hi F K c).hom := rfl

/-- The element of the subtype of Tag 08L8 is the Yoneda product attached to any presentation of
the obstruction. -/
theorem extensionExistenceObstruction_val_eq
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hi : IsFirstOrderThickening i) (F K : SheafOfModules.{u} (structureSheafRing X))
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K)
    (P : ObstructionPresentation i hi F K c) :
    (extensionExistenceObstruction i hi F K c).val = P.obstruction.hom :=
  congrArg (fun x : CategoryTheory.Abelian.Ext F K 2 => x.hom)
    (obstructionClass_eq i hi F K c P)

end AlgebraicGeometry.RingedSpaceThickening

end
