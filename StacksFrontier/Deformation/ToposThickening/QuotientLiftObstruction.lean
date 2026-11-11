module

public import StacksFrontier.Deformation.ToposThickening.IdealActionMono
public import StacksFrontier.Deformation.ToposThickening.ModuleMapObstruction
import StacksCore.Tactic.StacksAttribute

/-!
# The obstruction to lifting a quotient across a first order thickening

Let `(f, f')` be a strict morphism of first order thickenings of ringed topoi as in
Situation 08M7

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_ℬ) --t-->  (Sh(B'), O_{ℬ'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `𝒥 = Ker(t^♯) ⊂ O_{ℬ'}`, let `ℱ'` be an
`O'`-module flat over `O_{ℬ'}` and set `ℱ = i^*ℱ'`. A quotient `ℱ ⟶ 𝒬` with kernel `𝒦` and `𝒬`
flat over `O_ℬ` is the datum of Remark 0CZU of the Stacks project, read in the setting of
arbitrary ringed topoi in which, as the remark says, all of its arguments work. This file builds
the objects of that remark:

* the short exact sequence `0 ⟶ f^*𝒥 ⊗_O ℱ ⟶ ℱ' ⟶ ℱ ⟶ 0`;
* the preimage `π⁻¹(𝒦) ⊂ ℱ'` of `𝒦` under the reduction `π : ℱ' ⟶ ℱ`, and the canonical map
  `I·ℱ' = ℱ ⊗ f^*𝒥 ⟶ 𝒬 ⊗ f^*𝒥` whose kernel is the image of `𝒦 ⊗ f^*𝒥`.

## Notation

`O`-modules are sheaves of modules on the site of `(Sh(C), O)`, as in Stacks 08MT
(`Deformation.ToposThickening.relativeModuleMapObstructionClass`); `i^*` is
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules`, `i_*` is
`AlgebraicGeometry.RingedToposHom.pushforwardModules`, and the reduction `π` is the unit of the
adjunction `i^* ⊣ i_*`. For an `O`-module `𝒢` the remark abbreviates `f^*𝒥 ⊗_O 𝒢` as
`𝒢 ⊗_{O_ℬ} 𝒥`; this is `Deformation.ToposThickening.baseIdealTensor`, written `𝒢 ⊗ f^*𝒥` in the
tensor order of Stacks 08MT.

## References

* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u w v' u' vS uS wS vS' uS' wS' e

namespace Deformation.ToposThickening

/-- A composite `Y ≫ h ≫ k` vanishes as soon as, after an epimorphism `E`, it becomes
`K ≫ θ ≫ θ⁻¹ ≫ q` with `K ≫ q = 0`. -/
theorem eq_zero_of_epi_comp_of_factor {C : Type*} [Category C] [HasZeroMorphisms C]
    {a b c d e a' : C} (E : a ⟶ b) [Epi E] (Y : b ⟶ c) (h : c ⟶ d) (k : d ⟶ e) (K : a ⟶ a')
    (B : a' ⟶ c) (θ : a' ⟶ d) [IsIso θ] (q : a' ⟶ e) (hθ : B ≫ h = θ) (hEY : E ≫ Y = K ≫ B)
    (hk : k = inv θ ≫ q) (hq : K ≫ q = 0) : Y ≫ h ≫ k = 0 := by
  rw [← cancel_epi E, comp_zero, ← Category.assoc, hEY, Category.assoc, ← Category.assoc B, hθ,
    hk, IsIso.hom_inv_id_assoc, hq]

/-- Bookkeeping for `Deformation.ToposThickening.quotientLiftIdealAction_eq`. -/
theorem comp_comp_comp_eq_of_comm {C : Type*} [Category C] {a b c d e g : C}
    {U : a ⟶ b} {R : b ⟶ c} [IsIso R] {P : a ⟶ d} {Y : d ⟶ c} {H : c ⟶ g} {ι : g ⟶ e}
    {act : b ⟶ e} (hr : U ≫ R = P ≫ Y) (hH : H ≫ ι = inv R ≫ act) :
    (P ≫ Y ≫ H) ≫ ι = U ≫ act := by
  calc (P ≫ Y ≫ H) ≫ ι = (P ≫ Y) ≫ (H ≫ ι) := by simp only [Category.assoc]
    _ = (U ≫ R) ≫ (inv R ≫ act) := by rw [hr, hH]
    _ = U ≫ act := by simp

/-- Bookkeeping for `Deformation.ToposThickening.quotientLiftCanonicalMap_isColimit`. -/
theorem comp_comp_eq_zero_of_comm {C : Type*} [Category C] [HasZeroMorphisms C]
    {a b c d e g z : C} {E : a ⟶ b} {Ψ : b ⟶ c} {Y : c ⟶ d} {H : d ⟶ e} {k : e ⟶ z}
    {K : a ⟶ g} {B : g ⟶ d} {θ : g ⟶ e} (hEY : E ≫ Ψ ≫ Y = K ≫ B) (hθ : B ≫ H = θ)
    (h0 : Ψ ≫ Y ≫ H ≫ k = 0) : K ≫ θ ≫ k = 0 := by
  rw [← hθ, Category.assoc, ← Category.assoc K, ← hEY]
  simp only [Category.assoc, h0, comp_zero]

/-- Bookkeeping: a composite whose last factor kills `W` kills `W`. -/
theorem comp_six_comp_eq_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {a b c d e g h z : C} (p₁ : a ⟶ b) (p₂ : b ⟶ c) (p₃ : c ⟶ d) (p₄ : d ⟶ e) (p₅ : e ⟶ g)
    (p₆ : g ⟶ h) {W : h ⟶ z} (hW : p₆ ≫ W = 0) : (p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ p₅ ≫ p₆) ≫ W = 0 := by
  simp only [Category.assoc, hW, comp_zero]

/-- Bookkeeping: reassociation of a four-fold composite. -/
theorem comp_comp_comp_comp_assoc {C : Type*} [Category C] {a b c d e g : C} (p₁ : a ⟶ b)
    (p₂ : b ⟶ c) (p₃ : c ⟶ d) (p₄ : d ⟶ e) (p₅ : e ⟶ g) :
    ((p₁ ≫ p₂) ≫ p₃ ≫ p₄) ≫ p₅ = p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ p₅ := by
  simp only [Category.assoc]

/-- **The kernel of a cokernel is the image**: if `φ` is a cokernel of `u : A ⟶ F`, then the kernel
of `φ` is a subobject `𝒦` of `F` exactly when `u` factors as an epimorphism onto `𝒦` followed by
the inclusion of `𝒦`. -/
theorem mk_kernelι_eq_iff_exists_epi {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {A F G : 𝒜}
    (u : A ⟶ F) (φ : F ⟶ G) (w : u ≫ φ = 0) (hφ : IsColimit (CokernelCofork.ofπ φ w))
    (K : Subobject F) :
    Subobject.mk (kernel.ι φ) = K ↔ ∃ e : A ⟶ (K : 𝒜), Epi e ∧ e ≫ K.arrow = u := by
  have hex : (ShortComplex.mk u φ w).Exact := ShortComplex.exact_of_g_is_cokernel _ hφ
  have hepi : Epi (kernel.lift φ u w) := hex.epi_kernelLift
  constructor
  · intro h
    have h' : Subobject.mk (kernel.ι φ) = Subobject.mk K.arrow := h.trans
        (Subobject.mk_arrow K).symm
    refine ⟨kernel.lift φ u w ≫ (Subobject.isoOfMkEqMk _ _ h').hom, epi_comp _ _, ?_⟩
    rw [Category.assoc, Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp, kernel.lift_ι]
  · rintro ⟨e, he, hu⟩
    have hK : K.arrow ≫ φ = 0 := by
      rw [← cancel_epi e, ← Category.assoc, hu, w, comp_zero]
    have hfac : kernel.lift φ u w = e ≫ kernel.lift φ K.arrow hK := by
      apply (cancel_mono (kernel.ι φ)).1
      rw [Category.assoc, kernel.lift_ι, kernel.lift_ι, hu]
    have : Epi (kernel.lift φ K.arrow hK) := by
      rw [hfac] at hepi
      exact epi_of_epi e _
    have : IsIso (kernel.lift φ K.arrow hK) := isIso_of_mono_of_epi _
    refine (Subobject.mk_eq_mk_of_comm _ _ (asIso (kernel.lift φ K.arrow hK)).symm ?_).trans
      (Subobject.mk_arrow K)
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, kernel.lift_ι]

/-- **Dividing a short exact sequence by a subobject of its first term.** Let
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be short exact, `u : D ⟶ X₁` a map and `q : X₁ ⟶ A` a cokernel of `u`.
Then `0 ⟶ A ⟶ X₂/u(D) ⟶ X₃ ⟶ 0` is short exact. -/
theorem shortExact_cokernel_comp {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {S : ShortComplex 𝒜}
    (hS : S.ShortExact) {D A : 𝒜} (u : D ⟶ S.X₁) (q : S.X₁ ⟶ A) (hu : u ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hu)) (a : A ⟶ cokernel (u ≫ S.f))
    (ha : q ≫ a = S.f ≫ cokernel.π (u ≫ S.f)) :
    (ShortComplex.mk a (cokernel.desc (u ≫ S.f) S.g (by rw [Category.assoc, S.zero, comp_zero]))
      (Cofork.IsColimit.hom_ext hq (by
        change q ≫ _ = q ≫ 0
        rw [comp_zero, ← Category.assoc, ha, Category.assoc, cokernel.π_desc,
          S.zero]))).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hqepi : Epi q := ⟨fun {Z} g h hgh => Cofork.IsColimit.hom_ext hq hgh⟩
  have hepi : Epi (cokernel.desc (u ≫ S.f) S.g (by rw [Category.assoc, S.zero, comp_zero])) := by
    have : Epi (cokernel.π (u ≫ S.f) ≫
      cokernel.desc (u ≫ S.f) S.g (by rw [Category.assoc, S.zero, comp_zero])) := by
      rw [cokernel.π_desc]; infer_instance
    exact epi_of_epi (cokernel.π _) _
  refine ShortComplex.ShortExact.mk' ?_ ?_ hepi
  · rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro Z z hz
    dsimp at z hz
    obtain ⟨Z₁, π₁, hπ₁, b, hb⟩ := surjective_up_to_refinements_of_epi (cokernel.π (u ≫ S.f)) z
    have hbg : b ≫ S.g = 0 := by
      rw [← cokernel.π_desc (u ≫ S.f) S.g (by rw [Category.assoc, S.zero, comp_zero]),
        ← Category.assoc, ← hb, Category.assoc, hz, comp_zero]
    obtain ⟨Z₂, π₂, hπ₂, x, hx⟩ := hS.exact.exact_up_to_refinements b hbg
    refine ⟨Z₂, π₂ ≫ π₁, epi_comp _ _, x ≫ q, ?_⟩
    dsimp
    rw [Category.assoc, hb, ← Category.assoc, hx, Category.assoc, Category.assoc, ha]
  · apply (Preadditive.mono_iff_cancel_zero _).2
    intro Z z hz
    obtain ⟨Z₁, π₁, hπ₁, y, hy⟩ := surjective_up_to_refinements_of_epi q z
    have hyf : (y ≫ S.f) ≫ cokernel.π (u ≫ S.f) = 0 := by
      rw [Category.assoc, ← ha, ← Category.assoc, ← hy, Category.assoc, hz, comp_zero]
    obtain ⟨Z₂, π₂, hπ₂, v, hv⟩ :=
      (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements (cokernelIsCokernel _)
        (y ≫ S.f)).1 hyf
    have hv' : π₂ ≫ y = v ≫ u := by
      apply (cancel_mono S.f).1
      rw [Category.assoc, hv, Category.assoc]
    apply (cancel_epi π₁).1
    rw [comp_zero, hy]
    apply (cancel_epi π₂).1
    rw [comp_zero, ← Category.assoc, hv', Category.assoc, hu, comp_zero]

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

/-- **The remark's `𝒢 ⊗_{O_T} 𝒥`**: the endofunctor `𝒢 ↦ 𝒢 ⊗_O f^*𝒥` of `O`-modules, the
coefficient functor of Stacks 08MT. -/
noncomputable abbrev baseIdealTensor :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).flip.obj
    (basePullbackIdeal t f ht)

section CanonicalMap

open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap multiplicationMap)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)

/-- **The comparison `i_*(f^*𝒥 ⊗_O 𝓜) ⟶ I ⊗_O 𝓜`** for an arbitrary `O`-module `𝓜`, read on the
thickened topos: the chain of identifications out of which
`Deformation.ToposThickening.idealProductTensorIso` is built before its last factor — the
comparison `f^*𝒥 = i^*((f')^*𝒥)`, the projection formula `(f')^*𝒥 ⊗ i_*𝓜 ≅ i_*(i^*(f')^*𝒥 ⊗ 𝓜)`
of a closed immersion, the canonical map of ideals `(f')^*𝒥 ⟶ I` tensored with `i_*𝓜`, and the
reduction comparison `I ⊗_{O'} i_*𝓜 = I ⊗_O 𝓜`. -/
noncomputable def baseIdealTensorToIdealTensor
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    i.pushforwardModules.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
          (basePullbackIdeal t f ht)).obj M) ⟶
      (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj
            ((pushforwardModuleFunctor i.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M)).obj hi.I) :=
  haveI := Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isClosedImmersion i
    hi.isClosedImmersion ⟨hi.surjective.imageSieve_mem⟩
    ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I) M
  (i.pushforwardModulesIso.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
        (basePullbackIdeal t f ht)).obj M)).inv ≫
    (Stacks.Sheaves.RingedToposModules.pushforwardModules i.toRingedToposModulesHom).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map
        (basePullbackIdealIsoPullback i t f f' hi ht comm).hom).app M) ≫
    inv (Stacks.SheafOfModules.pushforwardTensorMap i.toRingedToposModulesHom
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I) M) ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I)).map
        (i.pushforwardModulesIso.app M).hom ≫
    idealTensorComparison i t f f' hi ht comm
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M) ≫
    reductionTensorMap i.fSharp hi.I
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
        ((pushforwardModuleFunctor i.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M))
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M)
      (𝟙 _)


omit [S.J.HasSheafCompose (forget AddCommGrpCat)] [HasWeakSheafify S.J AddCommGrpCat] in
  omit [S.J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify X.J AddCommGrpCat] in
  omit [HasSheafify X'.J AddCommGrpCat] in
  include hi in
  /-- The projection-formula comparison used in
  `Deformation.ToposThickening.baseIdealTensorToIdealTensor` is an isomorphism. -/
  private theorem isIso_pushforwardTensorMap_thickening
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsIso (Stacks.SheafOfModules.pushforwardTensorMap i.toRingedToposModulesHom
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I) M) :=
  Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isClosedImmersion i
    hi.isClosedImmersion ⟨hi.surjective.imageSieve_mem⟩ _ M

omit [HasSheafify X.J AddCommGrpCat] [HasSheafify X'.J AddCommGrpCat] in
include comm in
/-- `Deformation.ToposThickening.baseIdealTensorToIdealTensor` unfolded into the composite of
its factors. -/
theorem baseIdealTensorToIdealTensor_eq
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    haveI := Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isClosedImmersion i
      hi.isClosedImmersion ⟨hi.surjective.imageSieve_mem⟩
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I) M
    baseIdealTensorToIdealTensor i t f f' hi ht comm M =
    (i.pushforwardModulesIso.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
        (basePullbackIdeal t f ht)).obj M)).inv ≫
    (Stacks.Sheaves.RingedToposModules.pushforwardModules i.toRingedToposModulesHom).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map
        (basePullbackIdealIsoPullback i t f f' hi ht comm).hom).app M) ≫
    inv (Stacks.SheafOfModules.pushforwardTensorMap i.toRingedToposModulesHom
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I) M) ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I)).map
        (i.pushforwardModulesIso.app M).hom ≫
    idealTensorComparison i t f f' hi ht comm
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M) ≫
    reductionTensorMap i.fSharp hi.I
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
        ((pushforwardModuleFunctor i.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M))
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M)
      (𝟙 _) := rfl

omit [HasSheafify X.J AddCommGrpCat] [HasSheafify X'.J AddCommGrpCat] in
include comm in
/-- **The comparison of `Deformation.ToposThickening.baseIdealTensorToIdealTensor` is natural** in
the `O`-module. -/
theorem baseIdealTensorToIdealTensor_natural
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : M ⟶ N) :
    i.pushforwardModules.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
          (basePullbackIdeal t f ht)).map g) ≫
        baseIdealTensorToIdealTensor i t f f' hi ht comm N =
      baseIdealTensorToIdealTensor i t f f' hi ht comm M ≫
        (SheafOfModules.restrictScalars (ringMap i.fSharp)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).map
              ((pushforwardModuleFunctor i.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map g)) := by
  have hPM := isIso_pushforwardTensorMap_thickening i t f' hi ht M
  have hPN := isIso_pushforwardTensorMap_thickening i t f' hi ht N
  have h1 : i.pushforwardModules.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
            (basePullbackIdeal t f ht)).map g) ≫
        (i.pushforwardModulesIso.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
              (basePullbackIdeal t f ht)).obj N)).inv =
      (i.pushforwardModulesIso.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
              (basePullbackIdeal t f ht)).obj M)).inv ≫
        (Stacks.Sheaves.RingedToposModules.pushforwardModules i.toRingedToposModulesHom).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
            (basePullbackIdeal t f ht)).map g) :=
    (i.pushforwardModulesIso.inv.naturality _)
  have h2 : (Stacks.Sheaves.RingedToposModules.pushforwardModules i.toRingedToposModulesHom).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
      (basePullbackIdeal t f ht)).map g) ≫
        (Stacks.Sheaves.RingedToposModules.pushforwardModules i.toRingedToposModulesHom).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map
            (basePullbackIdealIsoPullback i t f f' hi ht comm).hom).app N) =
      (Stacks.Sheaves.RingedToposModules.pushforwardModules i.toRingedToposModulesHom).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map
          (basePullbackIdealIsoPullback i t f f' hi ht comm).hom).app M) ≫
        (Stacks.Sheaves.RingedToposModules.pushforwardModules i.toRingedToposModulesHom).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          ((pullbackModules i.toRingedToposModulesHom).obj
              ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))).map g) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
        (Stacks.Sheaves.RingedToposModules.pushforwardModules i.toRingedToposModulesHom).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
          (basePullbackIdealIsoPullback i t f f' hi ht comm).hom).naturality g)
  have h3 : (Stacks.Sheaves.RingedToposModules.pushforwardModules i.toRingedToposModulesHom).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          ((pullbackModules i.toRingedToposModulesHom).obj
              ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))).map g) ≫
        inv (Stacks.SheafOfModules.pushforwardTensorMap i.toRingedToposModulesHom
            ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I) N) =
      inv (Stacks.SheafOfModules.pushforwardTensorMap i.toRingedToposModulesHom
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I) M) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj
            ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I)).map
            ((Stacks.Sheaves.RingedToposModules.pushforwardModules
              i.toRingedToposModulesHom).map g) := by
    have h := Stacks.SheafOfModules.pushforwardTensorMap_natural i.toRingedToposModulesHom
      (𝟙 ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I)) g
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
      at h
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have h4 :
      ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I)).map
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules i.toRingedToposModulesHom).map g) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj
            ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I)).map
          (i.pushforwardModulesIso.app N).hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I)).map
          (i.pushforwardModulesIso.app M).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj
            ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I)).map
            (i.pushforwardModules.map g) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (i.pushforwardModulesIso.hom.naturality g)
  have h5 :
      ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I)).map
          (i.pushforwardModules.map g) ≫
        idealTensorComparison i t f f' hi ht comm
            ((pushforwardModuleFunctor i.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N) =
      idealTensorComparison i t f f' hi ht comm
          ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
          M) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj hi.idealOfThickening.I).map
          (i.pushforwardModules.map g) :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).map
      (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap).naturality
        (i.pushforwardModules.map g)
  have h6 : ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj hi.idealOfThickening.I).map
          (i.pushforwardModules.map g) ≫
        reductionTensorMap i.fSharp hi.I
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
              ((pushforwardModuleFunctor i.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N))
              ((pushforwardModuleFunctor i.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N) (𝟙 _) =
      reductionTensorMap i.fSharp hi.I
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
              ((pushforwardModuleFunctor i.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M))
              ((pushforwardModuleFunctor i.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M) (𝟙 _) ≫
        (SheafOfModules.restrictScalars (ringMap i.fSharp)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).map
                ((pushforwardModuleFunctor i.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map g)) :=
    Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_natural_right i.fSharp hi.I
      (𝟙 _) (𝟙 _)
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).map
          ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          g))
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map g)
          (by rw [Category.id_comp, Category.comp_id])
  have h56 :
      ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I)).map
          (i.pushforwardModules.map g) ≫
        (idealTensorComparison i t f f' hi ht comm
            ((pushforwardModuleFunctor i.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N) ≫
          reductionTensorMap i.fSharp hi.I
            ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
                ((pushforwardModuleFunctor i.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N))
                ((pushforwardModuleFunctor i.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N) (𝟙 _)) =
      (idealTensorComparison i t f f' hi ht comm
          ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
          M) ≫
        reductionTensorMap i.fSharp hi.I
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
              ((pushforwardModuleFunctor i.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M))
              ((pushforwardModuleFunctor i.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M) (𝟙 _)) ≫
        (SheafOfModules.restrictScalars (ringMap i.fSharp)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).map
                ((pushforwardModuleFunctor i.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map g)) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h5).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h6).trans (Category.assoc _ _ _).symm)))
  rw [baseIdealTensorToIdealTensor_eq, baseIdealTensorToIdealTensor_eq]
  exact ((CommSq.mk h1.symm).horiz_comp ((CommSq.mk h2.symm).horiz_comp
    ((CommSq.mk h3.symm).horiz_comp ((CommSq.mk h4.symm).horiz_comp (CommSq.mk h56.symm))))).w.symm

omit [HasSheafify X.J AddCommGrpCat] [HasSheafify X'.J AddCommGrpCat] in
include comm in
/-- **The comparison is surjective** for a strict square: its only factor that is not an
isomorphism is the canonical map of ideals `(f')^*𝒥 ⟶ I` tensored with `i_*𝓜`, which is surjective
because the square is strict (Definition 08M9) and tensoring is right exact. -/
theorem epi_baseIdealTensorToIdealTensor
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Epi (baseIdealTensorToIdealTensor i t f f' hi ht comm M) := by
  have := isIso_pushforwardTensorMap_thickening i t f' hi ht M
  have h6 := isIso_reductionTensorMapStructureRestrict i hi
    ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M)
  have hE : Epi (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap :=
    hstrict
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj X'.O
    ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M))
  have h5 : Epi (idealTensorComparison i t f f' hi ht comm
      ((pushforwardModuleFunctor i.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M)) :=
    @Functor.map_epi _ _ _ _ _ inferInstance _ _ _ hE
  rw [baseIdealTensorToIdealTensor_eq]
  exact epi_comp' inferInstance (epi_comp' inferInstance (epi_comp' inferInstance
    (epi_comp' inferInstance (epi_comp' h5 (@IsIso.epi_of_iso _ _ _ _ _ h6)))))

omit [HasSheafify X.J AddCommGrpCat] in
include comm in
/-- **The comparison is an isomorphism at `i^*ℱ'` for `ℱ'` flat over `O_{ℬ'}`**, the square being
strict: the canonical map of ideals tensored with `i_*i^*ℱ'` is then an isomorphism by the
"moreover" clause of Stacks 08MQ
(`Deformation.ToposThickening.isIso_idealTensorComparison_of_isFlat`). -/
theorem isIso_baseIdealTensorToIdealTensor
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F')) :
    IsIso (baseIdealTensorToIdealTensor i t f f' hi ht comm
      ((pullbackModules i.toRingedToposModulesHom).obj F')) := by
  have := isIso_pushforwardTensorMap_thickening i t f' hi ht
    ((pullbackModules i.toRingedToposModulesHom).obj F')
  have hM := isIso_reductionTensorMapStructureRestrict i hi (reducedPullbackModule i F')
  have hC := isIso_idealTensorComparison_of_isFlat i t f f' hi ht comm F' hstrict hflat
  rw [baseIdealTensorToIdealTensor_eq]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
      (IsIso.comp_isIso' hC hM))))

end CanonicalMap

variable (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
  (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
  (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
    ((SheafOfModules.restrictScalars
      ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        f'.fSharpInverseImage)).obj F'))

open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap multiplicationMap) in
/-- **The canonical map `ℱ ⊗ f^*𝒥 ⟶ I·ℱ'`** for `ℱ = i^*ℱ'`, read on the thickened topos: the
symmetry of the tensor product, the comparison
`Deformation.ToposThickening.baseIdealTensorToIdealTensor`, and the second factor
`I ⊗_O ℱ ⟶ I·ℱ'` of the canonical map of Stacks 08MQ. On a local section it is
`m̄ ⊗ j ↦ (f')^♯(j)·m`. -/
noncomputable def reductionKernelMap :
    i.pushforwardModules.obj
        ((baseIdealTensor t f ht).obj ((pullbackModules i.toRingedToposModulesHom).obj F')) ⟶
      (idealProductSubmodule hi F').toSheafOfModules :=
  i.pushforwardModules.map ((Stacks.SheafOfModules.FlatSquareZero.tensorLeftIsoTensorRight X.O
      (basePullbackIdeal t f ht)).app ((pullbackModules i.toRingedToposModulesHom).obj F')).inv ≫
    baseIdealTensorToIdealTensor i t f f' hi ht comm
      ((pullbackModules i.toRingedToposModulesHom).obj F') ≫
    canonicalSecondFactor i hi (reducedPullbackModule i F') F'
      (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')
      (idealProductSubmodule_unit_comp_zero hi F') (idealProductShortComplex_shortExact hi F')

open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap multiplicationMap) in
omit [HasSheafify X.J AddCommGrpCat] in
/-- The canonical map `ℱ ⊗ f^*𝒥 ⟶ I·ℱ'` followed by the inclusion of `I·ℱ'` is the composite of
the comparison with the action `I ⊗_{O'} ℱ' ⟶ ℱ'` of the ideal, read through the reduction
comparison `I ⊗_{O'} ℱ' = I ⊗_O ℱ`. -/
theorem reductionKernelMap_comp_ι :
    haveI := isIso_reductionTensorMap_thickening i hi (reducedPullbackModule i F') F'
      (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')
      (idealProductSubmodule_unit_comp_zero hi F') (idealProductShortComplex_shortExact hi F')
    reductionKernelMap i t f f' hi ht comm F' ≫ (idealProductSubmodule hi F').ι =
      i.pushforwardModules.map ((Stacks.SheafOfModules.FlatSquareZero.tensorLeftIsoTensorRight
          X.O (basePullbackIdeal t f ht)).app
            ((pullbackModules i.toRingedToposModulesHom).obj F')).inv ≫
        baseIdealTensorToIdealTensor i t f f' hi ht comm
          ((pullbackModules i.toRingedToposModulesHom).obj F') ≫
        inv (reductionTensorMap i.fSharp hi.I F' (reducedPullbackModule i F')
          (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')) ≫
        multiplicationMap i.fSharp hi.I F' hi.incl := by
  simp only [reductionKernelMap, canonicalSecondFactor, Category.assoc]
  exact _ ≫= _ ≫= _ ≫= multiplicationToIdealProduct_comp_ι i hi _ F' _ _ _

omit [HasSheafify X.J AddCommGrpCat] in
include hstrict hflat in
/-- **The canonical map `ℱ ⊗ f^*𝒥 ⟶ I·ℱ'` is an isomorphism** for `ℱ'` flat over `O_{ℬ'}` and a
strict square: both factors of the canonical map of Stacks 08MQ are then isomorphisms. -/
theorem isIso_reductionKernelMap : IsIso (reductionKernelMap i t f f' hi ht comm F') := by
  have hΨ := isIso_baseIdealTensorToIdealTensor i t f f' hi ht comm F' hstrict hflat
  have hB := (isIso_canonicalFactors_of_isFlat i t f f' hi ht comm F' hstrict hflat).2
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hΨ hB)

/-- **`ℱ ⊗ f^*𝒥 = I·ℱ'`** for `ℱ = i^*ℱ'` with `ℱ'` flat over `O_{ℬ'}` and a strict square, read
on the thickened topos: the canonical map `Deformation.ToposThickening.reductionKernelMap`, an
isomorphism by Stacks 08MQ. -/
noncomputable def reductionKernelIso :
    i.pushforwardModules.obj
        ((baseIdealTensor t f ht).obj ((pullbackModules i.toRingedToposModulesHom).obj F')) ≅
      (idealProductSubmodule hi F').toSheafOfModules :=
  @asIso _ _ _ _ (reductionKernelMap i t f f' hi ht comm F')
    (isIso_reductionKernelMap i t f f' hi ht comm F' hstrict hflat)

/-- **The sequence `0 ⟶ ℱ ⊗ f^*𝒥 ⟶ ℱ' ⟶ ℱ ⟶ 0` of Remark 0CZU**, of `O'`-modules: the first map
is the inclusion `i` of `ℱ ⊗ f^*𝒥 = I·ℱ'` and the second the reduction `π`. -/
noncomputable def reductionShortComplex :
    ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :=
  ShortComplex.mk
    ((reductionKernelIso i t f f' hi ht comm F' hstrict hflat).hom ≫
      (idealProductSubmodule hi F').ι)
    (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')
    (by rw [Category.assoc, idealProductSubmodule_unit_comp_zero hi F', comp_zero])

omit [HasSheafify X.J AddCommGrpCat] in
/-- **The sequence `0 ⟶ ℱ ⊗ f^*𝒥 ⟶ ℱ' ⟶ ℱ ⟶ 0` is short exact**, `ℱ'` being flat over
`O_{ℬ'}`: it is the sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i_*i^*ℱ' ⟶ 0` of Stacks 08MP with its first term
replaced through the isomorphism `ℱ ⊗ f^*𝒥 ≅ I·ℱ'` of Stacks 08MQ. -/
theorem reductionShortComplex_shortExact :
    (reductionShortComplex i t f f' hi ht comm F' hstrict hflat).ShortExact :=
  shortExact_isoComp_f (idealProductShortComplex_shortExact hi F')
    (reductionKernelIso i t f f' hi ht comm F' hstrict hflat)

variable (K : Subobject ((pullbackModules i.toRingedToposModulesHom).obj F'))

/-- The direct image `i_*𝒦 ⟶ i_*ℱ` of the inclusion of the kernel. -/
noncomputable abbrev kernelPushforwardι :
    i.pushforwardModules.obj (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ⟶ i.pushforwardModules.obj ((pullbackModules i.toRingedToposModulesHom).obj F') :=
  i.pushforwardModules.map K.arrow

/-- **The preimage `π⁻¹(𝒦) ⊂ ℱ'`** of the kernel `𝒦` of the quotient under the reduction
`π : ℱ' ⟶ i_*ℱ`, as the fibre product of `i_*𝒦 ⟶ i_*ℱ` and `π`. -/
noncomputable abbrev quotientLiftPreimage :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O) :=
  pullback (kernelPushforwardι i F' K) (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')

/-- The inclusion `π⁻¹(𝒦) ⟶ ℱ'`. -/
noncomputable abbrev quotientLiftPreimageι :
    quotientLiftPreimage i F' K ⟶ F' :=
  pullback.snd _ _

/-- The projection `π⁻¹(𝒦) ⟶ i_*𝒦`, the restriction of the reduction. -/
noncomputable abbrev quotientLiftPreimageπ :
    quotientLiftPreimage i F' K ⟶
      i.pushforwardModules.obj
        (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  pullback.fst _ _

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [HasWeakSheafify X'.J AddCommGrpCat]
    [X'.J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify X.J AddCommGrpCat]
    [HasSheafify X'.J AddCommGrpCat] in
include hi in
/-- The direct image `i_*𝒦 ⟶ i_*ℱ` of the inclusion of the kernel is a monomorphism: the direct
image along a first order thickening is exact (Stacks 08M3). -/
theorem mono_kernelPushforwardι : Mono (kernelPushforwardι i F' K) := by
  have := preservesFiniteLimits_pushforwardModules hi
  exact Functor.map_mono _ _

omit [HasWeakSheafify X'.J AddCommGrpCat] [X'.J.WEqualsLocallyBijective AddCommGrpCat]
    [HasSheafify X.J AddCommGrpCat] [HasSheafify X'.J AddCommGrpCat] in
include hi in
/-- The inclusion `π⁻¹(𝒦) ⟶ ℱ'` is a monomorphism. -/
theorem mono_quotientLiftPreimageι : Mono (quotientLiftPreimageι i F' K) := by
  have := mono_kernelPushforwardι i hi F' K
  exact pullback.snd_of_mono

/-- The inclusion `I·ℱ' ⟶ π⁻¹(𝒦)`: the ideal product is killed by the reduction. -/
noncomputable abbrev idealProductToQuotientLiftPreimage :
    (idealProductSubmodule hi F').toSheafOfModules ⟶ quotientLiftPreimage i F' K :=
  pullback.lift 0 (idealProductSubmodule hi F').ι
    (by rw [zero_comp, idealProductSubmodule_unit_comp_zero hi F'])

/-- **The sequence `0 ⟶ I·ℱ' ⟶ π⁻¹(𝒦) ⟶ i_*𝒦 ⟶ 0`**, the pullback of the sequence of
Stacks 08MP along `i_*𝒦 ⟶ i_*ℱ`. -/
noncomputable abbrev quotientLiftPreimageShortComplex :
    ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :=
  ShortComplex.mk (idealProductToQuotientLiftPreimage i hi F' K) (quotientLiftPreimageπ i F' K)
    (pullback.lift_fst _ _ _)

omit [HasSheafify X.J AddCommGrpCat] [HasSheafify X'.J AddCommGrpCat] in
/-- **The sequence `0 ⟶ I·ℱ' ⟶ π⁻¹(𝒦) ⟶ i_*𝒦 ⟶ 0` is short exact.** -/
theorem quotientLiftPreimageShortComplex_shortExact :
    (quotientLiftPreimageShortComplex i hi F' K).ShortExact :=
  let := hi.abelian
  pullback_shortExact (idealProductShortComplex_shortExact hi F') (kernelPushforwardι i F' K)

/-- **The canonical map `I·ℱ' = ℱ ⊗ f^*𝒥 ⟶ 𝒬 ⊗ f^*𝒥`** of the remark, where `𝒬 = ℱ/𝒦`: the
inverse of the identification `ℱ ⊗ f^*𝒥 ≅ I·ℱ'` followed by the direct image of the projection
`ℱ ⊗ f^*𝒥 ⟶ 𝒬 ⊗ f^*𝒥`. -/
noncomputable def quotientLiftCanonicalMap :
    (idealProductSubmodule hi F').toSheafOfModules ⟶
      i.pushforwardModules.obj ((baseIdealTensor t f ht).obj (cokernel K.arrow)) :=
  (reductionKernelIso i t f f' hi ht comm F' hstrict hflat).inv ≫
    i.pushforwardModules.map ((baseIdealTensor t f ht).map (cokernel.π K.arrow))


/-- **The action of `I` on `π⁻¹(𝒦)`, corestricted to `I·ℱ'`**: the action
`I ⊗_{O'} π⁻¹(𝒦) ⟶ π⁻¹(𝒦)` lands in `I·ℱ'`, the kernel of the reduction. -/
noncomputable def quotientLiftIdealAction :
    (idealTensorFunctor hi).obj (quotientLiftPreimage i F' K) ⟶
      (idealProductSubmodule hi F').toSheafOfModules :=
  (KernelFork.IsLimit.lift' (idealProductShortComplex_shortExact hi F').fIsKernel
    ((idealTensorFunctor hi).map (quotientLiftPreimageι i F' K) ≫ (idealAction hi).app F')
    ((Category.assoc _ _ _).trans (((idealTensorFunctor hi).map _ ≫=
      idealAction_comp_unit hi F').trans comp_zero))).1

omit [HasSheafify X.J AddCommGrpCat] in
/-- The defining property of `Deformation.ToposThickening.quotientLiftIdealAction`. -/
theorem quotientLiftIdealAction_comp_ι :
    quotientLiftIdealAction i hi F' K ≫ (idealProductSubmodule hi F').ι =
      (idealTensorFunctor hi).map (quotientLiftPreimageι i F' K) ≫ (idealAction hi).app F' :=
  (KernelFork.IsLimit.lift' _ _ _).2

omit [HasSheafify X.J AddCommGrpCat] in
/-- The action of `I` on `π⁻¹(𝒦)` is its corestriction followed by `I·ℱ' ⊂ π⁻¹(𝒦)`. -/
theorem quotientLiftIdealAction_comp_idealProductToQuotientLiftPreimage :
    quotientLiftIdealAction i hi F' K ≫ idealProductToQuotientLiftPreimage i hi F' K =
      (idealAction hi).app (quotientLiftPreimage i F' K) := by
  have := mono_quotientLiftPreimageι i hi F' K
  apply (cancel_mono (quotientLiftPreimageι i F' K)).1
  rw [Category.assoc, show idealProductToQuotientLiftPreimage i hi F' K ≫
      quotientLiftPreimageι i F' K = (idealProductSubmodule hi F').ι from pullback.lift_snd _ _ _,
    quotientLiftIdealAction_comp_ι]
  exact (idealAction hi).naturality (quotientLiftPreimageι i F' K)

open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap multiplicationMap) in
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor) in
omit [HasSheafify X.J AddCommGrpCat] in
/-- The second factor `I ⊗_O ℱ ⟶ I·ℱ'` of Stacks 08MQ followed by the inclusion of `I·ℱ'` is the
action of `I` on `ℱ'` read through the reduction comparison `I ⊗_{O'} ℱ' = I ⊗_O ℱ`. -/
theorem canonicalSecondFactor_unit_comp_ι :
    haveI := isIso_reductionTensorMap_thickening i hi (reducedPullbackModule i F') F'
      (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')
      (idealProductSubmodule_unit_comp_zero hi F') (idealProductShortComplex_shortExact hi F')
    canonicalSecondFactor i hi (reducedPullbackModule i F') F'
          (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')
          (idealProductSubmodule_unit_comp_zero hi F') (idealProductShortComplex_shortExact hi F') ≫
        (idealProductSubmodule hi F').ι =
      inv (reductionTensorMap i.fSharp hi.I F' (reducedPullbackModule i F')
          (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')) ≫
        (idealAction hi).app F' := by
  unfold canonicalSecondFactor
  rw [Category.assoc]
  exact _ ≫= multiplicationToIdealProduct_comp_ι i hi _ F' _ _ _

open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap multiplicationMap) in
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor) in
omit [HasSheafify X.J AddCommGrpCat] in
/-- **The action of `I` on `π⁻¹(𝒦)`, corestricted to `I·ℱ'`, factors through `I ⊗_O 𝒦`**: it is
the reduction comparison `I ⊗_{O'} π⁻¹(𝒦) ⟶ I ⊗_O 𝒦` (along `π⁻¹(𝒦) ⟶ i_*𝒦`), the inclusion
`I ⊗_O 𝒦 ⟶ I ⊗_O ℱ`, and the second factor `I ⊗_O ℱ ⟶ I·ℱ'` of Stacks 08MQ. -/
theorem quotientLiftIdealAction_eq :
    quotientLiftIdealAction i hi F' K =
      reductionTensorMap i.fSharp hi.I (quotientLiftPreimage i F' K)
          ((pushforwardModuleFunctor i.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
              (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (quotientLiftPreimageπ i F' K) ≫
        (SheafOfModules.restrictScalars (ringMap i.fSharp)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).map
              ((pushforwardModuleFunctor i.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map K.arrow)) ≫
        canonicalSecondFactor i hi (reducedPullbackModule i F') F'
          (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')
          (idealProductSubmodule_unit_comp_zero hi F')
          (idealProductShortComplex_shortExact hi F') := by
  have := isIso_reductionTensorMap_thickening i hi (reducedPullbackModule i F') F'
    (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')
    (idealProductSubmodule_unit_comp_zero hi F') (idealProductShortComplex_shortExact hi F')
  have hr : (idealTensorFunctor hi).map (quotientLiftPreimageι i F' K) ≫
        reductionTensorMap i.fSharp hi.I F' (reducedPullbackModule i F')
          (i.pullbackAdjPushforwardModulesViaComparison.unit.app F') =
      reductionTensorMap i.fSharp hi.I (quotientLiftPreimage i F' K)
          ((pushforwardModuleFunctor i.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
              (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (quotientLiftPreimageπ i F' K) ≫
        (SheafOfModules.restrictScalars (ringMap i.fSharp)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).map
              ((pushforwardModuleFunctor i.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map K.arrow)) :=
    Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_natural_right i.fSharp hi.I
      (quotientLiftPreimageπ i F' K) (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')
      (quotientLiftPreimageι i F' K)
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        K.arrow) pullback.condition
  apply (cancel_mono (idealProductSubmodule hi F').ι).1
  rw [quotientLiftIdealAction_comp_ι]
  exact (comp_comp_comp_eq_of_comm hr (canonicalSecondFactor_unit_comp_ι i hi F')).symm

open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap multiplicationMap) in
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor) in
omit [HasSheafify X.J AddCommGrpCat] [HasSheafify X'.J AddCommGrpCat] in
/-- The reduction comparison along `π⁻¹(𝒦) ⟶ i_*𝒦` is `I ⊗ (π⁻¹(𝒦) ⟶ i_*𝒦)` followed by the
reduction comparison of `i_*𝒦`. -/
theorem reductionTensorMap_quotientLiftPreimageπ :
    reductionTensorMap i.fSharp hi.I (quotientLiftPreimage i F' K)
          ((pushforwardModuleFunctor i.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
              (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (quotientLiftPreimageπ i F' K) =
      (idealTensorFunctor hi).map (quotientLiftPreimageπ i F' K) ≫
        reductionTensorMap i.fSharp hi.I
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
              ((pushforwardModuleFunctor i.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
              (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
          ((pushforwardModuleFunctor i.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
              (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (𝟙 _) := by
  have h := Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_natural_right i.fSharp hi.I
    (quotientLiftPreimageπ i F' K) (𝟙 _) (quotientLiftPreimageπ i F' K) (𝟙 _)
    (congrArg (quotientLiftPreimageπ i F' K ≫ ·)
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).map_id _))
  refine Eq.trans ?_ h.symm
  exact ((congrArg (_ ≫ (SheafOfModules.restrictScalars (ringMap i.fSharp)).map ·)
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I)).map_id _)).trans
    ((congrArg (_ ≫ ·) ((SheafOfModules.restrictScalars (ringMap i.fSharp)).map_id _)).trans
      (Category.comp_id _))).symm

open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap multiplicationMap) in
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor) in
omit [HasSheafify X.J AddCommGrpCat] [HasSheafify X'.J AddCommGrpCat] in
/-- **The comparison `i_*(f^*𝒥 ⊗ -) ⟶ I ⊗_O -` along `𝒦 ⟶ ℱ`**, preceded by the symmetry of the
tensor product. -/
theorem baseIdealTensorToIdealTensor_kernel :
    i.pushforwardModules.map ((Stacks.SheafOfModules.FlatSquareZero.tensorLeftIsoTensorRight
        X.O (basePullbackIdeal t f ht)).app
          (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inv ≫
        baseIdealTensorToIdealTensor i t f f' hi ht comm
          (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≫
        (SheafOfModules.restrictScalars (ringMap i.fSharp)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).map
              ((pushforwardModuleFunctor i.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map K.arrow)) =
      i.pushforwardModules.map ((baseIdealTensor t f ht).map K.arrow) ≫
        i.pushforwardModules.map ((Stacks.SheafOfModules.FlatSquareZero.tensorLeftIsoTensorRight
          X.O (basePullbackIdeal t f ht)).app
            ((pullbackModules i.toRingedToposModulesHom).obj F')).inv ≫
        baseIdealTensorToIdealTensor i t f f' hi ht comm
          ((pullbackModules i.toRingedToposModulesHom).obj F') := by
  rw [← baseIdealTensorToIdealTensor_natural, ← Category.assoc, ← Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, Iso.app_inv, Iso.app_inv]
  congr 2
  exact ((Stacks.SheafOfModules.FlatSquareZero.tensorLeftIsoTensorRight X.O
    (basePullbackIdeal t f ht)).inv.naturality K.arrow).symm

omit [HasWeakSheafify X'.J AddCommGrpCat] [X'.J.WEqualsLocallyBijective AddCommGrpCat] in
  omit [HasSheafify X'.J AddCommGrpCat] in
  include hi in
  /-- The direct image of `𝒦 ⊗ f^*𝒥 ⟶ ℱ ⊗ f^*𝒥` is killed by `ℱ ⊗ f^*𝒥 ⟶ 𝒬 ⊗ f^*𝒥`. -/
  private theorem map_baseIdealTensor_arrow_comp_map_cokernel_π :
    i.pushforwardModules.map ((baseIdealTensor t f ht).map K.arrow) ≫
      i.pushforwardModules.map ((baseIdealTensor t f ht).map (cokernel.π K.arrow)) = 0 := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj X.O
    (basePullbackIdeal t f ht)
  have := preservesFiniteColimits_pushforwardModules hi
  rw [← Functor.map_comp, ← Functor.map_comp, cokernel.condition, Functor.map_zero,
    Functor.map_zero]

open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap multiplicationMap) in
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor) in
/-- **The action of `I` on `π⁻¹(𝒦)` lands in the image of `𝒦 ⊗ f^*𝒥`**: its composite with the
canonical map `I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥` vanishes. On sections, `a·s` for `a` in `I` and `s` in `π⁻¹(𝒦)` is
the image of `π(s) ⊗ a`, and `π(s)` lies in `𝒦`. -/
theorem quotientLiftIdealAction_comp_canonicalMap :
    quotientLiftIdealAction i hi F' K ≫
        quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K = 0 := by
  have := isIso_reductionKernelMap i t f f' hi ht comm F' hstrict hflat
  have := epi_baseIdealTensorToIdealTensor i t f f' hi ht comm hstrict
    (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  have hW : (SheafOfModules.restrictScalars (ringMap i.fSharp)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).map
              ((pushforwardModuleFunctor i.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map K.arrow)) ≫
        canonicalSecondFactor i hi (reducedPullbackModule i F') F'
          (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')
          (idealProductSubmodule_unit_comp_zero hi F') (idealProductShortComplex_shortExact hi F') ≫
        quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K = 0 :=
    eq_zero_of_epi_comp_of_factor _ _ _ _ _ _ (reductionKernelMap i t f f' hi ht comm F') _
      (Category.assoc _ _ _)
      ((Category.assoc _ _ _).trans (baseIdealTensorToIdealTensor_kernel i t f f' hi ht comm F' K))
      rfl (map_baseIdealTensor_arrow_comp_map_cokernel_π i t f hi ht F' K)
  rw [quotientLiftIdealAction_eq]
  exact ((Category.assoc _ _ _).trans (_ ≫= hW)).trans comp_zero

open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap multiplicationMap) in
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor) in
/-- **Stacks 0CZU, the kernel of `I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥`**: the canonical map
`I·ℱ' = ℱ ⊗ f^*𝒥 ⟶ 𝒬 ⊗ f^*𝒥` is a cokernel of the action `I ⊗_{O'} π⁻¹(𝒦) ⟶ I·ℱ'` of the ideal on
`π⁻¹(𝒦)`. That is, `I·π⁻¹(𝒦) ⊂ I·ℱ'` is the kernel of `I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥`, which is the image of
`𝒦 ⊗ f^*𝒥` in `ℱ ⊗ f^*𝒥 = I·ℱ'`. -/
noncomputable def quotientLiftCanonicalMap_isColimit :
    IsColimit (CokernelCofork.ofπ (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)
      (quotientLiftIdealAction_comp_canonicalMap i t f f' hi ht comm F' hstrict hflat K)) := by
  haveI := isIso_reductionKernelMap i t f f' hi ht comm F' hstrict hflat
  haveI := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj X.O
    (basePullbackIdeal t f ht)
  haveI := preservesFiniteColimits_pushforwardModules hi
  haveI : Epi (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K) :=
    epi_comp' inferInstance (Functor.map_epi _ _)
  haveI := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj X'.O
    ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I)
  haveI : Epi (quotientLiftPreimageπ i F' K) :=
    (quotientLiftPreimageShortComplex_shortExact i hi F' K).epi_g
  haveI : Epi ((idealTensorFunctor hi).map (quotientLiftPreimageπ i F' K)) :=
    Functor.map_epi _ _
  have hc := CokernelCofork.mapIsColimit _ (cokernelIsCokernel K.arrow)
    (baseIdealTensor t f ht ⋙ i.pushforwardModules)
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun {Z} k hk => ?_)
  have hk' : quotientLiftIdealAction i hi F' K ≫ k = 0 := hk
  rw [quotientLiftIdealAction_eq, reductionTensorMap_quotientLiftPreimageπ] at hk'
  have h1 : reductionTensorMap i.fSharp hi.I
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
            ((pushforwardModuleFunctor i.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
                (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
          ((pushforwardModuleFunctor i.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
              (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (𝟙 _) ≫
        (SheafOfModules.restrictScalars (ringMap i.fSharp)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).map
              ((pushforwardModuleFunctor i.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map K.arrow)) ≫
        canonicalSecondFactor i hi (reducedPullbackModule i F') F'
          (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')
          (idealProductSubmodule_unit_comp_zero hi F') (idealProductShortComplex_shortExact hi F') ≫
        k = 0 :=
    (cancel_epi ((idealTensorFunctor hi).map (quotientLiftPreimageπ i F' K))).1
      ((comp_comp_comp_comp_assoc _ _ _ _ _).symm.trans (hk'.trans comp_zero.symm))
  have h2 : baseIdealTensorToIdealTensor i t f f' hi ht comm
          (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≫
        (SheafOfModules.restrictScalars (ringMap i.fSharp)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).map
              ((pushforwardModuleFunctor i.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map K.arrow)) ≫
        canonicalSecondFactor i hi (reducedPullbackModule i F') F'
          (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')
          (idealProductSubmodule_unit_comp_zero hi F') (idealProductShortComplex_shortExact hi F') ≫
        k = 0 := by
    rw [baseIdealTensorToIdealTensor_eq]
    exact comp_six_comp_eq_zero _ _ _ _ _ _ h1
  have h3 : i.pushforwardModules.map ((baseIdealTensor t f ht).map K.arrow) ≫
      reductionKernelMap i t f f' hi ht comm F' ≫ k = 0 :=
    comp_comp_eq_zero_of_comm
      (baseIdealTensorToIdealTensor_kernel i t f f' hi ht comm F' K) (Category.assoc _ _ _).symm h2
  refine ⟨(CokernelCofork.IsColimit.desc' hc (reductionKernelMap i t f f' hi ht comm F' ≫ k)
    h3).1, ?_⟩
  have hd := (CokernelCofork.IsColimit.desc' hc (reductionKernelMap i t f f' hi ht comm F' ≫ k)
    h3).2
  exact (Category.assoc _ _ _).trans ((inv (reductionKernelMap i t f f' hi ht comm F') ≫= hd).trans
    (IsIso.inv_hom_id_assoc _ _))


omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [X'.J.HasSheafCompose (forget AddCommGrpCat)] in
  omit [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
  omit [HasWeakSheafify X'.J AddCommGrpCat] [X'.J.WEqualsLocallyBijective AddCommGrpCat] in
  omit [HasSheafify X.J AddCommGrpCat] [HasSheafify X'.J AddCommGrpCat] in
  include hi in
  /-- The direct image along a first order thickening is faithful. -/
  private theorem faithful_pushforwardModules : i.pushforwardModules.Faithful :=
  (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some.faithful

/-- **A lift of the quotient `ℱ ⟶ ℱ/𝒦` to `ℱ'`** (Remark 0CZU): a subobject `𝒦' ⊂ ℱ'` whose
quotient `ℱ'/𝒦'` is flat over `O_{ℬ'}` and restricts to the given quotient, in the sense of the
functoriality of the functor of quotients: the kernel of `ℱ = i^*ℱ' ⟶ i^*(ℱ'/𝒦')` is `𝒦`. -/
def IsQuotientLift (K' : Subobject F') : Prop :=
  AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj (cokernel K'.arrow)) ∧
    Subobject.mk (kernel.ι ((pullbackModules i.toRingedToposModulesHom).map
      (cokernel.π K'.arrow))) = K

omit [S'.J.HasSheafCompose (forget AddCommGrpCat)] in
include hi in
/-- **A lift of the quotient, through the reduction**: `𝒦'` lifts `𝒦` exactly when `ℱ'/𝒦'` is
flat over `O_{ℬ'}`, `𝒦'` lies in `π⁻¹(𝒦)`, and `𝒦'` maps onto `𝒦` under the reduction. -/
theorem isQuotientLift_iff (K' : Subobject F') :
    IsQuotientLift i f' F' K K' ↔
      AlgebraicGeometry.SheafOfModules.IsFlat
          ((SheafOfModules.restrictScalars
            ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
              f'.fSharpInverseImage)).obj (cokernel K'.arrow)) ∧
        ∃ h : (K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ⟶
            quotientLiftPreimage i F' K,
          h ≫ quotientLiftPreimageι i F' K = K'.arrow ∧ Epi (h ≫ quotientLiftPreimageπ i F' K) := by
  have := faithful_pushforwardModules i hi
  have : (pullbackModules i.toRingedToposModulesHom).IsLeftAdjoint :=
    ⟨_, ⟨i.pullbackAdjPushforwardModulesViaComparison⟩⟩
  have := preservesFiniteColimits_pushforwardModules hi
  have w : (pullbackModules i.toRingedToposModulesHom).map K'.arrow ≫
      (pullbackModules i.toRingedToposModulesHom).map (cokernel.π K'.arrow) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have hφ : IsColimit (CokernelCofork.ofπ _ w) :=
    CokernelCofork.mapIsColimit _ (cokernelIsCokernel K'.arrow) _
  unfold IsQuotientLift
  refine and_congr_right fun _ => (mk_kernelι_eq_iff_exists_epi _ _ w hφ K).trans ?_
  constructor
  · rintro ⟨e, he, hu⟩
    have hg : i.pullbackAdjPushforwardModulesViaComparison.homEquiv _ _ e ≫
        kernelPushforwardι i F' K =
          K'.arrow ≫ i.pullbackAdjPushforwardModulesViaComparison.unit.app F' := by
      rw [kernelPushforwardι, ← Adjunction.homEquiv_naturality_right, hu,
        Adjunction.homEquiv_unit]
      exact (i.pullbackAdjPushforwardModulesViaComparison.unit.naturality K'.arrow).symm
    refine ⟨pullback.lift _ _ hg, pullback.lift_snd _ _ _, ?_⟩
    rw [pullback.lift_fst, Adjunction.homEquiv_unit]
    have := epi_pullbackAdjPushforward_unit_app hi (K' : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    have : Epi (i.pushforwardModules.map e) := Functor.map_epi _ _
    infer_instance
  · rintro ⟨h, hι, hπ⟩
    refine ⟨(i.pullbackAdjPushforwardModulesViaComparison.homEquiv _ _).symm
      (h ≫ quotientLiftPreimageπ i F' K), ?_, ?_⟩
    · rw [Adjunction.homEquiv_counit]
      have : Epi ((pullbackModules i.toRingedToposModulesHom).map
        (h ≫ quotientLiftPreimageπ i F' K)) := Functor.map_epi _ _
      infer_instance
    · apply (i.pullbackAdjPushforwardModulesViaComparison.homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc,
        show quotientLiftPreimageπ i F' K ≫ i.pushforwardModules.map K.arrow =
          quotientLiftPreimageι i F' K ≫ i.pullbackAdjPushforwardModulesViaComparison.unit.app F'
          from pullback.condition, ← Category.assoc, hι, Adjunction.homEquiv_unit]
      exact i.pullbackAdjPushforwardModulesViaComparison.unit.naturality K'.arrow

/-- **The image `i(𝒦 ⊗ f^*𝒥) ⊂ I·ℱ'`**: the inclusion `𝒦 ⊗ f^*𝒥 ⟶ ℱ ⊗ f^*𝒥` followed by the
identification `ℱ ⊗ f^*𝒥 ≅ I·ℱ'` of Stacks 08MQ. -/
noncomputable def quotientLiftKernelTensorMap :
    i.pushforwardModules.obj ((baseIdealTensor t f ht).obj
        (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
      (idealProductSubmodule hi F').toSheafOfModules :=
  i.pushforwardModules.map ((baseIdealTensor t f ht).map K.arrow) ≫
    (reductionKernelIso i t f f' hi ht comm F' hstrict hflat).hom

/-- The image `i(𝒦 ⊗ f^*𝒥)` is killed by the canonical map `I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥`. -/
theorem quotientLiftKernelTensorMap_comp_canonicalMap :
    quotientLiftKernelTensorMap i t f f' hi ht comm F' hstrict hflat K ≫
      quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K = 0 := by
  simp only [quotientLiftKernelTensorMap, quotientLiftCanonicalMap, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact map_baseIdealTensor_arrow_comp_map_cokernel_π i t f hi ht F' K

/-- The canonical map `I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥` is an epimorphism. -/
theorem epi_quotientLiftCanonicalMap :
    Epi (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K) := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj X.O
    (basePullbackIdeal t f ht)
  have := preservesFiniteColimits_pushforwardModules hi
  exact epi_comp' inferInstance (Functor.map_epi _ _)

/-- **`I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥` is a cokernel of `𝒦 ⊗ f^*𝒥 ⟶ I·ℱ'`**: tensoring with `f^*𝒥` and the
direct image are right exact. -/
noncomputable def quotientLiftCanonicalMap_isColimit_kernelTensor :
    IsColimit (CokernelCofork.ofπ (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)
      (quotientLiftKernelTensorMap_comp_canonicalMap i t f f' hi ht comm F' hstrict hflat K)) := by
  haveI := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj X.O
    (basePullbackIdeal t f ht)
  haveI := preservesFiniteColimits_pushforwardModules hi
  haveI : Epi (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K) :=
    epi_comp' inferInstance (Functor.map_epi _ _)
  have hc := CokernelCofork.mapIsColimit _ (cokernelIsCokernel K.arrow)
    (baseIdealTensor t f ht ⋙ i.pushforwardModules)
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun {Z} k hk => ?_)
  have hk' : i.pushforwardModules.map ((baseIdealTensor t f ht).map K.arrow) ≫
      (reductionKernelIso i t f f' hi ht comm F' hstrict hflat).hom ≫ k = 0 :=
    (Category.assoc _ _ _).symm.trans hk
  refine ⟨(CokernelCofork.IsColimit.desc' hc _ hk').1, ?_⟩
  have hd := (CokernelCofork.IsColimit.desc' hc _ hk').2
  exact (Category.assoc _ _ _).trans
    (((reductionKernelIso i t f f' hi ht comm F' hstrict hflat).inv ≫= hd).trans
      (Iso.inv_hom_id_assoc _ _))

/-- **The inclusion `i(𝒦 ⊗ f^*𝒥) ⟶ π⁻¹(𝒦)`.** -/
noncomputable abbrev quotientLiftKernelInclusion :
    i.pushforwardModules.obj ((baseIdealTensor t f ht).obj
        (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
      quotientLiftPreimage i F' K :=
  quotientLiftKernelTensorMap i t f f' hi ht comm F' hstrict hflat K ≫
    idealProductToQuotientLiftPreimage i hi F' K

/-- **The middle term `π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥)` of the extension of Remark 0CZU**, as an `O'`-module. -/
noncomputable abbrev quotientLiftExtensionModule :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O) :=
  cokernel (quotientLiftKernelInclusion i t f f' hi ht comm F' hstrict hflat K)

/-- The map `𝒬 ⊗ f^*𝒥 = I·ℱ'/i(𝒦 ⊗ f^*𝒥) ⟶ π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥)`. -/
noncomputable def quotientLiftExtensionι :
    i.pushforwardModules.obj ((baseIdealTensor t f ht).obj (cokernel K.arrow)) ⟶
      quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K :=
  (quotientLiftCanonicalMap_isColimit_kernelTensor i t f f' hi ht comm F' hstrict hflat K).desc
    (CokernelCofork.ofπ (idealProductToQuotientLiftPreimage i hi F' K ≫ cokernel.π _)
      (by rw [← Category.assoc]; exact cokernel.condition _))

/-- The canonical map `I·ℱ' ⟶ 𝒬 ⊗ f^*𝒥` followed by `𝒬 ⊗ f^*𝒥 ⟶ π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥)` is the
inclusion `I·ℱ' ⟶ π⁻¹(𝒦)` followed by the projection to the quotient. -/
theorem quotientLiftCanonicalMap_comp_extensionι :
    quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K ≫
        quotientLiftExtensionι i t f f' hi ht comm F' hstrict hflat K =
      idealProductToQuotientLiftPreimage i hi F' K ≫
        cokernel.π (quotientLiftKernelInclusion i t f f' hi ht comm F' hstrict hflat K) :=
  (quotientLiftCanonicalMap_isColimit_kernelTensor i t f f' hi ht comm F' hstrict hflat K).fac _
    WalkingParallelPair.one

/-- The map `π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥) ⟶ i_*𝒦` induced by the reduction. -/
noncomputable def quotientLiftExtensionπ :
    quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K ⟶
      i.pushforwardModules.obj
        (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  cokernel.desc _ (quotientLiftPreimageπ i F' K)
    ((Category.assoc _ _ _).trans ((quotientLiftKernelTensorMap i t f f' hi ht comm F' hstrict
      hflat K ≫= (quotientLiftPreimageShortComplex i hi F' K).zero).trans comp_zero))

/-- The two maps `𝒬 ⊗ f^*𝒥 ⟶ π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥) ⟶ i_*𝒦` compose to zero. -/
theorem quotientLiftExtensionι_comp_π :
    quotientLiftExtensionι i t f f' hi ht comm F' hstrict hflat K ≫
      quotientLiftExtensionπ i t f f' hi ht comm F' hstrict hflat K = 0 := by
  refine Cofork.IsColimit.hom_ext
    (quotientLiftCanonicalMap_isColimit_kernelTensor i t f f' hi ht comm F' hstrict hflat K) ?_
  change quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K ≫ _ =
    quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K ≫ 0
  rw [comp_zero, ← Category.assoc, quotientLiftCanonicalMap_comp_extensionι, Category.assoc,
    quotientLiftExtensionπ, cokernel.π_desc]
  exact (quotientLiftPreimageShortComplex i hi F' K).zero

/-- **The extension `0 ⟶ 𝒬 ⊗ f^*𝒥 ⟶ π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥) ⟶ 𝒦 ⟶ 0` of Remark 0CZU, read on the
thickened topos**, as a sequence of `O'`-modules. -/
noncomputable abbrev quotientLiftExtensionThickened :
    ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :=
  ShortComplex.mk (quotientLiftExtensionι i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftExtensionπ i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftExtensionι_comp_π i t f f' hi ht comm F' hstrict hflat K)

/-- **The sequence `0 ⟶ 𝒬 ⊗ f^*𝒥 ⟶ π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥) ⟶ 𝒦 ⟶ 0` is short exact.** It is the
sequence `0 ⟶ I·ℱ' ⟶ π⁻¹(𝒦) ⟶ i_*𝒦 ⟶ 0` divided by `i(𝒦 ⊗ f^*𝒥) ⊂ I·ℱ'`, whose cokernel in
`I·ℱ' = ℱ ⊗ f^*𝒥` is `𝒬 ⊗ f^*𝒥`. -/
theorem quotientLiftExtensionThickened_shortExact :
    (quotientLiftExtensionThickened i t f f' hi ht comm F' hstrict hflat K).ShortExact :=
  shortExact_cokernel_comp (quotientLiftPreimageShortComplex_shortExact i hi F' K)
    (quotientLiftKernelTensorMap i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftKernelTensorMap_comp_canonicalMap i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftCanonicalMap_isColimit_kernelTensor i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftExtensionι i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftCanonicalMap_comp_extensionι i t f f' hi ht comm F' hstrict hflat K)

/-- **`π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥)` is killed by `I`**: for `a` in `I` and `s` in `π⁻¹(𝒦)` the product `a·s`
lies in `i(𝒦 ⊗ f^*𝒥)` (`Deformation.ToposThickening.quotientLiftIdealAction_comp_canonicalMap`).
So the extension of Remark 0CZU is one of `O`-modules. -/
theorem idealAction_quotientLiftExtensionModule :
    (idealAction hi).app
      (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K) = 0 := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj X'.O
    ((SheafOfModules.restrictScalars (Stacks.SheafOfModules.FlatSquareZero.ringMap i.fSharp)).obj
        hi.I)
  have : Epi ((idealTensorFunctor hi).map (cokernel.π
      (quotientLiftKernelInclusion i t f f' hi ht comm F' hstrict hflat K))) := Functor.map_epi _ _
  apply (cancel_epi ((idealTensorFunctor hi).map (cokernel.π
      (quotientLiftKernelInclusion i t f f' hi ht comm F' hstrict hflat K)))).1
  rw [comp_zero, (idealAction hi).naturality, Functor.id_map,
    ← quotientLiftIdealAction_comp_idealProductToQuotientLiftPreimage, Category.assoc,
    ← quotientLiftCanonicalMap_comp_extensionι, ← Category.assoc,
    quotientLiftIdealAction_comp_canonicalMap, zero_comp]

/-- The unit `π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥) ⟶ i_*i^*(π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥))` is an isomorphism: the module is
killed by `I`. -/
theorem isIso_unit_quotientLiftExtensionModule :
    IsIso (i.pullbackAdjPushforwardModulesViaComparison.unit.app
      (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K)) :=
  CokernelCofork.IsColimit.isIso_π _ (unitIsCokernelIdealAction hi _)
    (idealAction_quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K)

/-- The first map `𝒬 ⊗ f^*𝒥 ⟶ i^*(π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥))` of the extension of Remark 0CZU, read on
`(Sh(C), O)` through the fully faithful direct image. -/
noncomputable def quotientLiftExtensionLeft :
    (baseIdealTensor t f ht).obj (cokernel K.arrow) ⟶
      (pullbackModules i.toRingedToposModulesHom).obj
        (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K) :=
  (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some.preimage
      (quotientLiftExtensionι i t f f' hi ht comm F' hstrict hflat K ≫
        i.pullbackAdjPushforwardModulesViaComparison.unit.app
          (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K))

/-- The second map `i^*(π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥)) ⟶ 𝒦` of the extension of Remark 0CZU. -/
noncomputable def quotientLiftExtensionRight :
    (pullbackModules i.toRingedToposModulesHom).obj
        (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K) ⟶
      (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some.preimage
      (@inv _ _ _ _ (i.pullbackAdjPushforwardModulesViaComparison.unit.app
          (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K))
        (isIso_unit_quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K) ≫
        quotientLiftExtensionπ i t f f' hi ht comm F' hstrict hflat K)

/-- The direct image of the first map of the extension is `quotientLiftExtensionι` followed by
the unit of `i^* ⊣ i_*`. -/
theorem pushforwardModules_map_quotientLiftExtensionLeft :
    i.pushforwardModules.map (quotientLiftExtensionLeft i t f f' hi ht comm F' hstrict hflat K) =
      quotientLiftExtensionι i t f f' hi ht comm F' hstrict hflat K ≫
        i.pullbackAdjPushforwardModulesViaComparison.unit.app
          (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K) :=
  (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some.map_preimage _

/-- The direct image of the second map of the extension is the inverse of the unit of
`i^* ⊣ i_*` followed by `quotientLiftExtensionπ`. -/
theorem pushforwardModules_map_quotientLiftExtensionRight :
    i.pushforwardModules.map (quotientLiftExtensionRight i t f f' hi ht comm F' hstrict hflat K) =
      @inv _ _ _ _ (i.pullbackAdjPushforwardModulesViaComparison.unit.app
          (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K))
        (isIso_unit_quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K) ≫
        quotientLiftExtensionπ i t f f' hi ht comm F' hstrict hflat K :=
  (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some.map_preimage _

/-- The two maps of the extension of Remark 0CZU compose to zero. -/
theorem quotientLiftExtensionLeft_comp_right :
    quotientLiftExtensionLeft i t f f' hi ht comm F' hstrict hflat K ≫
      quotientLiftExtensionRight i t f f' hi ht comm F' hstrict hflat K = 0 := by
  have := isIso_unit_quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K
  have := faithful_pushforwardModules i hi
  apply i.pushforwardModules.map_injective
  rw [Functor.map_comp, pushforwardModules_map_quotientLiftExtensionLeft,
    pushforwardModules_map_quotientLiftExtensionRight, Category.assoc, IsIso.hom_inv_id_assoc,
    quotientLiftExtensionι_comp_π, Functor.map_zero]

/-- **The canonical extension of Remark 0CZU**,
`0 ⟶ 𝒬 ⊗ f^*𝒥 ⟶ π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥) ⟶ 𝒦 ⟶ 0`, as a sequence of `O`-modules: the middle term is
`i^*` of the `O'`-module `π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥)`, which is killed by `I`, and the two maps are the
ones of `Deformation.ToposThickening.quotientLiftExtensionThickened`, read through the fully
faithful direct image `i_*` (Stacks 08M3). -/
noncomputable abbrev quotientLiftExtension :
    ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  ShortComplex.mk (quotientLiftExtensionLeft i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftExtensionRight i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftExtensionLeft_comp_right i t f f' hi ht comm F' hstrict hflat K)

/-- **The canonical extension of Remark 0CZU is short exact.** Its direct image along the
thickening is the short exact sequence
`Deformation.ToposThickening.quotientLiftExtensionThickened`, and the direct image is fully
faithful and exact (Stacks 08M3), so reflects short exactness. -/
theorem quotientLiftExtension_shortExact :
    (quotientLiftExtension i t f f' hi ht comm F' hstrict hflat K).ShortExact := by
  have := isIso_unit_quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K
  have := faithful_pushforwardModules i hi
  have := preservesFiniteColimits_pushforwardModules hi
  have := preservesFiniteLimits_pushforwardModules hi
  have h' : ((quotientLiftExtension i t f f' hi ht comm F' hstrict hflat K).map
      i.pushforwardModules).ShortExact :=
    ShortComplex.shortExact_of_iso
      (S₁ := quotientLiftExtensionThickened i t f f' hi ht comm F' hstrict hflat K)
      (ShortComplex.isoMk (Iso.refl _) (asIso (i.pullbackAdjPushforwardModulesViaComparison.unit.app
          (quotientLiftExtensionModule i t f f' hi ht comm F' hstrict hflat K))) (Iso.refl _)
        (by
          rw [Iso.refl_hom, Category.id_comp, asIso_hom]
          exact pushforwardModules_map_quotientLiftExtensionLeft i t f f' hi ht comm F' hstrict
            hflat K)
        (by
          rw [Iso.refl_hom, Category.comp_id, asIso_hom]
          change _ ≫ i.pushforwardModules.map
            (quotientLiftExtensionRight i t f f' hi ht comm F' hstrict hflat K) = _
          rw [pushforwardModules_map_quotientLiftExtensionRight, IsIso.hom_inv_id_assoc]))
      (quotientLiftExtensionThickened_shortExact i t f f' hi ht comm F' hstrict hflat K)
  refine ShortComplex.ShortExact.mk'
    ((ShortComplex.exact_map_iff_of_faithful _ i.pushforwardModules).1 h'.exact) ?_ ?_
  · have := h'.mono_f
    exact i.pushforwardModules.mono_of_mono_map this
  · have := h'.epi_g
    exact i.pushforwardModules.epi_of_epi_map this

variable [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **The obstruction class `o_x(T') ∈ Ext¹_O(𝒦, 𝒬 ⊗ f^*𝒥)` of Remark 0CZU**: the class of the
canonical extension `0 ⟶ 𝒬 ⊗ f^*𝒥 ⟶ π⁻¹(𝒦)/i(𝒦 ⊗ f^*𝒥) ⟶ 𝒦 ⟶ 0`
(`Deformation.ToposThickening.quotientLiftExtension`). -/
noncomputable def quotientLiftObstruction :
    Abelian.Ext.{e} (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((baseIdealTensor t f ht).obj (cokernel K.arrow)) 1 :=
  (quotientLiftExtension_shortExact i t f f' hi ht comm F' hstrict hflat K).extClass

end QuotientLift



end Deformation.ToposThickening

end
