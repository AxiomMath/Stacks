module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSquareZeroThickening

/-!
# The ideal part of a flat module over a square-zero thickening is the kernel of its reduction

Let `f : O' ⟶ O` be a locally surjective morphism of sheaves of commutative rings whose kernel
is identified with a square-zero ideal `I`, let `G` be an `O'`-module and let
`q : G ⟶ F|_{O'}` exhibit `F` as the extension of scalars `G ⊗_{O'} O`, in the sense of its
universal property. Then `q` is a cokernel of multiplication `I ⊗_{O'} G ⟶ G`, the comparison
`I ⊗_{O'} G ⟶ (I ⊗_O F)|_{O'}` is invertible, and so multiplication induces a map
`I ⊗_O F ⟶ G`, sending `a ⊗ x̄` to `a · x`. When `G` is flat this map is a kernel of `q`, by
**Stacks 08M4**
(`Stacks.SheafOfModules.FlatSquareZero.isFlat_iff_reduction_isFlat_and_multiplication_mono`).

## Main definitions

* `Stacks.SheafOfModules.FlatSquareZero.idealTensorKernelι`: the map `I ⊗_O F ⟶ G`.

## Main results

* `Stacks.SheafOfModules.FlatSquareZero.isColimit_of_isExtension`: a morphism with the universal
  property of extension of scalars is a cokernel of multiplication by the ideal.
* `Stacks.SheafOfModules.FlatSquareZero.idealTensorKernelIsLimit` and
  `Stacks.SheafOfModules.FlatSquareZero.exists_isKernel_idealTensor`: for flat `G` the map
  `I ⊗_O F ⟶ G` is a kernel of `q`.

## Implementation notes

The vanishing of `G ⟶ N|_{O'}` on multiplication by the ideal is stated here for any
multiplication map given by the pure-tensor formula
(`comp_restrictScalars_eq_zero_of_tmul`), and the descent of a morphism of restrictions of
scalars along the locally surjective `f` is Mathlib's
`PresheafOfModules.restrictHomEquivOfIsLocallySurjective`. The cokernel of multiplication is taken
from the public `Stacks.SheafOfModules.FlatSquareZero.exists_reduction_and_multiplicationMaps`
and compared with `q` through the two universal properties.

## References

* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TensorProduct

universe v u w

namespace Stacks.SheafOfModules.FlatSquareZero

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Every morphism from `G` into the restriction of scalars of an `O`-module kills any
multiplication map by the ideal**: the ideal acts on such a module through its reduction, which is
zero. Stated for any morphism `nu : I ⊗_{O'} G ⟶ G` given on local pure tensors by `a ⊗ x ↦ a · x`,
of which `Stacks.SheafOfModules.FlatSquareZero.multiplicationMap` is one
(`multiplicationMap_tmul`). -/
lemma comp_restrictScalars_eq_zero_of_tmul
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0)
    (nu : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).obj
        ((SheafOfModules.restrictScalars (ringMap f)).obj I) ⟶ G)
    (hnu : ∀ (U : Cᵒᵖ) (a : I.val.obj U) (x : G.val.obj U),
      nu.val.app U
          (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
              Stacks.SheafOfModules.Tensor.ringSheaf O')
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
          (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
            G.val)).app U (a ⊗ₜ[O'.obj.obj U] x)) =
        (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
          i.val.app U a) • x)
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (g : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj N) :
    nu ≫ g = 0 := by
  apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a x
  refine (congrArg (g.val.app U).hom (hnu U a x)).trans
    (((g.val.app U).hom.map_smul
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
        i.val.app U a) x).trans ?_)
  let : Module (O.obj.obj U) (N.val.obj U) := (N.val.obj U).isModule
  change @SMul.smul (O.obj.obj U) (N.val.obj U) inferInstance
    (f.hom.app U (show O'.obj.obj U from i.val.app U a)) (g.val.app U x) = 0
  exact (congrArg (fun scalar : O.obj.obj U =>
    scalar • (show N.val.obj U from g.val.app U x)) (hi_zero U a)).trans (zero_smul _ _)

section IdealTensorKernel

variable {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
  (hf : Presheaf.IsLocallySurjective J f.hom)
  (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
  (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
    f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0)
  (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
    ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x)
  (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F)
  (hq : ∀ N : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O),
    Function.Bijective (fun a : F ⟶ N ↦
      q ≫ (SheafOfModules.restrictScalars (ringMap f)).map a))

include hf hi_zero hi_univ hq

/-- **A morphism with the universal property of extension of scalars is a cokernel of
multiplication by the ideal.** The public
`Stacks.SheafOfModules.FlatSquareZero.exists_reduction_and_multiplicationMaps` provides a
cokernel `q₁ : G ⟶ F₁|_{O'}` of multiplication; every morphism into a restriction of scalars
kills multiplication and restriction of scalars is fully faithful, so `q₁` has the universal
property of extension of scalars too, and the two universal properties identify `F` with `F₁`
compatibly with `q` and `q₁`. -/
noncomputable def isColimit_of_isExtension :
    IsColimit (CokernelCofork.ofπ q
      (comp_restrictScalars_eq_zero_of_tmul f I G i hi_zero _ (multiplicationMap_tmul f I G i)
        F q)) := by
  let R := SheafOfModules.restrictScalars (ringMap f)
  letI : Presheaf.IsLocallySurjective J (ringMap f).hom := ⟨hf.imageSieve_mem⟩
  let h := exists_reduction_and_multiplicationMaps f hf I G i hi_zero hi_univ
  let F₁ := h.choose
  let nu := h.choose_spec.choose
  let q₁ := h.choose_spec.choose_spec.choose
  let hnuq₁ := h.choose_spec.choose_spec.choose_spec.choose
  let hq₁ : IsColimit (CokernelCofork.ofπ q₁ hnuq₁) :=
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hnu : nu = multiplicationMap f I G i :=
    multiplicationMap_unique f I G i nu _
      h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
      (multiplicationMap_tmul f I G i)
  have hz : multiplicationMap f I G i ≫ q = 0 :=
    comp_restrictScalars_eq_zero_of_tmul f I G i hi_zero _ (multiplicationMap_tmul f I G i) F q
  -- `a : F ⟶ F₁` from the universal property of `q`.
  let a : F ⟶ F₁ := ((hq F₁).surjective q₁).choose
  have ha : q ≫ R.map a = q₁ := ((hq F₁).surjective q₁).choose_spec
  -- `b : F₁ ⟶ F` from the cokernel property of `q₁` and fullness.
  have hz' : nu ≫ q = 0 := by rw [hnu]; exact hz
  let b' : R.obj F₁ ⟶ R.obj F := hq₁.desc (CokernelCofork.ofπ q hz')
  have hb' : q₁ ≫ b' = q := hq₁.fac (CokernelCofork.ofπ q hz') WalkingParallelPair.one
  let b : F₁ ⟶ F := ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    (ringMap f).hom F.isSheaf).symm b'.val⟩
  have hRb : R.map b = b' := SheafOfModules.hom_ext
    ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective (ringMap f).hom
      F.isSheaf).apply_symm_apply b'.val)
  have hb : q₁ ≫ R.map b = q := by rw [hRb]; exact hb'
  have hab : a ≫ b = 𝟙 F := by
    apply (hq F).injective
    change q ≫ R.map (a ≫ b) = q ≫ R.map (𝟙 F)
    rw [R.map_comp, ← Category.assoc, ha, hb, R.map_id, Category.comp_id]
  have : Epi q₁ := Cofork.IsColimit.epi hq₁
  have hba : b ≫ a = 𝟙 F₁ := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun m => ?_))
    have hR : R.map (b ≫ a) = R.map (𝟙 F₁) := by
      apply (cancel_epi q₁).mp
      rw [R.map_comp, ← Category.assoc, hb, ha, R.map_id, Category.comp_id]
    exact congrArg (fun k => k.val.app U m) hR
  haveI : IsIso (R.map b) := ⟨R.map a, by rw [← R.map_comp, hba, R.map_id],
    by rw [← R.map_comp, hab, R.map_id]⟩
  haveI : Epi q := by rw [← hb]; exact epi_comp _ _
  refine CokernelCofork.IsColimit.ofπ' q hz fun {Y} k hk => ?_
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hq₁ k (show nu ≫ k = 0 by rw [hnu]; exact hk)
  refine ⟨R.map a ≫ l, ?_⟩
  rw [← Category.assoc, ha]
  exact hl

/-- The comparison `I ⊗_{O'} G ⟶ (I ⊗_O F)|_{O'}` is invertible when `q : G ⟶ F|_{O'}` presents
`F` as the extension of scalars of `G`: that presentation is a cokernel of multiplication by
the ideal, which is what `reductionTensorMap_isIso` asks for. -/
lemma isIso_reductionTensorMap_of_isExtension : IsIso (reductionTensorMap f I G F q) :=
  reductionTensorMap_isIso f hf I I G F i hi_zero q
    (comp_restrictScalars_eq_zero_of_tmul f I G i hi_zero _ (multiplicationMap_tmul f I G i) F q)
    (isColimit_of_isExtension f hf I G F i hi_zero hi_univ q hq)

/-- **The ideal part of a module over a square-zero thickening**, as a map into it: the
multiplication map `I ⊗_O F ⟶ G`. It is multiplication `I ⊗_{O'} G ⟶ G` read through the
inverse of the comparison `reductionTensorMap f I G F q`, which is invertible by
`isIso_reductionTensorMap_of_isExtension`. On local pure tensors it sends `a ⊗ x̄` to `a · x`
(`idealTensorKernelι_tmul`). -/
noncomputable def idealTensorKernelι :
    (SheafOfModules.restrictScalars (ringMap f)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).obj I) ⟶
      G :=
  @CategoryTheory.inv _ _ _ _ (reductionTensorMap f I G F q)
      (isIso_reductionTensorMap_of_isExtension f hf I G F i hi_zero hi_univ q hq) ≫
    multiplicationMap f I G i

/-- The comparison composed with `idealTensorKernelι` is multiplication by the ideal. -/
lemma reductionTensorMap_comp_idealTensorKernelι :
    reductionTensorMap f I G F q ≫ idealTensorKernelι f hf I G F i hi_zero hi_univ q hq =
      multiplicationMap f I G i := by
  have := isIso_reductionTensorMap_of_isExtension f hf I G F i hi_zero hi_univ q hq
  rw [idealTensorKernelι, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- `idealTensorKernelι` sends a local pure tensor `a ⊗ x̄` to `a · x`. -/
lemma idealTensorKernelι_tmul (U : Cᵒᵖ) (a : I.val.obj U) (x : G.val.obj U) :
    (idealTensorKernelι f hf I G F i hi_zero hi_univ q hq).val.app U
        (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
            Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj I.val F.val)).app U
          (a ⊗ₜ[O.obj.obj U] q.val.app U x)) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
        i.val.app U a) • x := by
  rw [← reductionTensorMap_tmul f I G F q U a x]
  change (reductionTensorMap f I G F q ≫
    idealTensorKernelι f hf I G F i hi_zero hi_univ q hq).val.app U _ = _
  rw [reductionTensorMap_comp_idealTensorKernelι]
  exact multiplicationMap_tmul f I G i U a x

/-- The ideal part is killed by the reduction. -/
lemma idealTensorKernelι_comp_reduction :
    idealTensorKernelι f hf I G F i hi_zero hi_univ q hq ≫ q = 0 := by
  rw [idealTensorKernelι, Category.assoc,
    comp_restrictScalars_eq_zero_of_tmul f I G i hi_zero _ (multiplicationMap_tmul f I G i) F q,
    comp_zero]

/-- **The ideal part of a flat module over a square-zero thickening is the kernel of its
reduction**, as the limit datum itself: `idealTensorKernelι` is a kernel of `q`.

Both halves use the flatness of `G`: the map is a monomorphism by **Stacks 08M4**, and `q` is a
cokernel of multiplication by `I` on `G`, hence of `idealTensorKernelι`, so the mono is the
kernel of its own cokernel. -/
noncomputable def idealTensorKernelIsLimit
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0)
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat G) :
    IsLimit (KernelFork.ofι (idealTensorKernelι f hf I G F i hi_zero hi_univ q hq)
      (idealTensorKernelι_comp_reduction f hf I G F i hi_zero hi_univ q hq)) := by
  have hnuq : multiplicationMap f I G i ≫ q = 0 :=
    comp_restrictScalars_eq_zero_of_tmul f I G i hi_zero _ (multiplicationMap_tmul f I G i) F q
  let hcoker : IsColimit (CokernelCofork.ofπ q hnuq) :=
    isColimit_of_isExtension f hf I G F i hi_zero hi_univ q hq
  have hfac := reductionTensorMap_comp_idealTensorKernelι f hf I G F i hi_zero hi_univ q hq
  have hz : idealTensorKernelι f hf I G F i hi_zero hi_univ q hq ≫ q = 0 :=
    idealTensorKernelι_comp_reduction f hf I G F i hi_zero hi_univ q hq
  haveI : Mono (idealTensorKernelι f hf I G F i hi_zero hi_univ q hq) :=
    ((isFlat_iff_reduction_isFlat_and_multiplication_mono f hf I G F i hi_zero hi_univ hsq
      (multiplicationMap f I G i) (multiplicationMap_tmul f I G i) q hnuq hcoker _
      (idealTensorKernelι_tmul f hf I G F i hi_zero hi_univ q hq)).1 hG).2
  haveI : Epi q := Cofork.IsColimit.epi hcoker
  have hcokermu : IsColimit (CokernelCofork.ofπ
      (f := idealTensorKernelι f hf I G F i hi_zero hi_univ q hq) q hz) :=
    CokernelCofork.IsColimit.ofπ' q hz fun {N} k hk =>
      CokernelCofork.IsColimit.desc' hcoker k
        (by rw [← hfac, Category.assoc, hk, comp_zero])
  exact CategoryTheory.Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ q hz) hcokermu

end IdealTensorKernel

/-- **The ideal part of a flat module over a square-zero thickening is the kernel of its
reduction.**

Let `f : O' ⟶ O` be a locally surjective morphism of sheaves of commutative rings whose kernel
is the square-zero ideal `I`, let `G` be a **flat** `O'`-module, and let `q : G ⟶ F|_{O'}`
exhibit `F` as the extension of scalars `G ⊗_{O'} O`, the universal property being the
hypothesis `hq`. Then the multiplication map `I ⊗_O F ⟶ G`, which on local pure tensors sends
`a ⊗ x̄` to `a · x`, is a kernel of `q`. -/
theorem exists_isKernel_idealTensor
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0)
    (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
      ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x)
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0)
    (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F)
    (hq : ∀ N : SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O),
      Function.Bijective (fun a : F ⟶ N ↦
        q ≫ (SheafOfModules.restrictScalars (ringMap f)).map a))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat G) :
    ∃ mu : (SheafOfModules.restrictScalars (ringMap f)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).obj I) ⟶ G,
      (∀ (U : Cᵒᵖ) (a : I.val.obj U) (x : G.val.obj U),
        mu.val.app U
            (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
                Stacks.SheafOfModules.Tensor.ringSheaf O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
              (PresheafOfModules.tensorObj I.val F.val)).app U
              (a ⊗ₜ[O.obj.obj U] q.val.app U x)) =
          (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
            i.val.app U a) • x) ∧
      ∃ hz : mu ≫ q = 0, Nonempty (IsLimit (KernelFork.ofι mu hz)) :=
  ⟨idealTensorKernelι f hf I G F i hi_zero hi_univ q hq,
    idealTensorKernelι_tmul f hf I G F i hi_zero hi_univ q hq,
    idealTensorKernelι_comp_reduction f hf I G F i hi_zero hi_univ q hq,
    ⟨idealTensorKernelIsLimit f hf I G F i hi_zero hi_univ q hq hsq hG⟩⟩

end Stacks.SheafOfModules.FlatSquareZero

end
