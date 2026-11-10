module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ToposThickening.TwoExtensions

/-!
# The difference construction for extensions over a first order thickening

Let `D` be two extensions of modules over a first order thickening of ringed topoi, together
with maps on their quotient and kernel modules. The lifts of those maps to the middle terms are
the splittings of a single extension, built as follows: the pullback of the second extension
along the first quotient map, twisted by the given map of quotients, receives the kernel of the
first extension, and the cokernel of that map is an extension of the first quotient by the
second kernel whose retractions are exactly the lifts.

This file assembles the ingredients. The difference construction and its retraction criterion
are stated for an arbitrary abelian category; the descent ingredients concern a sheaf of modules
annihilated by the kernel of a locally surjective map of sheaves of rings, which is the
situation of a square-zero ideal; and the last section specialises to a first order thickening
of ringed topoi, where it records the compatibility condition on the two ideal actions, the
notion of a lift, and the map whose cokernel is the difference extension.

## Main definitions

* `Deformation.ToposThickening.quotientKerPresheaf` and `.quotientKerInclusion`: the sectionwise
  quotient of a sheaf of rings by the kernel of a map of sheaves of rings, and its injection
  into the target.
* `Deformation.ToposThickening.descendModule`: a sheaf of modules annihilated by the kernel of a
  locally surjective map of sheaves of rings descends along that map.
* `Deformation.ToposThickening.moduleHomEquivOfLocallySurjective`: restriction of scalars along
  a locally surjective map of sheaves of rings is bijective on morphisms.
* `Deformation.ToposThickening.CompatibleActions`: the maps on the end terms commute with the
  actions of the square-zero ideal.
* `Deformation.ToposThickening.IsExtensionLift`: a middle-term map inducing the prescribed maps
  on the two end terms.
* `Deformation.ToposThickening.differenceCospanFst` and
  `Deformation.ToposThickening.differenceRelation`: the twisted quotient map of the first
  extension, and the map from the kernel of the first extension into the pullback along it,
  whose cokernel is the difference extension.

## Main results

* `Deformation.ToposThickening.quotient_shortExact`: dividing out a subobject of the kernel term
  leaves a short exact sequence.
* `Deformation.ToposThickening.differencePullback_shortExact`: the twisted pullback of the second
  extension is a short exact sequence over the first middle term.
* `Deformation.ToposThickening.difference_retraction_iff`: the difference extension splits
  exactly when the prescribed end maps extend to a map of the two sequences.
* `Deformation.ToposThickening.shortExact_of_fullyFaithful_map` and
  `Deformation.ToposThickening.descend_shortExact`: short exactness is reflected by a fully
  faithful additive functor, and such a sequence descends along it with the same splittings.
* `Deformation.ToposThickening.extClass_comp_mk₀_eq_zero_iff`: the Ext class of a short exact
  sequence kills a map out of its kernel term exactly when that map extends to the middle term.

## Implementation notes

Modules over the source structure sheaf are represented on the target topos by modules over its
direct image. The compatibility of the two ideal-action maps is expressed on pure tensors of
local sections; that is the displayed commutative square of the source.

## References

* [Stacks Project, Tag 08MD](https://stacks.math.columbia.edu/tag/08MD)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w' e

namespace Deformation.ToposThickening

section ModuleDescent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{w}} (α : R ⟶ S)

/-- The presheaf of rings obtained by dividing a sheaf of rings, section by section, by the
kernel of a map of sheaves of rings. -/
def quotientKerPresheaf : Cᵒᵖ ⥤ RingCat.{w} where
  obj U := RingCat.of (R.obj.obj U ⧸ RingHom.ker (α.hom.app U).hom)
  map {U V} f := RingCat.ofHom (Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (R.obj.map f).hom) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (α.hom.app V) (R.obj.map f a) = 0
      have h := ConcreteCategory.congr_hom (α.hom.naturality f) a
      dsimp at h
      rw [h, show α.hom.app U a = 0 from ha, map_zero]))
  map_id U := by
    ext a
    change Ideal.Quotient.mk _ (R.obj.map (𝟙 U) a) = _
    simp
  map_comp f g := by
    ext a
    change Ideal.Quotient.mk _ (R.obj.map (f ≫ g) a) = _
    simp [Functor.map_comp]

/-- The injection of that sectionwise quotient into the target sheaf of rings. -/
def quotientKerInclusion : quotientKerPresheaf α ⟶ S.obj where
  app U := RingCat.ofHom (α.hom.app U).hom.kerLift
  naturality {U V} f := by
    ext a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ConcreteCategory.congr_hom (α.hom.naturality f) a

/-- The sectionwise quotient injects into the target sheaf of rings. -/
lemma quotientKerInclusion_injective (U : Cᵒᵖ) :
    Function.Injective ((quotientKerInclusion α).app U) :=
  (α.hom.app U).hom.kerLift_injective

/-- If the map of sheaves of rings is locally surjective, so is the injection of the
sectionwise quotient. -/
lemma quotientKerInclusion_locallySurjective
    [Presheaf.IsLocallySurjective J α.hom] :
    Presheaf.IsLocallySurjective J (quotientKerInclusion α) :=
  ⟨fun x => J.superset_covering (by rintro V f ⟨a, ha⟩; exact ⟨Ideal.Quotient.mk _ a, ha⟩)
    (Presheaf.imageSieve_mem J α.hom x)⟩

/-- A sheaf of modules annihilated, section by section, by the kernel of a locally surjective
map of sheaves of rings descends along that map, together with the identification of its
restriction of scalars with the original module. -/
noncomputable def descendModule
    [Presheaf.IsLocallySurjective J α.hom]
    (M : SheafOfModules.{w} R)
    (hM : ∀ (U : Cᵒᵖ) (a : R.obj.obj U), α.hom.app U a = 0 →
      ∀ m : M.val.obj U, a • m = 0) :
    Σ N : SheafOfModules.{w} S, (SheafOfModules.restrictScalars α).obj N ≅ M := by
  let hT (U : Cᵒᵖ) : Module.IsTorsionBySet (R.obj.obj U) (M.val.obj U)
      (RingHom.ker (α.hom.app U).hom) := fun m a => hM U a a.property m
  letI (U : Cᵒᵖ) : Module ((quotientKerPresheaf α).obj U) (M.val.presheaf.obj U) :=
    (hT U).module
  let M₀ : PresheafOfModules.{w} (quotientKerPresheaf α) :=
    PresheafOfModules.ofPresheaf M.val.presheaf (by
      intro U V f a m
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact M.val.map_smul f a m)
  letI : Presheaf.IsLocallyInjective J (quotientKerInclusion α) :=
    Presheaf.isLocallyInjective_of_injective J _ (quotientKerInclusion_injective α)
  letI : Presheaf.IsLocallySurjective J (quotientKerInclusion α) :=
    quotientKerInclusion_locallySurjective α
  let N := PresheafOfModules.sheafify (quotientKerInclusion α)
    (M₀ := M₀) (A := (⟨M₀.presheaf, M.isSheaf⟩ : Sheaf J AddCommGrpCat.{w}))
    (𝟙 M₀.presheaf)
  have hm (U : Cᵒᵖ) (r : R.obj.obj U) (m : M.val.obj U) :
      (α.hom.app U r) • (show N.val.obj U from m) = r • m :=
    (((PresheafOfModules.toSheafify (quotientKerInclusion α)
      (M₀ := M₀) (A := (⟨M₀.presheaf, M.isSheaf⟩ : Sheaf J AddCommGrpCat.{w}))
      (𝟙 M₀.presheaf)).app U).hom.map_smul
      (Ideal.Quotient.mk _ r) m).symm
  let e : (SheafOfModules.restrictScalars α).obj N ⟶ M :=
    ⟨PresheafOfModules.homMk (𝟙 M.val.presheaf) (fun U r m => hm U r m)⟩
  let e' : M ⟶ (SheafOfModules.restrictScalars α).obj N :=
    ⟨PresheafOfModules.homMk (𝟙 M.val.presheaf) (fun U r m => (hm U r m).symm)⟩
  exact ⟨N, {
    hom := e
    inv := e'
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl }⟩

end ModuleDescent

section ModuleSections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A scalar that kills every local section coming from a locally surjective map of sheaves of
modules kills every section of the target. -/
lemma smul_eq_zero_of_locallySurjective {R : Sheaf J RingCat.{w}}
    {M N : SheafOfModules.{w} R} (q : M ⟶ N)
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map q.val)]
    (U : Cᵒᵖ) (r : R.obj.obj U) (z : N.val.obj U)
    (h : ∀ (V : C) (t : V ⟶ U.unop) (x : M.val.obj (Opposite.op V)),
      R.obj.map t.op r • q.val.app (Opposite.op V) x = 0) : r • z = 0 := by
  apply N.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf R.obj).map q.val) z)
  rintro V t ⟨x, hx⟩
  change q.val.app (Opposite.op V) x = N.val.map t.op z at hx
  change N.val.map t.op (r • z) = N.val.map t.op 0
  rw [N.val.map_smul, map_zero, ← hx]
  exact h V t x

/-- Two sections of a pullback of sheaves of modules agreeing under both projections are
equal. -/
lemma pullback_sections_ext {R : Sheaf J RingCat.{w}}
    {M N T : SheafOfModules.{w} R} (f : M ⟶ T) (g : N ⟶ T)
    (U : Cᵒᵖ) (x y : (pullback f g).val.obj U)
    (h₁ : (pullback.fst f g).val.app U x = (pullback.fst f g).val.app U y)
    (h₂ : (pullback.snd f g).val.app U x = (pullback.snd f g).val.app U y) : x = y := by
  let F := (SheafOfModules.toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat) ⋙
    (evaluation Cᵒᵖ AddCommGrpCat).obj U
  apply Concrete.isLimit_ext _ (isLimitOfPreserves F (limit.isLimit (cospan f g))) x y
  intro j
  rcases j with (_ | (_ | _))
  · change (F.map (limit.π (cospan f g) WalkingCospan.one)) x =
      (F.map (limit.π (cospan f g) WalkingCospan.one)) y
    rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, F.map_comp]
    exact congrArg (f.val.app U) h₁
  · exact h₁
  · exact h₂

/-- Restriction of scalars along a locally surjective map of sheaves of rings is bijective on
morphisms between sheaves of modules over the target. -/
noncomputable def moduleHomEquivOfLocallySurjective
    {R S : Sheaf J RingCat.{w}} (α : R ⟶ S)
    (hα : Presheaf.IsLocallySurjective J α.hom)
    {M N : SheafOfModules.{w} S} :
    ((SheafOfModules.restrictScalars α).obj M ⟶
      (SheafOfModules.restrictScalars α).obj N) ≃ (M ⟶ N) where
  toFun f := by
    letI := hα
    exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (α := α.hom) N.isSheaf).symm f.val⟩
  invFun f := (SheafOfModules.restrictScalars α).map f
  left_inv f := by
    have := hα
    exact SheafOfModules.hom_ext ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (α := α.hom) N.isSheaf).apply_symm_apply f.val)
  right_inv f := by
    have := hα
    exact SheafOfModules.hom_ext ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (α := α.hom) N.isSheaf).symm_apply_apply f.val)

end ModuleSections

section ExtensionDifference

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Dividing the middle term of a short exact sequence by a subobject of its kernel term that
is itself the kernel term of a second short exact sequence leaves a short exact sequence. -/
lemma quotient_shortExact
    {K E F L P : C} {f : K ⟶ E} {g : E ⟶ F} {hfg : f ≫ g = 0}
    {l : L ⟶ P} {p : P ⟶ E} {hlp : l ≫ p = 0}
    (hE : (ShortComplex.mk f g hfg).ShortExact)
    (hP : (ShortComplex.mk l p hlp).ShortExact)
    (j : K ⟶ P) (hjp : j ≫ p = f) :
    (ShortComplex.mk (l ≫ cokernel.π j)
      (cokernel.desc j (p ≫ g) (by rw [← Category.assoc, hjp, hfg]))
      (by rw [Category.assoc, cokernel.π_desc, ← Category.assoc, hlp,
        zero_comp])).ShortExact := by
  have := hE.mono_f
  have := hE.epi_g
  have := hP.mono_f
  have := hP.epi_g
  have : Mono j := mono_of_mono_fac hjp
  let q := cokernel.π j
  let t := cokernel.desc j (p ≫ g) (by rw [← Category.assoc, hjp, hfg])
  have hqt : q ≫ t = p ≫ g := cokernel.π_desc _ _ _
  have hjq : j ≫ q = 0 := cokernel.condition j
  have hJ : (ShortComplex.mk j q hjq).Exact := ShortComplex.cokernelSequence_exact j
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.exact_iff_exact_up_to_refinements _).2
    intro A z hz
    dsimp only at z hz
    obtain ⟨A', π, hπ, x, hx⟩ := surjective_up_to_refinements_of_epi q z
    have hxg : (x ≫ p) ≫ g = 0 := by
      rw [Category.assoc, ← hqt, ← Category.assoc, ← hx, Category.assoc]
      exact congrArg (π ≫ ·) hz |>.trans (comp_zero)
    obtain ⟨k, hk⟩ := hE.exact.lift' (x ≫ p) hxg
    have hxkp : (x - k ≫ j) ≫ p = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, hjp, hk, sub_self]
    obtain ⟨y, hy⟩ := hP.exact.lift' (x - k ≫ j) hxkp
    dsimp only at k hk y hy
    refine ⟨A', π, hπ, y, ?_⟩
    change π ≫ z = y ≫ (l ≫ q)
    rw [← Category.assoc, hy, Preadditive.sub_comp, Category.assoc, hjq,
      comp_zero, sub_zero, hx]
  · apply (Preadditive.mono_iff_cancel_zero _).2
    intro A z hz
    dsimp only at z hz
    obtain ⟨k, hk⟩ := hJ.lift' (z ≫ l) (by simpa [Category.assoc] using hz)
    dsimp only at k hk
    have hkzero : k = 0 := by
      apply (cancel_mono f).1
      rw [zero_comp, ← hjp, ← Category.assoc, hk, Category.assoc, hlp, comp_zero]
    apply (cancel_mono l).1
    rw [zero_comp, ← hk, hkzero, zero_comp]
  · exact epi_of_epi_fac hqt

/-- The pullback of the second short exact sequence along the first quotient map, twisted by a
map of quotients, is itself a short exact sequence over the first middle term. -/
lemma differencePullback_shortExact
    {S₁ S₂ : ShortComplex C} (h₂ : S₂.ShortExact) (φ : S₁.X₃ ⟶ S₂.X₃) :
    (ShortComplex.mk
      (pullback.lift (f := S₁.g ≫ φ) (g := S₂.g) (0 : S₂.X₁ ⟶ S₁.X₂) S₂.f (by simp))
      (pullback.fst (S₁.g ≫ φ) S₂.g) (pullback.lift_fst _ _ _)).ShortExact := by
  have := h₂.mono_f
  have := h₂.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ inferInstance
  · apply (ShortComplex.exact_iff_exact_up_to_refinements _).2
    intro A z hz
    dsimp only at z hz
    obtain ⟨y, hy⟩ := h₂.exact.lift' (z ≫ pullback.snd (S₁.g ≫ φ) S₂.g) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hz, zero_comp])
    refine ⟨A, 𝟙 A, inferInstance, y, ?_⟩
    dsimp only
    rw [Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, comp_zero]
      exact hz
    · rw [Category.assoc, pullback.lift_snd]
      exact hy.symm
  · exact mono_of_mono_fac (pullback.lift_snd
      (0 : S₂.X₁ ⟶ S₁.X₂) S₂.f (by simp))

/-- The difference extension splits exactly when the prescribed maps on the end terms extend to
a map of the two short exact sequences. -/
lemma difference_retraction_iff
    {S₁ S₂ : ShortComplex C} (h₂ : S₂.ShortExact)
    (ψ : S₁.X₁ ⟶ S₂.X₁) (φ : S₁.X₃ ⟶ S₂.X₃) :
    let l := pullback.lift (f := S₁.g ≫ φ) (g := S₂.g) (0 : S₂.X₁ ⟶ S₁.X₂) S₂.f (by simp)
    let j := pullback.lift (f := S₁.g ≫ φ) (g := S₂.g) S₁.f (ψ ≫ S₂.f) (by simp)
    (∃ r : cokernel j ⟶ S₂.X₁, (l ≫ cokernel.π j) ≫ r = 𝟙 _) ↔
      ∃ t : S₁.X₂ ⟶ S₂.X₂, S₁.f ≫ t = ψ ≫ S₂.f ∧
        t ≫ S₂.g = S₁.g ≫ φ := by
  dsimp only
  let p := pullback.fst (S₁.g ≫ φ) S₂.g
  let s := pullback.snd (S₁.g ≫ φ) S₂.g
  let l := pullback.lift (f := S₁.g ≫ φ) (g := S₂.g) (0 : S₂.X₁ ⟶ S₁.X₂) S₂.f (by simp)
  let j := pullback.lift (f := S₁.g ≫ φ) (g := S₂.g) S₁.f (ψ ≫ S₂.f) (by simp)
  let q := cokernel.π j
  have := h₂.mono_f
  have hP := differencePullback_shortExact (S₁ := S₁) h₂ φ
  have : Epi p := hP.epi_g
  have hlp : l ≫ p = 0 := pullback.lift_fst _ _ _
  have hls : l ≫ s = S₂.f := pullback.lift_snd _ _ _
  have hjp : j ≫ p = S₁.f := pullback.lift_fst _ _ _
  have hjs : j ≫ s = ψ ≫ S₂.f := pullback.lift_snd _ _ _
  have hjq : j ≫ q = 0 := cokernel.condition j
  have hps : p ≫ S₁.g ≫ φ = s ≫ S₂.g := pullback.condition
  constructor
  · rintro ⟨r, hr⟩
    change (l ≫ q) ≫ r = 𝟙 _ at hr
    obtain ⟨t, ht⟩ := hP.exact.desc' (s - q ≫ r ≫ S₂.f) (by
      change l ≫ (s - q ≫ r ≫ S₂.f) = 0
      rw [Preadditive.comp_sub, hls, ← Category.assoc, ← Category.assoc,
        hr, Category.id_comp, sub_self])
    change p ≫ t = s - q ≫ r ≫ S₂.f at ht
    refine ⟨t, ?_, ?_⟩
    · rw [← hjp, Category.assoc, ht, Preadditive.comp_sub, hjs,
        ← Category.assoc, hjq, zero_comp, sub_zero]
    · apply (cancel_epi p).1
      rw [← Category.assoc, ht, Preadditive.sub_comp, Category.assoc,
        Category.assoc, S₂.zero, comp_zero, comp_zero, sub_zero, hps]
  · rintro ⟨t, hft, htg⟩
    obtain ⟨c, hc⟩ := h₂.exact.lift' (s - p ≫ t) (by
      rw [Preadditive.sub_comp, Category.assoc, htg, hps, sub_self])
    have hjc : j ≫ c = 0 := by
      apply (cancel_mono S₂.f).1
      rw [Category.assoc, hc, Preadditive.comp_sub, hjs,
        ← Category.assoc, hjp, hft, sub_self, zero_comp]
    refine ⟨cokernel.desc j c hjc, ?_⟩
    change (l ≫ q) ≫ cokernel.desc j c hjc = 𝟙 _
    rw [Category.assoc, cokernel.π_desc]
    apply (cancel_mono S₂.f).1
    rw [Category.assoc, hc, Preadditive.comp_sub, hls,
      ← Category.assoc, hlp, zero_comp, sub_zero, Category.id_comp]

/-- A short complex whose image under a fully faithful additive functor is short exact is itself
short exact. -/
lemma shortExact_of_fullyFaithful_map
    {B : Type*} [Category B] [Abelian B] (F : C ⥤ B) [F.Additive]
    (hF : F.FullyFaithful) (S : ShortComplex C) (hS : (S.map F).ShortExact) :
    S.ShortExact := by
  have := hF.full
  have := hF.faithful
  have : Mono (S.map F).f := hS.mono_f
  have : Mono (F.map S.f) := hS.mono_f
  have : Epi (F.map S.g) := hS.epi_g
  refine ShortComplex.ShortExact.mk' ?_
    (F.mono_of_mono_map (f := S.f) inferInstance)
    (F.epi_of_epi_map (f := S.g) inferInstance)
  exact S.exact_of_f_is_kernel (isLimitOfReflects F
    (((KernelFork.ofι S.f S.zero).isLimitMapConeEquiv F).symm hS.exact.fIsKernel))

/-- A short exact sequence whose middle term is identified with the image of an object under a
fully faithful additive functor descends along that functor, with the same splittings. -/
lemma descend_shortExact
    {B : Type*} [Category B] [Abelian B] (R : C ⥤ B) [R.Additive]
    (hR : R.FullyFaithful) {A Z N : C} {H : B}
    (a : R.obj A ⟶ H) (b : H ⟶ R.obj Z) (hab : a ≫ b = 0)
    (hS : (ShortComplex.mk a b hab).ShortExact) (e : R.obj N ≅ H) :
    ∃ (a' : A ⟶ N) (b' : N ⟶ Z) (h : a' ≫ b' = 0),
      (ShortComplex.mk a' b' h).ShortExact ∧
      ((∃ r : N ⟶ A, a' ≫ r = 𝟙 A) ↔
        (∃ r : H ⟶ R.obj A, a ≫ r = 𝟙 (R.obj A))) := by
  let a' := hR.preimage (a ≫ e.inv)
  let b' := hR.preimage (e.hom ≫ b)
  have ha : R.map a' = a ≫ e.inv := hR.map_preimage _
  have hb : R.map b' = e.hom ≫ b := hR.map_preimage _
  have hz : a' ≫ b' = 0 := by
    apply hR.map_injective
    simp only [R.map_comp, R.map_zero, ha, hb, Category.assoc, e.inv_hom_id_assoc, hab]
  refine ⟨a', b', hz, ?_, ?_⟩
  · apply shortExact_of_fullyFaithful_map R hR
    let eS : (ShortComplex.mk a' b' hz).map R ≅ ShortComplex.mk a b hab :=
      ShortComplex.isoMk (Iso.refl _) e (Iso.refl _)
        (by simpa using (congrArg (· ≫ e.hom) ha).symm)
        (by simpa using hb.symm)
    exact ShortComplex.shortExact_of_iso eS.symm hS
  · constructor
    · rintro ⟨r, hr⟩
      refine ⟨e.inv ≫ R.map r, ?_⟩
      rw [← Category.assoc, ← ha, ← R.map_comp, hr, R.map_id]
    · rintro ⟨r, hr⟩
      refine ⟨hR.preimage (e.hom ≫ r), ?_⟩
      apply hR.map_injective
      rw [R.map_comp, R.map_id, ha, hR.map_preimage, Category.assoc,
        e.inv_hom_id_assoc, hr]

end ExtensionDifference

section Ext

/-- A degree-zero Yoneda extension is a short exact sequence. -/
lemma yonedaExtension_shortExact
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {B A : 𝒜}
    (E : Abelian.YonedaExtension B A 0) :
    (ShortComplex.mk E.f E.g (yonedaExtension_comp_zero E)).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · apply (ShortComplex.exact_iff_exact_toComposableArrows _).2
    change (ComposableArrows.mk₂ E.f E.g).Exact
    exact E.exact_g
  · have := E.mono_f
    infer_instance
  · have := E.epi_g
    infer_instance

/-- The Ext class of a short exact sequence kills a map out of its kernel term exactly when
that map extends to the middle term. -/
lemma extClass_comp_mk₀_eq_zero_iff
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{e} 𝒜]
    {S : ShortComplex 𝒜} {Y : 𝒜} (hS : S.ShortExact) (v : S.X₁ ⟶ Y) :
    hS.extClass.comp (Abelian.Ext.mk₀ v) (add_zero 1) = 0 ↔
      ∃ t : S.X₂ ⟶ Y, S.f ≫ t = v := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y
      (Abelian.Ext.mk₀ v) (add_zero 1) h
    obtain ⟨t, rfl⟩ := (Abelian.Ext.mk₀_bijective S.X₂ Y).surjective y
    exact ⟨t, (Abelian.Ext.mk₀_bijective S.X₁ Y).injective
      (by rwa [Abelian.Ext.mk₀_comp_mk₀] at hy)⟩
  · rintro ⟨t, rfl⟩
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc _

end Ext

variable {X : RingedTopos.{v, u, w}}
  {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]

/-- The structure map of a first order thickening is locally surjective on the underlying
sheaves of rings. -/
lemma structureMap_locallySurjective (D : TwoExtensions i) :
    Presheaf.IsLocallySurjective Y.J
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp).hom := by
  change Presheaf.IsLocallySurjective Y.J
    (Functor.whiskerRight i.fSharp.hom (forget₂ CommRingCat RingCat))
  have h := D.thickening.surjective
  refine ⟨?_⟩
  intro U s
  simpa [Presheaf.imageSieve] using h.imageSieve_mem s

/-- The maps on the end terms commute with the actions of the square-zero ideal. This is the
action square evaluated on local pure tensors. -/
def CompatibleActions (D : TwoExtensions i) : Prop :=
  ∀ (U : Y.Cᵒᵖ) (a : D.thickening.I.val.obj U) (x : D.F.val.obj U),
    D.kernelMap.val.app U
        (D.firstActionMap.1.val.app U
          (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O)).obj)).unit.app
            (PresheafOfModules.tensorObj D.thickening.I.val D.F.val)).app U
            (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] x))) =
      D.secondActionMap.1.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
            i.toToposHom).obj X.O))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
            i.toToposHom).obj X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj D.thickening.I.val D.G.val)).app U
          (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U]
            D.quotientMap.val.app U x))

/-- A middle-term map inducing the prescribed maps on the two end terms. -/
def IsExtensionLift (D : TwoExtensions i)
    (φ' : D.firstExtension.Z.left ⟶ D.secondExtension.Z.left) : Prop :=
  ((SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).map
        D.kernelMap ≫ D.secondExtension.f = D.firstExtension.f ≫ φ') ∧
  (φ' ≫ D.secondExtension.g = D.firstExtension.g ≫
    (SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).map
        D.quotientMap)

/-- The first leg of the cospan whose pullback carries the difference construction: the quotient
map of the first extension, followed by the given map of quotient modules. -/
noncomputable abbrev differenceCospanFst (D : TwoExtensions i) :=
  D.firstExtension.g ≫ (SheafOfModules.restrictScalars
    ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).map D.quotientMap

/-- The map from the kernel of the first extension into the twisted pullback of the two middle
terms. Its cokernel is the difference extension. -/
noncomputable def differenceRelation (D : TwoExtensions i) :
    (SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj D.K ⟶
      pullback (differenceCospanFst D) D.secondExtension.g :=
  pullback.lift D.firstExtension.f
    ((SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).map
        D.kernelMap ≫ D.secondExtension.f) (by
          rw [← Category.assoc, yonedaExtension_comp_zero, zero_comp,
            Category.assoc, yonedaExtension_comp_zero, comp_zero])

end Deformation.ToposThickening

end
