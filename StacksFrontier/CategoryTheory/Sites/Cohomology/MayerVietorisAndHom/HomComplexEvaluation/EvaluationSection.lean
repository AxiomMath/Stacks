module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexEvaluation.LocalSectionAction
import all StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexEvaluation.LocalSectionAction

/-!
# The evaluation section of a homogeneous pure tensor

Let `(C, O)` be a ringed site, and let `K`, `L`, `M` be complexes of `O`-modules. For local
sections `φ` of the internal Hom complex from `L` to `M` and `k` of `K` over `U`, this file
builds the local section `evaluationSection` of the internal Hom complex from the internal Hom
complex from `K` to `L` to `M` that sends a Hom section `ψ` to `φ(ψ(k))`, up to the Koszul sign
forced by the total-complex and Hom-complex differentials, and proves its compatibility with
restriction, with the `O(U)`-module structures and with the differentials.

## Main definitions

* `Stacks.Cohomology.moduleCochainOfHomSection`: the cochain on the slice site over `U` that a
  local section of an internal Hom complex over `U` corresponds to.

## Main results

* `Stacks.Cohomology.moduleCochainOfHomSection_add`, `_zsmul` and `_d`: passing to the cochain
  of a local Hom section is additive, `ℤ`-homogeneous, and turns the differential of the
  internal Hom complex into the Hom-complex differential.

## Implementation notes

`cochainValue` evaluates a local Hom cochain at an object of the slice with the modules of
sections of the original site as its argument and result types, so that the identification of
sections of the slice with sections of the original site is discharged there rather than inside
the goals.

## References

* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
-/
@[expose] public section

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.RingedSite
open CochainComplex.HomComplex
open Stacks.Cohomology.InternalHom

universe u

namespace Stacks.Cohomology

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-- The value of a local Hom cochain on a section over an object of the slice over `U`, with
the modules of sections of the original site as its argument and result types: the cochain is a
morphism of the restrictions to the slice, so those two identifications are discharged here
rather than inside the goals below. -/
private noncomputable abbrev cochainValue
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) {n : ℤ}
    (c : Cochain (restrictComplex X A U) (restrictComplex X B U) n)
    (p q : ℤ) (hpq : p + n = q) {V : X.C} (i : V ⟶ U)
    (x : (A.X p).val.obj (op V)) : (B.X q).val.obj (op V) :=
  ((c.v p q hpq).val.app (op (Over.mk i))) x

private lemma over_add_app_apply (U : X.C)
    {A B : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)} (f g : A ⟶ B)
    (W : (Over U)ᵒᵖ) (x : A.val.obj W) :
    (ModuleCat.Hom.hom ((f + g).val.app W)) x =
      (ModuleCat.Hom.hom (f.val.app W)) x + (ModuleCat.Hom.hom (g.val.app W)) x := by
  have hv : (f + g).val = f.val + g.val := by with_unfolding_all rfl
  rw [hv, PresheafOfModules.add_app, ModuleCat.hom_add, LinearMap.add_apply]

/-- A sum of cochains is evaluated summand-wise. -/
private lemma cochainValue_add
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) {n : ℤ}
    (c c' : Cochain (restrictComplex X A U) (restrictComplex X B U) n)
    (p q : ℤ) (hpq : p + n = q) {V : X.C} (i : V ⟶ U)
    (x : (A.X p).val.obj (op V)) :
    cochainValue X U (c + c') p q hpq i x =
      cochainValue X U c p q hpq i x + cochainValue X U c' p q hpq i x :=
  (congrArg (fun z : (restrictComplex X A U).X p ⟶ (restrictComplex X B U).X q =>
      (ModuleCat.Hom.hom (z.val.app (op (Over.mk i)))) x) (Cochain.add_v c c' p q hpq)).trans
    (over_add_app_apply (X := X) U (c.v p q hpq) (c'.v p q hpq) (op (Over.mk i)) x)

/-- A sign-scaled cochain is evaluated with the sign pulled out. -/
private lemma cochainValue_units_smul
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) {n : ℤ} (z : ℤˣ)
    (c : Cochain (restrictComplex X A U) (restrictComplex X B U) n)
    (p q : ℤ) (hpq : p + n = q) {V : X.C} (i : V ⟶ U)
    (x : (A.X p).val.obj (op V)) :
    cochainValue X U (z • c) p q hpq i x = z • cochainValue X U c p q hpq i x :=
  (congrArg (fun w : (restrictComplex X A U).X p ⟶ (restrictComplex X B U).X q =>
      (ModuleCat.Hom.hom (w.val.app (op (Over.mk i)))) x)
      (Cochain.units_smul_v z c p q hpq)).trans
    (over_units_smul_app_apply (X := X) U (c.v p q hpq) z (op (Over.mk i)) x)

/-- The Leibniz formula for the Hom-complex differential, evaluated at a section over an
object of the slice. -/
private lemma cochain_delta_value
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) {n : ℤ}
    (c : Cochain (restrictComplex X A U) (restrictComplex X B U) n)
    {V : X.C} (i : V ⟶ U) (p q q' : ℤ) (hpq : p + n = q) (hq : q + 1 = q')
    (x : (A.X p).val.obj (op V)) :
    cochainValue X U (CochainComplex.HomComplex.δ n (n + 1) c) p q' (by omega) i x =
      (B.d q q').val.app (op V) (cochainValue X U c p q hpq i x) +
        (n + 1).negOnePow • cochainValue X U c (p + 1) q' (by omega) i
          ((A.d p (p + 1)).val.app (op V) x) := by
  subst hq
  refine Eq.trans (congrArg
    (fun w : (restrictComplex X A U).X p ⟶ (restrictComplex X B U).X (q + 1) =>
      (ModuleCat.Hom.hom (w.val.app (op (Over.mk i)))) x)
    (CochainComplex.HomComplex.δ_v n (n + 1) rfl c p (q + 1) (by omega) q (p + 1)
      (by omega) rfl)) ?_
  refine (over_add_app_apply (X := X) U (c.v p q hpq ≫ (restrictComplex X B U).d q (q + 1))
    ((n + 1).negOnePow • ((restrictComplex X A U).d p (p + 1) ≫
      c.v (p + 1) (q + 1) (by omega))) (op (Over.mk i)) x).trans ?_
  exact congrArg
    (fun y => (B.d q (q + 1)).val.app (op V) (cochainValue X U c p q hpq i x) + y)
    (over_units_smul_app_apply (X := X) U
      ((restrictComplex X A U).d p (p + 1) ≫ c.v (p + 1) (q + 1) (by omega))
      (n + 1).negOnePow (op (Over.mk i)) x)

private lemma evaluationCochain_app
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (W : (Over U)ᵒᵖ)
    (t r s a p : ℤ) (hra : r + s = a) (hap : a + t = p)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U))
    (ψ : ((sheafHomComplex X K L).obj.X s).val.obj (op W.unop.left)) :
    (((evaluationCochain X U t r φ k).v s p (by omega)).val.app W) ψ =
    (r + (-a) * r).negOnePow •
      applyHomSectionOver X (sheafHomComplex X L M) U W.unop.left W.unop.hom
        t a p hap φ
        (applyHomSection X (sheafHomComplex X K L) W.unop.left s r a hra ψ
          (restrictSection X (K.X r) W.unop.hom k)) := by
  subst a
  let e := evaluateHomSectionMap X (sheafHomComplex X K L) U s r (r + s) rfl k
  let f := ((AddCommGrpCat.Hom.hom
    (((sheafHomComplex X L M).sectionsIso U).hom.f t) φ).v (r + s) p hap)
  let ψ' : (((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj
      ((sheafHomComplex X K L).obj.X s)).val.obj W) := ψ
  have hs := over_zsmul_app_apply (X := X) U (e ≫ f)
    (r + (-(r + s)) * r).negOnePow W ψ'
  have hcomp : (ConcreteCategory.hom (((e ≫ f).val.app W))) ψ' =
      applyHomSectionOver X (sheafHomComplex X L M) U W.unop.left W.unop.hom
        t (r + s) p hap φ
        (applyHomSection X (sheafHomComplex X K L) W.unop.left s r (r + s) rfl ψ
          (restrictSection X (K.X r) W.unop.hom k)) := by
    change (ConcreteCategory.hom (f.val.app W))
      ((ConcreteCategory.hom (e.val.app W)) ψ') = _
    rw [evaluateHomSectionMap_app]
    with_unfolding_all rfl
  change (ConcreteCategory.hom (((r + (-(r + s)) * r).negOnePow •
      (e ≫ f)).val.app W)) ψ' = _
  exact hs.trans (congrArg (fun z => (r + (-(r + s)) * r).negOnePow • z) hcomp)

private lemma evaluationCochain_add_right
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k k' : (K.X r).val.obj (op U)) :
    evaluationCochain X U t r φ (k + k') =
      evaluationCochain X U t r φ k + evaluationCochain X U t r φ k' := by
  apply Cochain.ext
  intro s p hsp
  rw [Cochain.add_v]
  ext W ψ
  let ψ' : ((sheafHomComplex X K L).obj.X s).val.obj (op W.unop.left) := ψ
  change (ConcreteCategory.hom
    (((evaluationCochain X U t r φ (k + k')).v s p hsp).val.app W)) ψ' = _
  have hp : r + s + t = p := by omega
  conv_lhs =>
    rw [evaluationCochain_app (W := W) (a := r + s) (hra := rfl) (hap := hp)
      (ψ := ψ') (φ := φ)]
  conv_rhs =>
    simp only [SheafOfModules.add_val, PresheafOfModules.add_app,
      ModuleCat.hom_add, LinearMap.add_apply]
    rw [evaluationCochain_app (W := W) (a := r + s) (hra := rfl) (hap := hp)
      (ψ := ψ') (φ := φ)]
    rw [evaluationCochain_app (W := W) (a := r + s) (hra := rfl) (hap := hp)
      (ψ := ψ') (φ := φ)]
  rw [restrictSection_add, applyHomSection_add_right, applyHomSectionOver_add_right,
    smul_add]
  rfl

private lemma evaluationCochain_add_left
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (t r : ℤ)
    (φ φ' : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    evaluationCochain X U t r (φ + φ') k =
      evaluationCochain X U t r φ k + evaluationCochain X U t r φ' k := by
  apply Cochain.ext
  intro s p hsp
  rw [Cochain.add_v]
  ext W ψ
  let ψ' : ((sheafHomComplex X K L).obj.X s).val.obj (op W.unop.left) := ψ
  change (ConcreteCategory.hom
      (((evaluationCochain X U t r (φ + φ') k).v s p hsp).val.app W)) ψ' =
    (ConcreteCategory.hom (((evaluationCochain X U t r φ k).v s p hsp).val.app W)) ψ' +
      (ConcreteCategory.hom (((evaluationCochain X U t r φ' k).v s p hsp).val.app W)) ψ'
  have hp : r + s + t = p := by omega
  rw [evaluationCochain_app (W := W) (a := r + s) (hra := rfl) (hap := hp)
      (ψ := ψ') (φ := φ + φ'),
    evaluationCochain_app (W := W) (a := r + s) (hra := rfl) (hap := hp)
      (ψ := ψ') (φ := φ),
    evaluationCochain_app (W := W) (a := r + s) (hra := rfl) (hap := hp)
      (ψ := ψ') (φ := φ')]
  rw [applyHomSectionOver_add_left, smul_add]
  rfl

/-- The section of the iterated internal Hom complex that a homogeneous pure tensor
evaluates to. -/
private noncomputable abbrev evaluationSection
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    ((sheafHomComplex X (sheafHomComplex X K L).obj M).obj.X (t + r)).val.obj
      (op U) :=
  (((sheafHomComplex X (sheafHomComplex X K L).obj M).sectionsIso U).inv.f
    (t + r)).hom (evaluationCochain X U t r φ k)

private lemma evaluationSection_add_left
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (t r : ℤ)
    (φ φ' : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    evaluationSection X U t r (φ + φ') k =
      evaluationSection X U t r φ k + evaluationSection X U t r φ' k := by
  change ((sheafHomComplex X (sheafHomComplex X K L).obj M).sectionsIso U).inv.f
      (t + r) (evaluationCochain X U t r (φ + φ') k) = _
  rw [evaluationCochain_add_left]
  exact map_add _ _ _

private lemma evaluationSection_add_right
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k k' : (K.X r).val.obj (op U)) :
    evaluationSection X U t r φ (k + k') =
      evaluationSection X U t r φ k + evaluationSection X U t r φ k' := by
  change ((sheafHomComplex X (sheafHomComplex X K L).obj M).sectionsIso U).inv.f
      (t + r) (evaluationCochain X U t r φ (k + k')) = _
  rw [evaluationCochain_add_right]
  exact map_add _ _ _

private lemma evaluationSection_applyOver
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U V : X.C) (i : V ⟶ U)
    (t r s a p : ℤ) (hra : r + s = a) (hap : a + t = p)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U))
    (ψ : ((sheafHomComplex X K L).obj.X s).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X (sheafHomComplex X K L).obj M)
        U V i (t + r) s p (by omega) (evaluationSection X U t r φ k) ψ =
      (r + (-a) * r).negOnePow •
        applyHomSectionOver X (sheafHomComplex X L M) U V i t a p hap φ
          (applyHomSection X (sheafHomComplex X K L) V s r a hra ψ
            (restrictSection X (K.X r) i k)) := by
  let H := sheafHomComplex X (sheafHomComplex X K L).obj M
  let e := (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (t + r)).mapIso
    (H.sectionsIso U)
  have he := e.inv_hom_id_apply (evaluationCochain X U t r φ k)
  change (((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f (t + r))
      (((H.sectionsIso U).inv.f (t + r)).hom (evaluationCochain X U t r φ k))).v
      s p (by omega)).val.app (op (Over.mk i))) ψ = _
  rw [show ((H.sectionsIso U).hom.f (t + r)).hom
      (((H.sectionsIso U).inv.f (t + r)).hom (evaluationCochain X U t r φ k)) =
        evaluationCochain X U t r φ k from he]
  exact evaluationCochain_app X U (op (Over.mk i)) t r s a p hra hap φ k ψ

private lemma evaluationSection_apply
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C)
    (t r s a p : ℤ) (hra : r + s = a) (hap : a + t = p)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U))
    (ψ : ((sheafHomComplex X K L).obj.X s).val.obj (op U)) :
    applyHomSection X (sheafHomComplex X (sheafHomComplex X K L).obj M)
        U (t + r) s p (by omega) (evaluationSection X U t r φ k) ψ =
      (r + (-a) * r).negOnePow •
        applyHomSection X (sheafHomComplex X L M) U t a p hap φ
          (applyHomSection X (sheafHomComplex X K L) U s r a hra ψ k) := by
  have h := evaluationSection_applyOver X U U (𝟙 U) t r s a p hra hap φ k ψ
  rwa [restrictSection_id] at h

private noncomputable abbrev evaluationCochainAt
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C)
    (t r n : ℤ) (h : t + r = n)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    Cochain (restrictComplex X (sheafHomComplex X K L).obj U)
      (restrictComplex X M U) n :=
  h ▸ evaluationCochain X U t r φ k

private lemma evaluationCochainAt_v
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C)
    (t r n : ℤ) (h : t + r = n)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) (s p : ℤ) (hsp : s + n = p) :
    (evaluationCochainAt X U t r n h φ k).v s p hsp =
      (evaluationCochain X U t r φ k).v s p (by omega) := by
  subst n
  rfl

/-- The cochain on the slice site over `U` that a local section of an internal Hom complex
over `U` corresponds to under `SheafHomComplex.sectionsIso`. -/
noncomputable def moduleCochainOfHomSection
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n : ℤ)
    (x : (H.obj.X n).val.obj (op U)) :
    Cochain (restrictComplex X K U) (restrictComplex X L U) n :=
  AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) x

private lemma moduleCochainOfHomSection_apply
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n p q : ℤ)
    (hpq : p + n = q) (x : (H.obj.X n).val.obj (op U))
    (k : (K.X p).val.obj (op U)) :
    (((moduleCochainOfHomSection X H U n x).v p q hpq).val.app
      (op (Over.mk (𝟙 U)))) k =
      applyHomSection X H U n p q hpq x k := rfl

/-- Passing to the cochain of a local Hom section is additive. -/
lemma moduleCochainOfHomSection_add
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n : ℤ)
    (x y : (H.obj.X n).val.obj (op U)) :
    moduleCochainOfHomSection X H U n (x + y) =
      moduleCochainOfHomSection X H U n x + moduleCochainOfHomSection X H U n y :=
  map_add _ x y

/-- Passing to the cochain of a local Hom section is `ℤ`-homogeneous. -/
lemma moduleCochainOfHomSection_zsmul
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n : ℤ) (z : ℤ)
    (x : (H.obj.X n).val.obj (op U)) :
    moduleCochainOfHomSection X H U n (z • x) =
      z • moduleCochainOfHomSection X H U n x :=
  map_zsmul _ z x

/-- Passing to the cochain of a local Hom section turns the differential of the internal Hom
complex into the Hom-complex differential of the slice. -/
lemma moduleCochainOfHomSection_d
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n : ℤ)
    (x : (H.obj.X n).val.obj (op U)) :
    moduleCochainOfHomSection X H U (n + 1)
        (((H.obj.d n (n + 1)).val.app (op U)) x) =
      CochainComplex.HomComplex.δ n (n + 1)
        (moduleCochainOfHomSection X H U n x) := by
  let e := H.sectionsIso U
  let x' : (sectionComplex X H.obj U).X n := x
  have hc := e.hom.comm n (n + 1)
  have hcx := congrArg (fun f : AddCommGrpCat.Hom _ _ => f.hom x') hc
  have hsec :
      (AddCommGrpCat.Hom.hom ((sectionComplex X H.obj U).d n (n + 1))) x' =
        (ModuleCat.Hom.hom ((H.obj.d n (n + 1)).val.app (op U))) x' := rfl
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at hcx
  have hmain :
      (CochainComplex.HomComplex.δ n (n + 1)
        (moduleCochainOfHomSection X H U n x)) =
        moduleCochainOfHomSection X H U (n + 1)
          (((H.obj.d n (n + 1)).val.app (op U)) x) := by
    change (ConcreteCategory.hom
        (((restrictComplex X K U).HomComplex (restrictComplex X L U)).d n (n + 1)))
        ((ConcreteCategory.hom (e.hom.f n)) x') =
      (ConcreteCategory.hom (e.hom.f (n + 1)))
        ((ModuleCat.Hom.hom ((H.obj.d n (n + 1)).val.app (op U))) x')
    exact hcx.trans (congrArg (fun y => (e.hom.f (n + 1)) y) hsec)
  simpa only [moduleCochainOfHomSection, CochainComplex.HomComplex_d_hom_apply]
    using hmain.symm

/-- The action is `ℤˣ`-homogeneous in the source section. -/
private lemma applyHomSectionOver_units_zsmul_right
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (z : ℤˣ) (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq f (z • x) =
      z • applyHomSectionOver X H U V i n p q hpq f x :=
  map_zsmul_unit _ z x

private lemma applyHomSectionOver_differential
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i (n + 1) p (q + 1) (by omega)
        (((H.obj.d n (n + 1)).val.app (op U)) f) x =
      (L.d q (q + 1)).val.app (op V)
          (applyHomSectionOver X H U V i n p q hpq f x) +
        (n + 1).negOnePow •
          applyHomSectionOver X H U V i n (p + 1) (q + 1) (by omega) f
            ((K.d p (p + 1)).val.app (op V) x) := by
  have h := cochain_delta_value X U (moduleCochainOfHomSection X H U n f) i p q (q + 1)
    hpq rfl x
  rwa [← moduleCochainOfHomSection_d] at h

private lemma applyHomSectionOver_differential_to
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (n p q q' : ℤ) (hpq : p + n = q) (hqq' : q + 1 = q')
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i (n + 1) p q' (by omega)
        (((H.obj.d n (n + 1)).val.app (op U)) f) x =
      (L.d q q').val.app (op V)
          (applyHomSectionOver X H U V i n p q hpq f x) +
        (n + 1).negOnePow •
          applyHomSectionOver X H U V i n (p + 1) q' (by omega) f
            ((K.d p (p + 1)).val.app (op V) x) := by
  subst q'
  exact applyHomSectionOver_differential X H U V i n p q hpq f x

/-- `evaluationCochain_app`, read through `cochainValue`. -/
private lemma evaluationCochain_cochainValue
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C)
    {V : X.C} (i : V ⟶ U) (t r s a p : ℤ) (hra : r + s = a) (hap : a + t = p)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U))
    (ψ : ((sheafHomComplex X K L).obj.X s).val.obj (op V)) :
    cochainValue X U (evaluationCochain X U t r φ k) s p (by omega) i ψ =
      (r + (-a) * r).negOnePow •
        applyHomSectionOver X (sheafHomComplex X L M) U V i t a p hap φ
          (applyHomSection X (sheafHomComplex X K L) V s r a hra ψ
            (restrictSection X (K.X r) i k)) :=
  evaluationCochain_app X U (op (Over.mk i)) t r s a p hra hap φ k ψ

/-- Re-indexing an evaluation cochain does not change its values. -/
private lemma cochainValue_evaluationCochainAt
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C)
    (t r n : ℤ) (h : t + r = n)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) (s p : ℤ) (hsp : s + n = p)
    {V : X.C} (i : V ⟶ U)
    (ψ : ((sheafHomComplex X K L).obj.X s).val.obj (op V)) :
    cochainValue X U (evaluationCochainAt X U t r n h φ k) s p hsp i ψ =
      cochainValue X U (evaluationCochain X U t r φ k) s p (by omega) i ψ :=
  congrArg (fun w : (restrictComplex X (sheafHomComplex X K L).obj U).X s ⟶
      (restrictComplex X M U).X p =>
    (ModuleCat.Hom.hom (w.val.app (op (Over.mk i)))) ψ)
    (evaluationCochainAt_v X U t r n h φ k s p hsp)

private lemma evaluationCochain_differential
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    CochainComplex.HomComplex.δ (t + r) (t + r + 1)
        (evaluationCochain X U t r φ k) =
      evaluationCochainAt X U (t + 1) r (t + r + 1) (by omega)
          (((sheafHomComplex X L M).obj.d t (t + 1)).val.app (op U) φ) k +
        t.negOnePow • evaluationCochainAt X U t (r + 1) (t + r + 1) (by omega) φ
          ((K.d r (r + 1)).val.app (op U) k) := by
  apply Cochain.ext
  intro s p hsp
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  let V := W.unop.left
  let i : V ⟶ U := W.unop.hom
  let ψ' : ((sheafHomComplex X K L).obj.X s).val.obj (op V) := ψ
  change cochainValue X U (CochainComplex.HomComplex.δ (t + r) (t + r + 1)
      (evaluationCochain X U t r φ k)) s p hsp i ψ' =
    cochainValue X U (evaluationCochainAt X U (t + 1) r (t + r + 1) (by omega)
        (((sheafHomComplex X L M).obj.d t (t + 1)).val.app (op U) φ) k +
      t.negOnePow • evaluationCochainAt X U t (r + 1) (t + r + 1) (by omega) φ
        ((K.d r (r + 1)).val.app (op U) k)) s p hsp i ψ'
  rw [cochain_delta_value X U (evaluationCochain X U t r φ k) i s (p - 1) p
      (by omega) (by omega) ψ',
    cochainValue_add, cochainValue_units_smul,
    cochainValue_evaluationCochainAt, cochainValue_evaluationCochainAt,
    evaluationCochain_cochainValue X U i t r s (r + s) (p - 1) rfl (by omega) φ k ψ',
    evaluationCochain_cochainValue X U i t r (s + 1) (r + s + 1) p (by omega) (by omega)
      φ k ((((sheafHomComplex X K L).obj.d s (s + 1)).val.app (op V)) ψ'),
    evaluationCochain_cochainValue X U i (t + 1) r s (r + s) p rfl (by omega)
      ((((sheafHomComplex X L M).obj.d t (t + 1)).val.app (op U)) φ) k ψ',
    evaluationCochain_cochainValue X U i t (r + 1) s (r + s + 1) p (by omega) (by omega)
      φ ((K.d r (r + 1)).val.app (op U) k) ψ']
  have hψ := applyHomSectionOver_differential X (sheafHomComplex X K L) V V (𝟙 V) s r (r + s)
    rfl ψ' (restrictSection X (K.X r) i k)
  have hφ' := applyHomSectionOver_differential_to X (sheafHomComplex X L M) U V i t (r + s)
    (p - 1) p (by omega) (by omega) φ
    (applyHomSection X (sheafHomComplex X K L) V s r (r + s) rfl ψ'
      (restrictSection X (K.X r) i k))
  change applyHomSection X (sheafHomComplex X K L) V (s + 1) r (r + s + 1) (by omega)
    ((((sheafHomComplex X K L).obj.d s (s + 1)).val.app (op V)) ψ')
    (restrictSection X (K.X r) i k) = _ at hψ
  rw [hψ, hφ']
  simp only [applyHomSectionOver_add_right, applyHomSectionOver_units_zsmul_right,
    map_zsmul_unit, smul_add, smul_smul]
  have hs₁ : ((t + r + 1).negOnePow * (r + (-(r + s + 1)) * r).negOnePow) =
      ((t + 1).negOnePow * (r + (-(r + s)) * r).negOnePow) := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add]
    congr 1
    ring
  have hs₂ : ((t + r + 1).negOnePow * (r + (-(r + s + 1)) * r).negOnePow *
      (s + 1).negOnePow) =
      (t.negOnePow * ((r + 1) + (-(r + s + 1)) * (r + 1)).negOnePow) := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add]
    apply (Int.negOnePow_eq_iff _ _).2
    refine ⟨r + s + 1, ?_⟩
    ring
  simp only [← mul_assoc]
  rw [hs₂, hs₁, ← restrictSection_map X (K.d r (r + 1)) i k]
  let uu : (M.X p).val.obj (op V) :=
    (M.d (p - 1) p).val.app (op V)
      (applyHomSectionOver X (sheafHomComplex X L M) U V i t (r + s) (p - 1) (by omega) φ
        (applyHomSection X (sheafHomComplex X K L) V s r (r + s) rfl ψ'
          (restrictSection X (K.X r) i k)))
  let vv : (M.X p).val.obj (op V) :=
    applyHomSectionOver X (sheafHomComplex X L M) U V i t (r + s + 1) p (by omega) φ
      ((L.d (r + s) (r + s + 1)).val.app (op V)
        (applyHomSection X (sheafHomComplex X K L) V s r (r + s) rfl ψ'
          (restrictSection X (K.X r) i k)))
  let ww : (M.X p).val.obj (op V) :=
    applyHomSectionOver X (sheafHomComplex X L M) U V i t (r + s + 1) p (by omega) φ
      (applyHomSection X (sheafHomComplex X K L) V s (r + 1) (r + s + 1) (by omega) ψ'
        ((K.d r (r + 1)).val.app (op V) (restrictSection X (K.X r) i k)))
  change (r + (-(r + s)) * r).negOnePow • uu +
      (((t + 1).negOnePow * (r + (-(r + s)) * r).negOnePow) • vv +
        (t.negOnePow * ((r + 1) + (-(r + s + 1)) * (r + 1)).negOnePow) • ww) =
    (r + (-(r + s)) * r).negOnePow • uu +
      ((r + (-(r + s)) * r).negOnePow * (t + 1).negOnePow) • vv +
        (t.negOnePow * ((r + 1) + (-(r + s + 1)) * (r + 1)).negOnePow) • ww
  rw [mul_comm (t + 1).negOnePow]
  exact (add_assoc _ _ _).symm

/-- Local Hom sections over `U` are equal when they act equally on all sections over objects
of the slice. -/
private lemma homSection_ext
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n : ℤ) (x y : (H.obj.X n).val.obj (op U))
    (h : ∀ (V : X.C) (i : V ⟶ U) (p q : ℤ) (hpq : p + n = q) (ψ : (K.X p).val.obj (op V)),
      applyHomSectionOver X H U V i n p q hpq x ψ = applyHomSectionOver X H U V i n p q hpq y ψ) :
    x = y := by
  let e := (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) n).mapIso
    (H.sectionsIso U)
  have hinj : Function.Injective (AddCommGrpCat.Hom.hom e.hom) := by
    intro x y hxy
    simpa only [e.hom_inv_id_apply] using congrArg (AddCommGrpCat.Hom.hom e.inv) hxy
  apply hinj
  apply Cochain.ext
  intro p q hpq
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact h W.unop.left W.unop.hom p q hpq

private lemma evaluationSection_restrict
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U V : X.C) (i : V ⟶ U)
    (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    restrictSection X ((sheafHomComplex X (sheafHomComplex X K L).obj M).obj.X (t + r)) i
        (evaluationSection X U t r φ k) =
      evaluationSection X V t r
        (restrictSection X ((sheafHomComplex X L M).obj.X t) i φ)
        (restrictSection X (K.X r) i k) := by
  let H := sheafHomComplex X (sheafHomComplex X K L).obj M
  let en := (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (t + r)).mapIso
    (H.sectionsIso V)
  have hinj : Function.Injective (AddCommGrpCat.Hom.hom en.hom) := by
    intro x y hxy
    simpa only [en.hom_inv_id_apply] using congrArg (AddCommGrpCat.Hom.hom en.inv) hxy
  apply hinj
  change (AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f (t + r)))
      (restrictSection X (H.obj.X (t + r)) i (evaluationSection X U t r φ k)) =
    (AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f (t + r)))
      (evaluationSection X V t r
        (restrictSection X ((sheafHomComplex X L M).obj.X t) i φ)
        (restrictSection X (K.X r) i k))
  apply Cochain.ext
  intro s p hsp
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  let g : W.unop.left ⟶ V := W.unop.hom
  let ψ' : ((sheafHomComplex X K L).obj.X s).val.obj (op W.unop.left) := ψ
  have hU := H.restrict_natural i (t + r) s p hsp (evaluationSection X U t r φ k) g ψ'
  have hV := evaluationSection_applyOver X V W.unop.left g t r s (r + s) p rfl
    (by omega) (restrictSection X ((sheafHomComplex X L M).obj.X t) i φ)
    (restrictSection X (K.X r) i k) ψ'
  have hU' := evaluationSection_applyOver X U W.unop.left (g ≫ i) t r s (r + s) p rfl
    (by omega) φ k ψ'
  change _ = _ at hU
  rw [restrictSection_comp] at hV
  have hout₀ :
      applyHomSectionOver X (sheafHomComplex X L M) U W.unop.left (g ≫ i)
          t (r + s) p (by omega) φ
          (applyHomSection X (sheafHomComplex X K L) W.unop.left s r (r + s) rfl ψ'
            (restrictSection X (K.X r) (g ≫ i) k)) =
        applyHomSectionOver X (sheafHomComplex X L M) V W.unop.left g
          t (r + s) p (by omega)
          (restrictSection X ((sheafHomComplex X L M).obj.X t) i φ)
          (applyHomSection X (sheafHomComplex X K L) W.unop.left s r (r + s) rfl ψ'
            (restrictSection X (K.X r) (g ≫ i) k)) := by
    rw [applyHomSectionOver_restrict, applyHomSectionOver_restrict]
    congr 1
    rw [op_comp, PresheafOfModules.map_comp_apply]
  have hout := congrArg (fun z => (r + (-(r + s)) * r).negOnePow • z) hout₀
  exact hU.symm.trans (hU'.trans (hout.trans hV.symm))

private lemma evaluationSection_smul_right
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (t r : ℤ)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    evaluationSection X U t r φ (c • k) =
      c • evaluationSection X U t r φ k := by
  let H := sheafHomComplex X (sheafHomComplex X K L).obj M
  let e := (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (t + r)).mapIso
    (H.sectionsIso U)
  have hmap : (AddCommGrpCat.Hom.hom e.hom) (evaluationSection X U t r φ (c • k)) =
      (AddCommGrpCat.Hom.hom e.hom) (c • evaluationSection X U t r φ k) := by
    apply Cochain.ext
    intro s p hsp
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ψ
    let ψ' : ((sheafHomComplex X K L).obj.X s).val.obj (op W.unop.left) := ψ
    let i : W.unop.left ⟶ U := W.unop.hom
    change applyHomSectionOver X H U W.unop.left i (t + r) s p hsp
        (evaluationSection X U t r φ (c • k)) ψ' =
      applyHomSectionOver X H U W.unop.left i (t + r) s p hsp
        (c • evaluationSection X U t r φ k) ψ'
    have hleft := evaluationSection_applyOver X U W.unop.left i t r s (r + s) p rfl
      (by omega) φ (c • k) ψ'
    have hright := evaluationSection_applyOver X U W.unop.left i t r s (r + s) p rfl
      (by omega) φ k ψ'
    have hinner :
        applyHomSection X (sheafHomComplex X K L) W.unop.left s r (r + s) rfl ψ'
          (restrictSection X (K.X r) i (c • k)) =
        restrictScalar X i c •
          applyHomSection X (sheafHomComplex X K L) W.unop.left s r (r + s) rfl ψ'
            (restrictSection X (K.X r) i k) :=
      (congrArg
        (fun z : (K.X r).val.obj (op W.unop.left) =>
          applyHomSection X (sheafHomComplex X K L) W.unop.left s r (r + s) rfl ψ' z)
        (restrictSection_smul X (K.X r) i c k)).trans
        (applyHomSectionOver_smul_right X (sheafHomComplex X K L) W.unop.left W.unop.left
          (𝟙 W.unop.left) s r (r + s) rfl ψ' (restrictScalar X i c)
          (restrictSection X (K.X r) i k))
    have hsmul' := applyHomSectionOver_smul_left X H U W.unop.left i c (t + r) s p hsp
      (evaluationSection X U t r φ k) ψ'
    rw [hleft, hsmul', hright, hinner, applyHomSectionOver_smul_right, smul_comm]
  refine Eq.trans (e.hom_inv_id_apply (evaluationSection X U t r φ (c • k))).symm ?_
  refine Eq.trans (congrArg (fun z => (AddCommGrpCat.Hom.hom e.inv) z) hmap) ?_
  exact e.hom_inv_id_apply (c • evaluationSection X U t r φ k)

private lemma evaluationSection_smul_left
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (t r : ℤ)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    evaluationSection X U t r (c • φ) k = c • evaluationSection X U t r φ k := by
  let H := sheafHomComplex X (sheafHomComplex X K L).obj M
  let e := (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (t + r)).mapIso
    (H.sectionsIso U)
  have hmap : (AddCommGrpCat.Hom.hom e.hom) (evaluationSection X U t r (c • φ) k) =
      (AddCommGrpCat.Hom.hom e.hom) (c • evaluationSection X U t r φ k) := by
    apply Cochain.ext
    intro s p hsp
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ψ
    let ψ' : ((sheafHomComplex X K L).obj.X s).val.obj (op W.unop.left) := ψ
    let i : W.unop.left ⟶ U := W.unop.hom
    change applyHomSectionOver X H U W.unop.left i (t + r) s p hsp
        (evaluationSection X U t r (c • φ) k) ψ' =
      applyHomSectionOver X H U W.unop.left i (t + r) s p hsp
        (c • evaluationSection X U t r φ k) ψ'
    have hleft := evaluationSection_applyOver X U W.unop.left i t r s (r + s) p rfl
      (by omega) (c • φ) k ψ'
    have hright := evaluationSection_applyOver X U W.unop.left i t r s (r + s) p rfl
      (by omega) φ k ψ'
    have hsmul' := applyHomSectionOver_smul_left X H U W.unop.left i c (t + r) s p hsp
      (evaluationSection X U t r φ k) ψ'
    rw [hleft, hsmul', hright, applyHomSectionOver_smul_left, smul_comm]
  refine Eq.trans (e.hom_inv_id_apply (evaluationSection X U t r (c • φ) k)).symm ?_
  refine Eq.trans (congrArg (fun z => (AddCommGrpCat.Hom.hom e.inv) z) hmap) ?_
  exact e.hom_inv_id_apply (c • evaluationSection X U t r φ k)

end Stacks.Cohomology

end
