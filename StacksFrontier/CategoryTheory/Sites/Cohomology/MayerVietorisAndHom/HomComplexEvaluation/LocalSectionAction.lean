module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Homology.Bifunctor
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexMaps
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplex

/-!
# Local sections of internal Hom complexes acting on local sections of their source

Let `(C, O)` be a ringed site. This file sets up the action of a local section of an internal
Hom complex on a local section of its source, one of the two ingredients of the evaluation
morphism of Stacks 0A92, and the specification `EvaluationConstruction` of evaluation
morphisms by their action on homogeneous local pure tensors.

The action is `applyHomSection`, with the variant `applyHomSectionOver` at a section over a
smaller object of the slice site; `evaluateHomSectionMap` fixes a source section and lets a
homogeneous Hom section act on all sections of the slice, and `evaluationCochain` assembles the
evaluation of a homogeneous pure tensor as a cochain on the slice.

## Main definitions

* `Stacks.Cohomology.restrictSection`: restriction of a local section of a sheaf of modules
  along an arrow of the site.
* `Stacks.Cohomology.sheafSection`: a local section of the underlying presheaf of modules of a
  complex of sheaves of modules, read as a section of the sheaf.
* `Stacks.Cohomology.applyHomSection`: the value of a local section of an internal Hom complex
  on a local section of its source.
* `Stacks.Cohomology.EvaluationConstruction`: evaluation morphisms, specified by their action
  on all homogeneous local pure tensors.

## Main results

* `Stacks.Cohomology.applyHomSectionOver_smul_left` and `_smul_right`: the action over a
  smaller object of the slice is `O(U)`-linear in the Hom section and in the source section.

## Implementation notes

The sections of an internal Hom complex over an object are, by construction, Mathlib's
`CochainComplex.HomComplex` of the restrictions to the slice site. `applyHomSection` and
`applyHomSectionOver` carry that identification in their own result types, and
`restrictSection` and `restrictScalar` declare the modules of sections themselves as their
result types, which is what lets the lemmas be proved by composing equalities rather than by
rewriting.

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

/-- Restriction of a local section of a sheaf of modules along an arrow of the site, with the
sections over the source as declared result type: Mathlib's restriction map lands in a
restriction of scalars, and this abbreviation is where that identification is discharged. -/
noncomputable abbrev restrictSection
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {U V : X.C}
    (i : V ⟶ U) (s : (M.val.obj (op U) : ModuleCat _)) : (M.val.obj (op V) : ModuleCat _) :=
  M.val.map i.op s

/-- Restriction of a local section of the sheaf of rings along an arrow of the site. -/
private noncomputable abbrev restrictScalar {U V : X.C} (i : V ⟶ U)
    (c : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : RingCat)) :
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) : RingCat) :=
  (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map i.op c

/-- Restriction along the identity is the identity on sections. -/
private lemma restrictSection_id
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : (M.val.obj (op U) : ModuleCat _)) : restrictSection X M (𝟙 U) s = s := by
  change M.val.map (𝟙 (op U)) s = s
  rw [M.val.map_id]
  rfl

/-- Restriction of sections is additive. -/
private lemma restrictSection_add
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {U V : X.C} (i : V ⟶ U)
    (s t : (M.val.obj (op U) : ModuleCat _)) :
    restrictSection X M i (s + t) = restrictSection X M i s + restrictSection X M i t :=
  map_add _ _ _

/-- Restriction of sections is semilinear over restriction of scalars. -/
private lemma restrictSection_smul
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {U V : X.C} (i : V ⟶ U)
    (c : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : RingCat))
        (s : (M.val.obj (op U) : ModuleCat _)) :
    restrictSection X M i (c • s) = restrictScalar X i c • restrictSection X M i s :=
  PresheafOfModules.map_smul M.val i.op c s

/-- Restricting twice is restricting once. -/
private lemma restrictSection_comp
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {U V W : X.C}
    (j : W ⟶ V) (i : V ⟶ U) (s : (M.val.obj (op U) : ModuleCat _)) :
    restrictSection X M j (restrictSection X M i s) = restrictSection X M (j ≫ i) s :=
  (PresheafOfModules.map_comp_apply M.val i.op j.op s).symm

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
private lemma restrictSection_map
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : M ⟶ N)
    {U V : X.C} (i : V ⟶ U) (s : (M.val.obj (op U) : ModuleCat _)) :
    (f.val.app (op V)) (restrictSection X M i s) =
      restrictSection X N i (f.val.app (op U) s) :=
  PresheafOfModules.naturality_apply f.val i.op s

/-- A local section of the underlying presheaf of modules of a complex of sheaves of modules,
with the sheaf's own module of sections as declared result type: the monoidal structure spells
the ring `X.O.obj ⋙ forget₂ CommRingCat RingCat` where the sheaf spells it
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj`, and this abbreviation is where that
identification is discharged. -/
noncomputable abbrev sheafSection
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (n : ℤ)
        (U : X.Cᵒᵖ)
    (x : ((underlyingPresheafComplex X A).X n).obj U) : (A.X n).val.obj U := x

/-- Evaluate a homogeneous internal Hom section on a section of its source. -/
noncomputable abbrev applyHomSection
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op U)) :
    (L.X q).val.obj (op U) :=
  (((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) f).v p q hpq).val.app
    (op (Over.mk (𝟙 U)))) x

/-- Evaluate a local Hom section on a section over a smaller object of the slice. -/
noncomputable abbrev applyHomSectionOver
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    (L.X q).val.obj (op V) :=
  (((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) f).v p q hpq).val.app
    (op (Over.mk i))) x

/-- Evaluation commutes with restriction of a Hom section to a smaller slice. -/
private lemma applyHomSectionOver_restrict
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq f x =
      applyHomSection X H V n p q hpq ((H.obj.X n).val.map i.op f) x := by
  have h := H.restrict_natural i n p q hpq f (𝟙 V) x
  change (((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) f).v p q hpq).val.app
      (op (Over.mk (𝟙 V ≫ i)))) x = _ at h
  rwa [Category.id_comp] at h

private lemma applyHomSectionOver_map
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op U)) :
    applyHomSectionOver X H U V i n p q hpq f ((K.X p).val.map i.op x) =
      (L.X q).val.map i.op (applyHomSection X H U n p q hpq f x) := by
  let g := (((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) f).v p q hpq).val)
  let j : Over.mk i ⟶ Over.mk (𝟙 U) := Over.homMk i (by simp)
  let x' : ((restrictComplex X K U).X p).val.obj (op (Over.mk (𝟙 U))) := x
  exact PresheafOfModules.naturality_apply g j.op x'

/-- Evaluation maps, specified by their action on all homogeneous local pure tensors. -/
structure EvaluationConstruction where
  /-- The evaluation morphism for a triple of complexes. -/
  evaluate :
      (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) →
    tensorTotal X (sheafHomComplex X L M).obj K ⟶
      (sheafHomComplex X (sheafHomComplex X K L).obj M).obj
  /-- Its action on a homogeneous local pure tensor, with the Koszul sign. -/
  evaluate_tmul : ∀
      (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (U : X.C) (t r s a p : ℤ) (hra : r + s = a) (hap : a + t = p)
      (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
      (k : (K.X r).val.obj (op U))
      (ψ : ((sheafHomComplex X K L).obj.X s).val.obj (op U)),
    applyHomSection X (sheafHomComplex X (sheafHomComplex X K L).obj M)
        U (t + r) s p (by omega)
        (((evaluate K L M).f (t + r)).val.app (op U)
          (tensorTotalSection X (sheafHomComplex X L M).obj K U t r φ k)) ψ =
      (r + (-a) * r).negOnePow •
        applyHomSection X (sheafHomComplex X L M) U t a p hap φ
          (applyHomSection X (sheafHomComplex X K L) U s r a hra ψ k)

private lemma over_app
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : A ⟶ B) (U V : X.C)
        (i : V ⟶ U)
    (x : A.val.obj (op V)) :
    ((f.over U).val.app (op (Over.mk i))) x = (f.val.app (op V)) x := rfl

private theorem applyHomSectionOver_sheafHomComplexMap
    {K K' L L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : K' ⟶ K) (f : L ⟶ L') (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X K L).obj.X n).val.obj (op U))
    (x : (K'.X p).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X K' L') U V i n p q hpq
      (((sheafHomComplexMap X g f).f n).val.app (op U) s) x =
    (f.f q).val.app (op V)
      (applyHomSectionOver X (sheafHomComplex X K L) U V i n p q hpq s
        ((g.f p).val.app (op V) x)) := by
  have h := (sheafHomComplexConstruction X).map_isInduced g f U n p q hpq s
  have h' := congrArg (fun z => (z.val.app (op (Over.mk i))) x) h
  simp only [SheafOfModules.comp_val, ModuleCat.hom_comp,
    PresheafOfModules.comp_app] at h'
  exact h'

private theorem applyHomSection_sheafHomComplexMap
    {K K' L L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : K' ⟶ K) (f : L ⟶ L') (U : X.C) (n p q : ℤ)
    (hpq : p + n = q) (s : ((sheafHomComplex X K L).obj.X n).val.obj (op U))
    (x : (K'.X p).val.obj (op U)) :
    applyHomSection X (sheafHomComplex X K' L') U n p q hpq
      (((sheafHomComplexMap X g f).f n).val.app (op U) s) x =
    (f.f q).val.app (op U)
      (applyHomSection X (sheafHomComplex X K L) U n p q hpq s
        ((g.f p).val.app (op U) x)) :=
  applyHomSectionOver_sheafHomComplexMap X g f U U (𝟙 U) n p q hpq s x

private lemma applyHomSectionOver_add_left
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q)
    (f f' : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq (f + f') x =
      applyHomSectionOver X H U V i n p q hpq f x +
        applyHomSectionOver X H U V i n p q hpq f' x := by
  have h := map_add (AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n)) f f'
  exact congrArg (fun z => (((z.v p q hpq).val.app (op (Over.mk i))) x)) h

private lemma applyHomSection_add_left
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n p q : ℤ)
    (hpq : p + n = q) (f f' : (H.obj.X n).val.obj (op U))
    (x : (K.X p).val.obj (op U)) :
    applyHomSection X H U n p q hpq (f + f') x =
      applyHomSection X H U n p q hpq f x + applyHomSection X H U n p q hpq f' x :=
  applyHomSectionOver_add_left X H U U (𝟙 U) n p q hpq f f' x

private lemma applyHomSection_smul_left
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n p q : ℤ)
    (hpq : p + n = q) (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op U)) :
    applyHomSection X H U n p q hpq (c • f) x =
      c • applyHomSection X H U n p q hpq f x := by
  have h := H.smul_natural U c n p q hpq f (𝟙 U) x
  have hi : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (𝟙 U).op = 𝟙 _ := by simp
  rw [hi] at h
  exact h

/-- Fixing a source section makes a homogeneous local Hom section act on all
sections of the slice. -/
private noncomputable def evaluateHomSectionMap
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (k : (K.X p).val.obj (op U)) :
    (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj (H.obj.X n) ⟶
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj (L.X q) := by
  let F := (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj
      (H.obj.X n)
  let G := (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj (L.X q)
  letI (W : (Over U)ᵒᵖ) : CommRing
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj W) :=
    inferInstanceAs
        (CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W.unop.left)))
  letI (W : (Over U)ᵒᵖ) : Module (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj W)
      ((L.X q).val.obj (op W.unop.left)) :=
    inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W.unop.left))
      ((L.X q).val.obj (op W.unop.left)))
  let τ₀ : F.val.presheaf ⟶ G.val.presheaf :=
    { app := fun W => AddCommGrpCat.ofHom {
        toFun := fun ψ =>
          applyHomSection X H W.unop.left n p q hpq ψ
            ((K.X p).val.map W.unop.hom.op k)
        map_zero' := by
          have hz := map_zero (AddCommGrpCat.Hom.hom ((H.sectionsIso W.unop.left).hom.f n))
          have hz' := congrArg
            (fun z => (z.v p q hpq).val.app (op (Over.mk (𝟙 W.unop.left)))) hz
          exact congrArg (fun f => f ((K.X p).val.map W.unop.hom.op k)) hz'
        map_add' := by
          intro ψ ψ'
          exact applyHomSection_add_left X H W.unop.left n p q hpq ψ ψ'
            ((K.X p).val.map W.unop.hom.op k)
      }
      naturality := by
        intro W Z f
        ext ψ
        have hk : (K.X p).val.map Z.unop.hom.op k =
            (K.X p).val.map f.unop.left.op
              ((K.X p).val.map W.unop.hom.op k) := by
          rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w f.unop]
        change applyHomSection X H Z.unop.left n p q hpq
            ((H.obj.X n).val.map f.unop.left.op ψ)
            ((K.X p).val.map Z.unop.hom.op k) =
          (L.X q).val.map f.unop.left.op
            (applyHomSection X H W.unop.left n p q hpq ψ
              ((K.X p).val.map W.unop.hom.op k))
        have h₁ := applyHomSectionOver_restrict X H W.unop.left Z.unop.left
          f.unop.left n p q hpq ψ ((K.X p).val.map Z.unop.hom.op k)
        have h₂ := applyHomSectionOver_map X H W.unop.left Z.unop.left
          f.unop.left n p q hpq ψ ((K.X p).val.map W.unop.hom.op k)
        rw [← h₁, hk]
        exact h₂
    }
  let τ : F.val ⟶ G.val := PresheafOfModules.homMk τ₀ (by
      intro W c ψ
      have h := H.smul_natural W.unop.left c n p q hpq ψ (𝟙 W.unop.left)
        ((K.X p).val.map W.unop.hom.op k)
      change applyHomSection X H W.unop.left n p q hpq (c • ψ)
          ((K.X p).val.map W.unop.hom.op k) =
        c • applyHomSection X H W.unop.left n p q hpq ψ
          ((K.X p).val.map W.unop.hom.op k)
      have hi : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (𝟙 (op W.unop.left)) = 𝟙 _ :=
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map_id _
      rwa [op_id, hi] at h)
  exact ⟨τ⟩

private lemma evaluateHomSectionMap_app_id
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n p q : ℤ)
    (hpq : p + n = q) (k : (K.X p).val.obj (op U))
    (ψ : (H.obj.X n).val.obj (op U)) :
    ((evaluateHomSectionMap X H U n p q hpq k).val.app
      (op (Over.mk (𝟙 U)))) ψ = applyHomSection X H U n p q hpq ψ k := by
  simp [evaluateHomSectionMap, applyHomSection]
  rfl

private lemma evaluateHomSectionMap_app
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (W : (Over U)ᵒᵖ)
    (n p q : ℤ) (hpq : p + n = q) (k : (K.X p).val.obj (op U))
    (ψ : (H.obj.X n).val.obj (op W.unop.left)) :
    ((evaluateHomSectionMap X H U n p q hpq k).val.app W) ψ =
        applyHomSection X H W.unop.left n p q hpq ψ
          ((K.X p).val.map W.unop.hom.op k) := by
  simp [evaluateHomSectionMap, applyHomSection]
  rfl

/-- The local Hom cochain obtained by evaluating a homogeneous Hom section on a source
section, with its Koszul sign. -/
private noncomputable def evaluationCochain
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    Cochain (restrictComplex X (sheafHomComplex X K L).obj U)
      (restrictComplex X M U) (t + r) := by
  refine Cochain.mk ?_
  intro s p hsp
  let a := r + s
  have hra : r + s = a := rfl
  have hap : a + t = p := by omega
  exact (r + (-a) * r).negOnePow •
      (evaluateHomSectionMap X (sheafHomComplex X K L) U s r a hra k ≫
        ((AddCommGrpCat.Hom.hom (((sheafHomComplex X L M).sectionsIso U).hom.f t) φ).v
          a p hap))

/-- Scaling a local Hom section by a section of the structure sheaf scales its action over a
smaller object of the slice by the restriction of that scalar. -/
lemma applyHomSectionOver_smul_left
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq (c • f) x =
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map i.op c) •
        applyHomSectionOver X H U V i n p q hpq f x := by
  have h := H.smul_natural U c n p q hpq f i x
  exact h

private lemma applyHomSectionOver_add_right
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x x' : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq f (x + x') =
      applyHomSectionOver X H U V i n p q hpq f x +
        applyHomSectionOver X H U V i n p q hpq f x' :=
  map_add _ x x'

/-- The action of a local Hom section over a smaller object of the slice is linear in the
source section. -/
lemma applyHomSectionOver_smul_right
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U))
        (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V))
    (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq f (c • x) =
      c • applyHomSectionOver X H U V i n p q hpq f x :=
  map_smul _ c x

private lemma over_zsmul_app_apply (U : X.C)
    {A B : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)} (f : A ⟶ B)
    (n : ℤ) (W : (Over U)ᵒᵖ) (x : A.val.obj W) :
    (ModuleCat.Hom.hom ((n • f).val.app W)) x =
      n • (ModuleCat.Hom.hom (f.val.app W)) x := by
  have hv : (n • f).val = n • f.val := by with_unfolding_all rfl
  rw [hv, PresheafOfModules.zsmul_app, ModuleCat.hom_zsmul, LinearMap.smul_apply]

private lemma over_units_smul_app_apply (U : X.C)
    {A B : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)} (f : A ⟶ B)
    (n : ℤˣ) (W : (Over U)ᵒᵖ) (x : A.val.obj W) :
    ((n • f).val.app W) x = n • (f.val.app W) x :=
  over_zsmul_app_apply (X := X) U f (n : ℤ) W x

private lemma applyHomSection_add_right
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) (U : X.C) (n p q : ℤ)
    (hpq : p + n = q) (f : (H.obj.X n).val.obj (op U))
    (x x' : (K.X p).val.obj (op U)) :
    applyHomSection X H U n p q hpq f (x + x') =
      applyHomSection X H U n p q hpq f x + applyHomSection X H U n p q hpq f x' :=
  map_add _ _ _

end Stacks.Cohomology

end
