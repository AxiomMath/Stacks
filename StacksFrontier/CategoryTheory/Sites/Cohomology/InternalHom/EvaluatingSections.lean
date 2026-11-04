module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
import StacksCore.Tactic.StacksAttribute

/-! # Evaluating sections of the internal Hom complex of a ringed site

Let `(C, O)` be a ringed site and let `L` and `M` be complexes of `O`-modules. A section of
degree `n` of the internal Hom complex `SheafHom(L, M)` over an object `U` of the site is, by
the characterisation `AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsIso`, a degree-`n`
cochain from `L|_U` to `M|_U`, so it can be *evaluated* on a section of `L` of degree `p` over
any object `V` of the site equipped with an arrow `V ⟶ U`. This file records that evaluation
and its elementary properties: additivity and `O`-linearity in each variable, compatibility
with restriction along arrows of the site, the Leibniz rule for the differential of the
internal Hom complex, and the formula for the induced map
`AlgebraicGeometry.RingedSite.homMap`.

Evaluation is the language in which the canonical maps between internal Hom complexes and
tensor complexes — the evaluation map of Stacks 0A92 and the composition map of Stacks 0A91 —
are characterised, since those maps are specified by their action on homogeneous local
sections.

## Main definitions

* `AlgebraicGeometry.RingedSite.applyHomSectionOver`: evaluation of a homogeneous section of
  the internal Hom complex over `U` on a section of its source over an object of the slice site
  over `U`.
* `AlgebraicGeometry.RingedSite.applyHomSection`: the case of a section over `U` itself.
* `AlgebraicGeometry.RingedSite.evaluateHomSectionMap`: evaluation at a *fixed* section of the
  source, as a morphism of sheaves of `O|_U`-modules on the slice site.

## Main results

* `AlgebraicGeometry.RingedSite.applyHomSectionOver_differential`: the Leibniz rule.
* `AlgebraicGeometry.RingedSite.applyHomSectionOver_homMap` and
  `AlgebraicGeometry.RingedSite.applyHomSection_homMap`: `homMap k m` acts by pre- and
  postcomposition.
* `AlgebraicGeometry.RingedSite.homSection_ext`: a section of the internal Hom complex is
  determined by its values.

## Implementation notes

`applyHomSectionOver` is phrased so that its arguments and value are sections of the complexes
`L` and `M` themselves rather than of their restrictions `L|_U` and `M|_U`. The two spellings
are definitionally equal — restriction reindexes the sections along `C/U ⥤ C` — but only the
first is in the vocabulary of the statements of Stacks 0A91 and 0A92, and the
`SheafHomComplex.sectionsEquiv` API of
`StacksDraft.Ch21.Sec34.HomComplexTensorCurrying` is what bridges the two without any
transparency option.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Evaluate a degree-`n` section of the internal Hom complex over `U` on a degree-`p` section
of its source over an object `V` of the site equipped with an arrow `i : V ⟶ U`. -/
abbrev applyHomSectionOver (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U) (n p q : ℤ)
    (hpq : p + n = q) (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    (L.X q).val.obj (op V) :=
  ((H.sectionsEquiv U n f).v p q hpq).val.app (op (Over.mk i)) x

/-- Evaluate a degree-`n` section of the internal Hom complex over `U` on a degree-`p` section
of its source over `U` itself. -/
abbrev applyHomSection (H : SheafHomComplex X K L) (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op U)) : (L.X q).val.obj (op U) :=
  applyHomSectionOver X H U U (𝟙 U) n p q hpq f x

variable (H : SheafHomComplex X K L)

/-- Evaluating a section over `U` on a section over `W` along a composite is evaluating its
restriction to the intermediate object. -/
lemma applyHomSectionOver_restrict_comp (U V W : X.C) (i : V ⟶ U) (g : W ⟶ V) (n p q : ℤ)
    (hpq : p + n = q) (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op W)) :
    applyHomSectionOver X H U W (g ≫ i) n p q hpq f x =
      applyHomSectionOver X H V W g n p q hpq ((H.obj.X n).val.map i.op f) x :=
  H.restrict_natural i n p q hpq f g x

/-- Evaluating a section over `U` on a section over `V` is evaluating its restriction to `V`. -/
lemma applyHomSectionOver_restrict (U V : X.C) (i : V ⟶ U) (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq f x =
      applyHomSection X H V n p q hpq ((H.obj.X n).val.map i.op f) x := by
  simpa using applyHomSectionOver_restrict_comp X H U V V i (𝟙 V) n p q hpq f x

/-- Evaluation commutes with restriction of the source section along an arrow of the site. -/
lemma applyHomSectionOver_map (U V : X.C) (i : V ⟶ U) (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op U)) :
    applyHomSectionOver X H U V i n p q hpq f ((K.X p).val.map i.op x) =
      (L.X q).val.map i.op (applyHomSection X H U n p q hpq f x) :=
  PresheafOfModules.naturality_apply ((H.sectionsEquiv U n f).v p q hpq).val
    (Over.homMk i (by simp) : Over.mk i ⟶ Over.mk (𝟙 U)).op x

/-- Evaluation is additive in the Hom section. -/
lemma applyHomSectionOver_add_left (U V : X.C) (i : V ⟶ U) (n p q : ℤ) (hpq : p + n = q)
    (f f' : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq (f + f') x =
      applyHomSectionOver X H U V i n p q hpq f x +
        applyHomSectionOver X H U V i n p q hpq f' x :=
  congrArg (fun z : Cochain _ _ n ↦ ((z.v p q hpq).val.app (op (Over.mk i))) x)
    (map_add (H.sectionsEquiv U n) f f')

/-- Evaluation is additive in the Hom section. -/
lemma applyHomSection_add_left (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (f f' : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op U)) :
    applyHomSection X H U n p q hpq (f + f') x =
      applyHomSection X H U n p q hpq f x + applyHomSection X H U n p q hpq f' x :=
  applyHomSectionOver_add_left X H U U (𝟙 U) n p q hpq f f' x

/-- Evaluation is semilinear in the Hom section: scaling the section by `r` scales the value by
the restriction of `r`. -/
lemma applyHomSectionOver_smul_left (U V : X.C) (i : V ⟶ U)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq (r • f) x =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map i.op r •
        applyHomSectionOver X H U V i n p q hpq f x :=
  H.smul_natural U r n p q hpq f i x

/-- Evaluation is `O(U)`-linear in the Hom section. -/
lemma applyHomSection_smul_left (U : X.C)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) (n p q : ℤ)
    (hpq : p + n = q) (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op U)) :
    applyHomSection X H U n p q hpq (r • f) x =
      r • applyHomSection X H U n p q hpq f x := by
  rw [applyHomSection, applyHomSectionOver_smul_left]
  congr 1
  simp

/-- Evaluation is additive in the source section. -/
lemma applyHomSectionOver_add_right (U V : X.C) (i : V ⟶ U) (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x x' : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq f (x + x') =
      applyHomSectionOver X H U V i n p q hpq f x +
        applyHomSectionOver X H U V i n p q hpq f x' :=
  map_add _ x x'

/-- Evaluation is linear in the source section. -/
lemma applyHomSectionOver_smul_right (U V : X.C) (i : V ⟶ U) (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U))
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V))
    (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq f (r • x) =
      r • applyHomSectionOver X H U V i n p q hpq f x :=
  map_smul _ r x

/-- Evaluation commutes with scaling the source section by a unit of `ℤ`. -/
lemma applyHomSectionOver_units_zsmul_right (U V : X.C) (i : V ⟶ U) (n p q : ℤ)
    (hpq : p + n = q) (f : (H.obj.X n).val.obj (op U)) (c : ℤˣ)
    (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq f (c • x) =
      c • applyHomSectionOver X H U V i n p q hpq f x :=
  map_zsmul _ (c : ℤ) x

/-- Evaluation is linear in the source section. -/
lemma applyHomSection_smul_right (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U))
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (x : (K.X p).val.obj (op U)) :
    applyHomSection X H U n p q hpq f (r • x) = r • applyHomSection X H U n p q hpq f x :=
  map_smul _ r x

/-- Evaluation is additive in the source section. -/
lemma applyHomSection_add_right (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x x' : (K.X p).val.obj (op U)) :
    applyHomSection X H U n p q hpq f (x + x') =
      applyHomSection X H U n p q hpq f x + applyHomSection X H U n p q hpq f x' :=
  map_add _ _ _

/-- A section of the internal Hom complex is determined by the values of its evaluations. -/
lemma homSection_ext (U : X.C) (n : ℤ) {f g : (H.obj.X n).val.obj (op U)}
    (h : ∀ (p q : ℤ) (hpq : p + n = q) (V : X.C) (i : V ⟶ U) (x : (K.X p).val.obj (op V)),
      applyHomSectionOver X H U V i n p q hpq f x =
        applyHomSectionOver X H U V i n p q hpq g x) : f = g := by
  refine (H.sectionsEquiv U n).injective (Cochain.ext _ _ fun p q hpq ↦ ?_)
  exact SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext
    (LinearMap.ext fun x ↦ h p q hpq W.unop.left W.unop.hom x))


/-- A sum of morphisms of sheaves of modules acts on sections by addition. -/
lemma add_val_app_apply {U : X.C}
    {A B : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)} (f g : A ⟶ B)
    (W : (Over U)ᵒᵖ) (x : A.val.obj W) :
    (f + g).val.app W x = f.val.app W x + g.val.app W x := by
  with_unfolding_all rfl


/-- A unit multiple of a morphism of sheaves of modules acts on sections by scaling. -/
lemma units_zsmul_val_app_apply {U : X.C}
    {A B : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)}
    (f : A ⟶ B) (n : ℤˣ) (W : (Over U)ᵒᵖ) (x : A.val.obj W) :
    (n • f).val.app W x = n • (f.val.app W) x :=
  zsmul_val_app_apply (n : ℤ) f W x

/-- **The Leibniz rule for the internal Hom complex.** Evaluating the differential of a Hom
section is the differential of its evaluation plus, up to sign, its evaluation on the
differential of the source section. -/
private lemma applyHomSectionOver_differential_aux (U V : X.C) (i : V ⟶ U) (n p q : ℤ)
    (hpq : p + n = q) (f : (H.obj.X n).val.obj (op U))
    (x : ((restrictComplex X K U).X p).val.obj (op (Over.mk i))) :
    ((H.sectionsEquiv U (n + 1) ((H.obj.d n (n + 1)).val.app (op U) f)).v p (q + 1)
          (by omega)).val.app (op (Over.mk i)) x =
      ((restrictComplex X L U).d q (q + 1)).val.app (op (Over.mk i))
          (((H.sectionsEquiv U n f).v p q hpq).val.app (op (Over.mk i)) x) +
        (n + 1).negOnePow •
          ((H.sectionsEquiv U n f).v (p + 1) (q + 1) (by omega)).val.app (op (Over.mk i))
            (((restrictComplex X K U).d p (p + 1)).val.app (op (Over.mk i)) x) := by
  have h := congrArg (fun z : Cochain _ _ (n + 1) ↦
    ((z.v p (q + 1) (by omega)).val.app (op (Over.mk i))) x) (H.sectionsEquiv_d U n (n + 1) f)
  rw [δ_v n (n + 1) rfl _ p (q + 1) (by omega) q (p + 1) (by omega) rfl] at h
  simp only [add_val_app_apply, units_zsmul_val_app_apply, comp_val_app_apply] at h
  exact h

/-- **The Leibniz rule for the internal Hom complex.** Evaluating the differential of a Hom
section is the differential of its evaluation plus, up to sign, its evaluation on the
differential of the source section. -/
lemma applyHomSectionOver_differential (U V : X.C) (i : V ⟶ U) (n p q q' : ℤ) (hpq : p + n = q)
    (hqq' : q + 1 = q') (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i (n + 1) p q' (by omega)
        ((H.obj.d n (n + 1)).val.app (op U) f) x =
      (L.d q q').val.app (op V) (applyHomSectionOver X H U V i n p q hpq f x) +
        (n + 1).negOnePow •
          applyHomSectionOver X H U V i n (p + 1) q' (by omega) f
            ((K.d p (p + 1)).val.app (op V) x) := by
  subst hqq'
  exact applyHomSectionOver_differential_aux X H U V i n p q hpq f x

/-- Evaluation of the induced map `homMap k m` is pre- and postcomposition with `k` and `m`. -/
lemma applyHomSectionOver_homMap
    {K' L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : K' ⟶ K) (f : L ⟶ L') (U V : X.C) (i : V ⟶ U) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X K L).obj.X n).val.obj (op U)) (x : (K'.X p).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X K' L') U V i n p q hpq
        (((homMap X g f).f n).val.app (op U) s) x =
      (f.f q).val.app (op V)
        (applyHomSectionOver X (sheafHomComplex X K L) U V i n p q hpq s
          ((g.f p).val.app (op V) x)) :=
  congrArg (fun z ↦ (z.val.app (op (Over.mk i))) x)
    (sectionsIso_homMap_v X g f U n p q hpq s)

/-- Evaluation of the induced map `homMap k m` is pre- and postcomposition with `k` and `m`. -/
lemma applyHomSection_homMap
    {K' L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : K' ⟶ K) (f : L ⟶ L') (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X K L).obj.X n).val.obj (op U)) (x : (K'.X p).val.obj (op U)) :
    applyHomSection X (sheafHomComplex X K' L') U n p q hpq
        (((homMap X g f).f n).val.app (op U) s) x =
      (f.f q).val.app (op U)
        (applyHomSection X (sheafHomComplex X K L) U n p q hpq s ((g.f p).val.app (op U) x)) :=
  applyHomSectionOver_homMap X g f U U (𝟙 U) n p q hpq s x

/-- The map on sections underlying `evaluateHomSectionMap`: over an object `W ⟶ U` of the
slice site it evaluates a Hom section on the restriction of the fixed source section `k`. -/
def evaluateHomSectionPresheafMap (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (k : (K.X p).val.obj (op U)) :
    ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj
        (H.obj.X n)).val.presheaf ⟶
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj
        (L.X q)).val.presheaf where
  app W := AddCommGrpCat.ofHom
    { toFun := fun ψ ↦ applyHomSection X H W.unop.left n p q hpq ψ
        ((K.X p).val.map W.unop.hom.op k)
      map_zero' := congrArg
        (fun z : Cochain _ _ n ↦
          ((z.v p q hpq).val.app (op (Over.mk (𝟙 W.unop.left))))
            ((K.X p).val.map W.unop.hom.op k))
        (map_zero (H.sectionsEquiv W.unop.left n))
      map_add' := fun ψ ψ' ↦ applyHomSection_add_left X H W.unop.left n p q hpq ψ ψ'
        ((K.X p).val.map W.unop.hom.op k) }
  naturality := by
    intro W Z g
    ext ψ
    have hk : (K.X p).val.map Z.unop.hom.op k =
        (K.X p).val.map g.unop.left.op ((K.X p).val.map W.unop.hom.op k) := by
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w g.unop]
    change applyHomSection X H Z.unop.left n p q hpq
        ((H.obj.X n).val.map g.unop.left.op ψ)
        ((K.X p).val.map Z.unop.hom.op k) =
      (L.X q).val.map g.unop.left.op
        (applyHomSection X H W.unop.left n p q hpq ψ
          ((K.X p).val.map W.unop.hom.op k))
    rw [← applyHomSectionOver_restrict X H W.unop.left Z.unop.left g.unop.left n p q hpq
      ψ ((K.X p).val.map Z.unop.hom.op k), hk]
    exact applyHomSectionOver_map X H W.unop.left Z.unop.left g.unop.left n p q hpq ψ
      ((K.X p).val.map W.unop.hom.op k)

/-- Evaluation at a *fixed* degree-`p` section `k` of the source over `U`, as a morphism of
sheaves of `O|_U`-modules from the degree-`n` term of the internal Hom complex to the
degree-`q` term of the target, both restricted to the site over `U`. -/
def evaluateHomSectionMap (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (k : (K.X p).val.obj (op U)) :
    (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj (H.obj.X n) ⟶
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj (L.X q) :=
  ⟨PresheafOfModules.homMk (evaluateHomSectionPresheafMap X H U n p q hpq k) (fun W r ψ ↦
    applyHomSection_smul_left X H W.unop.left r n p q hpq ψ
      ((K.X p).val.map W.unop.hom.op k))⟩

/-- `evaluateHomSectionMap` acts on sections over an object of the slice site by evaluation on
the restriction of the fixed source section. -/
lemma evaluateHomSectionMap_app (U : X.C) (W : (Over U)ᵒᵖ) (n p q : ℤ) (hpq : p + n = q)
    (k : (K.X p).val.obj (op U)) (ψ : (H.obj.X n).val.obj (op W.unop.left)) :
    (evaluateHomSectionMap X H U n p q hpq k).val.app W ψ =
      applyHomSection X H W.unop.left n p q hpq ψ ((K.X p).val.map W.unop.hom.op k) := rfl

/-- `evaluateHomSectionMap_app`, with the section of the internal Hom complex read as a
section of its restriction to the slice site over `U`. This is the spelling in which the
morphism is applied inside a cochain between restricted complexes. -/
lemma evaluateHomSectionMap_app' (U : X.C) (W : (Over U)ᵒᵖ) (n p q : ℤ) (hpq : p + n = q)
    (k : (K.X p).val.obj (op U))
    (ψ : ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj
      (H.obj.X n)).val.obj W) :
    (evaluateHomSectionMap X H U n p q hpq k).val.app W ψ =
      applyHomSection X H W.unop.left n p q hpq ψ ((K.X p).val.map W.unop.hom.op k) := rfl

/-- `evaluateHomSectionMap` acts on sections over `U` itself by evaluation on the fixed source
section. -/
lemma evaluateHomSectionMap_app_id (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (k : (K.X p).val.obj (op U)) (ψ : (H.obj.X n).val.obj (op U)) :
    (evaluateHomSectionMap X H U n p q hpq k).val.app (op (Over.mk (𝟙 U))) ψ =
      applyHomSection X H U n p q hpq ψ k := by
  rw [evaluateHomSectionMap_app]
  congr 1
  simp

end AlgebraicGeometry.RingedSite

end
