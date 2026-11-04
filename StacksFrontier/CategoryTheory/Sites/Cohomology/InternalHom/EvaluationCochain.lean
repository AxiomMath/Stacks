module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluatingSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplex
import StacksCore.Tactic.StacksAttribute

/-! # The evaluation cochain of internal Hom complexes on a ringed site

Let `(C, O)` be a ringed site and let `K`, `L` and `M` be complexes of `O`-modules. The
canonical evaluation morphism of complexes of `O`-modules of Stacks 0A92,

`Tot(SheafHom(L, M) ⊗_O K) ⟶ SheafHom(SheafHom(K, L), M)`,

is characterised by its values on homogeneous local sections: a section `φ` of `SheafHom(L, M)`
of degree `t` and a section `k` of `K` of degree `r` are sent to the section of
`SheafHom(SheafHom(K, L), M)` of degree `t + r` which takes a section `ψ` of `SheafHom(K, L)`
of degree `s` to `φ(ψ(k))`, up to the Koszul sign `(-1)^{r + (-a)r}` with `a = r + s`.

This file constructs that section, `evaluationSection`, together with the cochain
`evaluationCochain` it corresponds to under the characterising isomorphism
`SheafHomComplex.sectionsIso`, and establishes the properties the evaluation morphism is
assembled from: additivity and `O`-linearity in `φ` and in `k`, and compatibility with
restriction along arrows of the site.

## Main definitions

* `AlgebraicGeometry.RingedSite.evaluationCochain`: the cochain from `SheafHom(K, L)|_U` to
  `M|_U` attached to a homogeneous pair `(φ, k)` of local sections.
* `AlgebraicGeometry.RingedSite.evaluationSection`: the corresponding section of
  `SheafHom(SheafHom(K, L), M)`.

## Main results

* `AlgebraicGeometry.RingedSite.evaluationSection_apply` and
  `AlgebraicGeometry.RingedSite.evaluationSection_applyOver`: the characterising formula.
* `AlgebraicGeometry.RingedSite.evaluationSection_add_left`,
  `AlgebraicGeometry.RingedSite.evaluationSection_add_right`,
  `AlgebraicGeometry.RingedSite.evaluationSection_smul_left`,
  `AlgebraicGeometry.RingedSite.evaluationSection_smul_right` and
  `AlgebraicGeometry.RingedSite.evaluationSection_restrict`: `O`-bilinearity and compatibility
  with restriction, which are what make the pairs `(φ, k)` factor through the tensor product
  and define a morphism of sheaves.

## Implementation notes

Everything is proved through `AlgebraicGeometry.RingedSite.homSection_ext`, which says that a
section of an internal Hom complex is determined by the values of its evaluations; that keeps
the file inside the evaluation vocabulary of
`StacksDraft.Ch21.Sec34.HomSectionEvaluation` and is what lets it be written without any
transparency option.

A section of the internal Hom complex over an object of the slice site over `U` has two
definitionally equal spellings — as a section of the complex itself, and as a section of its
restriction to the slice. Lemmas whose proofs pass through the cochain structure need the
second, so `evaluationCochain_app_slice` states the characterising formula at that spelling and
`evaluationCochain_app` restates it at the first.

## References

* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Tag 0A60](https://stacks.math.columbia.edu/tag/0A60)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/- `map_unit_zsmul` -- that an additive map commutes with scaling by a unit of `ℤ` -- stood
here, unused, and character-identical to `map_units_zsmul` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/EvaluationMorphism.lean:85`, which
imports this module and uses its copy three times. Deleted in favour of that one; both were
`private`, so nothing outside either module could see either. -/

variable {K L M :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Restricting a section along the identity does nothing. -/
private lemma map_id_section {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (U : X.C) (x : A.val.obj (op U)) : A.val.map (𝟙 U).op x = x := by
  rw [op_id, A.val.map_id]
  rfl

/-- The cochain from `SheafHom(K, L)|_U` to `M|_U` that evaluation sends the pure tensor of a
degree-`t` section `φ` of `SheafHom(L, M)` and a degree-`r` section `k` of `K` to: in degree
`s` it is evaluation on `k` followed by `φ`, with the Koszul sign. -/
noncomputable def evaluationCochain (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    Cochain (restrictComplex X (sheafHomComplex X K L).obj U) (restrictComplex X M U) (t + r) :=
  Cochain.mk fun s p hsp ↦
    (r + (-(r + s)) * r).negOnePow •
      (evaluateHomSectionMap X (sheafHomComplex X K L) U s r (r + s) rfl k ≫
        ((sheafHomComplex X L M).sectionsEquiv U t φ).v (r + s) p (by omega))

/-- The value of `evaluationCochain` on a section of `SheafHom(K, L)`, read as a section of the
restriction of `SheafHom(K, L)` to the slice site over `U`. -/
lemma evaluationCochain_app_slice (U : X.C) (W : (Over U)ᵒᵖ) (t r s a p : ℤ) (hra : r + s = a)
    (hap : a + t = p) (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U))
    (ψ : ((restrictComplex X (sheafHomComplex X K L).obj U).X s).val.obj W) :
    ((evaluationCochain X U t r φ k).v s p (by omega)).val.app W ψ =
      (r + (-a) * r).negOnePow •
        applyHomSectionOver X (sheafHomComplex X L M) U W.unop.left W.unop.hom t a p hap φ
          (applyHomSection X (sheafHomComplex X K L) W.unop.left s r a hra ψ
            ((K.X r).val.map W.unop.hom.op k)) := by
  subst hra
  show ((r + (-(r + s)) * r).negOnePow •
      (evaluateHomSectionMap X (sheafHomComplex X K L) U s r (r + s) rfl k ≫
        ((sheafHomComplex X L M).sectionsEquiv U t φ).v (r + s) p (by omega))).val.app W ψ = _
  rw [units_zsmul_val_app_apply, comp_val_app_apply, evaluateHomSectionMap_app']
  rfl

/-- The value of `evaluationCochain` on a section of `SheafHom(K, L)` over an object of the
slice site over `U`. -/
lemma evaluationCochain_app (U : X.C) (W : (Over U)ᵒᵖ) (t r s a p : ℤ) (hra : r + s = a)
    (hap : a + t = p) (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U))
    (ψ : ((sheafHomComplex X K L).obj.X s).val.obj (op W.unop.left)) :
    ((evaluationCochain X U t r φ k).v s p (by omega)).val.app W ψ =
      (r + (-a) * r).negOnePow •
        applyHomSectionOver X (sheafHomComplex X L M) U W.unop.left W.unop.hom t a p hap φ
          (applyHomSection X (sheafHomComplex X K L) W.unop.left s r a hra ψ
            ((K.X r).val.map W.unop.hom.op k)) :=
  evaluationCochain_app_slice X U W t r s a p hra hap φ k ψ

/-- Two cochains out of a restricted complex are equal if their components agree on all sections
over the slice site. -/
private lemma cochain_ext_val_app {U : X.C} {n : ℤ}
    (f g : Cochain (restrictComplex X (sheafHomComplex X K L).obj U) (restrictComplex X M U) n)
    (h : ∀ s p hsp W ψ, (f.v s p hsp).val.app W ψ = (g.v s p hsp).val.app W ψ) : f = g := by
  refine Cochain.ext _ _ fun s p hsp ↦ ?_
  exact SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext
    (LinearMap.ext fun ψ ↦ h s p hsp W ψ))

/-- `evaluationCochain` is additive in the section of `SheafHom(L, M)`. -/
lemma evaluationCochain_add_left (U : X.C) (t r : ℤ)
    (φ φ' : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    evaluationCochain X U t r (φ + φ') k =
      evaluationCochain X U t r φ k + evaluationCochain X U t r φ' k := by
  refine cochain_ext_val_app X _ _ fun s p hsp W ψ ↦ ?_
  rw [Cochain.add_v, add_val_app_apply,
    evaluationCochain_app_slice X U W t r s (r + s) p rfl (by omega) (φ + φ') k ψ,
    evaluationCochain_app_slice X U W t r s (r + s) p rfl (by omega) φ k ψ,
    evaluationCochain_app_slice X U W t r s (r + s) p rfl (by omega) φ' k ψ,
    applyHomSectionOver_add_left, smul_add]
  rfl

/-- `evaluationCochain` is additive in the section of `K`. -/
lemma evaluationCochain_add_right (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k k' : (K.X r).val.obj (op U)) :
    evaluationCochain X U t r φ (k + k') =
      evaluationCochain X U t r φ k + evaluationCochain X U t r φ k' := by
  refine cochain_ext_val_app X _ _ fun s p hsp W ψ ↦ ?_
  rw [Cochain.add_v, add_val_app_apply,
    evaluationCochain_app_slice X U W t r s (r + s) p rfl (by omega) φ (k + k') ψ,
    evaluationCochain_app_slice X U W t r s (r + s) p rfl (by omega) φ k ψ,
    evaluationCochain_app_slice X U W t r s (r + s) p rfl (by omega) φ k' ψ,
    map_add]
  exact (congrArg (fun z ↦ (r + -(r + s) * r).negOnePow • z)
    ((congrArg (applyHomSectionOver X (sheafHomComplex X L M) U W.unop.left W.unop.hom t
          (r + s) p (by omega) φ)
        (applyHomSection_add_right X (sheafHomComplex X K L) W.unop.left s r (r + s) rfl ψ
          ((K.X r).val.map W.unop.hom.op k) ((K.X r).val.map W.unop.hom.op k'))).trans
      (applyHomSectionOver_add_right X (sheafHomComplex X L M) U W.unop.left W.unop.hom t
        (r + s) p (by omega) φ _ _))).trans (smul_add _ _ _)

/-- The section of `SheafHom(SheafHom(K, L), M)` of degree `t + r` corresponding to
`evaluationCochain`. -/
noncomputable def evaluationSection (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    ((sheafHomComplex X (sheafHomComplex X K L).obj M).obj.X (t + r)).val.obj (op U) :=
  ((sheafHomComplex X (sheafHomComplex X K L).obj M).sectionsEquiv U (t + r)).symm
    (evaluationCochain X U t r φ k)

/-- The cochain of `evaluationSection` is `evaluationCochain`. -/
lemma evaluationSection_cochain (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    (sheafHomComplex X (sheafHomComplex X K L).obj M).sectionsEquiv U (t + r)
        (evaluationSection X U t r φ k) = evaluationCochain X U t r φ k :=
  ((sheafHomComplex X (sheafHomComplex X K L).obj M).sectionsEquiv U
    (t + r)).apply_symm_apply _

/-- Evaluating `evaluationSection` on a section of `SheafHom(K, L)` over an object of the slice
site over `U` gives the expected composite, with the Koszul sign. -/
lemma evaluationSection_applyOver (U V : X.C) (i : V ⟶ U) (t r s a p : ℤ) (hra : r + s = a)
    (hap : a + t = p) (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) (ψ : ((sheafHomComplex X K L).obj.X s).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X (sheafHomComplex X K L).obj M) U V i (t + r) s p
        (by omega) (evaluationSection X U t r φ k) ψ =
      (r + (-a) * r).negOnePow •
        applyHomSectionOver X (sheafHomComplex X L M) U V i t a p hap φ
          (applyHomSection X (sheafHomComplex X K L) V s r a hra ψ
            ((K.X r).val.map i.op k)) :=
  (congrArg (fun z : Cochain _ _ (t + r) ↦ ((z.v s p (by omega)).val.app (op (Over.mk i))) ψ)
      (evaluationSection_cochain X U t r φ k)).trans
    (evaluationCochain_app X U (op (Over.mk i)) t r s a p hra hap φ k ψ)

/-- Evaluating `evaluationSection` on a section of `SheafHom(K, L)` over `U` gives the expected
composite, with the Koszul sign. -/
lemma evaluationSection_apply (U : X.C) (t r s a p : ℤ) (hra : r + s = a) (hap : a + t = p)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U))
    (ψ : ((sheafHomComplex X K L).obj.X s).val.obj (op U)) :
    applyHomSection X (sheafHomComplex X (sheafHomComplex X K L).obj M) U (t + r) s p
        (by omega) (evaluationSection X U t r φ k) ψ =
      (r + (-a) * r).negOnePow •
        applyHomSection X (sheafHomComplex X L M) U t a p hap φ
          (applyHomSection X (sheafHomComplex X K L) U s r a hra ψ k) := by
  rw [applyHomSection, evaluationSection_applyOver X U U (𝟙 U) t r s a p hra hap φ k ψ,
    map_id_section]

/-- A sum relation between the cochains transfers to the sections of `evaluationSection`. -/
private lemma evaluationSection_add_of_cochain (U : X.C) (t r : ℤ)
    {φ φ₁ φ₂ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)}
    {k k₁ k₂ : (K.X r).val.obj (op U)}
    (h : evaluationCochain X U t r φ k =
      evaluationCochain X U t r φ₁ k₁ + evaluationCochain X U t r φ₂ k₂) :
    evaluationSection X U t r φ k =
      evaluationSection X U t r φ₁ k₁ + evaluationSection X U t r φ₂ k₂ := by
  show ((sheafHomComplex X (sheafHomComplex X K L).obj M).sectionsEquiv U (t + r)).symm
      (evaluationCochain X U t r φ k) = _
  rw [h, map_add]
  rfl

/-- `evaluationSection` is additive in the section of `SheafHom(L, M)`. -/
lemma evaluationSection_add_left (U : X.C) (t r : ℤ)
    (φ φ' : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    evaluationSection X U t r (φ + φ') k =
      evaluationSection X U t r φ k + evaluationSection X U t r φ' k := by
  exact evaluationSection_add_of_cochain X U t r (evaluationCochain_add_left X U t r ..)

/-- `evaluationSection` is additive in the section of `K`. -/
lemma evaluationSection_add_right (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k k' : (K.X r).val.obj (op U)) :
    evaluationSection X U t r φ (k + k') =
      evaluationSection X U t r φ k + evaluationSection X U t r φ k' := by
  exact evaluationSection_add_of_cochain X U t r (evaluationCochain_add_right X U t r ..)

/-- `evaluationSection` is compatible with restriction along an arrow of the site. -/
lemma evaluationSection_restrict (U V : X.C) (i : V ⟶ U) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    ((sheafHomComplex X (sheafHomComplex X K L).obj M).obj.X (t + r)).val.map i.op
        (evaluationSection X U t r φ k) =
      evaluationSection X V t r (((sheafHomComplex X L M).obj.X t).val.map i.op φ)
        ((K.X r).val.map i.op k) := by
  refine homSection_ext X (sheafHomComplex X (sheafHomComplex X K L).obj M) V (t + r)
    fun s p hsp W g ψ ↦ ?_
  rw [← applyHomSectionOver_restrict_comp X (sheafHomComplex X (sheafHomComplex X K L).obj M)
      U V W i g (t + r) s p hsp (evaluationSection X U t r φ k) ψ,
    evaluationSection_applyOver X U W (g ≫ i) t r s (r + s) p rfl (by omega) φ k ψ,
    evaluationSection_applyOver X V W g t r s (r + s) p rfl (by omega)
      (((sheafHomComplex X L M).obj.X t).val.map i.op φ) ((K.X r).val.map i.op k) ψ]
  have hk : (K.X r).val.map g.op ((K.X r).val.map i.op k) = (K.X r).val.map (g ≫ i).op k := by
    rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  rw [hk]
  congr 1
  exact applyHomSectionOver_restrict_comp X (sheafHomComplex X L M) U V W i g t (r + s) p
    (by omega) φ _

/-- `evaluationSection` is `O(U)`-linear in the section of `K`. -/
lemma evaluationSection_smul_right (U : X.C) (t r : ℤ)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    evaluationSection X U t r φ (c • k) = c • evaluationSection X U t r φ k := by
  refine homSection_ext X (sheafHomComplex X (sheafHomComplex X K L).obj M) U (t + r)
    fun s p hsp V i ψ ↦ ?_
  rw [evaluationSection_applyOver X U V i t r s (r + s) p rfl (by omega) φ (c • k) ψ,
    applyHomSectionOver_smul_left X (sheafHomComplex X (sheafHomComplex X K L).obj M) U V i c
      (t + r) s p hsp (evaluationSection X U t r φ k) ψ,
    evaluationSection_applyOver X U V i t r s (r + s) p rfl (by omega) φ k ψ,
    (K.X r).val.map_smul i.op c k]
  exact (congrArg (fun z ↦ (r + -(r + s) * r).negOnePow • z)
    ((congrArg (applyHomSectionOver X (sheafHomComplex X L M) U V i t (r + s) p (by omega) φ)
        (applyHomSection_smul_right X (sheafHomComplex X K L) V s r (r + s) rfl ψ
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map i.op c)
          ((K.X r).val.map i.op k))).trans
      (applyHomSectionOver_smul_right X (sheafHomComplex X L M) U V i t (r + s) p (by omega) φ
        _ _))).trans (smul_comm _ _ _)

/-- `evaluationSection` is `O(U)`-linear in the section of `SheafHom(L, M)`. -/
lemma evaluationSection_smul_left (U : X.C) (t r : ℤ)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    evaluationSection X U t r (c • φ) k = c • evaluationSection X U t r φ k := by
  refine homSection_ext X (sheafHomComplex X (sheafHomComplex X K L).obj M) U (t + r)
    fun s p hsp V i ψ ↦ ?_
  rw [evaluationSection_applyOver X U V i t r s (r + s) p rfl (by omega) (c • φ) k ψ,
    applyHomSectionOver_smul_left X (sheafHomComplex X (sheafHomComplex X K L).obj M) U V i c
      (t + r) s p hsp (evaluationSection X U t r φ k) ψ,
    evaluationSection_applyOver X U V i t r s (r + s) p rfl (by omega) φ k ψ,
    applyHomSectionOver_smul_left, smul_comm]

/-- `evaluationCochain`, transported to the degree `n = t + r`. -/
noncomputable abbrev evaluationCochainAt (U : X.C) (t r n : ℤ) (h : t + r = n)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    Cochain (restrictComplex X (sheafHomComplex X K L).obj U) (restrictComplex X M U) n :=
  h ▸ evaluationCochain X U t r φ k

/-- The components of `evaluationCochainAt` are those of `evaluationCochain`. -/
lemma evaluationCochainAt_v (U : X.C) (t r n : ℤ) (h : t + r = n)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U))
    (s p : ℤ) (hsp : s + n = p) :
    (evaluationCochainAt X U t r n h φ k).v s p hsp =
      (evaluationCochain X U t r φ k).v s p (by omega) := by
  subst h
  rfl

end AlgebraicGeometry.RingedSite

end
