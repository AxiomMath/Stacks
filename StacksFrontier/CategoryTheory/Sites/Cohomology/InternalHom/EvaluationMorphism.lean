module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationCochain
import StacksCore.Tactic.StacksAttribute

/-! # The evaluation morphism of internal Hom complexes on a ringed site

Let `(C, O)` be a ringed site and let `K`, `L` and `M` be complexes of `O`-modules. This file
assembles the canonical morphism of complexes of `O`-modules of Stacks 0A92,

`Tot(SheafHom(L, M) ⊗_O K) ⟶ SheafHom(SheafHom(K, L), M)`,

out of the homogeneous local evaluation sections of
`StacksDraft.Ch21.Sec34.EvaluationOfHomComplexes`, and proves that it is functorial in all
three complexes.

## Main definitions

* `AlgebraicGeometry.RingedSite.evaluationSectionAt`: the evaluation section of
  `AlgebraicGeometry.RingedSite.evaluationSection`, transported to a degree `n = t + r`.
* `AlgebraicGeometry.RingedSite.evaluationMap`: the evaluation morphism of Stacks 0A92.
* `AlgebraicGeometry.RingedSite.EvaluationConstruction`: the evaluation morphism together with
  its characterisation on homogeneous local pure tensors.

## Main results

* `AlgebraicGeometry.RingedSite.evaluationSectionAt_d`: the Leibniz rule for evaluation.
* `AlgebraicGeometry.RingedSite.evaluationMap_tensorTotalSection`: the characterisation of
  `evaluationMap` on homogeneous local pure tensors.
* `AlgebraicGeometry.RingedSite.evaluationConstruction`: **Stacks 0A92**, the canonical
  evaluation morphism.
* `AlgebraicGeometry.RingedSite.evaluationMap_natural`: **Stacks 0A92**, functoriality in all
  three complexes.

## Implementation notes

The construction follows `StacksDraft.Ch21.Sec34.CompositionOfHomComplexes` exactly. The
bilinearity of `AlgebraicGeometry.RingedSite.evaluationSection` makes it a morphism out of the
degreewise tensor product of presheaves of modules, the Leibniz rule
`AlgebraicGeometry.RingedSite.evaluationSectionAt_d` makes the resulting family a morphism out
of the total complex of the double complex of those tensor products, and
`AlgebraicGeometry.RingedSite.sheafifyLift` passes from there to the degreewise
sheafification, which is `AlgebraicGeometry.RingedSite.tensorTotal`.

Unlike composition, evaluation raises the degree of its two arguments to `t + r` with a Koszul
sign depending on the degree of the section it is applied to, so the Leibniz rule cannot be
read off a cochain-level identity; it is proved in the evaluation vocabulary of
`StacksDraft.Ch21.Sec34.HomSectionEvaluation` through
`AlgebraicGeometry.RingedSite.homSection_ext`, from the Leibniz rule
`AlgebraicGeometry.RingedSite.applyHomSectionOver_differential` applied three times, and the
resulting signs are compared with `Int.negOnePow_eq_iff`.

Because the degree of `evaluationSection` is literally `t + r`, a version
`evaluationSectionAt` carrying the degree as a separate parameter is needed: the two summands
of the Leibniz rule naturally live in degrees `(t + 1) + r` and `t + (r + 1)`, which are not
the degree `t + r + 1` of the target.

Functoriality is proved from the uniqueness statement
`AlgebraicGeometry.RingedSite.tensorTotal_hom_ext`: a morphism out of `tensorTotal` is
determined by its values on the homogeneous local pure tensors, so both composites need only
be computed there, where each is a single application of
`AlgebraicGeometry.RingedSite.applyHomSection_homMap`.

## References

* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A60](https://stacks.math.columbia.edu/tag/0A60)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-- An additive map commutes with scaling by a unit of `ℤ`. -/
private lemma map_units_zsmul {A B F : Type*} [AddGroup A] [AddGroup B] [FunLike F A B]
    [AddMonoidHomClass F A B] (f : F) (s : ℤˣ) (x : A) : f (s • x) = s • f x :=
  map_zsmul f (s : ℤ) x

section Sections

variable {K L M :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Evaluation of a Hom section scaled by a unit of `ℤ`. -/
lemma applyHomSectionOver_units_zsmul_left (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (n p q : ℤ) (hpq : p + n = q) (c : ℤˣ) (f : (H.obj.X n).val.obj (op U))
    (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq (c • f) x =
      c • applyHomSectionOver X H U V i n p q hpq f x := by
  refine (congrArg (fun z : Cochain _ _ n ↦ ((z.v p q hpq).val.app (op (Over.mk i))) x)
    (map_units_zsmul (H.sectionsEquiv U n) c f)).trans ?_
  rw [Cochain.units_smul_v]
  exact units_zsmul_val_app_apply X ((H.sectionsEquiv U n f).v p q hpq) c
    (op (Over.mk i)) x

/-- The evaluation section of `evaluationSection`, transported to the degree `n = t + r`. -/
noncomputable def evaluationSectionAt (U : X.C) (t r n : ℤ) (h : t + r = n)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    ((sheafHomComplex X (sheafHomComplex X K L).obj M).obj.X n).val.obj (op U) :=
  ((sheafHomComplex X (sheafHomComplex X K L).obj M).sectionsEquiv U n).symm
    (evaluationCochainAt X U t r n h φ k)

/-- In the degree `t + r` the transported section is `evaluationSection` itself. -/
lemma evaluationSectionAt_self (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    evaluationSectionAt X U t r (t + r) rfl φ k = evaluationSection X U t r φ k := rfl

/-- Evaluating `evaluationSectionAt` on a section of `SheafHom(K, L)` over an object of the
slice site over `U` gives the expected composite, with the Koszul sign. -/
lemma evaluationSectionAt_applyOver (U V : X.C) (i : V ⟶ U) (t r n s a p : ℤ) (h : t + r = n)
    (hra : r + s = a) (hap : a + t = p)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U))
    (ψ : ((sheafHomComplex X K L).obj.X s).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X (sheafHomComplex X K L).obj M) U V i n s p
        (by omega) (evaluationSectionAt X U t r n h φ k) ψ =
      (r + (-a) * r).negOnePow •
        applyHomSectionOver X (sheafHomComplex X L M) U V i t a p hap φ
          (applyHomSection X (sheafHomComplex X K L) V s r a hra ψ
            ((K.X r).val.map i.op k)) := by
  subst h
  exact evaluationSection_applyOver X U V i t r s a p hra hap φ k ψ

/-- `evaluationSectionAt` is additive in the section of `SheafHom(L, M)`. -/
lemma evaluationSectionAt_add_left (U : X.C) (t r n : ℤ) (h : t + r = n)
    (φ φ' : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    evaluationSectionAt X U t r n h (φ + φ') k =
      evaluationSectionAt X U t r n h φ k + evaluationSectionAt X U t r n h φ' k := by
  subst h
  exact evaluationSection_add_left X U t r φ φ' k

/-- `evaluationSectionAt` is additive in the section of `K`. -/
lemma evaluationSectionAt_add_right (U : X.C) (t r n : ℤ) (h : t + r = n)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k k' : (K.X r).val.obj (op U)) :
    evaluationSectionAt X U t r n h φ (k + k') =
      evaluationSectionAt X U t r n h φ k + evaluationSectionAt X U t r n h φ k' := by
  subst h
  exact evaluationSection_add_right X U t r φ k k'

/-- `evaluationSectionAt` is `O(U)`-linear in the section of `SheafHom(L, M)`. -/
lemma evaluationSectionAt_smul_left (U : X.C) (t r n : ℤ) (h : t + r = n)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    evaluationSectionAt X U t r n h (c • φ) k = c • evaluationSectionAt X U t r n h φ k := by
  subst h
  exact evaluationSection_smul_left X U t r c φ k

/-- `evaluationSectionAt` is `O(U)`-linear in the section of `K`. -/
lemma evaluationSectionAt_smul_right (U : X.C) (t r n : ℤ) (h : t + r = n)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    evaluationSectionAt X U t r n h φ (c • k) = c • evaluationSectionAt X U t r n h φ k := by
  subst h
  exact evaluationSection_smul_right X U t r c φ k

/-- `evaluationSectionAt` is compatible with restriction along an arrow of the site. -/
lemma evaluationSectionAt_restrict (U V : X.C) (i : V ⟶ U) (t r n : ℤ) (h : t + r = n)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    ((sheafHomComplex X (sheafHomComplex X K L).obj M).obj.X n).val.map i.op
        (evaluationSectionAt X U t r n h φ k) =
      evaluationSectionAt X V t r n h (((sheafHomComplex X L M).obj.X t).val.map i.op φ)
        ((K.X r).val.map i.op k) := by
  subst h
  exact evaluationSection_restrict X U V i t r φ k

/-- **The Leibniz rule for the internal Hom complex**, for a Hom section and a source section
over the same object. -/
lemma applyHomSection_differential (H : SheafHomComplex X K L) (U : X.C) (n p q q' : ℤ)
    (hpq : p + n = q) (hqq' : q + 1 = q') (f : (H.obj.X n).val.obj (op U))
    (x : (K.X p).val.obj (op U)) :
    applyHomSection X H U (n + 1) p q' (by omega)
        ((H.obj.d n (n + 1)).val.app (op U) f) x =
      (L.d q q').val.app (op U) (applyHomSection X H U n p q hpq f x) +
        (n + 1).negOnePow • applyHomSection X H U n (p + 1) q' (by omega) f
          ((K.d p (p + 1)).val.app (op U) x) :=
  applyHomSectionOver_differential X H U U (𝟙 U) n p q q' hpq hqq' f x

/-- **The Leibniz rule for evaluation.** -/
lemma evaluationSectionAt_d (U : X.C) (t r n n' : ℤ) (h : t + r = n) (hn' : n + 1 = n')
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (k : (K.X r).val.obj (op U)) :
    ((sheafHomComplex X (sheafHomComplex X K L).obj M).obj.d n n').val.app (op U)
        (evaluationSectionAt X U t r n h φ k) =
      evaluationSectionAt X U (t + 1) r n' (by omega)
          (((sheafHomComplex X L M).obj.d t (t + 1)).val.app (op U) φ) k +
        t.negOnePow • evaluationSectionAt X U t (r + 1) n' (by omega) φ
          ((K.d r (r + 1)).val.app (op U) k) := by
  subst hn'
  refine homSection_ext X (sheafHomComplex X (sheafHomComplex X K L).obj M) U (n + 1)
    fun s p hsp V i ψ ↦ ?_
  rw [applyHomSectionOver_differential X (sheafHomComplex X (sheafHomComplex X K L).obj M)
      U V i n s (s + n) p rfl (by omega) (evaluationSectionAt X U t r n h φ k) ψ,
    evaluationSectionAt_applyOver X U V i t r n s (r + s) (s + n) h rfl (by omega) φ k ψ,
    evaluationSectionAt_applyOver X U V i t r n (s + 1) (r + s + 1) p h (by omega) (by omega)
      φ k _,
    applyHomSectionOver_add_left, applyHomSectionOver_units_zsmul_left,
    evaluationSectionAt_applyOver X U V i (t + 1) r (n + 1) s (r + s) p (by omega) rfl
      (by omega) _ k ψ,
    evaluationSectionAt_applyOver X U V i t (r + 1) (n + 1) s (r + s + 1) p (by omega)
      (by omega) (by omega) φ _ ψ,
    map_units_zsmul,
    applyHomSectionOver_differential X (sheafHomComplex X L M) U V i t (r + s) (s + n) p
      (by omega) (by omega) φ _,
    applyHomSection_differential X (sheafHomComplex X K L) V s r (r + s) (r + s + 1) rfl rfl
      ψ ((K.X r).val.map i.op k),
    applyHomSectionOver_add_right, applyHomSectionOver_units_zsmul_right,
    ← PresheafOfModules.naturality_apply (K.d r (r + 1)).val i.op k]
  have hA : (n + 1).negOnePow * (r + -(r + s + 1) * r).negOnePow =
      (r + -(r + s) * r).negOnePow * (t + 1).negOnePow := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add]
    congr 1
    subst h
    ring
  have hB : (n + 1).negOnePow * ((r + -(r + s + 1) * r).negOnePow * (s + 1).negOnePow) =
      t.negOnePow * (r + 1 + -(r + s + 1) * (r + 1)).negOnePow := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
    subst h
    exact ⟨r + s + 1, by ring⟩
  simp only [smul_add, smul_smul, hA, hB]
  abel

/-- Evaluation of homogeneous local sections, as a morphism out of the degreewise tensor
product of the underlying presheaf of modules of the internal Hom complex and that of `K`. -/
noncomputable def evaluationTensorMap (t r n : ℤ) (hn : t + r = n) :
    (underlyingPresheafComplex X (sheafHomComplex X L M).obj).X t ⊗
        (underlyingPresheafComplex X K).X r ⟶
      (underlyingPresheafComplex X
        (sheafHomComplex X (sheafHomComplex X K L).obj M).obj).X n where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun φ k ↦ evaluationSectionAt X U.unop t r n hn φ k)
    (fun φ φ' k ↦ evaluationSectionAt_add_left X U.unop t r n hn φ φ' k)
    (fun c φ k ↦ evaluationSectionAt_smul_left X U.unop t r n hn c φ k)
    (fun φ k k' ↦ evaluationSectionAt_add_right X U.unop t r n hn φ k k')
    (fun c φ k ↦ evaluationSectionAt_smul_right X U.unop t r n hn c φ k)
  naturality {U V} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun φ k ↦ ?_
    change evaluationSectionAt X V.unop t r n hn
        (((sheafHomComplex X L M).obj.X t).val.map f φ) ((K.X r).val.map f k) =
      ((sheafHomComplex X (sheafHomComplex X K L).obj M).obj.X n).val.map f
        (evaluationSectionAt X U.unop t r n hn φ k)
    exact (evaluationSectionAt_restrict X U.unop V.unop f.unop t r n hn φ k).symm

/-- `evaluationTensorMap` sends a local pure tensor of homogeneous sections to their evaluation
section. -/
lemma evaluationTensorMap_tmul (t r n : ℤ) (hn : t + r = n) (U : X.Cᵒᵖ)
    (φ : ((underlyingPresheafComplex X (sheafHomComplex X L M).obj).X t).obj U)
    (k : ((underlyingPresheafComplex X K).X r).obj U) :
    (evaluationTensorMap X t r n hn).app U
        (φ ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] k) =
      evaluationSectionAt X U.unop t r n hn φ k := rfl

end Sections

section Morphism

variable (K L M :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The presheaf-level source of the evaluation morphism: the total complex of the double
complex of pointwise tensor products of the underlying presheaf of the internal Hom complex
`SheafHom(L, M)` and that of `K`. -/
noncomputable abbrev evaluationPresheafSource :
    CochainComplex (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ :=
  tensorTotalPresheaf X (sheafHomComplex X L M).obj K

/-- The degree-`n` component of the presheaf-level evaluation morphism, assembled from the
degreewise evaluation maps on the summands of the total complex. -/
noncomputable def evaluationPresheafDegree (n : ℤ) :
    (evaluationPresheafSource X K L M).X n ⟶
      (underlyingPresheafComplex X
        (sheafHomComplex X (sheafHomComplex X K L).obj M).obj).X n :=
  HomologicalComplex.mapBifunctorDesc fun t r h ↦ evaluationTensorMap X t r n (by simpa using h)

/-- `evaluationPresheafDegree` restricts to `evaluationTensorMap` on each summand. -/
lemma ι_evaluationPresheafDegree (t r n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (t, r) = n) :
    HomologicalComplex.ιMapBifunctor
          (underlyingPresheafComplex X (sheafHomComplex X L M).obj)
          (underlyingPresheafComplex X K)
          (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ) t r n h ≫
        evaluationPresheafDegree X K L M n =
      evaluationTensorMap X t r n (by simpa using h) :=
  HomologicalComplex.ι_mapBifunctorDesc _ t r h

/-- The presheaf-level evaluation morphism. -/
noncomputable def evaluationPresheafMap :
    evaluationPresheafSource X K L M ⟶
      underlyingPresheafComplex X
        (sheafHomComplex X (sheafHomComplex X K L).obj M).obj where
  f n := evaluationPresheafDegree X K L M n
  comm' n n' hnn := by
    obtain rfl : n + 1 = n' := hnn
    refine HomologicalComplex.mapBifunctor.hom_ext fun t r htr ↦ ?_
    have htr' : t + r = n := by simpa using htr
    rw [← Category.assoc, ι_evaluationPresheafDegree, ← Category.assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (ComplexShape.up_mk t (t + 1) rfl) r (n + 1)
        (show t + 1 + r = n + 1 by omega),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ t (ComplexShape.up_mk r (r + 1) rfl) (n + 1)
        (show t + (r + 1) = n + 1 by omega),
      Preadditive.add_comp, Linear.units_smul_comp, Linear.units_smul_comp, Category.assoc,
      Category.assoc, ι_evaluationPresheafDegree, ι_evaluationPresheafDegree]
    have hε₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (t, r) = 1 := rfl
    have hε₂ : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (t, r) = t.negOnePow := rfl
    rw [hε₁, hε₂, one_smul]
    refine PresheafOfModules.hom_ext fun U ↦ ?_
    refine ModuleCat.MonoidalCategory.tensor_ext fun φ k ↦ ?_
    simp only [PresheafOfModules.comp_app, PresheafOfModules.add_app, Units.smul_def,
      PresheafOfModules.zsmul_app]
    exact evaluationSectionAt_d X U.unop t r n (n + 1) htr' rfl φ k

/-- `evaluationPresheafMap` sends a local pure tensor of homogeneous sections, included into the
total complex, to their evaluation section. -/
lemma evaluationPresheafMap_tmul (t r n : ℤ) (hn : t + r = n) (U : X.C)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    ModuleCat.Hom.hom (((evaluationPresheafMap X K L M).f n).app (op U))
        ((HomologicalComplex.ιMapBifunctor
          (underlyingPresheafComplex X (sheafHomComplex X L M).obj)
          (underlyingPresheafComplex X K)
          (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ)
          t r n (by simpa using hn)).app (op U)
          (φ ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] k)) =
      evaluationSectionAt X U t r n hn φ k :=
  (congrArg (fun f ↦ ModuleCat.Hom.hom (f.app (op U))
      (φ ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] k))
    (ι_evaluationPresheafDegree X K L M t r n (by simpa using hn))).trans
      (evaluationTensorMap_tmul X t r n hn (op U) φ k)

/-- **The evaluation morphism of internal Hom complexes** of Stacks 0A92:

`Tot(SheafHom(L, M) ⊗_O K) ⟶ SheafHom(SheafHom(K, L), M)`.

It is the morphism out of the degreewise sheafification determined by the presheaf-level
evaluation morphism. -/
noncomputable def evaluationMap :
    tensorTotal X (sheafHomComplex X L M).obj K ⟶
      (sheafHomComplex X (sheafHomComplex X K L).obj M).obj :=
  sheafifyLift X (evaluationPresheafMap X K L M)

/-- The characterisation of `evaluationMap`: it sends the homogeneous local pure tensor of a
degree-`t` section `φ` of `SheafHom(L, M)` and a degree-`r` section `k` of `K` to the
evaluation section they determine. -/
lemma evaluationMap_tensorTotalSection (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    ((evaluationMap X K L M).f (t + r)).val.app (op U)
        (tensorTotalSection X (sheafHomComplex X L M).obj K U t r φ k) =
      evaluationSection X U t r φ k :=
  (sheafifyLift_unit_apply X (evaluationPresheafMap X K L M) (t + r) (op U) _).trans
    (evaluationPresheafMap_tmul X K L M t r (t + r) rfl U φ k)

end Morphism

/-- An evaluation morphism of internal Hom complexes, characterised by its action on every
homogeneous local pure tensor: the pure tensor of a degree-`t` section `φ` of `SheafHom(L, M)`
and a degree-`r` section `k` of `K` is sent to the section of `SheafHom(SheafHom(K, L), M)`
taking a degree-`s` section `ψ` of `SheafHom(K, L)` to `φ(ψ(k))`, up to the Koszul sign
`(-1)^{r + (-a)r}` with `a = r + s`. -/
structure EvaluationConstruction where
  /-- The morphism of complexes of `O`-modules induced by evaluation. -/
  evaluate (K L M :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotal X (sheafHomComplex X L M).obj K ⟶
      (sheafHomComplex X (sheafHomComplex X K L).obj M).obj
  /-- Homogeneous local pure tensors act by evaluation, with the Koszul sign. -/
  evaluate_tmul : ∀ (K L M :
        CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
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

/-- **Stacks 0A92.** For complexes `K`, `L`, `M` of modules on a ringed site there is a
canonical morphism of complexes of `O`-modules

`Tot(SheafHom(L, M) ⊗_O K) ⟶ SheafHom(SheafHom(K, L), M)`,

namely the one sending each homogeneous local pure tensor `φ ⊗ k` to the local section taking
`ψ` to `φ(ψ(k))`, with the Koszul sign. -/
@[stacks 0A92 "canonical evaluation morphism"]
noncomputable def evaluationConstruction : EvaluationConstruction X where
  evaluate K L M := evaluationMap X K L M
  evaluate_tmul K L M U t r s a p hra hap φ k ψ := by
    rw [evaluationMap_tensorTotalSection]
    exact evaluationSection_apply X U t r s a p hra hap φ k ψ

section Functoriality

/-- The sheafification unit is natural: the sheafification of a morphism of presheaves of
modules agrees with it on sections coming from the presheaf level. -/
lemma sheafification_map_unit_apply
    {P Q : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj} (h : P ⟶ Q)
    (U : X.Cᵒᵖ) (x : P.obj U) :
    ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map h).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app P).app U x) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app Q).app U
        (h.app U x) :=
  (congrArg (fun z ↦ z.app U x)
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.naturality h)).symm

variable {A A' B B' :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- A morphism out of the total tensor-product complex is determined by its values on the
homogeneous local pure tensors. -/
lemma tensorTotal_hom_ext
    {Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {α β : tensorTotal X A B ⟶ Z}
    (hab : ∀ (U : X.C) (t r : ℤ) (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)),
      (α.f (t + r)).val.app (op U) (tensorTotalSection X A B U t r a b) =
        (β.f (t + r)).val.app (op U) (tensorTotalSection X A B U t r a b)) :
    α = β := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  refine ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv _ _).injective ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun t r htr ↦ ?_
  obtain rfl : t + r = n := by simpa using htr
  exact PresheafOfModules.hom_ext fun U ↦
    ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ hab U.unop t r a b

/-- `tensorTotalMap` sends a homogeneous local pure tensor to the pure tensor of the images of
its two factors. -/
lemma tensorTotalMap_tensorTotalSection (f : A ⟶ A') (g : B ⟶ B') (U : X.C) (t r : ℤ)
    (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    ((tensorTotalMap X f g).f (t + r)).val.app (op U) (tensorTotalSection X A B U t r a b) =
      tensorTotalSection X A' B' U t r ((f.f t).val.app (op U) a)
        ((g.f r).val.app (op U) b) := by
  let : (SheafOfModules.forget.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  let leftMap : underlyingPresheafComplex X A ⟶ underlyingPresheafComplex X A' :=
    ((SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f
  let rightMap : underlyingPresheafComplex X B ⟶ underlyingPresheafComplex X B' :=
    ((SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g
  let totalMap : tensorTotalPresheaf X A B ⟶ tensorTotalPresheaf X A' B' :=
    HomologicalComplex.mapBifunctorMap leftMap rightMap
      (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
      (ComplexShape.up ℤ)
  have inclusion_naturality :
      ιTensorTotalPresheaf X A B t r (t + r) rfl ≫ totalMap.f (t + r) =
        ((curriedTensor
            (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
            (leftMap.f t)).app
            ((underlyingPresheafComplex X B).X r) ≫
          ((curriedTensor
            (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
            ((underlyingPresheafComplex X A').X t)).map (rightMap.f r) ≫
          ιTensorTotalPresheaf X A' B' t r (t + r) rfl :=
    HomologicalComplex.ι_mapBifunctorMap leftMap rightMap
      (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
      (ComplexShape.up ℤ)
      t r (t + r) rfl
  have section_naturality := congrArg
    (fun morphism : tensorTotalPresheafTerm X A B t r ⟶
        (tensorTotalPresheaf X A' B').X (t + r) ↦ morphism.app (op U))
    inclusion_naturality
  have key : (totalMap.f (t + r)).app (op U)
        ((ιTensorTotalPresheaf X A B t r (t + r) rfl).app (op U)
          (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b)) =
      (ιTensorTotalPresheaf X A' B' t r (t + r) rfl).app (op U)
        ((f.f t).val.app (op U) a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)]
          (g.f r).val.app (op U) b) :=
    congrArg
      (fun morphism : (tensorTotalPresheafTerm X A B t r).obj (op U) ⟶
          ((tensorTotalPresheaf X A' B').X (t + r)).obj (op U) ↦
        morphism (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b))
      section_naturality
  refine Eq.trans (sheafification_map_unit_apply X (totalMap.f (t + r)) (op U) _) ?_
  exact congrArg
    (fun z ↦ ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
      ((HomologicalComplex.mapBifunctor (underlyingPresheafComplex X A')
        (underlyingPresheafComplex X B')
        (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
        (ComplexShape.up ℤ)).X
          (t + r))).app (op U) z) key

section Natural

variable {K K' L L' M M' :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The evaluation sections are natural in `K`, contranatural in `L` and natural in `M`. -/
lemma evaluationSection_homMap (k : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M') (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U)) (x : (K.X r).val.obj (op U)) :
    ((homMap X (homMap X k l) m).f (t + r)).val.app (op U) (evaluationSection X U t r φ x) =
      evaluationSection X U t r (((homMap X l m).f t).val.app (op U) φ)
        ((k.f r).val.app (op U) x) := by
  refine homSection_ext X (sheafHomComplex X (sheafHomComplex X K' L').obj M') U (t + r)
    fun s p hsp V i ψ ↦ ?_
  rw [applyHomSectionOver_homMap X (homMap X k l) m U V i (t + r) s p hsp
      (evaluationSection X U t r φ x) ψ,
    evaluationSection_applyOver X U V i t r s (r + s) p rfl (by omega) φ x _,
    map_units_zsmul,
    applyHomSection_homMap X k l V s r (r + s) rfl ψ ((K.X r).val.map i.op x),
    PresheafOfModules.naturality_apply (k.f r).val i.op x,
    evaluationSection_applyOver X U V i t r s (r + s) p rfl (by omega) _ _ ψ,
    applyHomSectionOver_homMap X l m U V i t (r + s) p (by omega) φ _]

/-- **Stacks 0A92.** The evaluation morphism is natural in `K`, contranatural in `L` and
natural in `M`. -/
@[stacks 0A92 "functoriality in all three complexes"]
theorem evaluationMap_natural (k : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M') :
    tensorTotalMap X (homMap X l m) k ≫ evaluationMap X K' L' M' =
      evaluationMap X K L M ≫ homMap X (homMap X k l) m := by
  refine tensorTotal_hom_ext X fun U t r φ x ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, comp_val_app_apply',
    comp_val_app_apply', tensorTotalMap_tensorTotalSection, evaluationMap_tensorTotalSection,
    evaluationMap_tensorTotalSection, evaluationSection_homMap]

end Natural

end Functoriality

end AlgebraicGeometry.RingedSite

end
