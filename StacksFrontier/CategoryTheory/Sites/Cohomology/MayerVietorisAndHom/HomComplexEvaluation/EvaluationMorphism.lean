module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexEvaluation.LocalSectionAction
import all StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexEvaluation.LocalSectionAction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexEvaluation.EvaluationSection
import all StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexEvaluation.EvaluationSection

/-!
# The evaluation morphism of internal Hom complexes on a ringed site

Let `(C, O)` be a ringed site. This file constructs the canonical evaluation morphism of Stacks
0A92, from the total tensor product of the internal Hom complex from `L` to `M` with `K` to
the internal Hom complex from the internal Hom complex from `K` to `L` to `M`, and proves that
it is natural in all three complexes.

The degreewise evaluation map of the unsheafified total complex is assembled from the
`O(U)`-bilinear map `evaluationBilinear` that `evaluationSection` induces on local sections; it
is compatible with the differentials, and `AlgebraicGeometry.RingedSite.sheafifyLift` lifts it
to the total tensor complex.

## Main definitions

* `Stacks.Cohomology.evaluationConstruction` and `Stacks.Cohomology.evaluation` (Stacks 0A92):
  the canonical evaluation morphism.

## Main results

* `Stacks.Cohomology.homSection_ext`: two local sections of an internal Hom complex that act
  in the same way on every section agree.
* `Stacks.Cohomology.exists_natural_evaluation`: an evaluation morphism exists and is natural
  in all three complexes.
* `Stacks.Cohomology.evaluation_natural` (Stacks 0A92): the evaluation morphism is natural in
  `K`, contranatural in `L` and natural in `M`.

## Implementation notes

The monoidal structure on presheaves of modules spells the sheaf of rings as
`X.O.obj ⋙ forget₂ CommRingCat RingCat` where a sheaf of modules spells it
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj`, so `evaluationBilinear` is stated over the
former ring, and the local instances of this file transport the ring and module structures
across the two spellings.

The degreewise evaluation map is transported along the index equation `t + r = n` by pattern
matching on that equation rather than by an `eqToHom`, which is what keeps its compatibility
with the differentials free of transport terms.

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

/-- The ring of sections of the structure sheaf over `U`, viewed through the forgetful functor
to rings, is commutative. -/
noncomputable local instance (U : X.Cᵒᵖ) :
    CommRing ((X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U) :=
  inferInstanceAs (CommRing (X.O.obj.obj U))

/-- The sections over `U` of a presheaf of modules are a module over the ring of sections of the
structure sheaf over `U`. -/
noncomputable local instance
    (A : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) (U : X.Cᵒᵖ) :
    Module ((X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U) (A.obj U) :=
  inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (A.obj U))

/-- The two actions of the ring of sections over `U` on the sections over `U` of a presheaf of
modules commute. -/
noncomputable local instance
    (A : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) (U : X.Cᵒᵖ) :
    SMulCommClass ((X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U)
      ((X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U) (A.obj U) :=
  inferInstanceAs (SMulCommClass ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (A.obj U))

/-- The `O(U)`-bilinear map that evaluation induces on local sections: it sends `φ` and `k` to
the Hom section `evaluationSection`. Its source and target are spelled as modules over
`X.O.obj ⋙ forget₂ CommRingCat RingCat`, the ring the monoidal structure on presheaves of
modules uses, rather than over `(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj`. -/
private noncomputable def evaluationBilinear
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (t r : ℤ) (U : X.Cᵒᵖ) :
    ((underlyingPresheafComplex X (sheafHomComplex X L M).obj).X t).obj U →ₗ[
        (X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U]
      ((underlyingPresheafComplex X K).X r).obj U →ₗ[
          (X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U]
        ((underlyingPresheafComplex X (sheafHomComplex X (sheafHomComplex X K L).obj M).obj).X
          (t + r)).obj U where
  toFun φ :=
    { toFun := fun k => evaluationSection X U.unop t r φ k
      map_add' := evaluationSection_add_right X U.unop t r φ
      map_smul' := fun c k => evaluationSection_smul_right X U.unop t r c φ k }
  map_add' φ φ' := LinearMap.ext fun k => evaluationSection_add_left X U.unop t r φ φ' k
  map_smul' c φ := LinearMap.ext fun k => evaluationSection_smul_left X U.unop t r c φ k

private noncomputable def evaluationSummandMap
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (t r : ℤ) :
    ((curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
      ((underlyingPresheafComplex X (sheafHomComplex X L M).obj).X t)).obj
        ((underlyingPresheafComplex X K).X r) ⟶
      (underlyingPresheafComplex X (sheafHomComplex X (sheafHomComplex X K L).obj M).obj).X
        (t + r) := by
  let A := (sheafHomComplex X L M).obj
  let B := K
  let H := sheafHomComplex X (sheafHomComplex X K L).obj M
  refine {
    app := fun U => ModuleCat.ofHom (TensorProduct.lift (evaluationBilinear X t r U))
    naturality := ?_ }
  intro U V f
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro φ k
  change evaluationSection X V.unop t r
      (restrictSection X (A.X t) f.unop φ) (restrictSection X (B.X r) f.unop k) =
    restrictSection X (H.obj.X (t + r)) f.unop (evaluationSection X U.unop t r φ k)
  exact (evaluationSection_restrict X U.unop V.unop f.unop t r φ k).symm

private noncomputable def evaluationFun
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        (n : ℤ) :
    (HomologicalComplex.mapBifunctor
      (underlyingPresheafComplex X (sheafHomComplex X L M).obj) (underlyingPresheafComplex X K)
      (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ)).X n ⟶
    (underlyingPresheafComplex X (sheafHomComplex X (sheafHomComplex X K L).obj M).obj).X n :=
  HomologicalComplex.mapBifunctorDesc fun t r h =>
    match h with
    | rfl => evaluationSummandMap X t r

/-- The value of the degreewise evaluation map of presheaves of modules on a homogeneous pure
tensor of local sections, with the modules of sections of the sheaves as its argument and
result types. -/
private noncomputable abbrev evaluationTensor
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (t r n : ℤ) (h : t + r = n) (U : X.Cᵒᵖ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj U) (k : (K.X r).val.obj U) :
    ((sheafHomComplex X (sheafHomComplex X K L).obj M).obj.X n).val.obj U :=
  (evaluationFun X K L M n).app U
    ((HomologicalComplex.ιMapBifunctor (underlyingPresheafComplex X (sheafHomComplex X L M).obj)
      (underlyingPresheafComplex X K)
          (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
      (ComplexShape.up ℤ) t r n h).app U
        (φ ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] k))

private lemma evaluationSummandMap_tmul
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    (evaluationSummandMap X t r).app (op U)
      (φ ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] k) =
      evaluationSection X U t r φ k := by
  with_unfolding_all rfl

private lemma evaluationFun_tmul
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        (U : X.C)
    (t r n : ℤ) (h : t + r = n)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    (evaluationFun X K L M n).app (op U)
      (((HomologicalComplex.ιMapBifunctor
        (underlyingPresheafComplex X (sheafHomComplex X L M).obj) (underlyingPresheafComplex X K)
        (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
            (ComplexShape.up ℤ)
        t r n h).app (op U))
        (φ ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] k)) =
      h ▸ evaluationSection X U t r φ k := by
  subst n
  change ((HomologicalComplex.ιMapBifunctor
      (underlyingPresheafComplex X (sheafHomComplex X L M).obj) (underlyingPresheafComplex X K)
      (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ)
      t r (t + r) rfl ≫ evaluationFun X K L M (t + r)).app (op U))
      (φ ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] k) =
        evaluationSection X U t r φ k
  rw [evaluationFun, HomologicalComplex.ι_mapBifunctorDesc]
  exact evaluationSummandMap_tmul X U t r φ k

/-- Two local sections of an internal Hom complex that act in the same way on every section
over every object of the slice are equal. -/
lemma homSection_ext
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (H : SheafHomComplex X K L)
    (U : X.C) (n : ℤ) {f g : (H.obj.X n).val.obj (op U)}
    (h : ∀ (p q : ℤ) (hpq : p + n = q) (V : X.C) (i : V ⟶ U)
      (x : (K.X p).val.obj (op V)),
      applyHomSectionOver X H U V i n p q hpq f x =
        applyHomSectionOver X H U V i n p q hpq g x) : f = g := by
  let e := (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) n).mapIso
    (H.sectionsIso U)
  have he : e.hom f = e.hom g := by
    apply Cochain.ext
    intro p q hpq
    ext W x
    exact h p q hpq W.unop.left W.unop.hom x
  exact e.addCommGroupIsoToAddEquiv.injective he

private lemma evaluationSection_natural
    {K K' L L' M M' : CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M') (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (x : (K.X r).val.obj (op U)) :
    evaluationSection X U t r
        (((sheafHomComplexMap X l m).f t).val.app (op U) φ)
        ((k.f r).val.app (op U) x) =
      ((sheafHomComplexMap X (sheafHomComplexMap X k l) m).f (t + r)).val.app (op U)
          (evaluationSection X U t r φ x) := by
  apply homSection_ext
  intro s p hsp V i ψ
  rw [evaluationSection_applyOver X U V i t r s (r + s) p rfl (by omega),
    applyHomSectionOver_sheafHomComplexMap,
    applyHomSectionOver_sheafHomComplexMap,
    evaluationSection_applyOver X U V i t r s (r + s) p rfl (by omega),
    applyHomSection_sheafHomComplexMap]
  rw [map_zsmul_unit]
  congr 5
  exact (PresheafOfModules.naturality_apply (k.f r).val i.op x).symm

private lemma evaluationFun_natural
    {K K' L L' M M' : CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M') (n : ℤ) :
    letI : (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
      SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (HomologicalComplex.mapBifunctorMap
      (((SheafOfModules.forget.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (sheafHomComplexMap X l m))
      (((SheafOfModules.forget.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map k)
      (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ)).f n ≫
        evaluationFun X K' L' M' n =
      evaluationFun X K L M n ≫
        ((sheafHomComplexMap X (sheafHomComplexMap X k l) m).f n).val := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro t r h
  change t + r = n at h
  subst n
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro φ x
  change (evaluationFun X K' L' M' (t + r)).app U
      ((HomologicalComplex.ιMapBifunctor
        (underlyingPresheafComplex X (sheafHomComplex X L' M').obj) (underlyingPresheafComplex X K')
        (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
            (ComplexShape.up ℤ)
        t r (t + r) rfl).app U
        ((((sheafHomComplexMap X l m).f t).val.app U
            (sheafSection X (sheafHomComplex X L M).obj t U φ))
          ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] (k.f r).val.app U
              (sheafSection X K r U x))) =
    ((sheafHomComplexMap X (sheafHomComplexMap X k l) m).f (t + r)).val.app U
      ((evaluationFun X K L M (t + r)).app U
        ((HomologicalComplex.ιMapBifunctor
          (underlyingPresheafComplex X (sheafHomComplex X L M).obj) (underlyingPresheafComplex X K)
          (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
              (ComplexShape.up ℤ)
          t r (t + r) rfl).app U
          (sheafSection X (sheafHomComplex X L M).obj t U φ
            ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
            sheafSection X K r U x)))
  rw [evaluationFun_tmul, evaluationFun_tmul]
  exact evaluationSection_natural X k l m U.unop t r
    (sheafSection X (sheafHomComplex X L M).obj t U φ) (sheafSection X K r U x)

private lemma evaluationSection_cochain
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
        (U : X.C) (t r : ℤ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    moduleCochainOfHomSection X (sheafHomComplex X (sheafHomComplex X K L).obj M)
      U (t + r) (evaluationSection X U t r φ k) = evaluationCochain X U t r φ k :=
  ((HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (t + r)).mapIso
    ((sheafHomComplex X (sheafHomComplex X K L).obj M).sectionsIso U)).inv_hom_id_apply _

private lemma evaluationFun_cochain
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        (U : X.C)
    (t r n : ℤ) (h : t + r = n)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj (op U))
    (k : (K.X r).val.obj (op U)) :
    moduleCochainOfHomSection X (sheafHomComplex X (sheafHomComplex X K L).obj M)
      U n ((evaluationFun X K L M n).app (op U)
      (((HomologicalComplex.ιMapBifunctor
        (underlyingPresheafComplex X (sheafHomComplex X L M).obj) (underlyingPresheafComplex X K)
        (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
            (ComplexShape.up ℤ)
        t r n h).app (op U)) (φ ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj
            (op U)] k))) =
      evaluationCochainAt X U t r n h φ k := by
  subst n
  rw [evaluationFun_tmul]
  exact evaluationSection_cochain X U t r φ k

/-- `evaluationFun_cochain`, read through `evaluationTensor`. -/
private lemma evaluationTensor_cochain
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (t r n : ℤ) (h : t + r = n) (U : X.Cᵒᵖ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj U) (k : (K.X r).val.obj U) :
    moduleCochainOfHomSection X (sheafHomComplex X (sheafHomComplex X K L).obj M)
        U.unop n (evaluationTensor X K L M t r n h U φ k) =
      evaluationCochainAt X U.unop t r n h φ k :=
  evaluationFun_cochain X K L M U.unop t r n h φ k

/-- The degreewise evaluation map is compatible with the differentials on homogeneous pure
tensors, which is the Leibniz rule for evaluation. -/
private lemma evaluationTensor_differential
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        (t r : ℤ) (U : X.Cᵒᵖ)
    (φ : ((sheafHomComplex X L M).obj.X t).val.obj U) (k : (K.X r).val.obj U) :
    ((sheafHomComplex X (sheafHomComplex X K L).obj M).obj.d (t + r) (t + r + 1)).val.app U
        (evaluationTensor X K L M t r (t + r) rfl U φ k) =
      evaluationTensor X K L M (t + 1) r (t + r + 1) (by omega) U
          (((sheafHomComplex X L M).obj.d t (t + 1)).val.app U φ) k +
        (t.negOnePow : ℤ) • evaluationTensor X K L M t (r + 1) (t + r + 1) (by omega) U φ
          ((K.d r (r + 1)).val.app U k) := by
  let H := sheafHomComplex X (sheafHomComplex X K L).obj M
  let e := (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ)
    (t + r + 1)).mapIso (H.sectionsIso U.unop)
  apply e.addCommGroupIsoToAddEquiv.injective
  change moduleCochainOfHomSection X H U.unop (t + r + 1)
      ((H.obj.d (t + r) (t + r + 1)).val.app U
        (evaluationTensor X K L M t r (t + r) rfl U φ k)) =
    moduleCochainOfHomSection X H U.unop (t + r + 1)
      (evaluationTensor X K L M (t + 1) r (t + r + 1) (by omega) U
          (((sheafHomComplex X L M).obj.d t (t + 1)).val.app U φ) k +
        (t.negOnePow : ℤ) • evaluationTensor X K L M t (r + 1) (t + r + 1) (by omega) U φ
          ((K.d r (r + 1)).val.app U k))
  rw [moduleCochainOfHomSection_d, evaluationTensor_cochain, evaluationCochain_differential,
    moduleCochainOfHomSection_add, moduleCochainOfHomSection_zsmul,
    evaluationTensor_cochain, evaluationTensor_cochain]
  rfl

private noncomputable def evaluationPresheaf
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    HomologicalComplex.mapBifunctor
      (underlyingPresheafComplex X (sheafHomComplex X L M).obj) (underlyingPresheafComplex X K)
      (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ) ⟶
      underlyingPresheafComplex X (sheafHomComplex X (sheafHomComplex X K L).obj M).obj where
  f := evaluationFun X K L M
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro t r h
    change t + r = n at h
    subst n
    let A := underlyingPresheafComplex X (sheafHomComplex X L M).obj
    let B := underlyingPresheafComplex X K
    let F := curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    change _ = (HomologicalComplex.ιMapBifunctor A B F (ComplexShape.up ℤ)
      t r (t + r) rfl ≫ (HomologicalComplex.mapBifunctor A B F
        (ComplexShape.up ℤ)).d (t + r) (t + r + 1)) ≫ _
    have hP : HomologicalComplex.ιMapBifunctor A B F (ComplexShape.up ℤ) t r (t + r) rfl ≫
        (HomologicalComplex.mapBifunctor A B F (ComplexShape.up ℤ)).d (t + r) (t + r + 1) =
        (F.map (A.d t (t + 1))).app (B.X r) ≫
            HomologicalComplex.ιMapBifunctor A B F (ComplexShape.up ℤ) (t + 1) r (t + r + 1)
              (by dsimp; omega) +
          t.negOnePow • ((F.obj (A.X t)).map (B.d r (r + 1)) ≫
            HomologicalComplex.ιMapBifunctor A B F (ComplexShape.up ℤ) t (r + 1) (t + r + 1)
              (by dsimp; omega)) := by
      rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
        HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
        HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
          (show (ComplexShape.up ℤ).Rel t (t + 1) from rfl) _ _ (by dsimp; omega),
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
          (show (ComplexShape.up ℤ).Rel r (r + 1) from rfl) _ (by dsimp; omega)]
      simp only [ComplexShape.ε₁, TotalComplexShape.ε₁, one_smul]
      rfl
    rw [hP]
    simp only [Preadditive.add_comp, Units.smul_def, Preadditive.zsmul_comp,
      Category.assoc]
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro φ k
    simp only [PresheafOfModules.add_app, PresheafOfModules.zsmul_app,
      PresheafOfModules.comp_app]
    change ((sheafHomComplex X (sheafHomComplex X K L).obj M).obj.d (t + r)
          (t + r + 1)).val.app U
        (evaluationTensor X K L M t r (t + r) rfl U
          (sheafSection X (sheafHomComplex X L M).obj t U φ) (sheafSection X K r U k)) =
      evaluationTensor X K L M (t + 1) r (t + r + 1) (by omega) U
          (((sheafHomComplex X L M).obj.d t (t + 1)).val.app U
            (sheafSection X (sheafHomComplex X L M).obj t U φ)) (sheafSection X K r U k) +
        (t.negOnePow : ℤ) • evaluationTensor X K L M t (r + 1) (t + r + 1) (by omega) U
          (sheafSection X (sheafHomComplex X L M).obj t U φ)
          ((K.d r (r + 1)).val.app U (sheafSection X K r U k))
    exact evaluationTensor_differential X K L M t r U
      (sheafSection X (sheafHomComplex X L M).obj t U φ) (sheafSection X K r U k)

/-- There is an evaluation morphism for every three complexes of `O`-modules, natural in all
three arguments. -/
theorem exists_natural_evaluation :
    ∃ E : EvaluationConstruction X,
      ∀ {K K' L L' M M' : CochainComplex (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
      (k : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M'),
      tensorTotalMap X (sheafHomComplexMap X l m) k ≫
          E.evaluate K' L' M' = E.evaluate K L M ≫
            sheafHomComplexMap X (sheafHomComplexMap X k l) m := by
  let E : EvaluationConstruction X := {
    evaluate := fun K L M => sheafifyLift X (evaluationPresheaf X K L M)
    evaluate_tmul := by
      intro K L M U t r s a p hra hap φ k ψ
      unfold tensorTotalSection
      rw [sheafifyLift_unit_apply]
      change applyHomSection X _ U (t + r) s p _
        ((evaluationFun X K L M (t + r)).app (op U) _) ψ = _
      rw [evaluationFun_tmul]
      exact evaluationSection_apply X U t r s a p hra hap φ k ψ }
  refine ⟨E, ?_⟩
  intro K K' L L' M M' k l m
  apply HomologicalComplex.hom_ext
  intro n
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv_naturality_right_square _ _ _ _
      (evaluationFun_natural X k l m n)

/-- The canonical evaluation morphism for every three complexes of modules. -/
@[stacks 0A92 "canonical evaluation morphism"]
noncomputable def evaluationConstruction : EvaluationConstruction X :=
  Classical.choose (exists_natural_evaluation X)

/-- The canonical evaluation map from a total tensor complex to an iterated internal Hom. -/
noncomputable abbrev evaluation
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotal X (sheafHomComplex X L M).obj K ⟶
      (sheafHomComplex X (sheafHomComplex X K L).obj M).obj :=
  (evaluationConstruction X).evaluate K L M

/-- Evaluation is natural in `K`, contranatural in `L`, and natural in `M`. -/
@[stacks 0A92 "functoriality in all three complexes"]
theorem evaluation_natural
    {K K' L L' M M' : CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M') :
    tensorTotalMap X (sheafHomComplexMap X l m) k ≫
        evaluation X K' L' M' =
      evaluation X K L M ≫
        sheafHomComplexMap X (sheafHomComplexMap X k l) m :=
  (Classical.choose_spec (exists_natural_evaluation X)) k l m

end Stacks.Cohomology

end
