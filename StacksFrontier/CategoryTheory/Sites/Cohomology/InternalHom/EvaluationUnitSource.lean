module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorTotalUnitRightFactor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeUnitSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeUnitTensorFactor

/-!
# The evaluation morphism of Stacks 0A92 at a trivialised single-degree source

Let `X` be a ringed site, let `E` be a cochain complex of `O`-modules vanishing outside a single
degree `k` and with `E^k ≅ O`, and let `I`, `I'` be arbitrary cochain complexes of `O`-modules.
The evaluation morphism of Stacks 0A92

`Tot(SheafHom(I, I') ⊗_O E) ⟶ SheafHom(SheafHom(E, I), I')`

is then an **isomorphism**.

## Implementation notes

The degree of the inner internal Hom is `a - k` where `a` is the degree at which the outer
Hom-section is read, and the two spellings `a - k` and `s` with `k + s = a` are not
interchangeable inside a type. Both of the degree variables therefore appear explicitly
throughout, joined by an equation.

## Main definitions

* `AlgebraicGeometry.RingedSite.unitSourceHomIso`: evaluation at the trivialising section, as an
  isomorphism `SheafHom(E, I)^s ≅ I^a` for any `a` with `k + s = a`.

## Main results

* `AlgebraicGeometry.RingedSite.applyHomSectionOver_evaluationMap_unitRightFactor`: the
  component of the evaluation morphism, read on a section of the collapsed source, evaluates by
  the inner evaluation at the trivialising section, with a Koszul sign.
* `AlgebraicGeometry.RingedSite.isIso_evaluationMap_of_unitSource`: the evaluation morphism of
  Stacks 0A92 is an isomorphism at a trivialised single-degree source.

## References

* [Stacks Project, Lemma 20.49.6 (Tag 0A92)](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Lemma 20.49.5 (Tag 08JH)](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Lemma 36.10.12 (Tag 08JJ)](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u} X.O) (ComplexShape.up ℤ)]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
  HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- A morphism restricted to a slice site acts on the sections over an object of that slice
presented as `Over.mk i` by the original morphism's action on the sections over the source of
`i`. -/
private lemma over_val_app_mk
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : A ⟶ B) {V W : X.C}
    (i : W ⟶ V) (x : A.val.obj (op W)) :
    (φ.over V).val.app (op (Over.mk i)) x = φ.val.app (op W) x := rfl

variable {E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  (k : ℤ) (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (hE : ∀ p, p ≠ k → IsZero (E.X p))
  (I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **Evaluation at the trivialising section, with the degree of the target given
independently.** This is `AlgebraicGeometry.RingedSite.homUnitEvaluationIso` with the degree of
`I` supplied as a variable `a` together with `k + s = a` rather than computed as `k + s`. -/
def unitSourceHomIso (s a : ℤ) (h : k + s = a) :
    (sheafHomComplex X E I).obj.X s ≅ I.X a :=
  homUnitEvaluationIso X k s e hE ≪≫ I.XIsoOfEq h

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
  HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- `AlgebraicGeometry.RingedSite.unitSourceHomIso` sends a section `ψ` of `SheafHom(E, I)` to
its value at the trivialising section of `E`. -/
lemma unitSourceHomIso_hom_apply (s a : ℤ) (h : k + s = a) (W : X.C)
    (ψ : ((sheafHomComplex X E I).obj.X s).val.obj (op W)) :
    (unitSourceHomIso X k e hE I s a h).hom.val.app (op W) ψ =
      applyHomSection X (sheafHomComplex X E I) W s k a h ψ
        (e.inv.val.app (op W)
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W))) := by
  subst h
  have hid : (unitSourceHomIso X k e hE I s (k + s) rfl).hom =
      homUnitEvaluation X (F := I) k s e := Category.comp_id _
  rw [hid]
  exact homUnitEvaluation_val_app X k s e W ψ

/-- Evaluating the component of the evaluation morphism of Stacks 0A92 at a section coming from
the collapse of the source, on a section `ψ` of `SheafHom(E, I)`, gives the evaluation of the
original section on the value of `ψ` at the trivialising section of `E`, up to the Koszul sign
`(-1)^{k + (-a)k}`. -/
theorem applyHomSectionOver_evaluationMap_unitRightFactor
    (m c : ℤ) (hc : m + k = c) (V W : X.C) (i : W ⟶ V) (s a p : ℤ)
    (hka : k + s = a) (hap : a + m = p)
    (φ : ((sheafHomComplex X I I').obj.X m).val.obj (op V))
    (ψ : ((sheafHomComplex X E I).obj.X s).val.obj (op W)) :
    applyHomSectionOver X (sheafHomComplex X (sheafHomComplex X E I).obj I') V W i c s p
        (by omega)
        (((evaluationMap X E I I').f c).val.app (op V)
          ((unitRightFactorIsoAt X k e hE m c hc).hom.val.app (op V) φ)) ψ =
      (k + (-a) * k).negOnePow •
        applyHomSectionOver X (sheafHomComplex X I I') V W i m a p hap φ
          ((unitSourceHomIso X k e hE I s a hka).hom.val.app (op W) ψ) := by
  subst hc
  refine Eq.trans (congrArg (fun z =>
    applyHomSectionOver X (sheafHomComplex X (sheafHomComplex X E I).obj I') V W i (m + k) s p
      (by omega) z ψ)
    ((congrArg (fun y => ((evaluationMap X E I I').f (m + k)).val.app (op V) y)
        (unitRightFactorIsoAt_hom_apply X k e hE m (m + k) rfl V φ)).trans
      (evaluationMap_tensorTotalSection X E I I' V m k φ
        (e.inv.val.app (op V) (1 : (ringSheaf X.O).obj.obj (op V)))))) ?_
  refine Eq.trans (evaluationSection_applyOver X V W i m k s a p hka hap φ
    (e.inv.val.app (op V) (1 : (ringSheaf X.O).obj.obj (op V))) ψ) ?_
  refine congrArg (fun z => (k + (-a) * k).negOnePow •
    applyHomSectionOver X (sheafHomComplex X I I') V W i m a p hap φ z) ?_
  refine Eq.trans (congrArg
    (fun y => applyHomSection X (sheafHomComplex X E I) W s k a hka ψ y)
    (restrictSection_unitSection X k e i)) ?_
  exact (unitSourceHomIso_hom_apply X k e hE I s a hka W ψ).symm

/-- The component of the evaluation morphism on the collapsed source is injective on
sections. -/
private lemma injective_evaluationMap_unitRightFactor (m c : ℤ) (hc : m + k = c) (V : X.Cᵒᵖ) :
    Function.Injective (((unitRightFactorIsoAt X k e hE m c hc).hom ≫
      (evaluationMap X E I I').f c).val.app V) := by
  intro φ φ' hφ
  refine homSection_ext X (sheafHomComplex X I I') V.unop m (fun a q haq W i x => ?_)
  obtain ⟨ψ, hψ⟩ : ∃ ψ, (unitSourceHomIso X k e hE I (a - k) a (by omega)).hom.val.app (op W) ψ
      = x :=
    (bijective_val_app_of_iso X (unitSourceHomIso X k e hE I (a - k) a (by omega)) (op W)).2 x
  have hev := congrArg (fun z =>
    applyHomSectionOver X (sheafHomComplex X (sheafHomComplex X E I).obj I') V.unop W i c
      (a - k) q (by omega) z ψ) hφ
  rw [comp_val_app_apply', comp_val_app_apply'] at hev
  rw [applyHomSectionOver_evaluationMap_unitRightFactor X k e hE I I' m c hc V.unop W i
      (a - k) a q (by omega) (by omega) φ ψ,
    applyHomSectionOver_evaluationMap_unitRightFactor X k e hE I I' m c hc V.unop W i
      (a - k) a q (by omega) (by omega) φ' ψ, hψ] at hev
  exact MulAction.injective _ hev

/-- The component of the evaluation morphism on the collapsed source is surjective on
sections. -/
private lemma surjective_evaluationMap_unitRightFactor (m c : ℤ) (hc : m + k = c) (V : X.Cᵒᵖ) :
    Function.Surjective (((unitRightFactorIsoAt X k e hE m c hc).hom ≫
      (evaluationMap X E I I').f c).val.app V) := by
  intro t
  refine ⟨((sheafHomComplex X I I').sectionsEquiv V.unop m).symm
    (Cochain.mk (fun a q haq =>
      (k + (-a) * k).negOnePow •
        ((unitSourceHomIso X k e hE I (a - k) a (by omega)).inv.over V.unop ≫
          (((sheafHomComplex X (sheafHomComplex X E I).obj I').sectionsEquiv V.unop c t).v
            (a - k) q (by omega))))), ?_⟩
  refine homSection_ext X (sheafHomComplex X (sheafHomComplex X E I).obj I') V.unop c
    (fun s p hsp W i ψ => ?_)
  obtain ⟨a, rfl⟩ : ∃ a, s = a - k := ⟨k + s, by omega⟩
  rw [comp_val_app_apply',
    applyHomSectionOver_evaluationMap_unitRightFactor X k e hE I I' m c hc V.unop W i
      (a - k) a p (by omega) (by omega) _ ψ]
  have hfam : applyHomSectionOver X (sheafHomComplex X I I') V.unop W i m a p (by omega)
      (((sheafHomComplex X I I').sectionsEquiv V.unop m).symm
        (Cochain.mk (fun a' q' (_ : a' + m = q') =>
          (k + (-a') * k).negOnePow •
            ((unitSourceHomIso X k e hE I (a' - k) a' (by omega)).inv.over V.unop ≫
              (((sheafHomComplex X (sheafHomComplex X E I).obj I').sectionsEquiv V.unop c t).v
                (a' - k) q' (by omega))))))
        ((unitSourceHomIso X k e hE I (a - k) a (by omega)).hom.val.app (op W) ψ) =
      (k + (-a) * k).negOnePow •
        applyHomSectionOver X (sheafHomComplex X (sheafHomComplex X E I).obj I') V.unop W i c
          (a - k) p hsp t ψ := by
    refine Eq.trans (congrArg
      (fun z : Cochain (restrictComplex X I V.unop) (restrictComplex X I' V.unop) m =>
        (z.v a p (by omega)).val.app (op (Over.mk i))
          ((unitSourceHomIso X k e hE I (a - k) a (by omega)).hom.val.app (op W) ψ))
      (((sheafHomComplex X I I').sectionsEquiv V.unop m).apply_symm_apply
        (Cochain.mk (fun a' q' (_ : a' + m = q') =>
          (k + (-a') * k).negOnePow •
            ((unitSourceHomIso X k e hE I (a' - k) a' (by omega)).inv.over V.unop ≫
              (((sheafHomComplex X (sheafHomComplex X E I).obj I').sectionsEquiv V.unop c t).v
                (a' - k) q' (by omega))))))) ?_
    refine Eq.trans (units_zsmul_val_app_apply X _ ((k + (-a) * k).negOnePow)
      (op (Over.mk i)) _) ?_
    refine congrArg (fun z => (k + (-a) * k).negOnePow •
      (((((sheafHomComplex X (sheafHomComplex X E I).obj I').sectionsEquiv V.unop c t).v
        (a - k) p (by omega))).val.app (op (Over.mk i)) z)) ?_
    refine Eq.trans (over_val_app_mk X
      (unitSourceHomIso X k e hE I (a - k) a (by omega)).inv i _) ?_
    exact congrArg (fun φ : (sheafHomComplex X E I).obj.X (a - k) ⟶
        (sheafHomComplex X E I).obj.X (a - k) => φ.val.app (op W) ψ)
      (unitSourceHomIso X k e hE I (a - k) a (by omega)).hom_inv_id
  rw [hfam, smul_smul, Int.units_mul_self, one_smul]

include e hE in
/-- **The evaluation morphism of Stacks 0A92 is an isomorphism when the source of the inner
internal Hom is concentrated in one degree and trivialised there.** If `E` vanishes outside
degree `k` and `E^k ≅ O`, then

`Tot(SheafHom(I, I') ⊗_O E) ⟶ SheafHom(SheafHom(E, I), I')`

is an isomorphism, for arbitrary `I` and `I'`. -/
theorem isIso_evaluationMap_of_unitSource : IsIso (evaluationMap X E I I') := by
  have hn : ∀ n, IsIso ((evaluationMap X E I I').f n) := by
    intro n
    have : IsIso ((unitRightFactorIsoAt X k e hE (n - k) n (by omega)).hom ≫
        (evaluationMap X E I I').f n) :=
      Stacks.SheafOfModules.isIso_of_bijective_app _ (fun V =>
        ⟨injective_evaluationMap_unitRightFactor X k e hE I I' (n - k) n (by omega) V,
          surjective_evaluationMap_unitRightFactor X k e hE I I' (n - k) n (by omega) V⟩)
    exact IsIso.of_isIso_comp_left (unitRightFactorIsoAt X k e hE (n - k) n _).hom _
  exact HomologicalComplex.Hom.isIso_of_components _

end AlgebraicGeometry.RingedSite

end
