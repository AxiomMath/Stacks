module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.UncurryingOfMorphisms
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.AssociatorSections
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparisonSections

/-!
# Uncurrying the interchange morphism

Let `(C, O)` be a ringed site, `A`, `F`, `B`, `I` complexes of `O`-modules and
`s : F ⟶ SheafHom(B, I)` a morphism of complexes. The interchange morphism of Stacks 0BYT,
precomposed with `Tot(A ⊗ s)`, is a morphism `Tot(A ⊗_O F) ⟶ SheafHom(B, Tot(A ⊗_O I))`. Its
uncurrying (Stacks 0A90) is the associator followed by `Tot(A ⊗ ev_s)`, where
`ev_s : Tot(F ⊗_O B) ⟶ I` is the uncurrying of `s`: on local pure tensors both send
`(a ⊗ x) ⊗ b` to `a ⊗ s(x)(b)`.

## Main results

* `AlgebraicGeometry.RingedSite.curryMap_uncurryMap`: currying inverts uncurrying.
* `AlgebraicGeometry.RingedSite.uncurryMap_f_tensorComplexSection_eq`: the uncurrying of `f`
  sends `k ⊗ l` to `f(k)(l)`.
* `AlgebraicGeometry.RingedSite.uncurryMap_tensorHomInterchange`: the identity above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable
  {A B M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **Currying inverts uncurrying.** -/
theorem curryMap_uncurryMap (f : A ⟶ (sheafHomComplex X B M).obj) :
    curryMap X (uncurryMap X f) = f := by
  apply globalHomSection_injective X
  rw [curryMap, globalHomSection_homOfGlobalCocycle]
  dsimp only [curryGlobalSection, uncurryMap]
  rw [globalHomSection_homOfGlobalCocycle]
  dsimp only [uncurryGlobalSection]
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ConcreteCategory.id_apply]

/-- **The uncurrying on a local pure tensor**, read as an evaluation: `k ⊗ l ↦ f(k)(l)`. -/
theorem uncurryMap_f_tensorComplexSection_eq (f : A ⟶ (sheafHomComplex X B M).obj)
    (t r d : ℤ) (hrd : r + t = d) (htr : t + r = d) (W : X.C) (k : (A.X t).val.obj (op W))
    (l : (B.X r).val.obj (op W)) :
    ((uncurryMap X f).f d).val.app (op W) (tensorComplexSection X t r d htr k l) =
      applyHomSection X (sheafHomComplex X B M) W t r d hrd ((f.f t).val.app (op W) k) l := by
  have h := curryMap_apply X (uncurryMap X f) t r d hrd W k l
  rw [curryMap_uncurryMap] at h
  exact h.symm

/-- The map of total tensor complexes induced by a map in the second variable, on a local pure
tensor. -/
theorem tensorComplex_obj_map_tensorComplexSection
    {K L L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (l : L' ⟶ L) (t r c : ℤ) (htr : t + r = c) {W : X.C} (k₀ : (K.X t).val.obj (op W))
    (l₀ : (L'.X r).val.obj (op W)) :
    ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).map l).f c).val.app (op W)
        (tensorComplexSection X t r c htr k₀ l₀) =
      tensorComplexSection X t r c htr k₀ ((l.f r).val.app (op W) l₀) := by
  have h := tensorComplexMap_tensorComplexSection X (𝟙 K) l t r c htr k₀ l₀
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ConcreteCategory.id_apply] at h
  exact h

/-- **The uncurrying of the interchange morphism.** For `s : F ⟶ SheafHom(B, I)` and any
`q : Tot(A ⊗_O I) ⟶ J`, the uncurrying of `Tot(A ⊗ s) ≫ (interchange) ≫ SheafHom(B, q)` is the
associator followed by `Tot(A ⊗ ev_s)` and `q`, where `ev_s` is the uncurrying of `s`. -/
theorem uncurryMap_tensorHomInterchange
    {A F B I J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (s : F ⟶ (sheafHomComplex X B I).obj) (q : tensorTotal X A I ⟶ J) :
    uncurryMap X ((tensorTotalIsoTensorComplex X A F).inv ≫ tensorTotalMap X (𝟙 A) s ≫
        tensorHomInterchange X A I B ≫ homMap X (𝟙 B) q) =
      (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator A F B).hom ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (uncurryMap X s) ≫
        (tensorTotalIsoTensorComplex X A I).inv ≫ q := by
  suffices h : curryMap X
      ((Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator A F B).hom ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (uncurryMap X s) ≫
        (tensorTotalIsoTensorComplex X A I).inv ≫ q) =
      (tensorTotalIsoTensorComplex X A F).inv ≫ tensorTotalMap X (𝟙 A) s ≫
        tensorHomInterchange X A I B ≫ homMap X (𝟙 B) q by
    rw [← h, uncurryMap_curryMap]
  rw [← cancel_epi (tensorTotalIsoTensorComplex X A F).hom, Iso.hom_inv_id_assoc]
  refine tensorTotalHomSection_ext X fun U V i t r a d had x y z => ?_
  have hR : applyHomSectionOver X (sheafHomComplex X B J) U V i (t + r) a d had
      (((tensorTotalMap X (𝟙 A) s ≫ tensorHomInterchange X A I B ≫ homMap X (𝟙 B) q).f
        (t + r)).val.app (op U) (tensorTotalSection X A F U t r x y)) z =
      (q.f d).val.app (op V) (tensorTotalSectionAt X A I V t (a + r) d (by omega)
        (restrictSection X i x) (applyHomSection X (sheafHomComplex X B I) V r a (a + r) rfl
          ((s.f r).val.app (op V) (restrictSection X i y)) z)) := by
    simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ConcreteCategory.comp_apply]
    rw [tensorTotalMap_tensorTotalSection, applyHomSectionOver_homMap,
      tensorHomInterchange_applyHomSectionOver X A I B U V i t r a (a + r) d rfl (by omega)]
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
      ConcreteCategory.id_apply]
    rw [applyHomSectionOver_map_apply (Y := X) s U V i r a (a + r) rfl]
  rw [hR]
  have hTot : ((tensorTotalIsoTensorComplex X A F).hom.f (t + r)).val.app (op U)
      (tensorTotalSection X A F U t r x y) = tensorComplexSection X t r (t + r) rfl x y := by
    rw [← tensorTotalSectionAt_self, ← tensorTotalIsoTensorComplex_inv_tensorComplexSection]
    exact Stacks.SheafOfModules.hom_val_app_inv_val_app
      (HomologicalComplex.Hom.isoApp (tensorTotalIsoTensorComplex X A F) (t + r)) (op U) _
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply]
  rw [hTot, applyHomSectionOver_map_apply (Y := X) _ U V i (t + r) a d had,
    ← tensorComplexSection_restrict, curryMap_apply X _ (t + r) a d had V]
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply]
  refine (congrArg (fun w => ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map
      (uncurryMap X s) ≫
        (tensorTotalIsoTensorComplex X A I).inv ≫ q).f d).val.app (op V) w)
    (tensorComplexAssociator_hom_tensorComplexSection X t r a (t + r) (a + r) d rfl (by omega)
      (by omega) (by omega) _ _ _)).trans ?_
  refine (congrArg (fun w => (((tensorTotalIsoTensorComplex X A I).inv ≫ q).f d).val.app (op V) w)
    (tensorComplex_obj_map_tensorComplexSection X (uncurryMap X s) t (a + r) d (by omega)
      (restrictSection X i x)
      (tensorComplexSection X r a (a + r) (by omega) (restrictSection X i y) z))).trans ?_
  refine (congrArg (fun w => (((tensorTotalIsoTensorComplex X A I).inv ≫ q).f d).val.app (op V)
      (tensorComplexSection X t (a + r) d (by omega) (restrictSection X i x) w))
    (uncurryMap_f_tensorComplexSection_eq X s r a (a + r) rfl (by omega) V
      (restrictSection X i y) z)).trans ?_
  exact congrArg (fun w => (q.f d).val.app (op V) w)
    (tensorTotalIsoTensorComplex_inv_tensorComplexSection X A I V t (a + r) d (by omega)
      (restrictSection X i x) _)

end AlgebraicGeometry.RingedSite

end
