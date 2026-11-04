module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingIsomorphism
import StacksCore.Tactic.StacksAttribute

/-! # Naturality of the currying isomorphism of internal Hom complexes

Let `(C, O)` be a ringed site. The currying isomorphism of Stacks 0A90,

`SheafHom(K, SheafHom(L, M)) ≅ SheafHom(Tot(K ⊗_O L), M)`,

is constructed in `StacksDraft.Ch21.Sec34.CurryingIsoOfHomComplexes`. This file proves that it
is natural in all three complexes, for the functoriality
`AlgebraicGeometry.RingedSite.homMap` of the internal Hom complex and the functoriality of the
total tensor complex of Stacks 06YM. This is the last part of Stacks 0A90.

## Main results

* `AlgebraicGeometry.RingedSite.ι_tensorComplexMap` and
  `AlgebraicGeometry.RingedSite.tensorComplexMap_tensorComplexSection`: the morphism of total
  tensor complexes induced by `k : K' ⟶ K` and `l : L' ⟶ L` restricted to the `(t, r)` summand,
  and its action on a local pure tensor.
* `AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso_natural`: simultaneous naturality of the
  currying isomorphism.

## Implementation notes

The induced morphism of total tensor complexes is the composite of two
`CategoryTheory.HomologicalComplex.mapBifunctorMap`s, one in each variable, because that is how
`CategoryTheory.Functor.map₂HomologicalComplex` acts on morphisms. Its restriction to a summand
is therefore two applications of `HomologicalComplex.ι_mapBifunctorMap`, each followed by the
removal of an identity; that computation is carried out at the `mapBifunctor` spelling, in which
those lemmas are indexed, and is transported to the `Stacks.SheafOfModules.Tensor.tensorComplex`
  spelling by a
single `exact`, the two being `rfl`-equal but not seen through by the rewriting.

Naturality itself is then checked on local pure tensors, where
`AlgebraicGeometry.RingedSite.homSection_tensor_ext` reduces it to the identity

`m ∘ α(k·) ∘ l· = (m ∘ α ∘ l·)(k·)`

between values of the currying rule, which is two applications of
`AlgebraicGeometry.RingedSite.applyHomSectionOver_homMap`.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u})

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable {K K' L L' M M' :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- `ι` composed with the induced map of total tensor complexes, at the `mapBifunctor`
spelling. -/
private lemma ι_mapBifunctorMap_comp (k : K' ⟶ K) (l : L' ⟶ L) (t r c : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (t, r) = c) :
    HomologicalComplex.ιMapBifunctor K' L' (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)
        t r c h ≫
      ((HomologicalComplex.mapBifunctorMap k (𝟙 L') (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ)).f c ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 K) l (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ)).f c) =
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (k.f t)).app (L'.X r) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (K.X t)).map (l.f r) ≫
        HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) t r c h := by
  simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- `ι` composed with the induced map of total tensor complexes. -/
lemma ι_tensorComplexMap (k : K' ⟶ K) (l : L' ⟶ L) (t r c : ℤ) (htr : t + r = c) :
    HomologicalComplex.ιMapBifunctor K' L' (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)
        t r c (by simpa using htr) ≫
      ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map k).app L' ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).map l).f c) =
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (k.f t)).app (L'.X r) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (K.X t)).map (l.f r) ≫
        HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) t r c (by simpa using htr) :=
  ι_mapBifunctorMap_comp X k l t r c (by simpa using htr)


/-- The induced map of total tensor complexes sends a local pure tensor to the local pure
tensor of the images. -/
lemma tensorComplexMap_tensorComplexSection (k : K' ⟶ K) (l : L' ⟶ L) (t r c : ℤ)
    (htr : t + r = c) {W : X.C} (k₀ : (K'.X t).val.obj (op W))
    (l₀ : (L'.X r).val.obj (op W)) :
    ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map k).app L' ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).map l).f c).val.app (op W)
        (tensorComplexSection X t r c htr k₀ l₀) =
      tensorComplexSection X t r c htr ((k.f t).val.app (op W) k₀)
        ((l.f r).val.app (op W) l₀) := by
  have hA := sheafification_map_unit_apply X ((k.f t).val ▷ (L'.X r).val) (op W)
    (k₀ ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l₀)
  have hB := sheafification_map_unit_apply X ((K.X t).val ◁ (l.f r).val) (op W)
    ((k.f t).val.app (op W) k₀ ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l₀)
  refine (congrArg (fun φ : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (K'.X t)).obj (L'.X
    r) ⟶
      ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L).X c) ↦ φ.val.app (op W)
      (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        ((K'.X t).val ⊗ (L'.X r).val)).app (op W)
          (k₀ ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l₀)))
    (ι_tensorComplexMap X k l t r c htr)).trans ?_
  refine (congrArg (fun y : (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (K.X t)).obj (L'.X
    r)).val.obj
      (op W) ↦ (HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ) t r c (by simpa using htr)).val.app (op W)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (K.X t)).map (l.f r)).val.app (op W)
          y)) hA).trans ?_
  exact congrArg (fun y : (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (K.X t)).obj (L.X
    r)).val.obj
      (op W) ↦ (HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ) t r c (by simpa using htr)).val.app (op W) y) hB


/-- **Stacks 0A90.** The currying isomorphism is natural in all three complexes. -/
lemma sheafHomTensorCurryIso_natural (k : K' ⟶ K) (l : L' ⟶ L) (m : M ⟶ M') :
    homMap X k (homMap X l m) ≫ (sheafHomTensorCurryIso X K' L' M').hom =
      (sheafHomTensorCurryIso X K L M).hom ≫
        homMap X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map k).app L' ≫
          ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).map l) m := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨V⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, comp_val_app_apply',
    comp_val_app_apply', sheafHomTensorCurryIso_hom_f, sheafHomTensorCurryIso_hom_f,
    curryHom_app, curryHom_app]
  refine homSection_tensor_ext X V fun c d hcd t r htr W g k₀ l₀ ↦ ?_
  rw [applyHomSectionOver_curryFun, applyHomSectionOver_homMap,
    tensorComplexMap_tensorComplexSection, applyHomSectionOver_curryFun,
    ← curryRule_degree X V (((homMap X k (homMap X l m)).f n).val.app (op V) a) t r d (t + n)
      rfl (by omega) g k₀ l₀,
    applyHomSectionOver_homMap, applyHomSection_homMap,
    curryRule_degree X V a t r d (t + n) rfl (by omega) g ((k.f t).val.app (op W) k₀)
      ((l.f r).val.app (op W) l₀)]

end AlgebraicGeometry.RingedSite
end
