module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ModuleLowerShriekAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleBicomplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.SectionCocontinuous

/-!
# Evaluation on a fibrewise point resolution and sheafification

In the situation of
`StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleBasic`, each
functor `V ↦ A_{n,V}` lies over the identity of the base, so it is cocontinuous from the base to
the inherited topology of the total category. Consequently the evaluation
`G ↦ (V ↦ G(A_{n,V}))` of presheaves of modules carries maps inverted by sheafification on the
total category to maps inverted by sheafification on the base: the complex of sheaves of a
fibrewise point resolution of a sheaf `F` (Stacks 08VB) may be computed from any presheaf whose
sheafification is `F`.

## Main results

* `Stacks.Sites.FibredCategory.FibredCategorySituation.isCocontinuous_pointLevel`: `V ↦ A_{n,V}`
  is cocontinuous.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.W_toPresheaf_modulePointLevel_map`: the
  evaluation `G ↦ (V ↦ G(A_{n,V}))` preserves maps inverted by sheafification.

## References

* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
-/

@[expose] public section

open CategoryTheory

universe uD vD uC vC w

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  {A : s.base.C ⥤ CosimplicialObject s.C}
  (hA : A ⋙ (Functor.whiskeringRight SimplexCategory s.C s.base.C).obj s.p =
    Functor.const SimplexCategory)
  (O : s.base.Cᵒᵖ ⥤ RingCat.{max w uD vD uC vC})

include hA in
/-- **`V ↦ A_{n,V}` is cocontinuous** from the base to the topology the total category inherits:
it lies over the identity of the base. -/
theorem isCocontinuous_pointLevel (n : SimplexCategory) :
    (pointLevel s A n).IsCocontinuous s.base.J s.topology :=
  Functor.isCocontinuous_of_isHomLift s.p s.base.J (pointLevel s A n)
    (fun V => obj_obj_proj s hA V n) (fun g => isHomLift_map_app s hA g n)

/-- **Evaluation on `A_{n,•}` preserves maps inverted by sheafification**: if a map of presheaves
of `p⁻¹O`-modules on the total category is inverted by sheafification on underlying abelian
presheaves, so is the induced map `V ↦ G(A_{n,V}) ⟶ V ↦ G'(A_{n,V})` on the base. -/
theorem W_toPresheaf_modulePointLevel_map (n : SimplexCategory)
    {G G' : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)} (φ : G ⟶ G')
    (hφ : s.topology.W ((PresheafOfModules.toPresheaf _).map φ)) :
    s.base.J.W ((PresheafOfModules.toPresheaf O).map ((modulePointLevel s hA O n).map φ)) :=
  have := isCocontinuous_pointLevel s hA n
  Presheaf.W_whiskerLeft_of_isCocontinuous (pointLevel s A n) hφ

/-- **The complex of sheaves of a fibrewise point resolution may be computed from a presheaf**:
a map of presheaves of `p⁻¹O`-modules on the total category which is inverted by sheafification
induces an isomorphism of the sheafified complexes `V ↦ G(A_{•,V})`. -/
theorem isIso_sheafification_map_modulePointMooreCochain_map
    (R : Sheaf s.base.J RingCat.{max w uD vD uC vC})
    {G G' : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ R.obj)} (φ : G ⟶ G')
    (hφ : s.topology.W ((PresheafOfModules.toPresheaf _).map φ)) :
    IsIso (((PresheafOfModules.sheafification (𝟙 R.obj)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((modulePointMooreCochain s hA R.obj).map φ)) := by
  have key : ∀ {P Q : PresheafOfModules.{max w uD vD uC vC} R.obj} (g : P ⟶ Q),
      s.base.J.W ((PresheafOfModules.toPresheaf _).map g) →
        IsIso ((PresheafOfModules.sheafification (𝟙 R.obj)).map g) := fun g hg => by
    have e := PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (J := s.base.J) (𝟙 R.obj)
    have h' : ((MorphismProperty.isomorphisms _).inverseImage
        (PresheafOfModules.sheafification (𝟙 R.obj))) g := e ▸ hg
    exact h'
  suffices ∀ j, IsIso ((((PresheafOfModules.sheafification (𝟙 R.obj)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((modulePointMooreCochain s hA R.obj).map φ)).f j) from
    HomologicalComplex.Hom.isIso_of_components _
  intro j
  by_cases hj : 0 < j
  · have h0 := isZero_modulePointMooreCochain_X s hA R.obj G j hj
    have h1 := isZero_modulePointMooreCochain_X s hA R.obj G' j hj
    exact Limits.isIso_of_source_target_iso_zero _
      ((PresheafOfModules.sheafification (𝟙 R.obj)).map_isZero h0).isoZero
      ((PresheafOfModules.sheafification (𝟙 R.obj)).map_isZero h1).isoZero
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
    refine key _ ?_
    have hf : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
    rw [show ((modulePointMooreCochain s hA R.obj).map φ).f (-(n : ℤ)) =
        (HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) hf).hom ≫
          ((modulePointLevel s hA R.obj (SimplexCategory.mk n)).map φ) ≫
            (HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) hf).inv from
      HomologicalComplex.extendMap_f _ _ hf]
    refine (congrArg (fun g => s.base.J.W g) (((PresheafOfModules.toPresheaf R.obj).map_comp _
      _).trans (congrArg (_ ≫ ·) ((PresheafOfModules.toPresheaf R.obj).map_comp _ _)))).mpr ?_
    refine MorphismProperty.comp_mem _ _ _ (ObjectProperty.isLocal_of_isIso _
      ((PresheafOfModules.toPresheaf R.obj).mapIso (HomologicalComplex.extendXIso
        ((modulePointMooreComplex s hA R.obj).obj G) _ hf)).hom) ?_
    exact MorphismProperty.comp_mem _ _ _
      (W_toPresheaf_modulePointLevel_map s hA R.obj _ φ hφ) (ObjectProperty.isLocal_of_isIso _
        ((PresheafOfModules.toPresheaf R.obj).mapIso (HomologicalComplex.extendXIso
          ((modulePointMooreComplex s hA R.obj).obj G') _ hf)).inv)

end Stacks.Sites.FibredCategory.FibredCategorySituation
