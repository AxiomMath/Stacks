module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingUnitLaw
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.UnitRightFactorCollapse

/-!
# The unit law of the currying isomorphism at a structure-sheaf tensor factor

Let `(C, O)` be a ringed site and let `A` and `M` be complexes of `O`-modules. The currying
isomorphism of **Stacks 0A90**

`SheafHom(K, SheafHom(L, M)) ≅ SheafHom(Tot(K ⊗_O L), M)`

is read here at `L = O[0]`, where the inner internal Hom of its source collapses by evaluation at
the unit section (`AlgebraicGeometry.RingedSite.structureSheafHomIso` of Tag 0A91) and its target
collapses by the right unit isomorphism `Tot(A ⊗_O O[0]) ≅ A` of Tag 0FNG
(`AlgebraicGeometry.RingedSite.structureSheafComplexTensorRightIso`). The two collapses agree:

`SheafHom(1_A, structureSheafHomIso⁻¹) ≫ curry = SheafHom(ρ_ A, 1_M)`.

## Main results

* `AlgebraicGeometry.RingedSite.curryFun_homMap_structureSheafHomIso_inv`: the unit law on local
  sections.
* `AlgebraicGeometry.RingedSite.homMap_structureSheafHomIso_inv_comp_sheafHomTensorCurryIso'` and
  `AlgebraicGeometry.RingedSite.homMap_structureSheafHomIso_inv_comp_sheafHomTensorCurryIso`: the
  unit law as an equality of morphisms of complexes, at the
  `Stacks.SheafOfModules.Tensor.tensorComplex` spelling of the collapse and then with the
  collapse spelled `ρ_ A`.

## Implementation notes

The right unit collapse has two spellings, `ρ_ A` of `CochainComplex.symmetricCategory` and
`structureSheafComplexTensorRightIso` at the `Stacks.SheafOfModules.Tensor.tensorComplex`
spelling. They are `rfl`, but a goal mentioning both is not type-correct at `implicit`
transparency, so the elementwise computation is at the `tensorComplex` spelling and the two are
crossed once at the end.

A degree-zero section of the structure sheaf complex and a section of the structure sheaf are
definitionally the same, but only the latter is found by instance search as a scalar, so the
section is renamed into a scalar by an `obtain` rather than by a type ascription.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (A M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The right unit collapse sends the local pure tensor of `a` with the unit section to `a`, at
the `Stacks.SheafOfModules.Tensor.tensorComplex` spelling of the total tensor complex. -/
private lemma structureSheafComplexTensorRightIso_hom_f_val_app_one (c : ℤ) (W : X.C)
    (a : (A.X c).val.obj (op W)) :
    ((structureSheafComplexTensorRightIso X A).hom.f c).val.app (op W)
        (tensorComplexSection X c 0 c (add_zero c) a (structureSheafOne X W)) = a :=
  rightUnitor_hom_f_val_app_one X A c W a

/-- The unit law of the currying isomorphism at a structure-sheaf tensor factor, on local
sections. -/
lemma curryFun_homMap_structureSheafHomIso_inv (n : ℤ) (U : X.C)
    (s : ((sheafHomComplex X A M).obj.X n).val.obj (op U)) :
    curryFun X U
        (((homMap X (𝟙 A) (structureSheafHomIso X M).inv).f n).val.app (op U) s) =
      ((homMap X (structureSheafComplexTensorRightIso X A).hom (𝟙 M)).f n).val.app (op U) s := by
  refine homSection_tensor_ext X U fun c d hcd t r htr W g a k ↦ ?_
  rcases eq_or_ne r 0 with rfl | hr
  · obtain rfl : c = t := by omega
    subst hcd
    -- read the degree-zero section of the structure sheaf as a scalar
    obtain ⟨k, rfl⟩ : ∃ k' : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W),
        (k' : ((structureSheafComplex X).X 0).val.obj (op W)) = k := ⟨k, rfl⟩
    have hks : (k • structureSheafOne X W :
        ((structureSheafComplex X).X 0).val.obj (op W)) = k := by
      change k * 1 = k
      exact mul_one _
    rw [← hks, tensorComplexSection_smul_right, applyHomSectionOver_smul_right,
      applyHomSectionOver_smul_right, applyHomSectionOver_curryFun,
      ← curryRule_degree X U _ c 0 (c + n) (c + n) rfl (by omega) g a (structureSheafOne X W),
      applyHomSectionOver_homMap, id_f_val_app_apply,
      applyHomSection_structureSheafHomIso_inv, applyHomSectionOver_homMap,
      structureSheafComplexTensorRightIso_hom_f_val_app_one, id_f_val_app_apply]
  · rw [structureSheafComplex_section_eq_zero X W hr k]
    have h0 : tensorComplexSection X (K := A) (L := structureSheafComplex X) t r c htr a 0 = 0 := by
      have h := tensorComplexSection_smul_right X t r c htr
        (0 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) a
        (0 : ((structureSheafComplex X).X r).val.obj (op W))
      rwa [zero_smul, zero_smul] at h
    rw [h0]
    exact (map_zero _).trans (map_zero _).symm

/-- The unit law of the currying isomorphism at a structure-sheaf tensor factor, at the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling of the right unit collapse. -/
theorem homMap_structureSheafHomIso_inv_comp_sheafHomTensorCurryIso' :
    homMap X (𝟙 A) (structureSheafHomIso X M).inv ≫
        (sheafHomTensorCurryIso X A (structureSheafComplex X) M).hom =
      homMap X (structureSheafComplexTensorRightIso X A).hom (𝟙 M) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_))
  exact curryFun_homMap_structureSheafHomIso_inv X A M n V.unop s

/-- The right unit law of the currying isomorphism: currying a section of `SheafHom(A, M)`, read
as a section of `SheafHom(A, SheafHom(O[0], M))` by the identification of Tag 0A91, is
precomposition with the right unit collapse `ρ_ A : Tot(A ⊗_O O[0]) ≅ A`. -/
theorem homMap_structureSheafHomIso_inv_comp_sheafHomTensorCurryIso :
    homMap X (𝟙 A) (structureSheafHomIso X M).inv ≫
        (sheafHomTensorCurryIso X A (structureSheafComplex X) M).hom =
      homMap X (ρ_ A).hom (𝟙 M) :=
  homMap_structureSheafHomIso_inv_comp_sheafHomTensorCurryIso' X A M

end AlgebraicGeometry.RingedSite

end
