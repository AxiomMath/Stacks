module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.UnitLeftFactorCollapse

/-!
# The unit law of the currying isomorphism at a structure-sheaf source

Let `(C, O)` be a ringed site and let `L` and `M` be complexes of `O`-modules. The currying
isomorphism of **Stacks 0A90**

`SheafHom(K, SheafHom(L, M)) ≅ SheafHom(Tot(K ⊗_O L), M)`

is read here at `K = O[0]`, where its source collapses by evaluation at the unit section
(`AlgebraicGeometry.RingedSite.structureSheafHomIso` of Tag 0A91) and its target collapses by
the left unit isomorphism `Tot(O[0] ⊗_O L) ≅ L` of Tag 0FNG
(`AlgebraicGeometry.RingedSite.structureSheafComplexTensorLeftIso`). This file proves that the
two collapses agree:

`structureSheafHomIso⁻¹ ≫ curry = SheafHom(λ_ L, 1_M)`.

Equivalently: currying a section `s` of `SheafHom(L, M)`, read as a section of
`SheafHom(O[0], SheafHom(L, M))`, is precomposition with the left unit collapse.

## The computation

A local section of `SheafHom(Tot(O[0] ⊗_O L), M)` is determined by its values on the local pure
tensors (`AlgebraicGeometry.RingedSite.homSection_tensor_ext`), so everything reduces to the
value of both sides on a pure tensor `k ⊗ l` with `k` a section of `O[0]` in degree `t` and `l`
a section of `L` in degree `r`. There is no sign to track: the currying rule
`AlgebraicGeometry.RingedSite.curryRule` is a bare "evaluate at `k`, then at `l`", and the
differential square of the left unitor kills the Koszul factor of the total complex because the
trivialised factor sits in degree zero (see
`StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.UnitLeftFactorCollapse`).

Two cases. For `t ≠ 0` the section `k` vanishes
(`AlgebraicGeometry.RingedSite.structureSheafComplex_section_eq_zero`), hence so does the pure
tensor, and both sides are zero. For `t = 0` the section `k` is the scalar multiple `k · 1` of
the unit section; both sides are linear in it, so it suffices to treat `k = 1`, and there the
left-hand side is evaluation of `structureSheafHomIso⁻¹` at the unit section — which returns the
section it started from — while the right-hand side is the left unit collapse of `1 ⊗ l`, which
returns `l`.

## Main results

* `AlgebraicGeometry.RingedSite.curryFun_structureSheafHomIso_inv`: the unit law on local
  sections.
* `AlgebraicGeometry.RingedSite.structureSheafHomIso_inv_comp_sheafHomTensorCurryIso`: the unit
  law as an equality of morphisms of complexes, with the collapse spelled `λ_ L`.
* `AlgebraicGeometry.RingedSite.applyHomSectionOver_structureSheafHomIso_inv_one`: evaluation of
  `structureSheafHomIso⁻¹` at the unit section over an object of the slice site.

## Implementation notes

The left unit collapse has two spellings, `λ_ L` of `CochainComplex.symmetricCategory` and
`AlgebraicGeometry.RingedSite.structureSheafComplexTensorLeftIso` at the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling of the total tensor complex that Tag 0A90
is stated for. The two are `rfl`, but a goal mentioning both is not type-correct at the
`implicit` transparency level, after which no rewriting tactic acts on it: the symptom
is a `rw` reporting "did not find an occurrence" of a pattern that is visibly present. So the
whole elementwise computation is carried out at the `tensorComplex` spelling — hence
`structureSheafComplexTensorLeftIso_hom_f_val_app_one`, which is
`AlgebraicGeometry.RingedSite.leftUnitor_hom_f_val_app_one` moved across by a single `exact` in
its own declaration — and the crossing to `λ_ L` is paid once, at the end, between
`structureSheafHomIso_inv_comp_sheafHomTensorCurryIso'` and
`structureSheafHomIso_inv_comp_sheafHomTensorCurryIso`.

A degree-zero section of the structure sheaf complex and a section of the structure sheaf are
definitionally the same thing, but only the latter is found by instance search as a scalar, so
the section is renamed into a scalar by an `obtain` rather than by a type ascription: an
ascription leaves the term's inferred type unchanged and the `SMul` instance is then not found.

No `@[stacks]` attribute: Tag 0A90 asserts the currying isomorphism, which
`AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso` already carries, and Tag 0A91 asserts the
composition morphism. This unit coherence between them is a step in the proof of the duality
statements downstream, not a clause of either tag's statement.

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

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **Evaluating the inverse identification `I ≅ SheafHom(O[0], I)` at the unit section over an
object of the slice site** returns the restricted section. This is
`AlgebraicGeometry.RingedSite.applyHomSection_structureSheafHomIso_inv` over `g : W ⟶ U` rather
than over `U` itself. -/
lemma applyHomSectionOver_structureSheafHomIso_inv_one
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {U W : X.C} (g : W ⟶ U) (n : ℤ)
    (s : (I.X n).val.obj (op U)) :
    applyHomSectionOver X (sheafHomComplex X (structureSheafComplex X) I) U W g n 0 n (zero_add n)
        (((structureSheafHomIso X I).inv.f n).val.app (op U) s) (structureSheafOne X W) =
      restrictSection X g s := by
  rw [← structureSheafOne_restrict X g, applyHomSectionOver_map,
    applyHomSection_structureSheafHomIso_inv]

variable (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The left unit collapse on the local pure tensor of the unit section, read at the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling of the total tensor complex. This is
`AlgebraicGeometry.RingedSite.leftUnitor_hom_f_val_app_one`; the two statements differ only in
the spelling of the source complex, and that difference is `rfl`. -/
private lemma structureSheafComplexTensorLeftIso_hom_f_val_app_one (c : ℤ) (W : X.C)
    (l : (L.X c).val.obj (op W)) :
    ((structureSheafComplexTensorLeftIso X L).hom.f c).val.app (op W)
        (tensorComplexSection X 0 c c (zero_add c) (structureSheafOne X W) l) = l :=
  leftUnitor_hom_f_val_app_one X L c W l

/-- The unit law of the currying isomorphism, on local sections. -/
lemma curryFun_structureSheafHomIso_inv (n : ℤ) (U : X.C)
    (s : ((sheafHomComplex X L M).obj.X n).val.obj (op U)) :
    curryFun X U
        (((structureSheafHomIso X (sheafHomComplex X L M).obj).inv.f n).val.app (op U) s) =
      ((homMap X (structureSheafComplexTensorLeftIso X L).hom (𝟙 M)).f n).val.app (op U) s := by
  refine homSection_tensor_ext X U fun c d hcd t r htr W g k l ↦ ?_
  rcases eq_or_ne t 0 with rfl | ht
  · obtain rfl : c = r := by omega
    -- read the degree-zero section of the structure sheaf as a scalar
    obtain ⟨k, rfl⟩ : ∃ k' : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W),
        (k' : ((structureSheafComplex X).X 0).val.obj (op W)) = k := ⟨k, rfl⟩
    have hks : (k • structureSheafOne X W :
        ((structureSheafComplex X).X 0).val.obj (op W)) = k := by
      show k * 1 = k
      exact mul_one _
    rw [← hks, tensorComplexSection_smul_left, applyHomSectionOver_smul_right,
      applyHomSectionOver_smul_right, applyHomSectionOver_curryFun,
      ← curryRule_degree X U _ 0 c d n (zero_add n) hcd g (structureSheafOne X W) l,
      applyHomSectionOver_structureSheafHomIso_inv_one, ← applyHomSectionOver_restrict,
      applyHomSectionOver_homMap, structureSheafComplexTensorLeftIso_hom_f_val_app_one,
      id_f_val_app_apply]
  · rw [structureSheafComplex_section_eq_zero X W ht k]
    have h0 : tensorComplexSection X (K := structureSheafComplex X) (L := L) t r c htr 0 l = 0 := by
      have h := tensorComplexSection_smul_left X t r c htr
        (0 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W))
        (0 : ((structureSheafComplex X).X t).val.obj (op W)) l
      rwa [zero_smul, zero_smul] at h
    rw [h0]
    exact (map_zero _).trans (map_zero _).symm

/-- The unit law of the currying isomorphism, at the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling of the left unit collapse. -/
theorem structureSheafHomIso_inv_comp_sheafHomTensorCurryIso' :
    (structureSheafHomIso X (sheafHomComplex X L M).obj).inv ≫
        (sheafHomTensorCurryIso X (structureSheafComplex X) L M).hom =
      homMap X (structureSheafComplexTensorLeftIso X L).hom (𝟙 M) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_))
  exact curryFun_structureSheafHomIso_inv X L M n V.unop s

/-- **The unit law of the currying isomorphism of Stacks 0A90.** -/
theorem structureSheafHomIso_inv_comp_sheafHomTensorCurryIso :
    (structureSheafHomIso X (sheafHomComplex X L M).obj).inv ≫
        (sheafHomTensorCurryIso X (structureSheafComplex X) L M).hom =
      homMap X (λ_ L).hom (𝟙 M) :=
  structureSheafHomIso_inv_comp_sheafHomTensorCurryIso' X L M

end AlgebraicGeometry.RingedSite

end
