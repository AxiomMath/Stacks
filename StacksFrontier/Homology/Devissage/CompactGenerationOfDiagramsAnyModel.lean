module

public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTrans
public import StacksFrontier.Homology.Devissage.CompactGenerationOfDiagrams

/-!
# The dévissage along the free diagrams, at any chosen model of the derived category

Let `C` be a small category and let `D` be an abelian category, with its morphisms in the universe
`u` of the objects and morphisms of `C`, which is Grothendieck abelian relative to `u`, has
countable products and has those products exact. Let `S` be a separating family of projective
compact objects of `D`. A morphism `τ : F ⟶ G` of exact direct-sum-preserving functors out of
`D(Cᵒᵖ ⥤ D)` which is compatible with the shift is an isomorphism as soon as it is invertible on
each free diagram `CategoryTheory.Presheaf.freeYoneda X (S i)` placed in degree zero.

`StacksDraft.CompactDevissage.isCompactlyGenerated_derivedCategory_diagrams` says that those
objects compactly generate, but it says it *at a model whose morphisms live in `Type u`*, because
the cell presentation of
`CategoryTheory.Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated` tests compactness
at the hom universe of the category. At `CategoryTheory.HasDerivedCategory.standard` the morphisms
of `D(Cᵒᵖ ⥤ D)` live one level higher, where `HasCoproducts` indexed by the hom universe fails, so
the dévissage cannot be run there at all. This file removes that restriction from the
*conclusion*: `τ` is invertible exactly when its whiskering by the comparison equivalence with the
[Stacks, Tag 079Q] model is, and there the cell presentation does apply.

## Main results

* `StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda` — the dévissage at a model whose
  morphisms live in `Type u`.
* `StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel` — the dévissage at an
  arbitrary chosen model, `CategoryTheory.HasDerivedCategory.standard` included.
* `StacksDraft.CompactDevissage.natIsoOfIsIsoAppFreeYoneda` — the resulting natural isomorphism.

## Implementation notes

The transport is the one of
`StacksDraft.CompactDevissage.isIso_of_isIso_app_uliftRegularModule_anyModel`, and the three
instance precautions recorded there are load-bearing here too: every class of the ambient model is
fixed before the second model is introduced, the additivity of the shift functors is supplied by
name because `(n : ℤ)` is an explicit binder and a local hypothesis is therefore not an instance
candidate, and the two `Pretriangulated` instances are introduced with `let` rather than `have`
because `Pretriangulated` carries data.

The locally small model is `Stacks.Injectives.hasDerivedCategory_diagrams`, and the two models are
compared by `StacksDraft.DerivedModel.modelEquiv`, which is model-generic: it takes both
`HasDerivedCategory` instances as explicit arguments.
`StacksDraft.DerivedModel.modelInverseCompQIso` identifies `e.inverse.obj (Q X)` with `Q X` for a
cochain complex `X`, which is what carries the hypothesis at the generators from one model to the
other.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor CategoryTheory.ObjectProperty
open StacksDraft.DerivedModel

universe uD u u' v' w

namespace StacksDraft.CompactDevissage

open StacksDraft.NatTransDevissage

section Diagrams

variable {C : Type u} [SmallCategory C] {D : Type uD} [Category.{u} D] [Abelian D]
  [IsGrothendieckAbelian.{u} D] [HasProductsOfShape ℕ D]
  [HasExactLimitsOfShape (Discrete ℕ) D]
  {D' : Type u'} [Category.{v'} D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

/-- **The dévissage along the free diagrams, at a locally small model.** A morphism of exact
direct-sum-preserving functors out of `D(Cᵒᵖ ⥤ D)` is an isomorphism as soon as it is invertible on
every `CategoryTheory.Presheaf.freeYoneda X (S i)` in degree zero.

The hypothesis `[HasDerivedCategory.{u} (Cᵒᵖ ⥤ D)]` asks the morphisms to live in the universe `u`
of the objects of `C`, which is what the cell presentation needs; such a model exists by
`Stacks.Injectives.hasDerivedCategory_diagrams`. For an arbitrary model use
`isIso_of_isIso_app_freeYoneda_anyModel`. -/
theorem isIso_of_isIso_app_freeYoneda [HasDerivedCategory.{u} (Cᵒᵖ ⥤ D)]
    {ι : Type u} (S : ι → D) [∀ i, Projective (S i)]
    (hcomp : ∀ i, IsCompactObject.{u} (S i))
    (hS : (ObjectProperty.ofObj S).IsSeparating)
    {F G : DerivedCategory (Cᵒᵖ ⥤ D) ⥤ D'}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) G]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (hτ : ∀ (X : C) (i : ι), IsIso (τ.app ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ D) 0).obj
      (Presheaf.freeYoneda X (S i))))) : IsIso τ := by
  classical
  let : HasCoproducts.{u} D := fun J ↦ inferInstance
  have : HasCoproducts.{u} (DerivedCategory (Cᵒᵖ ⥤ D)) :=
    Stacks.Injectives.hasCoproducts_derivedCategory_diagrams C D
  have hproj : ∀ p : C × ι, Projective (Presheaf.freeYoneda p.1 (S p.2)) := fun p ↦
    Stacks.CategoryHomology.freeYonedaProjective p.1 (S p.2)
  have hsep : (ObjectProperty.ofObj
      (fun p : C × ι ↦ Presheaf.freeYoneda p.1 (S p.2))).IsSeparating :=
    Presheaf.isSeparating C hS
  exact isIso_of_isCompactlyGenerated τ
    (fun p : C × ι ↦ (DerivedCategory.singleFunctor (Cᵒᵖ ⥤ D) 0).obj
      (Presheaf.freeYoneda p.1 (S p.2)))
    (fun p ↦ by
      have := Presheaf.isCompactObject_freeYoneda.{u} p.1 (S p.2) (hcomp p.2)
      exact StacksDraft.Perfect.isCompactObject_derived_single _ 0)
    (Stacks.Cohomology.isWeakTriangulatedGenerator_single_of_projective_separating _ hsep)
    (fun p ↦ hτ p.1 p.2)

/-- **The dévissage along the free diagrams at an arbitrary chosen model**,
`CategoryTheory.HasDerivedCategory.standard` included.

The cell presentation behind the dévissage cannot be run at the standard model, where the hom
universe of `D(Cᵒᵖ ⥤ D)` is above the universe `u` indexing its direct sums. It does not have to
be: `τ` is invertible exactly when its whiskering by the comparison equivalence with the
[Stacks, Tag 079Q] model is, and there the previous statement applies. -/
theorem isIso_of_isIso_app_freeYoneda_anyModel [h : HasDerivedCategory.{w} (Cᵒᵖ ⥤ D)]
    {ι : Type u} (S : ι → D) [∀ i, Projective (S i)]
    (hcomp : ∀ i, IsCompactObject.{u} (S i))
    (hS : (ObjectProperty.ofObj S).IsSeparating)
    {F G : DerivedCategory (Cᵒᵖ ⥤ D) ⥤ D'}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) G]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (hτ : ∀ (X : C) (i : ι), IsIso (τ.app ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ D) 0).obj
      (Presheaf.freeYoneda X (S i))))) : IsIso τ := by
  -- the ambient model's classes are fixed FIRST; a second model in scope makes them
  -- unsynthesizable, and `Pretriangulated` carries data so it must be a `let`
  let t1 := @DerivedCategory.instPretriangulated (Cᵒᵖ ⥤ D) _ _ h
  let h₂ := Stacks.Injectives.hasDerivedCategory_diagrams C D
  let t2 := @DerivedCategory.instPretriangulated (Cᵒᵖ ⥤ D) _ _ h₂
  let e := modelEquiv h h₂
  have hadd1 : ∀ n : ℤ, (shiftFunctor (@DerivedCategory (Cᵒᵖ ⥤ D) _ _ h) n).Additive :=
    fun n => @DerivedCategory.instAdditiveShiftFunctorInt _ _ _ h n
  have hadd2 : ∀ n : ℤ, (shiftFunctor (@DerivedCategory (Cᵒᵖ ⥤ D) _ _ h₂) n).Additive :=
    fun n => @DerivedCategory.instAdditiveShiftFunctorInt _ _ _ h₂ n
  let hcs := StacksDraft.Perfect.derivedEquivalenceCommShift h h₂
  have hetri := StacksDraft.Perfect.derivedEquivalence_isTriangulated h h₂
  let hinvcs := e.commShiftInverse ℤ
  let hecs := e.commShift_of_functor ℤ
  have hetri2 := Equivalence.IsTriangulated.mk' e hetri
  have hinvtri : e.inverse.IsTriangulated := inferInstance
  have hτ' : IsIso (Functor.whiskerLeft e.inverse τ) :=
    isIso_of_isIso_app_freeYoneda S hcomp hS (Functor.whiskerLeft e.inverse τ) fun X i ↦
      isIso_app_of_iso τ ((modelInverseCompQIso h h₂).app
        ((CochainComplex.singleFunctor (Cᵒᵖ ⥤ D) 0).obj (Presheaf.freeYoneda X (S i)))).symm
        (hτ X i)
  have hall : ∀ X, IsIso (τ.app X) := by
    intro X
    have h1 : IsIso ((Functor.whiskerLeft e.inverse τ).app (e.functor.obj X)) := inferInstance
    exact isIso_app_of_iso τ (e.unitIso.app X).symm h1
  exact NatIso.isIso_of_isIso_app τ

/-- The natural isomorphism produced by the dévissage along the free diagrams at an arbitrary
chosen model. -/
def natIsoOfIsIsoAppFreeYoneda [h : HasDerivedCategory.{w} (Cᵒᵖ ⥤ D)]
    {ι : Type u} (S : ι → D) [∀ i, Projective (S i)]
    (hcomp : ∀ i, IsCompactObject.{u} (S i))
    (hS : (ObjectProperty.ofObj S).IsSeparating)
    {F G : DerivedCategory (Cᵒᵖ ⥤ D) ⥤ D'}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) G]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (hτ : ∀ (X : C) (i : ι), IsIso (τ.app ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ D) 0).obj
      (Presheaf.freeYoneda X (S i))))) : F ≅ G :=
  have := isIso_of_isIso_app_freeYoneda_anyModel S hcomp hS τ hτ
  asIso τ

end Diagrams

end StacksDraft.CompactDevissage

end
