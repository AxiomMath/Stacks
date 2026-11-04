module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Ext into a product

Let `𝒜` be an abelian category and `(F i)_{i ∈ ι}` a family of objects of `𝒜` admitting a
product. Corestriction along the projections `∏ F ⟶ F i` gives a comparison morphism
`Ext^n(X, ∏ F) ⟶ ∏ Ext^n(X, F i)`. It is an isomorphism for `n = 0`, where both sides compute
`Hom`, and a monomorphism for `n = 1`: an extension of `X` by `∏ F` whose pushforward along
every projection splits admits a retraction of its inclusion, assembled from the retractions of
the pushforwards, hence splits itself.

In higher degrees the comparison need not be injective, so no statement is made for `n ≥ 2`.

## Main results

* `CategoryTheory.Abelian.isIso_piComparison_extFunctorObj_zero`: the comparison
  `Ext^0(X, ∏ F) ⟶ ∏ Ext^0(X, F i)` is an isomorphism.
* `CategoryTheory.Abelian.mono_piComparison_extFunctorObj_one`: the comparison
  `Ext^1(X, ∏ F) ⟶ ∏ Ext^1(X, F i)` is a monomorphism.

## Implementation notes

The comparison is Mathlib's `CategoryTheory.Limits.piComparison` for the functor
`CategoryTheory.Abelian.extFunctorObj X n`, so no new map is introduced. The coefficient
universe of the extension groups and the universe of the index type are unrelated.
-/

@[expose] public noncomputable section

universe t w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasExt.{w} 𝒜]
  {ι : Type t} (F : ι → 𝒜) (X : 𝒜) [HasProduct F]

/-- The `i`-th component of the comparison morphism `Ext^n(X, ∏ F) ⟶ ∏ Ext^n(X, F i)` is
corestriction along the projection `∏ F ⟶ F i`. -/
private theorem piComparison_extFunctorObj_apply (n : ℕ)
    [HasProduct fun i ↦ (extFunctorObj.{w} X n).obj (F i)]
    (e : Ext.{w} X (∏ᶜ F) n) (i : ι) :
    Pi.π (fun j ↦ (extFunctorObj.{w} X n).obj (F j)) i
      (piComparison (extFunctorObj.{w} X n) F e) =
      e.comp (Ext.mk₀ (Pi.π F i)) (add_zero n) := by
  have equality := congrArg (fun φ :
      (extFunctorObj.{w} X n).obj (∏ᶜ F) ⟶ (extFunctorObj.{w} X n).obj (F i) ↦ φ e)
    (piComparison_comp_π (extFunctorObj.{w} X n) F i)
  rwa [AddCommGrpCat.comp_apply (piComparison (extFunctorObj.{w} X n) F)
    (Pi.π (fun j ↦ (extFunctorObj.{w} X n).obj (F j)) i) e] at equality

/-- **Degree-zero extension groups commute with products.** The comparison morphism
`Ext^0(X, ∏ F) ⟶ ∏ Ext^0(X, F i)` given by corestriction along the projections is an
isomorphism, both sides being the group of morphisms out of `X`. -/
public theorem isIso_piComparison_extFunctorObj_zero
    [HasProduct fun i ↦ (extFunctorObj.{w} X 0).obj (F i)] :
    IsIso (piComparison (extFunctorObj.{w} X 0) F) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro e e' h
    apply Ext.addEquiv₀.injective
    apply Pi.hom_ext
    intro i
    apply (Ext.mk₀_bijective _ _).injective
    have component := piComparison_extFunctorObj_apply F X 0 e' i
    rw [← h, piComparison_extFunctorObj_apply F X 0 e i] at component
    rwa [← Ext.mk₀_addEquiv₀_apply e, ← Ext.mk₀_addEquiv₀_apply e',
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀] at component
  · intro e
    refine ⟨Ext.mk₀ (Pi.lift fun i ↦ Ext.addEquiv₀
      (Pi.π (fun j ↦ (extFunctorObj.{w} X 0).obj (F j)) i e)), ?_⟩
    apply Concrete.limit_ext
    intro ⟨i⟩
    show Pi.π (fun j ↦ (extFunctorObj.{w} X 0).obj (F j)) i
      ((piComparison (extFunctorObj.{w} X 0) F) _) =
        Pi.π (fun j ↦ (extFunctorObj.{w} X 0).obj (F j)) i e
    rw [piComparison_extFunctorObj_apply F X 0 _ i, Ext.mk₀_comp_mk₀, Pi.lift_π]
    exact Ext.mk₀_addEquiv₀_apply _

/-- An extension of `X` by `∏ F` whose corestriction along every projection vanishes is split:
each corestriction being zero, the inclusion of `∏ F` admits a retraction to each `F i`, and
these assemble into a retraction of the inclusion itself. -/
private theorem ext_one_eq_zero_of_comp_pi_eq_zero (e : Ext.{w} X (∏ᶜ F) 1)
    (vanishes : ∀ i, e.comp (Ext.mk₀ (Pi.π F i)) (add_zero 1) = 0) : e = 0 := by
  obtain ⟨M, incl, proj, zero, exactness, class_eq⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum 𝒜 X (∏ᶜ F)).1 e
  have lifts (i : ι) : ∃ r : M ⟶ F i, incl ≫ r = Pi.π F i := by
    obtain ⟨r, hr⟩ := Ext.contravariant_sequence_exact₁ exactness (F i)
      (Ext.mk₀ (Pi.π F i)) (add_zero 1) (by simpa only [class_eq] using vanishes i)
    refine ⟨Ext.addEquiv₀ r, ?_⟩
    apply (Ext.mk₀_bijective _ _).injective
    simpa only [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply] using hr
  choose r hr using lifts
  have retraction : incl ≫ Pi.lift r = 𝟙 (∏ᶜ F) :=
    Pi.hom_ext _ _ fun i ↦ by simpa only [Category.assoc, Pi.lift_π, Category.id_comp] using hr i
  calc
    e = e.comp (Ext.mk₀ (𝟙 (∏ᶜ F))) (add_zero 1) := by simp
    _ = e.comp (Ext.mk₀ (incl ≫ Pi.lift r)) (add_zero 1) := by rw [retraction]
    _ = 0 := by
        rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero, ← class_eq,
          exactness.extClass_comp, Ext.zero_comp]

/-- **Degree-one extension groups inject into the product.** The comparison morphism
`Ext^1(X, ∏ F) ⟶ ∏ Ext^1(X, F i)` given by corestriction along the projections is a
monomorphism. -/
public theorem mono_piComparison_extFunctorObj_one
    [HasProduct fun i ↦ (extFunctorObj.{w} X 1).obj (F i)] :
    Mono (piComparison (extFunctorObj.{w} X 1) F) := by
  rw [AddCommGrpCat.mono_iff_injective]
  exact (injective_iff_map_eq_zero _).2 fun e h ↦
    ext_one_eq_zero_of_comp_pi_eq_zero F X e fun i ↦ by
      rw [← piComparison_extFunctorObj_apply F X 1 e i, h]
      exact map_zero _

end CategoryTheory.Abelian

end
