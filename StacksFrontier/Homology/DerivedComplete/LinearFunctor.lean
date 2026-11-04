module

public import StacksFrontier.Homology.DerivedComplete

/-!
# Linear functors preserving countable products preserve derived completeness

An `A`-linear functor `G` between `A`-linear categories with countable products which preserves
those products intertwines the maps `1 - f·shift` on `∏ K` and on `∏ G(K)`, so it carries objects
derived complete at `f` (Stacks 091S) to objects derived complete at `f`, and objects derived
complete with respect to an ideal `I` to objects derived complete with respect to `I`.

## Main results

* `DerivedCompletionReflection.map_oneSubSmulShift_comp_piComparison`: the comparison map
  `G(∏ K) ⟶ ∏ G(K)` intertwines `G(1 - f·shift)` with `1 - f·shift`.
* `DerivedCompletionReflection.isDerivedCompleteAt_obj`: `G` preserves derived completeness at
  an element `f`.
* `DerivedCompletionReflection.isDerivedComplete_obj`: `G` preserves derived completeness with
  respect to an ideal `I`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits


namespace DerivedCompletionReflection

variable {A : Type*} [CommRing A] {𝒟 ℰ : Type*} [Category 𝒟] [Category ℰ] [Preadditive 𝒟]
  [Preadditive ℰ] [Linear A 𝒟] [Linear A ℰ] [HasProductsOfShape ℕ 𝒟] [HasProductsOfShape ℕ ℰ]

/-- For a linear functor `G`, the comparison map `G(∏ K) ⟶ ∏ G(K)` intertwines
`G.map (oneSubSmulShift K f)` with `oneSubSmulShift (G.obj K) f`. -/
theorem map_oneSubSmulShift_comp_piComparison (G : 𝒟 ⥤ ℰ) [G.Additive] [G.Linear A] (K : 𝒟)
    (f : A) :
    G.map (oneSubSmulShift K f) ≫ piComparison G (fun _ : ℕ => K) =
      piComparison G (fun _ : ℕ => K) ≫ oneSubSmulShift (G.obj K) f := by
  refine Pi.hom_ext _ _ fun n => ?_
  rw [Category.assoc, piComparison_comp_π, ← G.map_comp, oneSubSmulShift_π, Category.assoc,
    oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul, piComparison_comp_π,
    piComparison_comp_π, G.map_sub, G.map_smul]

/-- A linear functor preserving countable products carries an object derived complete at `f`
to an object derived complete at `f`. -/
theorem isDerivedCompleteAt_obj (G : 𝒟 ⥤ ℰ) [G.Additive] [G.Linear A]
    [PreservesLimitsOfShape (Discrete ℕ) G] {K : 𝒟} {f : A} (h : IsDerivedCompleteAt K f) :
    IsDerivedCompleteAt (G.obj K) f := by
  rw [isDerivedCompleteAt_iff_isIso] at h ⊢
  have e := map_oneSubSmulShift_comp_piComparison G K f
  rw [← IsIso.inv_comp_eq] at e
  rw [← e]
  infer_instance

/-- A linear functor preserving countable products carries an object derived complete with
respect to an ideal `I` to an object derived complete with respect to `I`. -/
theorem isDerivedComplete_obj (G : 𝒟 ⥤ ℰ) [G.Additive] [G.Linear A]
    [PreservesLimitsOfShape (Discrete ℕ) G] {I : Ideal A} {K : 𝒟} (h : IsDerivedComplete I K) :
    IsDerivedComplete I (G.obj K) :=
  fun f hf => isDerivedCompleteAt_obj G (h f hf)

end DerivedCompletionReflection
