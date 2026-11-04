module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Linear

/-!
# Linearity of the total complex of a bifunctor in its first variable

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor between `R`-linear categories such that `F - X₂` is
`R`-linear for every object `X₂`. Then for every complex `K₂` the functor
`K₁ ↦ Tot(F(K₁, K₂))` on complexes is `R`-linear: on the summand `F(K₁ᵖ, K₂ᑫ)` of the total
complex the map induced by `r • f` is `F(r • fᵖ, K₂ᑫ) = r • F(fᵖ, K₂ᑫ)`.

## Main results

* `HomologicalComplex.mapBifunctorMap_smul_left`: `Tot(F(r • f, 𝟙)) = r • Tot(F(f, 𝟙))`.
* `HomologicalComplex.linear_map₂HomologicalComplex_flip_obj`: the functor
  `K₁ ↦ Tot(F(K₁, K₂))` is `R`-linear.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable (R : Type*) [Semiring R] {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  [CategoryTheory.Linear R C₁] [CategoryTheory.Linear R D]
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  [∀ X₂, (F.flip.obj X₂).Linear R] (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]
  [DecidableEq J]

/-- **The map of total complexes induced by `r • f` in the first variable is `r` times the map
induced by `f`.** -/
theorem mapBifunctorMap_smul_left {K₁ L₁ : HomologicalComplex C₁ c₁}
    (K₂ : HomologicalComplex C₂ c₂) [K₁.HasMapBifunctor K₂ F c] [L₁.HasMapBifunctor K₂ F c]
    (f : K₁ ⟶ L₁) (r : R) :
    mapBifunctorMap (r • f) (𝟙 K₂) F c = r • mapBifunctorMap f (𝟙 K₂) F c := by
  ext j i₁ i₂ h
  have hlin : (F.map (r • f.f i₁)).app (K₂.X i₂) = r • (F.map (f.f i₁)).app (K₂.X i₂) :=
    (F.flip.obj (K₂.X i₂)).map_smul r (f.f i₁)
  rw [smul_f_apply, Linear.comp_smul, ι_mapBifunctorMap, ι_mapBifunctorMap, smul_f_apply, hlin,
    Linear.smul_comp]

/-- **The total complex `K₁ ↦ Tot(F(K₁, K₂))` is `R`-linear in its first variable.** -/
theorem linear_map₂HomologicalComplex_flip_obj (K₂ : HomologicalComplex C₂ c₂)
    [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂),
      K₁.HasMapBifunctor K₂ F c] :
    ((F.map₂HomologicalComplex c₁ c₂ c).flip.obj K₂).Linear R where
  map_smul f r := mapBifunctorMap_smul_left R F c K₂ f r

end HomologicalComplex
