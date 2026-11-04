module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Comparing the cohomology of distinguished triangles

Small tools for comparing the cohomology of objects of a derived category along a morphism of
distinguished triangles.

## Main results

* `DerivedCategory.isIso_homologyFunctor_map_hom₃`: the five lemma for a morphism of
  distinguished triangles in a derived category.
* `DerivedCategory.epi_homologyFunctor_map_mor₁_of_isZero` and
  `DerivedCategory.mono_homologyFunctor_map_mor₁_of_isZero`: the cohomology of the first map of a
  distinguished triangle is onto (resp. injective) where the third vertex has no cohomology
  (resp. no cohomology one degree lower).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

open HomologySequence

/-- **The five lemma for a morphism of distinguished triangles.** Let `φ : T ⟶ T'` be a morphism
of distinguished triangles in `D(C)`. If in degree `n` the map on `H^n` of the first vertices is
onto and that of the second vertices is invertible, and in degree `n + 1` the map of the first
vertices is invertible and that of the second vertices injective, then the map on `H^n` of the
third vertices is invertible. -/
theorem isIso_homologyFunctor_map_hom₃ {T T' : Triangle (DerivedCategory C)}
    (hT : T ∈ distTriang _) (hT' : T' ∈ distTriang _) (φ : T ⟶ T') (n : ℤ)
    (h₁ : Epi ((homologyFunctor C n).map φ.hom₁))
    (h₂ : IsIso ((homologyFunctor C n).map φ.hom₂))
    (h₄ : IsIso ((homologyFunctor C (n + 1)).map φ.hom₁))
    (h₅ : Mono ((homologyFunctor C (n + 1)).map φ.hom₂)) :
    IsIso ((homologyFunctor C n).map φ.hom₃) := by
  let H := homologyFunctor C 0
  let row (U : Triangle (DerivedCategory C)) :=
    (H.homologySequenceComposableArrows₅ U n (n + 1) rfl).δlast
  have hexact (U : Triangle (DerivedCategory C)) (hU : U ∈ distTriang _) : (row U).Exact :=
    (H.homologySequenceComposableArrows₅_exact U hU n (n + 1) rfl).δlast
  let ψ : row T ⟶ row T' :=
    ComposableArrows.homMk₄
      ((homologyFunctor C n).map φ.hom₁)
      ((homologyFunctor C n).map φ.hom₂)
      ((homologyFunctor C n).map φ.hom₃)
      ((homologyFunctor C (n + 1)).map φ.hom₁)
      ((homologyFunctor C (n + 1)).map φ.hom₂)
      (((homologyFunctor C n).map_commSq ⟨φ.comm₁⟩).w)
      (((homologyFunctor C n).map_commSq ⟨φ.comm₂⟩).w)
      (H.homologySequenceδ_naturality φ n (n + 1) rfl).symm
      (((homologyFunctor C (n + 1)).map_commSq ⟨φ.comm₁⟩).w)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (hexact T hT) (hexact T' hT') ψ
    h₁ h₂ h₄ h₅

variable {T : Triangle (DerivedCategory C)} (hT : T ∈ distTriang _)
include hT

/-- In a distinguished triangle, the first map is onto on `H^n` when the third vertex has no
`H^n`. -/
theorem epi_homologyFunctor_map_mor₁_of_isZero (n : ℤ)
    (h : IsZero ((homologyFunctor C n).obj T.obj₃)) :
    Epi ((homologyFunctor C n).map T.mor₁) :=
  (epi_homologyMap_mor₁_iff T hT n).2 (h.eq_of_tgt _ _)

/-- In a distinguished triangle, the first map is injective on `H^{n+1}` when the third vertex
has no `H^n`. -/
theorem mono_homologyFunctor_map_mor₁_of_isZero (n : ℤ)
    (h : IsZero ((homologyFunctor C n).obj T.obj₃)) :
    Mono ((homologyFunctor C (n + 1)).map T.mor₁) :=
  (mono_homologyMap_mor₁_iff T hT n (n + 1) rfl).2 (h.eq_of_src _ _)

/-- In a distinguished triangle, the third vertex has no `H^n` when the first map is onto on
`H^n` and injective on `H^{n+1}`. -/
theorem isZero_homologyFunctor_obj₃ (n : ℤ) (h₁ : Epi ((homologyFunctor C n).map T.mor₁))
    (h₂ : Mono ((homologyFunctor C (n + 1)).map T.mor₁)) :
    IsZero ((homologyFunctor C n).obj T.obj₃) :=
  (exact₃ T hT n (n + 1) rfl).isZero_X₂ ((epi_homologyMap_mor₁_iff T hT n).1 h₁)
    ((mono_homologyMap_mor₁_iff T hT n (n + 1) rfl).1 h₂)

end DerivedCategory
