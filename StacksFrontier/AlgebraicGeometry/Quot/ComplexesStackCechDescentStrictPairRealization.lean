module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentStrictPair

/-!
# Stacks 0GMF on the strict components, realized

Piece P-0DHF of the 0DLA programme needs
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictPairRealization`:
a pair `(K₀, α)` on the spaces-étale sites satisfying the cocycle condition comes from a pair of
Stacks 0GMF on the strict components. It is proved here as
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictPairRealization`.

The object of the pair is a preimage of `K₀` under the realization `R_0` (an equivalence), its
gluing map is the preimage of `α` under `R_1` read through the squares
`strictComponentDerivedTransitionIso`, and its cocycle condition
(`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictPairRealization_cocycle`) is that of
`α`, transported along `R_2` (`CategoryTheory.hypercoverCocycle_of_realize`) by the
pseudonaturality of the realizations (`strictComponentDerivedTransitionIso_compOfEq`). The cocycle
condition of `α` is read through
`CategoryTheory.IsHypercoverDescentCocycle.of_components`, which identifies the restrictions of
`α` along the edges with given morphisms.

Nothing here is registered.

## References

* [Stacks Project, Tag 0GMF](https://stacks.math.columbia.edu/tag/0GMF)
* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v₁ u₁ v₂ u₂

/-- **The cocycle condition of Stacks 0GMF / 0DLA, read through given morphisms**: if the nine
natural transformations and morphisms `x, q, y` are the pullback triangles of the vertices and
the pullbacks of `α` along the three edges, then `IsHypercoverDescentCocycle` gives the cocycle
identity between them. -/
theorem IsHypercoverDescentCocycle.of_components {A : Type u₁} [Category.{v₁} A]
    (D : A → Type u₂) (instD : ∀ a, Category.{v₂} (D a))
    (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {U₀ U₁ U₂ : A} {s t : U₁ ⟶ U₀} {e₀₁ e₁₂ e₀₂ : U₂ ⟶ U₁} {K₀ : D U₀}
    {α : (pull s).obj K₀ ≅ (pull t).obj K₀} {v₀ v₁ v₂ : U₂ ⟶ U₀} {h₀ : e₀₁ ≫ s = v₀}
    {h₁ : e₀₁ ≫ t = v₁} {h₁' : e₁₂ ≫ s = v₁} {h₂ : e₁₂ ≫ t = v₂} {h₀' : e₀₂ ≫ s = v₀}
    {h₂' : e₀₂ ≫ t = v₂}
    {x₀₂ : pull v₀ ⟶ pull s ⋙ pull e₀₁}
    {q₂ : (pull e₀₁).obj ((pull s).obj K₀) ⟶ (pull e₀₁).obj ((pull t).obj K₀)}
    {y₁₂ : pull t ⋙ pull e₀₁ ⟶ pull v₁} {x₁₀ : pull v₁ ⟶ pull s ⋙ pull e₁₂}
    {q₀ : (pull e₁₂).obj ((pull s).obj K₀) ⟶ (pull e₁₂).obj ((pull t).obj K₀)}
    {y₂₀ : pull t ⋙ pull e₁₂ ⟶ pull v₂} {x₀₁ : pull v₀ ⟶ pull s ⋙ pull e₀₂}
    {q₁ : (pull e₀₂).obj ((pull s).obj K₀) ⟶ (pull e₀₂).obj ((pull t).obj K₀)}
    {y₂₁ : pull t ⋙ pull e₀₂ ⟶ pull v₂}
    (ex₀₂ : (hypercoverPullTriangle pull comp h₀).hom = x₀₂)
    (eq₂ : (pull e₀₁).map α.hom = q₂)
    (ey₁₂ : (hypercoverPullTriangle pull comp h₁).inv = y₁₂)
    (ex₁₀ : (hypercoverPullTriangle pull comp h₁').hom = x₁₀)
    (eq₀ : (pull e₁₂).map α.hom = q₀)
    (ey₂₀ : (hypercoverPullTriangle pull comp h₂).inv = y₂₀)
    (ex₀₁ : (hypercoverPullTriangle pull comp h₀').hom = x₀₁)
    (eq₁ : (pull e₀₂).map α.hom = q₁)
    (ey₂₁ : (hypercoverPullTriangle pull comp h₂').inv = y₂₁)
    (hα : IsHypercoverDescentCocycle pull comp s t e₀₁ e₁₂ e₀₂ α) :
    (x₀₂.app K₀ ≫ q₂ ≫ y₁₂.app K₀) ≫ (x₁₀.app K₀ ≫ q₀ ≫ y₂₀.app K₀) =
      x₀₁.app K₀ ≫ q₁ ≫ y₂₁.app K₀ := by
  subst ex₀₂ eq₂ ey₁₂ ex₁₀ eq₀ ey₂₀ ex₀₁ eq₁ ey₂₁
  exact hα v₀ v₁ v₂ h₀ h₁ h₁' h₂ h₀' h₂'

end CategoryTheory

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.CategoryTheory.Hypercovering
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedBaseChangeOfToposHom

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

/-! ### The vertices of `⦋2⦌` on `X` -/

/-- The vertex `0` of `⦋2⦌` on `X`, through the faces `δ²₂` and `δ¹₁`. -/
theorem strictPairVertex_two_one :
    X.map (SimplexCategory.δ (2 : Fin 3)).op ≫ X.map (SimplexCategory.δ (1 : Fin 2)).op =
      X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 0).op := by
  simp only [← X.map_comp, ← op_comp, SimplexCategory.delta_one_comp_delta_two]

/-- The vertex `0` of `⦋2⦌` on `X`, through the faces `δ²₁` and `δ¹₁`. -/
theorem strictPairVertex_one_one :
    X.map (SimplexCategory.δ (1 : Fin 3)).op ≫ X.map (SimplexCategory.δ (1 : Fin 2)).op =
      X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 0).op := by
  simp only [← X.map_comp, ← op_comp, SimplexCategory.delta_one_comp_delta_one]

/-- The vertex `1` of `⦋2⦌` on `X`, through the faces `δ²₂` and `δ¹₀`. -/
theorem strictPairVertex_two_zero :
    X.map (SimplexCategory.δ (2 : Fin 3)).op ≫ X.map (SimplexCategory.δ (0 : Fin 2)).op =
      X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 1).op := by
  simp only [← X.map_comp, ← op_comp, SimplexCategory.delta_zero_comp_delta_two]

/-- The vertex `1` of `⦋2⦌` on `X`, through the faces `δ²₀` and `δ¹₁`. -/
theorem strictPairVertex_zero_one :
    X.map (SimplexCategory.δ (0 : Fin 3)).op ≫ X.map (SimplexCategory.δ (1 : Fin 2)).op =
      X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 1).op := by
  simp only [← X.map_comp, ← op_comp, SimplexCategory.delta_one_comp_delta_zero]

/-- The vertex `2` of `⦋2⦌` on `X`, through the faces `δ²₀` and `δ¹₀`. -/
theorem strictPairVertex_zero_zero :
    X.map (SimplexCategory.δ (0 : Fin 3)).op ≫ X.map (SimplexCategory.δ (0 : Fin 2)).op =
      X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 2).op := by
  simp only [← X.map_comp, ← op_comp, SimplexCategory.delta_zero_comp_delta_zero]

/-- The vertex `2` of `⦋2⦌` on `X`, through the faces `δ²₁` and `δ¹₀`. -/
theorem strictPairVertex_one_zero :
    X.map (SimplexCategory.δ (1 : Fin 3)).op ≫ X.map (SimplexCategory.δ (0 : Fin 2)).op =
      X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 2).op := by
  simp only [← X.map_comp, ← op_comp, SimplexCategory.delta_zero_comp_delta_one]

/-! ### The cocycle condition -/

/-- **The cocycle condition of the pair of `strictPairRealization`.** If `ι` realizes, through
the squares `strictComponentDerivedTransitionIso` and `ε : R_0 K ≅ K₀`, to a gluing map `α`
satisfying the cocycle condition, then `(K, ι)` satisfies the cocycle condition of Stacks 0GMF:
`hypercoverCocycle_of_realize` at the six instances of
`strictComponentDerivedTransitionIso_compOfEq`, with the cocycle condition of `α` read through
`IsHypercoverDescentCocycle.of_components`. -/
theorem strictPairRealization_cocycle
    {K₀ : spacesEtaleDerivedModules B S hS (X.obj (op (SimplexCategory.mk 0)))}
    (α : (spacesEtaleDerivedPull B S hS (X.δ (1 : Fin 2))).obj K₀ ≅
      (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).obj K₀)
    (hα : @IsHypercoverDescentCocycle _ _ (spacesEtaleDerivedModules B S hS)
      (fun _ => inferInstance) (fun f => spacesEtaleDerivedPull B S hS f)
      (fun f g => spacesEtaleDerivedPullComp B S hS f g) _ _ _ (X.δ (1 : Fin 2)) (X.δ (0 : Fin 2))
      (X.δ (2 : Fin 3)) (X.δ (0 : Fin 3)) (X.δ (1 : Fin 3)) _ α)
    (K : DerivedCategory ((strictSituation X).componentRingedTopos (strictStructureSheaf X)
      (SimplexCategory.mk 0)).Modules)
    (ε : (strictComponentDerivedRealize X (SimplexCategory.mk 0)).obj K ≅ K₀)
    (ι : ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
        (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
        (SimplexCategory.δ (0 : Fin 2))).obj K)
    (hι : (strictComponentDerivedRealize X (SimplexCategory.mk 1)).map ι.hom =
      (strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2))).hom.app K ≫
        (spacesEtaleDerivedPull B S hS (X.δ (1 : Fin 2))).map ε.hom ≫ α.hom ≫
        (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).map ε.inv ≫
        (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2))).inv.app K) :
    ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
        (SimplexCategory.δ (1 : Fin 3))).map ι.hom =
      ((strictSituation X).derivedModuleGlueLeft (strictStructureSheaf X) K).inv ≫
        ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
          (SimplexCategory.δ (2 : Fin 3))).map ι.hom ≫
        ((strictSituation X).derivedModuleGlueMiddle (strictStructureSheaf X) K).hom ≫
        ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
          (SimplexCategory.δ (0 : Fin 3))).map ι.hom ≫
        ((strictSituation X).derivedModuleGlueRight (strictStructureSheaf X) K).hom := by
  have comp := fun (ψ : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 1)
    (φ : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2)
    (θ : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 2)
    (h : ψ ≫ φ = θ) (hk : X.map φ.op ≫ X.map ψ.op = X.map θ.op) =>
    strictComponentDerivedTransitionIso_compOfEq X ψ φ θ h hk K
  have hA := comp _ _ _ SimplexCategory.delta_one_comp_delta_two (strictPairVertex_two_one X)
  have hB := comp _ _ _ SimplexCategory.delta_one_comp_delta_one (strictPairVertex_one_one X)
  have hC := comp _ _ _ SimplexCategory.delta_zero_comp_delta_two (strictPairVertex_two_zero X)
  have hD := comp _ _ _ SimplexCategory.delta_one_comp_delta_zero (strictPairVertex_zero_one X)
  have hE := comp _ _ _ SimplexCategory.delta_zero_comp_delta_zero (strictPairVertex_zero_zero X)
  have hF := comp _ _ _ SimplexCategory.delta_zero_comp_delta_one (strictPairVertex_one_zero X)
  -- The functors, squares and triangles are read off from `hA`, ..., `hF`; `α`, `ι` and `hι`
  -- are elaborated after them, so that every datum is in the form of the six instances.
  refine hypercoverCocycle_of_realize (strictComponentDerivedRealize X (SimplexCategory.mk 0))
    (strictComponentDerivedRealize X (SimplexCategory.mk 1))
    (strictComponentDerivedRealize X (SimplexCategory.mk 2))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ε (by exact id α) (by exact ι)
    (by exact hι) _ _ _ _ _ _ hA hB hC hD hE hF ?_
  exact IsHypercoverDescentCocycle.of_components (spacesEtaleDerivedModules B S hS)
    (fun _ => inferInstance) (fun f => spacesEtaleDerivedPull B S hS f)
    (fun f g => spacesEtaleDerivedPullComp B S hS f g) (by exact rfl) (by exact rfl)
    (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl)
    (by exact rfl) (by exact hα)

/-! ### The comparisons in degrees zero and one -/

/-- The comparison in degree zero of the pair of `strictPairRealization`: the realization of the
coherent unit `pairDerivedModuleObjZeroIso`, followed by `ε`. -/
def strictPairDegreeZeroIso
    (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
    {K₀ : spacesEtaleDerivedModules B S hS (X.obj (op (SimplexCategory.mk 0)))}
    (ε : (strictComponentDerivedRealize X (SimplexCategory.mk 0)).obj Pr.obj ≅ K₀) :
    (strictComponentDerivedRealize X (SimplexCategory.mk 0)).obj
        (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).obj
          (SimplexCategory.mk 0)) ≅ K₀ :=
  (strictComponentDerivedRealize X (SimplexCategory.mk 0)).mapIso
    ((strictSituation X).pairDerivedModuleObjZeroIso (strictStructureSheaf X) Pr) ≪≫ ε

/-- The comparison in degree one of the pair of `strictPairRealization`, defined from the
transition along `δ¹₀`, the square `strictComponentDerivedTransitionIso` and
`strictPairDegreeZeroIso`. -/
def strictPairDegreeOneIso
    (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
    {K₀ : spacesEtaleDerivedModules B S hS (X.obj (op (SimplexCategory.mk 0)))}
    (ε : (strictComponentDerivedRealize X (SimplexCategory.mk 0)).obj Pr.obj ≅ K₀) :
    (strictComponentDerivedRealize X (SimplexCategory.mk 1)).obj
        (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).obj
          (SimplexCategory.mk 1)) ≅ (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).obj K₀ :=
  (strictComponentDerivedRealize X (SimplexCategory.mk 1)).mapIso
      ((strictSituation X).pairDerivedModuleTransitionIso (strictStructureSheaf X) Pr
        (SimplexCategory.δ (0 : Fin 2))).symm ≪≫
    (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2))).app _ ≪≫
    (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).mapIso (strictPairDegreeZeroIso X Pr ε)

/-- The transition along `δ¹₀` of the pair of `strictPairRealization` realizes to the identity
through `strictPairDegreeZeroIso` and `strictPairDegreeOneIso`. -/
theorem strictPairRealization_delta_zero
    (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
    {K₀ : spacesEtaleDerivedModules B S hS (X.obj (op (SimplexCategory.mk 0)))}
    (ε : (strictComponentDerivedRealize X (SimplexCategory.mk 0)).obj Pr.obj ≅ K₀) :
    (strictComponentDerivedRealize X (SimplexCategory.mk 1)).map
          (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).map
            (SimplexCategory.δ (0 : Fin 2))) =
        (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2))).hom.app _ ≫
          (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).map
            (strictPairDegreeZeroIso X Pr ε).hom ≫ (strictPairDegreeOneIso X Pr ε).inv :=
  hypercoverPair_realize_delta_zero (strictComponentDerivedRealize X (SimplexCategory.mk 0))
    (strictComponentDerivedRealize X (SimplexCategory.mk 1))
    ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
      (SimplexCategory.δ (0 : Fin 2)))
    (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2)))
    (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2)))
    (strictPairDegreeZeroIso X Pr ε)
    ((strictSituation X).pairDerivedModuleTransitionIso (strictStructureSheaf X) Pr
      (SimplexCategory.δ (0 : Fin 2)))

/-- The transition along `δ¹₁` of the pair of `strictPairRealization` realizes to `α` through
`strictPairDegreeZeroIso` and `strictPairDegreeOneIso`, if its gluing map realizes to `α`. -/
theorem strictPairRealization_delta_one
    (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
    {K₀ : spacesEtaleDerivedModules B S hS (X.obj (op (SimplexCategory.mk 0)))}
    (α : (spacesEtaleDerivedPull B S hS (X.δ (1 : Fin 2))).obj K₀ ≅
      (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).obj K₀)
    (ε : (strictComponentDerivedRealize X (SimplexCategory.mk 0)).obj Pr.obj ≅ K₀)
    (hι : (strictComponentDerivedRealize X (SimplexCategory.mk 1)).map Pr.iso.hom =
      (strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2))).hom.app Pr.obj ≫
        (spacesEtaleDerivedPull B S hS (X.δ (1 : Fin 2))).map ε.hom ≫ α.hom ≫
        (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).map ε.inv ≫
        (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2))).inv.app Pr.obj) :
    (strictComponentDerivedRealize X (SimplexCategory.mk 1)).map
          (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).map
            (SimplexCategory.δ (1 : Fin 2))) =
        (strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2))).hom.app _ ≫
          (spacesEtaleDerivedPull B S hS (X.δ (1 : Fin 2))).map
            (strictPairDegreeZeroIso X Pr ε).hom ≫ α.hom ≫ (strictPairDegreeOneIso X Pr ε).inv :=
  hypercoverPair_realize_delta_one (strictComponentDerivedRealize X (SimplexCategory.mk 0))
    (strictComponentDerivedRealize X (SimplexCategory.mk 1))
    ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
      (SimplexCategory.δ (1 : Fin 2)))
    ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
      (SimplexCategory.δ (0 : Fin 2)))
    (spacesEtaleDerivedPull B S hS (X.δ (1 : Fin 2)))
    (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2)))
    (strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2)))
    (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2)))
    ((strictSituation X).pairDerivedModuleObjZeroIso (strictStructureSheaf X) Pr) ε α Pr.iso hι
    ((strictSituation X).pairDerivedModuleTransitionIso (strictStructureSheaf X) Pr
      (SimplexCategory.δ (0 : Fin 2)))
    ((strictSituation X).pairDerivedModuleTransition (strictStructureSheaf X) Pr
      (SimplexCategory.δ (1 : Fin 2)))
    ((strictSituation X).pairDerivedModuleTransition_delta_one (strictStructureSheaf X) Pr)

/-- In every degree `k` the system of a pair realizes to the pullback of `K₀` along the last
vertex of `⦋k⦌`, through the square `strictComponentDerivedTransitionIso` and `ε`. -/
theorem strictPairRealization_vertex
    (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
    {K₀ : spacesEtaleDerivedModules B S hS (X.obj (op (SimplexCategory.mk 0)))}
    (ε : (strictComponentDerivedRealize X (SimplexCategory.mk 0)).obj Pr.obj ≅ K₀) (k : ℕ) :
    Nonempty ((strictComponentDerivedRealize X (SimplexCategory.mk k)).obj
          (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).obj
            (SimplexCategory.mk k)) ≅
        (spacesEtaleDerivedPull B S hS (X.map (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk k) (Fin.last k)).op)).obj K₀) :=
  ⟨(strictComponentDerivedTransitionIso X
      (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk k) (Fin.last k))).app
        Pr.obj ≪≫
    (spacesEtaleDerivedPull B S hS (X.map (SimplexCategory.const (SimplexCategory.mk 0)
      (SimplexCategory.mk k) (Fin.last k)).op)).mapIso ε⟩

/-! ### Stacks 0GMF on the strict components, realized -/

/-- **Stacks 0GMF on the strict components, realized.** A pair `(K₀, α)` on the spaces-étale
sites satisfying the cocycle condition comes from a pair of Stacks 0GMF on the strict
components: the object is a preimage `K` of `K₀` under the realization `R_0`, the gluing map is
the preimage of `α` under `R_1` read through the squares `strictComponentDerivedTransitionIso`,
and its cocycle condition is `strictPairRealization_cocycle`. -/
theorem strictPairRealization : StrictPairRealization X := by
  intro K₀ α hα
  obtain ⟨K, ⟨ε⟩⟩ : ∃ K, Nonempty
      ((strictComponentDerivedRealize X (SimplexCategory.mk 0)).obj K ≅ K₀) :=
    ⟨_, ⟨(strictComponentDerivedRealize X (SimplexCategory.mk 0)).objObjPreimageIso K₀⟩⟩
  obtain ⟨ι, hι⟩ : ∃ ι : ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
        (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
        (SimplexCategory.δ (0 : Fin 2))).obj K,
      (strictComponentDerivedRealize X (SimplexCategory.mk 1)).map ι.hom =
        (strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2))).hom.app K ≫
          (spacesEtaleDerivedPull B S hS (X.δ (1 : Fin 2))).map ε.hom ≫ α.hom ≫
          (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).map ε.inv ≫
          (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2))).inv.app K :=
    ⟨(strictComponentDerivedRealize X (SimplexCategory.mk 1)).preimageIso
      ((strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2))).app K ≪≫
        (spacesEtaleDerivedPull B S hS (X.δ (1 : Fin 2))).mapIso ε ≪≫ α ≪≫
        (spacesEtaleDerivedPull B S hS (X.δ (0 : Fin 2))).mapIso ε.symm ≪≫
        ((strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2))).app K).symm),
      Functor.map_preimage _ _⟩
  refine ⟨⟨K, ι, strictPairRealization_cocycle X α hα K ε ι hι⟩, strictPairDegreeZeroIso X _ ε,
    strictPairDegreeOneIso X _ ε, ?_, ?_, strictPairRealization_vertex X _ ε⟩
  · exact strictPairRealization_delta_zero X _ _
  · exact strictPairRealization_delta_one X _ _ _ (by exact hι)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
