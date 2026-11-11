module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceEtaleStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceLimitProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation

/-!
# Derived sections over an étale test space commute with reduction (Stacks 0DIP)

In Situation [Stacks, Tag 0DIK] let `K` be as in [Stacks, Tag 0DIL], let `j : U ⟶ X` be étale
with `U` quasi-compact and quasi-separated, and let `Uₙ = U ×_X Xₙ`. Then
`RΓ(U, K) ⊗^L_A Aₙ = RΓ(Uₙ, Kₙ)` in `D(Aₙ)`.

## Main results

* `CategoryTheory.Functor.isIso_map_mor₁_of_isZero_map_obj₃`: a triangulated functor which kills
  the third vertex of a distinguished triangle inverts its first map.
* `…isQuasiCompact_spaceProjection`, `…isQuasiSeparated_spaceProjection`: `Xₙ ⟶ X` is
  quasi-compact and quasi-separated, being a closed immersion.
* `…isQuasicoherent_cone_coheratorLimitPullbackMap`: the cone `Cₙ` of `τₙ : Lpₙ^* K ⟶ Kₙ` lies in
  `D_QCoh(𝒪_{Xₙ})`.

## References

* [Stacks Project, Tag 0DIP](https://stacks.math.columbia.edu/tag/0DIP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard

/-- **A triangulated functor which kills the third vertex of a distinguished triangle inverts its
first map**: it carries the triangle to a distinguished triangle with zero third vertex. -/
theorem _root_.CategoryTheory.Functor.isIso_map_mor₁_of_isZero_map_obj₃
    {C E : Type*} [Category* C] [Category* E] [HasZeroObject C] [HasZeroObject E]
    [HasShift C ℤ] [HasShift E ℤ] [Preadditive C] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated C] [Pretriangulated E] (F : C ⥤ E) [F.CommShift ℤ] [F.IsTriangulated]
    (T : Triangle C) (hT : T ∈ distTriang C) (h : IsZero (F.obj T.obj₃)) :
    IsIso (F.map T.mor₁) :=
  (Triangle.isZero₃_iff_isIso₁ _ (F.map_distinguished T hT)).1 h

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- `Xₙ ⟶ X` is quasi-compact, being a closed immersion. -/
theorem isQuasiCompact_spaceProjection (n : ℕ) :
    IsQuasiCompact D.B (limitBase D.system) D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom :=
  isQuasiCompact_of_isClosedImmersion D.B (limitBase D.system) D.containsLimitBase _
    (D.stage n).2 D.X.left.2
    (isClosedImmersion_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective n)

/-- `Xₙ ⟶ X` is quasi-separated, being a closed immersion. -/
theorem isQuasiSeparated_spaceProjection (n : ℕ) :
    IsQuasiSeparated D.B (limitBase D.system) D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom :=
  isQuasiSeparated_of_isClosedImmersion D.B (limitBase D.system) D.containsLimitBase
    ((isClosedImmersion_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective n))

end SeparatedDerivedExistenceSystem

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})
  (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).FullSubcategory)
  (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)

/-- **The cone of `τₙ : Lpₙ^* K ⟶ Kₙ` has quasi-coherent cohomology sheaves**: `Lpₙ^* K` does
(Stacks 08F4) and `Kₙ`, being pseudo-coherent, does (Stacks 08JL). -/
theorem isQuasicoherent_cone_coheratorLimitPullbackMap (n : ℕ)
    (T : Triangle (derivedCategoryAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
    (hT : T ∈ distTriang _)
    (h₁ : T.obj₁ = (D.stageDerivedPullback n).obj
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
        (D.coheratorLimit DQ)))
    (h₂ : T.obj₂ = D.K n) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (ringedSiteAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).O))) T.obj₃ := by
  let P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedSiteAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).O))
  have hP : WeakSerre.IsWeakSerre P :=
    @WeakSerre.isWeakSerre_of_isWeakSerreClass _ _
      (modulesAbelianSmallEtale D.B (limitBase D.system) D.containsLimitBase (D.stage n).1
        (D.stage n).2) _
      (quasicoherentSheaves_isWeakSerreClass_schemeUniverse D.B (limitBase D.system)
        D.containsLimitBase (D.stage n).1 (D.stage n).2)
  have : (DerivedCategoryB.derivedCategoryB P).IsTriangulated :=
    DerivedCategoryB.derivedCategoryB_isTriangulated P hP
  have : (DerivedCategoryB.derivedCategoryB P).IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms P hP
  refine ObjectProperty.ext_of_isTriangulatedClosed₃ _ T hT ?_ ?_
  · rw [h₁]
    exact derivedQuasicoherent_smallEtaleDerivedModulePullback D.B (limitBase D.system)
      D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) _
      (D.coheratorLimit DQ).property
  · rw [h₂]
    exact fun q => D.isQuasicoherentOnSite_homology_K n q

end SeparatedDerivedExistenceSystem

end AlgebraicGeometry.Space
