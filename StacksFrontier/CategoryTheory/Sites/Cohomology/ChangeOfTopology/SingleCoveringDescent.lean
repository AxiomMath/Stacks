module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BoundedBelowComparisonEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CohomologyOverAnObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedUnitIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DescentOfCohomologyClasses
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.VanishingConditionInduction
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeEdge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.HypercohomologyDevissage

/-!
# Descent of cohomology classes along a single covering arrow

In the situation of Stacks 0EZ3 assume the vanishing condition `(V_n)`. This file carries out
the closing argument of the proof of Stacks 0EZE.

## Main results

* `Stacks.ComparingTopologies.exists_homology_derivedCohomologyComparison_eq_of_triangle`: let
  `ε_*ℱ → K → L → ε_*ℱ[1]`, or more generally any distinguished triangle `M → K → L → M[1]` of
  `D⁺(C_{τ'}/Y)`, have its third vertex `L` concentrated in degrees `[0, n]` with cohomology in
  `𝒜'_Y`. A class of `H^{n+1}_τ(Y, ε_Y^{-1}M)` which dies in `H^{n+1}_τ(Y, ε_Y^{-1}K)` comes from
  `H^{n+1}_{τ'}(Y, M)` under the change-of-topology comparison.

## The argument

The comparison is `RΓ_{τ'}` applied to the derived unit `u : 𝟭 ⟶ Rε_{Y,*} ∘ ε_Y^{-1}`, read
through the identification `RΓ_{τ'} ∘ Rε_{Y,*} ≅ RΓ_τ` of Stacks 0D6H. The unit commutes with the
shift, so it is a morphism from the triangle to its image under `Rε_{Y,*} ∘ ε_Y^{-1}`, and the
lifting lemma `Stacks.Cohomology.exists_hypercohomology_map_hom₁_eq` applies: it asks for
surjectivity of `H^n_{τ'}(Y, u_L)`, which is the dévissage of Stacks 0EZB
(`isIso_homology_derivedComparisonUnit_of_bounded`) followed by
`Stacks.Cohomology.isIso_hypercohomologyFunctor_map_of_isIso_of_mono_homologyFunctor_map`.

## References

* [Stacks Project, Tag 0EZE](https://stacks.math.columbia.edu/tag/0EZE)
* [Stacks Project, Tag 0EZB](https://stacks.math.columbia.edu/tag/0EZB)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus
attribute [local instance] commShiftMapDerivedCategoryPlus
attribute [local instance] commShiftMapDerivedCategoryPlusFactorsh

/-- The derived unit `u : 𝟭 ⟶ Rε_{Y,*} ∘ ε_Y^{-1}` as a morphism from a triangle to its image
under `Rε_{Y,*} ∘ ε_Y^{-1}`; it is one because `u` commutes with the shift. -/
def derivedComparisonUnitTriangleHom (S : CohomologyComparison C) (Y : C)
    (T : Triangle (DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck Y))) :
    T ⟶ ((abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).mapDerivedCategoryPlus ⋙
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine Y).rightDerivedFunctorPlus).mapTriangle.obj T where
  hom₁ := (derivedComparisonUnit S Y).app T.obj₁
  hom₂ := (derivedComparisonUnit S Y).app T.obj₂
  hom₃ := (derivedComparisonUnit S Y).app T.obj₃
  comm₁ := (derivedComparisonUnit S Y).naturality T.mor₁
  comm₂ := (derivedComparisonUnit S Y).naturality T.mor₂
  comm₃ := by
    set F := (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).mapDerivedCategoryPlus ⋙
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine Y).rightDerivedFunctorPlus
    have hnat : T.mor₃ ≫ (derivedComparisonUnit S Y).app (T.obj₁⟦(1 : ℤ)⟧) =
        (derivedComparisonUnit S Y).app T.obj₃ ≫ F.map T.mor₃ :=
      (derivedComparisonUnit S Y).naturality T.mor₃
    have hcs := NatTrans.shift_app_comm (derivedComparisonUnit S Y) (1 : ℤ) T.obj₁
    change T.mor₃ ≫ ((derivedComparisonUnit S Y).app T.obj₁)⟦(1 : ℤ)⟧' =
      (derivedComparisonUnit S Y).app T.obj₃ ≫ F.map T.mor₃ ≫
        (F.commShiftIso (1 : ℤ)).hom.app T.obj₁
    rw [← Category.assoc, ← hnat, Category.assoc, ← hcs]
    simp

/-- **The closing step of Stacks 0EZE, in the derived category.** Assume `(V_n)`. Let
`M → K → L → M[1]` be a distinguished triangle in `D⁺(C_{τ'}/Y)` whose third vertex `L` is
concentrated in degrees `[0, n]` with all its cohomology sheaves in `𝒜'_Y`. Then every class of
`H^{n+1}_τ(Y, ε_Y^{-1}M)` which dies in `H^{n+1}_τ(Y, ε_Y^{-1}K)` is the image of a class of
`H^{n+1}_{τ'}(Y, M)` under the change-of-topology comparison
`Stacks.ComparingTopologies.derivedCohomologyComparison`. -/
theorem exists_homology_derivedCohomologyComparison_eq_of_triangle (S : CohomologyComparison C)
    (n : ℕ) (hV : S.vanishingCondition n) (Y : C)
    (T : Triangle (DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck Y)))
    (hT : T ∈ distTriang _) [T.obj₃.IsGE 0] [T.obj₃.IsLE (n : ℤ)]
    (hL : ∀ i : ℤ, S.weakSerre Y ((DerivedCategory.Plus.homologyFunctor _ i).obj T.obj₃))
    (ξ : (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).obj
      ((globalSectionsOver S.fineCoverage.toGrothendieck Y).rightDerivedFunctorPlus.obj
        ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
          Y).mapDerivedCategoryPlus.obj T.obj₁)))
    (hξ : (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
      ((globalSectionsOver S.fineCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map
        ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
          Y).mapDerivedCategoryPlus.map T.mor₁)) ξ = 0) :
    ∃ β : (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).obj
        ((globalSectionsOver S.coarseCoverage.toGrothendieck Y).rightDerivedFunctorPlus.obj
          T.obj₁),
      (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
        ((derivedCohomologyComparison S Y).app T.obj₁) β = ξ := by
  have hE := isTriangulated_abelianComparisonPullback_mapDerivedCategoryPlus S Y
  have hT' := ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
      Y).mapDerivedCategoryPlus ⋙ (abelianComparisonPushforward S.fineCoverage
        S.coarseCoverage S.coarse_le_fine Y).rightDerivedFunctorPlus).map_distinguished T hT
  -- `H^n_{τ'}(Y, u_L)` is surjective, by the dévissage of Stacks 0EZB
  have hiso := isIso_homology_derivedComparisonUnit_of_bounded S n hV Y T.obj₃ hL
  have hmono : Mono ((DerivedCategory.Plus.homologyFunctor _ ((n : ℤ) + 1)).map
      ((derivedComparisonUnit S Y).app T.obj₃)) :=
    (DerivedCategory.Plus.isZero_homology_of_isLE T.obj₃ (n : ℤ) ((n : ℤ) + 1)
      (by omega)).mono _
  have hepi :=
    Stacks.Cohomology.isIso_hypercohomologyFunctor_map_of_isIso_of_mono_homologyFunctor_map
    (S.coarseCoverage.toGrothendieck.over Y) (Over.mk (𝟙 Y))
    ((derivedComparisonUnit S Y).app T.obj₃) (n : ℤ) hiso hmono (n : ℤ) le_rfl
  -- the class, moved to the coarse side through Stacks 0D6H
  let x := (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
    ((derivedGlobalSectionsComparisonPlusIso S Y).inv.app
      ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
        Y).mapDerivedCategoryPlus.obj T.obj₁)) ξ
  have hx0 : (Stacks.Cohomology.hypercohomologyFunctor (S.coarseCoverage.toGrothendieck.over Y)
      (Over.mk (𝟙 Y)) ((n : ℤ) + 1)).map
      (((abelianComparisonPullback S.fineCoverage S.coarseCoverage
          Y).mapDerivedCategoryPlus ⋙ (abelianComparisonPushforward S.fineCoverage
            S.coarseCoverage S.coarse_le_fine Y).rightDerivedFunctorPlus).mapTriangle.obj
              T).mor₁ x = 0 := by
    have hnat := (derivedGlobalSectionsComparisonPlusIso S Y).inv.naturality
      ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
        Y).mapDerivedCategoryPlus.map T.mor₁)
    have h := congrArg (fun g => (DerivedCategory.Plus.homologyFunctor Ab.{max u v}
      ((n : ℤ) + 1)).map g ξ) hnat
    simp only [Functor.map_comp, ConcreteCategory.comp_apply, hξ, map_zero] at h
    exact h.symm
  obtain ⟨β, hβ⟩ := Stacks.Cohomology.exists_hypercohomology_map_hom₁_eq
    (S.coarseCoverage.toGrothendieck.over Y) (Over.mk (𝟙 Y)) hT'
    (derivedComparisonUnitTriangleHom S Y T) (n : ℤ) ((n : ℤ) + 1) rfl
    (@IsIso.epi_of_iso _ _ _ _ _ hepi) x hx0
  refine ⟨β, ?_⟩
  have hβ' : (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
      ((globalSectionsOver S.coarseCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map
        ((derivedComparisonUnit S Y).app T.obj₁)) β = x := hβ
  have hdef : (derivedCohomologyComparison S Y).app T.obj₁ =
      (globalSectionsOver S.coarseCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map
          ((derivedComparisonUnit S Y).app T.obj₁) ≫
        (derivedGlobalSectionsComparisonPlusIso S Y).hom.app
          ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
            Y).mapDerivedCategoryPlus.obj T.obj₁) := by
    simp [derivedCohomologyComparison]
  rw [hdef, Functor.map_comp, ConcreteCategory.comp_apply, hβ']
  show ((DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
      ((derivedGlobalSectionsComparisonPlusIso S Y).inv.app _) ≫
    (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
      ((derivedGlobalSectionsComparisonPlusIso S Y).hom.app _)) ξ = ξ
  rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rfl

/-- The homology of a single object `X[0]` of `D⁺(A)` vanishes in nonzero degrees. -/
private theorem isZero_homology_single_of_ne {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (X : A) {i : ℤ} (hi : i ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor A i).obj
      ((DerivedCategory.Plus.singleFunctor A 0).obj X)) :=
  hi.lt_or_gt.elim (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 i)
    (DerivedCategory.Plus.isZero_homology_of_isLE _ 0 i)

/-- The canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])` is invertible on `H^0` for a left exact `P`. -/
private theorem isIso_homology_zero_singleDerivedUnit_aux {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] (X : A) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map
      (Stacks.DerivedIndexing.singleDerivedUnit P 0 X)) := by
  have hu₀ := (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
    P P.rightDerivedFunctorPlus P.rightDerivedFunctorPlusUnit).2.2.2 inferInstance X
  simp only [Stacks.DerivedIndexing.singleDerivedUnit_zero,
    Stacks.DerivedIndexing.rightDerivedPlusUnitSingle, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp]
  infer_instance

/-- On cohomology sheaves, the derived change-of-topology inverse image is the inverse image of
the cohomology sheaves. -/
def homologyAbelianComparisonPullbackIso (S : CohomologyComparison C) (Y : C) (i : ℤ)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck Y)) :
    (DerivedCategory.Plus.homologyFunctor _ i).obj
        ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
          Y).mapDerivedCategoryPlus.obj K) ≅
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).obj
        ((DerivedCategory.Plus.homologyFunctor _ i).obj K) := by
  change (DerivedCategory.homologyFunctor _ i).obj
      ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
        Y).mapDerivedCategory.obj K.obj) ≅
    (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).obj
      ((DerivedCategory.homologyFunctor _ i).obj K.obj)
  exact ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
    Y).mapDerivedCategoryHomologyIso i).app K.obj

/-- **The closing step of Stacks 0EZE, for a map out of a single sheaf.** Assume `(V_n)`, let
`ℱ` be an abelian sheaf on `C_τ/Y` with `ε_{Y,*}ℱ` in `𝒜'_Y`, and let `w : ℱ[0] ⟶ N` be a map in
`D⁺(C_τ/Y)` such that the cohomology sheaves of `Rε_{Y,*}N` in degrees `0, …, n` lie in `𝒜'_Y`
and the composite `ε_{Y,*}ℱ ⟶ H^0(Rε_{Y,*}N)` is injective. Then every class of
`H^{n+1}_τ(Y, ℱ)` which dies in `H^{n+1}_τ(Y, N)` is the image under the canonical comparison
`H^{n+1}_{τ'}(Y, ε_{Y,*}ℱ) ⟶ H^{n+1}_τ(Y, ℱ)`, read in the derived category: `RΓ_{τ'}` applied
to `(ε_{Y,*}ℱ)[0] ⟶ Rε_{Y,*}(ℱ[0])` followed by Stacks 0D6H.

The triangle is `(ε_{Y,*}ℱ)[0] ⟶ τ_{≤n}Rε_{Y,*}N ⟶ L`; its image under `ε_Y^{-1}` maps to
`ℱ[0] ⟶ N` through the counit of `ε_Y^{-1} ⊣ Rε_{Y,*}`, which is invertible, and the closing
step `exists_homology_derivedCohomologyComparison_eq_of_triangle` applies to it. -/
theorem exists_homology_singleDerivedPullback_eq_of_map (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (Y : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over Y) Ab.{max u v})
    (hF : S.weakSerre Y ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine Y).obj F))
    (N : DerivedCategory.Plus (AbelianSheaves S.fineCoverage.toGrothendieck Y))
    (w : (DerivedCategory.Plus.singleFunctor _ 0).obj F ⟶ N)
    (h₁ : ∀ i : ℤ, 0 ≤ i → i ≤ n → S.weakSerre Y ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine Y).rightDerivedFunctorPlus.obj N)))
    [((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine Y).rightDerivedFunctorPlus.obj N).IsGE 0]
    (h₂ : Mono ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (Stacks.DerivedIndexing.singleDerivedUnit (abelianComparisonPushforward S.fineCoverage
          S.coarseCoverage S.coarse_le_fine Y) 0 F ≫
        (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine Y).rightDerivedFunctorPlus.map w)))
    (ξ : (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).obj
      ((globalSectionsOver S.fineCoverage.toGrothendieck Y).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (hξ : (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
      ((globalSectionsOver S.fineCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map w) ξ = 0) :
    ∃ β : (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).obj
        ((globalSectionsOver S.coarseCoverage.toGrothendieck Y).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
              S.coarse_le_fine Y).obj F))),
      (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
        ((globalSectionsOver S.coarseCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map
            (Stacks.DerivedIndexing.singleDerivedUnit (abelianComparisonPushforward
              S.fineCoverage S.coarseCoverage S.coarse_le_fine Y) 0 F) ≫
          (derivedGlobalSectionsComparisonPlusIso S Y).hom.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) β = ξ := by
  let push := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine Y
  let pull := abelianComparisonPullback S.fineCoverage S.coarseCoverage Y
  let σ := Stacks.DerivedIndexing.singleDerivedUnit push 0 F
  let adj := derivedComparisonAdjunction S Y
  let t := DerivedCategory.Plus.TStructure.t (C := AbelianSheaves S.coarseCoverage.toGrothendieck Y)
  have hsingle : ((DerivedCategory.Plus.singleFunctor _ 0).obj (push.obj F)).IsLE (n : ℤ) :=
    (DerivedCategory.Plus.isLE_iff _ _).2 fun i hi ↦
      DerivedCategory.Plus.isZero_homology_of_isLE _ 0 i (by omega)
  let u' := t.liftTruncLE (σ ≫ push.rightDerivedFunctorPlus.map w) (n : ℤ)
  have hu' : u' ≫ (t.truncLEι (n : ℤ)).app (push.rightDerivedFunctorPlus.obj N) =
      σ ≫ push.rightDerivedFunctorPlus.map w := t.liftTruncLE_ι _ _
  obtain ⟨L, g, h, hT⟩ := distinguished_cocone_triangle u'
  let H (i : ℤ) := DerivedCategory.Plus.homologyFunctor
    (AbelianSheaves S.coarseCoverage.toGrothendieck Y) i
  have hT₁ : ∀ i : ℤ, i ≠ 0 →
      IsZero ((H i).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj (push.obj F))) :=
    fun i hi ↦ isZero_homology_single_of_ne _ hi
  have hK'zero : ∀ i : ℤ, (n : ℤ) < i →
      IsZero ((H i).obj ((t.truncLE (n : ℤ)).obj (push.rightDerivedFunctorPlus.obj N))) :=
    fun i hi ↦ DerivedCategory.Plus.isZero_homology_truncLE_obj _ i _ hi
  have hK'iso : ∀ i : ℤ, i ≤ (n : ℤ) →
      IsIso ((H i).map ((t.truncLEι (n : ℤ)).app (push.rightDerivedFunctorPlus.obj N))) :=
    fun i hi ↦ DerivedCategory.Plus.isIso_homologyMap_truncLEι_app _ i (n : ℤ) hi
  have hK'neg : ∀ i : ℤ, i < 0 →
      IsZero ((H i).obj ((t.truncLE (n : ℤ)).obj (push.rightDerivedFunctorPlus.obj N))) := by
    intro i hi
    have := hK'iso i (by omega)
    exact (DerivedCategory.Plus.isZero_homology_of_isGE (push.rightDerivedFunctorPlus.obj N) 0 i
      hi).of_iso (asIso ((H i).map ((t.truncLEι (n : ℤ)).app (push.rightDerivedFunctorPlus.obj N))))
  have hwsc : (S.weakSerre Y).IsWeakSerreClass := S.weakSerreClass Y
  have hK'mem : ∀ i : ℤ, i ≤ (n : ℤ) →
      S.weakSerre Y ((H i).obj ((t.truncLE (n : ℤ)).obj (push.rightDerivedFunctorPlus.obj N))) := by
    intro i hi
    rcases lt_or_ge i 0 with hneg | hnn
    · exact (S.weakSerre Y).prop_of_isZero (hK'neg i hneg)
    · have := hK'iso i hi
      exact (S.weakSerre Y).prop_of_iso
        (asIso ((H i).map ((t.truncLEι (n : ℤ)).app (push.rightDerivedFunctorPlus.obj N)))).symm
        (h₁ i hnn hi)
  have hmono₀ : Mono ((H 0).map u') := by
    have : Mono ((H 0).map u' ≫ (H 0).map ((t.truncLEι (n : ℤ)).app
        (push.rightDerivedFunctorPlus.obj N))) := by
      rw [← Functor.map_comp, hu']
      exact h₂
    exact mono_of_mono _ ((H 0).map ((t.truncLEι (n : ℤ)).app (push.rightDerivedFunctorPlus.obj N)))
  have hLGE : L.IsGE 0 := by
    have := DerivedCategory.Plus.isGE_three_of_epi_of_mono_homologyMap_mor₁
      (Triangle.mk u' g h) hT (-1)
      (fun j hj ↦ (hK'neg j (by omega)).epi _)
      (fun j hj ↦ by
        rcases eq_or_lt_of_le hj with hj' | hj'
        · rw [show j = 0 by omega]
          exact hmono₀
        · exact (hT₁ j (by omega)).mono _)
    simpa using this
  have hLzero : ∀ i : ℤ, (n : ℤ) < i → IsZero ((H i).obj L) := by
    intro i hi
    have hex := (DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₃
      (Triangle.mk u' g h) hT i (i + 1) rfl
    exact hex.isZero_of_both_zeros ((hK'zero i hi).eq_of_src _ _)
      ((hT₁ (i + 1) (by omega)).eq_of_tgt _ _)
  have hLLE : L.IsLE (n : ℤ) := (DerivedCategory.Plus.isLE_iff _ _).2 hLzero
  have hL : ∀ i : ℤ, S.weakSerre Y ((DerivedCategory.Plus.homologyFunctor _ i).obj L) := by
    intro i
    rcases lt_or_ge i 0 with hneg | hnn
    · exact (S.weakSerre Y).prop_of_isZero (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 i hneg)
    rcases lt_or_ge (n : ℤ) i with hbig | hle
    · exact (S.weakSerre Y).prop_of_isZero (hLzero i hbig)
    rcases eq_or_lt_of_le hnn with h0 | hpos
    · subst h0
      have e₀ := (DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₂
        (Triangle.mk u' g h) hT 0
      have e₁ := (DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₃
        (Triangle.mk u' g h) hT 0 1 rfl
      have e₂ := (DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₁
        (Triangle.mk u' g h) hT 0 1 rfl
      refine ObjectProperty.prop_mid_of_exact₄ (fun S' hS' h₀ h₁ h₃ h₄ ↦
          (S.weakSerre Y).prop_obj₂_of_exact S' hS' h₀ h₁ h₃ h₄) _ _ _ e₀ e₁ e₂
        ?_ (hK'mem 0 (by omega)) ((S.weakSerre Y).prop_of_isZero (hT₁ 1 (by omega))) ?_
      · exact (S.weakSerre Y).prop_of_iso
          ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := AbelianSheaves
            S.coarseCoverage.toGrothendieck Y) 0).app (push.obj F)).symm hF
      · rcases lt_or_ge (n : ℤ) 1 with hn | hn
        · exact (S.weakSerre Y).prop_of_isZero (hK'zero 1 hn)
        · exact hK'mem 1 hn
    · have := DerivedCategory.Plus.isIso_homologyMap_mor₂_of_isLE₁ (Triangle.mk u' g h) hT i 0
        (inferInstanceAs (((DerivedCategory.Plus.singleFunctor _ 0).obj (push.obj F)).IsLE 0)) hpos
      exact (S.weakSerre Y).prop_of_iso (@asIso _ _ _ _ ((H i).map g) this) (hK'mem i hle)
  let e' := pull.mapDerivedCategoryPlus.map σ ≫ adj.counit.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  have hcounit := isIso_derivedComparisonAdjunction_counit_app S Y
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  have hσ₀ : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map σ) :=
    isIso_homology_zero_singleDerivedUnit_aux push F
  have he' : IsIso e' := by
    suffices IsIso (pull.mapDerivedCategoryPlus.map σ) from IsIso.comp_isIso
    apply (isIso_iff_of_reflects_iso _ DerivedCategory.Plus.ι).1
    rw [DerivedCategory.isIso_iff]
    intro i
    show IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
      (pull.mapDerivedCategoryPlus.map σ))
    rcases eq_or_ne i 0 with rfl | hi
    · exact DerivedCategory.Plus.isIso_homology_mapDerivedCategoryPlus_map pull σ 0 hσ₀
    · apply IsZero.isIso
      · exact (pull.map_isZero (hT₁ i hi)).of_iso
          (homologyAbelianComparisonPullbackIso S Y i _)
      · exact (isZero_homology_single_of_ne F hi).of_iso
          (asIso ((DerivedCategory.Plus.homologyFunctor _ i).map
            (adj.counit.app ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))
  have hue : (derivedComparisonUnit S Y).app _ ≫ push.rightDerivedFunctorPlus.map e' = σ := by
    rw [← derivedComparisonAdjunction_unit]
    exact (adj.homEquiv_unit _ _ e').symm.trans
      ((adj.homEquiv _ _).apply_symm_apply σ |>.trans rfl)
  let c := pull.mapDerivedCategoryPlus.map ((t.truncLEι (n : ℤ)).app
    (push.rightDerivedFunctorPlus.obj N)) ≫ adj.counit.app N
  have hc : pull.mapDerivedCategoryPlus.map u' ≫ c = e' ≫ w := by
    show pull.mapDerivedCategoryPlus.map u' ≫ pull.mapDerivedCategoryPlus.map
        ((t.truncLEι (n : ℤ)).app (push.rightDerivedFunctorPlus.obj N)) ≫ adj.counit.app N =
      (pull.mapDerivedCategoryPlus.map σ ≫
        adj.counit.app ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫ w
    rw [← Category.assoc, ← Functor.map_comp, hu', Functor.map_comp, Category.assoc,
      Category.assoc]
    exact congrArg (fun z => pull.mapDerivedCategoryPlus.map σ ≫ z) (adj.counit.naturality w)
  have hcmono : Mono ((DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
      ((globalSectionsOver S.fineCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map c)) := by
    have hcN := isIso_derivedComparisonAdjunction_counit_app S Y N
    have hci : ∀ j : ℤ, j ≤ (n : ℤ) →
        IsIso ((DerivedCategory.Plus.homologyFunctor _ j).map c) := by
      intro j hj
      have := DerivedCategory.Plus.isIso_homology_mapDerivedCategoryPlus_map pull
        ((t.truncLEι (n : ℤ)).app (push.rightDerivedFunctorPlus.obj N)) j (hK'iso j hj)
      simp only [c, Functor.map_comp]
      infer_instance
    obtain ⟨M, g', h', hT'⟩ := distinguished_cocone_triangle c
    have hMGE : M.IsGE ((n : ℤ) + 1) :=
      DerivedCategory.Plus.isGE_three_of_epi_of_mono_homologyMap_mor₁
        (Triangle.mk c g' h') hT' (n : ℤ)
        (fun j hj ↦ by
          have := hci j hj
          exact (inferInstance : Epi ((DerivedCategory.Plus.homologyFunctor _ j).map c)))
        (fun j hj ↦ by
          rcases eq_or_lt_of_le hj with hj' | hj'
          · subst hj'
            apply IsZero.mono
            exact (pull.map_isZero (hK'zero ((n : ℤ) + 1) (by omega))).of_iso
              (homologyAbelianComparisonPullbackIso S Y _ _)
          · have := hci j (by omega)
            exact (inferInstance : Mono ((DerivedCategory.Plus.homologyFunctor _ j).map c)))
    rw [show (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
        ((globalSectionsOver S.fineCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map c) =
      (Stacks.Cohomology.hypercohomologyFunctor (S.fineCoverage.toGrothendieck.over Y)
        (Over.mk (𝟙 Y)) ((n : ℤ) + 1)).map (Triangle.mk c g' h').mor₁ from rfl,
      Stacks.Cohomology.mono_hypercohomology_map_mor₁_iff _ _ _ hT' (n : ℤ) ((n : ℤ) + 1) rfl]
    exact (Stacks.Cohomology.isZero_hypercohomology_of_isGE _ _ M ((n : ℤ) + 1) (n : ℤ)
      (by omega)).eq_of_src _ _
  let ξ' := (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
    ((globalSectionsOver S.fineCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map
      (inv e')) ξ
  have hξ' : (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
      ((globalSectionsOver S.fineCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map
        (pull.mapDerivedCategoryPlus.map (Triangle.mk u' g h).mor₁)) ξ' = 0 := by
    apply (AddCommGrpCat.mono_iff_injective _).1 hcmono
    rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    show (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
      ((globalSectionsOver S.fineCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map
        (pull.mapDerivedCategoryPlus.map u' ≫ c)) ξ' = 0
    rw [hc]
    simp only [ξ', ← ConcreteCategory.comp_apply, ← Functor.map_comp, IsIso.inv_hom_id_assoc]
    exact hξ
  have : (Triangle.mk u' g h).obj₃.IsGE 0 := hLGE
  have : (Triangle.mk u' g h).obj₃.IsLE (n : ℤ) := hLLE
  obtain ⟨β, hβ⟩ := exists_homology_derivedCohomologyComparison_eq_of_triangle S n hV Y
    (Triangle.mk u' g h) hT hL ξ' hξ'
  refine ⟨β, ?_⟩
  have hdef : (derivedCohomologyComparison S Y).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (push.obj F)) ≫
      (globalSectionsOver S.fineCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map e' =
      (globalSectionsOver S.coarseCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map σ ≫
        (derivedGlobalSectionsComparisonPlusIso S Y).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F) := by
    have hn := (derivedGlobalSectionsComparisonPlusIso S Y).hom.naturality e'
    simp only [Functor.comp_map] at hn
    simp only [derivedCohomologyComparison, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp, Category.assoc]
    rw [← hn, ← Category.assoc, ← Functor.map_comp, hue]
    rfl
  rw [← hdef, Functor.map_comp, ConcreteCategory.comp_apply]
  show (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
    ((globalSectionsOver S.fineCoverage.toGrothendieck Y).rightDerivedFunctorPlus.map e')
      ((DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
        ((derivedCohomologyComparison S Y).app (Triangle.mk u' g h).obj₁) β) = ξ
  rw [hβ]
  simp only [ξ', ← ConcreteCategory.comp_apply, ← Functor.map_comp, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- The canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])` is invertible on `H^0` for a left exact `P`. -/
theorem isIso_homology_zero_singleDerivedUnit {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] (X : A) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map
      (Stacks.DerivedIndexing.singleDerivedUnit P 0 X)) := by
  exact isIso_homology_zero_singleDerivedUnit_aux P X

section BaseChangeUnit

variable (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y) [Limits.HasPullbacksAlong f]

/-- Base change along `f` is continuous for the localized topologies, being right adjoint to
the cocontinuous composition with `f`. -/
theorem overPullback_isContinuous : (Over.pullback f).IsContinuous (J.over Y) (J.over X) :=
  (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous _ _

/-- The unit `ℱ ⟶ f_*f^{-1}ℱ` of restriction along `f` and base change along `f`, on abelian
sheaves on `C_J/Y`; its value over `U` is the restriction to `U ×_Y X`. -/
def baseChangeUnit :
    letI := overPullback_isContinuous J f
    𝟭 (Sheaf (J.over Y) Ab.{max u v}) ⟶ overPullback J f ⋙
      (Over.pullback f).sheafPushforwardContinuous Ab.{max u v} (J.over Y) (J.over X) :=
  letI := overPullback_isContinuous J f
  ((Over.mapPullbackAdj f).sheafPushforwardContinuous (E := Ab.{max u v}) (J.over X)
    (J.over Y)).unit

/-- If the single arrow `f` is a covering, the unit `ℱ ⟶ f_*f^{-1}ℱ` is a monomorphism: over
`U` it is the restriction along `U ×_Y X ⟶ U`, which is again a covering. -/
theorem mono_baseChangeUnit_app (K : Precoverage C) [K.IsStableUnderBaseChange]
    (hcov : Presieve.singleton f ∈ K Y) (F : Sheaf (K.toGrothendieck.over Y) Ab.{max u v}) :
    Mono ((baseChangeUnit K.toGrothendieck f).app F) := by
  refine (sheafToPresheaf _ _).mono_of_mono_map ?_
  suffices hU : ∀ U, Mono (((sheafToPresheaf (K.toGrothendieck.over Y) Ab.{max u v}).map
      ((baseChangeUnit K.toGrothendieck f).app F)).app U) from
    NatTrans.mono_of_mono_app _
  intro U
  rw [AddCommGrpCat.mono_iff_injective]
  intro a b hab
  have hE := (isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose (K.toGrothendieck.over Y) (forget Ab.{max u v})).obj F).property
  let c := (Over.mapPullbackAdj f).counit.app U.unop
  have hcov' : Sieve.generate (Presieve.singleton c) ∈ (K.toGrothendieck.over Y) U.unop := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    refine K.toGrothendieck.superset_covering ?_ (K.generate_mem_toGrothendieck
      (by
        simpa only [Presieve.ofArrows_pUnit] using K.mem_coverings_of_isPullback
          (ι := PUnit.{max u v + 1}) (fun _ => f)
          (by simpa only [Presieve.ofArrows_pUnit] using hcov) U.unop.hom
          (fun _ => Limits.pullback.fst U.unop.hom f) (fun _ => Limits.pullback.snd U.unop.hom f)
          (fun _ => IsPullback.of_hasPullback _ _)))
    refine Sieve.generate_mono ?_
    rintro _ _ ⟨⟩
    exact ⟨_, c, 𝟙 _, ⟨⟩, by simp [c]⟩
  refine (hE.isSeparated _ hcov').ext ?_
  rintro V _ ⟨W, k, l, ⟨⟩, rfl⟩
  show F.obj.map (k ≫ c).op a = F.obj.map (k ≫ c).op b
  rw [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact congrArg _ hab

end BaseChangeUnit

/-- **The closing step of Stacks 0EZE.** Assume `(V_n)`. Let `f : X ⟶ Y` be an arrow of the
distinguished class which by itself is a covering for the finer topology, and `ℱ` a sheaf of
`𝒜_Y`. A class `ξ ∈ H^{n+1}_τ(Y, ℱ)` which restricts to zero over `X` is the image of a class of
`H^{n+1}_{τ'}(Y, ε_{Y,*}ℱ)` under the change-of-topology comparison of Stacks 0EZC.

This is `exists_homology_singleDerivedPullback_eq_of_map` for the map
`ℱ[0] ⟶ (f_*f^{-1}ℱ)[0] ⟶ R(f_*f^{-1})(ℱ[0])`: its derived direct images to the coarser site have
their cohomology in `𝒜'_Y` through degree `n` by Stacks 0EZ7 and the vanishing condition, the
unit `ℱ ⟶ f_*f^{-1}ℱ` is injective because `f` is a covering, and on cohomology over `Y` the map
is the restriction to `X` read through the edge morphism of `(f_*f^{-1}, Γ(Y, -))`. -/
theorem exists_cohomologyComparison_eq_of_restriction_eq_zero (S : CohomologyComparison C)
    (n : ℕ) (hV : S.vanishingCondition n) {X Y : C} (f : X ⟶ Y) (hf : S.morphismProperty f)
    (hcov : Presieve.singleton f ∈ S.fineCoverage Y)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over Y) Ab.{max u v}) (hF : S.fineWeakSerre Y F)
    (ξ : Stacks.sheafCohomology (S.fineCoverage.toGrothendieck.over Y) F (Over.mk (𝟙 Y)) (n + 1))
    (hξ : Stacks.sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over Y)
      (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 Y)) (n + 1) F ξ = 0) :
    ∃ η, (cohomologyComparison S Y (n + 1)).app F η = ξ := by
  have : Limits.HasPullbacksAlong f := fun {Z} g => by
    obtain ⟨Q, a, b, h, _⟩ := S.morphismProperty_baseChange f hf g
    exact h.flip.hasPullback
  let Jf := S.fineCoverage.toGrothendieck
  let := overPullback_isContinuous Jf f
  let push := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine Y
  let Γf := globalSectionsOver Jf Y
  let Γc := globalSectionsOver S.coarseCoverage.toGrothendieck Y
  let adj := (Over.mapPullbackAdj f).sheafPushforwardContinuous (E := Ab.{max u v})
    (Jf.over X) (Jf.over Y)
  let P' := (Over.pullback f).sheafPushforwardContinuous Ab.{max u v} (Jf.over Y) (Jf.over X)
  let Φ := overPullback Jf f ⋙ P'
  have : P'.IsRightAdjoint := adj.isRightAdjoint
  have : P'.Additive := Functor.additive_of_preserves_binary_products _
  have : P'.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  have : PreservesFiniteLimits Φ := inferInstance
  let η := baseChangeUnit Jf f
  let F0 := (DerivedCategory.Plus.singleFunctor (AbelianSheaves Jf Y) 0).obj F
  let N := Φ.rightDerivedFunctorPlus.obj F0
  let w := (DerivedCategory.Plus.singleFunctor (AbelianSheaves Jf Y) 0).map (η.app F) ≫
    Stacks.DerivedIndexing.singleDerivedUnit Φ 0 F
  have hF' : S.weakSerre Y (push.obj F) :=
    (CohomologyComparison.fineWeakSerre_iff_weakSerre_pushforward S Y F).1 hF
  have hNGE : N.IsGE 0 := Functor.isGE_rightDerivedFunctorPlus_obj Φ F0 0
  have hRNGE : (push.rightDerivedFunctorPlus.obj N).IsGE 0 :=
    Functor.isGE_rightDerivedFunctorPlus_obj push N 0
  have h₁ : ∀ i : ℤ, 0 ≤ i → i ≤ n → S.weakSerre Y
      ((DerivedCategory.Plus.homologyFunctor _ i).obj (push.rightDerivedFunctorPlus.obj N)) := by
    intro i hi0 hin
    obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
    have hin' : i ≤ n := by omega
    have hcl := (S.weakSerreClass Y).toIsClosedUnderIsomorphisms
    let Jc := S.coarseCoverage.toGrothendieck
    let := overPullback_isContinuous Jc f
    let pushX := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
    let P'c := (Over.pullback f).sheafPushforwardContinuous Ab.{max u v} (Jc.over Y) (Jc.over X)
    have : P'c.IsRightAdjoint := ((Over.mapPullbackAdj f).sheafPushforwardContinuous
      (E := Ab.{max u v}) (Jc.over X) (Jc.over Y)).isRightAdjoint
    have : P'c.Additive := Functor.additive_of_preserves_binary_products _
    let eP : P'c ≅ overPushforward Jc f := Adjunction.rightAdjointUniq
      ((Over.mapPullbackAdj f).sheafPushforwardContinuous (E := Ab.{max u v}) (Jc.over X)
        (Jc.over Y))
      ((Over.map f).sheafAdjunctionCocontinuous Ab.{max u v} (Jc.over X) (Jc.over Y))
    let M := (overPullback Jf f).obj F
    have hM : S.fineWeakSerre X M := CohomologyComparison.fineWeakSerre_overMapPullback S f F hF
    have hM' : S.weakSerre X (pushX.obj M) :=
      (CohomologyComparison.fineWeakSerre_iff_weakSerre_pushforward S X M).1 hM
    -- `R^i P(ε_{X,*} f^{-1} ℱ)` lies in `𝒜'_Y` by Stacks 0EZ7
    have h7 := S.weakSerre_rightDerived_relocalizationPushforward f hf _ hM' i
    -- the derived functor of `P'` agrees with that of `P`
    let eR : (P'c.rightDerived i).obj (pushX.obj M) ≅
        ((overPushforward Jc f).rightDerived i).obj (pushX.obj M) :=
      { hom := (NatTrans.rightDerived eP.hom i).app _
        inv := (NatTrans.rightDerived eP.inv i).app _
        hom_inv_id := by
          rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, eP.hom_inv_id,
            NatTrans.rightDerived_id]
          rfl
        inv_hom_id := by
          rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, eP.inv_hom_id,
            NatTrans.rightDerived_id]
          rfl }
    have hX : ∀ q, 1 ≤ q → q ≤ i → IsZero ((pushX.rightDerived q).obj M) :=
      fun q hq hqi ↦ hV X M hM q hq (hqi.trans hin')
    -- the edge morphism of `(ε_{X,*}, P')` is invertible through degree `n`
    let eE := Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso pushX P'c M i hX
    -- restriction along `f` is exact, so it collapses
    let eC := Stacks.RightDerivedComp.objIso (overPullback Jf f) (injectiveResolution F)
      (fun m hm ↦ Stacks.Cohomology.isZero_rightDerived_obj_of_preservesHomology
        (overPullback Jf f) F m hm) (pushX ⋙ P'c) i
    let eD := (Stacks.DerivedIndexing.rightDerivedIso (Φ ⋙ push) i).app F
    let eT := (DerivedCategory.Plus.homologyFunctor _ (i : ℤ)).mapIso
      ((Stacks.DerivedIndexing.rightDerivedPlusCompIso Φ push).app F0)
    exact hcl.of_iso (eR.symm ≪≫ eE ≪≫ eC.symm ≪≫ eD ≪≫ eT) h7
  have h₂ : Mono ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (Stacks.DerivedIndexing.singleDerivedUnit push 0 F
          ≫ push.rightDerivedFunctorPlus.map w)) := by
    let H₀ := DerivedCategory.Plus.homologyFunctor
      (AbelianSheaves S.coarseCoverage.toGrothendieck Y) 0
    let Hf₀ := DerivedCategory.Plus.homologyFunctor (AbelianSheaves Jf Y) 0
    let σΦ := Stacks.DerivedIndexing.singleDerivedUnit Φ 0 F
    -- naturality of `(Pℱ)[0] ⟶ RP(ℱ[0])` in `ℱ`
    have hnat : Stacks.DerivedIndexing.singleDerivedUnit push 0 F ≫
        push.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (AbelianSheaves Jf Y) 0).map (η.app F)) =
        (DerivedCategory.Plus.singleFunctor _ 0).map (push.map (η.app F)) ≫
          Stacks.DerivedIndexing.singleDerivedUnit push 0 (Φ.obj F) := by
      simp only [Stacks.DerivedIndexing.singleDerivedUnit_zero]
      exact ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle push).naturality
        (η.app F)).symm
    have hfac : Stacks.DerivedIndexing.singleDerivedUnit push 0 F ≫
        push.rightDerivedFunctorPlus.map w =
        (DerivedCategory.Plus.singleFunctor _ 0).map (push.map (η.app F)) ≫
          Stacks.DerivedIndexing.singleDerivedUnit push 0 (Φ.obj F) ≫
            push.rightDerivedFunctorPlus.map σΦ := by
      show _ ≫ push.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaves Jf Y) 0).map (η.app F) ≫ σΦ) = _
      rw [Functor.map_comp, ← Category.assoc, hnat, Category.assoc]
    rw [hfac, Functor.map_comp, Functor.map_comp]
    -- the first factor: the unit `ℱ ⟶ f_*f^{-1}ℱ` is injective
    have hη : Mono (η.app F) :=
      mono_baseChangeUnit_app f S.fineCoverage hcov F
    have h1 : Mono (H₀.map ((DerivedCategory.Plus.singleFunctor _ 0).map (push.map
        (η.app F)))) := by
      have e := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := AbelianSheaves S.coarseCoverage.toGrothendieck Y) 0).hom.naturality
          (push.map (η.app F))
      have : Mono ((DerivedCategory.Plus.singleFunctor _ 0 ⋙ H₀).map (push.map (η.app F)) ≫
          (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
            (C := AbelianSheaves S.coarseCoverage.toGrothendieck Y) 0).hom.app _) := by
        rw [e]
        exact mono_comp _ _
      exact @mono_of_mono _ _ _ _ _ _ ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := AbelianSheaves S.coarseCoverage.toGrothendieck Y) 0).hom.app _) this
    -- the second factor: `H^0` of `(ε_*G)[0] ⟶ Rε_*(G[0])` is invertible
    have h2 := isIso_homology_zero_singleDerivedUnit push (Φ.obj F)
    -- the third factor: the cone of `σΦ` is concentrated in degrees `≥ 1`
    have h3 : IsIso (H₀.map (push.rightDerivedFunctorPlus.map σΦ)) := by
      have hσ := isIso_homology_zero_singleDerivedUnit Φ F
      obtain ⟨Cn, g', h', hT'⟩ := distinguished_cocone_triangle σΦ
      have hGE : Cn.IsGE 1 := by
        have := DerivedCategory.Plus.isGE_three_of_epi_of_mono_homologyMap_mor₁
          (Triangle.mk σΦ g' h') hT' 0
          (fun j hj ↦ by
            rcases eq_or_lt_of_le hj with hj' | hj'
            · subst hj'
              exact (inferInstance : Epi (Hf₀.map σΦ))
            · exact ((DerivedCategory.Plus.isZero_homology_of_isGE N 0 j hj').epi _ : _))
          (fun j hj ↦ by
            rcases eq_or_ne j 0 with rfl | hj'
            · exact (inferInstance : Mono (Hf₀.map σΦ))
            · exact (isZero_homology_single_of_ne _ hj').mono _)
        simpa using this
      have hRGE : (push.rightDerivedFunctorPlus.obj Cn).IsGE 1 :=
        Functor.isGE_rightDerivedFunctorPlus_obj push Cn 1
      exact DerivedCategory.Plus.isIso_homologyMap_mor₁_of_isGE₃
        (push.rightDerivedFunctorPlus.mapTriangle.obj (Triangle.mk σΦ g' h'))
        (push.rightDerivedFunctorPlus.map_distinguished _ hT') 0 1 hRGE (by omega)
    infer_instance
  let ξD := (Stacks.DerivedIndexing.rightDerivedIso Γf (n + 1)).hom.app F ξ
  have hξD : (DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map
      (Γf.rightDerivedFunctorPlus.map w) ξD = 0 := by
    -- the restriction of `ξ` to `X ×_Y Y` vanishes, since it factors through `X`
    let c := (Over.mapPullbackAdj f).counit.app (Over.mk (𝟙 Y))
    let k : (Over.map f).obj ((Over.pullback f).obj (Over.mk (𝟙 Y))) ⟶ Over.mk f :=
      Over.homMk (Limits.pullback.snd (𝟙 Y) f) rfl
    have hck : c = k ≫ (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 Y)) := by
      ext
      simpa [c, k] using Limits.pullback.condition (f := 𝟙 Y) (g := f)
    have hres : Stacks.sheafCohomologyRestriction (Jf.over Y) c (n + 1) F ξ = 0 := by
      rw [hck, Stacks.sheafCohomologyRestriction_comp, hξ, map_zero]
    have hA := ConcreteCategory.congr_hom
      (Stacks.Cohomology.RightDerivedEdge.rightDerived_map_comp_edge_app Φ Γf η (n + 1) F) ξ
    have hB := ConcreteCategory.congr_hom
      (Stacks.DerivedIndexing.map_comp_edge_comp_rightDerivedIso Φ Γf (n + 1) (η.app F)) ξ
    have hval : ((Stacks.DerivedIndexing.rightDerivedIso Γf (n + 1)).hom.app F ≫
        (Γf.rightDerivedPlus ((n + 1 : ℕ) : ℤ)).map (η.app F) ≫
          (Stacks.DerivedIndexing.rightDerivedPlusEdge Φ Γf ((n + 1 : ℕ) : ℤ)).app F) ξ = 0 := by
      refine hB.symm.trans ?_
      show (Stacks.DerivedIndexing.rightDerivedIso (Φ ⋙ Γf) (n + 1)).hom.app F
        (((Γf.rightDerived (n + 1)).map (η.app F) ≫
          (Stacks.Cohomology.RightDerivedEdge.edge Φ Γf (n + 1)).app F) ξ) = 0
      rw [hA]
      show (Stacks.DerivedIndexing.rightDerivedIso (Φ ⋙ Γf) (n + 1)).hom.app F
        (Stacks.sheafCohomologyRestriction (Jf.over Y) c (n + 1) F ξ) = 0
      rw [hres]
      exact map_zero _
    rw [Stacks.DerivedIndexing.rightDerivedPlusEdge_app_eq] at hval
    let cI := (Stacks.DerivedIndexing.rightDerivedPlusCompIso Φ Γf).app F0
    apply (AddCommGrpCat.mono_iff_injective
      ((DerivedCategory.Plus.homologyFunctor Ab.{max u v} ((n : ℤ) + 1)).map cI.inv)).1
      inferInstance
    rw [map_zero]
    have hw : Γf.rightDerivedFunctorPlus.map w ≫ cI.inv =
        Γf.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (AbelianSheaves Jf Y) 0).map (η.app F)) ≫
          Stacks.DerivedIndexing.singleDerivedPullback Φ Γf 0 F := by
      simp only [w, Stacks.DerivedIndexing.singleDerivedPullback, Functor.map_comp,
        Category.assoc]
      rfl
    refine (ConcreteCategory.congr_hom ((DerivedCategory.Plus.homologyFunctor Ab.{max u v}
      ((n : ℤ) + 1)).map_comp (Γf.rightDerivedFunctorPlus.map w) cI.inv) ξD).symm.trans ?_
    rw [hw, Functor.map_comp]
    exact hval
  obtain ⟨β, hβ⟩ := exists_homology_singleDerivedPullback_eq_of_map S n hV Y F hF' N w h₁ h₂
    ξD hξD
  refine ⟨(Stacks.DerivedIndexing.rightDerivedIso Γc (n + 1)).inv.app (push.obj F) β, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective
    ((Stacks.DerivedIndexing.rightDerivedIso Γf (n + 1)).hom.app F)).1 inferInstance
  show ((cohomologyComparison S Y (n + 1)).app F ≫
      (Stacks.DerivedIndexing.rightDerivedIso Γf (n + 1)).hom.app F)
    ((Stacks.DerivedIndexing.rightDerivedIso Γc (n + 1)).inv.app (push.obj F) β) = ξD
  rw [cohomologyComparison_comp_rightDerivedIso]
  show ((Stacks.DerivedIndexing.rightDerivedIso Γc (n + 1)).inv.app (push.obj F) ≫
      (Stacks.DerivedIndexing.rightDerivedIso Γc (n + 1)).hom.app (push.obj F) ≫
      (Stacks.DerivedIndexing.rightDerivedPlusEdge push Γc ((n + 1 : ℕ) : ℤ)).app F) β = ξD
  rw [Iso.inv_hom_id_app_assoc, Stacks.DerivedIndexing.rightDerivedPlusEdge_app_eq]
  exact hβ

/-- **The descent statement of Stacks 0EZE holds under `(V_n)`.** For an arrow `f : W ⟶ V` of
the localized site whose underlying arrow is in the distinguished class and is a covering for the
finer topology, a class of degree `n + 1` over `V` whose restriction to `W` dies on a coarse
covering of `W` dies on a coarse covering of `V`.

The source's argument: by Stacks 0EZC the restriction to `W` comes from a coarse class `θ`, which
is unique, hence has equal pullbacks to `W ×_V W`; Stacks 0EZD kills `θ` after base change to a
coarse covering `{Z ⟶ V}`, and over each `Z` the class then restricts to zero along the base
change of `f`, so the closing step `exists_cohomologyComparison_eq_of_restriction_eq_zero`
applies there. -/
theorem CohomologyComparison.singleCoveringDescent (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) : S.SingleCoveringDescent (n + 1) := by
  intro X₀ F hF V W f hP hcov ζ ⟨R₀, hR₀⟩
  let Jf := S.fineCoverage.toGrothendieck
  let Jc := S.coarseCoverage.toGrothendieck
  let push := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X₀
  -- Stacks 0EZC: the restriction of `ζ` to `W` comes from a coarse class `θ`
  obtain ⟨θ, hθ⟩ := (mem_range_cohomologyComparisonAt_iff S n hV X₀ W F hF
    (Stacks.sheafCohomologyRestriction (Jf.over X₀) f (n + 1) F ζ)).2
      ⟨R₀, fun g ↦ by rw [← Stacks.sheafCohomologyRestriction_comp]; exact hR₀ g⟩
  -- the comparison commutes with restriction
  have hnat : ∀ {U : Over X₀} (k : U ⟶ W), (cohomologyComparisonAt S X₀ U (n + 1)).app F
      (Stacks.sheafCohomologyRestriction (Jc.over X₀) k (n + 1) (push.obj F) θ) =
        Stacks.sheafCohomologyRestriction (Jf.over X₀) (k ≫ f) (n + 1) F ζ := by
    intro U k
    rw [Stacks.sheafCohomologyRestriction_comp, ← hθ, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, cohomologyComparisonAt_naturality]
  -- relocalization to `C/V.left`
  let Y := V.left
  let eW : (Over.map V.hom).obj (Over.mk f.left) ⟶ W := Over.homMk (𝟙 W.left) (by simp [Over.w f])
  let θm := Stacks.sheafCohomologyRestriction (Jc.over X₀) eW (n + 1) (push.obj F) θ
  let ι := overMapSheafCohomologyIso Jc V.hom (push.obj F) (Over.mk f.left) (n + 1)
  let θ' := ι.hom θm
  have hrel : ∀ {Q : Over Y} (k : Q ⟶ Over.mk f.left),
      Stacks.sheafCohomologyRestriction (Jc.over Y) k (n + 1)
        ((Jc.overMapPullback Ab.{max u v} V.hom).obj (push.obj F)) θ' =
      (overMapSheafCohomologyIso Jc V.hom (push.obj F) Q (n + 1)).hom
        (Stacks.sheafCohomologyRestriction (Jc.over X₀) ((Over.map V.hom).map k ≫ eW) (n + 1)
          (push.obj F) θ) := by
    intro Q k
    rw [Stacks.sheafCohomologyRestriction_comp]
    simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom
      (overMapSheafCohomologyIso_hom_comp_restriction Jc V.hom (push.obj F) k (n + 1)) θm
  -- the self-intersection `W ×_V W`, and the equalizer condition for `θ'`
  obtain ⟨Zc, q, p, hpb, -⟩ := S.morphismProperty_baseChange f.left hP f.left
  let P' : Over Y := Over.mk (q ≫ f.left)
  let p₁ : P' ⟶ Over.mk f.left := Over.homMk q
  let p₂ : P' ⟶ Over.mk f.left := Over.homMk p (by simp [P', hpb.w])
  have heq : Stacks.sheafCohomologyRestriction (Jc.over Y) p₁ (n + 1)
        ((Jc.overMapPullback Ab.{max u v} V.hom).obj (push.obj F)) θ' =
      Stacks.sheafCohomologyRestriction (Jc.over Y) p₂ (n + 1)
        ((Jc.overMapPullback Ab.{max u v} V.hom).obj (push.obj F)) θ' := by
    rw [hrel, hrel]
    refine congrArg (overMapSheafCohomologyIso Jc V.hom (push.obj F) P' (n + 1)).hom ?_
    apply (AddCommGrpCat.mono_iff_injective _).1
      (mono_cohomologyComparisonAt S n hV X₀ _ F hF)
    rw [hnat, hnat]
    refine congrArg (fun k => Stacks.sheafCohomologyRestriction (Jf.over X₀) k (n + 1) F ζ) ?_
    ext
    simp [p₁, p₂, eW, hpb.w]
  have hF'Y := S.weakSerre_relocalizationInverseImage V.hom (push.obj F)
    ((CohomologyComparison.fineWeakSerre_iff_weakSerre_pushforward S X₀ F).1 hF)
  -- Stacks 0EZD
  obtain ⟨R, hR, hRθ⟩ := exists_coarseCovering_restrict_eq_zero_of_equalizer S f.left hP hcov
    _ hF'Y n P' p₁ p₂ hpb θ' heq
  -- over each member of the covering the class dies on a coarse covering
  have key : ∀ ⦃Z : C⦄ (g : Z ⟶ Y), R g →
      ∃ R' : (Jc.over X₀).Cover (Over.mk (g ≫ V.hom)), ∀ k : R'.Arrow,
        Stacks.sheafCohomologyRestriction (Jf.over X₀)
          (k.f ≫ (Over.homMk g : Over.mk (g ≫ V.hom) ⟶ V)) (n + 1) F ζ = 0 := by
    intro Z g hg
    obtain ⟨Q, a, b, hQ, ha⟩ := hRθ g hg
    obtain ⟨Z', q', p', hpb', hPp'⟩ := S.morphismProperty_baseChange f.left hP g
    let Zo : Over X₀ := Over.mk (g ≫ V.hom)
    let zmap : Zo ⟶ V := Over.homMk g
    -- the comparison pullback square, and the vanishing of `θ` on it
    let a'' : Over.mk (p' ≫ g) ⟶ Over.mk f.left := Over.homMk q' (by simp [hpb'.w])
    have hQw : (hQ.lift q' p' hpb'.w) ≫ Q.hom = p' ≫ g := by
      rw [← Over.w b]
      simp
    let l : Over.mk (p' ≫ g) ⟶ Q := Over.homMk (hQ.lift q' p' hpb'.w) hQw
    have hla : l ≫ a = a'' := by
      ext
      simp [l, a'']
    have ha'' : Stacks.sheafCohomologyRestriction (Jc.over Y) a'' (n + 1)
        ((Jc.overMapPullback Ab.{max u v} V.hom).obj (push.obj F)) θ' = 0 := by
      rw [← hla, Stacks.sheafCohomologyRestriction_comp, ha, map_zero]
    have hθ0 : Stacks.sheafCohomologyRestriction (Jc.over X₀) ((Over.map V.hom).map a'' ≫ eW)
        (n + 1) (push.obj F) θ = 0 := by
      rw [hrel] at ha''
      apply (AddCommGrpCat.mono_iff_injective
        (overMapSheafCohomologyIso Jc V.hom (push.obj F) (Over.mk (p' ≫ g)) (n + 1)).hom).1
        inferInstance
      rw [ha'', map_zero]
    -- the class over `Zo` restricts to zero along the base change of `f`
    let j : (Over.mk (p' ≫ Zo.hom) : Over X₀) ⟶ (Over.map V.hom).obj (Over.mk (p' ≫ g)) :=
      Over.homMk (𝟙 _) (by simp [Zo])
    have hk : (Over.homMk p' : (Over.mk (p' ≫ Zo.hom) : Over X₀) ⟶ Zo) ≫ zmap =
        (j ≫ (Over.map V.hom).map a'' ≫ eW) ≫ f := by
      ext
      simp [j, a'', eW, zmap, hpb'.w]
    have hzero : Stacks.sheafCohomologyRestriction (Jf.over X₀)
        (Over.homMk p' : (Over.mk (p' ≫ Zo.hom) : Over X₀) ⟶ Zo) (n + 1) F
          (Stacks.sheafCohomologyRestriction (Jf.over X₀) zmap (n + 1) F ζ) = 0 := by
      rw [← Stacks.sheafCohomologyRestriction_comp, hk, ← hnat,
        Stacks.sheafCohomologyRestriction_comp, hθ0, map_zero, map_zero]
    have hcov' : Presieve.singleton p' ∈ S.fineCoverage Z := by
      simpa only [Presieve.ofArrows_pUnit] using S.fineCoverage.mem_coverings_of_isPullback
        (ι := PUnit.{max u v + 1}) (fun _ => f.left)
        (by simpa only [Presieve.ofArrows_pUnit] using hcov) g
        (fun _ => p') (fun _ => q') (fun _ => hpb'.flip)
    obtain ⟨η, hη⟩ := exists_cohomologyComparison_eq_of_restriction_eq_zero S n hV p' hPp'
      hcov' _ (CohomologyComparison.fineWeakSerre_overMapPullback S Zo.hom F hF)
      ((sheafCohomologyOverIso Jf F Zo (n + 1)).hom
        (Stacks.sheafCohomologyRestriction (Jf.over X₀) zmap (n + 1) F ζ))
      ((sheafCohomologyOverIso_restriction_eq_zero_iff Jf F Zo (n + 1) p' _).2 hzero)
    obtain ⟨R', hR'⟩ := (mem_range_cohomologyComparison_over_iff S n hV X₀ F hF Zo
      (Stacks.sheafCohomologyRestriction (Jf.over X₀) zmap (n + 1) F ζ)).1 ⟨η, hη⟩
    exact ⟨R', fun k ↦ by rw [Stacks.sheafCohomologyRestriction_comp]; exact hR' k⟩
  -- transitivity of the coarser topology
  let E := Stacks.sheafCohomologyVanishingSieve (Jf.over X₀) F (n + 1) ζ
  have hEmem : E ∈ Jc.over X₀ V := by
    refine (Jc.over X₀).transitive (S.coarseCoverage.toGrothendieck.overEquiv_symm_mem_over V _
      (S.coarseCoverage.generate_mem_toGrothendieck hR)) E ?_
    intro Z w hw
    obtain ⟨Y₀, a, v, hRv, hav⟩ : Sieve.generate R w.left := hw
    have hav' : a ≫ (Over.mk (v ≫ V.hom) : Over X₀).hom = Z.hom := by
      show a ≫ v ≫ V.hom = Z.hom
      rw [← Category.assoc, hav]
      exact Over.w w
    have hfacw : (Over.homMk a hav' : Z ⟶ Over.mk (v ≫ V.hom)) ≫
        (Over.homMk v : Over.mk (v ≫ V.hom) ⟶ V) = w := by
      ext
      exact hav
    rw [← hfacw, Sieve.pullback_comp]
    refine (Jc.over X₀).pullback_stable _ ?_
    obtain ⟨R', hR'⟩ := key v hRv
    exact (Jc.over X₀).superset_covering (fun Z' h hh ↦ hR' ⟨Z', h, hh⟩) R'.2
  exact ⟨⟨E, hEmem⟩, fun g ↦ g.hf⟩

end Stacks.ComparingTopologies

end
