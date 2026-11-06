module

public import StacksFrontier.Algebra.Homology.DoubleMappingCone
public import StacksFrontier.Homology.DoubleExtend

/-!
# The projection of a two-term complex onto its shifted degree `-1` term

Let `f : X₀ ⟶ X₁` be a morphism in an abelian category and let `double f` be the two-term
complex with `f` in degrees `-1` and `0`. A morphism `g : X₀ ⟶ G` has two natural classes in
`Hom_{D}(double f, G⟦1⟧)`:

* the chain map `double f ⟶ G[-1]` which is `g` in degree `-1`, read through the identification
  `G[-1] ≅ G[0]⟦1⟧` of the single functors;
* the projection `CochainComplex.doubleProjQ f` of the distinguished triangle
  `X₀ ⟶ X₁ ⟶ double f ⟶ X₀⟦1⟧`, followed by `g⟦1⟧`.

They differ by a sign, which comes from the third map of the triangle of a mapping cone being
`-1` on the shifted source (`CochainComplex.mappingCone.inl_v_triangle_mor₃_f`).

## Main results

* `CochainComplex.doubleToSingleNegOne_comp_shiftIso_inv`: the comparison at the level of
  cochain complexes.
* `CochainComplex.Q_map_doubleToSingleNegOne_comp_shiftIso_inv`: the comparison in the derived
  category.

## References

* [Stacks Project, Tag 08UJ](https://stacks.math.columbia.edu/tag/08UJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated HomologicalComplex CochainComplex.HomComplex

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X₀ X₁ : C} (f : X₀ ⟶ X₁)

/-- The third map of the triangle of the mapping cone of `φ`, with source written
`mappingCone φ`. -/
abbrev mappingConeTriangleδ {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    mappingCone φ ⟶ K⟦(1 : ℤ)⟧ :=
  Cocycle.homOf ((-mappingCone.fst φ).rightShift 1 0 (zero_add 1))

omit [HasDerivedCategory C] in
/-- `CochainComplex.mappingConeTriangleδ φ` is the third map of the triangle of the mapping cone
of `φ`. -/
theorem mappingConeTriangleδ_eq {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    (mappingCone.triangle φ).mor₃ = mappingConeTriangleδ φ :=
  rfl

/-- The chain map `double f ⟶ G[-1]` which is `g` in degree `-1`. -/
abbrev doubleToSingleNegOne {G : C} (g : X₀ ⟶ G) :
    (double f ComplexShape.upIntRelNegOneZero : CochainComplex C ℤ) ⟶
      (CochainComplex.singleFunctor C (-1)).obj G :=
  mkHomToSingle ((doubleXIso₀ f ComplexShape.upIntRelNegOneZero).hom ≫ g) (by
    intro i hi
    rw [double_d_eq_zero₁ f ComplexShape.upIntRelNegOneZero i (-1) (by
      have : i + 1 = -1 := hi
      omega), zero_comp])

omit [HasDerivedCategory C] in
/-- **The sign comparison on cochain complexes**: the chain map which is `g` in degree `-1`, read
through `G[-1] ≅ G[0]⟦1⟧`, is minus the composite of `CochainComplex.doubleToMappingCone`, the
third map of the cone triangle, and `g⟦1⟧`. -/
theorem doubleToSingleNegOne_comp_shiftIso_inv {G : C} (g : X₀ ⟶ G) :
    doubleToSingleNegOne f g ≫
        ((CochainComplex.singleFunctors C).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app G =
      -(doubleToMappingCone f ComplexShape.upIntRelNegOneZero ≫
        mappingConeTriangleδ ((single C (ComplexShape.up ℤ) 0).map f) ≫
          (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).map
            ((single C (ComplexShape.up ℤ) 0).map g)) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = -1
  · subst hn
    have h3 : (mappingCone.inl ((single C (ComplexShape.up ℤ) 0).map f)).v 0 (-1) (by decide) ≫
        (mappingConeTriangleδ ((single C (ComplexShape.up ℤ) 0).map f)).f (-1) =
        -(CochainComplex.shiftFunctorObjXIso ((single C (ComplexShape.up ℤ) 0).obj X₀) 1 (-1) 0
          (by decide)).inv :=
      mappingCone.inl_v_triangle_mor₃_f ((single C (ComplexShape.up ℤ) 0).map f) 0 (-1)
        (by decide)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply, doubleToMappingCone,
      mkHomFromDouble_f₀, assoc]
    rw [reassoc_of% h3]
    simp [CochainComplex.singleFunctors, CochainComplex.singleFunctor, single_map_f_self,
      shiftFunctorObjXIso, singleObjXSelf, singleObjXIsoOfEq]
  · exact (isZero_single_obj_X (ComplexShape.up ℤ) 0 G (n + 1) (by omega)).eq_of_tgt _ _

/-- **The two classes of `g : X₀ ⟶ G` in `Hom(double f, G⟦1⟧)` differ by a sign**: the chain map
which is `g` in degree `-1`, read through `G[-1] ≅ G[0]⟦1⟧`, is minus the projection
`double f ⟶ X₀⟦1⟧` of the cone triangle followed by `g⟦1⟧`. -/
theorem Q_map_doubleToSingleNegOne_comp_shiftIso_inv {G : C} (g : X₀ ⟶ G) :
    DerivedCategory.Q.map (doubleToSingleNegOne f g) ≫
        ((DerivedCategory.singleFunctors C).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app G =
      -(doubleProjQ f ComplexShape.upIntRelNegOneZero ≫
        ((DerivedCategory.singleFunctor C 0).map g)⟦(1 : ℤ)⟧') := by
  have hs : ((DerivedCategory.singleFunctors C).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app G =
      DerivedCategory.Q.map
          (((CochainComplex.singleFunctors C).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app G) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single C (ComplexShape.up ℤ) 0).obj G) := by
    simp [DerivedCategory.singleFunctors]
  have hp : doubleProjQ f ComplexShape.upIntRelNegOneZero =
      DerivedCategory.Q.map (doubleToMappingCone f ComplexShape.upIntRelNegOneZero ≫
          mappingConeTriangleδ ((single C (ComplexShape.up ℤ) 0).map f)) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single C (ComplexShape.up ℤ) 0).obj X₀) := by
    rw [Functor.map_comp, assoc]
    rfl
  rw [hs, hp, ← assoc, ← Functor.map_comp, doubleToSingleNegOne_comp_shiftIso_inv,
    Functor.map_neg, Preadditive.neg_comp, assoc, Functor.map_comp, Functor.map_comp, assoc,
    assoc]
  have hn := (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality
    ((single C (ComplexShape.up ℤ) 0).map g)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [Functor.map_comp, assoc]
  rfl

end CochainComplex

end
