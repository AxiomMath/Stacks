module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksFrontier.Algebra.Homology.TricomplexRotation

/-!
# The total complex of a short complex of bicomplexes which is split in every bidegree

Let `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` be a short complex of bicomplexes in an abelian category which is
split in every bidegree.  Then the induced short complex of total complexes is split in every
degree, hence short exact.  The splittings need not commute with the differentials.

## Main results

* `HomologicalComplex₂.splittingTotal`: the splitting of a degree of the total complexes.
* `HomologicalComplex₂.shortExact_total_of_splitting`: the short complex of total complexes is
  short exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
  [TotalComplexShape c₁ c₂ c₁₂]

/-- The total complex of the zero morphism of bicomplexes is zero. -/
theorem total_map_zero (K L : HomologicalComplex₂ C c₁ c₂) [K.HasTotal c₁₂] [L.HasTotal c₁₂]
    [DecidableEq I₁₂] : total.map (0 : K ⟶ L) c₁₂ = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => total.hom_ext _ fun i₁ i₂ h => ?_
  rw [ιTotal_map, HomologicalComplex.zero_f, HomologicalComplex.zero_f, HomologicalComplex.zero_f,
    zero_comp, comp_zero]

/-- The total complex is additive in the bicomplex. -/
theorem total_map_add {K L : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c₁₂] [L.HasTotal c₁₂]
    [DecidableEq I₁₂] (f g : K ⟶ L) :
    total.map (f + g) c₁₂ = total.map f c₁₂ + total.map g c₁₂ := by
  refine HomologicalComplex.hom_ext _ _ fun n => total.hom_ext _ fun i₁ i₂ h => ?_
  rw [HomologicalComplex.add_f_apply, ιTotal_map, Preadditive.comp_add, ιTotal_map, ιTotal_map,
    HomologicalComplex.add_f_apply, HomologicalComplex.add_f_apply, Preadditive.add_comp]

/-- The total complex functor from bicomplexes to complexes is additive. -/
instance totalFunctor_additive [∀ K : HomologicalComplex₂ C c₁ c₂, K.HasTotal c₁₂]
    [DecidableEq I₁₂] : (totalFunctor C c₁ c₂ c₁₂).Additive where
  map_add {_ _ f g} := total_map_add f g

section

variable [DecidableEq I₁₂] (T : ShortComplex (HomologicalComplex₂ C c₁ c₂))
  [T.X₁.HasTotal c₁₂] [T.X₂.HasTotal c₁₂] [T.X₃.HasTotal c₁₂]

/-- **The splitting of a degree of the total complexes**, assembled from the splittings of the
bidegrees. -/
def splittingTotal
    (σ : ∀ i₁ i₂,
      (T.map (HomologicalComplex.eval _ _ i₁ ⋙ HomologicalComplex.eval _ _ i₂)).Splitting)
    (n : I₁₂) :
    (ShortComplex.mk ((total.map T.f c₁₂).f n) ((total.map T.g c₁₂).f n)
      (by rw [← HomologicalComplex.comp_f, ← total.map_comp, T.zero, total_map_zero,
        HomologicalComplex.zero_f])).Splitting where
  r := T.X₂.totalDesc fun i₁ i₂ h => (σ i₁ i₂).r ≫ T.X₁.ιTotal c₁₂ i₁ i₂ n h
  s := T.X₃.totalDesc fun i₁ i₂ h => (σ i₁ i₂).s ≫ T.X₂.ιTotal c₁₂ i₁ i₂ n h
  f_r := by
    refine total.hom_ext _ fun i₁ i₂ h => ?_
    dsimp
    rw [ιTotal_map_assoc, ι_totalDesc, ← Category.assoc, Category.comp_id]
    exact eq_whisker (σ i₁ i₂).f_r _ |>.trans (Category.id_comp _)
  s_g := by
    refine total.hom_ext _ fun i₁ i₂ h => ?_
    dsimp
    rw [ι_totalDesc_assoc, Category.assoc, ιTotal_map, ← Category.assoc, Category.comp_id]
    exact eq_whisker (σ i₁ i₂).s_g _ |>.trans (Category.id_comp _)
  id := by
    refine total.hom_ext _ fun i₁ i₂ h => ?_
    dsimp
    rw [Preadditive.comp_add, ι_totalDesc_assoc, ιTotal_map_assoc, Category.assoc, ιTotal_map,
      ι_totalDesc, Category.comp_id, ← Category.assoc, ← Category.assoc,
      ← Preadditive.add_comp]
    exact eq_whisker (σ i₁ i₂).id _ |>.trans (Category.id_comp _)

/-- **The total complexes of a short complex of bicomplexes split in every bidegree form a short
exact sequence.** -/
theorem shortExact_total_of_splitting
    (σ : ∀ i₁ i₂,
      (T.map (HomologicalComplex.eval _ _ i₁ ⋙ HomologicalComplex.eval _ _ i₂)).Splitting) :
    (ShortComplex.mk (total.map T.f c₁₂) (total.map T.g c₁₂)
      (by rw [← total.map_comp, T.zero, total_map_zero])).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    (splittingTotal T σ n).shortExact

end

end HomologicalComplex₂
