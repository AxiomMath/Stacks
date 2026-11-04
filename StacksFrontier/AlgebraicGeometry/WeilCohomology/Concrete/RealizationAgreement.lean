module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Actions of correspondences are determined by the equidimensional pieces

Let `W` be data (D0)–(D3) satisfying (A), (B), (C). Consider a family `T` of linear maps
`T(f) : H^n(X) → H^n(Y)`, one for every correspondence `f ∈ Corr⁰(X, Y)` of degree zero, which is
functorial, additive, and on the graph `[Γ_g]` of a morphism `g` is the pullback `g^*`: for
instance the realization `G` of a functor from Chow motives, or the action
`c ↦ pr₂,*(γ(c) ∪ pr₁^* -)` of Stacks 0FHL. This file shows:

* the transposed graph `[Γ_jᵗ]` of an open and closed immersion `j` acts by extension by zero
  (`Stacks.WeilCohomology.WeilData.CorrAction.cographHom`): it restricts to the identity on
  the image of `j` and to `0` on the complement (Stacks 0FHJ);
* two such families agree as soon as they agree on correspondences between nonempty
  equidimensional schemes (`Stacks.WeilCohomology.WeilData.CorrAction.ext`): a correspondence
  `f : X ⟶ Y` is read through the parts `X_d`, `Y_e` of `X` and `Y` as
  `[Γ_{X_d}]ᵗ ≫ f ≫ [Γ_{Y_e}]`, and `H^*(X)` is the sum of the extensions by zero of the
  restrictions to its parts.

This is the reduction to equidimensional schemes in the proof of Stacks 0FHM, that the
realization of Stacks 0FHK acts on correspondences by the formula of Stacks 0FHL.

## Main definitions

* `Stacks.WeilCohomology.WeilData.CorrAction`: a functorial, additive action of correspondences
  of degree zero on `H^*`, by pullbacks on graphs.

## References

* [Stacks Project, Tag 0FHJ](https://stacks.math.columbia.edu/tag/0FHJ)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.GradedCategory

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (W : WeilData k F)

/-- A smooth projective scheme as an object of the category of correspondences of degree zero. -/
abbrev dz (P : (SmoothProjectiveScheme k).FullSubcategory) :
    DegreeZero ℚ (CorrespondenceCategory k) :=
  GradedCompositionData.Obj.mk P

/-- **An action of correspondences of degree zero on `H^*`**: linear maps
`T(f) : H^n(X) → H^n(Y)` for `f ∈ Corr⁰(X, Y)`, functorial and additive, acting on the graph of
a morphism `g` by the pullback `g^*`. -/
structure CorrAction where
  /-- The action `T(f)` in degree `n`. -/
  act : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (_ : dz X ⟶ dz Y) (n : ℤ),
    W.grade X n →ₗ[F] W.grade Y n
  act_comp : ∀ {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : dz X ⟶ dz Y)
      (g : dz Y ⟶ dz Z) (n : ℤ),
    act (f ≫ g) n = act g n ∘ₗ act f n
  act_zero : ∀ (X Y : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ),
    act (0 : dz X ⟶ dz Y) n = 0
  act_add : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f g : dz X ⟶ dz Y) (n : ℤ),
    act (f + g) n = act f n + act g n
  act_graph : ∀ {P Q : (SmoothProjectiveScheme k).FullSubcategory} (g : Q ⟶ P) (f : dz P ⟶ dz Q),
    DegreeZero.val f = graphHom g → ∀ n, act f n = W.pullDeg g n

namespace CorrAction

variable {W} (T : W.CorrAction)

/-- The graph `[Γ_g]` of a morphism `g : Q ⟶ P`, as a correspondence of degree zero. -/
@[sga "7 XX 4.4" "partial"]
def graphZero {P Q : (SmoothProjectiveScheme k).FullSubcategory} (g : Q ⟶ P) : dz P ⟶ dz Q :=
  DegreeZero.homMk (ChowMotiveCat.homOf 0 (graphCorrespondenceSP g))
    (ChowMotiveCat.homOf_mem_grade _)

/-- The transposed graph `[Γ_gᵗ]` of a morphism `g : X ⟶ P`, as a correspondence of degree
zero. -/
def cographZero {X P : (SmoothProjectiveScheme k).FullSubcategory} (g : X ⟶ P) : dz X ⟶ dz P :=
  DegreeZero.homMk (cographHom g) (cographHom_mem_grade g)

omit [CharZero F] in
/-- The graph `[Γ_g]` of a morphism `g` acts by the pullback `g^*`. -/
theorem act_graphZero {P Q : (SmoothProjectiveScheme k).FullSubcategory} (g : Q ⟶ P) (n : ℤ) :
    T.act (graphZero g) n = W.pullDeg g n :=
  T.act_graph g _ (ChowMotiveCat.homOf_graphCorrespondenceSP g) n

omit [CharZero F] in
/-- The identity correspondence acts by the identity. -/
theorem act_id (P : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    T.act (𝟙 (dz P)) n = LinearMap.id := by
  rw [T.act_graph (𝟙 P) _ ((DegreeZero.id_val _).trans (CorrespondenceCategory.id_eq_graphHom P))
    n]
  ext a
  simp [pullDeg, W.pull_id]

/-- The underlying correspondence of `[Γ_jᵗ] ≫ [Γ_g]` is the composite of the transposed graph of
`j` with the graph of `g`. -/
theorem val_cographZero_comp_graphZero {X Z P : (SmoothProjectiveScheme k).FullSubcategory}
    (j : X ⟶ P) (g : Z ⟶ P) :
    (DegreeZero.val (cographZero j ≫ graphZero g) : (GradedCompositionData.Obj.mk X :
      (canonicalCorrespondenceCompositionData k).Obj) ⟶ GradedCompositionData.Obj.mk Z) =
      ChowMotiveCat.homOf (0 + 0) ((canonicalCorrespondenceCompositionData k).comp
        (cographCorrespondenceSP j) (graphCorrespondenceSP g)) := by
  rw [← ChowMotiveCat.homOf_comp_homOf]
  rfl

/-- For an open immersion `j`, the composite `[Γ_jᵗ] ≫ [Γ_j]` is the identity. -/
theorem cographZero_comp_graphZero_self {X P : (SmoothProjectiveScheme k).FullSubcategory}
    (j : X ⟶ P) [IsOpenImmersion j.hom.left] : cographZero j ≫ graphZero j = 𝟙 _ := by
  apply DegreeZero.hom_ext
  rw [val_cographZero_comp_graphZero]
  have h := cographHom_comp_graph_self j
  rw [cographHom, ChowMotiveCat.homOf_comp_homOf] at h
  exact h

/-- If `j` and `g` have disjoint images, the composite `[Γ_jᵗ] ≫ [Γ_g]` is zero. -/
theorem cographZero_comp_graphZero_of_disjoint {X Z P : (SmoothProjectiveScheme k).FullSubcategory}
    (j : X ⟶ P) (g : Z ⟶ P) (hjg : Disjoint (Set.range j.hom.left) (Set.range g.hom.left)) :
    cographZero j ≫ graphZero g = 0 := by
  apply DegreeZero.hom_ext
  rw [val_cographZero_comp_graphZero]
  have h := cographHom_comp_graph_of_disjoint j g hjg
  rw [cographHom, ChowMotiveCat.homOf_comp_homOf] at h
  exact h

variable (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

/-- **The transposed graph of an open and closed immersion acts by extension by zero.** -/
theorem act_cographZero {X P : (SmoothProjectiveScheme k).FullSubcategory} (j : X ⟶ P)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] (n : ℤ) :
    T.act (cographZero j) n = extendDeg hA hB hC j n := by
  ext x
  refine sub_eq_zero.1 (eq_zero_of_pull_eq_zero_of_pull_complι_eq_zero hA hB hC j ?_ ?_)
  · rw [map_sub, coe_extendDeg, pull_extendByZero_self, ← coe_pullDeg, ← LinearMap.comp_apply,
      ← T.act_graphZero, ← T.act_comp, cographZero_comp_graphZero_self, T.act_id,
      LinearMap.id_apply, sub_self]
  · rw [map_sub, coe_extendDeg, (pull_extendByZero_and hA hB hC j x).2, ← coe_pullDeg,
      ← LinearMap.comp_apply, ← T.act_graphZero, ← T.act_comp,
      cographZero_comp_graphZero_of_disjoint j (complι j) (by
        rw [range_complι]; exact disjoint_compl_right),
      T.act_zero, LinearMap.zero_apply, ZeroMemClass.coe_zero, sub_zero]

include hA hB hC in
/-- **Two actions of correspondences agree as soon as they agree between nonempty equidimensional
schemes.** -/
theorem ext (T T' : W.CorrAction)
    (h : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ},
      IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Y e →
      ∀ (f : dz X ⟶ dz Y) (n : ℤ), T.act f n = T'.act f n)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : dz X ⟶ dz Y) (n : ℤ) :
    T.act f n = T'.act f n := by
  ext a
  refine sub_eq_zero.1 (eq_zero_of_pull_eq_zero (hA := hA) (hB := hB) (hC := hC)
    (partSupport Y) (fun e ↦ partι Y e) (exists_mem_partSupport Y) fun e he ↦ ?_)
  have hY := isNonemptyEquidimensional_part Y (nonempty_part_iff.2 (mem_partSupport.1 he))
  have key : ∀ S : W.CorrAction, W.pull (partι Y e) (S.act f n a : W.H Y) =
      ∑ d ∈ partSupport X, (S.act (cographZero (partι X d) ≫ f ≫ graphZero (partι Y e)) n
        (W.pullDeg (partι X d) n a) : W.H (part Y e)) := by
    intro S
    have ha := sum_extendByZero_pull (hA := hA) (hB := hB) (hC := hC) (partSupport X)
      (fun d ↦ partι X d) (exists_mem_partSupport X)
      (fun s _ t _ hst ↦ disjoint_range_partι X hst) (a : W.H X)
    have ha' : a = ∑ d ∈ partSupport X,
        S.act (cographZero (partι X d)) n (W.pullDeg (partι X d) n a) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [S.act_cographZero hA hB hC, coe_extendDeg, coe_pullDeg]
      exact ha.symm
    conv_lhs => rw [ha']
    rw [map_sum, Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [S.act_comp, S.act_comp, LinearMap.comp_apply, LinearMap.comp_apply, act_graphZero,
      coe_pullDeg]
  rw [map_sub, key T, key T', ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  have hX := isNonemptyEquidimensional_part X (nonempty_part_iff.2 (mem_partSupport.1 hd))
  rw [h hX hY, sub_self]

end CorrAction

end Stacks.WeilCohomology.WeilData

end
