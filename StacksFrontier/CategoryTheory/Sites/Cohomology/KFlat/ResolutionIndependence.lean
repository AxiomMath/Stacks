module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TensorPreservesQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# A quasi-isomorphism of K-flat complexes stays one after tensoring with anything

Let `(C, O)` be a ringed site and `α : P ⟶ Q` a quasi-isomorphism of K-flat complexes of
`O`-modules. Then for *every* complex `F` of `O`-modules the induced map
`Tot(F ⊗_O α)` is a quasi-isomorphism, and likewise `Tot(α ⊗_O F)`. This is Stacks 06YT; it
is what makes the derived tensor product independent of the chosen K-flat resolution.

The proof is the one in the source. Choose a K-flat resolution `r : M ⟶ F` (Stacks 06YS) and
consider the square

```
Tot(M ⊗ P) --> Tot(M ⊗ Q)
    |              |
Tot(F ⊗ P) --> Tot(F ⊗ Q)
```

whose horizontal maps are `Tot(1 ⊗ α)` and whose vertical maps are `Tot(r ⊗ 1)`. The top
horizontal map is a quasi-isomorphism because `M` is K-flat, and both vertical maps are
quasi-isomorphisms because `P` and `Q` are — all three by Stacks 06YP. Hence so is the bottom
horizontal map.

## Main results

* `Stacks.SheafOfModules.quasiIso_tensorComplex_obj_map_of_kFlat`: `Tot(F ⊗ α)` is a
  quasi-isomorphism.
* `Stacks.SheafOfModules.quasiIso_tensorComplex_map_app_of_kFlat`: `Tot(α ⊗ F)` is a
  quasi-isomorphism.
* `Stacks.SheafOfModules.quasiIso_mapBifunctorMap_id_of_kFlat_right` and
  `quasiIso_mapBifunctorMap_id_of_kFlat_left`: the same two statements in the
  `HomologicalComplex.mapBifunctorMap` spelling.

## Implementation notes

The square commutes because `HomologicalComplex.mapBifunctorMap` is functorial in the pair of
morphisms (`HomologicalComplex.mapBifunctorMap_comp`), both composites being
`Tot(r ⊗ α)`. The cancellation of the left vertical map is Mathlib's
`_root_.quasiIso_iff_comp_left`.

The object universe of the site is independent of its morphism and section universes, as in
`Stacks.SheafOfModules.exists_kFlat_quasiIso`, from which the K-flat resolution comes.

## References

* [Stacks Project, Tag 06YT](https://stacks.math.columbia.edu/tag/06YT)
* [Stacks Project, Tag 06YP](https://stacks.math.columbia.edu/tag/06YP)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- If a square of chain maps commutes and three of its sides are quasi-isomorphisms, so is the
fourth. -/
private theorem quasiIso_of_comp_eq_comp {V : Type*} [Category V] [Abelian V]
    {K L M N : CochainComplex V ℤ} (a : K ⟶ L) (u : K ⟶ M) (v : M ⟶ N) {b : L ⟶ N}
    (h : a ≫ b = u ≫ v) [QuasiIso a] [QuasiIso u] [QuasiIso v] : QuasiIso b := by
  have : QuasiIso (a ≫ b) := by
    rw [h]
    infer_instance
  exact (_root_.quasiIso_iff_comp_left a b).1 this

/-- A quasi-isomorphism `α` of K-flat complexes induces a quasi-isomorphism
`Tot(F ⊗ α)` for every complex `F`. This is Stacks 06YT. -/
@[stacks 06YT "the quasi-isomorphism in the right tensor factor"]
theorem quasiIso_mapBifunctorMap_id_of_kFlat_right
    {P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (α : P ⟶ Q) (hα : QuasiIso α) (hP : IsKFlat X.O P) (hQ : IsKFlat X.O Q)
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 F) α (Stacks.SheafOfModules.Tensor.sheafTensor
      X.O)
      (ComplexShape.up ℤ)) := by
  obtain ⟨M, r, hM, hr⟩ := exists_kFlat_quasiIso X F
  have := IsKFlat.quasiIso_mapBifunctorMap_id_left X.O M hM α hα
  have := IsKFlat.quasiIso_mapBifunctorMap_id_right X.O Q hQ r hr
  have := IsKFlat.quasiIso_mapBifunctorMap_id_right X.O P hP r hr
  refine quasiIso_of_comp_eq_comp (HomologicalComplex.mapBifunctorMap r (𝟙 P) _ _)
    (HomologicalComplex.mapBifunctorMap (𝟙 M) α _ _)
    (HomologicalComplex.mapBifunctorMap r (𝟙 Q) _ _) ?_
  rw [HomologicalComplex.mapBifunctorMap_comp, HomologicalComplex.mapBifunctorMap_comp]
  simp

/-- A quasi-isomorphism `α` of K-flat complexes induces a quasi-isomorphism
`Tot(α ⊗ F)` for every complex `F`. This is the mirror image of Stacks 06YT. -/
@[stacks 06YT "the quasi-isomorphism in the left tensor factor"]
theorem quasiIso_mapBifunctorMap_id_of_kFlat_left
    {P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (α : P ⟶ Q) (hα : QuasiIso α) (hP : IsKFlat X.O P) (hQ : IsKFlat X.O Q)
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 F) (Stacks.SheafOfModules.Tensor.sheafTensor
      X.O)
      (ComplexShape.up ℤ)) := by
  obtain ⟨M, r, hM, hr⟩ := exists_kFlat_quasiIso X F
  have := IsKFlat.quasiIso_mapBifunctorMap_id_right X.O M hM α hα
  have := IsKFlat.quasiIso_mapBifunctorMap_id_left X.O Q hQ r hr
  have := IsKFlat.quasiIso_mapBifunctorMap_id_left X.O P hP r hr
  refine quasiIso_of_comp_eq_comp (HomologicalComplex.mapBifunctorMap (𝟙 P) r _ _)
    (HomologicalComplex.mapBifunctorMap α (𝟙 M) _ _)
    (HomologicalComplex.mapBifunctorMap (𝟙 Q) r _ _) ?_
  rw [HomologicalComplex.mapBifunctorMap_comp, HomologicalComplex.mapBifunctorMap_comp]
  simp

/-- Stacks 06YT in the `Stacks.SheafOfModules.Tensor.tensorComplex` spelling: the quasi-isomorphism
  `α` of
K-flat complexes sits in the right tensor slot. The square whose cancellation gives the
result is the naturality square of `tensorComplex.map r` at `α`, for a K-flat resolution
`r : M ⟶ F`. -/
@[stacks 06YT "right tensor factor, tensorComplex spelling"]
theorem quasiIso_tensorComplex_obj_map_of_kFlat
    {P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (α : P ⟶ Q) (hα : QuasiIso α) (hP : IsKFlat X.O P) (hQ : IsKFlat X.O Q)
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj F).map α) := by
  obtain ⟨M, r, hM, hr⟩ := exists_kFlat_quasiIso X F
  have := IsKFlat.quasiIso_tensorComplex_obj_map X.O M hM α hα
  have := IsKFlat.quasiIso_tensorComplex_map_app X.O Q hQ r hr
  have := IsKFlat.quasiIso_tensorComplex_map_app X.O P hP r hr
  exact quasiIso_of_comp_eq_comp _ _ _
    (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map r).naturality α).symm

/-- Stacks 06YT in the `Stacks.SheafOfModules.Tensor.tensorComplex` spelling, mirror image: the
quasi-isomorphism `α` of K-flat complexes sits in the left tensor slot. -/
@[stacks 06YT "left tensor factor, tensorComplex spelling"]
theorem quasiIso_tensorComplex_map_app_of_kFlat
    {P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (α : P ⟶ Q) (hα : QuasiIso α) (hP : IsKFlat X.O P) (hQ : IsKFlat X.O Q)
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map α).app F) := by
  obtain ⟨M, r, hM, hr⟩ := exists_kFlat_quasiIso X F
  have := IsKFlat.quasiIso_tensorComplex_map_app X.O M hM α hα
  have := IsKFlat.quasiIso_tensorComplex_obj_map X.O Q hQ r hr
  have := IsKFlat.quasiIso_tensorComplex_obj_map X.O P hP r hr
  exact quasiIso_of_comp_eq_comp _ _ _
    (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map α).naturality r)

end Stacks.SheafOfModules

end
