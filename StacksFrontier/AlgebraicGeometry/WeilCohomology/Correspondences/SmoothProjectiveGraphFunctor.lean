module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphComposition

/-!
# The contravariant graph functor on smooth projective schemes

Sending a smooth projective scheme over `k` to itself and a morphism `f : Y ⟶ X` to the class
`[Γ_f] ∈ Corr⁰(X, Y)` of its graph is a contravariant functor from smooth projective schemes over
`k` to the category of correspondences of Stacks 0FG2, the identity on objects (Stacks 0FG3).

## Main definitions

* `Stacks.WeilCohomology.graphHom`: the graph class `[Γ_f]` of `f : Y ⟶ X`, read as a morphism
  `X ⟶ Y` of the category of correspondences.
* `Stacks.WeilCohomology.graphFunctor`: the contravariant functor `f ↦ [Γ_f]`.

## Main results

* `Stacks.WeilCohomology.graphHom_id` and `Stacks.WeilCohomology.graphHom_comp`: the two functor
  laws, `[Γ_{𝟙 X}] = 𝟙 X` and `[Γ_g] ∘ [Γ_f] = [Γ_{f ∘ g}]`.

## Implementation notes

The identity law is the identification of the diagonal with the graph of the identity
(`Stacks.WeilCohomology.graphCorr_id`), and the composition law is the computation
`[Γ_g] ∘ [Γ_f] = pr₁₃,*([Γ_f × Z] · [X × Γ_g]) = [Γ_{f ∘ g}]` by the proper intersection formula
of Stacks 0FFD on `X × Y × Z`
(`Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula.comp_graphCorr`).

As for Stacks 0FG2
(`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition`),
the construction is stated for a family `Δ` of diagonal classes satisfying associativity
(Stacks 0FG0 (1)) and the proper-intersection formula (Stacks 0FFD); both are theorems for the
canonical family of Gysin classes of diagonals.

The same functor for an arbitrary graded category of correspondences, with proper pushforward of
correspondences supplied as data, is
`Stacks.WeilCohomology.GradedCompositionData.PushforwardData.graphFunctor` in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphFunctor`.

## References

* [Stacks Project, Tag 0FG3](https://stacks.math.columbia.edu/tag/0FG3)
* [Stacks Project, Tag 0FG1](https://stacks.math.columbia.edu/tag/0FG1)
* [Stacks Project, Tag 0FG2](https://stacks.math.columbia.edu/tag/0FG2)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.WeilCohomology

open _root_.AlgebraicGeometry

variable {k : Type u} [Field k] {Δ : DiagonalClassFamily k} {hassoc : Δ.CompositionAssoc}
  {hΔ : Δ.ProperIntersectionFormula}

/-- The graph class `[Γ_f] ∈ Corr⁰(P, Q)` of a morphism `f : Q ⟶ P` of smooth projective schemes
over `k`. -/
def graphCorrespondenceSP {P Q : (SmoothProjectiveScheme k).FullSubcategory} (f : Q ⟶ P) :
    SmoothProjectiveCorr P Q 0 :=
  (SmoothProjectiveCorr.toCorr P Q 0).symm
    (graphCorr k P.obj.hom Q.obj.hom f.hom.left (Over.w f.hom))

/-- The graph class `[Γ_f] ∈ Corr⁰(P, Q)` of a morphism `f : Q ⟶ P` of smooth projective schemes
over `k`, as a morphism `P ⟶ Q` of the category of correspondences. -/
def graphHom {P Q : (SmoothProjectiveScheme k).FullSubcategory} (f : Q ⟶ P) :
    (GradedCompositionData.Obj.mk P : (correspondenceCompositionData k Δ hassoc hΔ).Obj) ⟶
      GradedCompositionData.Obj.mk Q :=
  DirectSum.of (fun i ↦ SmoothProjectiveCorr P Q i) 0 (graphCorrespondenceSP f)

/-- The morphism of correspondences attached to `f : Q ⟶ P` is homogeneous of degree zero: it
lies in `Corr⁰(P, Q)`. -/
theorem graphHom_mem_grade {P Q : (SmoothProjectiveScheme k).FullSubcategory} (f : Q ⟶ P) :
    graphHom (Δ := Δ) (hassoc := hassoc) (hΔ := hΔ) f ∈
      GradedCategory.grade (R := ℚ) (GradedCompositionData.Obj.mk P :
        (correspondenceCompositionData k Δ hassoc hΔ).Obj) (GradedCompositionData.Obj.mk Q) 0 :=
  (GradedCompositionData.mem_grade_iff _).2 ⟨_, rfl⟩

/-- The graph of an identity is the identity correspondence, the class of the diagonal. -/
theorem graphHom_id (P : (SmoothProjectiveScheme k).FullSubcategory) :
    graphHom (Δ := Δ) (hassoc := hassoc) (hΔ := hΔ) (𝟙 P) =
      𝟙 (GradedCompositionData.Obj.mk P : (correspondenceCompositionData k Δ hassoc hΔ).Obj) := by
  rw [GradedCompositionData.id_eq]
  exact congrArg (DirectSum.of (fun i ↦ SmoothProjectiveCorr P P i) 0)
    (congrArg (SmoothProjectiveCorr.toCorr P P 0).symm (graphCorr_id k P.obj.hom))

/-- Graphs compose contravariantly: `[Γ_g] ∘ [Γ_f] = [Γ_{f ∘ g}]` for `f : Q ⟶ P` and
`g : R ⟶ Q`, that is `graphHom f ≫ graphHom g = graphHom (g ≫ f)`. -/
theorem graphHom_comp {P Q R : (SmoothProjectiveScheme k).FullSubcategory} (f : Q ⟶ P) (g : R ⟶ Q) :
    graphHom (Δ := Δ) (hassoc := hassoc) (hΔ := hΔ) f ≫ graphHom g = graphHom (g ≫ f) := by
  have h₀ := (correspondenceCompositionData k Δ hassoc hΔ).of_comp_of
    (X := GradedCompositionData.Obj.mk P) (Y := GradedCompositionData.Obj.mk Q)
    (Z := GradedCompositionData.Obj.mk R) (graphCorrespondenceSP f) (graphCorrespondenceSP g)
  have hgf : graphCorr k P.obj.hom R.obj.hom (g.hom.left ≫ f.hom.left)
      (by rw [Category.assoc, Over.w f.hom, Over.w g.hom]) =
      SmoothProjectiveCorr.toCorr P R 0 (graphCorrespondenceSP (g ≫ f)) :=
    rfl
  have h₁ : SmoothProjectiveCorr.toCorr P R (0 + 0)
      ((correspondenceCompositionData k Δ hassoc hΔ).comp (graphCorrespondenceSP f)
        (graphCorrespondenceSP g)) =
      corrCongr k P.obj.hom R.obj.hom (add_zero 0).symm
        (SmoothProjectiveCorr.toCorr P R 0 (graphCorrespondenceSP (g ≫ f))) :=
    (toCorr_correspondenceCompositionData_comp k Δ hassoc hΔ _ _).trans
      ((hΔ.comp_graphCorr k P.obj.hom Q.obj.hom R.obj.hom f.hom.left (Over.w f.hom) g.hom.left
        (Over.w g.hom)).trans (congrArg (corrCongr k P.obj.hom R.obj.hom (add_zero 0).symm) hgf))
  have h₂ := (LinearEquiv.eq_symm_apply (SmoothProjectiveCorr.toCorr P R (0 + 0))).mpr h₁
  simp only [graphHom]
  rw [h₀, h₂]
  exact of_toCorr_symm_corrCongr _ (graphCorrespondenceSP (g ≫ f))

/-- The contravariant functor from smooth projective schemes over `k` to the category of
correspondences which is the identity on objects and sends `f : Q ⟶ P` to the class
`[Γ_f] ∈ Corr⁰(P, Q)` of its graph, for a family of diagonal classes satisfying associativity and
the proper-intersection formula.

Stacks 0FG3 is its instance at the canonical family of Gysin classes of diagonals (Stacks 0FBR),
where both properties are theorems: `Stacks.WeilCohomology.canonicalGraphFunctor`. -/
def graphFunctor (k : Type u) [Field k] (Δ : DiagonalClassFamily k) (hassoc : Δ.CompositionAssoc)
    (hΔ : Δ.ProperIntersectionFormula) :
    ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ ⥤
      (correspondenceCompositionData k Δ hassoc hΔ).Obj where
  obj P := GradedCompositionData.Obj.mk P.unop
  map f := graphHom f.unop
  map_id P := graphHom_id P.unop
  map_comp f g := (graphHom_comp f.unop g.unop).symm

/-- The graph functor is the identity on objects. -/
@[simp]
theorem graphFunctor_obj (P : ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ) :
    ((graphFunctor k Δ hassoc hΔ).obj P).as = P.unop :=
  rfl

/-- The graph functor sends `f` to the class of its graph. -/
@[simp]
theorem graphFunctor_map {P Q : ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ} (f : P ⟶ Q) :
    (graphFunctor k Δ hassoc hΔ).map f = graphHom f.unop :=
  rfl

end Stacks.WeilCohomology

end
