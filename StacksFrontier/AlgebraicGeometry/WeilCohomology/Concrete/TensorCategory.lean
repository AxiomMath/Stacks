module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Monoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Tensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalGradedCategory

/-!
# The tensor product on the category of correspondences

This file transports the tensor product of correspondences of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Tensor` to the graded category of
correspondences of Stacks 0FG2, `(canonicalCorrespondenceCompositionData k).Obj`. It also
defines the constraints that Stacks 0FG7 uses there. The associativity, unit and commutativity
constraints are the graphs of the corresponding isomorphisms of smooth projective schemes (see
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Monoidal`), taken through the graph
functor of Stacks 0FG3.

## Main definitions

* `Stacks.WeilCohomology.CorrespondenceCategory k`: the category of correspondences of
  Stacks 0FG2, a name for `(canonicalCorrespondenceCompositionData k).Obj`.
* `Stacks.WeilCohomology.CorrespondenceCategory.tensorObj`: `X ⊗ Y = X × Y`.
* `Stacks.WeilCohomology.CorrespondenceCategory.tensorCorr`: the tensor product of homogeneous
  correspondences, `Corrʳ(X, Y) × Corr^{r'}(X', Y') ⟶ Corr^{r+r'}(X × X', Y × Y')`.
* `Stacks.WeilCohomology.CorrespondenceCategory.tensorHom`: its bilinear extension to the
  morphisms `⨁ᵣ Corrʳ` of the category of correspondences.
* `Stacks.WeilCohomology.CorrespondenceCategory.graphIso`: the graph of an isomorphism of smooth
  projective schemes, as an isomorphism of correspondences;
  `Stacks.WeilCohomology.CorrespondenceCategory.associatorIso`, `leftUnitorIso`,
  `rightUnitorIso` and `braidingIso` are the graphs of the constraints of
  `Stacks.WeilCohomology.SmoothProjectiveScheme`.

## Main results

* `Stacks.WeilCohomology.CorrespondenceCategory.tensorHom_of_of`: on homogeneous morphisms the
  tensor product is the tensor product of correspondences, and degrees add.
* `Stacks.WeilCohomology.CorrespondenceCategory.tensorHom_mem_grade`: the tensor product of
  morphisms of degrees `r` and `r'` has degree `r + r'`.
* `Stacks.WeilCohomology.CorrespondenceCategory.graphIso_hom_mem_grade` and
  `graphIso_inv_mem_grade`: the graph constraints have degree `0`.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

/-- **The category of correspondences** of Stacks 0FG2 over the field `k`: smooth projective
schemes over `k`, with morphisms `⨁ᵣ Corrʳ(X, Y)` composed by composition of correspondences
formed with the canonical diagonal classes. -/
abbrev CorrespondenceCategory : Type (u + 1) :=
  (canonicalCorrespondenceCompositionData k).Obj

namespace CorrespondenceCategory

variable {k}

/-- The tensor product of objects of the category of correspondences: the product over `k`. -/
abbrev tensorObj (X Y : CorrespondenceCategory k) : CorrespondenceCategory k :=
  GradedCompositionData.Obj.mk (X.as ⊗ Y.as)

/-- The unit object of the category of correspondences: `Spec k`. -/
abbrev tensorUnit : CorrespondenceCategory k :=
  GradedCompositionData.Obj.mk (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))

/-- The tensor product of homogeneous correspondences between smooth projective schemes,
`Corrʳ(X, Y) × Corr^{r'}(X', Y') ⟶ Corr^{r+r'}(X × X', Y × Y')`, `c ⊗ c' = pr₁₃^* c · pr₂₄^* c'`,
formed with the canonical diagonal classes. -/
def tensorCorr {X Y X' Y' : (SmoothProjectiveScheme k).FullSubcategory} (r r' : ℤ) :
    SmoothProjectiveCorr X Y r →ₗ[ℚ] SmoothProjectiveCorr X' Y' r' →ₗ[ℚ]
      SmoothProjectiveCorr (X ⊗ X') (Y ⊗ Y') (r + r') :=
  ((tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) r
      r').compl₁₂
    (SmoothProjectiveCorr.toCorr X Y r).toLinearMap
    (SmoothProjectiveCorr.toCorr X' Y' r').toLinearMap).compr₂
    (SmoothProjectiveCorr.toCorr (X ⊗ X') (Y ⊗ Y') (r + r')).symm.toLinearMap

/-- Under the identification of `SmoothProjectiveCorr` with correspondences of the underlying
schemes, `tensorCorr` is the tensor product of correspondences formed with the canonical
diagonal classes. -/
theorem toCorr_tensorCorr {X Y X' Y' : (SmoothProjectiveScheme k).FullSubcategory} (r r' : ℤ)
    (a : SmoothProjectiveCorr X Y r) (b : SmoothProjectiveCorr X' Y' r') :
    SmoothProjectiveCorr.toCorr (X ⊗ X') (Y ⊗ Y') (r + r') (tensorCorr r r' a b) =
      tensor k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k) r r'
        (SmoothProjectiveCorr.toCorr X Y r a) (SmoothProjectiveCorr.toCorr X' Y' r' b) :=
  rfl

/-- The tensor product of morphisms of the category of correspondences: the bilinear extension of
`Stacks.WeilCohomology.CorrespondenceCategory.tensorCorr` to `⨁ᵣ Corrʳ`. -/
def tensorHomLinear (X Y X' Y' : (SmoothProjectiveScheme k).FullSubcategory) :
    TotalCorrespondence (fun P Q r ↦ SmoothProjectiveCorr P Q r) X Y →ₗ[ℚ]
      TotalCorrespondence (fun P Q r ↦ SmoothProjectiveCorr P Q r) X' Y' →ₗ[ℚ]
        TotalCorrespondence (fun P Q r ↦ SmoothProjectiveCorr P Q r) (X ⊗ X') (Y ⊗ Y') :=
  DirectSum.toModule ℚ ℤ _ fun r ↦
    (DirectSum.toModule ℚ ℤ _ fun r' ↦
      ((tensorCorr r r').compr₂ (DirectSum.lof ℚ ℤ
        (fun i ↦ SmoothProjectiveCorr (X ⊗ X') (Y ⊗ Y') i) (r + r'))).flip).flip

/-- The tensor product of two morphisms of the category of correspondences. -/
def tensorHom {X₁ Y₁ X₂ Y₂ : CorrespondenceCategory k} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  tensorHomLinear X₁.as Y₁.as X₂.as Y₂.as f g

/-- On homogeneous morphisms the tensor product is the tensor product of correspondences, and
degrees add. -/
@[simp]
theorem tensorHom_of_of {X₁ Y₁ X₂ Y₂ : CorrespondenceCategory k} {r r' : ℤ}
    (a : SmoothProjectiveCorr X₁.as Y₁.as r) (b : SmoothProjectiveCorr X₂.as Y₂.as r') :
    tensorHom (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₁.as Y₁.as i) r a)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₂.as Y₂.as i) r' b) =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr (X₁.as ⊗ X₂.as) (Y₁.as ⊗ Y₂.as) i) (r + r')
        (tensorCorr r r' a b) := by
  rw [← DirectSum.lof_eq_of ℚ, ← DirectSum.lof_eq_of ℚ, ← DirectSum.lof_eq_of ℚ, tensorHom,
    tensorHomLinear, DirectSum.toModule_lof, LinearMap.flip_apply, DirectSum.toModule_lof,
    LinearMap.flip_apply, LinearMap.compr₂_apply]

/-- The tensor product of morphisms of degrees `r` and `r'` has degree `r + r'`. -/
theorem tensorHom_mem_grade {X₁ Y₁ X₂ Y₂ : CorrespondenceCategory k} {f : X₁ ⟶ Y₁}
    {g : X₂ ⟶ Y₂} {r r' : ℤ} (hf : f ∈ GradedCategory.grade (R := ℚ) X₁ Y₁ r)
    (hg : g ∈ GradedCategory.grade (R := ℚ) X₂ Y₂ r') :
    tensorHom f g ∈ GradedCategory.grade (R := ℚ) (tensorObj X₁ X₂) (tensorObj Y₁ Y₂) (r + r') := by
  obtain ⟨a, rfl⟩ := (GradedCompositionData.mem_grade_iff _).1 hf
  obtain ⟨b, rfl⟩ := (GradedCompositionData.mem_grade_iff _).1 hg
  rw [tensorHom_of_of]
  exact (GradedCompositionData.mem_grade_iff _).2 ⟨_, rfl⟩

/-! ### Graphs of isomorphisms -/

/-- The graph of an isomorphism `e : X ≅ Y` of smooth projective schemes over `k`, as an
isomorphism of correspondences `X ≅ Y`. Its forward morphism is the class `[Γ_{e⁻¹}]` of the
graph of `e⁻¹ : Y ⟶ X` in `Corr⁰(X, Y)`, which as a cycle on `X × Y` is the graph of `e`. -/
def graphIso {X Y : (SmoothProjectiveScheme k).FullSubcategory} (e : X ≅ Y) :
    (GradedCompositionData.Obj.mk X : CorrespondenceCategory k) ≅ GradedCompositionData.Obj.mk Y :=
  (canonicalGraphFunctor k).mapIso e.symm.op

/-- The forward morphism of `graphIso e` is the graph of `e.inv`. -/
theorem graphIso_hom {X Y : (SmoothProjectiveScheme k).FullSubcategory} (e : X ≅ Y) :
    (graphIso e).hom = graphHom e.inv :=
  rfl

/-- The inverse morphism of `graphIso e` is the graph of `e.hom`. -/
theorem graphIso_inv {X Y : (SmoothProjectiveScheme k).FullSubcategory} (e : X ≅ Y) :
    (graphIso e).inv = graphHom e.hom :=
  rfl

/-- The graph of an isomorphism has degree `0`. -/
theorem graphIso_hom_mem_grade {X Y : (SmoothProjectiveScheme k).FullSubcategory} (e : X ≅ Y) :
    (graphIso e).hom ∈ GradedCategory.grade (R := ℚ) (GradedCompositionData.Obj.mk X :
      CorrespondenceCategory k) (GradedCompositionData.Obj.mk Y) 0 :=
  graphHom_mem_grade e.inv

/-- The inverse of the graph of an isomorphism has degree `0`. -/
theorem graphIso_inv_mem_grade {X Y : (SmoothProjectiveScheme k).FullSubcategory} (e : X ≅ Y) :
    (graphIso e).inv ∈ GradedCategory.grade (R := ℚ) (GradedCompositionData.Obj.mk Y :
      CorrespondenceCategory k) (GradedCompositionData.Obj.mk X) 0 :=
  graphHom_mem_grade e.hom

/-- The associativity constraint of the category of correspondences: the graph of the
associativity isomorphism `(X × Y) × Z ≅ X × (Y × Z)` of products of schemes. -/
abbrev associatorIso (X Y Z : CorrespondenceCategory k) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  graphIso (α_ X.as Y.as Z.as)

/-- The left unit constraint of the category of correspondences: the graph of
`Spec k × X ≅ X`. -/
abbrev leftUnitorIso (X : CorrespondenceCategory k) : tensorObj tensorUnit X ≅ X :=
  graphIso (λ_ X.as)

/-- The right unit constraint of the category of correspondences: the graph of
`X × Spec k ≅ X`. -/
abbrev rightUnitorIso (X : CorrespondenceCategory k) : tensorObj X tensorUnit ≅ X :=
  graphIso (ρ_ X.as)

/-- The commutativity constraint of the category of correspondences: the graph of the factor
switch `X × Y ≅ Y × X`. -/
abbrev braidingIso (X Y : CorrespondenceCategory k) : tensorObj X Y ≅ tensorObj Y X :=
  graphIso (β_ X.as Y.as)

end CorrespondenceCategory

end Stacks.WeilCohomology

end
