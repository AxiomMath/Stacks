module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationEvaluationSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryHomEquivTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparisonNaturality

/-!
# The transpose of the comparison of Stacks 08DM at a K-flat source

Let `X` be a ringed site and `B`, `C` complexes of `O`-modules with `B` K-flat.  The comparison
`σ : Q SheafHom(B, C) ⟶ RSheafHom(QB, QC)` of Stacks 08DM transposes, under the bijection of
Stacks 08J8, to the cochain-level evaluation `SheafHom(B, C) ⊗ B ⟶ C` of Stacks 0A90 read through
the canonical map `toTensor` of Stacks 06YU:

`derivedCurryHomEquiv σ = toTensor (SheafHom(B, C), B) ≫ Q(ev)`.

No hypothesis is made on `C`.

## Main results

* `AlgebraicGeometry.RingedSite.cochainEvaluation_naturality_target`: the cochain-level evaluation
  is natural in the target.
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_strictlyPerfectHomComparison`: the identity
  above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The cochain-level evaluation is natural in the target.**  For `v : C ⟶ C'`, evaluating
after the map `SheafHom(B, C) ⟶ SheafHom(B, C')` induced by `v` is evaluating and then applying
`v`. -/
theorem cochainEvaluation_naturality_target
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {C C' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (v : C ⟶ C') :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (homMap X (𝟙 B) v)).app B ≫
        cochainEvaluation X B C' =
      cochainEvaluation X B C ≫ v := by
  have hce : ∀ D : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      curryHomEquiv X (sheafHomComplex X B D).obj B D (𝟙 (sheafHomComplex X B D).obj) =
        cochainEvaluation X B D := fun D => by
    rw [← curryHomEquiv_symm_cochainEvaluation X B D]
    exact (curryHomEquiv X (sheafHomComplex X B D).obj B D).apply_symm_apply _
  have h₁ := curryHomEquiv_naturality_target X (sheafHomComplex X B C).obj B v
    (𝟙 (sheafHomComplex X B C).obj)
  have h₂ := curryHomEquiv_naturality_source X (homMap X (𝟙 B) v) B C'
    (𝟙 (sheafHomComplex X B C').obj)
  rw [Category.id_comp, hce] at h₁
  rw [Category.comp_id, hce] at h₂
  exact h₂.symm.trans h₁

/-- A square `q₁ ≫ q₂ = q₃ ≫ a` with `a` invertible, read as `(t ≫ q₁) ≫ q₂ ≫ a⁻¹ = t ≫ q₃`. -/
private lemma comp_inv_of_square {C : Type*} [Category C] {P Q₀ Q₁ R R' : C} (t : P ⟶ Q₀)
    (q₁ : Q₀ ⟶ Q₁) (q₂ : Q₁ ⟶ R') (q₃ : Q₀ ⟶ R) (a : R ⟶ R') [IsIso a]
    (h : q₁ ≫ q₂ = q₃ ≫ a) : ((t ≫ q₁) ≫ q₂) ≫ inv a = t ≫ q₃ := by
  simp only [Category.assoc]
  rw [reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]

/-- **The transpose of the comparison of Stacks 08DM at a K-flat source.**  For complexes `B`,
`C` of `O`-modules with `B` K-flat, the comparison
`σ : Q SheafHom(B, C) ⟶ RSheafHom(QB, QC)` transposes under the bijection of Stacks 08J8 to the
canonical map `Q SheafHom(B, C) ⊗^L QB ⟶ Q Tot(SheafHom(B, C) ⊗ B)` of Stacks 06YU followed by
the class of the cochain-level evaluation of Stacks 0A90. -/
theorem derivedCurryHomEquiv_strictlyPerfectHomComparison
    (B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) :
    derivedCurryHomEquiv X (DerivedCategory.Q.obj (sheafHomComplex X B C).obj)
        (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C)
        (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C) =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor
          (sheafHomComplex X B C).obj B ≫
        DerivedCategory.Q.map (cochainEvaluation X B C) := by
  have : IsIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app C)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have hσ : strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C =
      (DerivedCategory.Q.map (homMap X (𝟙 B) ((kInjectiveAugmentation X).app C)) ≫
        (derivedSheafHomComparison X B ((kInjectiveResolution X).obj C)).inv) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).map
            (inv (DerivedCategory.Q.map ((kInjectiveAugmentation X).app C))) := by
    rw [Functor.map_inv, Category.assoc]
    rfl
  rw [hσ, derivedCurryHomEquiv_naturality_target, derivedCurryHomEquiv_naturality_source,
    derivedCurryHomEquiv_eq_tensor_evaluation X _ _ _
      (derivedSheafHomComparison X B ((kInjectiveResolution X).obj C)).inv,
    derivedApplication_eq_cochainEvaluation X B ((kInjectiveResolution X).obj C) hB,
    ← (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor_eq_comparisonRight _ _ hB]
  have htt := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor_naturality
    (homMap X (𝟙 B) ((kInjectiveAugmentation X).app C)) (𝟙 B)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at htt
  rw [← Category.assoc _ ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor _ _),
    htt]
  have hev := congrArg DerivedCategory.Q.map
    (cochainEvaluation_naturality_target X B ((kInjectiveAugmentation X).app C))
  rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp] at hev
  exact comp_inv_of_square _ _ _ _ _ hev

end AlgebraicGeometry.RingedSite

end
