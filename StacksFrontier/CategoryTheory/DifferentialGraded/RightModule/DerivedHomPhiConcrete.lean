module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomChainIdentification
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomUnitNormalisation
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.LinkApplyLemmas
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.LinkOneModuleNaturality
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.GradedCohomologyFunctorial
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomReflectorData

/-!
# The identification `(*)` of Tag 09LK at one reflector

Let `L` be a reflector onto the `N`-local objects with unit `η`. The isomorphism
`DGCategory.derivedHomReflectorGradedCohomologyIso` identifies `H^n(U(R̃(q y)))` with the explicit
cohomology of the reflected evaluation `ev_x (L h_y)`, and the chain
`DGCategory.RightModule.chainEquivReflectorEvaluation` is a bijection out of that explicit
cohomology. Both taken at the same `L` and `η`, their composite is a bijection

`φ : H^n(U(R̃(q y))) ≃ Hom_{DA}(q x, (q y)⟦n⟧)`,

and `φ` is natural in every morphism `s : y₁ ⟶ y₂` of `K(C)`:

`φ y₂ (H^n(U(R̃(q s))) z) = φ y₁ z ≫ (q s)⟦n⟧`.

## Main definitions

* `DGCategory.derivedHomPhi`: the composite `φ`, as a bijection.

## Main results

* `CategoryTheory.conj_comp_shiftIso_naturality`: conjugation by an isomorphism
  `ε : q₁ ⋙ F ≅ q₂`, with the shift moved out of the target, is natural in the target variable.
* `CategoryTheory.homShiftEquivOfIsLocalization_naturality`,
  `CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift_naturality`,
  `CategoryTheory.ObjectProperty.homEquivReflectorShift_naturality`,
  `DGCategory.RightModule.homEquivDerivedYonedaOnK_naturality` and
  `DGCategory.RightModule.homShiftEquivEvaluationGradedCohomology_symm_evaluationOnK_mapK`: the
  naturality of each link of the chain in the module variable.
* `DGCategory.RightModule.chainEquivReflectorEvaluation_naturality`: the chain is natural.
* `DGCategory.derivedHomReflectorGradedCohomologyIso_hom_naturality`: the identification of
  `H^n(U(R̃(q y)))` with the explicit cohomology is natural.
* `DGCategory.derivedHomPhi_injective` and `DGCategory.derivedHomPhi_covariant`: `φ` is injective
  and covariantly natural.
* `DGCategory.exists_derivedHomPhi`: there is a reflector at which such a `φ` exists.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.ObjectProperty

universe w v₁ v₂ u₁ u₂ u₀ v u v' u' r

namespace CategoryTheory

section Conj

variable {S : Type u} [Category.{v} S] [HasShift S ℤ]
  {D₁ : Type u₁} [Category.{v₁} D₁] [HasShift D₁ ℤ]
  {D₂ : Type u₂} [Category.{v₂} D₂] [HasShift D₂ ℤ]
  (q₁ : S ⥤ D₁) [q₁.CommShift ℤ] (q₂ : S ⥤ D₂) [q₂.CommShift ℤ]
  (F : D₁ ⥤ D₂) [F.CommShift ℤ] (ε : q₁ ⋙ F ≅ q₂)

omit [HasShift S ℤ] [q₁.CommShift ℤ] [q₂.CommShift ℤ] in
/-- For `ε : q₁ ⋙ F ≅ q₂`, the map sending `h : q₁ x ⟶ (q₁ y)⟦n⟧` to
`ε⁻¹ ≫ F h ≫ (F.commShiftIso n).hom ≫ ε⟦n⟧` is natural in `y`. -/
theorem conj_comp_shiftIso_naturality (x y₁ y₂ : S) (n : ℤ) (t : y₁ ⟶ y₂)
    (h : q₁.obj x ⟶ (q₁.obj y₁)⟦n⟧) :
    ε.inv.app x ≫ F.map (h ≫ (shiftFunctor D₁ n).map (q₁.map t)) ≫
        (F.commShiftIso n).hom.app (q₁.obj y₂) ≫
          (shiftFunctor D₂ n).map (ε.hom.app y₂) =
      ε.inv.app x ≫ F.map h ≫ (F.commShiftIso n).hom.app (q₁.obj y₁) ≫
        (shiftFunctor D₂ n).map (ε.hom.app y₁) ≫
          (shiftFunctor D₂ n).map (q₂.map t) := by
  have hε : F.map (q₁.map t) ≫ ε.hom.app y₂ = ε.hom.app y₁ ≫ q₂.map t := ε.hom.naturality t
  have hcomm := F.commShiftIso_hom_naturality (q₁.map t) n
  simp only [Functor.map_comp, assoc]
  rw [reassoc_of% hcomm, ← Functor.map_comp, hε, Functor.map_comp]

end Conj

section Engine1

variable {S : Type u} [Category.{v} S] [HasShift S ℤ]
  {D₁ : Type u₁} [Category.{v₁} D₁] [HasShift D₁ ℤ]
  {D₂ : Type u₂} [Category.{v₂} D₂] [HasShift D₂ ℤ]
  (W : MorphismProperty S)
  (q₁ : S ⥤ D₁) [q₁.IsLocalization W] [q₁.CommShift ℤ]
  (q₂ : S ⥤ D₂) [q₂.IsLocalization W] [q₂.CommShift ℤ]

/-- `CategoryTheory.homShiftEquivOfIsLocalization` is natural in the target variable: it carries
postcomposition with `(q₁ t)⟦n⟧` to postcomposition with `(q₂ t)⟦n⟧`. -/
theorem homShiftEquivOfIsLocalization_naturality (x y₁ y₂ : S) (n : ℤ) (t : y₁ ⟶ y₂)
    (h : q₁.obj x ⟶ (q₁.obj y₁)⟦n⟧) :
    homShiftEquivOfIsLocalization W q₁ q₂ x y₂ n
        (h ≫ (shiftFunctor D₁ n).map (q₁.map t)) =
      homShiftEquivOfIsLocalization W q₁ q₂ x y₁ n h ≫
        (shiftFunctor D₂ n).map (q₂.map t) := by
  let := commShiftUniqFunctor W q₁ q₂
  simp only [homShiftEquivOfIsLocalization_apply, uniqFunctorShiftIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, assoc]
  exact conj_comp_shiftIso_naturality q₁ q₂ (Localization.uniq q₁ q₂ W).functor
    (Localization.compUniqFunctor q₁ q₂ W) x y₁ y₂ n t h

end Engine1

namespace ObjectProperty

section Engine2

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (A N : ObjectProperty C) [A.IsClosedUnderIsomorphisms] [A.IsTriangulated]
  [N.IsClosedUnderIsomorphisms] [N.IsTriangulated]
  {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  (L : A.FullSubcategory ⥤ D) [L.IsLocalization (N.inverseImage A.ι).trW] [L.CommShift ℤ]
  [L.IsTriangulated]

omit [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] [L.IsTriangulated] [A.IsClosedUnderIsomorphisms] in
/-- `CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift` is natural in the target
variable. -/
theorem homEquivVerdierEmbeddingShift_naturality [A.IsVerdierLeftLocalizing N]
    (x y₁ y₂ : A.FullSubcategory) (n : ℤ) (t : y₁ ⟶ y₂)
    (h : L.obj x ⟶ (L.obj y₁)⟦n⟧) :
    homEquivVerdierEmbeddingShift A N L x y₂ n (h ≫ (shiftFunctor D n).map (L.map t)) =
      homEquivVerdierEmbeddingShift A N L x y₁ n h ≫
        (shiftFunctor N.trW.Localization n).map ((A.ι ⋙ N.trW.Q).map t) := by
  let := A.verdierEmbeddingCommShift N L
  simp only [homEquivVerdierEmbeddingShift_apply, verdierEmbeddingShiftIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, assoc]
  exact conj_comp_shiftIso_naturality L (A.ι ⋙ N.trW.Q) (A.verdierEmbedding N L)
    (verdierEmbeddingCompIso A N L) x y₁ y₂ n t h

end Engine2

/-! ### Link 2 -/

section Reflector

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)
  {D : Type u'} [Category.{v'} D] (Q : C ⥤ D)
  [Q.IsLocalization P.localizingClosure.{w}.trW] [HasShift D ℤ] [IsTriangulated C]
  [Q.CommShift ℤ] {L : C ⥤ C} {η : 𝟭 C ⟶ L}

/-- `CategoryTheory.ObjectProperty.homEquivReflectorShift` is natural in the reflected variable:
it carries postcomposition with `(L t)⟦n⟧` to postcomposition with `(Q t)⟦n⟧`. -/
theorem homEquivReflectorShift_naturality
    (hL : ∀ X, P.localizingClosure.{w}.rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (A : C) {X Y : C} (t : X ⟶ Y) (n : ℤ) (f : A ⟶ (L.obj X)⟦n⟧) :
    P.homEquivReflectorShift Q hL hη A Y n (f ≫ (shiftFunctor C n).map (L.map t)) =
      P.homEquivReflectorShift Q hL hη A X n f ≫ (shiftFunctor D n).map (Q.map t) := by
  have hhom : Q.map t ≫ (P.localizingClosureUnitIso Q hη Y).hom =
      (P.localizingClosureUnitIso Q hη X).hom ≫ Q.map (L.map t) := by
    rw [P.localizingClosureUnitIso_hom Q hη, P.localizingClosureUnitIso_hom Q hη,
      ← Q.map_comp, ← Q.map_comp]
    exact congrArg Q.map (η.naturality t)
  have hu : Q.map (L.map t) ≫ (P.localizingClosureUnitIso Q hη Y).inv =
      (P.localizingClosureUnitIso Q hη X).inv ≫ Q.map t := by
    rw [Iso.comp_inv_eq, assoc, hhom, Iso.inv_hom_id_assoc]
  rw [homEquivReflectorShift_apply, homEquivReflectorShift_apply, Q.map_comp]
  simp only [Iso.app_hom, assoc]
  rw [reassoc_of% (Q.commShiftIso_hom_naturality (L.map t) n), ← Functor.map_comp, hu,
    Functor.map_comp]

end Reflector

end ObjectProperty

end CategoryTheory

/-! ### Links 1 and 4 -/

namespace DGCategory

namespace RightModule

section Bridge

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u₀} R}

attribute [local implicit_reducible] DGCategory.K

/-- The inverse of `DGCategory.RightModule.homShiftEquivEvaluationGradedCohomology` carries the
map that `ev_x u` induces on the explicit cohomology to postcomposition with the shift of `u`. -/
theorem homShiftEquivEvaluationGradedCohomology_symm_evaluationOnK_mapK
    {M N : (rightModuleCategory.{v} C).K} (u : M ⟶ N) (x : C.Obj)
    (e : (endDGCategory C x).Obj) (n : ℤ)
    (c : gradedCohomology ((evaluationDGFunctor.{v} C x).obj M) e n) :
    (homShiftEquivEvaluationGradedCohomology N x e n).symm
        ((gradedCohomologyMapK ((evaluationOnK.{v} C x).map u) e n) c) =
      (homShiftEquivEvaluationGradedCohomology M x e n).symm c ≫
        (shiftFunctor (rightModuleCategory.{v} C).K n).map u := by
  induction u using Quotient.inductionOn with
  | _ ψ =>
    have hmk := ConcreteCategory.congr_hom (C := ModuleCat.{v} R)
      (gradedCohomologyMapK_mk ((evaluationDGFunctor.{v} C x).mapCocycle ψ) e n) c
    have hval := homShiftEquivEvaluationGradedCohomology_comp ψ x e n
      ((homShiftEquivEvaluationGradedCohomology M x e n).symm c)
    have hsa := Equiv.apply_symm_apply (homShiftEquivEvaluationGradedCohomology M x e n) c
    exact (Equiv.symm_apply_eq _).2
      (hmk.trans ((congrArg (gradedCohomologyMapOf ψ x n) hsa).symm.trans hval.symm))

end Bridge

variable {R : Type r} [CommRing R]
  (C : DGCategory.{v, v} R) [Preadditive C.K] [HasZeroObject C.K] [HasShift C.K ℤ]
  [∀ n : ℤ, (shiftFunctor C.K n).Additive] [Pretriangulated C.K] [IsTriangulated C.K]
  [((yonedaDGFunctor C).onK).CommShift ℤ] [((yonedaDGFunctor C).onK).IsTriangulated]
  {ι : Type v} (G : ι → C.Obj)

attribute [local implicit_reducible] DGCategory.K

omit [IsTriangulated C.K] in
/-- `DGCategory.RightModule.homEquivDerivedYonedaOnK` is natural in the target variable. -/
theorem homEquivDerivedYonedaOnK_naturality {DA : Type u'} [Category.{v'} DA] [HasShift DA ℤ]
    (q : C.K ⥤ DA) [q.IsLocalization (yonedaInverseImage C G).trW] [q.CommShift ℤ]
    (x : C.K) {y₁ y₂ : C.K} (s : y₁ ⟶ y₂) (n : ℤ)
    (h : q.obj x ⟶ (q.obj y₁)⟦n⟧) :
    homEquivDerivedYonedaOnK C G q x y₂ n (h ≫ (shiftFunctor DA n).map (q.map s)) =
      homEquivDerivedYonedaOnK C G q x y₁ n h ≫
        (shiftFunctor (yonedaLocalizing C G).trW.Localization n).map
          ((yonedaLocalizing C G).trW.Q.map (((yonedaDGFunctor C).onK).map s)) := by
  have := isLocalization_yonedaLift_comp C G
  have := isVerdierLeftLocalizing_yonedaImage C G
  change homEquivYonedaImageVerdier C G ((yonedaLift C).obj x) ((yonedaLift C).obj y₂) n
      (homShiftEquivOfIsLocalization (yonedaInverseImage C G).trW q
        (yonedaLift C ⋙ yonedaImageQ C G) x y₂ n
        (h ≫ (shiftFunctor DA n).map (q.map s))) = _
  rw [homShiftEquivOfIsLocalization_naturality]
  exact homEquivVerdierEmbeddingShift_naturality (yonedaImage C) (yonedaLocalizing C G)
    (yonedaImageQ C G) ((yonedaLift C).obj x) ((yonedaLift C).obj y₁)
    ((yonedaLift C).obj y₂) n ((yonedaLift C).map s) _

omit [IsTriangulated C.K] in
/-- `DGCategory.RightModule.homEquivDerivedYonedaOnK'` is natural in the target variable. -/
theorem homEquivDerivedYonedaOnK'_naturality {DA : Type u'} [Category.{v'} DA] [HasShift DA ℤ]
    (q : C.K ⥤ DA) [q.IsLocalization (yonedaInverseImage C G).trW] [q.CommShift ℤ]
    (x : C.K) {y₁ y₂ : C.K} (s : y₁ ⟶ y₂) (n : ℤ)
    (h : q.obj x ⟶ (q.obj y₁)⟦n⟧) :
    homEquivDerivedYonedaOnK' C G q x y₂ n (h ≫ (shiftFunctor DA n).map (q.map s)) =
      homEquivDerivedYonedaOnK' C G q x y₁ n h ≫
        (shiftFunctor (ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Localization
            n).map
          ((ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q.map
            (((yonedaDGFunctor C).onK).map s)) :=
  homEquivDerivedYonedaOnK_naturality C G q x s n h

/-! ### The chain -/

section Chain

variable {L : (rightModuleCategory.{v} C).K ⥤ (rightModuleCategory.{v} C).K} [L.CommShift ℤ]
  {η : 𝟭 (rightModuleCategory.{v} C).K ⟶ L}
  (hL : ∀ X, (yonedaLocalizing C G).rightOrthogonal (L.obj X))
  (hη : ∀ (X Z : (rightModuleCategory.{v} C).K) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
    Triangle.mk f (η.app X) g ∈ distTriang (rightModuleCategory.{v} C).K →
      yonedaLocalizing C G Z)
  {DA : Type u'} [Category.{v'} DA] [HasShift DA ℤ] (q : C.K ⥤ DA)
  [q.IsLocalization (yonedaInverseImage C G).trW] [q.CommShift ℤ]

omit [IsTriangulated C.K] in
/-- The chain `(*)` of [Stacks, Tag 09LK] is natural in the source variable: it carries the map
induced by `L s` to postcomposition with `(q s)⟦n⟧`. -/
theorem chainEquivReflectorEvaluation_naturality (x : C.K) {y₁ y₂ : C.K} (s : y₁ ⟶ y₂)
    (e : (endDGCategory C (x : C.Obj)).Obj) (n : ℤ)
    (c : gradedCohomology ((evaluationDGFunctor.{v} C (x : C.Obj)).obj
      (L.obj (yonedaObjK (y₁ : C.Obj)))) e n) :
    chainEquivReflectorEvaluation C G hL hη q x y₂ e n
        ((gradedCohomologyMapK ((evaluationOnK.{v} C (x : C.Obj)).map
          (L.map (((yonedaDGFunctor C).onK).map s))) e n) c) =
      chainEquivReflectorEvaluation C G hL hη q x y₁ e n c ≫
        (shiftFunctor DA n).map (q.map s) := by
  refine homEquivDerivedYonedaOnK'_injective C G q x y₂ n ?_
  refine Eq.trans (Equiv.apply_symm_apply (homEquivDerivedYonedaOnK' C G q x y₂ n) _) ?_
  refine Eq.trans (congrArg
    (fun z ↦ homEquivReflectorShift (ofObj fun i ↦ yonedaObjK (G i))
      (ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q hL hη
      (yonedaObjK (x : C.Obj)) (yonedaObjK (y₂ : C.Obj)) n z)
    (homShiftEquivEvaluationGradedCohomology_symm_evaluationOnK_mapK
      (L.map (((yonedaDGFunctor C).onK).map s)) (x : C.Obj) e n c)) ?_
  refine Eq.trans (homEquivReflectorShift_naturality (ofObj fun i ↦ yonedaObjK (G i))
    (ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q hL hη
    (yonedaObjK (x : C.Obj)) (((yonedaDGFunctor C).onK).map s) n _) ?_
  refine Eq.trans ?_ (homEquivDerivedYonedaOnK'_naturality C G q x s n
    (chainEquivReflectorEvaluation C G hL hη q x y₁ e n c)).symm
  exact congrArg (fun z ↦ z ≫ _)
    (Equiv.apply_symm_apply (homEquivDerivedYonedaOnK' C G q x y₁ n) _).symm

end Chain

end RightModule

/-! ### The composite `φ` -/

section Phi

variable {R : Type r} [CommRing R]
  (C : DGCategory.{v, v} R) [Preadditive C.K] [HasZeroObject C.K] [HasShift C.K ℤ]
  [∀ n : ℤ, (shiftFunctor C.K n).Additive] [Pretriangulated C.K] [IsTriangulated C.K]
  [((yonedaDGFunctor C).onK).CommShift ℤ] [((yonedaDGFunctor C).onK).IsTriangulated]
  {ι : Type v} (G : ι → C.Obj)
  [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (L : (rightModuleCategory.{v} C).K ⥤ (rightModuleCategory.{v} C).K)
  [L.CommShift ℤ] [L.IsTriangulated]
  {DA : Type u'} [Category.{v'} DA] [HasZeroObject DA] [HasShift DA ℤ] [Preadditive DA]
  [∀ n : ℤ, (shiftFunctor DA n).Additive] [Pretriangulated DA]
  (q : C.K ⥤ DA) [q.IsLocalization (RightModule.yonedaInverseImage C G).trW] [q.CommShift ℤ]
  [q.IsTriangulated]

attribute [local implicit_reducible] DGCategory.K

omit [HasZeroObject DA] [HasShift DA ℤ] [Preadditive DA] [∀ n : ℤ, (shiftFunctor DA n).Additive]
  [Pretriangulated DA] [q.CommShift ℤ] [q.IsTriangulated] [IsTriangulated C.K] in
/-- `DGCategory.derivedHomReflectorGradedCohomologyIso` is natural in the source variable: for
`s : y₁ ⟶ y₂` in `K(C)` the map that `R̃(q s)` induces on the degree-`n` homology of the forgetful
image corresponds to the map that `ev_x (L h_s)` induces on the explicit cohomology. -/
theorem derivedHomReflectorGradedCohomologyIso_hom_naturality
    (hΦ : ∀ X, RightModule.yonedaInverseImage C G X →
      IsZero (((yonedaDGFunctor C).onK ⋙ L).obj X))
    (x : C.K) (e : (endDGCategory C (x : C.Obj)).Obj) (n : ℤ) {y₁ y₂ : C.K} (s : y₁ ⟶ y₂) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
          ((endDerivedForget C (x : C.Obj)).map
            ((derivedHomReflector C (x : C.Obj) L ((yonedaDGFunctor C).onK)
              (RightModule.yonedaInverseImage C G) q hΦ).map (q.map s))) ≫
        (derivedHomReflectorGradedCohomologyIso C (x : C.Obj) L ((yonedaDGFunctor C).onK)
          (RightModule.yonedaInverseImage C G) q hΦ y₂ e n).hom =
      (derivedHomReflectorGradedCohomologyIso C (x : C.Obj) L ((yonedaDGFunctor C).onK)
          (RightModule.yonedaInverseImage C G) q hΦ y₁ e n).hom ≫
        RightModule.gradedCohomologyMapK
          ((evaluationOnK.{v} C (x : C.Obj)).map
            (L.map (((yonedaDGFunctor C).onK).map s))) e n := by
  have hnat : (derivedHomReflector C (x : C.Obj) L ((yonedaDGFunctor C).onK)
          (RightModule.yonedaInverseImage C G) q hΦ).map (q.map s) ≫
        (derivedHomReflectorCompIso C (x : C.Obj) L ((yonedaDGFunctor C).onK)
          (RightModule.yonedaInverseImage C G) q hΦ).hom.app y₂ =
      (derivedHomReflectorCompIso C (x : C.Obj) L ((yonedaDGFunctor C).onK)
          (RightModule.yonedaInverseImage C G) q hΦ).hom.app y₁ ≫
        (RightModule.derivedQ (endDGCategory C (x : C.Obj))).map
          ((evaluationOnK.{v} C (x : C.Obj)).map
            (L.map (((yonedaDGFunctor C).onK).map s))) :=
    (derivedHomReflectorCompIso C (x : C.Obj) L ((yonedaDGFunctor C).onK)
      (RightModule.yonedaInverseImage C G) q hΦ).hom.naturality s
  rw [derivedHomReflectorGradedCohomologyIso_hom, derivedHomReflectorGradedCohomologyIso_hom,
    ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hnat, Functor.map_comp,
    Functor.map_comp, Category.assoc]
  exact congrArg (fun z ↦ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
      ((endDerivedForget C (x : C.Obj)).map
        ((derivedHomReflectorCompIso C (x : C.Obj) L ((yonedaDGFunctor C).onK)
          (RightModule.yonedaInverseImage C G) q hΦ).hom.app y₁)) ≫ z)
    (RightModule.derivedForgetGradedCohomologyIso_hom_naturality
      (endDGCategory C (x : C.Obj)) e n
      ((evaluationOnK.{v} C (x : C.Obj)).map (L.map (((yonedaDGFunctor C).onK).map s))))

variable {η : 𝟭 (rightModuleCategory.{v} C).K ⟶ L}

/-- **The identification `(*)` of [Stacks, Tag 09LK] at one reflector.** For a reflector `L`
onto the `N`-local objects with unit `η`, the bijection

`H^n(U(R̃(q y))) ≃ Hom_{DA}(q x, (q y)⟦n⟧)`

given by `DGCategory.derivedHomReflectorGradedCohomologyIso` followed by the chain
`DGCategory.RightModule.chainEquivReflectorEvaluation` at the same `L` and `η`. -/
def derivedHomPhi
    (hL : ∀ X, (RightModule.yonedaLocalizing C G).rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : (rightModuleCategory.{v} C).K) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang (rightModuleCategory.{v} C).K →
        RightModule.yonedaLocalizing C G Z)
    (hΦ : ∀ X, RightModule.yonedaInverseImage C G X →
      IsZero (((yonedaDGFunctor C).onK ⋙ L).obj X))
    (x y : C.K) (e : (endDGCategory C (x : C.Obj)).Obj) (n : ℤ) :
    ↥((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
        ((endDerivedForget C (x : C.Obj)).obj
          ((derivedHomReflector C (x : C.Obj) L ((yonedaDGFunctor C).onK)
            (RightModule.yonedaInverseImage C G) q hΦ).obj (q.obj y)))) ≃
      (q.obj x ⟶ (q.obj y)⟦n⟧) :=
  (derivedHomReflectorGradedCohomologyIso C (x : C.Obj) L ((yonedaDGFunctor C).onK)
        (RightModule.yonedaInverseImage C G) q hΦ y e n).toLinearEquiv.toEquiv.trans
    (RightModule.chainEquivReflectorEvaluation C G hL hη q x y e n)

omit [IsTriangulated C.K] [HasZeroObject DA] [Preadditive DA]
  [∀ n : ℤ, (shiftFunctor DA n).Additive] [Pretriangulated DA] [q.IsTriangulated] in
/-- The identification `DGCategory.derivedHomPhi` is injective. -/
theorem derivedHomPhi_injective
    (hL : ∀ X, (RightModule.yonedaLocalizing C G).rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : (rightModuleCategory.{v} C).K) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang (rightModuleCategory.{v} C).K →
        RightModule.yonedaLocalizing C G Z)
    (hΦ : ∀ X, RightModule.yonedaInverseImage C G X →
      IsZero (((yonedaDGFunctor C).onK ⋙ L).obj X))
    (x y : C.K) (e : (endDGCategory C (x : C.Obj)).Obj) (n : ℤ) :
    Function.Injective (derivedHomPhi C G L q hL hη hΦ x y e n) :=
  (derivedHomPhi C G L q hL hη hΦ x y e n).injective

omit [HasZeroObject DA] [Preadditive DA] [∀ n : ℤ, (shiftFunctor DA n).Additive]
  [Pretriangulated DA] [q.IsTriangulated] [IsTriangulated C.K] in
/-- **The covariant naturality square of `(*)`.** For every morphism `s : y₁ ⟶ y₂` of `K(C)` —
not only for a quasi-isomorphism —

`φ y₂ (H^n(U(R̃(q s))) z) = φ y₁ z ≫ (q s)⟦n⟧`. -/
theorem derivedHomPhi_covariant
    (hL : ∀ X, (RightModule.yonedaLocalizing C G).rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : (rightModuleCategory.{v} C).K) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang (rightModuleCategory.{v} C).K →
        RightModule.yonedaLocalizing C G Z)
    (hΦ : ∀ X, RightModule.yonedaInverseImage C G X →
      IsZero (((yonedaDGFunctor C).onK ⋙ L).obj X))
    (x : C.K) {y₁ y₂ : C.K} (s : y₁ ⟶ y₂) (e : (endDGCategory C (x : C.Obj)).Obj) (n : ℤ)
    (z : ↥((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
      ((endDerivedForget C (x : C.Obj)).obj
        ((derivedHomReflector C (x : C.Obj) L ((yonedaDGFunctor C).onK)
          (RightModule.yonedaInverseImage C G) q hΦ).obj (q.obj y₁))))) :
    derivedHomPhi C G L q hL hη hΦ x y₂ e n
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
          ((endDerivedForget C (x : C.Obj)).map
            ((derivedHomReflector C (x : C.Obj) L ((yonedaDGFunctor C).onK)
              (RightModule.yonedaInverseImage C G) q hΦ).map (q.map s))) z) =
      derivedHomPhi C G L q hL hη hΦ x y₁ e n z ≫ (shiftFunctor DA n).map (q.map s) := by
  have hA := ConcreteCategory.congr_hom (C := ModuleCat.{v} R)
    (derivedHomReflectorGradedCohomologyIso_hom_naturality C G L q hΦ x e n s) z
  refine Eq.trans (congrArg
    (fun w ↦ RightModule.chainEquivReflectorEvaluation C G hL hη q x y₂ e n w) hA) ?_
  exact RightModule.chainEquivReflectorEvaluation_naturality C G hL hη q x s e n _

omit [HasZeroObject DA] [Preadditive DA] [∀ n : ℤ, (shiftFunctor DA n).Additive]
  [Pretriangulated DA] [q.IsTriangulated] [IsTriangulated C.K] in
/-- **`(*)` at one reflector.** There is a triangulated endofunctor `L` of the homotopy category
of right modules with `L h_X` zero for every `X` in `Z = Φ⁻¹ N`, together with bijections
`φ : H^n(U(R̃(q y))) ≃ Hom_{DA}(q x, (q y)⟦n⟧)` natural in every morphism `s : y₁ ⟶ y₂` of
`K(C)`. -/
theorem exists_derivedHomPhi (x : C.K) :
    ∃ (L : (rightModuleCategory.{v} C).K ⥤ (rightModuleCategory.{v} C).K)
      (_ : L.CommShift ℤ) (_ : L.IsTriangulated)
      (hΦ : ∀ X, RightModule.yonedaInverseImage C G X →
        IsZero (((yonedaDGFunctor C).onK ⋙ L).obj X))
      (φ : ∀ (y : C.K) (_ : (endDGCategory C (x : C.Obj)).Obj) (n : ℤ),
        ↥((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
            ((endDerivedForget C (x : C.Obj)).obj
              ((derivedHomReflector C (x : C.Obj) L ((yonedaDGFunctor C).onK)
                (RightModule.yonedaInverseImage C G) q hΦ).obj (q.obj y)))) ≃
          (q.obj x ⟶ (q.obj y)⟦n⟧)),
      ∀ (y₁ y₂ : C.K) (s : y₁ ⟶ y₂) (e : (endDGCategory C (x : C.Obj)).Obj) (n : ℤ) (z),
        φ y₂ e n ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
            ((endDerivedForget C (x : C.Obj)).map
              ((derivedHomReflector C (x : C.Obj) L ((yonedaDGFunctor C).onK)
                (RightModule.yonedaInverseImage C G) q hΦ).map (q.map s))) z) =
          φ y₁ e n z ≫ (shiftFunctor DA n).map (q.map s) := by
  obtain ⟨L, cs, tri, η, hL, hη, hΦ⟩ :=
    exists_derivedHomReflector_data C G ((yonedaDGFunctor C).onK)
      (RightModule.yonedaInverseImage C G) fun _ h ↦ h
  exact ⟨L, cs, tri, hΦ, fun y e n ↦ derivedHomPhi C G L q hL hη hΦ x y e n,
    fun _ _ s e n z ↦ derivedHomPhi_covariant C G L q hL hη hΦ x s e n z⟩

end Phi

end DGCategory
