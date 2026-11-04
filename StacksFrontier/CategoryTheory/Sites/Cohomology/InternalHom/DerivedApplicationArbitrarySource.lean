module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CochainEvaluationLocalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationEvaluationSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingInternalHomNaturality

/-!
# The application morphism of Stacks 08J8 against a transpose, with no flatness hypothesis

Let `(C, O)` be a ringed site, let `A`, `B`, `C` be complexes of `O`-modules, let
`f : A ⟶ SheafHom(B, C)` be a morphism of complexes, and write

* `ε : RSheafHom(QB, QC) ⊗^L_O QB ⟶ QC` for the application morphism of Stacks 08J8, i.e. the
  bijection of Stacks 08DI at the identity
  (`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv X _ _ _ (𝟙 _)`);
* `σ : Q(SheafHom(B, C)) ⟶ RSheafHom(QB, QC)` for the comparison of Stacks 08DM
  (`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`);
* `T.toTensor : QA ⊗^L_O QB ⟶ Q(Tot(A ⊗_O B))` for the canonical map of the derived tensor
  product to the ordinary total tensor product, which needs no K-flatness.

The theorem proved here is

`Q f ▷ QB ≫ σ ▷ QB ≫ ε = T.toTensor A B ≫ Q(curryHomEquiv f)`,

with `curryHomEquiv` the cochain-level currying bijection of Stacks 0A90, with no hypothesis on
`B` and none on `C`. At `A = SheafHom(B, C)` and `f = 𝟙` this is the unconditional evaluation
square: the application morphism of Stacks 08J8, conjugated by `σ` and by `toTensor`, is the
cochain-level evaluation morphism `AlgebraicGeometry.RingedSite.cochainEvaluation` of
Stacks 0A90.

## Main results

* `AlgebraicGeometry.RingedSite.curryHomEquiv_homMap_source`: source-dinaturality of the
  cochain-level evaluation morphism of Stacks 0A90: the transpose of
  `homMap v 1 : SheafHom(B, C) ⟶ SheafHom(B', C)` is `1 ⊗ v` followed by the evaluation
  morphism of `SheafHom(B, C)`.
* `AlgebraicGeometry.RingedSite.derivedApplication_curryingSquare_toTensor`: the displayed
  identity, with no flatness or injectivity hypothesis on `B` or `C`.
* `AlgebraicGeometry.RingedSite.derivedApplication_eq_cochainEvaluation_toTensor`: the
  unconditional evaluation square, the case `A = SheafHom(B, C)`, `f = 𝟙`.

## Implementation notes

The comparisons `σ`, `σ'` and a K-flat resolution `v : B' ⟶ B` are variables, with their
characterisations as hypotheses: writing
`strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C` into a statement that also
mentions `derivedCurryHomEquiv` exhausts `maxRecDepth` at the declaration's type. Every
hypothesis is dischargeable at
`σ := strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C` and
`σ' := strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B' C`, with no condition
on `B` or `C`:

* `B'`, `v`, `hB'` and `QuasiIso v` from `Stacks.SheafOfModules.exists_kFlat_quasiIso`
  (Stacks 06YS);
* `hnat` from `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality_source` read
  backwards;
* `hσ'` from
  `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_precomposedHomComparisonClass`
  at `B'`.

`rw [Category.id_comp]` does not see through `(𝟙 F).app Y`: rewrite `NatTrans.id_app` first.
Rewriting between the `rfl`-equal `HomologicalComplex.mapBifunctorMap (𝟙 A) v _ _` and
`((Tensor.tensorComplex X.O).obj A).map v` roughly doubles the elaboration time, so the two are
crossed with `exact`. Reassociation in the derived category goes through the private
`paste_right` over an abstract category rather than through keyed rewriting.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.RingedSite

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

/-! ### The chain-level source-dinaturality of the evaluation morphism -/

/-- The induced map of total tensor complexes in the right variable alone sends a local pure
tensor to the local pure tensor of the images. -/
private lemma tensorComplexObjMap_tensorComplexSection
    (K L L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (l : L' ⟶ L) (t r c : ℤ)
    (htr : t + r = c) {W : X.C} (k₀ : (K.X t).val.obj (op W))
    (l₀ : (L'.X r).val.obj (op W)) :
    ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).map l).f c).val.app (op W)
        (tensorComplexSection X t r c htr k₀ l₀) =
      tensorComplexSection X t r c htr k₀ ((l.f r).val.app (op W) l₀) := by
  have h := tensorComplexMap_tensorComplexSection X (𝟙 K) l t r c htr k₀ l₀
  rwa [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h

/-- Source-dinaturality of the cochain-level evaluation morphism of Stacks 0A90: for
complexes `B`, `B'`, `C` of `O`-modules and `v : B' ⟶ B`, the transpose
`Tot(SheafHom(B, C) ⊗_O B') ⟶ C` of the induced map
`homMap v 1 : SheafHom(B, C) ⟶ SheafHom(B', C)` is `1 ⊗ v` followed by the evaluation morphism
`Tot(SheafHom(B, C) ⊗_O B) ⟶ C` of `SheafHom(B, C)`. -/
theorem curryHomEquiv_homMap_source
    (B B' C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : B' ⟶ B) :
    curryHomEquiv X (sheafHomComplex X B C).obj B' C (homMap X v (𝟙 C)) =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
          (sheafHomComplex X B C).obj).map v ≫ cochainEvaluation X B C := by
  refine tensorComplexSection_hom_ext X (sheafHomComplex X B C).obj B' C
    fun c t r htr W ξ y ↦ ?_
  have hrt : r + t = c := by omega
  rw [curryHomEquiv_val_app_tensorComplexSection X (sheafHomComplex X B C).obj B' C
      (homMap X v (𝟙 C)) c t r htr hrt W ξ y,
    applyHomSection_homMap X v (𝟙 C) W t r c hrt ξ y, id_f_val_app_apply,
    HomologicalComplex.comp_f, comp_val_app_apply,
    tensorComplexObjMap_tensorComplexSection X (sheafHomComplex X B C).obj B B' v t r c htr ξ y,
    cochainEvaluation_val_app_tensorComplexSection X B C c t r htr hrt W ξ
      ((v.f r).val.app (op W) y)]

/-! ### The two sides of the square, after precomposing with the resolution -/

/-- A commuting square stays commuting after postcomposing both sides with `z`. -/
private lemma paste_right {D : Type*} [Category D] {a b c d e : D}
    (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ d) (q' : d ⟶ c) (z : c ⟶ e)
    (h : p ≫ q = p' ≫ q') : p ≫ q ≫ z = p' ≫ q' ≫ z := by
  rw [← Category.assoc, h, Category.assoc]

/-- `f ⊗ 1` followed by `1 ⊗ v` and the evaluation of `SheafHom(B, C)` is `1 ⊗ v` followed by
the transpose of `f`. -/
private lemma tensorComplexMap_comp_cochainEvaluation
    (A B B' C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : B' ⟶ B)
    (f : A ⟶ (sheafHomComplex X B C).obj) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app B' ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
          (sheafHomComplex X B C).obj).map v ≫ cochainEvaluation X B C =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map v ≫
        curryHomEquiv X A B C f := by
  rw [curryHomEquiv_eq_tensor_evaluation X A B C f]
  exact paste_right _ _ _ _ _
    (NatTrans.naturality ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f) v).symm

/-- The canonical map `toTensor A B` of Stacks 06YU, precomposed with `1 ⊗ Qv`, is the one-sided
K-flat comparison at the K-flat complex `B'` followed by the class of `1 ⊗ v`. -/
private lemma toTensor_comp_of_resolution
    (A B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : B' ⟶ B)
    (hB' : Stacks.SheafOfModules.IsKFlat X.O B') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map v) ≫
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor A B =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B' hB').hom ≫
        DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map v) := by
  have hnt := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor_naturality (𝟙 A) v
  rwa [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor_eq_comparisonRight A B' hB']
    at hnt

/-- The canonical map `toTensor A B`, precomposed with `1 ⊗ Qv` and followed by
`Q(curryHomEquiv f)`, is the one-sided K-flat comparison at `B'` followed by the class of
`1 ⊗ v` and of the transpose of `f`. -/
private lemma toTensor_comp_curryHomEquiv_of_resolution
    (A B B' C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : B' ⟶ B)
    (hB' : Stacks.SheafOfModules.IsKFlat X.O B')
    (f : A ⟶ (sheafHomComplex X B C).obj) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map v) ≫
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor A B ≫
        DerivedCategory.Q.map (curryHomEquiv X A B C f) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B' hB').hom ≫
        DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map v ≫
            curryHomEquiv X A B C f) := by
  rw [CategoryTheory.Functor.map_comp]
  exact paste_right _ _ _ _ _ (toTensor_comp_of_resolution X A B B' v hB')

/-- `Q f ▷ QB ≫ σ ▷ QB ≫ ε`, precomposed with `1 ⊗ Qv`, is the one-sided K-flat comparison at
the K-flat complex `B'` followed by the class of the composite of `f ⊗ 1`, `1 ⊗ v` and the
evaluation of `SheafHom(B, C)`. -/
private lemma derivedApplication_curryingSquare_precomposed
    (A B B' C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : B' ⟶ B) (hB' : Stacks.SheafOfModules.IsKFlat X.O B')
    (σ : DerivedCategory.Q.obj (sheafHomComplex X B C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
        (DerivedCategory.Q.obj C))
    (σ' : DerivedCategory.Q.obj (sheafHomComplex X B' C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B'))).obj
        (DerivedCategory.Q.obj C))
    (hnat : σ ≫ ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map v).op).app
          (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map (homMap X v (𝟙 C)) ≫ σ')
    (hσ' : derivedSheafHomGlobalSectionsEquiv X
        (DerivedCategory.Q.obj (kFlatHomResolution X B' C))
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B'))).obj
          (DerivedCategory.Q.obj C))
        (precomposedHomComparisonClass X (derivedInternalHomOfBifunctor X) B' C
          (kFlatHomResolution X B' C) hB' (isKFlat_kFlatHomResolution X B' C)
          (kFlatHomResolutionMap X B' C)) =
      DerivedCategory.Q.map (kFlatHomResolutionMap X B' C) ≫ σ')
    (f : A ⟶ (sheafHomComplex X B C).obj) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map v) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj B) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map σ).app
          (DerivedCategory.Q.obj B) ≫
        derivedCurryHomEquiv X
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
            (DerivedCategory.Q.obj C))
          (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) (𝟙 _) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B' hB').hom ≫
        DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app B' ≫
            ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
              (sheafHomComplex X B C).obj).map v ≫ cochainEvaluation X B C) := by
  have h1 := derivedCurryHomEquiv_Q_map_comp X A B C σ f
  have h2 := derivedCurryHomEquiv_dinaturality X (DerivedCategory.Q.obj A)
    (DerivedCategory.Q.obj C) (DerivedCategory.Q.map v) (DerivedCategory.Q.map f ≫ σ)
  have h3 := derivedApplication_curryingSquare X A B' C hB' σ' hσ' (f ≫ homMap X v (𝟙 C))
  have h4 := derivedCurryHomEquiv_Q_map_comp X A B' C σ' (f ≫ homMap X v (𝟙 C))
  have h5 : (DerivedCategory.Q.map f ≫ σ) ≫
        ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map v).op).app
          (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map (f ≫ homMap X v (𝟙 C)) ≫ σ' := by
    rw [Category.assoc, hnat, CategoryTheory.Functor.map_comp, Category.assoc]
  have h6 : curryHomEquiv X A B' C (f ≫ homMap X v (𝟙 C)) =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app B' ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
          (sheafHomComplex X B C).obj).map v ≫ cochainEvaluation X B C := by
    rw [curryHomEquiv_naturality_source X f B' C (homMap X v (𝟙 C)),
      curryHomEquiv_homMap_source X B B' C v]
  rw [← h1, ← h2, h5, h4, h3, h6]

/-! ### The square with no hypothesis on the tensor factor -/

/-- The application morphism of Stacks 08J8 against a cochain-level transpose, with no
flatness hypothesis: for complexes `A`, `B`, `C` of `O`-modules, a morphism of complexes
`f : A ⟶ SheafHom(B, C)`, and the comparison `σ` of Stacks 08DM,

`Q f ▷ QB ≫ σ ▷ QB ≫ ε = T.toTensor A B ≫ Q(curryHomEquiv f)`,

where `ε` is the application morphism `RSheafHom(QB, QC) ⊗^L_O QB ⟶ QC` of Stacks 08J8 and
`T.toTensor` is the canonical map of Stacks 06YU from the derived tensor product to the ordinary
total tensor product. Neither `B` nor `C` is assumed K-flat or K-injective: `v : B' ⟶ B` is a
K-flat resolution, `σ'` the comparison at `B'` characterised by `hσ'`, and `hnat` relates `σ`
and `σ'` along `v`. -/
theorem derivedApplication_curryingSquare_toTensor
    (A B B' C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : B' ⟶ B) (hB' : Stacks.SheafOfModules.IsKFlat X.O B') [QuasiIso v]
    (σ : DerivedCategory.Q.obj (sheafHomComplex X B C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
        (DerivedCategory.Q.obj C))
    (σ' : DerivedCategory.Q.obj (sheafHomComplex X B' C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B'))).obj
        (DerivedCategory.Q.obj C))
    (hnat : σ ≫ ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map v).op).app
          (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map (homMap X v (𝟙 C)) ≫ σ')
    (hσ' : derivedSheafHomGlobalSectionsEquiv X
        (DerivedCategory.Q.obj (kFlatHomResolution X B' C))
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B'))).obj
          (DerivedCategory.Q.obj C))
        (precomposedHomComparisonClass X (derivedInternalHomOfBifunctor X) B' C
          (kFlatHomResolution X B' C) hB' (isKFlat_kFlatHomResolution X B' C)
          (kFlatHomResolutionMap X B' C)) =
      DerivedCategory.Q.map (kFlatHomResolutionMap X B' C) ≫ σ')
    (f : A ⟶ (sheafHomComplex X B C).obj) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj B) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map σ).app
          (DerivedCategory.Q.obj B) ≫
        derivedCurryHomEquiv X
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
            (DerivedCategory.Q.obj C))
          (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) (𝟙 _) =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor A B ≫
        DerivedCategory.Q.map (curryHomEquiv X A B C f) := by
  have : IsIso (DerivedCategory.Q.map v) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  rw [← cancel_epi (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
      (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map v)),
    derivedApplication_curryingSquare_precomposed X A B B' C v hB' σ σ' hnat hσ' f,
    toTensor_comp_curryHomEquiv_of_resolution X A B B' C v hB' f,
    tensorComplexMap_comp_cochainEvaluation X A B B' C v f]

/-- The unconditional evaluation square: for complexes `B`, `C` of `O`-modules with no
hypothesis on either, the application morphism of Stacks 08J8,

`ε : RSheafHom(QB, QC) ⊗^L_O QB ⟶ QC`,

is the cochain-level evaluation morphism `AlgebraicGeometry.RingedSite.cochainEvaluation` of
Stacks 0A90, conjugated by the comparison `σ` of Stacks 08DM on the internal Hom factor and by
the canonical map `toTensor` of Stacks 06YU. -/
theorem derivedApplication_eq_cochainEvaluation_toTensor
    (B B' C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : B' ⟶ B) (hB' : Stacks.SheafOfModules.IsKFlat X.O B') [QuasiIso v]
    (σ : DerivedCategory.Q.obj (sheafHomComplex X B C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
        (DerivedCategory.Q.obj C))
    (σ' : DerivedCategory.Q.obj (sheafHomComplex X B' C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B'))).obj
        (DerivedCategory.Q.obj C))
    (hnat : σ ≫ ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map v).op).app
          (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map (homMap X v (𝟙 C)) ≫ σ')
    (hσ' : derivedSheafHomGlobalSectionsEquiv X
        (DerivedCategory.Q.obj (kFlatHomResolution X B' C))
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B'))).obj
          (DerivedCategory.Q.obj C))
        (precomposedHomComparisonClass X (derivedInternalHomOfBifunctor X) B' C
          (kFlatHomResolution X B' C) hB' (isKFlat_kFlatHomResolution X B' C)
          (kFlatHomResolutionMap X B' C)) =
      DerivedCategory.Q.map (kFlatHomResolutionMap X B' C) ≫ σ') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map σ).app
          (DerivedCategory.Q.obj B) ≫
        derivedCurryHomEquiv X
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
            (DerivedCategory.Q.obj C))
          (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) (𝟙 _) =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor
          (sheafHomComplex X B C).obj B ≫
        DerivedCategory.Q.map (cochainEvaluation X B C) := by
  have h := derivedApplication_curryingSquare_toTensor X (sheafHomComplex X B C).obj B B' C v hB'
    σ σ' hnat hσ' (𝟙 (sheafHomComplex X B C).obj)
  have hce : curryHomEquiv X (sheafHomComplex X B C).obj B C (𝟙 (sheafHomComplex X B C).obj) =
      cochainEvaluation X B C := by
    rw [← curryHomEquiv_symm_cochainEvaluation X B C]
    exact (curryHomEquiv X (sheafHomComplex X B C).obj B C).apply_symm_apply _
  simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, hce] using h

end AlgebraicGeometry.RingedSite

end
