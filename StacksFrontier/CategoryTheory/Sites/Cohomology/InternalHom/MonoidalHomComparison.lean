module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingTransposeClauses
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualIsTheDerivedDual
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackLocality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomEquivalenceTransport
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomOfDualizable

/-!
# The comparison of a monoidal functor with the derived internal Hom

Let `X` and `Y` be ringed sites and let `P : D(O_X) ⥤ D(O_Y)` be a functor which is monoidal for
the symmetric monoidal structures of Stacks 0FPT on the two derived categories,
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`. The tensor–internal-Hom bijection of
Stacks 08J8 on each side, read through the identification of the monoidal tensor product with
the derived tensor product it is stated for, makes `P` carry a canonical comparison

`P RSheafHom(A, B) ⟶ RSheafHom(P A, P B)`,

the transpose of `μ ≫ P(ev) : P RSheafHom(A, B) ⊗ P A ⟶ P B`. This is the map of Stacks 08JF
when `P` is a derived pullback, written with the monoidal structure of `P` in place of the
comparison of Stacks 07A4. This file sets the comparison up in the abstract transpose framework
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose` and records the three facts about it
that only use the monoidal structure.

## Main definitions

* `AlgebraicGeometry.RingedSite.monoidalTensorPair`: the tensor product of Stacks 0FPT as a
  functor on pairs.
* `AlgebraicGeometry.RingedSite.monoidalCurryEquiv`: the bijection of Stacks 08J8,
  `(A ⟶ RSheafHom(B, C)) ≃ (A ⊗ B ⟶ C)`, with the monoidal tensor product on the right.
* `AlgebraicGeometry.RingedSite.monoidalTensorIso`: the tensorator of a monoidal functor, in the
  form `T ⋙ P ≅ P.prod P ⋙ T` the transpose framework consumes.
* `AlgebraicGeometry.RingedSite.homComparisonMonoidal`: the comparison
  `P RSheafHom(A, B) ⟶ RSheafHom(P A, P B)`, the transpose of `μ ≫ P(ev)` (by
  `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison_adjoint`).

## Main results

* `AlgebraicGeometry.RingedSite.monoidalCurryEquiv_naturalLeft`,
  `monoidalCurryEquiv_dinatural`, `monoidalCurryEquiv_targetNatural`: the three clauses of
  Stacks 08J8 for the monoidal spelling of the bijection.
* `AlgebraicGeometry.RingedSite.homComparisonMonoidal_comp`: the comparison of a composite of
  monoidal functors is the composite of the comparisons.
* `AlgebraicGeometry.RingedSite.homComparisonMonoidal_congr`: the comparison is invariant under a
  monoidal natural isomorphism.
* `AlgebraicGeometry.RingedSite.homComparisonMonoidal_naturality_source`: the comparison is
  natural in its first argument.
* `AlgebraicGeometry.RingedSite.isIso_homComparisonMonoidal_of_exactPairing`: the comparison is
  an isomorphism out of a dualizable object.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedInternalHomPullback

namespace Stacks.Cohomology.DerivedInternalHomPullback.Transpose

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)

/-- **An internal Hom carrying a source-natural tensor–hom bijection represents its
evaluation**: every morphism `W ⊗ A ⟶ B` factors uniquely as `(g ⊗ 1) ≫ ev`. -/
theorem bijective_map_comp_evaluation (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (A B W : D₁) :
    Function.Bijective fun g : W ⟶ (H₁.obj (op A)).obj B =>
      T₁.map (g ×ₘ 𝟙 A) ≫ evaluation H₁ T₁ e₁ A B := by
  have key : (fun g : W ⟶ (H₁.obj (op A)).obj B =>
      T₁.map (g ×ₘ 𝟙 A) ≫ evaluation H₁ T₁ e₁ A B) = e₁ W A B := by
    funext g
    rw [evaluation, ← hnat₁, Category.comp_id]
  rw [key]
  exact (e₁ W A B).bijective

/-- **The comparison is compatible with the two evaluations**:
`(c ⊗ 1) ≫ ev = m⁻¹ ≫ P(ev)`. -/
theorem map_homComparison_comp_evaluation (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (A B : D₁) :
    T₂.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ×ₘ 𝟙 (P.obj A)) ≫
        evaluation H₂ T₂ e₂ (P.obj A) (P.obj B) =
      m.inv.app ((H₁.obj (op A)).obj B, A) ≫ P.map (evaluation H₁ T₁ e₁ A B) := by
  rw [evaluation, ← hnat₂, Category.comp_id, homComparison_adjoint, homComparisonDatum]

end Stacks.Cohomology.DerivedInternalHomPullback.Transpose

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal

section Data

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The tensor product of the monoidal structure of Stacks 0FPT on `D(O)`, as a functor on
pairs. -/
abbrev monoidalTensorPair :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Functor.uncurry.obj (curriedTensor _)

/-- **The bijection of Stacks 08J8 with the monoidal tensor product**:
`(A ⟶ RSheafHom(B, C)) ≃ (A ⊗ B ⟶ C)`. It is `derivedCurryHomEquiv`, whose right-hand side is the
derived tensor product of Stacks 08J8, read across the identification
`derivedMonoidalTensorComparison` of that product with the monoidal one. -/
def monoidalCurryEquiv
    (A B C : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj C) ≃
      ((monoidalTensorPair X).obj (A, B) ⟶ C) :=
  (derivedCurryHomEquiv X A B C).toEquiv.trans
    ((((derivedMonoidalTensorComparison X).app A).app B).homCongr (Iso.refl C)).symm

/-- `monoidalCurryEquiv` is `derivedCurryHomEquiv` precomposed with the comparison
`derivedMonoidalTensorComparison` of the monoidal tensor product with the derived one. -/
theorem monoidalCurryEquiv_apply
    (A B C : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (f : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj C) :
    monoidalCurryEquiv X A B C f =
      ((derivedMonoidalTensorComparison X).hom.app A).app B ≫
        (derivedCurryHomEquiv X A B C).toEquiv f := by
  simp only [monoidalCurryEquiv, Equiv.trans_apply, Iso.homCongr_symm, Iso.homCongr_apply,
    Iso.symm_inv, Iso.refl_symm, Iso.refl_hom, Category.comp_id, Iso.app_hom]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- `monoidalTensorPair` sends a pair of morphisms to their tensor product. -/
theorem monoidalTensorPair_map_prod {A A' B B' :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : A ⟶ A') (g : B ⟶ B') :
    (monoidalTensorPair X).map (f ×ₘ g) = f ⊗ₘ g := by
  simp [monoidalTensorPair, Functor.uncurry_obj_map, tensorHom_def]

/-- **Stacks 08J8 in the source variable**, for the monoidal spelling of the bijection. -/
theorem monoidalCurryEquiv_naturalLeft :
    Transpose.TensorHomEquivNaturalLeft (derivedSheafHomBifunctor X) (monoidalTensorPair X)
      (monoidalCurryEquiv X) := by
  intro A A' B C φ ψ
  rw [monoidalCurryEquiv_apply, monoidalCurryEquiv_apply,
    derivedCurryHomEquiv_toEquiv_naturality_source, ← Category.assoc, ← Category.assoc]
  congr 1
  have h := NatTrans.congr_app ((derivedMonoidalTensorComparison X).hom.naturality φ) B
  simp only [NatTrans.comp_app, curriedTensor_map_app] at h
  simp only [derivedTensorPair, monoidalTensorPair, Functor.uncurry_obj_map,
    CategoryTheory.Functor.map_id, Category.comp_id, curriedTensor_map_app,
    curriedTensor_obj_map, MonoidalCategory.whiskerLeft_id]
  exact h.symm.trans (congrArg (· ≫ _) (Category.comp_id _).symm)

/-- **Stacks 08J8 in the internal-Hom variable**, for the monoidal spelling of the bijection. -/
theorem monoidalCurryEquiv_dinatural :
    Transpose.TensorHomEquivDinatural (derivedSheafHomBifunctor X) (monoidalTensorPair X)
      (monoidalCurryEquiv X) := by
  intro A B B' C φ ψ
  rw [monoidalCurryEquiv_apply, monoidalCurryEquiv_apply,
    derivedCurryHomEquiv_toEquiv_dinaturality, ← Category.assoc, ← Category.assoc]
  congr 1
  have h := ((derivedMonoidalTensorComparison X).hom.app A).naturality φ
  simp only [curriedTensor_obj_map] at h
  simp only [derivedTensorPair, monoidalTensorPair, Functor.uncurry_obj_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, curriedTensor_obj_map]
  exact h.symm

/-- **Stacks 08J8 in the target variable**, for the monoidal spelling of the bijection. -/
theorem monoidalCurryEquiv_targetNatural :
    EquivalenceTranspose.CurriedTargetNatural (derivedSheafHomBifunctor X)
      (monoidalTensorPair X) (monoidalCurryEquiv X) := by
  intro A B C C' φ ψ
  rw [monoidalCurryEquiv_apply, monoidalCurryEquiv_apply,
    derivedCurryHomEquiv_toEquiv_naturality_target, Category.assoc]

end Data

section Functor

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The tensorator of a monoidal functor between derived categories**, in the form
`T ⋙ P ≅ P.prod P ⋙ T` that the transpose framework consumes: at `(A, B)` it is
`δ : P(A ⊗ B) ≅ P A ⊗ P B`, so its inverse is `μ`. -/
def monoidalTensorIso
    (P : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [P.Monoidal] :
    monoidalTensorPair X ⋙ P ≅ P.prod P ⋙ monoidalTensorPair Y :=
  NatIso.ofComponents (fun Z => (Functor.Monoidal.μIso P Z.1 Z.2).symm) (fun {Z Z'} f => by
    obtain ⟨f₁, f₂⟩ := f
    simp only [Functor.comp_obj, Functor.comp_map, Functor.prod_obj, Functor.prod_map,
      Iso.symm_hom, Functor.Monoidal.μIso_inv]
    rw [monoidalTensorPair_map_prod, monoidalTensorPair_map_prod]
    exact (Functor.OplaxMonoidal.δ_natural P f₁ f₂).symm)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The inverse of `monoidalTensorIso P` at `(A, B)` is `μ : P A ⊗ P B ⟶ P(A ⊗ B)`. -/
@[simp]
theorem monoidalTensorIso_inv_app
    (P : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [P.Monoidal] (Z : _ × _) :
    (monoidalTensorIso P).inv.app Z = Functor.LaxMonoidal.μ P Z.1 Z.2 := rfl

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The forward map of `monoidalTensorIso P` at `(A, B)` is `δ : P(A ⊗ B) ⟶ P A ⊗ P B`. -/
@[simp]
theorem monoidalTensorIso_hom_app
    (P : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [P.Monoidal] (Z : _ × _) :
    (monoidalTensorIso P).hom.app Z = Functor.OplaxMonoidal.δ P Z.1 Z.2 := rfl

/-- **The comparison of a monoidal functor with the derived internal Hom**:
`P RSheafHom(A, B) ⟶ RSheafHom(P A, P B)`, the transpose under Stacks 08J8 of
`μ ≫ P(ev) : P RSheafHom(A, B) ⊗ P A ⟶ P B`. -/
def homComparisonMonoidal
    (P : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [P.Monoidal]
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    P.obj (((derivedSheafHomBifunctor X).obj (op A)).obj B) ⟶
      ((derivedSheafHomBifunctor Y).obj (op (P.obj A))).obj (P.obj B) :=
  Transpose.homComparison P (derivedSheafHomBifunctor X) (derivedSheafHomBifunctor Y)
    (monoidalTensorPair X) (monoidalTensorPair Y) (monoidalCurryEquiv X) (monoidalCurryEquiv Y)
    (monoidalTensorIso P) A B

/-- **The comparison is natural in its first argument.** -/
theorem homComparisonMonoidal_naturality_source
    (P : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [P.Monoidal]
    {A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : A ⟶ B)
    (F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    P.map (((derivedSheafHomBifunctor X).map φ.op).app F) ≫ homComparisonMonoidal P A F =
      homComparisonMonoidal P B F ≫
        ((derivedSheafHomBifunctor Y).map (P.map φ).op).app (P.obj F) :=
  Transpose.homComparison_naturality_source P _ _ _ _ _ _ _
    (monoidalCurryEquiv_naturalLeft X) (monoidalCurryEquiv_dinatural X)
    (monoidalCurryEquiv_naturalLeft Y) (monoidalCurryEquiv_dinatural Y) φ F

/-- **Lemma A in transpose form: the comparison is an isomorphism out of a dualizable object.**
If `K` has a right dual `K'`, the comparison `P RSheafHom(K, L) ⟶ RSheafHom(P K, P L)` is an
isomorphism for every `L`: a monoidal functor carries the internal Hom `L ⊗ K'` out of `K` to an
internal Hom out of `P K`, and the comparison is compatible with the two evaluations. -/
theorem isIso_homComparisonMonoidal_of_exactPairing
    (P : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [P.Monoidal]
    (K K' L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [ExactPairing K K'] :
    IsIso (homComparisonMonoidal P K L) := by
  refine isIso_of_tensorHomBijective_map P K K'
    (e := Transpose.evaluation (derivedSheafHomBifunctor X) (monoidalTensorPair X)
      (monoidalCurryEquiv X) K L) ?_
    (e' := Transpose.evaluation (derivedSheafHomBifunctor Y) (monoidalTensorPair Y)
      (monoidalCurryEquiv Y) (P.obj K) (P.obj L)) ?_ (homComparisonMonoidal P K L) ?_
  · intro W
    simpa only [monoidalTensorPair_map_prod, tensorHom_id] using
      Transpose.bijective_map_comp_evaluation _ _ _ (monoidalCurryEquiv_naturalLeft X) K L W
  · intro W
    simpa only [monoidalTensorPair_map_prod, tensorHom_id] using
      Transpose.bijective_map_comp_evaluation _ _ _ (monoidalCurryEquiv_naturalLeft Y)
        (P.obj K) (P.obj L) W
  · have h := Transpose.map_homComparison_comp_evaluation P (derivedSheafHomBifunctor X)
      (derivedSheafHomBifunctor Y) (monoidalTensorPair X) (monoidalTensorPair Y)
      (monoidalCurryEquiv X) (monoidalCurryEquiv Y) (monoidalTensorIso P)
      (monoidalCurryEquiv_naturalLeft Y) K L
    rw [monoidalTensorPair_map_prod, tensorHom_id, monoidalTensorIso_inv_app] at h
    exact h

end Functor

section Composite

variable {X Y Z : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
      (ComplexShape.up ℤ)]

/-- **The comparison of a composite of monoidal functors is the composite of the
comparisons**: `P'(P RSheafHom(A, B)) ⟶ P' RSheafHom(P A, P B) ⟶ RSheafHom(P' P A, P' P B)`. -/
theorem homComparisonMonoidal_comp
    (P : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (P' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    [P.Monoidal] [P'.Monoidal]
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    homComparisonMonoidal (P ⋙ P') A B =
      P'.map (homComparisonMonoidal P A B) ≫ homComparisonMonoidal P' (P.obj A) (P.obj B) := by
  have hm : monoidalTensorIso (P ⋙ P') =
      Transpose.compTensorIso P P' (monoidalTensorPair X) (monoidalTensorPair Y)
        (monoidalTensorPair Z) (monoidalTensorIso P) (monoidalTensorIso P') := by
    refine Iso.ext (NatTrans.ext (funext fun W => ?_))
    simp [Transpose.compTensorIso]
  rw [homComparisonMonoidal, hm]
  exact Transpose.homComparison_comp P P' _ _ _ _ _ _ _ _ _ _ _
    (monoidalCurryEquiv_naturalLeft Y) (monoidalCurryEquiv_naturalLeft Z) A B

end Composite

section Congr

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The comparison is invariant under a monoidal natural isomorphism**: if `c : P ≅ P'` is
monoidal, the comparison of `P'` is that of `P` conjugated by `c`. -/
theorem homComparisonMonoidal_congr
    {P P' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    [P.Monoidal] [P'.Monoidal] (c : P ≅ P') [NatTrans.IsMonoidal c.hom]
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    homComparisonMonoidal P' A B =
      c.inv.app _ ≫ homComparisonMonoidal P A B ≫
        ((derivedSheafHomBifunctor Y).map (c.inv.app A).op).app (P.obj B) ≫
          ((derivedSheafHomBifunctor Y).obj (op (P'.obj A))).map (c.hom.app B) := by
  refine Transpose.homComparison_congr _ _ _ _ _ _ _ _ c (monoidalCurryEquiv_naturalLeft Y)
    (monoidalCurryEquiv_dinatural Y) (monoidalCurryEquiv_targetNatural Y) (fun W => ?_) A B
  rw [monoidalTensorIso_inv_app, monoidalTensorIso_inv_app, monoidalTensorPair_map_prod]
  have h := NatTrans.IsMonoidal.tensor (τ := c.hom) W.1 W.2
  rw [← cancel_epi (c.hom.app W.1 ⊗ₘ c.hom.app W.2), ← h]
  simp

end Congr

end AlgebraicGeometry.RingedSite

end
