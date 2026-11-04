module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageDuality
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaComparisonMap
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaQuasiCoherent

/-!
# The duality formula on a compactification through the comparison map

Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of quasi-compact quasi-separated
schemes with `Y` Noetherian, `a` the right adjoint of `Rf_*` on `D_QCoh` and `K` a dualizing
complex on `Y`. The isomorphism `a(M) ≅ R𝓗om(Lf^* D_Y(M), a(K))` of
`Stacks.Duality.TwistedInverseImageDuality.dualityIso` corresponds under the tensor–internal-Hom
bijection of [Stacks, Tag 08J8] to the morphism `a(M) ⊗ᴸ Lf^* D_Y(M) ⟶ a(K)` given by the
comparison map `Lf^*E ⊗ a(L) ⟶ a(E ⊗ L)` of the monoidal adjunction `Lf^* ⊣ Rf_*` on `D_QCoh`
(Equation 48.8.0.1) at `(D_Y(M), M)`, followed by `a` of the evaluation `D_Y(M) ⊗ M ⟶ K`.

## Main results

* `Stacks.Duality.TwistedInverseImageDuality.comparison_map_adjunctionHomEquiv_symm_id`: the
  counit of `Rf_* ⊣ a` read at the standard model.
* `Stacks.Duality.TwistedInverseImageDuality.curry_dualityIso_hom_app`: the transpose of
  `dualityIso` under the bijection of [Stacks, Tag 08J8].
* `Stacks.Duality.TwistedInverseImageDuality.comparison_map_projectionMap_comp`: the projection
  formula of the standard model through the comparison of the models.
* `curry_dualityIso_hom_app_eq_compareWithPullbackTensor`: that transpose is the comparison map of
  Equation 48.8.0.1 followed by `a` of the evaluation.

## References

* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Duality.TwistedInverseImageDuality

open Stacks.Duality.ProjectionFormulaMonoidal (tensorModelIso swapIso tensorComparison)

section Chases

/-- The diagram chase behind `comparison_map_projectionMap_comp`. -/
lemma pb_chase {C C' : Type*} [Category C] [Category C'] (G : C' ⥤ C)
    {X₀ X₁ X₂ X₃ X₆ X₇ Y₂ Y₃ : C} {Z₄ Z₅ Z₈ Z₉ W₁ : C'}
    (Eρ : X₀ ⟶ X₇) (eF : X₇ ⟶ G.obj Z₈) (px : Z₈ ⟶ Z₉) (s₁ : X₀ ⟶ X₁) (ER : X₁ ⟶ X₆)
    (s₂ : X₆ ⟶ X₇) (t₁ : X₁ ⟶ X₂) (t₂ : X₂ ⟶ X₃) (P₁ : X₃ ⟶ G.obj Z₄) (t₃ : Z₄ ⟶ Z₅)
    (t₄ : G.obj Z₅ ⟶ X₆) (pS : Z₅ ⟶ Z₈) (pG : Z₄ ⟶ W₁) (pW : W₁ ⟶ Z₉) (n₁ : X₃ ⟶ Y₂)
    (P₂ : Y₂ ⟶ G.obj W₁) (sw : Y₂ ⟶ Y₃) (swi : Y₃ ⟶ Y₂) (ιP : Y₃ ⟶ G.obj Z₉)
    (e₁ : Y₂ ⟶ Y₂) (e₂ : W₁ ⟶ W₁) (e₃ : G.obj Z₉ ⟶ G.obj Z₉)
    (h₁ : Eρ = s₁ ≫ ER ≫ s₂) (h₂ : ER = t₁ ≫ t₂ ≫ P₁ ≫ G.map t₃ ≫ t₄)
    (h₃ : t₄ ≫ s₂ ≫ eF = G.map pS) (h₄ : t₃ ≫ pS ≫ px = pG ≫ pW)
    (h₅ : n₁ ≫ P₂ = P₁ ≫ G.map pG) (h₆ : ιP = swi ≫ e₁ ≫ P₂ ≫ G.map (e₂ ≫ pW) ≫ e₃)
    (he₁ : e₁ = 𝟙 _) (he₂ : e₂ = 𝟙 _) (he₃ : e₃ = 𝟙 _) (hsw : sw ≫ swi = 𝟙 _) :
    Eρ ≫ eF ≫ G.map px = s₁ ≫ t₁ ≫ t₂ ≫ n₁ ≫ sw ≫ ιP := by
  subst h₁ h₂ h₆ he₁ he₂ he₃
  simp only [Category.assoc, Category.id_comp, Category.comp_id, reassoc_of% hsw]
  rw [reassoc_of% h₃, ← G.map_comp, ← G.map_comp, h₄, reassoc_of% h₅, G.map_comp]

/-- Cancelling two inverse pairs inside a composite. -/
lemma cancel_chase {C : Type*} [Category C] {P Q R S U V : C} (a : P ⟶ Q) (b : Q ⟶ R)
    (c : R ⟶ S) (c' : S ⟶ R) (b' : R ⟶ Q) (d : Q ⟶ U) (e : U ⟶ V) (r : P ⟶ U)
    (hc : c ≫ c' = 𝟙 _) (hb : b ≫ b' = 𝟙 _) (hd : a ≫ d = r) :
    (a ≫ b) ≫ c ≫ c' ≫ b' ≫ d ≫ e = r ≫ e := by
  rw [reassoc_of% hc, Category.assoc, reassoc_of% hb, reassoc_of% hd]

/-- The diagram chase behind `comparison_map_tensor_counit`. -/
lemma core_chase {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ Q₀ Q₁ Q₂ R₁ R₂ : C}
    (Ee : P₀ ⟶ Q₀) (a₁ : P₀ ⟶ P₁) (Es : P₁ ⟶ Q₁) (a₂ : Q₁ ⟶ Q₀)
    (b₁ : P₁ ⟶ P₂) (Tg : P₂ ⟶ Q₂) (b₂ : Q₂ ⟶ Q₁)
    (c₁ : P₂ ⟶ P₃) (c₂ : P₃ ⟶ P₄) (c₃ : P₄ ⟶ Q₂)
    (w₁ : P₄ ⟶ R₁) (w₂ : Q₂ ⟶ R₂) (w₂' : R₂ ⟶ Q₂) (ιS : R₁ ⟶ R₂)
    (ha : Ee = a₁ ≫ Es ≫ a₂) (hb : Es = b₁ ≫ Tg ≫ b₂) (hc : Tg = c₁ ≫ c₂ ≫ c₃)
    (hw : c₃ ≫ w₂ = w₁ ≫ ιS) (hw' : w₂ ≫ w₂' = 𝟙 _) :
    Ee = a₁ ≫ b₁ ≫ c₁ ≫ c₂ ≫ w₁ ≫ ιS ≫ w₂' ≫ b₂ ≫ a₂ := by
  subst ha hb hc
  simp only [Category.assoc]
  rw [← reassoc_of% hw, reassoc_of% hw']

/-- A functor applied to a threefold composite. -/
lemma map_eq_comp₃ {C D : Type*} [Category C] [Category D] (E : C ⥤ D) {P Q R S : C}
    (x : P ⟶ S) (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ S) (h : x = a ≫ b ≫ c) :
    E.map x = E.map a ≫ E.map b ≫ E.map c := by
  rw [h, E.map_comp, E.map_comp]

/-- A naturality square with invertible vertical maps, solved for the bottom map. -/
lemma nat_conj {C : Type*} [Category C] {P Q P' Q' : C} (i : P ≅ P') (j : Q ≅ Q') (t : P ⟶ Q)
    (s : P' ⟶ Q') (s' : P' ⟶ Q') (n : t ≫ j.hom = i.hom ≫ s) (hs : s = s') :
    s' = i.inv ≫ t ≫ j.hom := by
  rw [← hs, n, Iso.inv_hom_id_assoc]

/-- A functor on pairs applied to `x ×ₘ 𝟙` with `x` a threefold composite. -/
lemma map_prod_comp₃ {C D : Type*} [Category C] [Category D] (T : C × C ⥤ D) {P₀ P₁ P₂ P₃ Q : C}
    (x : P₀ ⟶ P₃) (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) (y : Q ⟶ Q) (hx : x = a ≫ b ≫ c)
    (hy : y = 𝟙 Q) :
    T.map (x ×ₘ y) = T.map (a ×ₘ 𝟙 Q) ≫ T.map (b ×ₘ 𝟙 Q) ≫ T.map (c ×ₘ 𝟙 Q) := by
  subst hx hy
  simp only [← T.map_comp, prod_comp, Category.comp_id]

/-- Dropping an identity inside the image of a functor in a commutative square. -/
lemma comp_map_of_id_comp {C D : Type*} [Category C] [Category D] (ι : C ⥤ D) {P Q : D}
    {A B : C} (t : P ⟶ Q) (w₂ : Q ⟶ ι.obj B) (w₁ : P ⟶ ι.obj A) (i : A ⟶ A) (q : A ⟶ B)
    (n : t ≫ w₂ = w₁ ≫ ι.map (i ≫ q)) (hi : i = 𝟙 A) : t ≫ w₂ = w₁ ≫ ι.map q := by
  rw [n, hi, Category.id_comp]

/-- `G.map x` at `Z` through an isomorphism `F ≅ G` of bifunctors. -/
lemma nat_conj_app {C D E : Type*} [Category C] [Category D] [Category E] (F G : C ⥤ D ⥤ E)
    (e : F ≅ G) {P M : C} (x : P ⟶ M) (Z : D) :
    (G.map x).app Z = (e.inv.app P).app Z ≫ (F.map x).app Z ≫ (e.hom.app M).app Z := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, NatTrans.naturality, Iso.inv_hom_id_app_assoc]

/-- The uncurried bifunctor on `(x, 𝟙)`. -/
lemma comp_uncurry_map_id {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
    (F : C ⥤ D ⥤ E) (G : E ⥤ E') {P M : C} (x : P ⟶ M) (Z : D) :
    (Functor.uncurry.obj F ⋙ G).map ((x, 𝟙 Z) : (P, Z) ⟶ (M, Z)) = G.map ((F.map x).app Z) := by
  simp

/-- A functor preserves a composite equal to the identity. -/
private lemma map_comp_eq_id {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {P Q : C}
    {a : P ⟶ Q} {b : Q ⟶ P} (h : a ≫ b = 𝟙 _) : F.map a ≫ F.map b = 𝟙 _ := by
  rw [← F.map_comp, h, F.map_id]

/-- The diagram chase behind `curry_dualityIso_hom_app_eq_compareWithPullbackTensor`. -/
lemma cb_chase {C : Type*} [Category C] {P₀ P₁ T₀ T₁ S₀ R R' Z U₁ U₂ U₃ U₄ V₁ V₂ : C}
    (eQ : P₀ ⟶ P₀) (eπi : P₀ ⟶ P₁) (eπ : P₁ ⟶ P₀) (Eh : P₁ ⟶ Z) (Eri : P₁ ⟶ T₀) (Er : T₀ ⟶ P₁)
    (Ecur : T₀ ⟶ Z) (Ece : T₀ ⟶ T₁) (Ecβ : T₁ ⟶ Z) (px : P₀ ⟶ S₀) (ιP : R ⟶ S₀) (ιPi : S₀ ⟶ R)
    (σ₁ : T₀ ⟶ U₁) (σ₂ : U₁ ⟶ U₂) (σ₃ : U₂ ⟶ U₃) (σ₄ : U₃ ⟶ U₄) (σ₅ : U₄ ⟶ R) (q : R ⟶ R')
    (τ₁ : R' ⟶ V₁) (τ₂ : V₁ ⟶ V₂) (τ₃ : V₂ ⟶ T₁) (ev : R' ⟶ Z)
    (heQ : eQ = 𝟙 _) (he : eπi ≫ eπ = 𝟙 _) (hr : Eri ≫ Er = 𝟙 _) (hP : ιP ≫ ιPi = 𝟙 _)
    (hPB : Er ≫ eπ ≫ px = σ₁ ≫ σ₂ ≫ σ₃ ≫ σ₄ ≫ σ₅ ≫ ιP) (hEh : Eh = Eri ≫ Ecur)
    (hcur : Ecur = Ece ≫ Ecβ) (hcore : Ece = σ₁ ≫ σ₂ ≫ σ₃ ≫ σ₄ ≫ σ₅ ≫ q ≫ τ₁ ≫ τ₂ ≫ τ₃)
    (hev : ev = τ₁ ≫ τ₂ ≫ τ₃ ≫ Ecβ) :
    eQ ≫ eπi ≫ Eh = px ≫ ιPi ≫ q ≫ ev := by
  have h1 : σ₁ ≫ σ₂ ≫ σ₃ ≫ σ₄ ≫ σ₅ = Er ≫ eπ ≫ px ≫ ιPi := by
    simp only [← Category.assoc] at hPB ⊢
    rw [hPB]
    simp only [Category.assoc, hP, Category.comp_id]
  subst heQ hEh hcur hcore hev
  simp only [Category.assoc, Category.id_comp]
  rw [reassoc_of% h1, reassoc_of% hr, reassoc_of% he]

end Chases

section Formula

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- `M` in `D_QCoh(𝒪_Y)` at the standard model, as an object of `D_QCoh(𝒪_Y)` at the locally small
model. -/
abbrev toQCoh {Z : Scheme.{u}} (M : (qcoh Z).FullSubcategory) : quasiCoherentDerivedCategory Z :=
  ⟨(comparison Z).functor.obj M.obj, M.property⟩

/-- **The counit of `Rf_* ⊣ a` at the standard model**: read through the comparison of the models,
it is the comparison of `Rf_*` at the two models, `Rf_*` of the counit of the comparison and the
counit of `Rf_* ⊣ a` on `D_QCoh`. -/
theorem comparison_map_adjunctionHomEquiv_symm_id (M : (qcoh Y).FullSubcategory) :
    (comparison Y).functor.map ((adjunctionHomEquiv f M ((rightAdjointStd f).obj M)
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (toQCoh M)).property).symm (𝟙 _)) =
      (pushModelIso f).hom.app ((rightAdjointStd f).obj M) ≫
        (Stacks.Duality.derivedPushforward f).map ((comparison X).counitIso.hom.app
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (toQCoh M)).obj) ≫
        ((twistedInverseImageAdjunction f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app (toQCoh M)).hom := by
  set r := (pushModelIso f).hom.app ((rightAdjointStd f).obj M) ≫
    (Stacks.Duality.derivedPushforward f).map ((comparison X).counitIso.hom.app
      ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (toQCoh M)).obj) ≫
    ((twistedInverseImageAdjunction f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app (toQCoh M)).hom
  have key := DualityFormula.transportedHomEquiv_eq_of_fac (EX := comparison X)
    (EY := comparison Y) (π := push f)
    (π' := Stacks.Duality.derivedPushforward f) (eπ := pushModelIso f)
    (PX' := Coherator.quasiCoherentProp X) (PY' := Coherator.quasiCoherentProp Y)
    (πQ := quasiCoherentDerivedPushforward f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (eQ := ObjectProperty.liftCompιIso _ _ (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (a' := twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (adj := twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    M ((rightAdjointStd f).obj M)
    ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
      (toQCoh M)).property
    ((comparison Y).fullyFaithfulFunctor.preimage r)
    ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
      (toQCoh M))
    (ObjectProperty.homMk ((comparison X).counitIso.hom.app
      ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (toQCoh M)).obj))
    ((twistedInverseImageAdjunction f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app (toQCoh M)) (by
        apply ObjectProperty.hom_ext
        dsimp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
        rw [Functor.FullyFaithful.map_preimage, Iso.inv_hom_id_app_assoc]
        exact Category.id_comp _)
  have h1 : adjunctionHomEquiv f M ((rightAdjointStd f).obj M)
      ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (toQCoh M)).property ((comparison Y).fullyFaithfulFunctor.preimage r) = 𝟙 _ := by
    refine key.trans ?_
    simp only [Adjunction.homEquiv_unit, Adjunction.right_triangle_components,
      ObjectProperty.FullSubcategory.id_hom, Category.comp_id, Equivalence.toAdjunction_unit]
    exact (comparison X).unit_inverse_comp _
  rw [← h1, Equiv.symm_apply_apply, Functor.FullyFaithful.map_preimage]

omit [QuasiCompact f] [QuasiSeparated f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y] in
/-- The projection map of the standard model, through the comparison of the tensor products. -/
theorem comparison_map_projectionMap (F : Std X) (D : Std Y) :
    (comparison Y).functor.map (projectionMap f F D) =
      (comparison Y).functor.map
          (((ProjectionFormulaLocallySmall.standardTensorIso Y).inv.app ((push f).obj F)).app D) ≫
        (comparison Y).functor.map (adjunctionTensorMap
          (ProjectionFormulaMonoidal.standardAdjunction f)
          (ProjectionFormulaMonoidal.standardTensor Y) (ProjectionFormulaMonoidal.standardTensor X)
          (ProjectionFormulaMonoidal.standardComparison f) F D) ≫
        (comparison Y).functor.map ((push f).map
          (((ProjectionFormulaLocallySmall.standardTensorIso X).hom.app F).app
            ((pull f).obj D))) := by
  simp only [projectionMap, DualityFormula.conjugateProjection, Functor.map_comp]
  rfl

/-- The comparison `E_X(F ⊗ᴸ Lf^*D) ⟶ Lf^*D ⊗ᴸ A` for `F = E_X⁻¹(A)`, through the identifications
of the tensor products and of `Lf^*` at the two models, the counit of the comparison and the
braiding. -/
abbrev tensorPullComparison (A : quasiCoherentDerivedCategory X) (D : Std Y) (hD : qcoh Y D) :
    (comparison X).functor.obj (((tensor X).obj ((comparison X).inverse.obj A.obj)).obj
        ((pull f).obj D)) ⟶
      (((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj
        (toQCoh ⟨D, hD⟩))).obj A).obj :=
  (comparison X).functor.map (((ProjectionFormulaLocallySmall.standardTensorIso X).inv.app
      ((comparison X).inverse.obj A.obj)).app ((pull f).obj D)) ≫
    (tensorModelIso X).inv.app ((comparison X).inverse.obj A.obj, (pull f).obj D) ≫
    (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
      ((comparison X).counitIso.hom.app A.obj ×ₘ
        (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app D) ≫
    (swapIso X).hom.app (A, (quasiCoherentDerivedPullback' f).obj (toQCoh ⟨D, hD⟩))

omit [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y] in
/-- **The projection formula at the two models.** The projection map
`Rf_*F ⊗ᴸ D ⟶ Rf_*(F ⊗ᴸ Lf^*D)` of the standard model at `F = E_X⁻¹(A)`, followed by `Rf_*` of
`tensorPullComparison`, is the comparison of the models and of the tensor products followed by the
projection-formula map of `D_QCoh`. -/
theorem comparison_map_projectionMap_comp (A : quasiCoherentDerivedCategory X) (D : Std Y)
    (hD : qcoh Y D) :
    (comparison Y).functor.map (projectionMap f ((comparison X).inverse.obj A.obj) D) ≫
      (pushModelIso f).hom.app (((tensor X).obj ((comparison X).inverse.obj A.obj)).obj
        ((pull f).obj D)) ≫
        (Stacks.Duality.derivedPushforward f).map (tensorPullComparison f A D hD) =
    (comparison Y).functor.map
        (((ProjectionFormulaLocallySmall.standardTensorIso Y).inv.app
              ((push f).obj ((comparison X).inverse.obj A.obj))).app D) ≫
      (tensorModelIso Y).inv.app
          ((ProjectionFormulaLocallySmall.standardPushforward f).obj
            ((comparison X).inverse.obj A.obj), D) ≫
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)).map
            ((StacksDraft.DerivedModel.derivedPushforwardModelIso f.toLRSHom.toShHom).hom.app
                  ((comparison X).inverse.obj A.obj) ×ₘ
              𝟙 ((ProjectionFormulaMonoidal.modelFunctor Y).obj D)) ≫
          (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)).map
              ((Stacks.Duality.derivedPushforward f).map ((comparison X).counitIso.hom.app A.obj) ×ₘ
                𝟙 ((comparison Y).functor.obj D)) ≫
            (swapIso Y).hom.app ((quasiCoherentDerivedPushforward f
              (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj A, toQCoh ⟨D, hD⟩) ≫
              (ObjectProperty.ι _).map
                (projectionFormulaMap f
                  (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
                  (quasiCoherentDerivedPullbackTensorIso f).hom A (toQCoh ⟨D, hD⟩)) := by
  have h₂ := ProjectionFormulaMonoidal.modelFunctor_map_adjunctionTensorMap f
    (derivedPullbackCanonicalMonoidal_δ_model f) ((comparison X).inverse.obj A.obj) D
  have h₃ : (StacksDraft.DerivedModel.derivedPushforwardModelIso f.toLRSHom.toShHom).inv.app
        ((ProjectionFormulaMonoidal.standardTensor X).obj ((comparison X).inverse.obj A.obj,
          (ProjectionFormulaMonoidal.standardPullback f).obj D)) ≫
      (comparison Y).functor.map ((push f).map
        (((ProjectionFormulaLocallySmall.standardTensorIso X).hom.app
          ((comparison X).inverse.obj A.obj)).app ((pull f).obj D))) ≫
      (pushModelIso f).hom.app (((tensor X).obj ((comparison X).inverse.obj A.obj)).obj
        ((pull f).obj D)) =
      (Stacks.Duality.derivedPushforward f).map ((comparison X).functor.map
        (((ProjectionFormulaLocallySmall.standardTensorIso X).hom.app
          ((comparison X).inverse.obj A.obj)).app ((pull f).obj D))) :=
    (congrArg (_ ≫ ·) ((pushModelIso f).hom.naturality _)).trans (Iso.inv_hom_id_app_assoc _ _ _)
  have h₅ : (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)).map
        ((Stacks.Duality.derivedPushforward f).map ((comparison X).counitIso.hom.app A.obj) ×ₘ
          𝟙 ((comparison Y).functor.obj D)) ≫
      adjunctionTensorMap (derivedAdjunction f)
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y))
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X))
        (tensorComparison f)
        ((ObjectProperty.ι _).obj A) ((ObjectProperty.ι _).obj (toQCoh ⟨D, hD⟩)) =
    adjunctionTensorMap (derivedAdjunction f)
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y))
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X))
        (tensorComparison f)
        ((ProjectionFormulaMonoidal.modelFunctor X).obj ((comparison X).inverse.obj A.obj))
        ((ProjectionFormulaMonoidal.modelFunctor Y).obj D) ≫
      (Stacks.Duality.derivedPushforward f).map
        ((@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          ((comparison X).counitIso.hom.app A.obj ×ₘ
            (derivedPullback f).map (𝟙 ((comparison Y).functor.obj D)))) :=
    adjunctionTensorMap_natural (derivedAdjunction f)
    (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y))
    (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)) (tensorComparison f)
    ((comparison X).counitIso.hom.app A.obj) (𝟙 ((comparison Y).functor.obj D))
  have h₆ := ProjectionFormulaMonoidal.ι_map_projectionFormulaMap f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f) A (toQCoh ⟨D, hD⟩)
  simp only [quasiCoherentDerivedPullbackCompιIso,
    DerivedPushforward.quasiCoherentDerivedPushforwardCompιIso, ObjectProperty.liftCompιIso,
    Iso.symm_hom, Iso.symm_inv, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, ← prod_id] at h₆
  have h₄ : ((@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          (𝟙 ((ProjectionFormulaMonoidal.modelFunctor X).obj ((comparison X).inverse.obj A.obj)) ×ₘ
            (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).symm.hom.app D) ≫
          (tensorModelIso X).hom.app
            ((comparison X).inverse.obj A.obj,
              (ProjectionFormulaMonoidal.standardPullback f).obj D)) ≫
      (comparison X).functor.map
        (((ProjectionFormulaLocallySmall.standardTensorIso X).hom.app
          ((comparison X).inverse.obj A.obj)).app ((pull f).obj D)) ≫
      tensorPullComparison f A D hD =
      (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          ((comparison X).counitIso.hom.app A.obj ×ₘ
            (derivedPullback f).map (𝟙 ((comparison Y).functor.obj D))) ≫
        (swapIso X).hom.app (A, (quasiCoherentDerivedPullback' f).obj (toQCoh ⟨D, hD⟩)) := by
    have hc : (comparison X).functor.map
          (((ProjectionFormulaLocallySmall.standardTensorIso X).hom.app
            ((comparison X).inverse.obj A.obj)).app ((pull f).obj D)) ≫
        (comparison X).functor.map
          (((ProjectionFormulaLocallySmall.standardTensorIso X).inv.app
            ((comparison X).inverse.obj A.obj)).app ((pull f).obj D)) = 𝟙 _ :=
      map_comp_eq_id _ (by simp only [← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app])
    have hb := (tensorModelIso X).hom_inv_id_app
      ((comparison X).inverse.obj A.obj, (ProjectionFormulaMonoidal.standardPullback f).obj D)
    have hd : (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          (𝟙 ((ProjectionFormulaMonoidal.modelFunctor X).obj ((comparison X).inverse.obj A.obj)) ×ₘ
            (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).symm.hom.app D) ≫
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          ((comparison X).counitIso.hom.app A.obj ×ₘ
            (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app D) =
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          ((comparison X).counitIso.hom.app A.obj ×ₘ
            (derivedPullback f).map (𝟙 ((comparison Y).functor.obj D))) :=
      ((@MonoidalCategory.tensor _ _
        (Scheme.Modules.canonicalDerivedMonoidal X)).map_comp _ _).symm.trans
        (congrArg (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          (Prod.ext (Category.id_comp _)
            (((StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).inv_hom_id_app
              D).trans ((derivedPullback f).map_id ((comparison Y).functor.obj D)).symm)))
    exact cancel_chase _ _ _ _ _ _ _ _ hc hb hd
  exact pb_chase (Stacks.Duality.derivedPushforward f) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((swapIso Y).hom.app ((quasiCoherentDerivedPushforward f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj A, toQCoh ⟨D, hD⟩)) _ _ _ _ _
    (comparison_map_projectionMap f ((comparison X).inverse.obj A.obj) D) h₂ h₃ h₄ h₅ h₆
    ((@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)).map_id _)
    ((@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map_id _) rfl
    ((swapIso Y).hom_inv_id_app _)

/-- The counit of `Rf_* ⊣ a` tensored with `D`, at the standard model, through the comparison
isomorphisms of the models and of the tensor products and the braiding. -/
theorem comparison_map_tensor_counit (M : (qcoh Y).FullSubcategory) (D : Std Y) (hD : qcoh Y D) :
    (comparison Y).functor.map (((tensor Y).map ((adjunctionHomEquiv f M
        ((rightAdjointStd f).obj M) ((twistedInverseImage f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj (toQCoh M)).property).symm
          (𝟙 _))).app D) =
      (comparison Y).functor.map
          (((ProjectionFormulaLocallySmall.standardTensorIso Y).inv.app
            ((push f).obj ((comparison X).inverse.obj ((twistedInverseImage f
              (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
                (toQCoh M)).obj))).app D) ≫
        (tensorModelIso Y).inv.app
          ((ProjectionFormulaLocallySmall.standardPushforward f).obj
            ((comparison X).inverse.obj ((twistedInverseImage f
              (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj (toQCoh M)).obj), D) ≫
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)).map
          ((StacksDraft.DerivedModel.derivedPushforwardModelIso f.toLRSHom.toShHom).hom.app
              ((comparison X).inverse.obj ((twistedInverseImage f
                (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj (toQCoh M)).obj) ×ₘ
            𝟙 ((ProjectionFormulaMonoidal.modelFunctor Y).obj D)) ≫
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)).map
          ((Stacks.Duality.derivedPushforward f).map ((comparison X).counitIso.hom.app
            ((twistedInverseImage f
              (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj (toQCoh M)).obj) ×ₘ
            𝟙 ((comparison Y).functor.obj D)) ≫
        (swapIso Y).hom.app ((quasiCoherentDerivedPushforward f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj ((twistedInverseImage f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj (toQCoh M)),
          toQCoh ⟨D, hD⟩) ≫
        (ObjectProperty.ι _).map (((quasiCoherentDerivedTensor Y).obj (toQCoh ⟨D, hD⟩)).map
          ((twistedInverseImageAdjunction f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app (toQCoh M))) ≫
        (swapIso Y).inv.app (toQCoh M, toQCoh ⟨D, hD⟩) ≫
        (tensorModelIso Y).hom.app (M.obj, D) ≫
        (comparison Y).functor.map
          (((ProjectionFormulaLocallySmall.standardTensorIso Y).hom.app M.obj).app D) := by
  refine core_chase _ _ ((comparison Y).functor.map
      (((ProjectionFormulaMonoidal.standardTensorBifunctor Y).map ((adjunctionHomEquiv f M
        ((rightAdjointStd f).obj M) ((twistedInverseImage f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj (toQCoh M)).property).symm
          (𝟙 _))).app D)) _ _
    ((@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)).map
      ((comparison Y).functor.map ((adjunctionHomEquiv f M
        ((rightAdjointStd f).obj M) ((twistedInverseImage f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj (toQCoh M)).property).symm
          (𝟙 _)) ×ₘ (comparison Y).functor.map (𝟙 D))) _ _ _
    ((@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)).map
      (((twistedInverseImageAdjunction f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app (toQCoh M)).hom ×ₘ
        𝟙 ((comparison Y).functor.obj D))) _ _ _ _ ?_ ?_ ?_ ?_
    ((swapIso Y).hom_inv_id_app (toQCoh M, toQCoh ⟨D, hD⟩))
  · exact map_eq_comp₃ (comparison Y).functor _ _ _ _
      (nat_conj_app _ _ (ProjectionFormulaLocallySmall.standardTensorIso Y) _ D)
  · exact nat_conj ((tensorModelIso Y).app _) ((tensorModelIso Y).app (M.obj, D)) _ _ _
      ((tensorModelIso Y).hom.naturality (((((adjunctionHomEquiv f M
        ((rightAdjointStd f).obj M) ((twistedInverseImage f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj (toQCoh M)).property).symm
          (𝟙 _)), 𝟙 D) :
        (((push f).obj ((rightAdjointStd f).obj M), D) : Std Y × Std Y) ⟶ (M.obj, D))))
      (comp_uncurry_map_id _ _ _ _)
  · exact map_prod_comp₃ _ _ _ _ _ _ (comparison_map_adjunctionHomEquiv_symm_id f M)
      ((comparison Y).functor.map_id D)
  · exact comp_map_of_id_comp (ObjectProperty.ι _) _ _ _ _ _
      ((swapIso Y).hom.naturality ((((twistedInverseImageAdjunction f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app (toQCoh M)),
          𝟙 (toQCoh ⟨D, hD⟩)) : ((quasiCoherentDerivedPushforward f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj ((twistedInverseImage f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj (toQCoh M)),
          toQCoh ⟨D, hD⟩) ⟶ (toQCoh M, toQCoh ⟨D, hD⟩)))
      ((NatTrans.congr_app ((quasiCoherentDerivedTensor Y).map_id _) _).trans (NatTrans.id_app _ _))

omit [QuasiCompact f] [QuasiSeparated f] [CompactSpace X] [QuasiSeparatedSpace X] in
/-- The evaluation `D ⊗ᴸ M ⟶ K` corresponding to `β : M ⟶ R𝓗om(D, K)`, read on `D_QCoh(𝒪_Y)` at
the locally small model. -/
abbrev dualEvaluation (M : (qcoh Y).FullSubcategory) (D : Std Y) (hD : qcoh Y D)
    (Kq : (qcoh Y).FullSubcategory) (β : M.obj ⟶ ((sheafHom Y).obj (op D)).obj Kq.obj) :
    ((quasiCoherentDerivedTensor Y).obj (toQCoh ⟨D, hD⟩)).obj (toQCoh M) ⟶ toQCoh Kq :=
  ObjectProperty.homMk ((swapIso Y).inv.app (toQCoh M, toQCoh ⟨D, hD⟩) ≫
    (tensorModelIso Y).hom.app (M.obj, D) ≫
    (comparison Y).functor.map
      (((ProjectionFormulaLocallySmall.standardTensorIso Y).hom.app M.obj).app D) ≫
    (comparison Y).functor.map (curry Y M.obj D Kq.obj β))

/-- The transpose of the inverse projection formula, the counit and a morphism `ev` is the
comparison map of Equation 48.8.0.1 followed by `a(ev)`. -/
theorem homEquiv_inv_projectionFormulaMap_comp (K' L : quasiCoherentDerivedCategory Y)
    {Z : quasiCoherentDerivedCategory Y}
    (ev : ((quasiCoherentDerivedTensor Y).obj K').obj L ⟶ Z) :
    (twistedInverseImageAdjunction f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).homEquiv
        _ _ (inv (projectionFormulaMap f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (quasiCoherentDerivedPullbackTensorIso f).hom
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj L)
            K') ≫
        ((quasiCoherentDerivedTensor Y).obj K').map ((twistedInverseImageAdjunction f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app L) ≫ ev) =
      compareWithPullbackTensor f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (quasiCoherentDerivedPullbackTensorIso f).hom
          (twistedInverseImageAdjunction f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)) K' L ≫
        (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map ev := by
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  rfl

variable [IsNoetherian Y] {K : Std Y} (hK : IsDualizing K)

/-- **The transpose of the duality isomorphism on `X`.** Under the tensor–internal-Hom bijection
of [Stacks, Tag 08J8], `a(M) ⟶ R𝓗om(Lf^* D_Y(M), a(K))` is the morphism
`a(M) ⊗ᴸ Lf^* D_Y(M) ⟶ a(K)` corresponding under `Rf_* ⊣ a` to the inverse projection formula
followed by the counit `Rf_* a(M) ⟶ M` and the evaluation `M ⊗ᴸ D_Y(M) ⟶ K`. -/
theorem curry_dualityIso_hom_app (M : (plusCoh Y).FullSubcategory) :
    curry X ((rightAdjointStd f).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)
        ((pull f).obj (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj))
        ((rightAdjointStd f).obj (dualizingObject hK)) ((dualityIso f hK).hom.app M) =
      adjunctionHomEquiv f (dualizingObject hK)
        (((tensor X).obj ((rightAdjointStd f).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)).obj
          ((pull f).obj (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj)))
        (qcoh_tensor_pull f hK M.obj M.property
          ((rightAdjointStd f).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)).property)
        (@inv _ _ _ _ (projectionMap f
            ((rightAdjointStd f).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)
            (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj))
            (isIso_projectionMap_of_qcoh f
              ((rightAdjointStd f).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)
              (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj)
              ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
                (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)).property
              (qcoh_dual hK M.obj M.property)) ≫
          curry Y ((push f).obj ((rightAdjointStd f).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩))
            (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj) (dualizingObject hK).obj
            ((adjunctionHomEquiv f
              ⟨M.obj, plusCoh_le_qcoh _ M.property⟩
              ((rightAdjointStd f).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)
              ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
                (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)).property).symm (𝟙 _) ≫
            bidual Y (dualizingObject hK).obj M.obj)) := by
  have h := DualityFormula.cX_dualityFormulaIso_hom_app (TX := tensor X) (HX := sheafHom X)
      (cX := curry X)
      (TY := tensor Y) (HY := sheafHom Y) (cY := curry Y) (π := push f) (p := pull f)
      (PX := qcoh X) (PY := qcoh Y) (a := rightAdjointStd f) (α := adjunctionHomEquiv f)
      (ρ := projectionMap f) (K := dualizingObject hK) (β := bidual Y K) (𝓜 := plusCoh Y)
      (h𝓜 := plusCoh_le_qcoh)
      (hρ := fun F D hF hD => isIso_projectionMap_of_qcoh f F D hF hD)
      (hβ := fun M hM => isIso_bidual hK M hM)
      (hD := fun M hM => qcoh_dual hK M hM)
      (hT := fun M F hM hF => qcoh_tensor_pull f hK M hM F hF)
      (fun B Z k θ => curry_naturality_left X B Z k θ)
      (fun A _ _ Z l θ => curry_naturality_middle X A Z l θ)
      (fun B Z k θ => curry_naturality_left Y B Z k θ)
      (fun A _ _ Z l θ => curry_naturality_middle Y A Z l θ)
      (fun M _ _ hF hF' g h => DualityFormula.transportedHomEquiv_naturality_left M hF hF' g h)
      (fun φ F hF h => DualityFormula.transportedHomEquiv_naturality_right φ F hF h)
      (fun g D => projectionMap_natural_left f g D)
      (fun F _ _ d => projectionMap_natural_right f F d)
      (fun φ => bidual_naturality Y K φ)
      (fun M => ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        ⟨(comparison Y).functor.obj M.obj, M.property⟩).property)
      (fun M hM => qcoh_sheafHom_pull f hK M hM _
        ⟨isBoundedBelow_twistedInverseImage_obj f _
          (isBoundedBelow_of_isDualizingComplex_standard hK),
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            ⟨(comparison Y).functor.obj K, qcoh_of_isDualizingComplex hK⟩).property⟩) M
  exact h

/-- **The transpose of the duality isomorphism through the comparison map.** Under the
tensor–internal-Hom bijection, `a(M) ⟶ R𝓗om(Lf^* D_Y(M), a(K))` is, through the comparison of
the models, the comparison map `Lf^* D_Y(M) ⊗ᴸ a(M) ⟶ a(D_Y(M) ⊗ᴸ M)` of Equation 48.8.0.1
followed by `a` of the evaluation. -/
theorem curry_dualityIso_hom_app_eq_compareWithPullbackTensor (M : (plusCoh Y).FullSubcategory) :
    curry X ((rightAdjointStd f).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)
        ((pull f).obj (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj))
        ((rightAdjointStd f).obj (dualizingObject hK)) ((dualityIso f hK).hom.app M) =
      (comparison X).toAdjunction.homEquiv _ _
        (tensorPullComparison f ((twistedInverseImage f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
              (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩))
            (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj)
            (qcoh_dual hK M.obj M.property) ≫
          (compareWithPullbackTensor f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (quasiCoherentDerivedPullbackTensorIso f).hom
            (twistedInverseImageAdjunction f
              (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
            (toQCoh ⟨((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj,
              qcoh_dual hK M.obj M.property⟩)
            (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩) ≫
          (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
            (dualEvaluation ⟨M.obj, plusCoh_le_qcoh _ M.property⟩
              (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj)
              (qcoh_dual hK M.obj M.property) (dualizingObject hK)
              (bidual Y (dualizingObject hK).obj M.obj))).hom) := by
  refine (curry_dualityIso_hom_app f hK M).trans ?_
  refine (DualityFormula.transportedHomEquiv_eq_of_fac _ _ _ _ _
    (ObjectProperty.homMk (tensorPullComparison f ((twistedInverseImage f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
              (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩))
            (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj)
            (qcoh_dual hK M.obj M.property)))
    (inv (projectionFormulaMap f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (quasiCoherentDerivedPullbackTensorIso f).hom _ _) ≫
      ((quasiCoherentDerivedTensor Y).obj (toQCoh ⟨((sheafHom Y).obj (op M.obj)).obj
        (dualizingObject hK).obj, qcoh_dual hK M.obj M.property⟩)).map
        ((twistedInverseImageAdjunction f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app
          (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)) ≫
      dualEvaluation ⟨M.obj, plusCoh_le_qcoh _ M.property⟩
              (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj)
              (qcoh_dual hK M.obj M.property) (dualizingObject hK)
              (bidual Y (dualizingObject hK).obj M.obj)) ?_).trans ?_
  · apply ObjectProperty.hom_ext
    have hP : (ObjectProperty.ι _).map (projectionFormulaMap f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (quasiCoherentDerivedPullbackTensorIso f).hom ((twistedInverseImage f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩))
        (toQCoh ⟨(((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj),
          qcoh_dual hK M.obj M.property⟩)) ≫
        (ObjectProperty.ι _).map (inv (projectionFormulaMap f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (quasiCoherentDerivedPullbackTensorIso f).hom ((twistedInverseImage f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
              (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩))
          (toQCoh ⟨(((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj),
            qcoh_dual hK M.obj M.property⟩))) = 𝟙 _ := by
      exact map_comp_eq_id _ (IsIso.hom_inv_id _)
    exact cb_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
      ((pushModelIso f).inv_hom_id_app _)
      (map_comp_eq_id (comparison Y).functor (@IsIso.inv_hom_id _ _ _ _
        (projectionMap f ((rightAdjointStd f).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)
          (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj))
        (isIso_projectionMap_of_qcoh f _ _ ((twistedInverseImage f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)).property
          (qcoh_dual hK M.obj M.property))))
      hP (comparison_map_projectionMap_comp f ((twistedInverseImage f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩))
        (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj)
        (qcoh_dual hK M.obj M.property))
      ((comparison Y).functor.map_comp _ _)
      ((congrArg (comparison Y).functor.map (curry_naturality_left Y
        (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj)
        (dualizingObject hK).obj ((adjunctionHomEquiv f ⟨M.obj, plusCoh_le_qcoh _ M.property⟩
          ((rightAdjointStd f).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)).property).symm (𝟙 _))
        (bidual Y (dualizingObject hK).obj M.obj))).trans
        ((comparison Y).functor.map_comp _ _))
      (comparison_map_tensor_counit f ⟨M.obj, plusCoh_le_qcoh _ M.property⟩
        (((sheafHom Y).obj (op M.obj)).obj (dualizingObject hK).obj)
        (qcoh_dual hK M.obj M.property)) rfl
  · rw [homEquiv_inv_projectionFormulaMap_comp]
    rfl

end Formula

end Stacks.Duality.TwistedInverseImageDuality

end
