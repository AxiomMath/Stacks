module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import StacksFrontier.Algebra.Polynomial.Laurent
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global sections of the projective line

The global sections of the structure sheaf of the projective line over a commutative ring `k`
are the constants: the canonical map `k ⟶ Γ(ℙ¹_k, ⊤)` obtained from the structure morphism is
an isomorphism. Consequently the projective line over a field is not affine.

## Main results

* `AlgebraicGeometry.isIso_constantsToGlobalSections`: the map `k ⟶ Γ(ℙ¹_k, ⊤)` induced by the
  structure morphism is an isomorphism.
* `AlgebraicGeometry.not_isAffine_projectiveLine`: the projective line over a field is not
  affine.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Helpers

private theorem gammaSpec_map_apply {R S : CommRingCat} (f : R ⟶ S) (x : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso S).hom ((Spec.map f).appTop x) = f ((Scheme.ΓSpecIso R).hom x) :=
  congrArg (fun g : Γ(Spec R, ⊤) ⟶ S => g.hom x) (Scheme.ΓSpecIso_naturality f)

variable (k : Type u) [CommRing k]

/-- Inversion on the punctured line intertwines the two chart inclusions into the projective
line. -/
private lemma projectiveLineInversion_comp_charts :
    (projectiveLineInversionIso k).hom ≫
        projectiveLinePuncturedChart k ≫ projectiveLineYChart k =
      projectiveLinePuncturedChart k ≫ projectiveLineXChart k := by
  classical
  let D := projectiveLineGluingData k
  let i : ULift.{u} Bool := ULift.up false
  let j : ULift.{u} Bool := ULift.up true
  have hij : i ≠ j := by decide
  have hji : j ≠ i := Ne.symm hij
  have hV (a b : ULift.{u} Bool) (hab : a ≠ b) : D.V (a, b) = Spec (.of (LaurentPolynomial k)) := by
    dsimp only [D, projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
      projectiveLineGluingData']
    rw [dite_eq_right hab]
  have hf (a b : ULift.{u} Bool) (hab : a ≠ b) :
      D.f a b = eqToHom (hV a b hab) ≫ projectiveLinePuncturedChart k := by
    dsimp only [D, projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
      projectiveLineGluingData', CategoryTheory.GlueData'.f', CategoryTheory.GlueData'.f,
      projectiveLinePuncturedChart]
    simp only [dite_eq_right hab]
  have hvij := hV i j hij
  have hvji := hV j i hji
  have hfi := hf i j hij
  have hfj := hf j i hji
  have ht : D.t i j = eqToHom hvij ≫ (projectiveLineInversionIso k).hom ≫
      eqToHom hvji.symm := by
    dsimp only [D, projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
      projectiveLineGluingData', CategoryTheory.GlueData'.t, projectiveLineInversionIso]
    simp only [dite_eq_right hij, i, Bool.false_eq_true, ↓reduceIte]
  have hιi : D.ι i = projectiveLineXChart k := rfl
  have hιj : D.ι j = projectiveLineYChart k := rfl
  have hcastj : eqToHom hvji.symm ≫ eqToHom hvji = 𝟙 (Spec (.of (LaurentPolynomial k))) :=
    (eqToIso hvji).inv_hom_id
  have hfactor : ((eqToHom hvij ≫ (projectiveLineInversionIso k).hom) ≫ eqToHom hvji.symm) ≫
      (eqToHom hvji ≫ projectiveLinePuncturedChart k) =
      (eqToHom hvij ≫ (projectiveLineInversionIso k).hom) ≫
        projectiveLinePuncturedChart k := by
    simp only [Category.assoc, ← Category.assoc (eqToHom hvji.symm) (eqToHom hvji),
      hcastj, Category.id_comp]
  have h := D.glue_condition i j
  rw [ht, hfj, hfi, hιi, hιj] at h
  have h' :
      ((eqToHom hvij ≫ (projectiveLineInversionIso k).hom) ≫
          projectiveLinePuncturedChart k) ≫ projectiveLineYChart k =
        (eqToHom hvij ≫ projectiveLinePuncturedChart k) ≫ projectiveLineXChart k := by
    calc
      _ = (((eqToHom hvij ≫ (projectiveLineInversionIso k).hom) ≫
          eqToHom hvji.symm) ≫ (eqToHom hvji ≫ projectiveLinePuncturedChart k)) ≫
            projectiveLineYChart k :=
        congrArg (fun f => f ≫ projectiveLineYChart k) hfactor.symm
      _ = _ := h
  apply (cancel_epi (eqToHom hvij)).1
  simpa only [Category.assoc] using h'

/-- A global section of the projective line restricts on the two charts to polynomials whose
images in the Laurent polynomials agree after inverting the coordinate. -/
private lemma projectiveLineChart_overlap (s : Γ(projectiveLine k, ⊤)) :
    Polynomial.toLaurent ((Scheme.ΓSpecIso (.of (Polynomial k))).hom
      ((projectiveLineXChart k).appTop s)) =
      LaurentPolynomial.invert (Polynomial.toLaurent
        ((Scheme.ΓSpecIso (.of (Polynomial k))).hom
          ((projectiveLineYChart k).appTop s))) := by
  have hcompat' : (projectiveLinePuncturedChart k).appTop
        ((projectiveLineXChart k).appTop s) =
      (projectiveLineInversionIso k).hom.appTop
        ((projectiveLinePuncturedChart k).appTop ((projectiveLineYChart k).appTop s)) := by
    have h := congrArg (fun f : Spec (.of (LaurentPolynomial k)) ⟶ projectiveLine k =>
      f.appTop s) (projectiveLineInversion_comp_charts k)
    simpa only [Scheme.Hom.comp_appTop, Category.assoc,
      CommRingCat.hom_comp, RingHom.comp_apply] using h.symm
  have hcomp := congrArg (fun z : Γ(Spec (.of (LaurentPolynomial k)), ⊤) =>
    (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom z) hcompat'
  have hT := gammaSpec_map_apply (CommRingCat.ofHom (Polynomial.toLaurent (R := k)))
  show Polynomial.toLaurent
      ((Scheme.ΓSpecIso (.of (Polynomial k))).hom ((projectiveLineXChart k).appTop s)) =
    LaurentPolynomial.invert (Polynomial.toLaurent
      ((Scheme.ΓSpecIso (.of (Polynomial k))).hom ((projectiveLineYChart k).appTop s)))
  calc
    _ = (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom
        ((projectiveLinePuncturedChart k).appTop ((projectiveLineXChart k).appTop s)) := (hT _).symm
    _ = (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom
        ((projectiveLineInversionIso k).hom.appTop
          ((projectiveLinePuncturedChart k).appTop ((projectiveLineYChart k).appTop s))) := hcomp
    _ = LaurentPolynomial.invert ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom
        ((projectiveLinePuncturedChart k).appTop ((projectiveLineYChart k).appTop s))) := by
      have hinv : (projectiveLineInversionIso k).hom =
          Spec.map (LaurentPolynomial.invert.toRingEquiv.toCommRingCatIso.hom) := rfl
      rw [hinv]
      convert gammaSpec_map_apply
        (LaurentPolynomial.invert.toRingEquiv.toCommRingCatIso.hom)
        ((projectiveLinePuncturedChart k).appTop
          ((projectiveLineYChart k).appTop s)) using 1
      · rfl
    _ = _ := by
      show LaurentPolynomial.invert
          ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom
            ((Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := k)))).appTop
              ((projectiveLineYChart k).appTop s))) =
        LaurentPolynomial.invert (Polynomial.toLaurent
          ((Scheme.ΓSpecIso (.of (Polynomial k))).hom
            ((projectiveLineYChart k).appTop s)))
      convert congrArg LaurentPolynomial.invert (hT ((projectiveLineYChart k).appTop s)) using 1

end Helpers

/-- The canonical map from `k` to the global sections of the structure sheaf
on the projective line over `k` is an isomorphism. -/
@[stacks 01JE "projective_line_global_sections", ega "I 2.3.2" "Γ(X,O_X) ≅ K"]
theorem isIso_constantsToGlobalSections (k : Type u) [CommRing k] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
      (projectiveLine k ↘ Spec (.of k)).appTop) := by
  let f := projectiveLine k ↘ Spec (.of k)
  let F : CommRingCat.of k ⟶ Γ(projectiveLine k, ⊤) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let C : CommRingCat.of k ⟶ CommRingCat.of (Polynomial k) :=
    CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)
  have chartEval (chart : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
      (hchart : chart ≫ f = projectiveLineAffineStructureMorphism k) (a : k) :
      (Scheme.ΓSpecIso (.of (Polynomial k))).hom
        (chart.appTop (F.hom a)) = Polynomial.C a := by
    have hmap : F ≫ chart.appTop = C ≫ (Scheme.ΓSpecIso (.of (Polynomial k))).inv := by
      simp [F, f, C, ← Scheme.Hom.comp_appTop, hchart, Scheme.ΓSpecIso_inv_naturality]
    have h : chart.appTop (F.hom a) =
        (Spec.map C).appTop ((Scheme.ΓSpecIso (.of k)).inv a) := by
      simpa [CommRingCat.hom_comp, RingHom.comp_apply] using
        congrArg (fun g : CommRingCat.Hom _ _ => g.hom a) hmap
    rw [h, gammaSpec_map_apply]
    simp [C]
  have hxEval := chartEval (projectiveLineXChart k)
    (projectiveLineXChart_comp_structureMorphism k)
  have hyEval := chartEval (projectiveLineYChart k)
    (projectiveLineYChart_comp_structureMorphism k)
  have chartEq (chart : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
      (hev : ∀ a : k, (Scheme.ΓSpecIso (.of (Polynomial k))).hom
        (chart.appTop (F.hom a)) = Polynomial.C a) (c : k) {s : Γ(projectiveLine k, ⊤)}
      (h : Polynomial.C c = (Scheme.ΓSpecIso (.of (Polynomial k))).hom (chart.appTop s)) :
      chart.appTop (F.hom c) = chart.appTop s :=
    (Scheme.ΓSpecIso (.of (Polynomial k))).commRingCatIsoToRingEquiv.injective ((hev c).trans h)
  show IsIso F
  apply (CategoryTheory.ConcreteCategory.isIso_iff_bijective F).mpr
  constructor
  · intro a b hab
    apply Polynomial.C_injective
    calc
      Polynomial.C a = (Scheme.ΓSpecIso (.of (Polynomial k))).hom
          ((projectiveLineXChart k).appTop (F.hom a)) := (hxEval a).symm
      _ = (Scheme.ΓSpecIso (.of (Polynomial k))).hom
          ((projectiveLineXChart k).appTop (F.hom b)) :=
        congrArg (fun s => (Scheme.ΓSpecIso (.of (Polynomial k))).hom
          ((projectiveLineXChart k).appTop s)) hab
      _ = Polynomial.C b := hxEval b
  · intro s
    have hrel := projectiveLineChart_overlap k s
    obtain ⟨c, hg, hh⟩ := Polynomial.toLaurent_eq_invert_toLaurent_iff.mp hrel
    refine ⟨c, ?_⟩
    apply (projectiveLineGluingData k).openCover.ext_elem
    intro i
    cases i with
    | up b =>
      cases b with
      | false => exact chartEq _ hxEval c (hg.symm)
      | true => exact chartEq _ hyEval c (hh.symm)

/-- The projective line over a field is not affine. -/
@[stacks 01JE "projective_line_not_affine", ega "I 2.3.2" "X not affine"]
theorem not_isAffine_projectiveLine (k : Type u) [Field k] :
    ¬ IsAffine (projectiveLine k) := by
  intro h
  let c := (Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveLine k ↘ Spec (.of k)).appTop
  have hc : IsIso c := isIso_constantsToGlobalSections k
  let eΓ : CommRingCat.of k ≅ Γ(projectiveLine k, ⊤) := asIso c
  let e : projectiveLine k ≅ Spec (.of k) :=
    Scheme.isoSpec (projectiveLine k) ≪≫ Scheme.Spec.mapIso eΓ.op
  have he : Function.Injective e.hom.base :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso e.hom.base).injective
  have huniq : ∀ x y : projectiveLine k, x = y := fun x y => he (Subsingleton.elim _ _)
  let η : Spec (.of (Polynomial k)) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ≠ affineLineOrigin k := by
    intro hη
    have hIdeal : (⊥ : Ideal (Polynomial k)) = Ideal.span {Polynomial.X} := by
      simpa [η, affineLineOrigin] using congrArg PrimeSpectrum.asIdeal hη
    have hx : Polynomial.X ∈ (⊥ : Ideal (Polynomial k)) := by
      rw [hIdeal]
      exact Ideal.subset_span (by simp)
    simp at hx
  have hchart : (projectiveLineXChart k) η ≠ projectiveLineZero k := by
    show (projectiveLineXChart k).base η ≠ (projectiveLineXChart k).base (affineLineOrigin k)
    intro heq
    exact hη ((projectiveLineXChart k).isOpenEmbedding.injective heq)
  exact hchart (huniq _ _).symm

end AlgebraicGeometry

end
