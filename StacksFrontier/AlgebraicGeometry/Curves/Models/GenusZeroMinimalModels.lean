module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ProjectiveLineModel
public import StacksFrontier.AlgebraicGeometry.Models.BaseChange
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjPointOfRingHom
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.MatrixSubstitution
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.MY
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ToProjectiveLine

/-!
# Minimal models of a curve of genus zero are not unique

Let `R` be a discrete valuation ring with fraction field `K` and uniformizer `π`. The projective
line `ℙ¹_R` is a minimal model of `ℙ¹_K` for every identification of its generic fibre with
`ℙ¹_K`. Twisting the canonical identification by the automorphism `[u : v] ↦ [π u : v]` of
`ℙ¹_K` gives a second minimal model, and the two are not isomorphic as models.

## Main definitions

* `Stacks.Models.GenusZero.intPoint`: the point `[b : 1]` of the integral model of `ℙ¹`.
* `Stacks.Models.GenusZero.section`: the point `[b : 1]` of `ℙ¹_B` over `Spec B`.
* `Stacks.Models.GenusZero.scaling`: the automorphism `[u : v] ↦ [a u : v]` of `ℙ¹_K`.

## Main results

* `Stacks.Models.GenusZero.section_comp_scaling`: the scaling sends `[c : 1]` to `[a c : 1]`.
* `Stacks.Models.GenusZero.not_exists_isIso_isModelHom_scaling`: the two models of `ℙ¹_K` given
  by `ℙ¹_R` with the canonical identification and with the identification twisted by the scaling
  by `π` are not isomorphic.

## Implementation notes

A morphism of models `φ : ℙ¹_R ⟶ ℙ¹_R` from the first model to the second restricts on generic
fibres to the scaling by `π`. It sends the `R`-point `[1 : 1]` to the `R`-point `[π : 1]` and
fixes `[0 : 1]`, since `R`-points are determined by their restrictions to `Spec K`, `Spec R` being
reduced and `ℙ¹_R` separated. Over the residue field `[π : 1]` and `[0 : 1]` meet, while `[1 : 1]`
and `[0 : 1]` do not; so `φ` is not a monomorphism, and in particular not an isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace Stacks.Models.GenusZero

attribute [local instance] MvPolynomial.gradedAlgebra

section Points

variable (B : Type u) [CommRing B]

/-- The variables are homogeneous of degree one. -/
theorem X_mem (S : Type u) [CommRing S] (i : Fin 2) :
    (X i : MvPolynomial (Fin (1 + 1)) S) ∈
      Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading S 1 1 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _)

/-- The homomorphism `ℤ[T₀, T₁] → B` evaluating at `(b, 1)`. -/
def coordHom (b : B) : MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ) →+* B :=
  eval₂Hom ((Int.castRingHom B).comp ULift.ringEquiv.toRingHom) ![b, 1]

/-- The homomorphism `coordHom B b` sends `T₀` to `b`. -/
@[simp] theorem coordHom_X_zero (b : B) : coordHom B b (X 0) = b := by simp [coordHom]

/-- The homomorphism `coordHom B b` sends `T₁` to `1`. -/
@[simp] theorem coordHom_X_one (b : B) : coordHom B b (X 1) = 1 := by simp [coordHom]

/-- `coordHom` is natural in the ring of values. -/
theorem comp_coordHom {C : Type u} [CommRing C] (g : B →+* C) (b : B) :
    g.comp (coordHom B b) = coordHom C (g b) := by
  refine MvPolynomial.ringHom_ext (fun n => ?_) (fun i => ?_)
  · simp [coordHom]
  · fin_cases i <;> simp [coordHom]

/-- The point of the integral model `Proj ℤ[T₀, T₁]` of `ℙ¹` determined by `φ`, read on the chart
`D₊(Tₛ)`, as a morphism to `projectiveSpaceAtUniverse 1`. -/
def intPointOf {C : Type u} [CommRing C] (φ : MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ) →+* C)
    (s : Fin 2) (hu : IsUnit (φ (X s))) : Spec (.of C) ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  ProjPoint.point (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1) φ (X s)
    (X_mem _ s) one_pos hu

/-- The point `[b : 1]` of the integral model `Proj ℤ[T₀, T₁]` of `ℙ¹`, with values in `B`. -/
def intPoint (b : B) : Spec (.of B) ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  ProjPoint.point (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1)
    (coordHom B b) (X 1)
    (X_mem _ 1) one_pos (by rw [coordHom_X_one]; exact isUnit_one)

/-- The points `[b : 1]` are natural in the ring of values. -/
theorem SpecMap_comp_intPoint {C : Type u} [CommRing C] (g : B →+* C) (b : B) :
    Spec.map (CommRingCat.ofHom g) ≫ intPoint B b = intPoint C (g b) :=
  (ProjPoint.SpecMap_comp_point (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading
    (ULift.{u} ℤ) 1) g (coordHom B b) (X 1) (X_mem _ 1) one_pos _).trans
    (ProjPoint.point_congr_ringHom _ (comp_coordHom B g b) _ _ _ _ _)

/-- Over a nonzero ring, the points `[b : 1]` are distinct for distinct `b`. -/
theorem intPoint_injective {b b' : B} (h : intPoint B b = intPoint B b') : b = b' := by
  have h' := congrArg (fun φ => φ (HomogeneousLocalization.Away.mk
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1) (X_mem _ 1) 1 (X 0)
      (by simpa using X_mem _ 0)))
    (ProjPoint.awayEval_eq_of_point_eq _ _ _ _ _ h)
  simp only [ProjPoint.awayEval_mk, coordHom_X_zero] at h'
  have hone : ∀ c : B, ∀ hu : IsUnit (coordHom B c (X 1)), (↑(hu.unit⁻¹ ^ 1) : B) = 1 :=
    fun c hu => (ProjPoint.eq_val_inv_pow_of_mul_eq_one hu.unit 1 (by simp)).symm
  rwa [hone, hone, mul_one, mul_one] at h'

/-- The point `[b : 1]` of `ℙ¹_B`, as a section over `Spec B`. -/
def section' (b : B) : Spec (.of B) ⟶ projectiveSpaceOverRing 1 (.of B) :=
  pullback.lift (𝟙 _) (intPoint B b) (terminal.hom_ext _ _)

/-- The section `section' B b` composed with the first projection is the identity of `Spec B`. -/
@[simp] theorem section'_fst (b : B) : section' B b ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The section `section' B b` composed with the second projection is the point `intPoint B b`. -/
@[simp] theorem section'_snd (b : B) : section' B b ≫ pullback.snd _ _ = intPoint B b :=
  pullback.lift_snd _ _ _

/-- The section `[b : 1]` is the structure morphism's section. -/
@[simp] theorem section'_comp_structure (b : B) :
    section' B b ≫ (projectiveSpaceOverRing 1 (.of B) ↘ Spec (.of B)) = 𝟙 _ :=
  section'_fst B b

/-- The homomorphism `B[T₀, T₁] → B` evaluating at `(c, 1)`. -/
def polyHom (c : B) : MvPolynomial (Fin (1 + 1)) B →+* B := eval₂Hom (RingHom.id B) ![c, 1]

/-- The homomorphism `polyHom B c` sends `T₁` to `1`. -/
@[simp] theorem polyHom_X_one (c : B) : polyHom B c (X 1) = 1 := by simp [polyHom]

/-- The homomorphism `polyHom B c` sends `T₀` to `c`. -/
@[simp] theorem polyHom_X_zero (c : B) : polyHom B c (X 0) = c := by simp [polyHom]

/-- The point `[c : 1]` of the polynomial model `Proj B[T₀, T₁]`. -/
def polyPoint (c : B) :
    Spec (.of B) ⟶
      AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading B 1) :=
  ProjPoint.point (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading B 1) (polyHom B c) (X 1)
    (X_mem _ 1) one_pos (by rw [polyHom_X_one]; exact isUnit_one)

end Points

section MapHom

open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

variable {A A' σ τ : Type u} [CommRing A] [CommRing A'] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ A'] [AddSubgroupClass τ A'] (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  {B : Type u} [CommRing B]

/-- **Points and the morphism of Tag 01MY.** For a graded ring homomorphism `ψ : 𝒜 → ℬ` defined
everywhere on `Proj ℬ`, the point of `Proj ℬ` determined by `φ`, followed by the induced morphism
`Proj ℬ ⟶ Proj 𝒜`, is the point determined by `φ ∘ ψ`. -/
theorem point_comp_mapHom (ψ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ ψ = ⊤) (φ : A' →+* B)
    {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) (hu : IsUnit (φ (ψ s))) :
    ProjPoint.point ℬ φ (ψ s) (ψ.2 hs) hd hu ≫ (Scheme.topIso _).inv ≫
        (Scheme.isoOfEq _ hdom.symm).hom ≫ mapHom 𝒜 ℬ ψ =
      ProjPoint.point 𝒜 (φ.comp (ψ : A →+* A')) s hs hd hu := by
  have hι : (Proj.basicOpen ℬ (ψ s)).ι ≫ (Scheme.topIso _).inv ≫
      (Scheme.isoOfEq _ hdom.symm).hom =
        (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hs) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp
  unfold ProjPoint.point
  rw [Proj.awayι, Category.assoc, Category.assoc, reassoc_of% hι, homOfLE_mapHom, mapAwayHom,
    ← Proj.basicOpenIsoSpec_hom ℬ (ψ s) (ψ.2 hs) hd, Iso.inv_hom_id_assoc, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ProjPoint.awayEval_comp_awayMapOfGraded 𝒜 ψ φ hs hu]

end MapHom

section Comparison

open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.AlgebraicGeometry.ProjPolyChart

variable (B : Type u) [CommRing B]

/-- `polyHom` composed with the canonical coefficient map is `coordHom`. -/
theorem polyHom_comp_coordinateMap (c : B) :
    (polyHom B c).comp ((polynomialComparison B 1).coordinateMap :
      MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ) →+* MvPolynomial (Fin (1 + 1)) B) =
      coordHom B c := by
  refine MvPolynomial.ringHom_ext (fun n => ?_) (fun i => ?_)
  · simp [(polynomialComparison B 1).coordinateMap_apply, polyHom, coordHom]
  · fin_cases i <;> simp [(polynomialComparison B 1).coordinateMap_apply, polyHom, coordHom]

/-- The comparison of the two models, followed by the projection to `Spec B`. -/
private theorem polynomialComparison_inv_fst :
    (polynomialComparison B 1).iso.inv ≫ pullback.fst _ _ =
      Proj.toSpecZero (polyGrading B 1) ≫
        Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' (polyGrading B 1)).comp
          (algebraMap B (MvPolynomial (Fin (1 + 1)) B)))) := by
  rw [← (polynomialComparison B 1).toBase, Iso.inv_hom_id_assoc]

/-- The comparison of the two models, followed by the projection to `ℙ¹_ℤ`. -/
private theorem polynomialComparison_inv_snd :
    (polynomialComparison B 1).iso.inv ≫ pullback.snd _ _ =
      coordinateProjMap B 1 (polynomialComparison B 1).coordinateMap
        (polynomialComparison B 1).domain_eq_top := by
  rw [Iso.inv_comp_eq]
  exact (polynomialComparison B 1).toIntegral.symm

/-- The comparison of the two models sends the coordinate `Tₛ` to itself. -/
private theorem coordinateMap_X_eq (s : Fin 2) :
    (polynomialComparison B 1).coordinateMap (X s) = (X s : MvPolynomial (Fin (1 + 1)) B) := by
  rw [(polynomialComparison B 1).coordinateMap_apply]
  exact map_X _ _

/-- The degree-zero projection fixes the constants. -/
private theorem projZeroRingHom'_C (a : B) :
    (↑(GradedRing.projZeroRingHom' (polyGrading B 1) (C a)) : MvPolynomial (Fin (1 + 1)) B) =
      C a := by
  rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
    DirectSum.decompose_of_mem_same (polyGrading B 1)
      ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_C _ _))]

/-- **The point `[c : 1]` of the polynomial model is the point `[c : 1]` of `ℙ¹_B`**, under the
comparison of the two models. -/
theorem polyPoint_comp_iso_inv (c : B) :
    polyPoint B c ≫ (polynomialComparison B 1).iso.inv = section' B c := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, polynomialComparison_inv_fst, section'_fst, polyPoint, ← Category.assoc,
      ProjPoint.point_comp_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of B)
    ext a
    change polyHom B c (↑(GradedRing.projZeroRingHom' (polyGrading B 1) (C a))) = a
    rw [projZeroRingHom'_C]
    simp [polyHom]
  · have hX := coordinateMap_X_eq B 1
    rw [Category.assoc, polynomialComparison_inv_snd, section'_snd, polyPoint,
      ProjPoint.point_congr _ _ hX.symm _
        ((polynomialComparison B 1).coordinateMap.2 (X_mem _ 1)) _ _ (by rw [hX]; simp)]
    refine (point_comp_mapHom _ _ (polynomialComparison B 1).coordinateMap
      (polynomialComparison B 1).domain_eq_top (polyHom B c) (X_mem _ 1) one_pos _).trans ?_
    exact ProjPoint.point_congr_ringHom _ (polyHom_comp_coordinateMap B c) _ _ _ _ _

/-- The comparison of the two models sends the coordinate `Tₛ` to itself. -/
theorem coordinateMap_X (s : Fin 2) :
    (polynomialComparison B 1).coordinateMap (X s) = (X s : MvPolynomial (Fin (1 + 1)) B) :=
  coordinateMap_X_eq B s

/-- **Points of the polynomial model of `ℙ¹_B`, read on the base-change model.** The point of
`Proj B[T₀, T₁]` determined by `φ : B[T₀, T₁] →+* C` corresponds, under the comparison of the two
models, to the point of `ℙ¹_B` lying over `Spec(φ|_B)` and determined by `φ` on `ℤ[T₀, T₁]`. -/
theorem point_comp_iso_inv {L : Type u} [CommRing L] (φ : MvPolynomial (Fin (1 + 1)) B →+* L)
    (s : Fin 2) (hu : IsUnit (φ (X s))) :
    ProjPoint.point (polyGrading B 1) φ (X s) (X_mem _ s) one_pos hu ≫
        (polynomialComparison B 1).iso.inv =
      pullback.lift (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap B _))))
        (intPointOf (φ.comp ((polynomialComparison B 1).coordinateMap :
            MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ) →+* MvPolynomial (Fin (1 + 1)) B))
          s (by
            change IsUnit (φ ((polynomialComparison B 1).coordinateMap (X s)))
            rw [coordinateMap_X]; exact hu))
        (terminal.hom_ext _ _) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, polynomialComparison_inv_fst, pullback.lift_fst, ← Category.assoc,
      ProjPoint.point_comp_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have key : (φ.comp (algebraMap (polyGrading B 1 0) (MvPolynomial (Fin (1 + 1)) B))).comp
        ((GradedRing.projZeroRingHom' (polyGrading B 1)).comp
          (algebraMap B (MvPolynomial (Fin (1 + 1)) B))) =
        φ.comp (algebraMap B (MvPolynomial (Fin (1 + 1)) B)) := by
      ext a
      change φ (↑(GradedRing.projZeroRingHom' (polyGrading B 1) (C a))) = φ (C a)
      rw [projZeroRingHom'_C]
    rw [key]
  · rw [Category.assoc, polynomialComparison_inv_snd, pullback.lift_snd,
      ProjPoint.point_congr _ _ (coordinateMap_X B s).symm
      _ ((polynomialComparison B 1).coordinateMap.2 (X_mem _ s)) _ _
      (by rwa [coordinateMap_X])]
    exact point_comp_mapHom _ _ (polynomialComparison B 1).coordinateMap
      (polynomialComparison B 1).domain_eq_top φ (X_mem _ s) one_pos _

/-- The point `[c : 1]` of `ℙ¹_B`, transported to the polynomial model. -/
theorem section'_comp_iso_hom (c : B) :
    section' B c ≫ (polynomialComparison B 1).iso.hom = polyPoint B c := by
  rw [← polyPoint_comp_iso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Comparison

section Scaling

open Stacks.AlgebraicGeometry.ProjBaseChange

variable {K : Type u} [Field K]

/-- The diagonal matrix `diag(a, 1)`, for `a ≠ 0`. -/
def scalingMatrix (a : K) (ha : a ≠ 0) : Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![a, 1]) (by simpa using ha)

/-- **The scaling `[u : v] ↦ [a u : v]` of `ℙ¹_K`**, for `a ≠ 0`, as an automorphism over `K`.
It is the linear action of the inverse of `diag(a, 1)`, which `Proj` turns into the substitution
`T₀ ↦ a T₀`, `T₁ ↦ T₁`. -/
def scaling (a : K) (ha : a ≠ 0) :
    projectiveSpaceOverRing 1 (.of K) ≅ projectiveSpaceOverRing 1 (.of K) :=
  projectiveSpaceMatrixToAut K 1 (scalingMatrix a ha)⁻¹

/-- The scaling lies over `K`. -/
@[simp] theorem scaling_hom_comp_structure (a : K) (ha : a ≠ 0) :
    (scaling a ha).hom ≫ (projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K)) =
      projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K) :=
  projectiveSpaceMatrixToAut_hom_comp_structureMorphism K 1 _

/-- The substitution of `diag(a, 1)` followed by evaluation at `(c, 1)` is evaluation at
`(a c, 1)`. -/
theorem polyHom_comp_matrixSubst (a c : K) (ha : a ≠ 0) :
    (polyHom K c).comp (matrixSubstGradedHom K 1
      (((scalingMatrix a ha)⁻¹⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) : MvPolynomial (Fin (1 + 1)) K →+* MvPolynomial (Fin (1 + 1)) K) =
      polyHom K (a * c) := by
  rw [inv_inv]
  refine MvPolynomial.ringHom_ext (fun n => ?_) (fun i => ?_)
  · change polyHom K c (matrixSubstGradedHom K 1 _ (C n)) = polyHom K (a * c) (C n)
    rw [matrixSubstGradedHom_C]
    simp [polyHom]
  · change polyHom K c (matrixSubstGradedHom K 1 _ (X i)) = polyHom K (a * c) (X i)
    rw [matrixSubstGradedHom_X]
    fin_cases i <;> simp [polyHom, scalingMatrix, Fin.sum_univ_two, Matrix.diagonal_apply]

/-- **The scaling sends `[c : 1]` to `[a c : 1]`.** -/
theorem section'_comp_scaling (a c : K) (ha : a ≠ 0) :
    section' K c ≫ (scaling a ha).hom = section' K (a * c) := by
  rw [scaling, projectiveSpaceMatrixToAut_hom_eq, ← Category.assoc, section'_comp_iso_hom,
    ← polyPoint_comp_iso_inv, ← Category.assoc]
  congr 1
  have hX : (X 1 : MvPolynomial (Fin (1 + 1)) K) = matrixSubstGradedHom K 1
      (((scalingMatrix a ha)⁻¹⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) (X 1) := by
    rw [inv_inv, matrixSubstGradedHom_X]
    simp [scalingMatrix, Fin.sum_univ_two, Matrix.diagonal_apply]
  rw [polyPoint, ProjPoint.point_congr _ _ hX _ ((matrixSubstGradedHom K 1 _).2 (X_mem _ 1)) _ _
      (by rw [← hX]; simp), ProjPoint.point_comp_map, polyPoint]
  exact ProjPoint.point_congr_ringHom _ (polyHom_comp_matrixSubst a c ha) _ _ _ _ _

end Scaling

section ModelHom

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- A morphism of models `φ : X ⟶ X'` commutes with the projections `V ≅ X_K ⟶ X` and
`V ≅ X'_K ⟶ X'` of the generic fibres. -/
theorem _root_.Stacks.Models.IsModelHom.genericFiber_fst_comp {V X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of R)} {p' : X' ⟶ Spec (CommRingCat.of R)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)} {φ : X ⟶ X'}
    (hφ : IsModelHom p p' e e' φ) :
    e.hom ≫ pullback.fst p (genericPointInclusion R K) ≫ φ =
      e'.hom ≫ pullback.fst p' (genericPointInclusion R K) := by
  obtain ⟨h, he⟩ := hφ
  have hfst : pullback.fst p (genericPointInclusion R K) ≫ φ =
      genericFiberMapOfHomOver (K := K) p p' φ h ≫ pullback.fst p' (genericPointInclusion R K) :=
    (pullback.lift_fst _ _ _).symm
  rw [hfst, ← Category.assoc, he]

/-- A morphism `φ : X ⟶ X'` over `R` is a morphism of models as soon as it commutes with the
projections of the generic fibres to `X` and `X'`, the two identifications `e` and `e'` lying over
the same morphism `V ⟶ Spec K`. -/
theorem _root_.Stacks.Models.IsModelHom.of_genericFiber_fst_comp {V X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of R)} {p' : X' ⟶ Spec (CommRingCat.of R)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)} {φ : X ⟶ X'} (hφ : φ ≫ p' = p)
    (hsnd : e.hom ≫ pullback.snd p (genericPointInclusion R K) =
      e'.hom ≫ pullback.snd p' (genericPointInclusion R K))
    (hfst : e.hom ≫ pullback.fst p (genericPointInclusion R K) ≫ φ =
      e'.hom ≫ pullback.fst p' (genericPointInclusion R K)) :
    IsModelHom p p' e e' φ := by
  have h₁ : genericFiberMapOfHomOver (K := K) p p' φ hφ ≫
        pullback.fst p' (genericPointInclusion R K) =
      pullback.fst p (genericPointInclusion R K) ≫ φ :=
    pullback.lift_fst _ _ _
  have h₂ : genericFiberMapOfHomOver (K := K) p p' φ hφ ≫
        pullback.snd p' (genericPointInclusion R K) =
      pullback.snd p (genericPointInclusion R K) ≫ 𝟙 _ :=
    pullback.lift_snd _ _ _
  refine ⟨hφ, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, h₁, hfst]
  · rw [Category.assoc, h₂, Category.comp_id, hsnd]

end ModelHom

section NonUnique

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The pasting isomorphism of two pullback squares is compatible with the second projections.
This is the shape of `AlgebraicGeometry.ProjectiveSpace.baseChangeIso`. -/
theorem pullbackPasting_hom_snd {C : Type*} [Category C] [HasPullbacks C] {T S P W : C}
    (a : T ⟶ W) (b : P ⟶ W) (g : S ⟶ T) (a' : S ⟶ W) (h : g ≫ a = a') :
    ((pullbackSymmetry (pullback.fst a b) g).hom ≫ (pullbackRightPullbackFstIso a b g).hom ≫
      (pullback.congrHom h rfl).hom) ≫ pullback.snd a' b =
      pullback.fst (pullback.fst a b) g ≫ pullback.snd a b := by
  subst h
  simp [pullback.congrHom_hom]

/-- `ℙⁿ_T ×_T S ≅ ℙⁿ_S` is compatible with the projections to the integral model. -/
theorem projectiveSpaceOverBaseChangeIso_hom_snd (n : ℕ) {S T : Scheme.{u}} (g : S ⟶ T) :
    (projectiveSpaceOverBaseChangeIso n g).hom ≫ pullback.snd _ _ =
      pullback.fst (projectiveSpaceOver n T ↘ T) g ≫ pullback.snd _ _ :=
  pullbackPasting_hom_snd (terminal.from T) (terminal.from (ProjectiveSpaceZ n)) g _
    (terminal.comp_from g)

/-- A morphism `ℙ¹_T ⟶ ℙ¹_S` over `g : T ⟶ S` preserving the projections to the integral model
acts on points by composing the base coordinate with `g`. -/
private theorem lift_comp_of_comp_eq {S T W : Scheme.{u}} (g : T ⟶ S)
    (f : projectiveSpaceOver 1 T ⟶ projectiveSpaceOver 1 S)
    (hfst : f ≫ (projectiveSpaceOver 1 S ↘ S) = (projectiveSpaceOver 1 T ↘ T) ≫ g)
    (hsnd : f ≫ pullback.snd _ _ = pullback.snd _ _) (h : W ⟶ T)
    (k : W ⟶ projectiveSpaceAtUniverse.{u} 1) :
    pullback.lift h k (terminal.hom_ext _ _) ≫ f =
      pullback.lift (h ≫ g) k (terminal.hom_ext _ _) := by
  refine pullback.hom_ext ?_ ?_
  · change _ ≫ f ≫ (projectiveSpaceOver 1 S ↘ S) = _
    rw [hfst, pullback.lift_fst, ← Category.assoc]
    change (pullback.lift h k _ ≫ pullback.fst _ _) ≫ _ = _
    rw [pullback.lift_fst]
  · rw [Category.assoc, hsnd, pullback.lift_snd, pullback.lift_snd]

/-- The base change morphism `ℙ¹_T ⟶ ℙ¹_S` along `g : T ⟶ S`. -/
abbrev baseChangeLine {S T : Scheme.{u}} (g : T ⟶ S) :
    projectiveSpaceOver 1 T ⟶ projectiveSpaceOver 1 S :=
  (projectiveSpaceOverBaseChangeIso 1 g).inv ≫ pullback.fst _ _

/-- **The base change morphism `ℙ¹_T ⟶ ℙ¹_S`, on points.** -/
theorem lift_comp_baseChangeLine {S T W : Scheme.{u}} (g : T ⟶ S) (h : W ⟶ T)
    (k : W ⟶ projectiveSpaceAtUniverse.{u} 1) :
    pullback.lift h k (terminal.hom_ext _ _) ≫ baseChangeLine g =
      pullback.lift (h ≫ g) k (terminal.hom_ext _ _) := by
  have hsnd : baseChangeLine g ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [baseChangeLine, Category.assoc, ← projectiveSpaceOverBaseChangeIso_hom_snd,
      Iso.inv_hom_id_assoc]
  have hfst : baseChangeLine g ≫ (projectiveSpaceOver 1 S ↘ S) =
      (projectiveSpaceOver 1 T ↘ T) ≫ g := by
    rw [baseChangeLine, Category.assoc, pullback.condition, ← Category.assoc,
      ← projectiveSpaceOverBaseChangeIso_hom_over, Iso.inv_hom_id_assoc]
  exact lift_comp_of_comp_eq g _ hfst hsnd h k

/-- The base change morphism `ℙ¹_K ⟶ ℙ¹_R`, through the canonical identification of `ℙ¹_K` with
the generic fibre of `ℙ¹_R`. -/
abbrev genericFibreMap : projectiveSpaceOverRing 1 (.of K) ⟶ projectiveSpaceOverRing 1 (.of R) :=
  (projectiveLineGenericFibreIso (R := R) (K := K)).hom ≫ pullback.fst _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The base change morphism `ℙ¹_K ⟶ ℙ¹_R` preserves the projections to the integral model. -/
theorem genericFibreMap_snd :
    genericFibreMap (R := R) (K := K) ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [genericFibreMap, Category.assoc,
    show (projectiveLineGenericFibreIso (R := R) (K := K)).hom =
      (projectiveSpaceOverBaseChangeIso 1 (Spec.map (CommRingCat.ofHom (algebraMap R K)))).inv
      from rfl, ← projectiveSpaceOverBaseChangeIso_hom_snd, Iso.inv_hom_id_assoc]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The base change morphism `ℙ¹_K ⟶ ℙ¹_R` lies over `Spec K ⟶ Spec R`. -/
theorem genericFibreMap_structure :
    genericFibreMap (R := R) (K := K) ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) =
      (projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [genericFibreMap, Category.assoc, pullback.condition, ← Category.assoc,
    projectiveLineGenericFibreIso_hom_snd]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- **The base change morphism `ℙ¹_K ⟶ ℙ¹_R`, on points.** -/
theorem lift_comp_genericFibreMap {W : Scheme.{u}} (g : W ⟶ Spec (.of K))
    (k : W ⟶ projectiveSpaceAtUniverse.{u} 1) :
    pullback.lift g k (terminal.hom_ext _ _) ≫ genericFibreMap (R := R) (K := K) =
      pullback.lift (g ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) k
        (terminal.hom_ext _ _) := by
  exact lift_comp_of_comp_eq _ _ genericFibreMap_structure genericFibreMap_snd g k

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The point `[b : 1]` of `ℙ¹_K`, for `b ∈ R`, is the restriction of the `R`-point `[b : 1]`. -/
theorem section'_comp_genericFibreMap (b : R) :
    section' K (algebraMap R K b) ≫ genericFibreMap (R := R) (K := K) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ section' R b := by
  refine (lift_comp_genericFibreMap (𝟙 _) _).trans (pullback.hom_ext ?_ ?_)
  · simp [pullback.lift_fst]
  · simp [pullback.lift_snd, SpecMap_comp_intPoint]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The image of a uniformizer in the fraction field is nonzero. -/
theorem algebraMap_ne_zero_of_irreducible [IsDomain R] [IsFractionRing R K] {π : R}
    (hπ : Irreducible π) : algebraMap R K π ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero)

/-- **The twisted identification**: the canonical identification of `ℙ¹_K` with the generic
fibre of `ℙ¹_R`, precomposed with the scaling `[u : v] ↦ [π u : v]`. -/
def twistedGenericFibreIso {π : R} (hπ : Irreducible π) :
    projectiveSpaceOverRing 1 (.of K) ≅
      pullback (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  scaling (algebraMap R K π) (algebraMap_ne_zero_of_irreducible hπ) ≪≫
    projectiveLineGenericFibreIso

omit [IsDiscreteValuationRing R] in
/-- The twisted identification lies over `K`. -/
theorem twistedGenericFibreIso_hom_snd {π : R} (hπ : Irreducible π) :
    (twistedGenericFibreIso (K := K) hπ).hom ≫
        pullback.snd (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K) := by
  rw [twistedGenericFibreIso, Iso.trans_hom, Category.assoc,
    projectiveLineGenericFibreIso_hom_snd, scaling_hom_comp_structure]

omit [IsDiscreteValuationRing R] in
/-- A morphism of models from the canonical to the twisted model restricts on generic fibres to
the scaling by `π`. -/
theorem genericFibreMap_comp_of_isModelHom {π : R} (hπ : Irreducible π)
    {g : projectiveSpaceOverRing 1 (.of R) ⟶ projectiveSpaceOverRing 1 (.of R)}
    (hg : IsModelHom (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (projectiveLineGenericFibreIso (K := K)) (twistedGenericFibreIso hπ) g) :
    genericFibreMap (R := R) (K := K) ≫ g =
      (scaling (algebraMap R K π) (algebraMap_ne_zero_of_irreducible hπ)).hom ≫
        genericFibreMap (R := R) (K := K) := by
  have h := hg.genericFiber_fst_comp
  rw [twistedGenericFibreIso, Iso.trans_hom, Category.assoc] at h
  rwa [genericFibreMap, Category.assoc]

omit [IsDiscreteValuationRing R] in
/-- A morphism of models from the canonical to the twisted model sends the `R`-point `[b : 1]` to
the `R`-point `[π b : 1]`: the two agree on the generic point of `Spec R`, which is dense, and
`ℙ¹_R` is separated. -/
theorem section'_comp_of_isModelHom {π : R} (hπ : Irreducible π)
    {g : projectiveSpaceOverRing 1 (.of R) ⟶ projectiveSpaceOverRing 1 (.of R)}
    (hg : IsModelHom (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (projectiveLineGenericFibreIso (K := K)) (twistedGenericFibreIso hπ) g) (b : R) :
    section' R b ≫ g = section' R (π * b) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    isDominant_Spec_map_of_injective _ (IsFractionRing.injective R K)
  have : IsProper (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) :=
    isProper_projectiveSpaceOver 1 _
  refine ext_of_isDominant_of_isSeparated (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
    ?_ (Spec.map (CommRingCat.ofHom (algebraMap R K))) ?_
  · rw [Category.assoc, Exists.fst hg, section'_comp_structure, section'_comp_structure]
  · rw [← Category.assoc, ← section'_comp_genericFibreMap, Category.assoc,
      genericFibreMap_comp_of_isModelHom hπ hg, ← Category.assoc, section'_comp_scaling,
      ← map_mul, section'_comp_genericFibreMap]

/-- The `R`-points `[b : 1]` and `[b' : 1]` of `ℙ¹_R` agree over the residue field when `b` and
`b'` have the same residue. -/
private theorem residueSpecMap_comp_section'_eq {b b' : R}
    (h : algebraMap R (IsLocalRing.ResidueField R) b =
      algebraMap R (IsLocalRing.ResidueField R) b') :
    residueSpecMap R ≫ section' R b = residueSpecMap R ≫ section' R b' := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, section'_fst, Category.assoc, section'_fst]
  · rw [Category.assoc, section'_snd, Category.assoc, section'_snd, SpecMap_comp_intPoint,
      SpecMap_comp_intPoint, h]

/-- **The two minimal models are not isomorphic.** There is no isomorphism of models between
`ℙ¹_R` with the canonical identification of its generic fibre with `ℙ¹_K` and `ℙ¹_R` with that
identification twisted by the scaling `[u : v] ↦ [π u : v]`. -/
theorem not_exists_isIso_isModelHom_twisted {π : R} (hπ : Irreducible π) :
    ¬ ∃ g : projectiveSpaceOverRing 1 (.of R) ⟶ projectiveSpaceOverRing 1 (.of R), IsIso g ∧
      IsModelHom (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (projectiveLineGenericFibreIso (K := K)) (twistedGenericFibreIso hπ) g := by
  rintro ⟨g, hg, hmod⟩
  have hsec := section'_comp_of_isModelHom hπ hmod
  have hπ0 : algebraMap R (IsLocalRing.ResidueField R) π =
      algebraMap R (IsLocalRing.ResidueField R) 0 := by
    rw [map_zero]
    exact (IsLocalRing.residue_eq_zero_iff π).2 hπ.not_isUnit
  have h1 : (residueSpecMap R ≫ section' R 1) ≫ g = (residueSpecMap R ≫ section' R 0) ≫ g := by
    rw [Category.assoc, Category.assoc, hsec, hsec, mul_one, mul_zero]
    exact residueSpecMap_comp_section'_eq hπ0
  rw [cancel_mono] at h1
  have h2 : intPoint (IsLocalRing.ResidueField R) (algebraMap R _ 1) =
      intPoint (IsLocalRing.ResidueField R) (algebraMap R _ 0) := by
    rw [← SpecMap_comp_intPoint, ← SpecMap_comp_intPoint, ← section'_snd, ← section'_snd,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (fun q => q ≫ pullback.snd _ _) h1
  simpa using intPoint_injective (IsLocalRing.ResidueField R) h2

end NonUnique

end Stacks.Models.GenusZero

end
