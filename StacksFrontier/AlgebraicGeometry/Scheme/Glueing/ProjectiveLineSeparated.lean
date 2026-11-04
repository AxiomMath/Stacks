module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine
import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAffineChart

/-!
# The projective line is separated over its base

The structure morphism of the projective line over a commutative ring `k` is separated. The
criterion used is the one the diagonal provides directly: a morphism is separated exactly when
its diagonal is a closed immersion, and a closed immersion may be recognised on an open cover
of the target. Covering `ℙ¹ ×_{Spec k} ℙ¹` by the four products of the two standard charts
reduces the question to four statements about rings, because the preimage of the diagonal in
`U_a ×_{Spec k} U_b` is the intersection `U_a ∩ U_b`:

* on the two diagonal squares the map is the diagonal of the affine line over `Spec k`, so it
  is a closed immersion because a morphism of affine schemes is;
* on the two off-diagonal squares it is `Spec` of the surjection
  `k[x] ⊗_k k[y] ⟶ k[T, T⁻¹]`, `x ↦ T`, `y ↦ T⁻¹`, whose surjectivity is the statement that
  every Laurent polynomial is a polynomial times a power of `T⁻¹`.

Separatedness over `Spec k` transfers to the projective line over any base by base change, since
the relative projective line is the fibre product of `S` and `ℙ¹_ℤ` over the terminal scheme.

## Main definitions

* `AlgebraicGeometry.projectiveLineOverlapCoordinate`,
  `AlgebraicGeometry.projectiveLineOverlapInverseCoordinate`: the two coordinates of the
  projective line read as functions on the overlap, namely `T` and `T⁻¹`.
* `AlgebraicGeometry.projectiveLineOverlapTensorLift`: the induced map
  `k[x] ⊗_k k[y] ⟶ k[T, T⁻¹]`.

## Main results

* `AlgebraicGeometry.isSeparated_of_openCover_isPullback`: a morphism is separated as soon as
  every pair of members of an open cover of its source has an intersection whose canonical map
  into their fibre product over the target is a closed immersion.
* `AlgebraicGeometry.projectiveLineOverlapTensorLift_surjective`: the ring-theoretic heart,
  that `k[x] ⊗_k k[y] ⟶ k[T, T⁻¹]` is surjective.
* `AlgebraicGeometry.projectiveLineXChart_base_eq_projectiveLineYChart_base_iff`: the point-level
  form of that intersection, namely that a point of the first chart and a point of the second
  chart agree in the projective line exactly when they are the two readings of one point of the
  overlap.
* `AlgebraicGeometry.projectiveLine_isSeparated`: **Stacks 01KQ**, the structure morphism of the
  projective line is separated.
* `AlgebraicGeometry.projectiveLine_isSeparated_terminalFrom`: the absolute form. The relative
  form, for the first projection of `pullback (terminal.from S) (terminal.from ℙ¹_ℤ)`, which is
  literally the structure morphism of the relative projective line `ℙ¹_S`, is found by instance
  search, from `AlgebraicGeometry.projectiveLine_schemeIsSeparated`.

## Implementation notes

The gluing datum is built through `CategoryTheory.GlueData.ofGlueData'`, which defines the
overlap objects by a classical `dite` on equality of indices. That `dite` is not reducible at a
concrete index pair, so the identification of the overlap with `Spec k[T, T⁻¹]` is a
propositional equality and the two chart inclusions of the overlap are reached through
`eqToHom`; a single cancellation lemma absorbs all of that bookkeeping.

The statement holds over an arbitrary commutative ring, not only over a field as in the source.

## References

* [Stacks Project, Tag 01KQ](https://stacks.math.columbia.edu/tag/01KQ)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### A separatedness criterion on an open cover -/

/-- A pullback square may be precomposed with an isomorphism of its apex. -/
private alias isPullback_iso_comp := Space.isPullback_iso_vertex

/-- **A separatedness criterion.** A morphism `p : X ⟶ S` is separated as soon as, for every
pair of members `U a`, `U b` of an open cover of `X`, the intersection `U a ∩ U b` maps into the
fibre product `U a ×_S U b` by a closed immersion. The intersection is presented as a pullback
square rather than as an open subscheme, which is the shape a gluing datum supplies. -/
lemma isSeparated_of_openCover_isPullback {X S : Scheme.{u}} (p : X ⟶ S) (𝒰 : X.OpenCover)
    (H : ∀ a b, ∃ (W : Scheme.{u}) (wa : W ⟶ 𝒰.X a) (wb : W ⟶ 𝒰.X b)
      (hpb : IsPullback wa wb (𝒰.f a) (𝒰.f b)),
      IsClosedImmersion (pullback.lift wa wb
        (show wa ≫ (𝒰.f a ≫ p) = wb ≫ (𝒰.f b ≫ p) by
          rw [← Category.assoc, ← Category.assoc, hpb.w]))) :
    IsSeparated p := by
  constructor
  refine IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 p p) ?_
  rintro ⟨a, b⟩
  obtain ⟨W, wa, wb, hpb, hci⟩ := H a b
  have key := pullback_map_diagonal_isPullback (𝒰.f a) (𝒰.f b) p
  refine (MorphismProperty.cancel_left_of_respectsIso
    (P := @IsClosedImmersion) key.isoPullback.hom _).mp ?_
  have e : key.isoPullback.hom ≫ Scheme.Cover.pullbackHom
      (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 p p) (pullback.diagonal p) (a, b) =
      pullback.map (𝒰.f a) (𝒰.f b) (𝒰.f a ≫ p) (𝒰.f b ≫ p) (𝟙 _) (𝟙 _) p
        (Category.id_comp _).symm (Category.id_comp _).symm :=
    key.isoPullback_hom_snd
  rw [e]
  refine (MorphismProperty.cancel_left_of_respectsIso
    (P := @IsClosedImmersion) hpb.isoPullback.hom _).mp ?_
  have e₂ : hpb.isoPullback.hom ≫ pullback.map (𝒰.f a) (𝒰.f b) (𝒰.f a ≫ p) (𝒰.f b ≫ p)
      (𝟙 _) (𝟙 _) p (Category.id_comp _).symm (Category.id_comp _).symm =
      pullback.lift wa wb
        (show wa ≫ (𝒰.f a ≫ p) = wb ≫ (𝒰.f b ≫ p) by
          rw [← Category.assoc, ← Category.assoc, hpb.w]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id,
        hpb.isoPullback_hom_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id,
        hpb.isoPullback_hom_snd]
  rwa [← e₂] at hci

/-- Recognising the map from an intersection into a fibre product of two affine schemes as a
closed immersion: it suffices that the induced map out of the tensor product is surjective. -/
private lemma isClosedImmersion_lift_of_surjective
    {R Sa Sb T : Type u} [CommRing R] [CommRing Sa] [CommRing Sb] [CommRing T]
    [Algebra R Sa] [Algebra R Sb]
    (ψa : Sa →+* T) (ψb : Sb →+* T) (F : Sa ⊗[R] Sb →+* T)
    (hFa : ∀ x : Sa, F (x ⊗ₜ[R] 1) = ψa x)
    (hFb : ∀ x : Sb, F (1 ⊗ₜ[R] x) = ψb x)
    (hsurj : Function.Surjective F)
    (w : Spec.map (CommRingCat.ofHom ψa) ≫ Spec.map (CommRingCat.ofHom (algebraMap R Sa)) =
         Spec.map (CommRingCat.ofHom ψb) ≫ Spec.map (CommRingCat.ofHom (algebraMap R Sb))) :
    IsClosedImmersion (pullback.lift (Spec.map (CommRingCat.ofHom ψa))
      (Spec.map (CommRingCat.ofHom ψb)) w) := by
  have key : pullback.lift (Spec.map (CommRingCat.ofHom ψa))
      (Spec.map (CommRingCat.ofHom ψb)) w
      = Spec.map (CommRingCat.ofHom F) ≫ (pullbackSpecIso R Sa Sb).inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun x ↦ (hFa x).symm)
    · rw [pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun x ↦ (hFb x).symm)
  rw [key]
  exact (MorphismProperty.cancel_right_of_respectsIso
    (P := @IsClosedImmersion) _ (pullbackSpecIso R Sa Sb).inv).mpr
    (IsClosedImmersion.spec_of_surjective _ hsurj)

/-! ### The overlap of the two charts -/

variable (k : Type u) [CommRing k]

/-- The coordinate of the first chart of the projective line, read as a function on the overlap:
it sends `x` to `T`. -/
def projectiveLineOverlapCoordinate : Polynomial k →ₐ[k] LaurentPolynomial k :=
  Polynomial.aeval (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial k)

/-- The coordinate of the second chart of the projective line, read as a function on the
overlap: it sends `y` to `T⁻¹`. -/
def projectiveLineOverlapInverseCoordinate : Polynomial k →ₐ[k] LaurentPolynomial k :=
  Polynomial.aeval (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial k)

/-- The map `k[x] ⊗_k k[y] ⟶ k[T, T⁻¹]` sending `x` to `T` and `y` to `T⁻¹`. Its surjectivity is
what makes the projective line separated. -/
def projectiveLineOverlapTensorLift :
    Polynomial k ⊗[k] Polynomial k →ₐ[k] LaurentPolynomial k :=
  Algebra.TensorProduct.lift (projectiveLineOverlapCoordinate k)
    (projectiveLineOverlapInverseCoordinate k) fun _ _ ↦ Commute.all _ _

/-- The value of `k[x] ⊗_k k[y] ⟶ k[T, T⁻¹]` on a pure tensor. -/
@[simp]
theorem projectiveLineOverlapTensorLift_tmul (f g : Polynomial k) :
    projectiveLineOverlapTensorLift k (f ⊗ₜ[k] g) =
      projectiveLineOverlapCoordinate k f * projectiveLineOverlapInverseCoordinate k g :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- The first coordinate, as a map to the overlap, is the localization map `k[x] ⟶ k[T, T⁻¹]`. -/
theorem projectiveLineOverlapCoordinate_apply (f : Polynomial k) :
    projectiveLineOverlapCoordinate k f = Polynomial.toLaurent f := by
  have h : (projectiveLineOverlapCoordinate k).toRingHom = Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [projectiveLineOverlapCoordinate]
    · simp [projectiveLineOverlapCoordinate]
  exact congrFun
    (congrArg (fun φ : Polynomial k →+* LaurentPolynomial k ↦ (φ : _ → _)) h) f

/-- **The ring-theoretic heart of separatedness.** Every Laurent polynomial is a polynomial in
`T` times a power of `T⁻¹`, so `k[x] ⊗_k k[y] ⟶ k[T, T⁻¹]` is surjective. -/
@[ega "I 5.5.11" "partial"]
theorem projectiveLineOverlapTensorLift_surjective :
    Function.Surjective (projectiveLineOverlapTensorLift k) := by
  intro f
  obtain ⟨n, f', hf⟩ := LaurentPolynomial.exists_T_pow f
  refine ⟨f' ⊗ₜ[k] (Polynomial.X ^ n), ?_⟩
  rw [projectiveLineOverlapTensorLift_tmul, projectiveLineOverlapCoordinate_apply, hf, map_pow]
  simp only [projectiveLineOverlapInverseCoordinate, Polynomial.aeval_X, LaurentPolynomial.T_pow]
  rw [mul_assoc, ← LaurentPolynomial.T_add]
  simp

/-- The second chart's inclusion of the overlap, as a morphism of affine schemes. -/
theorem projectiveLineInversionIso_hom_comp_puncturedChart :
    (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom) := by
  rw [← Spec.map_preimage ((projectiveLineInversionIso k).hom ≫
    projectiveLinePuncturedChart k)]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro a
    simp [projectiveLineInversionIso, projectiveLineOverlapInverseCoordinate]
  · simp [projectiveLineInversionIso, projectiveLineOverlapInverseCoordinate]

/-- The second chart's inclusion of the overlap, read in the other order. -/
theorem projectiveLineInversionIso_inv_comp_puncturedChart :
    (projectiveLineInversionIso k).inv ≫ projectiveLinePuncturedChart k =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom) := by
  have : (projectiveLineInversionIso k).inv = (projectiveLineInversionIso k).hom := rfl
  rw [this, projectiveLineInversionIso_hom_comp_puncturedChart]

/-- Both chart restrictions of the structure morphism are the structure morphism of the affine
line, written through the algebra map so that `pullbackSpecIso` applies. -/
theorem projectiveLineChart_comp_structureMorphism_algebraMap
    (i : (projectiveLineGluingData k).J) :
    (projectiveLineGluingData k).ι i ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) :=
  (projectiveLineStructureMorphism k).2 i

/-! ### The intersections of the two charts -/

/-- Two `eqToHom`s between the same pair of objects, in either order, cancel in front of a
morphism. The overlap objects of `CategoryTheory.GlueData.ofGlueData'` are a classical `dite`,
so every identification of them is reached through such a pair. -/
private lemma eqToHom_eqToHom_comp_cancel {C : Type*} [Category C] {X Y Z : C}
    (hp : X = Y) (hq : Y = X) (h : X ⟶ Z) :
    eqToHom hp ≫ eqToHom hq ≫ h = h := by
  cases hp
  simp

/-- The inclusion of the overlap of two distinct charts into the first one, read through the
identification of the overlap with the punctured affine line, is the localization map. -/
private theorem eqToHom_comp_projectiveLineGluingData_f_of_ne {i j : ULift.{u} Bool}
    (hij : i ≠ j) (h : (projectiveLineGluingData k).V (i, j) = Spec (.of (LaurentPolynomial k))) :
    eqToHom h.symm ≫ (projectiveLineGluingData k).f i j = projectiveLinePuncturedChart k := by
  simp only [projectiveLineGluingData, projectiveLineGluingData', ne_eq,
    CategoryTheory.GlueData.ofGlueData', dite_eq_ite, CategoryTheory.GlueData'.f', hij,
    ↓reduceDIte]
  exact eqToHom_eqToHom_comp_cancel _ _ _

/-- The inclusion of the overlap of two distinct charts into the second one, read through the
same identification, is the inversion followed by the localization map. -/
private theorem eqToHom_comp_projectiveLineGluingData_t_f_of_ne {i j : ULift.{u} Bool}
    (hij : i ≠ j) (h : (projectiveLineGluingData k).V (i, j) = Spec (.of (LaurentPolynomial k))) :
    eqToHom h.symm ≫ ((projectiveLineGluingData k).t i j ≫ (projectiveLineGluingData k).f j i) =
      (if i.down then (projectiveLineInversionIso k).inv
        else (projectiveLineInversionIso k).hom) ≫ projectiveLinePuncturedChart k := by
  simp only [projectiveLineGluingData, projectiveLineGluingData', ne_eq,
    CategoryTheory.GlueData.ofGlueData', dite_eq_ite, CategoryTheory.GlueData'.f', hij,
    Ne.symm hij, ↓reduceDIte, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  exact eqToHom_eqToHom_comp_cancel _ _ _

/-- The punctured affine line is the intersection of two distinct charts of the projective line,
the second coordinate being the inversion composed with the localization map. -/
private theorem isPullback_projectiveLineCharts_of_ne {i j : ULift.{u} Bool} (hij : i ≠ j)
    (h : (projectiveLineGluingData k).V (i, j) = Spec (.of (LaurentPolynomial k))) :
    IsPullback (projectiveLinePuncturedChart k)
      ((if i.down then (projectiveLineInversionIso k).inv
        else (projectiveLineInversionIso k).hom) ≫ projectiveLinePuncturedChart k)
      ((projectiveLineGluingData k).ι i) ((projectiveLineGluingData k).ι j) := by
  have hp : IsPullback
      (eqToHom h.symm ≫ (projectiveLineGluingData k).f i j)
      (eqToHom h.symm ≫ ((projectiveLineGluingData k).t i j ≫
        (projectiveLineGluingData k).f j i))
      ((projectiveLineGluingData k).ι i) ((projectiveLineGluingData k).ι j) :=
    isPullback_iso_comp
      (IsPullback.of_isLimit ((projectiveLineGluingData k).vPullbackConeIsLimit i j))
      (eqToIso h.symm)
  rwa [eqToHom_comp_projectiveLineGluingData_f_of_ne k hij h,
    eqToHom_comp_projectiveLineGluingData_t_f_of_ne k hij h] at hp

/-- The overlap of the first and second chart is the punctured affine line. -/
theorem projectiveLineGluingData_V_xy :
    (projectiveLineGluingData k).V (projectiveLineXIndex k, projectiveLineYIndex k)
      = Spec (.of (LaurentPolynomial k)) := by
  simp [projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
    projectiveLineGluingData', projectiveLineXIndex, projectiveLineYIndex]

/-- The overlap of the second and first chart is the punctured affine line. -/
theorem projectiveLineGluingData_V_yx :
    (projectiveLineGluingData k).V (projectiveLineYIndex k, projectiveLineXIndex k)
      = Spec (.of (LaurentPolynomial k)) := by
  simp [projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
    projectiveLineGluingData', projectiveLineXIndex, projectiveLineYIndex]

/-- The inclusion of the overlap into the first chart, read through the identification of the
overlap object of the gluing datum with the punctured affine line, is the localization map. -/
theorem eqToHom_comp_projectiveLineGluingData_f_xy :
    eqToHom (projectiveLineGluingData_V_xy k).symm ≫
        (projectiveLineGluingData k).f (projectiveLineXIndex k) (projectiveLineYIndex k) =
      projectiveLinePuncturedChart k :=
  eqToHom_comp_projectiveLineGluingData_f_of_ne k (by simp) (projectiveLineGluingData_V_xy k)

/-- The inclusion of the overlap into the second chart, read through the same identification, is
the second coordinate `y ↦ T⁻¹`. -/
theorem eqToHom_comp_projectiveLineGluingData_t_f_xy :
    eqToHom (projectiveLineGluingData_V_xy k).symm ≫
        ((projectiveLineGluingData k).t (projectiveLineXIndex k) (projectiveLineYIndex k) ≫
          (projectiveLineGluingData k).f (projectiveLineYIndex k) (projectiveLineXIndex k)) =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom) := by
  rw [eqToHom_comp_projectiveLineGluingData_t_f_of_ne k (by simp)
    (projectiveLineGluingData_V_xy k)]
  exact projectiveLineInversionIso_hom_comp_puncturedChart k

/-- The punctured affine line is the intersection of the two charts of the projective line, the
first coordinate being `T` and the second `T⁻¹`. -/
theorem isPullback_projectiveLineCharts :
    IsPullback (projectiveLinePuncturedChart k)
      (Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom))
      (projectiveLineXChart k) (projectiveLineYChart k) := by
  rw [← projectiveLineInversionIso_hom_comp_puncturedChart]
  exact isPullback_projectiveLineCharts_of_ne k (i := projectiveLineXIndex k)
    (j := projectiveLineYIndex k) (by simp) (projectiveLineGluingData_V_xy k)

/-- The punctured affine line is the intersection of the two charts, read in the other order. -/
theorem isPullback_projectiveLineCharts' :
    IsPullback (projectiveLinePuncturedChart k)
      (Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom))
      (projectiveLineYChart k) (projectiveLineXChart k) := by
  rw [← projectiveLineInversionIso_inv_comp_puncturedChart]
  exact isPullback_projectiveLineCharts_of_ne k (i := projectiveLineYIndex k)
    (j := projectiveLineXIndex k) (by simp) (projectiveLineGluingData_V_yx k)

/-- **A point of the first chart and a point of the second chart have the same image in the
projective line exactly when they are the two readings of a single point of the overlap.** This
is the point-level form of the pullback square
`AlgebraicGeometry.isPullback_projectiveLineCharts`. -/
theorem projectiveLineXChart_base_eq_projectiveLineYChart_base_iff
    (p q : Spec (.of (Polynomial k))) :
    (projectiveLineXChart k).base p = (projectiveLineYChart k).base q ↔
      ∃ w : Spec (.of (LaurentPolynomial k)),
        (projectiveLinePuncturedChart k).base w = p ∧
          (Spec.map (CommRingCat.ofHom
            (projectiveLineOverlapInverseCoordinate k).toRingHom)).base w = q := by
  have hpb := isPullback_projectiveLineCharts k
  have := hpb.hasPullback
  refine ⟨fun h ↦ ?_, fun ⟨w, hwp, hwq⟩ ↦ ?_⟩
  · obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback p q h
    refine ⟨hpb.isoPullback.inv.base z, ?_, ?_⟩
    · rw [← hz₁, ← hpb.isoPullback_inv_fst]
      rfl
    · rw [← hz₂, ← hpb.isoPullback_inv_snd]
      rfl
  · rw [← hwp, ← hwq]
    exact congrArg (fun φ : Spec (.of (LaurentPolynomial k)) ⟶ projectiveLine k ↦ φ.base w) hpb.w

/-- The off-diagonal squares of the cover: the punctured affine line maps into the product of
two affine lines over `Spec k` by a closed immersion. -/
private lemma isClosedImmersion_overlapLift
    {Pa Pb : Spec (.of (Polynomial k)) ⟶ Spec (.of k)}
    (ha : Pa = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
    (hb : Pb = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
    (w : projectiveLinePuncturedChart k ≫ Pa =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom) ≫ Pb) :
    IsClosedImmersion (pullback.lift (projectiveLinePuncturedChart k)
      (Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom)) w) := by
  subst ha hb
  exact isClosedImmersion_lift_of_surjective _ _ (projectiveLineOverlapTensorLift k).toRingHom
    (fun f ↦ by
      rw [show (projectiveLineOverlapTensorLift k).toRingHom (f ⊗ₜ[k] 1) =
        projectiveLineOverlapTensorLift k (f ⊗ₜ[k] 1) from rfl,
        projectiveLineOverlapTensorLift_tmul, map_one, mul_one,
        projectiveLineOverlapCoordinate_apply])
    (fun f ↦ by
      rw [show (projectiveLineOverlapTensorLift k).toRingHom (1 ⊗ₜ[k] f) =
        projectiveLineOverlapTensorLift k (1 ⊗ₜ[k] f) from rfl,
        projectiveLineOverlapTensorLift_tmul, map_one, one_mul]
      rfl)
    (projectiveLineOverlapTensorLift_surjective k) w

/-! ### Separatedness -/

/-- **Stacks Project, Tag 01KQ.** The structure morphism of the projective line is separated.
This holds over an arbitrary commutative ring, not only over a field. -/
@[stacks 01KQ]
theorem projectiveLine_isSeparated :
    IsSeparated (projectiveLine k ↘ Spec (.of k)) := by
  refine isSeparated_of_openCover_isPullback _ (projectiveLineGluingData k).openCover ?_
  intro a b
  have hdiag : ∀ i, IsSeparated
      ((projectiveLineGluingData k).ι i ≫ (projectiveLine k ↘ Spec (.of k))) := fun i ↦ by
    rw [projectiveLineChart_comp_structureMorphism_algebraMap]
    exact inferInstanceAs (IsSeparated (projectiveLineAffineStructureMorphism k))
  have hmono : ∀ i, Mono ((projectiveLineGluingData k).openCover.f i) := by
    intro i
    have : IsOpenImmersion ((projectiveLineGluingData k).openCover.f i) :=
      (projectiveLineGluingData k).ι_isOpenImmersion i
    infer_instance
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  have hmonoa := hmono ⟨a⟩
  cases a <;> cases b
  · exact ⟨_, 𝟙 _, 𝟙 _, CategoryTheory.IsKernelPair.id_of_mono _,
      (hdiag _).isClosedImmersion_diagonal⟩
  · exact ⟨_, _, _, isPullback_projectiveLineCharts k,
      isClosedImmersion_overlapLift k
        (projectiveLineChart_comp_structureMorphism_algebraMap k _)
        (projectiveLineChart_comp_structureMorphism_algebraMap k _) _⟩
  · exact ⟨_, _, _, isPullback_projectiveLineCharts' k,
      isClosedImmersion_overlapLift k
        (projectiveLineChart_comp_structureMorphism_algebraMap k _)
        (projectiveLineChart_comp_structureMorphism_algebraMap k _) _⟩
  · exact ⟨_, 𝟙 _, 𝟙 _, CategoryTheory.IsKernelPair.id_of_mono _,
      (hdiag _).isClosedImmersion_diagonal⟩

/-- The projective line is separated over the terminal scheme. -/
theorem projectiveLine_isSeparated_terminalFrom :
    IsSeparated (terminal.from (projectiveLine k)) := by
  rw [← terminal.comp_from (projectiveLine k ↘ Spec (.of k))]
  have := projectiveLine_isSeparated k
  have : IsSeparated (terminal.from (Spec (.of k))) := inferInstance
  infer_instance

/-- The projective line is a separated scheme. -/
instance projectiveLine_schemeIsSeparated : Scheme.IsSeparated (projectiveLine k) :=
  ⟨projectiveLine_isSeparated_terminalFrom k⟩

end AlgebraicGeometry

end

end
