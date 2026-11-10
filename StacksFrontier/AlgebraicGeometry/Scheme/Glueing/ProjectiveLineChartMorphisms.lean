module

public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLinePoints
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSeparated

/-!
# Morphisms between projective lines given chartwise

The projective line `ℙ¹_R` is glued from two affine lines `Spec R[x]` and `Spec R[y]` along the
punctured line `Spec R[T, T⁻¹]`, with `x = T` and `y = T⁻¹`. A morphism out of `ℙ¹_R` is
therefore given by two morphisms out of the charts which agree on the overlap.

The morphisms of this file are the ones which send each chart into the corresponding chart.
Given a ring map `f : R ⟶ S` and two polynomials `p, q ∈ S[x]` with `p(T) · q(T⁻¹) = 1` in
`S[T, T⁻¹]`, the substitutions `x ↦ p` and `y ↦ q` (with coefficients mapped by `f`) agree on
the overlap and glue to a morphism `ℙ¹_S ⟶ ℙ¹_R` over `Spec S ⟶ Spec R`. Three instances are
singled out:

* `p = q = x` gives the base change morphism `ℙ¹_S ⟶ ℙ¹_R`, and the square it forms with the
  structure morphisms is cartesian: `ℙ¹_S = ℙ¹_R ×_{Spec R} Spec S`;
* `p = λ x` and `q = λ⁻¹ y` for a unit `λ` give the scaling `x ↦ λ x`;
* `p = x + c` and `q = y - c y²` for an element `c` with `c² = 0` give the translation
  `x ↦ x + c`, since `(T + c)(T⁻¹ - c T⁻²) = 1 - c² T⁻² = 1`.

## Main definitions

* `AlgebraicGeometry.projectiveLineDesc`: the morphism out of `ℙ¹_R` glued from two morphisms
  out of the charts agreeing on the overlap.
* `AlgebraicGeometry.projectiveLineHom`: the chart-preserving morphism `ℙ¹_S ⟶ ℙ¹_R` attached to
  `f : R →+* S` and two compatible substitutions.
* `AlgebraicGeometry.projectiveLineMap`: the base change morphism `ℙ¹_S ⟶ ℙ¹_R`.
* `AlgebraicGeometry.projectiveLineScaling`: the automorphism `x ↦ λ x` of `ℙ¹_R`.
* `AlgebraicGeometry.projectiveLineTranslation`: the automorphism `x ↦ x + c` of `ℙ¹_R` for
  `c² = 0`.

## Main results

* `AlgebraicGeometry.projectiveLine_hom_ext`: morphisms out of `ℙ¹_R` agreeing on both charts
  are equal.
* `AlgebraicGeometry.projectiveLineHom_comp_structureMorphism`: the chartwise morphism lies over
  `Spec S ⟶ Spec R`.
* `AlgebraicGeometry.isPullback_projectiveLineMap`: `ℙ¹_S` is the base change of `ℙ¹_R` along
  `Spec S ⟶ Spec R`.
* `AlgebraicGeometry.projectiveLineMap_comp_projectiveLineTranslation`: translations are
  compatible with base change.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

universe u

section Desc

variable {R : Type u} [CommRing R]

/-- Morphisms out of the projective line agreeing on both charts are equal. -/
theorem projectiveLine_hom_ext {Y : Scheme.{u}} {g h : projectiveLine R ⟶ Y}
    (hX : projectiveLineXChart R ≫ g = projectiveLineXChart R ≫ h)
    (hY : projectiveLineYChart R ≫ g = projectiveLineYChart R ≫ h) : g = h := by
  refine (projectiveLineGluingData R).openCover.hom_ext g h fun i ↦ ?_
  rcases i with ⟨_ | _⟩
  · exact hX
  · exact hY

/-- The morphism out of the projective line glued from two morphisms out of its charts which
agree on the overlap. -/
def projectiveLineDesc {Y : Scheme.{u}} (gX gY : Spec (.of R[X]) ⟶ Y)
    (h : projectiveLinePuncturedChart R ≫ gX =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫ gY) :
    projectiveLine R ⟶ Y :=
  (projectiveLineGluingData R).openCover.glueMorphisms
    (fun i ↦ match i with
      | ⟨false⟩ => gX
      | ⟨true⟩ => gY) (by
    have hp := isPullback_projectiveLineCharts R
    have hp' := isPullback_projectiveLineCharts' R
    rintro ⟨_ | _⟩ ⟨_ | _⟩
    · exact congrArg (· ≫ gX) ((cancel_mono (projectiveLineXChart R)).1 pullback.condition)
    · change pullback.fst (projectiveLineXChart R) (projectiveLineYChart R) ≫ gX =
        pullback.snd (projectiveLineXChart R) (projectiveLineYChart R) ≫ gY
      rw [← hp.isoPullback_inv_fst, ← hp.isoPullback_inv_snd, Category.assoc, Category.assoc, h]
    · change pullback.fst (projectiveLineYChart R) (projectiveLineXChart R) ≫ gY =
        pullback.snd (projectiveLineYChart R) (projectiveLineXChart R) ≫ gX
      rw [← hp'.isoPullback_inv_fst, ← hp'.isoPullback_inv_snd, Category.assoc, Category.assoc]
      congr 1
      rw [← projectiveLineInversionIso_hom_comp_puncturedChart, Category.assoc, h,
        ← projectiveLineInversionIso_inv_comp_puncturedChart, Category.assoc,
        Iso.hom_inv_id_assoc]
    · exact congrArg (· ≫ gY) ((cancel_mono (projectiveLineYChart R)).1 pullback.condition))

/-- On the first chart, the glued morphism is `gX`. -/
@[reassoc (attr := simp)]
theorem projectiveLineXChart_comp_desc {Y : Scheme.{u}} (gX gY : Spec (.of R[X]) ⟶ Y)
    (h : projectiveLinePuncturedChart R ≫ gX =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫ gY) :
    projectiveLineXChart R ≫ projectiveLineDesc gX gY h = gX :=
  (projectiveLineGluingData R).openCover.ι_glueMorphisms _ _ (projectiveLineXIndex R)

/-- On the second chart, the glued morphism is `gY`. -/
@[reassoc (attr := simp)]
theorem projectiveLineYChart_comp_desc {Y : Scheme.{u}} (gX gY : Spec (.of R[X]) ⟶ Y)
    (h : projectiveLinePuncturedChart R ≫ gX =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫ gY) :
    projectiveLineYChart R ≫ projectiveLineDesc gX gY h = gY :=
  (projectiveLineGluingData R).openCover.ι_glueMorphisms _ _ (projectiveLineYIndex R)

end Desc

/-- Composing the spectra of two ring maps is taking the spectrum of their composite. -/
theorem Spec_map_ofHom_comp_Spec_map_ofHom {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

section Hom

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (p q : S[X])
  (h : Polynomial.toLaurent p * projectiveLineOverlapInverseCoordinate S q = 1)

/-- The image `p(T)` of the first coordinate on the overlap, as a unit with inverse `q(T⁻¹)`. -/
def projectiveLineHomUnit : (LaurentPolynomial S)ˣ where
  val := Polynomial.toLaurent p
  inv := projectiveLineOverlapInverseCoordinate S q
  val_inv := h
  inv_val := by rw [mul_comm]; exact h

/-- The ring map `R[T, T⁻¹] ⟶ S[T, T⁻¹]` on the overlap induced by the substitution `x ↦ p`. -/
def projectiveLineHomOverlap : LaurentPolynomial R →+* LaurentPolynomial S :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp f) (projectiveLineHomUnit p q h)

/-- The substitution `x ↦ p` on the first chart agrees with `projectiveLineHomOverlap` on the
overlap. -/
theorem toLaurent_comp_eval₂RingHom :
    Polynomial.toLaurent.comp (eval₂RingHom (C.comp f) p) =
      (projectiveLineHomOverlap f p q h).comp Polynomial.toLaurent := by
  refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
  · simp [projectiveLineHomOverlap, LaurentPolynomial.eval₂_C]
  · simp [projectiveLineHomOverlap, projectiveLineHomUnit]

/-- The substitution `y ↦ q` on the second chart agrees with `projectiveLineHomOverlap` on the
overlap. -/
theorem overlapInverse_comp_eval₂RingHom :
    (projectiveLineOverlapInverseCoordinate S).toRingHom.comp (eval₂RingHom (C.comp f) q) =
      (projectiveLineHomOverlap f p q h).comp
        (projectiveLineOverlapInverseCoordinate R).toRingHom := by
  refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
  · simp [projectiveLineHomOverlap, projectiveLineOverlapInverseCoordinate,
      LaurentPolynomial.eval₂_C]
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [show projectiveLineOverlapInverseCoordinate R X = LaurentPolynomial.T (-1) by
      simp [projectiveLineOverlapInverseCoordinate]]
    rw [projectiveLineHomOverlap, LaurentPolynomial.eval₂_T]
    simp [projectiveLineHomUnit]

/-- **The chartwise morphism of projective lines.** For a ring map `f : R ⟶ S` and polynomials
`p, q ∈ S[x]` with `p(T) · q(T⁻¹) = 1`, the morphism `ℙ¹_S ⟶ ℙ¹_R` which sends each chart into
the corresponding chart by the substitutions `x ↦ p` and `y ↦ q`, coefficients being mapped by
`f`. -/
def projectiveLineHom : projectiveLine S ⟶ projectiveLine R :=
  projectiveLineDesc
    (Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) p)) ≫ projectiveLineXChart R)
    (Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) q)) ≫ projectiveLineYChart R) (by
      rw [← Category.assoc, ← Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom,
        Spec_map_ofHom_comp_Spec_map_ofHom, toLaurent_comp_eval₂RingHom f p q h,
        overlapInverse_comp_eval₂RingHom f p q h, ← Spec_map_ofHom_comp_Spec_map_ofHom,
        ← Spec_map_ofHom_comp_Spec_map_ofHom, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) (isPullback_projectiveLineCharts R).w)

/-- On the first chart, the chartwise morphism is the substitution `x ↦ p`. -/
@[reassoc (attr := simp)]
theorem projectiveLineXChart_comp_projectiveLineHom :
    projectiveLineXChart S ≫ projectiveLineHom f p q h =
      Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) p)) ≫ projectiveLineXChart R :=
  projectiveLineXChart_comp_desc _ _ _

/-- On the second chart, the chartwise morphism is the substitution `y ↦ q`. -/
@[reassoc (attr := simp)]
theorem projectiveLineYChart_comp_projectiveLineHom :
    projectiveLineYChart S ≫ projectiveLineHom f p q h =
      Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) q)) ≫ projectiveLineYChart R :=
  projectiveLineYChart_comp_desc _ _ _

/-- The chartwise morphism lies over `Spec S ⟶ Spec R`. -/
@[reassoc]
theorem projectiveLineHom_comp_structureMorphism :
    projectiveLineHom f p q h ≫ (projectiveLine R ↘ Spec (.of R)) =
      (projectiveLine S ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom f) := by
  refine projectiveLine_hom_ext ?_ ?_
  · rw [projectiveLineXChart_comp_projectiveLineHom_assoc,
      projectiveLineXChart_comp_structureMorphism, ← Category.assoc,
      projectiveLineXChart_comp_structureMorphism]
    simp only [projectiveLineAffineStructureMorphism, Spec_map_ofHom_comp_Spec_map_ofHom]
    congr 2
    ext r
    simp
  · rw [projectiveLineYChart_comp_projectiveLineHom_assoc,
      projectiveLineYChart_comp_structureMorphism, ← Category.assoc,
      projectiveLineYChart_comp_structureMorphism]
    simp only [projectiveLineAffineStructureMorphism, Spec_map_ofHom_comp_Spec_map_ofHom]
    congr 2
    ext r
    simp

/-- Any morphism agreeing with the chartwise substitutions on both charts is the chartwise
morphism. -/
theorem eq_projectiveLineHom {g : projectiveLine S ⟶ projectiveLine R}
    (hX : projectiveLineXChart S ≫ g =
      Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) p)) ≫ projectiveLineXChart R)
    (hY : projectiveLineYChart S ≫ g =
      Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) q)) ≫ projectiveLineYChart R) :
    g = projectiveLineHom f p q h :=
  projectiveLine_hom_ext (by rw [hX, projectiveLineXChart_comp_projectiveLineHom])
    (by rw [hY, projectiveLineYChart_comp_projectiveLineHom])

/-- If `x ∣ q`, the preimage of the first chart is the first chart. -/
theorem preimage_range_projectiveLineXChart (hq : X ∣ q) :
    (projectiveLineHom f p q h).base ⁻¹' Set.range (projectiveLineXChart R).base =
      Set.range (projectiveLineXChart S).base := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨⟨⟨⟩ | ⟨⟩⟩, y, rfl⟩ := (projectiveLineGluingData S).ι_jointly_surjective x
    · exact ⟨y, rfl⟩
    by_cases hy : (X : S[X]) ∈ y.asIdeal
    · obtain ⟨w, hw⟩ := hx
      have e : (projectiveLineXChart R).base w = (projectiveLineYChart R).base
          ((Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) q))).base y) := by
        rw [hw]
        change (projectiveLineYChart S ≫ projectiveLineHom f p q h).base y = _
        rw [projectiveLineYChart_comp_projectiveLineHom]
        rfl
      obtain ⟨v, -, hv⟩ := (projectiveLineXChart_base_eq_projectiveLineYChart_base_iff R _ _).1 e
      refine absurd ?_ ((mem_range_projectiveLineOverlapYInclusion_iff R _).1 ⟨v, hv⟩)
      change eval₂RingHom (C.comp f) q X ∈ y.asIdeal
      obtain ⟨r, rfl⟩ := hq
      rw [coe_eval₂RingHom, eval₂_X]
      exact y.asIdeal.mul_mem_right _ hy
    · obtain ⟨w, hw⟩ := (mem_range_projectiveLineOverlapYInclusion_iff S y).2 hy
      refine ⟨(projectiveLinePuncturedChart S).base w, ?_⟩
      rw [← hw]
      change (projectiveLinePuncturedChart S ≫ projectiveLineXChart S).base w =
        (projectiveLineOverlapYInclusion S ≫ projectiveLineYChart S).base w
      rw [(isPullback_projectiveLineCharts S).w]
  · rintro _ ⟨y, rfl⟩
    refine ⟨(Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) p))).base y, ?_⟩
    change _ = (projectiveLineXChart S ≫ projectiveLineHom f p q h).base y
    rw [projectiveLineXChart_comp_projectiveLineHom]
    rfl

/-- If `x ∣ p`, the preimage of the second chart is the second chart. -/
theorem preimage_range_projectiveLineYChart (hp : X ∣ p) :
    (projectiveLineHom f p q h).base ⁻¹' Set.range (projectiveLineYChart R).base =
      Set.range (projectiveLineYChart S).base := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨⟨⟨⟩ | ⟨⟩⟩, y, rfl⟩ := (projectiveLineGluingData S).ι_jointly_surjective x
    swap
    · exact ⟨y, rfl⟩
    by_cases hy : (X : S[X]) ∈ y.asIdeal
    · obtain ⟨w, hw⟩ := hx
      have e : (projectiveLineXChart R).base
          ((Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) p))).base y) =
            (projectiveLineYChart R).base w := by
        rw [hw]
        change _ = (projectiveLineXChart S ≫ projectiveLineHom f p q h).base y
        rw [projectiveLineXChart_comp_projectiveLineHom]
        rfl
      obtain ⟨v, hv, -⟩ := (projectiveLineXChart_base_eq_projectiveLineYChart_base_iff R _ _).1 e
      refine absurd ?_ ((mem_range_projectiveLinePuncturedChart_iff R _).1 ⟨v, hv⟩)
      change eval₂RingHom (C.comp f) p X ∈ y.asIdeal
      obtain ⟨r, rfl⟩ := hp
      rw [coe_eval₂RingHom, eval₂_X]
      exact y.asIdeal.mul_mem_right _ hy
    · obtain ⟨w, hw⟩ := (mem_range_projectiveLinePuncturedChart_iff S y).2 hy
      refine ⟨(projectiveLineOverlapYInclusion S).base w, ?_⟩
      rw [← hw]
      change (projectiveLineOverlapYInclusion S ≫ projectiveLineYChart S).base w =
        (projectiveLinePuncturedChart S ≫ projectiveLineXChart S).base w
      rw [(isPullback_projectiveLineCharts S).w]
  · rintro _ ⟨y, rfl⟩
    refine ⟨(Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) q))).base y, ?_⟩
    change _ = (projectiveLineYChart S ≫ projectiveLineHom f p q h).base y
    rw [projectiveLineYChart_comp_projectiveLineHom]
    rfl

/-- A morphism whose chart square commutes and whose preimage of the target chart is the source
chart makes that square a pullback. -/
private theorem isPullback_of_preimage_range_eq {X Y U V : Scheme.{u}} (ιU : U ⟶ X)
    [IsOpenImmersion ιU] (ιV : V ⟶ Y) [IsOpenImmersion ιV] (a : U ⟶ V) (g : X ⟶ Y)
    (w : ιU ≫ g = a ≫ ιV) (hr : g.base ⁻¹' Set.range ιV.base = Set.range ιU.base) :
    IsPullback ιU a g ιV := by
  let e := IsOpenImmersion.isoOfRangeEq ιU (pullback.fst g ιV) (by
    rw [Scheme.Pullback.range_fst, hr])
  refine IsPullback.of_iso_pullback ⟨w⟩ e (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _) ?_
  rw [← cancel_mono ιV, Category.assoc, ← pullback.condition, ← Category.assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, w]

/-- If `x ∣ q`, the first chart of `ℙ¹_S` is the preimage of the first chart of `ℙ¹_R`. -/
theorem isPullback_projectiveLineXChart_projectiveLineHom (hq : X ∣ q) :
    IsPullback (projectiveLineXChart S)
      (Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) p)))
      (projectiveLineHom f p q h) (projectiveLineXChart R) :=
  isPullback_of_preimage_range_eq _ _ _ _ (projectiveLineXChart_comp_projectiveLineHom f p q h)
    (preimage_range_projectiveLineXChart f p q h hq)

/-- If `x ∣ p`, the second chart of `ℙ¹_S` is the preimage of the second chart of `ℙ¹_R`. -/
theorem isPullback_projectiveLineYChart_projectiveLineHom (hp : X ∣ p) :
    IsPullback (projectiveLineYChart S)
      (Spec.map (CommRingCat.ofHom (eval₂RingHom (C.comp f) q)))
      (projectiveLineHom f p q h) (projectiveLineYChart R) :=
  isPullback_of_preimage_range_eq _ _ _ _ (projectiveLineYChart_comp_projectiveLineHom f p q h)
    (preimage_range_projectiveLineYChart f p q h hp)

/-- Composition of chartwise morphisms: the composite is the chartwise morphism of the composite
substitutions. -/
theorem projectiveLineHom_comp {T : Type u} [CommRing T] (g : S →+* T) (p' q' : T[X])
    (h' : Polynomial.toLaurent p' * projectiveLineOverlapInverseCoordinate T q' = 1)
    (p'' q'' : T[X])
    (h'' : Polynomial.toLaurent p'' * projectiveLineOverlapInverseCoordinate T q'' = 1)
    (hp : (eval₂RingHom (C.comp g) p').comp (eval₂RingHom (C.comp f) p) =
      eval₂RingHom (C.comp (g.comp f)) p'')
    (hq : (eval₂RingHom (C.comp g) q').comp (eval₂RingHom (C.comp f) q) =
      eval₂RingHom (C.comp (g.comp f)) q'') :
    projectiveLineHom g p' q' h' ≫ projectiveLineHom f p q h =
      projectiveLineHom (g.comp f) p'' q'' h'' := by
  refine eq_projectiveLineHom _ _ _ _ ?_ ?_
  · rw [projectiveLineXChart_comp_projectiveLineHom_assoc,
      projectiveLineXChart_comp_projectiveLineHom, ← Category.assoc,
      Spec_map_ofHom_comp_Spec_map_ofHom, hp]
  · rw [projectiveLineYChart_comp_projectiveLineHom_assoc,
      projectiveLineYChart_comp_projectiveLineHom, ← Category.assoc,
      Spec_map_ofHom_comp_Spec_map_ofHom, hq]

/-- The identity substitution gives the identity. -/
theorem projectiveLineHom_id
    (h : Polynomial.toLaurent (X : R[X]) * projectiveLineOverlapInverseCoordinate R X = 1) :
    projectiveLineHom (RingHom.id R) X X h = 𝟙 _ := by
  have e : eval₂RingHom (C.comp (RingHom.id R)) (X : R[X]) = RingHom.id _ :=
    Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)
  refine (eq_projectiveLineHom _ _ _ _ ?_ ?_).symm <;>
    · rw [e, Category.comp_id]
      exact (Category.id_comp _).symm.trans (by rw [← Spec.map_id]; rfl)

end Hom

/-! ### Base change -/

section BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- `T 1 * T (-1) = 1` in the Laurent polynomial ring. -/
private theorem T_one_mul_T_neg_one {R : Type u} [CommRing R] :
    (LaurentPolynomial.T 1 : LaurentPolynomial R) * LaurentPolynomial.T (-1) = 1 := by
  rw [← LaurentPolynomial.T_add]
  exact LaurentPolynomial.T_zero

/-- The identity substitutions are compatible on the overlap: `T · T⁻¹ = 1` in `S[T, T⁻¹]`. -/
theorem toLaurent_X_mul_overlapInverseCoordinate_X :
    Polynomial.toLaurent (X : S[X]) * projectiveLineOverlapInverseCoordinate S X = 1 := by
  rw [Polynomial.toLaurent_X, projectiveLineOverlapInverseCoordinate, aeval_X]
  exact T_one_mul_T_neg_one

/-- **The base change morphism `ℙ¹_S ⟶ ℙ¹_R`** of a ring map `f : R ⟶ S`: on both charts the
map `Spec S[x] ⟶ Spec R[x]` induced by `f` on coefficients. -/
def projectiveLineMap : projectiveLine S ⟶ projectiveLine R :=
  projectiveLineHom f X X toLaurent_X_mul_overlapInverseCoordinate_X

/-- The substitution `x ↦ x` with coefficients mapped by `f` is `Polynomial.mapRingHom f`. -/
theorem eval₂RingHom_C_comp_X : eval₂RingHom (C.comp f) (X : S[X]) = mapRingHom f :=
  Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)

/-- On the first chart, the base change morphism is induced by `f` on coefficients. -/
@[reassoc (attr := simp)]
theorem projectiveLineXChart_comp_projectiveLineMap :
    projectiveLineXChart S ≫ projectiveLineMap f =
      Spec.map (CommRingCat.ofHom (mapRingHom f)) ≫ projectiveLineXChart R := by
  rw [projectiveLineMap, projectiveLineXChart_comp_projectiveLineHom, eval₂RingHom_C_comp_X]

/-- On the second chart, the base change morphism is induced by `f` on coefficients. -/
@[reassoc (attr := simp)]
theorem projectiveLineYChart_comp_projectiveLineMap :
    projectiveLineYChart S ≫ projectiveLineMap f =
      Spec.map (CommRingCat.ofHom (mapRingHom f)) ≫ projectiveLineYChart R := by
  rw [projectiveLineMap, projectiveLineYChart_comp_projectiveLineHom, eval₂RingHom_C_comp_X]

/-- The base change morphism lies over `Spec S ⟶ Spec R`. -/
@[reassoc]
theorem projectiveLineMap_comp_structureMorphism :
    projectiveLineMap f ≫ (projectiveLine R ↘ Spec (.of R)) =
      (projectiveLine S ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom f) :=
  projectiveLineHom_comp_structureMorphism _ _ _ _

/-- The affine line over `S` is the base change of the affine line over `R`. -/
theorem isPullback_Spec_map_mapRingHom :
    IsPullback (Spec.map (CommRingCat.ofHom (mapRingHom f)))
      (Spec.map (CommRingCat.ofHom (C : S →+* S[X])))
      (Spec.map (CommRingCat.ofHom (C : R →+* R[X]))) (Spec.map (CommRingCat.ofHom f)) := by
  let := f.toAlgebra
  let : Algebra R[X] S[X] := Polynomial.algebra (R := R) (A := S)
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S R[X] S[X])).flip

/-- **The projective line is stable under base change**: `ℙ¹_S = ℙ¹_R ×_{Spec R} Spec S`. -/
theorem isPullback_projectiveLineMap :
    IsPullback (projectiveLineMap f) (projectiveLine S ↘ Spec (.of S))
      (projectiveLine R ↘ Spec (.of R)) (Spec.map (CommRingCat.ofHom f)) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (projectiveLineGluingData R).openCover
    fun i ↦ ?_
  have key : ∀ (ιR : Spec (.of R[X]) ⟶ projectiveLine R) (ιS : Spec (.of S[X]) ⟶ projectiveLine S),
      IsPullback ιS (Spec.map (CommRingCat.ofHom (mapRingHom f))) (projectiveLineMap f) ιR →
      ιR ≫ (projectiveLine R ↘ Spec (.of R)) = Spec.map (CommRingCat.ofHom C) →
      ιS ≫ (projectiveLine S ↘ Spec (.of S)) = Spec.map (CommRingCat.ofHom C) →
      IsPullback (pullback.snd (projectiveLineMap f) ιR)
        (pullback.fst (projectiveLineMap f) ιR ≫ (projectiveLine S ↘ Spec (.of S)))
        (ιR ≫ (projectiveLine R ↘ Spec (.of R))) (Spec.map (CommRingCat.ofHom f)) := by
    intro ιR ιS H hR hS
    refine (isPullback_Spec_map_mapRingHom f).of_iso H.isoPullback (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ (by simp)
    · simp
    · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoPullback_hom_fst, hS]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp, hR]
  have hX : X ∣ (X : S[X]) := dvd_refl _
  rcases i with ⟨_ | _⟩
  · have H := isPullback_projectiveLineXChart_projectiveLineHom f X X
      toLaurent_X_mul_overlapInverseCoordinate_X hX
    rw [eval₂RingHom_C_comp_X] at H
    exact key _ _ H (projectiveLineXChart_comp_structureMorphism R)
      (projectiveLineXChart_comp_structureMorphism S)
  · have H := isPullback_projectiveLineYChart_projectiveLineHom f X X
      toLaurent_X_mul_overlapInverseCoordinate_X hX
    rw [eval₂RingHom_C_comp_X] at H
    exact key _ _ H (projectiveLineYChart_comp_structureMorphism R)
      (projectiveLineYChart_comp_structureMorphism S)

end BaseChange

/-! ### Translations and scalings -/

section Automorphisms

variable {R : Type u} [CommRing R]

/-- For `c² = 0`, one has `(T + c)(T⁻¹ - c T⁻²) = 1` in `R[T, T⁻¹]`. -/
theorem toLaurent_mul_overlapInverseCoordinate_translation {c : R} (hc : c * c = 0) :
    Polynomial.toLaurent (X + C c) * projectiveLineOverlapInverseCoordinate R (X - C c * X ^ 2) =
      1 := by
  have h2 : (LaurentPolynomial.C c : LaurentPolynomial R) * LaurentPolynomial.C c = 0 := by
    rw [← map_mul, hc, map_zero]
  simp only [map_add, map_sub, map_mul, map_pow, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
    projectiveLineOverlapInverseCoordinate, aeval_X, aeval_C, LaurentPolynomial.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  linear_combination
    (1 - LaurentPolynomial.C c * LaurentPolynomial.T (-1)) * T_one_mul_T_neg_one (R := R) -
      LaurentPolynomial.T (-1) ^ 2 * h2

/-- **The translation `x ↦ x + c` of the projective line** by an element with `c² = 0`. On the
second chart it is `y ↦ y - c y²`, the expansion of `y / (1 + c y)`. -/
def projectiveLineTranslation (c : R) (hc : c * c = 0) : projectiveLine R ⟶ projectiveLine R :=
  projectiveLineHom (RingHom.id R) (X + C c) (X - C c * X ^ 2)
    (toLaurent_mul_overlapInverseCoordinate_translation hc)

/-- Translating by `c` and then by `-c` is the identity. -/
theorem projectiveLineTranslation_comp_neg {c : R} (hc : c * c = 0) :
    projectiveLineTranslation c hc ≫ projectiveLineTranslation (-c) (by rw [neg_mul_neg, hc]) =
      𝟙 _ := by
  rw [projectiveLineTranslation, projectiveLineTranslation,
    projectiveLineHom_comp _ _ _ _ _ _ _ _ X X toLaurent_X_mul_overlapInverseCoordinate_X,
    RingHom.comp_id, projectiveLineHom_id]
  · refine Polynomial.ringHom_ext (fun r ↦ by simp) ?_
    simp [map_neg]
  · have hC : (C c : R[X]) * C c = 0 := by rw [← C_mul, hc, C_0]
    refine Polynomial.ringHom_ext (fun r ↦ by simp) ?_
    simp only [coe_eval₂RingHom, eval₂_X, eval₂_sub, eval₂_mul, eval₂_C, eval₂_pow,
      RingHom.comp_apply, RingHom.id_apply, map_neg, eval₂_neg]
    linear_combination (-(2 : R[X]) * X ^ 3 + C c * X ^ 4) * hC

/-- The translation lies over the base. -/
@[reassoc (attr := simp)]
theorem projectiveLineTranslation_comp_structureMorphism {c : R} (hc : c * c = 0) :
    projectiveLineTranslation c hc ≫ (projectiveLine R ↘ Spec (.of R)) =
      projectiveLine R ↘ Spec (.of R) := by
  rw [projectiveLineTranslation, projectiveLineHom_comp_structureMorphism, CommRingCat.ofHom_id,
    Spec.map_id, Category.comp_id]

/-- **The translation automorphism `x ↦ x + c` of `ℙ¹_R`** for `c² = 0`, with inverse the
translation by `-c`. -/
def projectiveLineTranslationIso (c : R) (hc : c * c = 0) :
    projectiveLine R ≅ projectiveLine R where
  hom := projectiveLineTranslation c hc
  inv := projectiveLineTranslation (-c) (by rw [neg_mul_neg, hc])
  hom_inv_id := projectiveLineTranslation_comp_neg hc
  inv_hom_id := by
    have := projectiveLineTranslation_comp_neg (c := -c) (by rw [neg_mul_neg, hc])
    simp only [neg_neg] at this
    exact this

/-- Translations are compatible with base change: over `f : R ⟶ S`, the translation by `f c`
of `ℙ¹_S` lies over the translation by `c` of `ℙ¹_R`. -/
theorem projectiveLineMap_comp_projectiveLineTranslation {S : Type u} [CommRing S] (f : R →+* S)
    {c : R} (hc : c * c = 0) :
    projectiveLineMap f ≫ projectiveLineTranslation c hc =
      projectiveLineTranslation (f c) (by rw [← map_mul, hc, map_zero]) ≫ projectiveLineMap f := by
  unfold projectiveLineMap projectiveLineTranslation
  rw [projectiveLineHom_comp _ _ _ _ _ _ _ _ (X + C (f c)) (X - C (f c) * X ^ 2)
      (toLaurent_mul_overlapInverseCoordinate_translation (by rw [← map_mul, hc, map_zero])),
    projectiveLineHom_comp _ _ _ _ _ _ _ _ (X + C (f c)) (X - C (f c) * X ^ 2)
      (toLaurent_mul_overlapInverseCoordinate_translation (by rw [← map_mul, hc, map_zero])),
    RingHom.comp_id, RingHom.id_comp]
  all_goals refine Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)

/-- For a unit `u`, one has `(u T)(u⁻¹ T⁻¹) = 1` in `R[T, T⁻¹]`. -/
theorem toLaurent_mul_overlapInverseCoordinate_scaling (u : Rˣ) :
    Polynomial.toLaurent (C (u : R) * X) *
      projectiveLineOverlapInverseCoordinate R (C (↑u⁻¹ : R) * X) = 1 := by
  simp only [map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
    projectiveLineOverlapInverseCoordinate, aeval_X, aeval_C, LaurentPolynomial.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  calc LaurentPolynomial.C (u : R) * LaurentPolynomial.T 1 *
        (LaurentPolynomial.C (↑u⁻¹ : R) * LaurentPolynomial.T (-1)) =
      LaurentPolynomial.C ((u : R) * ↑u⁻¹) *
        (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) := by rw [map_mul]; ring
    _ = 1 := by rw [Units.mul_inv, map_one, T_one_mul_T_neg_one, one_mul]

/-- **The scaling `x ↦ u x` of the projective line** by a unit `u`. On the second chart it is
`y ↦ u⁻¹ y`. -/
def projectiveLineScaling (u : Rˣ) : projectiveLine R ⟶ projectiveLine R :=
  projectiveLineHom (RingHom.id R) (C (u : R) * X) (C (↑u⁻¹ : R) * X)
    (toLaurent_mul_overlapInverseCoordinate_scaling u)

/-- Scaling by `u` and then by `u⁻¹` is the identity. -/
theorem projectiveLineScaling_comp_inv (u : Rˣ) :
    projectiveLineScaling u ≫ projectiveLineScaling u⁻¹ = 𝟙 _ := by
  rw [projectiveLineScaling, projectiveLineScaling,
    projectiveLineHom_comp _ _ _ _ _ _ _ _ X X toLaurent_X_mul_overlapInverseCoordinate_X,
    RingHom.comp_id, projectiveLineHom_id]
  · refine Polynomial.ringHom_ext (fun r ↦ by simp) ?_
    simp only [coe_eval₂RingHom, eval₂_X, eval₂_mul, eval₂_C, RingHom.comp_apply,
      RingHom.id_apply]
    rw [← mul_assoc, ← C_mul, Units.inv_mul, C_1, one_mul]
  · refine Polynomial.ringHom_ext (fun r ↦ by simp) ?_
    simp only [coe_eval₂RingHom, eval₂_X, eval₂_mul, eval₂_C, RingHom.comp_apply,
      RingHom.id_apply, inv_inv]
    rw [← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul]

/-- The scaling lies over the base. -/
@[reassoc (attr := simp)]
theorem projectiveLineScaling_comp_structureMorphism (u : Rˣ) :
    projectiveLineScaling u ≫ (projectiveLine R ↘ Spec (.of R)) =
      projectiveLine R ↘ Spec (.of R) := by
  rw [projectiveLineScaling, projectiveLineHom_comp_structureMorphism, CommRingCat.ofHom_id,
    Spec.map_id, Category.comp_id]

/-- **The scaling automorphism `x ↦ u x` of `ℙ¹_R`**, with inverse the scaling by `u⁻¹`. -/
def projectiveLineScalingIso (u : Rˣ) : projectiveLine R ≅ projectiveLine R where
  hom := projectiveLineScaling u
  inv := projectiveLineScaling u⁻¹
  hom_inv_id := projectiveLineScaling_comp_inv u
  inv_hom_id := by
    have := projectiveLineScaling_comp_inv u⁻¹
    simp only [inv_inv] at this
    exact this

end Automorphisms

end AlgebraicGeometry
