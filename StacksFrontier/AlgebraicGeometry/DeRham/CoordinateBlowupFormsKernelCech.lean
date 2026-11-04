module

public import StacksFrontier.AlgebraicGeometry.DeRham.FormsGeneratorCalculus
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupTwistCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsComplementInjective
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsExtension
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateExceptionalLaurent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerStability

/-!
# The higher cohomology of the forms vanishing on the exceptional divisor

Fix a ring `R`, `n ≥ 1`, the coordinate blowup `b : L ⟶ X = 𝐀^{m+n}_R` with exceptional
divisor `j : E ⟶ L`, and `a ≥ 0`. Let `K = ker(Ω^a_{L/S} ⟶ j_*Ω^a_{E/S})` be the sheaf of
`a`-forms vanishing on `E`. Then `H^q(L, K) = 0` for `q ≥ 1`; this is the vanishing in clause
(3) of [Stacks, Tag 0FUR].

## Main definitions

* `Stacks.DeRham.CoordinateCech.formsKer`: the sheaf `K` of `a`-forms vanishing on `E`.

## Main results

* `Stacks.DeRham.CoordinateCech.isZero_rightDerived_formsKer`: `H^q(L, K) = 0` for `q ≥ 1`.
* `Stacks.DeRham.CoordinateCech.isZero_rightDerived_of_supported`: the higher cohomology of a
  quasi-coherent module vanishes when its sections over the intersections of a cover are
  identified with the functions supported on the allowed coordinates.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace AddMonoidAlgebra

universe u

namespace Stacks.DeRham.CoordinateCech

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- Reading a function on an open containing `W₀` as a Laurent polynomial. -/
def lamOf (hn : 0 < n) {V : (coordinateBlowup R m n).Opens} (h : punctured R m n ≤ V) :
    Γ(coordinateBlowup R m n, V) →+* Lau R m n :=
  (laurent R m n).comp (toFracOf R m n hn h)

/-- Reading a function as a Laurent polynomial commutes with restriction to a smaller open
containing `W₀`. -/
theorem lamOf_res (hn : 0 < n) {V V' : (coordinateBlowup R m n).Opens}
    (h : punctured R m n ≤ V') (hVV' : V' ≤ V) (z : Γ(coordinateBlowup R m n, V)) :
    lamOf R m n hn h (((coordinateBlowup R m n).presheaf.map (homOfLE hVV').op).hom z) =
      lamOf R m n hn (h.trans hVV') z := by
  simp only [lamOf, RingHom.comp_apply, toFracOf_res]

/-- Over an intersection of charts, reading functions as Laurent polynomials is injective. -/
theorem injective_lamOf_tupleOpen (hn : 0 < n) {p : ℕ} (x : Fin (p + 1) → Fin n) :
    Function.Injective (lamOf R m n hn (punctured_le_tupleOpen R m n hn x)) :=
  (laurent_injective R m n).comp (toFracOf_basicOpen_tupleRatio R m n hn x).1

/-- The functions over an intersection of charts, read as Laurent polynomials, are exactly the
chart Laurent polynomials. -/
theorem isChartLaurent_lamOf_tupleOpen (hn : 0 < n) {p : ℕ} (x : Fin (p + 1) → Fin n)
    (z : Γ(coordinateBlowup R m n, (tupleOpen R m n x).1)) :
    IsChartLaurent (Set.range (ULift.up.{u} ∘ x))
      (lamOf R m n hn (punctured_le_tupleOpen R m n hn x) z) := by
  have hf := ((toFracOf_basicOpen_tupleRatio R m n hn x).2 _).1 ⟨z, rfl⟩
  have h := coeff_laurent_mem_supported R m n 0 x (h := toFracOf R m n hn
    (punctured_le_basicOpen_tupleRatio R m n hn x) z) (by rwa [pow_zero, mul_one])
  intro v hv
  obtain ⟨⟨h1, h2⟩, h3⟩ := (Stacks.CechFinsupp.mem_supported.1 h) v hv
  exact ⟨h1, by simpa using h2, h3⟩

/-- Every chart Laurent polynomial is the Laurent polynomial of a function over the intersection
of charts. -/
theorem exists_lamOf_tupleOpen_eq (hn : 0 < n) {p : ℕ} (x : Fin (p + 1) → Fin n)
    (g : Lau R m n) (hg : IsChartLaurent (Set.range (ULift.up.{u} ∘ x)) g) :
    ∃ z : Γ(coordinateBlowup R m n, (tupleOpen R m n x).1),
      lamOf R m n hn (punctured_le_tupleOpen R m n hn x) z = g := by
  obtain ⟨h, hh1, hh2⟩ := exists_laurent_eq R m n 0 x g.coeff
    (Stacks.CechFinsupp.mem_supported.2 fun v hv ↦ by
      obtain ⟨h1, h2, h3⟩ := hg v hv
      exact ⟨⟨h1, by simpa using h2⟩, h3⟩)
  rw [pow_zero, mul_one] at hh2
  obtain ⟨z, hz⟩ := ((toFracOf_basicOpen_tupleRatio R m n hn x).2 h).2 hh2
  exact ⟨z, by simp only [lamOf, RingHom.comp_apply]; rw [hz]; exact coeff_injective hh1⟩

/-- A function pulled back from `X`, read as a Laurent polynomial. -/
theorem lamOf_appLE (hn : 0 < n) {V : (coordinateBlowup R m n).Opens} (h : punctured R m n ≤ V)
    (z : Γ(coordinateAmbient R m n, ⊤)) :
    lamOf R m n hn h (((coordinateBlowupToAmbient R m n).appLE ⊤ V le_top).hom z) =
      polyLaurent R m n z := by
  have h1 : resPunctured R m n h (((coordinateBlowupToAmbient R m n).appLE ⊤ V le_top).hom z) =
      ((coordinateBlowupToAmbient R m n).appLE ⊤ (punctured R m n) le_top).hom z :=
    congrArg (fun φ ↦ (CommRingCat.Hom.hom φ) z)
      (Scheme.Hom.appLE_map (coordinateBlowupToAmbient R m n) le_top (homOfLE h).op)
  change laurent R m n (puncturedEquiv R m n hn (resPunctured R m n h _)) = _
  rw [h1, puncturedEquiv_appLE, laurent_toFrac]

/-- The structure map of the ambient space on global sections is the inclusion of constants. -/
theorem coordinateAmbientToBase_appTop (r : R) :
    (coordinateAmbientToBase R m n).appTop ((Scheme.ΓSpecIso (.of R)).inv r) =
      Stacks.MoreMorphisms.gammaEquiv R m n (MvPolynomial.C r) := by
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ (coordinateAmbientToBase R m n).appTop) r =
    (Scheme.ΓSpecIso _).inv (MvPolynomial.C r)
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Pulling a function back from the base to an open of `L` factors through the global sections
of `X`. -/
private theorem appLE_coordinateBlowupToBase_eq {V : (coordinateBlowup R m n).Opens}
    (e : V ≤ coordinateBlowupToBase R m n ⁻¹ᵁ ⊤) (r : Γ(coordinateBase R, ⊤)) :
    ((coordinateBlowupToBase R m n).appLE ⊤ V e).hom r =
      ((coordinateBlowupToAmbient R m n).appLE ⊤ V le_top).hom
        ((coordinateAmbientToBase R m n).appTop r) := by
  have hcomp : (coordinateBlowupToBase R m n).appLE ⊤ V e =
      (coordinateAmbientToBase R m n).app ⊤ ≫
        (coordinateBlowupToAmbient R m n).appLE ⊤ V le_top := Scheme.Hom.comp_appLE _ _ _ _ _
  rw [hcomp]; rfl

/-- The constants, read as Laurent polynomials, are constant. -/
theorem lamOf_appLE_base (hn : 0 < n) {V : (coordinateBlowup R m n).Opens}
    (h : punctured R m n ≤ V) (e : V ≤ coordinateBlowupToBase R m n ⁻¹ᵁ ⊤)
    (r : Γ(coordinateBase R, ⊤)) :
    lamOf R m n hn h (((coordinateBlowupToBase R m n).appLE ⊤ V e).hom r) =
      single 0 ((Scheme.ΓSpecIso (.of R)).hom r) := by
  have hr : r = (Scheme.ΓSpecIso (.of R)).inv ((Scheme.ΓSpecIso (.of R)).hom r) := by simp
  rw [appLE_coordinateBlowupToBase_eq, lamOf_appLE]
  conv_lhs => rw [hr]
  rw [coordinateAmbientToBase_appTop, polyLaurent, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply, MvPolynomial.C_apply,
    Stacks.LaurentCoeff.toLaurent_monomial]
  congr 1
  ext; simp [Stacks.PartialLaurent.natToInt]

/-! ### The frame coordinates of the forms over `W₀` -/

variable (hn : 0 < n)

/-- The ring map of the forms over `W₀`: functions on the base to functions on `W₀`. -/
abbrev punctPhi : Γ(coordinateBase R, ⊤) ⟶ Γ(coordinateBlowup R m n, punctured R m n) :=
  (coordinateBlowupToBase R m n).appLE ⊤ (punctured R m n) le_top

/-- Reading the functions on `W₀` as Laurent polynomials. -/
abbrev punctLam : Γ(coordinateBlowup R m n, punctured R m n) →+* Lau R m n :=
  lamOf R m n hn (le_refl _)

/-- Each frame operator `frameOp s` vanishes on the Laurent polynomial of a function pulled back
from the base to `W₀`. -/
theorem punctLam_punctPhi (r : Γ(coordinateBase R, ⊤)) (s : Fin m ⊕ Fin n) :
    frameOp s (punctLam R m n hn ((punctPhi R m n) r)) = 0 :=
  (congrArg (frameOp s) (lamOf_appLE_base R m n hn (le_refl _) le_top r)).trans
    (frameOp_single_zero s _)

include hn in
/-- The torus `W₀` is an affine open. -/
theorem isAffineOpen_punctured : IsAffineOpen (punctured R m n) := (puncturedAffine R m n hn).2

/-- The identification of the `a`-forms over `W₀` with Kähler differentials. -/
abbrev punctIso (a : ℕ) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso (coordinateBlowupToBase R m n)
    (isAffineOpen_punctured R m n hn) (isAffineOpen_top _) le_top a

/-- **The frame coordinates of the `a`-forms over `W₀`.** -/
def punctCoord (a : ℕ) :
    Γ(Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n) (a : ℤ),
      punctured R m n) →+ (FrameIndex m n a →₀ R) where
  toFun ω := frameCoord R a (formsFrame (punctPhi R m n) (punctLam R m n hn)
    (punctLam_punctPhi R m n hn) a ((punctIso R m n hn a).hom ω))
  map_zero' := by simp
  map_add' x y := by simp

/-- The frame coordinates over `W₀` of a form are the coordinates of its frame expansion. -/
theorem punctCoord_apply (a : ℕ) (ω : Γ(Scheme.Hom.relativeDifferentialForms
      (coordinateBlowupToBase R m n) (a : ℤ), punctured R m n)) :
    punctCoord R m n hn a ω = frameCoord R a (formsFrame (punctPhi R m n) (punctLam R m n hn)
      (punctLam_punctPhi R m n hn) a ((punctIso R m n hn a).hom ω)) := rfl

/-- The frame coordinates of a generator over `W₀`. -/
theorem punctCoord_smul_gen (a : ℕ) (c : Γ(coordinateBlowup R m n, punctured R m n))
    (g : Fin a → Γ(coordinateBlowup R m n, punctured R m n)) :
    punctCoord R m n hn a (c • FormsGenerators.gen (coordinateBlowupToBase R m n) _ g) =
      frameCoord R a (punctLam R m n hn c • exteriorPower.ιMulti (Lau R m n) a fun i =>
        frameD (punctLam R m n hn (g i))) :=
  congrArg (frameCoord R a) (FormsGenerators.formsFrame_formsSectionsIso_smul_gen
    (coordinateBlowupToBase R m n) (isAffineOpen_punctured R m n hn) (isAffineOpen_top _) le_top
    (punctLam R m n hn) (punctLam_punctPhi R m n hn) c g)

/-- The frame coordinates of the restriction to `W₀` of a generator over an open `V ⊇ W₀`. -/
theorem punctCoord_res_smul_gen {V : (coordinateBlowup R m n).Opens} (h : punctured R m n ≤ V)
    (a : ℕ) (c : Γ(coordinateBlowup R m n, V)) (g : Fin a → Γ(coordinateBlowup R m n, V)) :
    punctCoord R m n hn a ((Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n)
        (a : ℤ)).presheaf.map (homOfLE h).op (c • FormsGenerators.gen _ V g)) =
      frameCoord R a (lamOf R m n hn h c • exteriorPower.ιMulti (Lau R m n) a fun i =>
        frameD (lamOf R m n hn h (g i))) := by
  rw [FormsGenerators.res_smul_gen, punctCoord_smul_gen]
  simp only [lamOf_res]

/-- Pulling functions back from `X` to `W₀`. -/
abbrev punctPsi : Γ(coordinateAmbient R m n, ⊤) →+* Γ(coordinateBlowup R m n, punctured R m n) :=
  ((coordinateBlowupToAmbient R m n).appLE ⊤ (punctured R m n) le_top).hom

/-- The coordinate functions on `W₀`. -/
abbrev punctVar (s : Fin m ⊕ Fin n) : Γ(coordinateBlowup R m n, punctured R m n) :=
  punctPsi R m n (Stacks.MoreMorphisms.gammaEquiv R m n (MvPolynomial.X s))

/-- The coordinate function `s` on `W₀` reads as the Laurent monomial of exponent
`Finsupp.single s 1`. -/
theorem punctLam_punctVar (s : Fin m ⊕ Fin n) :
    punctLam R m n hn (punctVar R m n s) = single (Finsupp.single s 1) 1 := by
  rw [lamOf_appLE, polyLaurent, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply, Stacks.LaurentCoeff.toLaurent_X]

/-- Under `puncturedEquiv`, a function on `X` pulled back to `W₀` is its image in the
localization. -/
theorem puncturedEquiv_punctPsi (z : Γ(coordinateAmbient R m n, ⊤)) :
    puncturedEquiv R m n hn (punctPsi R m n z) = toFrac R m n z :=
  puncturedEquiv_appLE R m n hn z

/-- A function on `X` that becomes a unit in the localization is a unit on `W₀`. -/
private theorem isUnit_punctPsi (hn : 0 < n) {z : Γ(coordinateAmbient R m n, ⊤)}
    (hz : IsUnit (toFrac R m n z)) : IsUnit (punctPsi R m n z) := by
  have h := hz.map (puncturedEquiv R m n hn).symm
  rwa [← puncturedEquiv_punctPsi R m n hn, RingEquiv.symm_apply_apply] at h

include hn in
/-- The coordinate functions `y_j` are units on `W₀`. -/
theorem isUnit_punctVar_inr (j : Fin n) : IsUnit (punctVar R m n (Sum.inr j)) :=
  isUnit_punctPsi R m n hn (isUnit_toFrac_coord R m n j)

/-- Pulling a function back from the base to `W₀` factors through the global sections of `X`. -/
theorem punctPhi_eq (r : Γ(coordinateBase R, ⊤)) :
    punctPhi R m n r = punctPsi R m n ((coordinateAmbientToBase R m n).appTop r) :=
  appLE_coordinateBlowupToBase_eq R m n le_top r

/-- The differential of a polynomial function on `X` pulled back to `W₀` lies in the span of the
differentials of the coordinate functions. -/
theorem d_punctPsi_mem_span (P : MvPolynomial (Fin m ⊕ Fin n) R) :
    (CommRingCat.KaehlerDifferential.D (punctPhi R m n)).d
        (punctPsi R m n (Stacks.MoreMorphisms.gammaEquiv R m n P)) ∈
      Submodule.span Γ(coordinateBlowup R m n, punctured R m n)
        (Set.range fun s => CommRingCat.KaehlerDifferential.d (f := punctPhi R m n)
          (punctVar R m n s)) := by
  set M := Submodule.span Γ(coordinateBlowup R m n, punctured R m n)
      (Set.range fun s => CommRingCat.KaehlerDifferential.d (f := punctPhi R m n)
        (punctVar R m n s))
  set D := CommRingCat.KaehlerDifferential.D (punctPhi R m n)
  induction P using MvPolynomial.induction_on with
  | C r =>
    have : punctPsi R m n (Stacks.MoreMorphisms.gammaEquiv R m n (MvPolynomial.C r)) =
        punctPhi R m n ((Scheme.ΓSpecIso (.of R)).inv r) := by
      rw [punctPhi_eq, coordinateAmbientToBase_appTop]
    rw [this, D.d_map]
    exact M.zero_mem
  | add p q hp hq =>
    rw [map_add, map_add, D.d_add]
    exact M.add_mem hp hq
  | mul_X p s hp =>
    rw [map_mul, map_mul, D.d_mul]
    exact M.add_mem (M.smul_mem _ (Submodule.subset_span ⟨s, rfl⟩)) (M.smul_mem _ hp)

include hn in
/-- The differentials of the coordinate functions span the Kähler differentials of `W₀`. -/
theorem span_d_punctVar :
    Submodule.span Γ(coordinateBlowup R m n, punctured R m n)
      (Set.range fun s => CommRingCat.KaehlerDifferential.d (f := punctPhi R m n)
        (punctVar R m n s)) = ⊤ := by
  classical
  set M := Submodule.span Γ(coordinateBlowup R m n, punctured R m n)
      (Set.range fun s ↦ CommRingCat.KaehlerDifferential.d (f := punctPhi R m n)
        (punctVar R m n s))
  let D := CommRingCat.KaehlerDifferential.D (punctPhi R m n)
  have hpoly : ∀ P : MvPolynomial (Fin m ⊕ Fin n) R,
      D.d (punctPsi R m n (Stacks.MoreMorphisms.gammaEquiv R m n P)) ∈ M :=
    d_punctPsi_mem_span R m n
  have hall : ∀ z, D.d z ∈ M := by
    intro z
    obtain ⟨⟨q, ⟨t, ht⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (coordProd R m n))
      (puncturedEquiv R m n hn z)
    obtain ⟨k, rfl⟩ := ht
    have hz' : z * punctPsi R m n (coordProd R m n ^ k) = punctPsi R m n q := by
      apply (puncturedEquiv R m n hn).injective
      rwa [map_mul, puncturedEquiv_punctPsi, puncturedEquiv_punctPsi]
    have hunit : IsUnit (punctPsi R m n (coordProd R m n ^ k)) := by
      refine isUnit_punctPsi R m n hn ?_
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (coordProd R m n) :
        IsUnit (toFrac R m n (coordProd R m n))).pow k
    have h1 := congrArg D.d hz'
    rw [D.d_mul] at h1
    obtain ⟨w, hw⟩ := hunit
    have h2 : D.d z = ((w⁻¹ : Units _) : Γ(coordinateBlowup R m n, punctured R m n)) •
        (D.d (punctPsi R m n q) - z • D.d (punctPsi R m n (coordProd R m n ^ k))) := by
      rw [← h1, add_sub_cancel_left, ← hw, smul_smul, Units.inv_mul, one_smul]
    rw [h2]
    have hq : D.d (punctPsi R m n q) ∈ M := by
      simpa using hpoly ((Stacks.MoreMorphisms.gammaEquiv R m n).symm q)
    have hp : D.d (punctPsi R m n (coordProd R m n ^ k)) ∈ M := by
      simpa using hpoly ((Stacks.MoreMorphisms.gammaEquiv R m n).symm (coordProd R m n ^ k))
    exact M.smul_mem _ (M.sub_mem hq (M.smul_mem _ hp))
  let := (punctPhi R m n).hom.toAlgebra
  have hs : Submodule.span Γ(coordinateBlowup R m n, punctured R m n)
      (Set.range fun b ↦ CommRingCat.KaehlerDifferential.d (f := punctPhi R m n) b) = ⊤ :=
    KaehlerDifferential.span_range_derivation _ _
  rw [eq_top_iff, ← hs, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  exact hall z

/-- The frame of the Kähler differentials of `W₀`: `d x_l` and `d log y_j`. -/
def punctFrame : Fin m ⊕ Fin n →
    CommRingCat.KaehlerDifferential (punctPhi R m n)
  | .inl l => CommRingCat.KaehlerDifferential.d (punctVar R m n (Sum.inl l))
  | .inr j => (((isUnit_punctVar_inr R m n hn j).unit⁻¹ : Units _) :
      Γ(coordinateBlowup R m n, punctured R m n)) •
      CommRingCat.KaehlerDifferential.d (punctVar R m n (Sum.inr j))

/-- The frame coordinates of `punctFrame s` are the indicator function of `s`. -/
theorem kaehlerFrame_punctFrame (s : Fin m ⊕ Fin n) :
    kaehlerFrame (punctPhi R m n) (punctLam R m n hn) (punctLam_punctPhi R m n hn)
      (punctFrame R m n hn s) = Pi.single s 1 := by
  classical
  rcases s with l | j
  · rw [punctFrame, kaehlerFrame_d, punctLam_punctVar, frameD_single_x]
  · rw [punctFrame, kaehlerFrame_smul, kaehlerFrame_d, punctLam_punctVar,
      frameD_single_y _ (fun l ↦ by simp)]
    set U := (isUnit_punctVar_inr R m n hn j).unit
    have hU : punctLam R m n hn (U : Γ(coordinateBlowup R m n, punctured R m n)) =
        single (Finsupp.single (Sum.inr j) 1) 1 := by
      rw [IsUnit.unit_spec, punctLam_punctVar]
    have hinv : punctLam R m n hn ((U⁻¹ : Units _) : Γ(coordinateBlowup R m n, punctured R m n)) =
        single (-Finsupp.single (Sum.inr j) (1 : ℤ)) 1 :=
      left_inv_eq_right_inv (a := punctLam R m n hn U)
        (by rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one])
        (by rw [hU, single_mul_single, add_neg_cancel, one_mul]; rfl)
    rw [hinv, smul_smul, single_mul_single, neg_add_cancel, one_mul]
    funext s
    rcases s with l | j'
    · simp
    · by_cases h : j' = j
      · subst h
        simp
        rfl
      · simp [Finsupp.single_apply, h, Ne.symm h]

/-- The frame `d x_l`, `d log y_j` spans the Kähler differentials of `W₀`. -/
theorem span_punctFrame :
    Submodule.span Γ(coordinateBlowup R m n, punctured R m n) (Set.range (punctFrame R m n hn)) =
      ⊤ := by
  refine eq_top_iff.2 ((span_d_punctVar R m n hn).symm.le.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨s, rfl⟩
  rcases s with l | j
  · exact Submodule.subset_span ⟨Sum.inl l, rfl⟩
  · have h : CommRingCat.KaehlerDifferential.d (f := punctPhi R m n) (punctVar R m n (Sum.inr j)) =
        ((isUnit_punctVar_inr R m n hn j).unit : Γ(coordinateBlowup R m n, punctured R m n)) •
          punctFrame R m n hn (Sum.inr j) := by
      rw [punctFrame, smul_smul, Units.mul_inv, one_smul]
    change CommRingCat.KaehlerDifferential.d (f := punctPhi R m n) (punctVar R m n (Sum.inr j)) ∈ _
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)

/-- **The frame coordinates over `W₀` determine the form.** -/
theorem punctCoord_injective (a : ℕ) : Function.Injective (punctCoord R m n hn a) := by
  intro x y hxy
  have h1 := frameCoord_injective (R := R) (m := m) (n := n) a hxy
  have h2 := formsFrame_injective (punctPhi R m n) (punctLam R m n hn) (punctLam_punctPhi R m n hn)
    ((laurent_injective R m n).comp ((puncturedEquiv R m n hn).injective.comp
      (fun _ _ h ↦ by simpa [resPunctured] using h))) (punctFrame R m n hn)
    (span_punctFrame R m n hn) (kaehlerFrame_punctFrame R m n hn) a h1
  exact (punctIso R m n hn a).toLinearEquiv.injective h2

/-! ### Sections of a kernel -/

section Kernel

open CategoryTheory.Limits

variable {Y : Scheme.{u}} {M N : Y.Modules} (g : M ⟶ N) (V : Y.Opens)

/-- A section of the kernel of `g` is sent to zero by `g`. -/
theorem app_kernel_ι_app (y : Γ(kernel g, V)) : g.app V ((kernel.ι g).app V y) = 0 := by
  change (kernel.ι g ≫ g).app V y = 0
  rw [kernel.condition]; rfl

end Kernel

/-! ### Restriction to `W₀` is injective on forms -/

/-- A function on `X`, pulled back to an intersection of charts. -/
abbrev tupleFn {p : ℕ} (x : Fin (p + 1) → Fin n) (z : Γ(coordinateAmbient R m n, ⊤)) :
    Γ(coordinateBlowup R m n, (tupleOpen R m n x).1) :=
  ((coordinateBlowup R m n).presheaf.map
    (homOfLE ((coordinateBlowup R m n).basicOpen_le (tupleRatio R m n x))).op).hom
    ((chartMap R m n (x 0)).hom z)

/-- A function on `X` pulled back to an intersection of charts reads as its Laurent
polynomial. -/
theorem lamOf_tupleFn {p : ℕ} (x : Fin (p + 1) → Fin n) (z : Γ(coordinateAmbient R m n, ⊤)) :
    lamOf R m n hn (punctured_le_tupleOpen R m n hn x) (tupleFn R m n x z) =
      polyLaurent R m n z := by
  rw [lamOf_res]
  simp only [lamOf, RingHom.comp_apply]
  rw [toFracOf_chartMap, laurent_toFrac]

/-- The generator `tupleGen` is the coordinate `coord (x 0)` pulled back to the intersection of
charts. -/
theorem tupleGen_eq {p : ℕ} (x : Fin (p + 1) → Fin n) :
    tupleGen R m n x = tupleFn R m n x (coord R m n (x 0)) := rfl

/-- A function over an intersection of charts whose Laurent polynomial is a unit is regular. -/
theorem isRegular_of_isUnit_lamOf {p : ℕ} (x : Fin (p + 1) → Fin n)
    (z : Γ(coordinateBlowup R m n, (tupleOpen R m n x).1))
    (hz : IsUnit (lamOf R m n hn (punctured_le_tupleOpen R m n hn x) z)) : IsRegular z := by
  have hinj := injective_lamOf_tupleOpen R m n hn x
  refine ⟨fun a b h ↦ hinj ?_, fun a b h ↦ hinj ?_⟩
  · have := congrArg (lamOf R m n hn (punctured_le_tupleOpen R m n hn x)) h
    simp only [map_mul] at this
    exact hz.mul_left_cancel this
  · have := congrArg (lamOf R m n hn (punctured_le_tupleOpen R m n hn x)) h
    simp only [map_mul] at this
    exact hz.mul_right_cancel this

/-- **A form over an intersection of charts vanishing on `W₀` vanishes.** -/
theorem res_punctured_forms_injective {p : ℕ} (x : Fin (p + 1) → Fin n) (a : ℕ) :
    Function.Injective ((Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n)
      (a : ℤ)).presheaf.map (homOfLE (punctured_le_tupleOpen R m n hn x)).op) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (coordinateBlowupToBase R m n) a
  set U := (tupleOpen R m n x).1
  set gU := tupleFn R m n x (coordProd R m n)
  refine (injective_iff_map_eq_zero _).2 fun s hs ↦ ?_
  have hle : U ⊓ (coordinateBlowup R m n).basicOpen gU ≤ punctured R m n := by
    rw [punctured_eq_basicOpen R m n hn (x 0)]
    intro y hy
    have := hy.2
    rw [Scheme.basicOpen_res] at this
    exact this.2
  have hz : (Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n)
        (a : ℤ)).presheaf.map
      (homOfLE (inf_le_left : U ⊓ (coordinateBlowup R m n).basicOpen gU ≤ U)).op s = 0 := by
    rw [show homOfLE (inf_le_left : U ⊓ (coordinateBlowup R m n).basicOpen gU ≤ U) =
      homOfLE hle ≫ homOfLE (punctured_le_tupleOpen R m n hn x) from rfl, op_comp,
      Functor.map_comp, ConcreteCategory.comp_apply, hs, map_zero]
  obtain ⟨k, hk⟩ := Scheme.Modules.exists_pow_smul_res_eq_zero_of_isCompact _ gU U
    (tupleOpen R m n x).2.isCompact le_rfl s hz
  have hid : (coordinateBlowup R m n).presheaf.map (homOfLE (le_refl U)).op gU = gU := by simp
  rw [hid] at hk
  have hreg : IsRegular (gU ^ k) := (isRegular_of_isUnit_lamOf R m n hn x gU (by
    rw [lamOf_tupleFn]; exact isUnit_polyLaurent_coordProd R m n)).pow k
  exact Stacks.Divisors.isSMulRegular_sections_relativeDifferentialForms
    (coordinateBlowupToBase R m n) (tupleOpen R m n x) ⟨⊤, isAffineOpen_top _⟩ le_top a _ hreg
    (hk.trans (smul_zero _).symm)

/-! ### The frame coordinates over an intersection of charts -/

section Tuple

variable {p : ℕ} (x : Fin (p + 1) → Fin n)

/-- An intersection of charts is an affine open. -/
theorem isAffineOpen_tupleOpen : IsAffineOpen (tupleOpen R m n x).1 := (tupleOpen R m n x).2

/-- Reading functions over an intersection of charts as Laurent polynomials. -/
abbrev tupleLam : Γ(coordinateBlowup R m n, (tupleOpen R m n x).1) →+* Lau R m n :=
  lamOf R m n hn (punctured_le_tupleOpen R m n hn x)

/-- The structure ring map of the forms over an intersection of charts. -/
abbrev tuplePhi : Γ(coordinateBase R, ⊤) ⟶ Γ(coordinateBlowup R m n, (tupleOpen R m n x).1) :=
  (coordinateBlowupToBase R m n).appLE ⊤ (tupleOpen R m n x).1 le_top

/-- Each frame operator `frameOp s` vanishes on the Laurent polynomial of a function pulled back
from the base to an intersection of charts. -/
theorem tupleLam_tuplePhi (r : Γ(coordinateBase R, ⊤)) (s : Fin m ⊕ Fin n) :
    frameOp s (tupleLam R m n hn x ((tuplePhi R m n x) r)) = 0 :=
  (congrArg (frameOp s) (lamOf_appLE_base R m n hn _ le_top r)).trans (frameOp_single_zero s _)

/-- The identification of the forms over an intersection of charts with Kähler differentials. -/
abbrev tupleIso (a : ℕ) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso (coordinateBlowupToBase R m n)
    (isAffineOpen_tupleOpen R m n x) (isAffineOpen_top _) le_top a

/-- **Restriction to `W₀`, in frame coordinates.** -/
theorem punctCoord_res (a : ℕ) (ω : Γ(Scheme.Hom.relativeDifferentialForms
      (coordinateBlowupToBase R m n) (a : ℤ), (tupleOpen R m n x).1)) :
    punctCoord R m n hn a ((Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n)
        (a : ℤ)).presheaf.map (homOfLE (punctured_le_tupleOpen R m n hn x)).op ω) =
      frameCoord R a (formsFrame (tuplePhi R m n x) (tupleLam R m n hn x)
        (tupleLam_tuplePhi R m n hn x) a ((tupleIso R m n x a).hom ω)) := by
  induction ω using FormsGenerators.induction_on_affine (coordinateBlowupToBase R m n)
    (isAffineOpen_tupleOpen R m n x) (isAffineOpen_top _) le_top with
  | h0 => simp
  | hadd ω ω' h h' => simp only [map_add, h, h']
  | hgen c g =>
    exact (punctCoord_res_smul_gen R m n hn (punctured_le_tupleOpen R m n hn x) a c g).trans
      (congrArg (frameCoord R a) (FormsGenerators.formsFrame_formsSectionsIso_smul_gen
        (coordinateBlowupToBase R m n) (isAffineOpen_tupleOpen R m n x) (isAffineOpen_top _) le_top
        (tupleLam R m n hn x) (tupleLam_tuplePhi R m n hn x) c g).symm)

/-- **The frame coordinates of a form over an intersection of charts are allowed.** -/
theorem frameAllowed_punctCoord_res (a : ℕ) (ω : Γ(Scheme.Hom.relativeDifferentialForms
      (coordinateBlowupToBase R m n) (a : ℤ), (tupleOpen R m n x).1))
    (e : FrameIndex m n a)
    (he : e ∈ (punctCoord R m n hn a ((Scheme.Hom.relativeDifferentialForms
      (coordinateBlowupToBase R m n) (a : ℤ)).presheaf.map
        (homOfLE (punctured_le_tupleOpen R m n hn x)).op ω)).support) :
    FrameAllowed (Set.range (ULift.up.{u} ∘ x)) e := by
  rw [punctCoord_res] at he
  exact frameAllowed_formsFrame _ _ _ _ (isChartLaurent_lamOf_tupleOpen R m n hn x) _ e he

/-! #### The exceptional divisor over an intersection of charts -/

/-- The preimage in `E` of an intersection of charts is an affine open. -/
theorem isAffineOpen_exceptionalTuple :
    IsAffineOpen ((coordinateExceptionalι R m n) ⁻¹ᵁ (tupleOpen R m n x).1) :=
  (isAffineOpen_tupleOpen R m n x).preimage _

/-- The structure ring map of the forms of `E` over an intersection of charts. -/
abbrev exceptionalPhi : Γ(coordinateBase R, ⊤) ⟶ Γ(coordinateExceptionalScheme R m n,
    (coordinateExceptionalι R m n) ⁻¹ᵁ (tupleOpen R m n x).1) :=
  (coordinateExceptionalι R m n ≫ coordinateBlowupToBase R m n).appLE ⊤ _ le_top

/-- Pulling a function back from the base to `E` over an intersection of charts is pulling it
back to `L` and restricting to `E`. -/
theorem exceptionalPhi_eq (r : Γ(coordinateBase R, ⊤)) :
    exceptionalPhi R m n x r =
      ((coordinateExceptionalι R m n).app (tupleOpen R m n x).1).hom (tuplePhi R m n x r) := by
  have h : (tuplePhi R m n x) ≫ (coordinateExceptionalι R m n).appLE (tupleOpen R m n x).1
      ((coordinateExceptionalι R m n) ⁻¹ᵁ (tupleOpen R m n x).1) le_rfl =
      exceptionalPhi R m n x :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  rw [Scheme.Hom.app_eq_appLE]
  exact (congrArg (fun φ ↦ φ.hom r) h).symm

/-- Each frame operator `frameOp s` vanishes on the Laurent polynomial of a function pulled back
from the base to `E` over an intersection of charts. -/
theorem exceptionalLam_exceptionalPhi (r : Γ(coordinateBase R, ⊤)) (s : Fin m ⊕ Fin n) :
    frameOp s (exceptionalChartLaurent R m n hn x (exceptionalPhi R m n x r)) = 0 := by
  rw [exceptionalPhi_eq, exceptionalChartLaurent_app]
  refine (congrArg (fun z ↦ frameOp s (wt0 R m n z))
    (lamOf_appLE_base R m n hn (punctured_le_tupleOpen R m n hn x) le_top r)).trans ?_
  rw [wt0_single]
  split_ifs
  · exact frameOp_single_zero s _
  · simp

/-- The identification of the forms of `E` over an intersection of charts. -/
abbrev exceptionalIso (a : ℕ) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso
    (coordinateExceptionalι R m n ≫ coordinateBlowupToBase R m n)
    (isAffineOpen_exceptionalTuple R m n x) (isAffineOpen_top _) le_top a

/-- The restriction of a form over an intersection of charts to the exceptional divisor. -/
def toExceptional (a : ℕ) (ω : Γ(Scheme.Hom.relativeDifferentialForms
      (coordinateBlowupToBase R m n) (a : ℤ), (tupleOpen R m n x).1)) :
    Γ(Scheme.Hom.relativeDifferentialForms
      (coordinateExceptionalι R m n ≫ coordinateBlowupToBase R m n) (a : ℤ),
        (coordinateExceptionalι R m n) ⁻¹ᵁ (tupleOpen R m n x).1) :=
  (Scheme.Hom.formsDirectImageComparison (coordinateExceptionalι R m n)
    (coordinateBlowupToBase R m n) (a : ℤ)).app (tupleOpen R m n x).1 ω

/-- Restriction of forms to `E` is additive. -/
theorem toExceptional_add (a : ℕ) (ω ω' : Γ(Scheme.Hom.relativeDifferentialForms
      (coordinateBlowupToBase R m n) (a : ℤ), (tupleOpen R m n x).1)) :
    toExceptional R m n x a (ω + ω') = toExceptional R m n x a ω + toExceptional R m n x a ω' :=
  map_add _ ω ω'

/-- The restriction to `E` of the generator `c • gen g` is the generator built from the
restrictions of `c` and of the `g i`. -/
theorem toExceptional_smul_gen (a : ℕ) (c : Γ(coordinateBlowup R m n, (tupleOpen R m n x).1))
    (g : Fin a → Γ(coordinateBlowup R m n, (tupleOpen R m n x).1)) :
    toExceptional R m n x a (c • FormsGenerators.gen _ _ g) =
      ((coordinateExceptionalι R m n).app (tupleOpen R m n x).1).hom c •
        FormsGenerators.gen (coordinateExceptionalι R m n ≫ coordinateBlowupToBase R m n) _
          fun i => ((coordinateExceptionalι R m n).app (tupleOpen R m n x).1).hom (g i) :=
  FormsGenerators.formsDirectImageComparison_app_smul_gen
    (coordinateBlowupToBase R m n) (coordinateExceptionalι R m n) (tupleOpen R m n x).1 c g

/-- The frame coordinates of the forms of `E` over an intersection of charts. -/
def exceptionalCoord (a : ℕ) :
    Γ(Scheme.Hom.relativeDifferentialForms
      (coordinateExceptionalι R m n ≫ coordinateBlowupToBase R m n) (a : ℤ),
        (coordinateExceptionalι R m n) ⁻¹ᵁ (tupleOpen R m n x).1) →+ (FrameIndex m n a →₀ R) where
  toFun ω := frameCoord R a (formsFrame (exceptionalPhi R m n x)
    (exceptionalChartLaurent R m n hn x) (exceptionalLam_exceptionalPhi R m n hn x) a
      ((exceptionalIso R m n x a).hom ω))
  map_zero' := by simp
  map_add' _ _ := by simp

/-- The frame coordinates of the forms over an intersection of charts. -/
def tupleFrameCoord (a : ℕ) :
    Γ(Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n) (a : ℤ),
      (tupleOpen R m n x).1) →+ (FrameIndex m n a →₀ R) where
  toFun ω := frameCoord R a (formsFrame (tuplePhi R m n x) (tupleLam R m n hn x)
        (tupleLam_tuplePhi R m n hn x) a ((tupleIso R m n x a).hom ω))
  map_zero' := by simp
  map_add' _ _ := by simp

/-- **Restriction of forms to `E`, in frame coordinates, is the weight-zero part.** -/
theorem exceptionalCoord_toExceptional (a : ℕ) (ω : Γ(Scheme.Hom.relativeDifferentialForms
      (coordinateBlowupToBase R m n) (a : ℤ), (tupleOpen R m n x).1)) :
    exceptionalCoord R m n hn x a (toExceptional R m n x a ω) =
      (tupleFrameCoord R m n hn x a ω).filter (fun e => yDegree m n e.2 = 0) := by
  induction ω using FormsGenerators.induction_on_affine (coordinateBlowupToBase R m n)
    (isAffineOpen_tupleOpen R m n x) (isAffineOpen_top _) le_top with
  | h0 => rw [show toExceptional R m n x a 0 = 0 from map_zero _, map_zero, map_zero,
      Finsupp.filter_zero]
  | hadd ω ω' h h' => rw [toExceptional_add, map_add, map_add, h, h', Finsupp.filter_add]
  | hgen c g =>
    have h2 := FormsGenerators.formsFrame_formsSectionsIso_smul_gen
      (coordinateExceptionalι R m n ≫ coordinateBlowupToBase R m n)
      (isAffineOpen_exceptionalTuple R m n x) (isAffineOpen_top _) le_top
      (exceptionalChartLaurent R m n hn x) (exceptionalLam_exceptionalPhi R m n hn x)
      (((coordinateExceptionalι R m n).app (tupleOpen R m n x).1).hom c)
      (fun i ↦ ((coordinateExceptionalι R m n).app (tupleOpen R m n x).1).hom (g i))
    have h3 := FormsGenerators.formsFrame_formsSectionsIso_smul_gen
      (coordinateBlowupToBase R m n) (isAffineOpen_tupleOpen R m n x) (isAffineOpen_top _) le_top
      (tupleLam R m n hn x) (tupleLam_tuplePhi R m n hn x) c g
    have h4 := frameCoord_filter_wt0 (tupleLam R m n hn x c) (fun i ↦ tupleLam R m n hn x (g i))
      (nonnegW_laurent_toFracOf_tupleOpen R m n hn x c)
      (fun i ↦ nonnegW_laurent_toFracOf_tupleOpen R m n hn x (g i))
    dsimp only [exceptionalCoord, tupleFrameCoord, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    have h5 : ∀ z, exceptionalChartLaurent R m n hn x
        (((coordinateExceptionalι R m n).app (tupleOpen R m n x).1).hom z) =
          wt0 R m n (tupleLam R m n hn x z) := fun z ↦ exceptionalChartLaurent_app R m n hn x z
    rw [toExceptional_smul_gen, h2, h3, h4]
    simp only [h5]

/-- The frame coordinates over `W₀` of the restriction of a form over an intersection of charts
are its frame coordinates `tupleFrameCoord`. -/
theorem punctCoord_res_eq (a : ℕ) (ω : Γ(Scheme.Hom.relativeDifferentialForms
      (coordinateBlowupToBase R m n) (a : ℤ), (tupleOpen R m n x).1)) :
    punctCoord R m n hn a ((Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n)
        (a : ℤ)).presheaf.map (homOfLE (punctured_le_tupleOpen R m n hn x)).op ω) =
      tupleFrameCoord R m n hn x a ω :=
  punctCoord_res R m n hn x a ω

/-- The generator `tupleGen` vanishes on `E`. -/
theorem exceptionalι_app_tupleGen :
    ((coordinateExceptionalι R m n).app (tupleOpen R m n x).1).hom (tupleGen R m n x) = 0 := by
  change tupleGen R m n x ∈ RingHom.ker
    ((coordinateExceptional R m n).subschemeι.app (tupleOpen R m n x)).hom
  rw [(coordinateExceptional R m n).ker_subschemeι_app (tupleOpen R m n x), ideal_tupleOpen]
  exact Ideal.mem_span_singleton_self _

/-- The generator `tupleGen` reads as the Laurent monomial of exponent `yExp (x 0)`. -/
theorem tupleLam_tupleGen :
    tupleLam R m n hn x (tupleGen R m n x) = single (yExp m n (x 0)) 1 := by
  rw [tupleGen_eq, lamOf_tupleFn, polyLaurent_coord]

/-- **A generator vanishing along `E` restricts to zero on `E`.** -/
theorem toExceptional_eq_zero (a : ℕ) (c : Γ(coordinateBlowup R m n, (tupleOpen R m n x).1))
    (g : Fin a → Γ(coordinateBlowup R m n, (tupleOpen R m n x).1))
    (h : (∃ c', c = tupleGen R m n x * c') ∨ ∃ i, g i = tupleGen R m n x) :
    toExceptional R m n x a (c • FormsGenerators.gen _ _ g) = 0 := by
  rw [toExceptional_smul_gen]
  rcases h with ⟨c', rfl⟩ | ⟨i, hi⟩
  · rw [map_mul, exceptionalι_app_tupleGen, zero_mul, zero_smul]
  · have hgen := FormsGenerators.gen_eq_zero
      (coordinateExceptionalι R m n ≫ coordinateBlowupToBase R m n)
      (isAffineOpen_exceptionalTuple R m n x) (isAffineOpen_top _) le_top
      (fun i => ((coordinateExceptionalι R m n).app (tupleOpen R m n x).1).hom (g i)) i
      (by rw [hi]; exact exceptionalι_app_tupleGen R m n x)
    rw [hgen, smul_zero]

end Tuple

/-! ### The sheaf of forms vanishing on `E` -/

variable (a : ℕ)

/-- **The sheaf `K = ker(Ω^a_{L/S} ⟶ j_*Ω^a_{E/S})` of `a`-forms vanishing on `E`.** -/
def formsKer : (coordinateBlowup R m n).Modules :=
  CategoryTheory.Limits.kernel (Scheme.Hom.formsDirectImageComparison
    (coordinateExceptionalι R m n) (coordinateBlowupToBase R m n) (a : ℤ))

/-- The inclusion `K ⟶ Ω^a_{L/S}`. -/
def formsKerι : formsKer R m n a ⟶
    Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n) (a : ℤ) :=
  CategoryTheory.Limits.kernel.ι (Scheme.Hom.formsDirectImageComparison
    (coordinateExceptionalι R m n) (coordinateBlowupToBase R m n) (a : ℤ))

/-- The sheaf `K` of forms vanishing on `E` is quasi-coherent. -/
instance isQuasicoherent_formsKer : (formsKer R m n a).IsQuasicoherent := by
  unfold formsKer
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (coordinateBlowupToBase R m n) a
  have := AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward
    (coordinateExceptionalι R m n)
    (Scheme.Hom.relativeDifferentialForms
      (coordinateExceptionalι R m n ≫ coordinateBlowupToBase R m n) (a : ℤ))
    (Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ a)
  infer_instance

/-- The frame coordinates of a section of `K` over `W₀`. -/
def kerVal : Γ(formsKer R m n a, punctured R m n) →+ (FrameIndex m n a →₀ R) where
  toFun t := punctCoord R m n hn a ((formsKerι R m n a).app (punctured R m n) t)
  map_zero' := by rw [map_zero, map_zero]
  map_add' t t' := by rw [map_add, map_add]

/-- The form underlying a section of `K` restricts to zero on `E`. -/
theorem formsKerι_app_eq_zero (U : (coordinateBlowup R m n).Opens) (s : Γ(formsKer R m n a, U)) :
    (Scheme.Hom.formsDirectImageComparison (coordinateExceptionalι R m n)
      (coordinateBlowupToBase R m n) (a : ℤ)).app U ((formsKerι R m n a).app U s) = 0 := by
  unfold formsKerι formsKer at *
  exact app_kernel_ι_app _ _ s

/-- On sections, the inclusion `K ⟶ Ω^a_{L/S}` is the kernel inclusion. -/
theorem formsKerι_app (U : (coordinateBlowup R m n).Opens) (s : Γ(formsKer R m n a, U)) :
    (formsKerι R m n a).app U s = (CategoryTheory.Limits.kernel.ι
      (Scheme.Hom.formsDirectImageComparison (coordinateExceptionalι R m n)
        (coordinateBlowupToBase R m n) (a : ℤ))).app U s := rfl

/-- A section of `K` over `W₀` is determined by its frame coordinates. -/
theorem kerVal_injective : Function.Injective (kerVal R m n hn a) :=
  show Function.Injective fun t ↦ punctCoord R m n hn a
    ((formsKerι R m n a).app (punctured R m n) t) from (punctCoord_injective R m n hn a).comp
    (Stacks.Algebraization.kernel_ι_app_injective (Scheme.Hom.formsDirectImageComparison
      (coordinateExceptionalι R m n) (coordinateBlowupToBase R m n) (a : ℤ)) (punctured R m n))

/-- The allowed frame coordinates of the forms vanishing on `E`: nonnegative in the `x`'s and of
positive degree in the `y`'s. -/
def kerOk : Set (FrameIndex m n a) := {e | (∀ l, 0 ≤ e.2 (Sum.inl l)) ∧ 1 ≤ yDegree m n e.2}

/-- For an allowed frame index `e ∈ kerOk`, some chart index lies outside `frameNeed e`. -/
theorem exists_not_mem_frameNeed (e : FrameIndex m n a) (he : e ∈ kerOk m n a) :
    ∃ k, k ∉ frameNeed.{u} e := by
  by_contra h
  push Not at h
  have hneg : ∀ k : Fin n, e.2 (Sum.inr k) ≤ 0 := fun k ↦ by
    have := h ⟨k⟩
    simp only [frameNeed, Set.mem_ofPred_eq] at this
    omega
  have hsum : yDegree m n e.2 ≤ ∑ _k : Fin n, (0 : ℤ) := Finset.sum_le_sum fun k _ ↦ hneg k
  simp only [Finset.sum_const_zero] at hsum
  have := he.2
  omega

section TupleKer

variable {p : ℕ} (x : Fin (p + 1) → Fin n)

/-- Restriction of sections of `K` to `W₀`. -/
def kerRes :
    Γ(formsKer R m n a, (tupleOpen R m n x).1) →+ Γ(formsKer R m n a, punctured R m n) where
  toFun s := (formsKer R m n a).presheaf.map (homOfLE (punctured_le_tupleOpen R m n hn x)).op s
  map_zero' := map_zero _
  map_add' := map_add _

/-- The frame coordinates of a section of `K` over `W₀` are those of its underlying form. -/
theorem kerVal_apply (t : Γ(formsKer R m n a, punctured R m n)) :
    kerVal R m n hn a t = punctCoord R m n hn a ((formsKerι R m n a).app (punctured R m n) t) :=
  rfl

/-- The inclusion `K ⟶ Ω^a_{L/S}` commutes with restriction to `W₀`. -/
theorem formsKerι_res (s : Γ(formsKer R m n a, (tupleOpen R m n x).1)) :
    (formsKerι R m n a).app (punctured R m n) (kerRes R m n hn a x s) =
      (Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n) (a : ℤ)).presheaf.map
        (homOfLE (punctured_le_tupleOpen R m n hn x)).op
          ((formsKerι R m n a).app (tupleOpen R m n x).1 s) := by
  have h := ConcreteCategory.congr_hom ((formsKerι R m n a).mapPresheaf.naturality
    (homOfLE (punctured_le_tupleOpen R m n hn x)).op) s
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h

/-- The frame coordinates over `W₀` of the restriction of a section of `K` over an intersection
of charts are the frame coordinates `tupleFrameCoord` of its underlying form. -/
theorem kerVal_kerRes (s : Γ(formsKer R m n a, (tupleOpen R m n x).1)) :
    kerVal R m n hn a (kerRes R m n hn a x s) =
      tupleFrameCoord R m n hn x a ((formsKerι R m n a).app (tupleOpen R m n x).1 s) := by
  rw [kerVal_apply, formsKerι_res, punctCoord_res_eq]

/-- **The frame coordinates of a section of `K` over an intersection of charts are supported.** -/
theorem kerVal_kerRes_mem (s : Γ(formsKer R m n a, (tupleOpen R m n x).1)) :
    kerVal R m n hn a (kerRes R m n hn a x s) ∈
      Stacks.CechFinsupp.supported (kerOk m n a) frameNeed (Set.range (ULift.up.{u} ∘ x)) := by
  rw [Stacks.CechFinsupp.mem_supported]
  intro e he
  have he' : e ∈ (punctCoord R m n hn a ((Scheme.Hom.relativeDifferentialForms
      (coordinateBlowupToBase R m n) (a : ℤ)).presheaf.map
        (homOfLE (punctured_le_tupleOpen R m n hn x)).op
          ((formsKerι R m n a).app (tupleOpen R m n x).1 s))).support := by
    rwa [punctCoord_res_eq, ← kerVal_kerRes]
  have hall := frameAllowed_punctCoord_res R m n hn x a
    ((formsKerι R m n a).app (tupleOpen R m n x).1 s) e he'
  refine ⟨⟨hall.1, ?_⟩, hall.2.2⟩
  by_contra hdeg
  have h0 : yDegree m n e.2 = 0 := by have := hall.2.1; omega
  have hzero : toExceptional R m n x a ((formsKerι R m n a).app (tupleOpen R m n x).1 s) = 0 :=
    formsKerι_app_eq_zero R m n a _ s
  have h1 : (tupleFrameCoord R m n hn x a ((formsKerι R m n a).app (tupleOpen R m n x).1 s)).filter
      (fun e ↦ yDegree m n e.2 = 0) = 0 := by
    rw [← exceptionalCoord_toExceptional, hzero, map_zero]
  have h2 :
      tupleFrameCoord R m n hn x a ((formsKerι R m n a).app (tupleOpen R m n x).1 s) e = 0 := by
    rw [← Finsupp.filter_apply_pos (fun e : FrameIndex m n a ↦ yDegree m n e.2 = 0) _ h0, h1,
      Finsupp.zero_apply]
  rw [kerVal_kerRes, Finsupp.mem_support_iff] at he
  exact he h2

/-- **Every supported function is the frame coordinates of a section of `K`.** -/
theorem exists_kerVal_kerRes_eq (gf : FrameIndex m n a →₀ R)
    (hg : gf ∈ Stacks.CechFinsupp.supported (kerOk m n a) frameNeed
      (Set.range (ULift.up.{u} ∘ x))) :
    ∃ s : Γ(formsKer R m n a, (tupleOpen R m n x).1),
      kerVal R m n hn a (kerRes R m n hn a x s) = gf := by
  classical
  set G := ((kerVal R m n hn a).comp (kerRes R m n hn a x)).range
  suffices gf ∈ G by obtain ⟨s, hs⟩ := this; exact ⟨s, hs⟩
  rw [← Finsupp.sum_single gf]
  refine AddSubgroup.sum_mem G fun e he ↦ ?_
  obtain ⟨⟨he1, he2⟩, he3⟩ := Stacks.CechFinsupp.mem_supported.1 hg e he
  have hk : (⟨x 0⟩ : ULift.{u} (Fin n)) ∈ Set.range (ULift.up ∘ x) := ⟨0, rfl⟩
  refine single_mem_of_generators _ hk G ?_ e he1 he2 he3 _
  intro c g hc hgc hvan
  obtain ⟨cz, hcz⟩ := exists_lamOf_tupleOpen_eq R m n hn x c hc
  choose gz hgz using fun i ↦ exists_lamOf_tupleOpen_eq R m n hn x (g i) (hgc i)
  have hinj := injective_lamOf_tupleOpen R m n hn x
  have hvan' : (∃ c', cz = tupleGen R m n x * c') ∨ ∃ i, gz i = tupleGen R m n x := by
    rcases hvan with ⟨c', hc', rfl⟩ | ⟨i, hi⟩
    · obtain ⟨c'', hc''⟩ := exists_lamOf_tupleOpen_eq R m n hn x c' hc'
      refine Or.inl ⟨c'', hinj ?_⟩
      rw [hcz, map_mul, hc'', tupleLam_tupleGen]
    · exact Or.inr ⟨i, hinj (by rw [hgz, hi, tupleLam_tupleGen])⟩
  obtain ⟨s0, hs0⟩ := Stacks.Algebraization.exists_kernel_section
    (Scheme.Hom.formsDirectImageComparison
      (coordinateExceptionalι R m n) (coordinateBlowupToBase R m n) (a : ℤ)) (tupleOpen R m n x).1
    (cz • FormsGenerators.gen (coordinateBlowupToBase R m n) _ gz)
    (toExceptional_eq_zero R m n x a cz gz hvan')
  let s : Γ(formsKer R m n a, (tupleOpen R m n x).1) := s0
  have hs : (formsKerι R m n a).app (tupleOpen R m n x).1 s =
      cz • FormsGenerators.gen (coordinateBlowupToBase R m n) _ gz := hs0
  refine ⟨s, ?_⟩
  change kerVal R m n hn a (kerRes R m n hn a x s) = _
  rw [kerVal_kerRes, hs, ← punctCoord_res_eq, punctCoord_res_smul_gen]
  simp only [hcz, hgz]

end TupleKer

/-! ### A Čech criterion phrased on sections of the module -/

section CechCriterion

open Stacks.CategoryTheory.CechComplex Stacks.Cohomology.CechSheaf
open Stacks.Cohomology.Basis (res)

variable {Y : Scheme.{u}} (M : Y.Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
  (U : ι → Y.Opens) (hU : (⊤ : Y.Opens) = ⨆ i, U i)
  (haff : ∀ (r : ℕ) (x : Fin (r + 1) → ι), IsAffineOpen (⨅ k, U (x k)))
  {W : Y.Opens} (hW : ∀ i, W ≤ U i)
  {E R' : Type*} [AddCommGroup R'] (val : Γ(M, W) →+ (E →₀ R')) (hval : Function.Injective val)
  {ok : Set E} {N : E → Set ι} (hok : ∀ e ∈ ok, ∃ k, k ∉ N e)

include hU haff hval hok in
/-- **Vanishing of the higher cohomology of a quasi-coherent module from a combinatorial
description of its sections over the intersections of a cover.** Suppose an open `W` lies in every
member of a cover with affine intersections, restriction to `W` is injective, and an injective
additive map `val` on the sections over `W` identifies the restrictions of the sections over the
intersection selected by a tuple `x` with the functions supported on the range of `x`, every
allowed weight leaving out an index. Then the higher cohomology of `M` vanishes. -/
theorem isZero_rightDerived_of_supported
    (hinj : ∀ (r : ℕ) (x : Fin (r + 1) → ι),
      Function.Injective (M.presheaf.map (homOfLE (le_inter_of_forall_le U hW x)).op))
    (hmem : ∀ (r : ℕ) (x : Fin (r + 1) → ι) (s : Γ(M, inter U x)),
      val (M.presheaf.map (homOfLE (le_inter_of_forall_le U hW x)).op s) ∈
        Stacks.CechFinsupp.supported ok N (Set.range x))
    (hreal : ∀ (r : ℕ) (x : Fin (r + 1) → ι) (g : E →₀ R'),
      g ∈ Stacks.CechFinsupp.supported ok N (Set.range x) →
        ∃ s : Γ(M, inter U x),
          val (M.presheaf.map (homOfLE (le_inter_of_forall_le U hW x)).op s) = g)
    (q : ℕ) (hq : 0 < q) :
    CategoryTheory.Limits.IsZero
      (((Stacks.Cohomology.sectionsFunctor Y ⊤).rightDerived q).obj M) := by
  classical
  refine (Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived Y ⊤ U hU
    (fun r x ↦ haff r x) M q).isZero_iff.2 ?_
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  let valAb : ToType ((abSections M).obj (op W)) →+ (E →₀ R') := val
  refine isZero_cechComplex_homology_of_res_injective ⊤ U hU M hW p
    (fun r x ↦ hinj r x) fun c hc hcoc ↦ ?_
  have hΦ : ∀ y, valAb (c y) ∈ Stacks.CechFinsupp.supported ok N (Set.range y) := fun y ↦ by
    obtain ⟨s, hs⟩ := hc y
    rw [← hs]
    exact hmem _ y s
  have hΦcoc : ∀ z, Stacks.CechFinsupp.cechCoboundary (fun y ↦ valAb (c y)) z = 0 := fun z ↦ by
    have := congrArg valAb (hcoc z)
    rw [map_zero, Stacks.CechFinsupp.cechCoboundary, map_sum] at this
    simp only [map_zsmul] at this
    exact this
  obtain ⟨b', hb', hb'c⟩ := Stacks.CechFinsupp.exists_cechCoboundary_eq hok _ hΦ hΦcoc
  choose s hs using fun x ↦ hreal _ x (b' x) (hb' x)
  refine ⟨fun x ↦ res (abSections M) (le_inter_of_forall_le U hW x) (s x),
    fun x ↦ ⟨s x, rfl⟩, fun x ↦ hval ?_⟩
  change valAb _ = valAb _
  rw [Stacks.CechFinsupp.cechCoboundary, map_sum]
  simp only [map_zsmul]
  refine (Finset.sum_congr rfl fun a _ ↦ ?_).trans (hb'c x)
  rw [← hs]
  rfl

omit [M.IsQuasicoherent] [Finite ι] in
/-- Restricting a section of `M` twice is restricting it once. -/
theorem presheaf_map_map {V V' V'' : Y.Opens} (h1 : V ≤ V') (h2 : V' ≤ V'') (s : Γ(M, V'')) :
    M.presheaf.map (homOfLE h1).op (M.presheaf.map (homOfLE h2).op s) =
      M.presheaf.map (homOfLE (h1.trans h2)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

omit [M.IsQuasicoherent] [Finite ι] in
/-- Restricting a section of `M` from `V` to `V` is the identity. -/
theorem presheaf_map_refl {V : Y.Opens} (h : V ≤ V) (s : Γ(M, V)) :
    M.presheaf.map (homOfLE h).op s = s := by
  rw [show (homOfLE h).op = 𝟙 (op V) from rfl, M.presheaf.map_id (op V)]
  rfl

end CechCriterion

/-! ### The higher cohomology of `K` -/

section KerCech

open Stacks.CategoryTheory.CechComplex Stacks.Cohomology.CechSheaf

variable (hn : 0 < n) (a : ℕ)

/-- Restriction of sections of `K` from an intersection of charts to `W₀` is injective. -/
theorem kerRes_injective {p : ℕ} (x : Fin (p + 1) → Fin n) :
    Function.Injective (kerRes R m n hn a x) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs ↦ ?_
  have h1 := formsKerι_res R m n hn a x s
  rw [hs, map_zero] at h1
  have h2 := res_punctured_forms_injective R m n hn x a (h1.symm.trans (map_zero _).symm)
  exact Stacks.Algebraization.kernel_ι_app_injective (Scheme.Hom.formsDirectImageComparison
    (coordinateExceptionalι R m n) (coordinateBlowupToBase R m n) (a : ℤ)) _
    (h2.trans (map_zero _).symm)

include hn in
/-- **The higher cohomology of the sheaf `K` of forms vanishing on `E` vanishes.** -/
theorem isZero_rightDerived_formsKer (q : ℕ) (hq : 0 < q) :
    CategoryTheory.Limits.IsZero
      (((Stacks.Cohomology.sectionsFunctor (coordinateBlowup R m n) ⊤).rightDerived q).obj
        (formsKer R m n a)) := by
  set M := formsKer R m n a
  have key : ∀ (r : ℕ) (x : Fin (r + 1) → ULift.{u} (Fin n)) (s : Γ(M, inter (chartCover R m n) x)),
      M.presheaf.map (homOfLE (le_inter_of_forall_le (chartCover R m n)
        (punctured_le_chartCover R m n hn) x)).op s =
      kerRes R m n hn a (fun i ↦ (x i).down)
        (M.presheaf.map (homOfLE (inter_chartCover R m n x).ge).op s) := fun r x s ↦
    (presheaf_map_map M _ _ s).symm
  refine isZero_rightDerived_of_supported M (chartCover R m n) (iSup_chartCover R m n hn)
    (fun r x ↦ isAffineOpen_iInf_chart R m n (fun k ↦ (x k).down))
    (punctured_le_chartCover R m n hn) (kerVal R m n hn a) (kerVal_injective R m n hn a)
    (fun e he ↦ exists_not_mem_frameNeed m n a e he) ?_ ?_ ?_ q hq
  · intro r x s s' hss'
    rw [key, key] at hss'
    have h := congrArg (M.presheaf.map (homOfLE (inter_chartCover R m n x).le).op)
      (kerRes_injective R m n hn a _ hss')
    rwa [presheaf_map_map, presheaf_map_map, presheaf_map_refl, presheaf_map_refl] at h
  · intro r x s
    rw [key, ← range_up_down]
    exact kerVal_kerRes_mem R m n hn a _ _
  · intro r x g hg
    rw [← range_up_down] at hg
    obtain ⟨t, ht⟩ := exists_kerVal_kerRes_eq R m n hn a _ g hg
    refine ⟨M.presheaf.map (homOfLE (inter_chartCover R m n x).le).op t, ?_⟩
    rwa [key, presheaf_map_map, presheaf_map_refl]

end KerCech

end Stacks.DeRham.CoordinateCech
