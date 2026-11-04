module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.CategoryTheory.Sites.Hypercover.ZeroFamily
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLinePoints

/-!
# An affine open of the projective line containing both `0` and `∞`

The projective line is not affine, but it is covered by affine opens other than its two standard
charts. The complement `U = ℙ¹ \ {1}` of the point `1` is such an open, and it contains both
distinguished points `0` and `∞`.

The point `1` is the point `(x - 1)` of the first chart, and also the point `(y - 1)` of the
second chart. With `s = 1/(x - 1)` one has `x = (s+1)/s` and `y = s/(s+1)`, so `U ∩ X₁ = D(x-1)`
is `D(s) ⊂ Spec k[s]` and `U ∩ X₂ = D(y-1)` is `D(s+1)`. These glue to an open immersion
`Spec k[s] ⟶ ℙ¹` with image exactly `{1}ᶜ`, which exhibits `ℙ¹ \ {1}` as an affine open with
coordinate ring `k[s]`.

## Main definitions

* `AlgebraicGeometry.laurentEvalOne`: evaluation at `1` on `k[T, T⁻¹]`, and
  `AlgebraicGeometry.laurentOne` the point `T = 1` of the punctured affine line.
* `AlgebraicGeometry.affineLineOne`: the point `(X - 1)` of an affine-line chart.
* `AlgebraicGeometry.projectiveLineOne`: the point `1` of the projective line.
* `AlgebraicGeometry.affineLineAwayOne`: the coordinate ring `k[x][1/(x-1)]` of the complement of
  `1` in a chart, with `AlgebraicGeometry.affineLineSOnXChart` and
  `AlgebraicGeometry.affineLineSOnYChart` the coordinate `s` read on either chart, namely
  `1/(x-1)` and `y/(1-y)`.

## Main results

* `AlgebraicGeometry.projectiveLineYChart_affineLineOne`: **the point `(y - 1)` of the second
  chart is the point `1`**.
* `AlgebraicGeometry.affineLineAwayOneEquivX` and
  `AlgebraicGeometry.affineLineAwayOneEquivY`: **`k[x][1/(x-1)]` is the localization of `k[s]`
  away from `s`, and `k[y][1/(y-1)]` is its localization away from `s + 1`.** This is the
  algebraic content of `D(s) ∪ D(s+1) = Spec k[s]`, with
  `AlgebraicGeometry.range_comap_affineLineSOnXChart` and
  `AlgebraicGeometry.range_comap_affineLineSOnYChart` the corresponding images on spectra.
* `AlgebraicGeometry.projectiveLineSChart`: **the third chart `Spec k[s] ⟶ ℙ¹`**, an open
  immersion by `AlgebraicGeometry.projectiveLineSChart_base_injective`, with
  `AlgebraicGeometry.projectiveLineSXPiece_comp_projectiveLineSChart` and
  `AlgebraicGeometry.projectiveLineSYPiece_comp_projectiveLineSChart` its two defining equations,
  `s = 1/(x-1)` and `s = y/(1-y)`.
* `AlgebraicGeometry.range_projectiveLineSChart`: **its image is `{1}ᶜ`**, so
  `AlgebraicGeometry.isAffineOpen_projectiveLineSChart` says `ℙ¹ \ {1}` is an affine open; it
  contains `0` and `∞` by
  `AlgebraicGeometry.projectiveLineZero_mem_opensRange_projectiveLineSChart` and
  `AlgebraicGeometry.projectiveLineInfinity_mem_opensRange_projectiveLineSChart`, and
  `AlgebraicGeometry.projectiveLineSChartIso` identifies it with `Spec k[s]`, so that
  `AlgebraicGeometry.projectiveLineSChartSectionsIso` gives `Γ(U, O_U) = k[s]`.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Evaluation at `1` on the punctured affine line -/

section CommRing

/-- Two inverse elements of a commutative ring are equal. -/
private theorem eq_of_mul_eq_one_of_mul_eq_one {A : Type*} [CommRing A] {c a b : A}
    (h₁ : c * a = 1) (h₂ : c * b = 1) : a = b := by
  linear_combination b * h₁ - a * h₂

/-- A ring map sends an inverse of `a` to any inverse of the image of `a`. -/
private theorem map_eq_of_mul_eq_one {A B : Type*} [CommRing A] [CommRing B] (L : A →+* B)
    {i a : A} {u v : B} (h : i * a = 1) (hu : L a = u) (hv : u * v = 1) : L i = v :=
  eq_of_mul_eq_one_of_mul_eq_one (c := u) (by rw [← hu, ← map_mul, mul_comm, h, map_one]) hv

variable (k : Type u) [CommRing k]

/-- The inverse coordinate times the coordinate of the punctured line is `1`. -/
private theorem T_neg_one_mul_T_one :
    (LaurentPolynomial.T (-1) : LaurentPolynomial k) * LaurentPolynomial.T 1 = 1 := by
  rw [← LaurentPolynomial.T_add]
  simp

/-- Evaluation at `1` on the punctured affine line: the ring map `k[T, T⁻¹] ⟶ k` extending
evaluation at `1` on `k[X]`, which exists because `1` is a unit. -/
def laurentEvalOne : LaurentPolynomial k →+* k :=
  IsLocalization.lift (M := Submonoid.powers (Polynomial.X : Polynomial k))
    (g := Polynomial.evalRingHom (1 : k)) (by
      rintro ⟨y, n, rfl⟩
      simp)

/-- Evaluation at `1` on the punctured line extends evaluation at `1` on polynomials. -/
@[simp] theorem laurentEvalOne_toLaurent (p : Polynomial k) :
    laurentEvalOne k (Polynomial.toLaurent p) = p.eval 1 :=
  IsLocalization.lift_eq (M := Submonoid.powers (Polynomial.X : Polynomial k)) _ p

/-- Evaluation at `1` is the identity on constants. -/
@[simp] theorem laurentEvalOne_C (a : k) : laurentEvalOne k (LaurentPolynomial.C a) = a := by
  rw [← Polynomial.toLaurent_C, laurentEvalOne_toLaurent]
  simp

/-- Evaluation at `1` sends the coordinate of the punctured line to `1`. -/
@[simp] theorem laurentEvalOne_T_one :
    laurentEvalOne k (LaurentPolynomial.T 1) = 1 := by
  rw [← Polynomial.toLaurent_X, laurentEvalOne_toLaurent]
  simp

/-- Evaluation at `1` sends the inverse coordinate of the punctured line to `1`. -/
@[simp] theorem laurentEvalOne_T_neg_one :
    laurentEvalOne k (LaurentPolynomial.T (-1)) = 1 := by
  exact map_eq_of_mul_eq_one _ (T_neg_one_mul_T_one k) (laurentEvalOne_T_one k) (one_mul 1)

/-- Evaluation at `1` on the punctured line restricts along the first coordinate to evaluation at
`1` on the affine line. -/
theorem laurentEvalOne_comp_toLaurent :
    (laurentEvalOne k).comp (Polynomial.toLaurent (R := k)) = Polynomial.evalRingHom 1 :=
  RingHom.ext fun p ↦ laurentEvalOne_toLaurent k p

/-- Evaluation at `1` on the punctured line restricts along the second coordinate `y ↦ T⁻¹` to
evaluation at `1` on the affine line: this is the statement that `1/1 = 1`. -/
theorem laurentEvalOne_comp_overlapInverseCoordinate :
    (laurentEvalOne k).comp (projectiveLineOverlapInverseCoordinate k).toRingHom =
      Polynomial.evalRingHom 1 := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [projectiveLineOverlapInverseCoordinate]
  · simp [projectiveLineOverlapInverseCoordinate]

end CommRing

/-! ### The point `1` -/

section Domain

variable (k : Type u) [CommRing k] [IsDomain k]

/-- The point `T = 1` of the punctured affine line, represented by the kernel of evaluation at
`1`. -/
def laurentOne : Spec (.of (LaurentPolynomial k)) :=
  PrimeSpectrum.comap (laurentEvalOne k) ⟨⊥, Ideal.isPrime_bot⟩

/-- Every coordinate on the punctured line that restricts to evaluation at `1` on the affine line
carries the point `T = 1` to the point `(X - 1)`. -/
theorem comap_laurentOne_of_comp_eq (f : Polynomial k →+* LaurentPolynomial k)
    (hf : (laurentEvalOne k).comp f = Polynomial.evalRingHom 1) :
    (PrimeSpectrum.comap f (laurentOne k)).asIdeal =
      Ideal.span {(Polynomial.X - 1 : Polynomial k)} := by
  show Ideal.comap f (Ideal.comap (laurentEvalOne k) (⊥ : Ideal k)) = _
  rw [Ideal.comap_comap, hf, ← RingHom.ker_eq_comap_bot, Polynomial.ker_evalRingHom]
  simp

/-- The point `1` of an affine-line chart, represented by the prime ideal `(X - 1)`. -/
@[stacks 01JE "projective_line_one"]
def affineLineOne : Spec (.of (Polynomial k)) :=
  ⟨Ideal.span {(Polynomial.X - 1 : Polynomial k)},
    (Ideal.span_singleton_prime (by simpa using Polynomial.X_sub_C_ne_zero (1 : k))).2
      (by simpa using Polynomial.prime_X_sub_C (1 : k))⟩

/-- The coordinate of the first chart carries the point `T = 1` of the punctured line to the point
`(x - 1)`. -/
theorem projectiveLinePuncturedChart_base_laurentOne :
    (projectiveLinePuncturedChart k).base (laurentOne k) = affineLineOne k :=
  PrimeSpectrum.ext
    (comap_laurentOne_of_comp_eq k _ (laurentEvalOne_comp_toLaurent k))

/-- The coordinate of the second chart carries the point `T = 1` of the punctured line to the
point `(y - 1)`. -/
theorem projectiveLineOverlapInverseCoordinate_base_laurentOne :
    (Spec.map (CommRingCat.ofHom
        (projectiveLineOverlapInverseCoordinate k).toRingHom)).base (laurentOne k) =
      affineLineOne k :=
  PrimeSpectrum.ext
    (comap_laurentOne_of_comp_eq k _ (laurentEvalOne_comp_overlapInverseCoordinate k))

/-- The point `1` of the projective line, namely the point `(x - 1)` in the `x`-chart. -/
@[stacks 01JE "projective_line_one"]
def projectiveLineOne : projectiveLine k :=
  projectiveLineXChart k (affineLineOne k)

/-- The point `1` is *also* the point `(y - 1)` of the second chart. -/
@[stacks 01JE "projective_line_one"]
theorem projectiveLineYChart_affineLineOne :
    projectiveLineYChart k (affineLineOne k) = projectiveLineOne k :=
  ((projectiveLineXChart_base_eq_projectiveLineYChart_base_iff k (affineLineOne k)
    (affineLineOne k)).mpr ⟨laurentOne k,
      projectiveLinePuncturedChart_base_laurentOne k,
      projectiveLineOverlapInverseCoordinate_base_laurentOne k⟩).symm

end Domain

/-! ### The coordinate `s = 1/(x - 1) = y/(1 - y)`

The complement of the point `1` in a chart is `D(x - 1)`, with coordinate ring `k[x][1/(x-1)]`.
The source's coordinate `s` is `1/(x-1)` there, and that presents the same ring as the
localization of `k[s]` away from `s`; read in the other chart, `s` is `y/(1-y)`, which presents
it as the localization of `k[s]` away from `s + 1`. Those two presentations are the content of
`D(s) ∪ D(s+1) = Spec k[s]`.
-/

section Reparametrization

/-- The inverse of the image of the localization generator, written on the left. -/
private theorem invSelf_mul_algebraMap {R : Type u} [CommRing R] (p : R) (S : Type u) [CommRing S]
    [Algebra R S] [IsLocalization.Away p S] :
    IsLocalization.Away.invSelf p * algebraMap R S p = 1 := by
  rw [mul_comm]
  exact IsLocalization.Away.mul_invSelf _

/-- The inverse of `X - 1` times `X - 1`, in any localization away from `X - 1`. -/
private theorem invSelf_X_sub_one_mul (k : Type u) [CommRing k] (S : Type u) [CommRing S]
    [Algebra (Polynomial k) S] [IsLocalization.Away (Polynomial.X - 1 : Polynomial k) S] :
    IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k) *
      (algebraMap (Polynomial k) S Polynomial.X - 1) = 1 := by
  have h := invSelf_mul_algebraMap (Polynomial.X - 1 : Polynomial k) S
  rwa [map_sub, map_one] at h

/-- The inverse of `X + 1` times `X + 1`, in any localization away from `X + 1`. -/
private theorem invSelf_X_add_one_mul (k : Type u) [CommRing k] (S : Type u) [CommRing S]
    [Algebra (Polynomial k) S] [IsLocalization.Away (Polynomial.X + 1 : Polynomial k) S] :
    IsLocalization.Away.invSelf (Polynomial.X + 1 : Polynomial k) *
      (algebraMap (Polynomial k) S Polynomial.X + 1) = 1 := by
  have h := invSelf_mul_algebraMap (Polynomial.X + 1 : Polynomial k) S
  rwa [map_add, map_one] at h

/-- **Reparametrizing a localization of a polynomial ring.** Two localizations of `k[X]`, away
from `p` and from `q`, are isomorphic as soon as there are substitutions `X ↦ f`, `X ↦ g` into
each that invert the other generator and are mutually inverse on the coordinate. -/
def awayEquivOfSubst {k : Type u} [CommRing k] (p q : Polynomial k)
    (A B : Type u) [CommRing A] [CommRing B] [Algebra (Polynomial k) A] [Algebra (Polynomial k) B]
    [IsLocalization.Away p A] [IsLocalization.Away q B]
    {f : Polynomial k →+* B} {g : Polynomial k →+* A}
    (hf : IsUnit (f p)) (hg : IsUnit (g q))
    (hfg : (IsLocalization.Away.lift q hg).comp f = algebraMap (Polynomial k) A)
    (hgf : (IsLocalization.Away.lift p hf).comp g = algebraMap (Polynomial k) B) :
    A ≃+* B :=
  RingEquiv.ofRingHom (IsLocalization.Away.lift p hf) (IsLocalization.Away.lift q hg)
    (by
      refine IsLocalization.ringHom_ext (Submonoid.powers q) ?_
      rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, hgf, RingHom.id_comp])
    (by
      refine IsLocalization.ringHom_ext (Submonoid.powers p) ?_
      rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, hfg, RingHom.id_comp])

/-- The isomorphism `awayEquivOfSubst` composed with the localization map `k[X] ⟶ A` is the
substitution `f`. -/
theorem awayEquivOfSubst_comp {k : Type u} [CommRing k] (p q : Polynomial k)
    (A B : Type u) [CommRing A] [CommRing B] [Algebra (Polynomial k) A] [Algebra (Polynomial k) B]
    [IsLocalization.Away p A] [IsLocalization.Away q B]
    {f : Polynomial k →+* B} {g : Polynomial k →+* A}
    (hf : IsUnit (f p)) (hg : IsUnit (g q))
    (hfg : (IsLocalization.Away.lift q hg).comp f = algebraMap (Polynomial k) A)
    (hgf : (IsLocalization.Away.lift p hf).comp g = algebraMap (Polynomial k) B) :
    (awayEquivOfSubst p q A B hf hg hfg hgf : A →+* B).comp (algebraMap (Polynomial k) A) = f := by
  simp only [awayEquivOfSubst, RingEquiv.coe_ringHom_ofRingHom]
  exact IsLocalization.Away.lift_comp (x := p) hf

/-- A ring map that becomes the localization map after an isomorphism of the target has the same
image on prime spectra as that localization map. -/
theorem range_comap_of_equiv_comp {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] (e : A ≃+* B) {f : R →+* B} (hf : (e : A →+* B).comp (algebraMap R A) = f) :
    Set.range (PrimeSpectrum.comap f) = Set.range (PrimeSpectrum.comap (algebraMap R A)) := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap (e : A →+* B)) := by
    intro x
    refine ⟨PrimeSpectrum.comap (e.symm : B →+* A) x, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply,
      show ((e.symm : B →+* A).comp (e : A →+* B)) = RingHom.id A from by ext b; simp,
      PrimeSpectrum.comap_id]
  rw [← hf, PrimeSpectrum.comap_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]

/-- The image on spectra of a substitution `f` that presents a localization away from `q` as a
reparametrization of the one away from `p` is the basic open `D(p)`. -/
private theorem range_comap_eq_basicOpen_of_subst {k : Type u} [CommRing k] (p q : Polynomial k)
    (A B : Type u) [CommRing A] [CommRing B] [Algebra (Polynomial k) A] [Algebra (Polynomial k) B]
    [IsLocalization.Away p A] [IsLocalization.Away q B]
    {f : Polynomial k →+* B} {g : Polynomial k →+* A}
    (hf : IsUnit (f p)) (hg : IsUnit (g q))
    (hfg : (IsLocalization.Away.lift q hg).comp f = algebraMap (Polynomial k) A)
    (hgf : (IsLocalization.Away.lift p hf).comp g = algebraMap (Polynomial k) B) :
    Set.range (PrimeSpectrum.comap f) = (PrimeSpectrum.basicOpen p : Set _) := by
  rw [range_comap_of_equiv_comp (awayEquivOfSubst p q A B hf hg hfg hgf)
    (awayEquivOfSubst_comp p q A B hf hg hfg hgf)]
  exact PrimeSpectrum.localization_away_comap_range _ _

variable (k : Type u) [CommRing k]

/-- The coordinate ring `k[x][1/(x-1)]` of the complement of the point `1` in an affine-line
chart. -/
abbrev affineLineAwayOne : Type u := Localization.Away (Polynomial.X - 1 : Polynomial k)

/-- **The coordinate `s = 1/(x - 1)`.** The substitution presenting `k[x][1/(x-1)]` as an algebra
over the polynomial ring in the coordinate `s`, on the first chart. -/
def affineLineSOnXChart : Polynomial k →+* affineLineAwayOne k :=
  (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k)) :
    Polynomial k →ₐ[k] affineLineAwayOne k).toRingHom

/-- **The coordinate `s = y/(1 - y)`.** The substitution presenting `k[y][1/(y-1)]` as an algebra
over the polynomial ring in the coordinate `s`, on the second chart. -/
def affineLineSOnYChart : Polynomial k →+* affineLineAwayOne k :=
  (Polynomial.aeval (-(IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k)) - 1) :
    Polynomial k →ₐ[k] affineLineAwayOne k).toRingHom

/-- On the first chart, `s = 1/(x - 1)`. -/
@[simp] theorem affineLineSOnXChart_X :
    affineLineSOnXChart k Polynomial.X =
      IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k) := by
  simp [affineLineSOnXChart]

/-- On the second chart, `s = -1/(y - 1) - 1`. -/
@[simp] theorem affineLineSOnYChart_X :
    affineLineSOnYChart k Polynomial.X =
      -(IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k)) - 1 := by
  simp [affineLineSOnYChart]

/-- The substitution `affineLineSOnXChart` is the identity on constants. -/
theorem affineLineSOnXChart_C (a : k) :
    affineLineSOnXChart k (Polynomial.C a) =
      algebraMap (Polynomial k) (affineLineAwayOne k) (Polynomial.C a) := by
  simp [affineLineSOnXChart,
    IsScalarTower.algebraMap_apply k (Polynomial k) (affineLineAwayOne k)]

/-- The substitution `affineLineSOnYChart` is the identity on constants. -/
theorem affineLineSOnYChart_C (a : k) :
    affineLineSOnYChart k (Polynomial.C a) =
      algebraMap (Polynomial k) (affineLineAwayOne k) (Polynomial.C a) := by
  simp [affineLineSOnYChart,
    IsScalarTower.algebraMap_apply k (Polynomial k) (affineLineAwayOne k)]

/-- On the second chart, `s = y · (-1/(y - 1)) = y/(1 - y)`. -/
theorem affineLineSOnYChart_X' :
    affineLineSOnYChart k Polynomial.X =
      algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X *
        -(IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k)) := by
  rw [affineLineSOnYChart_X]
  linear_combination invSelf_X_sub_one_mul k (affineLineAwayOne k)

/-! #### The `x`-side: `k[x][1/(x-1)]` is `k[s][1/s]` -/

/-- The coordinate `s = 1/(x - 1)` is a unit of `k[x][1/(x-1)]`. -/
theorem isUnit_affineLineSOnXChart_X :
    IsUnit (affineLineSOnXChart k Polynomial.X) := by
  rw [affineLineSOnXChart_X]
  exact IsUnit.of_mul_eq_one
    (algebraMap (Polynomial k) (affineLineAwayOne k) (Polynomial.X - 1))
    (invSelf_mul_algebraMap _ _)

/-- The substitution `x = (s+1)/s` inverse to `s = 1/(x-1)`. -/
def xOnSChart : Polynomial k →+*
    Localization.Away (Polynomial.X : Polynomial k) :=
  (Polynomial.aeval (1 + IsLocalization.Away.invSelf (Polynomial.X : Polynomial k)) :
    Polynomial k →ₐ[k] Localization.Away (Polynomial.X : Polynomial k)).toRingHom

/-- Under `x = (s+1)/s`, one has `x - 1 = 1/s`. -/
theorem xOnSChart_X_sub_one :
    xOnSChart k (Polynomial.X - 1) =
      IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) := by
  simp [xOnSChart]

/-- Under `x = (s+1)/s`, the function `x - 1` is a unit of `k[s][1/s]`. -/
theorem isUnit_xOnSChart_X_sub_one : IsUnit (xOnSChart k (Polynomial.X - 1)) := by
  rw [xOnSChart_X_sub_one]
  exact IsUnit.of_mul_eq_one
    (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) Polynomial.X)
    (invSelf_mul_algebraMap _ _)

/-- Substituting `x = (s+1)/s` into `s = 1/(x-1)` gives back `s`. -/
theorem affineLineSOnXChart_hfg :
    (IsLocalization.Away.lift (S := affineLineAwayOne k) (Polynomial.X - 1 : Polynomial k)
        (isUnit_xOnSChart_X_sub_one k)).comp (affineLineSOnXChart k) =
      algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) := by
  refine Polynomial.ringHom_ext ?_ ?_
  · intro a
    rw [RingHom.comp_apply, affineLineSOnXChart_C, IsLocalization.Away.lift_eq]
    simp [xOnSChart,
      IsScalarTower.algebraMap_apply k (Polynomial k)
        (Localization.Away (Polynomial.X : Polynomial k))]
  · rw [RingHom.comp_apply, affineLineSOnXChart_X]
    exact map_eq_of_mul_eq_one _
      (invSelf_mul_algebraMap (Polynomial.X - 1 : Polynomial k) (affineLineAwayOne k))
      (by rw [IsLocalization.Away.lift_eq, xOnSChart_X_sub_one]) (invSelf_mul_algebraMap _ _)

/-- Substituting `s = 1/(x-1)` into `x = (s+1)/s` gives back `x`. -/
theorem affineLineSOnXChart_hgf :
    (IsLocalization.Away.lift (S := Localization.Away (Polynomial.X : Polynomial k))
        (Polynomial.X : Polynomial k) (isUnit_affineLineSOnXChart_X k)).comp (xOnSChart k) =
      algebraMap (Polynomial k) (affineLineAwayOne k) := by
  refine Polynomial.ringHom_ext ?_ ?_
  · intro a
    have h1 : xOnSChart k (Polynomial.C a) =
        algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))
          (Polynomial.C a) := by
      simp [xOnSChart, IsScalarTower.algebraMap_apply k (Polynomial k)
        (Localization.Away (Polynomial.X : Polynomial k))]
    rw [RingHom.comp_apply, h1, IsLocalization.Away.lift_eq, affineLineSOnXChart_C]
  · have hgX : xOnSChart k Polynomial.X =
        1 + IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) := by simp [xOnSChart]
    rw [RingHom.comp_apply, hgX, map_add, map_one]
    refine (congrArg (1 + ·) (map_eq_of_mul_eq_one _
      (invSelf_mul_algebraMap (Polynomial.X : Polynomial k) _)
      (by rw [IsLocalization.Away.lift_eq, affineLineSOnXChart_X])
      (invSelf_X_sub_one_mul k (affineLineAwayOne k)))).trans ?_
    ring

/-- **`k[x][1/(x-1)]` is the localization of `k[s]` away from `s`,** for `s = 1/(x-1)`. -/
def affineLineAwayOneEquivX :
    Localization.Away (Polynomial.X : Polynomial k) ≃+* affineLineAwayOne k :=
  awayEquivOfSubst Polynomial.X (Polynomial.X - 1) _ _
    (isUnit_affineLineSOnXChart_X k) (isUnit_xOnSChart_X_sub_one k)
    (affineLineSOnXChart_hfg k) (affineLineSOnXChart_hgf k)

/-- **The image of `D(x-1) ⊂ X₁` in `Spec k[s]` is `D(s)`.** -/
theorem range_comap_affineLineSOnXChart :
    Set.range (PrimeSpectrum.comap (affineLineSOnXChart k)) =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) : Set _) := by
  exact range_comap_eq_basicOpen_of_subst Polynomial.X (Polynomial.X - 1) _ _
    (isUnit_affineLineSOnXChart_X k) (isUnit_xOnSChart_X_sub_one k)
    (affineLineSOnXChart_hfg k) (affineLineSOnXChart_hgf k)

/-! #### The `y`-side: `k[y][1/(y-1)]` is `k[s][1/(s+1)]` -/

/-- On the second chart, `s + 1 = -1/(y - 1)`. -/
theorem affineLineSOnYChart_X_add_one :
    affineLineSOnYChart k (Polynomial.X + 1) =
      -(IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k)) := by
  rw [map_add, map_one, affineLineSOnYChart_X]
  ring

/-- On the second chart, `s + 1` is a unit of `k[y][1/(y-1)]`. -/
theorem isUnit_affineLineSOnYChart_X_add_one :
    IsUnit (affineLineSOnYChart k (Polynomial.X + 1)) := by
  rw [affineLineSOnYChart_X_add_one]
  refine IsUnit.of_mul_eq_one
    (-(algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X - 1)) ?_
  linear_combination invSelf_X_sub_one_mul k (affineLineAwayOne k)

/-- The substitution `y = s/(s+1)` inverse to `s = y/(1-y)`. -/
def yOnSChart : Polynomial k →+*
    Localization.Away (Polynomial.X + 1 : Polynomial k) :=
  (Polynomial.aeval (algebraMap (Polynomial k)
      (Localization.Away (Polynomial.X + 1 : Polynomial k)) Polynomial.X *
      IsLocalization.Away.invSelf (Polynomial.X + 1 : Polynomial k)) :
    Polynomial k →ₐ[k] Localization.Away (Polynomial.X + 1 : Polynomial k)).toRingHom

/-- Under the substitution `yOnSChart`, `y = s/(s+1)`. -/
theorem yOnSChart_X : yOnSChart k Polynomial.X =
    algebraMap (Polynomial k) (Localization.Away (Polynomial.X + 1 : Polynomial k))
      Polynomial.X *
      IsLocalization.Away.invSelf (Polynomial.X + 1 : Polynomial k) := by simp [yOnSChart]

/-- Under `y = s/(s+1)`, one has `y - 1 = -1/(s+1)`. -/
theorem yOnSChart_X_sub_one : yOnSChart k (Polynomial.X - 1) =
    -(IsLocalization.Away.invSelf (Polynomial.X + 1 : Polynomial k)) := by
  rw [map_sub, map_one, yOnSChart_X]
  linear_combination invSelf_X_add_one_mul k (Localization.Away (Polynomial.X + 1 : Polynomial k))

/-- Under `y = s/(s+1)`, the function `y - 1` is a unit of `k[s][1/(s+1)]`. -/
theorem isUnit_yOnSChart_X_sub_one : IsUnit (yOnSChart k (Polynomial.X - 1)) := by
  rw [yOnSChart_X_sub_one]
  refine IsUnit.of_mul_eq_one
    (-(algebraMap (Polynomial k) (Localization.Away (Polynomial.X + 1 : Polynomial k))
      Polynomial.X + 1)) ?_
  linear_combination invSelf_X_add_one_mul k (Localization.Away (Polynomial.X + 1 : Polynomial k))

/-- Substituting `y = s/(s+1)` into `s = y/(1-y)` gives back `s`. -/
theorem affineLineSOnYChart_hfg :
    (IsLocalization.Away.lift (S := affineLineAwayOne k) (Polynomial.X - 1 : Polynomial k)
        (isUnit_yOnSChart_X_sub_one k)).comp (affineLineSOnYChart k) =
      algebraMap (Polynomial k) (Localization.Away (Polynomial.X + 1 : Polynomial k)) := by
  refine Polynomial.ringHom_ext ?_ ?_
  · intro a
    rw [RingHom.comp_apply, affineLineSOnYChart_C, IsLocalization.Away.lift_eq]
    simp [yOnSChart, IsScalarTower.algebraMap_apply k (Polynomial k)
      (Localization.Away (Polynomial.X + 1 : Polynomial k))]
  · have h := invSelf_X_add_one_mul k (Localization.Away (Polynomial.X + 1 : Polynomial k))
    have key := map_eq_of_mul_eq_one
      (IsLocalization.Away.lift (S := affineLineAwayOne k) (Polynomial.X - 1 : Polynomial k)
        (isUnit_yOnSChart_X_sub_one k))
      (invSelf_mul_algebraMap (Polynomial.X - 1 : Polynomial k) (affineLineAwayOne k))
      (u := -(IsLocalization.Away.invSelf (Polynomial.X + 1 : Polynomial k)))
      (v := -(algebraMap (Polynomial k) (Localization.Away (Polynomial.X + 1 : Polynomial k))
        Polynomial.X + 1))
      (by rw [IsLocalization.Away.lift_eq, yOnSChart_X_sub_one])
      (by linear_combination h)
    rw [RingHom.comp_apply, affineLineSOnYChart_X, map_sub, map_neg, map_one, key]
    ring

/-- Substituting `s = y/(1-y)` into `y = s/(s+1)` gives back `y`. -/
theorem affineLineSOnYChart_hgf :
    (IsLocalization.Away.lift (S := Localization.Away (Polynomial.X + 1 : Polynomial k))
        (Polynomial.X + 1 : Polynomial k)
        (isUnit_affineLineSOnYChart_X_add_one k)).comp (yOnSChart k) =
      algebraMap (Polynomial k) (affineLineAwayOne k) := by
  refine Polynomial.ringHom_ext ?_ ?_
  · intro a
    have h1 : yOnSChart k (Polynomial.C a) =
        algebraMap (Polynomial k) (Localization.Away (Polynomial.X + 1 : Polynomial k))
          (Polynomial.C a) := by
      simp [yOnSChart, IsScalarTower.algebraMap_apply k (Polynomial k)
        (Localization.Away (Polynomial.X + 1 : Polynomial k))]
    rw [RingHom.comp_apply, h1, IsLocalization.Away.lift_eq, affineLineSOnYChart_C]
  · have key := map_eq_of_mul_eq_one
      (IsLocalization.Away.lift (S := Localization.Away (Polynomial.X + 1 : Polynomial k))
        (Polynomial.X + 1 : Polynomial k) (isUnit_affineLineSOnYChart_X_add_one k))
      (invSelf_mul_algebraMap (Polynomial.X + 1 : Polynomial k)
        (Localization.Away (Polynomial.X + 1 : Polynomial k)))
      (u := -(IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k)))
      (v := -(algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X - 1))
      (by rw [IsLocalization.Away.lift_eq, affineLineSOnYChart_X_add_one])
      (by linear_combination invSelf_X_sub_one_mul k (affineLineAwayOne k))
    rw [RingHom.comp_apply, yOnSChart_X, map_mul, IsLocalization.Away.lift_eq,
      affineLineSOnYChart_X, key]
    linear_combination invSelf_X_sub_one_mul k (affineLineAwayOne k)

/-- **`k[y][1/(y-1)]` is the localization of `k[s]` away from `s + 1`,** for `s = y/(1-y)`. -/
def affineLineAwayOneEquivY :
    Localization.Away (Polynomial.X + 1 : Polynomial k) ≃+* affineLineAwayOne k :=
  awayEquivOfSubst (Polynomial.X + 1) (Polynomial.X - 1) _ _
    (isUnit_affineLineSOnYChart_X_add_one k) (isUnit_yOnSChart_X_sub_one k)
    (affineLineSOnYChart_hfg k) (affineLineSOnYChart_hgf k)

/-- **The image of `D(y-1) ⊂ X₂` in `Spec k[s]` is `D(s+1)`.** -/
theorem range_comap_affineLineSOnYChart :
    Set.range (PrimeSpectrum.comap (affineLineSOnYChart k)) =
      (PrimeSpectrum.basicOpen (Polynomial.X + 1 : Polynomial k) : Set _) := by
  exact range_comap_eq_basicOpen_of_subst (Polynomial.X + 1) (Polynomial.X - 1) _ _
    (isUnit_affineLineSOnYChart_X_add_one k) (isUnit_yOnSChart_X_sub_one k)
    (affineLineSOnYChart_hfg k) (affineLineSOnYChart_hgf k)

end Reparametrization

/-! ### The two pieces of the third chart -/

section Pieces

/-- A unit may be cancelled from a membership in a prime ideal. -/
private theorem mul_unit_mem_iff {R : Type*} [CommRing R] {q : Ideal R} {a u : R}
    (hu : IsUnit u) : a * u ∈ q ↔ a ∈ q := by
  refine ⟨fun h ↦ ?_, fun h ↦ Ideal.mul_mem_right _ _ h⟩
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have ha : a = a * u * v := by rw [mul_assoc, hv, mul_one]
  rw [ha]
  exact Ideal.mul_mem_right _ _ h

/-- A unit is not a member of a prime ideal. -/
private theorem notMem_of_isUnit {R : Type*} [CommRing R] {q : Ideal R} (hq : q.IsPrime) {u : R}
    (hu : IsUnit u) : u ∉ q := fun h ↦ hq.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

/-- `Spec` of a ring map that becomes the localization map after an isomorphism of the target is
an open immersion. -/
theorem isOpenImmersion_specMap_of_equiv_comp {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] (r : R) [IsLocalization.Away r A] (e : A ≃+* B)
    {f : R →+* B} (hf : (e : A →+* B).comp (algebraMap R A) = f) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) := by
  have hiso : IsIso (CommRingCat.ofHom (e : A →+* B)) := by
    refine ⟨CommRingCat.ofHom (e.symm : B →+* A), ?_, ?_⟩ <;>
      · apply CommRingCat.hom_ext
        ext x
        simp
  have hloc : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    IsOpenImmersion.of_isLocalization r
  rw [← hf, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

variable (k : Type u) [CommRing k]

/-- The `x`-side piece of the third chart, `D(s) ⊂ Spec k[s]` read as `D(x-1) ⊂ X₁`. -/
abbrev projectiveLineSXPiece :
    Spec (.of (affineLineAwayOne k)) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (affineLineSOnXChart k))

/-- The `y`-side piece of the third chart, `D(s+1) ⊂ Spec k[s]` read as `D(y-1) ⊂ X₂`. -/
abbrev projectiveLineSYPiece :
    Spec (.of (affineLineAwayOne k)) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (affineLineSOnYChart k))

/-- The `x`-side piece of the third chart is an open immersion. -/
instance : IsOpenImmersion (projectiveLineSXPiece k) :=
  isOpenImmersion_specMap_of_equiv_comp Polynomial.X
    (awayEquivOfSubst Polynomial.X (Polynomial.X - 1) _ _
      (isUnit_affineLineSOnXChart_X k) (isUnit_xOnSChart_X_sub_one k)
      (affineLineSOnXChart_hfg k) (affineLineSOnXChart_hgf k))
    (awayEquivOfSubst_comp Polynomial.X (Polynomial.X - 1) _ _
      (isUnit_affineLineSOnXChart_X k) (isUnit_xOnSChart_X_sub_one k)
      (affineLineSOnXChart_hfg k) (affineLineSOnXChart_hgf k))

/-- The `y`-side piece of the third chart is an open immersion. -/
instance : IsOpenImmersion (projectiveLineSYPiece k) :=
  isOpenImmersion_specMap_of_equiv_comp (Polynomial.X + 1)
    (awayEquivOfSubst (Polynomial.X + 1) (Polynomial.X - 1) _ _
      (isUnit_affineLineSOnYChart_X_add_one k) (isUnit_yOnSChart_X_sub_one k)
      (affineLineSOnYChart_hfg k) (affineLineSOnYChart_hgf k))
    (awayEquivOfSubst_comp (Polynomial.X + 1) (Polynomial.X - 1) _ _
      (isUnit_affineLineSOnYChart_X_add_one k) (isUnit_yOnSChart_X_sub_one k)
      (affineLineSOnYChart_hfg k) (affineLineSOnYChart_hgf k))

/-- The image of the `x`-side piece in `Spec k[s]` is `D(s)`. -/
theorem mem_range_projectiveLineSXPiece (p : Spec (.of (Polynomial k))) :
    p ∈ Set.range (projectiveLineSXPiece k).base ↔
      (Polynomial.X : Polynomial k) ∉ p.asIdeal := by
  have h : p ∈ Set.range (projectiveLineSXPiece k).base ↔
      p ∈ Set.range (PrimeSpectrum.comap (affineLineSOnXChart k)) := Iff.rfl
  rw [h, range_comap_affineLineSOnXChart]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- The image of the `y`-side piece in `Spec k[s]` is `D(s+1)`. -/
theorem mem_range_projectiveLineSYPiece (p : Spec (.of (Polynomial k))) :
    p ∈ Set.range (projectiveLineSYPiece k).base ↔
      (Polynomial.X + 1 : Polynomial k) ∉ p.asIdeal := by
  have h : p ∈ Set.range (projectiveLineSYPiece k).base ↔
      p ∈ Set.range (PrimeSpectrum.comap (affineLineSOnYChart k)) := Iff.rfl
  rw [h, range_comap_affineLineSOnYChart]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- The coordinate ring `k[x][1/(x(x-1))]` of the intersection of the two pieces. -/
abbrev affineLineAwayOneAwayX : Type u :=
  Localization.Away (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X)

/-- The inclusion of the intersection of the two pieces into the `x`-side piece. -/
abbrev projectiveLineSOverlapInclusion :
    Spec (.of (affineLineAwayOneAwayX k)) ⟶ Spec (.of (affineLineAwayOne k)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)))

/-- The inclusion of the intersection into the `x`-side piece is an open immersion. -/
instance : IsOpenImmersion (projectiveLineSOverlapInclusion k) :=
  IsOpenImmersion.of_isLocalization
    (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X)

/-- The image of the intersection in the `x`-side piece is the locus where `x` does not vanish. -/
theorem mem_range_projectiveLineSOverlapInclusion (b : Spec (.of (affineLineAwayOne k))) :
    b ∈ Set.range (projectiveLineSOverlapInclusion k).base ↔
      algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X ∉ b.asIdeal := by
  have h : b ∈ Set.range (projectiveLineSOverlapInclusion k).base ↔
      b ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k))) := Iff.rfl
  rw [h, PrimeSpectrum.localization_away_comap_range (affineLineAwayOneAwayX k)
    (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X)]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- `s + 1 = x/(x-1)` on the `x`-side piece. -/
theorem affineLineSOnXChart_X_add_one :
    affineLineSOnXChart k (Polynomial.X + 1) =
      algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k) := by
  have h := invSelf_mul_algebraMap (Polynomial.X - 1 : Polynomial k) (affineLineAwayOne k)
  rw [map_sub, map_one] at h
  rw [map_add, map_one, affineLineSOnXChart_X]
  linear_combination -h

/-- The intersection of the two pieces of the third chart, as a piece of `Spec k[s]`. -/
abbrev projectiveLineSOverlapPiece :
    Spec (.of (affineLineAwayOneAwayX k)) ⟶ Spec (.of (Polynomial k)) :=
  projectiveLineSOverlapInclusion k ≫ projectiveLineSXPiece k

/-- The image of the intersection of the two pieces in `Spec k[s]` is `D(s) ∩ D(s+1)`. -/
theorem mem_range_projectiveLineSOverlapPiece (p : Spec (.of (Polynomial k))) :
    p ∈ Set.range (projectiveLineSOverlapPiece k).base ↔
      (Polynomial.X : Polynomial k) ∉ p.asIdeal ∧
        (Polynomial.X + 1 : Polynomial k) ∉ p.asIdeal := by
  have hinv : IsUnit (IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k) :
      affineLineAwayOne k) :=
    IsUnit.of_mul_eq_one
      (algebraMap (Polynomial k) (affineLineAwayOne k) (Polynomial.X - 1))
      (invSelf_mul_algebraMap _ _)
  have key : ∀ b : Spec (.of (affineLineAwayOne k)),
      ((Polynomial.X + 1 : Polynomial k) ∉
          ((projectiveLineSXPiece k).base b).asIdeal ↔
        algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X ∉ b.asIdeal) := by
    intro b
    have hid : ((projectiveLineSXPiece k).base b).asIdeal =
        Ideal.comap (affineLineSOnXChart k) b.asIdeal := rfl
    rw [hid, Ideal.mem_comap, affineLineSOnXChart_X_add_one, mul_unit_mem_iff hinv]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨?_, ?_⟩
    · have hid : ((projectiveLineSXPiece k).base
          ((projectiveLineSOverlapInclusion k).base c)).asIdeal =
          Ideal.comap (affineLineSOnXChart k)
            ((projectiveLineSOverlapInclusion k).base c).asIdeal := rfl
      show (Polynomial.X : Polynomial k) ∉ _
      rw [show ((projectiveLineSOverlapPiece k).base c) =
        (projectiveLineSXPiece k).base ((projectiveLineSOverlapInclusion k).base c) from rfl,
        hid, Ideal.mem_comap, affineLineSOnXChart_X]
      exact notMem_of_isUnit ((projectiveLineSOverlapInclusion k).base c).2 hinv
    · rw [show ((projectiveLineSOverlapPiece k).base c) =
        (projectiveLineSXPiece k).base ((projectiveLineSOverlapInclusion k).base c) from rfl,
        key]
      exact (mem_range_projectiveLineSOverlapInclusion k _).mp ⟨c, rfl⟩
  · rintro ⟨hX, hX1⟩
    obtain ⟨b, hb⟩ := (mem_range_projectiveLineSXPiece k p).mpr hX
    obtain ⟨c, hc⟩ := (mem_range_projectiveLineSOverlapInclusion k b).mpr
      ((key b).mp (by rw [hb]; exact hX1))
    exact ⟨c, by
      rw [show ((projectiveLineSOverlapPiece k).base c) =
        (projectiveLineSXPiece k).base ((projectiveLineSOverlapInclusion k).base c) from rfl,
        hc, hb]⟩

end Pieces

/-! ### The cover of `Spec k[s]` by the two pieces -/

/-- The indices of the cover of `Spec k[s]` used to build the third chart: the two pieces
`D(s)` and `D(s+1)`, together with their intersection. -/
inductive ProjectiveLineSIndex : Type
  | xSide : ProjectiveLineSIndex
  | ySide : ProjectiveLineSIndex
  | overlap : ProjectiveLineSIndex

namespace ProjectiveLineSIndex

/-- The intersection is below the two pieces; the two pieces are incomparable. -/
instance : Preorder ProjectiveLineSIndex where
  le a b := a = b ∨ a = overlap
  le_refl _ := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | rfl
    · exact hbc
    · exact Or.inr rfl

/-- An index is below another exactly when they are equal or the first is the intersection. -/
theorem le_iff (a b : ProjectiveLineSIndex) : a ≤ b ↔ a = b ∨ a = overlap := Iff.rfl

/-- The intersection is below every index. -/
theorem overlap_le (a : ProjectiveLineSIndex) : overlap ≤ a := Or.inr rfl

end ProjectiveLineSIndex

section Cover

open ProjectiveLineSIndex

/-- **A cover indexed by a preorder whose pieces are closed under intersection is locally
directed:** it suffices that the images of the members are monotone in the index and that two
members' images have a common lower bound through every point of their intersection. -/
@[instance_reducible]
def coverLocallyDirectedOfInter {X : Scheme.{u}} {𝒰 : X.OpenCover} [Preorder 𝒰.I₀]
    (hle : ∀ {i j : 𝒰.I₀}, i ≤ j → Set.range (𝒰.f i).base ⊆ Set.range (𝒰.f j).base)
    (H : ∀ (i j : 𝒰.I₀) (a : X), a ∈ Set.range (𝒰.f i).base → a ∈ Set.range (𝒰.f j).base →
      ∃ (l : 𝒰.I₀) (_ : l ≤ i) (_ : l ≤ j) (y : 𝒰.X l), (𝒰.f l).base y = a) :
    𝒰.LocallyDirected where
  trans {i j} hij := IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle (leOfHom hij))
  trans_id i := by rw [← cancel_mono (𝒰.f i)]; simp
  trans_comp hij hjk := by rw [← cancel_mono (𝒰.f _)]; simp
  directed {i j} x := by
    obtain ⟨l, hli, hlj, y, hy⟩ := H i j ((pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).base x)
      ⟨_, rfl⟩ (by rw [pullback.condition]; exact ⟨_, rfl⟩)
    refine ⟨l, homOfLE hli, homOfLE hlj, y, ?_⟩
    apply (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc, IsOpenImmersion.lift_fac, hy]

variable (k : Type u) [CommRing k]

/-- **The cover `Spec k[s] = D(s) ∪ D(s+1)`**, with the intersection adjoined so that the cover
is locally directed. The two pieces are the complement of `1` read in either chart. -/
def projectiveLineSCover : (Spec (.of (Polynomial k))).OpenCover where
  I₀ := ProjectiveLineSIndex
  X i := match i with
    | .xSide => Spec (.of (affineLineAwayOne k))
    | .ySide => Spec (.of (affineLineAwayOne k))
    | .overlap => Spec (.of (affineLineAwayOneAwayX k))
  f i := match i with
    | .xSide => projectiveLineSXPiece k
    | .ySide => projectiveLineSYPiece k
    | .overlap => projectiveLineSOverlapPiece k
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun p ↦ ?_, ?_⟩
    · by_cases hX : (Polynomial.X : Polynomial k) ∈ p.asIdeal
      · have hX1 : (Polynomial.X + 1 : Polynomial k) ∉ p.asIdeal := by
          intro hmem
          exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _
            (by simpa using Ideal.sub_mem _ hmem hX) isUnit_one)
        obtain ⟨b, hb⟩ := (mem_range_projectiveLineSYPiece k p).mpr hX1
        exact ⟨.ySide, b, hb⟩
      · obtain ⟨b, hb⟩ := (mem_range_projectiveLineSXPiece k p).mpr hX
        exact ⟨.xSide, b, hb⟩
    · intro i
      cases i <;> dsimp <;> infer_instance

/-- The `x`-side member of the cover is the `x`-side piece. -/
@[simp] theorem projectiveLineSCover_f_xSide :
    (projectiveLineSCover k).f .xSide = projectiveLineSXPiece k := rfl

/-- The `y`-side member of the cover is the `y`-side piece. -/
@[simp] theorem projectiveLineSCover_f_ySide :
    (projectiveLineSCover k).f .ySide = projectiveLineSYPiece k := rfl

/-- The intersection member of the cover is the intersection of the two pieces. -/
@[simp] theorem projectiveLineSCover_f_overlap :
    (projectiveLineSCover k).f .overlap = projectiveLineSOverlapPiece k := rfl

/-- The indices of the cover carry the preorder of `ProjectiveLineSIndex`. -/
instance : Preorder (projectiveLineSCover k).I₀ :=
  inferInstanceAs (Preorder ProjectiveLineSIndex)

/-- The images of the members of the cover are monotone in the index. -/
theorem projectiveLineSCover_range_subset {i j : ProjectiveLineSIndex} (hij : i ≤ j) :
    Set.range ((projectiveLineSCover k).f i).base ⊆
      Set.range ((projectiveLineSCover k).f j).base := by
  rcases hij with rfl | rfl
  · exact subset_rfl
  · cases j with
    | overlap => exact subset_rfl
    | xSide =>
        rintro p ⟨c, hc⟩
        exact ⟨(projectiveLineSOverlapInclusion k).base c, hc⟩
    | ySide =>
        intro p hp
        refine (mem_range_projectiveLineSYPiece k p).mpr ?_
        exact ((mem_range_projectiveLineSOverlapPiece k p).mp hp).2

/-- The cover `Spec k[s] = D(s) ∪ D(s+1)`, with the intersection adjoined, is locally directed. -/
instance : (projectiveLineSCover k).LocallyDirected :=
  coverLocallyDirectedOfInter (projectiveLineSCover_range_subset k) <| by
    intro i j a hi hj
    cases i with
    | overlap => exact ⟨.overlap, le_rfl, overlap_le _, hi.choose, hi.choose_spec⟩
    | xSide =>
        cases j with
        | xSide => exact ⟨.xSide, le_rfl, le_rfl, hi.choose, hi.choose_spec⟩
        | overlap => exact ⟨.overlap, overlap_le _, le_rfl, hj.choose, hj.choose_spec⟩
        | ySide =>
            have h := (mem_range_projectiveLineSOverlapPiece k a).mpr
              ⟨(mem_range_projectiveLineSXPiece k a).mp hi,
               (mem_range_projectiveLineSYPiece k a).mp hj⟩
            exact ⟨.overlap, overlap_le _, overlap_le _, h.choose, h.choose_spec⟩
    | ySide =>
        cases j with
        | ySide => exact ⟨.ySide, le_rfl, le_rfl, hi.choose, hi.choose_spec⟩
        | overlap => exact ⟨.overlap, overlap_le _, le_rfl, hj.choose, hj.choose_spec⟩
        | xSide =>
            have h := (mem_range_projectiveLineSOverlapPiece k a).mpr
              ⟨(mem_range_projectiveLineSXPiece k a).mp hj,
               (mem_range_projectiveLineSYPiece k a).mp hi⟩
            exact ⟨.overlap, overlap_le _, overlap_le _, h.choose, h.choose_spec⟩

end Cover

/-! ### The third chart `Spec k[s] ⟶ ℙ¹` -/

section Chart

open ProjectiveLineSIndex

variable (k : Type u) [CommRing k]

/-- `y = 1/x` read on the intersection of the two pieces. -/
def yOnProjectiveLineSOverlap : Polynomial k →+* affineLineAwayOneAwayX k :=
  (Polynomial.aeval (IsLocalization.Away.invSelf
      (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X)) :
    Polynomial k →ₐ[k] affineLineAwayOneAwayX k).toRingHom

private theorem invSelf_xBar_mul :
    IsLocalization.Away.invSelf
        (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X) *
      algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)
        (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X) = 1 :=
  invSelf_mul_algebraMap _ _

private theorem invSelf_xSubOne_mul :
    algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)
        (IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k)) *
      (algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)
        (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X) - 1) = 1 := by
  have h := invSelf_mul_algebraMap (Polynomial.X - 1 : Polynomial k) (affineLineAwayOne k)
  rw [map_sub, map_one] at h
  have h' := congrArg (algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)) h
  simp only [map_mul, map_sub, map_one] at h'
  exact h'

private theorem invSelf_xBar_sub_one_mul_neg :
    (IsLocalization.Away.invSelf
        (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X) - 1) *
      (-(algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)
          (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X) *
        algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)
          (IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k)))) = 1 := by
  have h1 := invSelf_xBar_mul k
  have h2 := invSelf_xSubOne_mul k
  linear_combination
    (-(algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)
      (IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k)))) * h1 + h2

/-- On the intersection of the two pieces, `y - 1 = 1/x - 1`. -/
theorem yOnProjectiveLineSOverlap_X_sub_one :
    yOnProjectiveLineSOverlap k (Polynomial.X - 1) =
      IsLocalization.Away.invSelf
        (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X) - 1 := by
  simp [yOnProjectiveLineSOverlap]

/-- On the intersection of the two pieces, `y - 1` is a unit. -/
theorem isUnit_yOnProjectiveLineSOverlap_X_sub_one :
    IsUnit (yOnProjectiveLineSOverlap k (Polynomial.X - 1)) := by
  rw [yOnProjectiveLineSOverlap_X_sub_one]
  exact IsUnit.of_mul_eq_one _ (invSelf_xBar_sub_one_mul_neg k)

/-- The inclusion of the intersection of the two pieces into the `y`-side piece: on the
intersection `y = 1/x`. -/
def projectiveLineSOverlapYInclusion :
    Spec (.of (affineLineAwayOneAwayX k)) ⟶ Spec (.of (affineLineAwayOne k)) :=
  Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.lift (S := affineLineAwayOne k) (Polynomial.X - 1 : Polynomial k)
      (isUnit_yOnProjectiveLineSOverlap_X_sub_one k)))

private theorem awayOneToOverlap_comp_algebraMap :
    (IsLocalization.Away.lift (S := affineLineAwayOne k) (Polynomial.X - 1 : Polynomial k)
          (isUnit_yOnProjectiveLineSOverlap_X_sub_one k)).comp
        (algebraMap (Polynomial k) (affineLineAwayOne k)) =
      yOnProjectiveLineSOverlap k :=
  IsLocalization.Away.lift_comp (x := (Polynomial.X - 1 : Polynomial k)) _

private theorem awayOneToOverlap_invSelf :
    (IsLocalization.Away.lift (S := affineLineAwayOne k) (Polynomial.X - 1 : Polynomial k)
        (isUnit_yOnProjectiveLineSOverlap_X_sub_one k))
      (IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k)) =
      -(algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)
          (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X) *
        algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)
          (IsLocalization.Away.invSelf (Polynomial.X - 1 : Polynomial k))) := by
  exact map_eq_of_mul_eq_one _
    (invSelf_mul_algebraMap (Polynomial.X - 1 : Polynomial k) (affineLineAwayOne k))
    (by rw [IsLocalization.Away.lift_eq, yOnProjectiveLineSOverlap_X_sub_one])
    (invSelf_xBar_sub_one_mul_neg k)

/-- The intersection of the two pieces sits inside the `y`-side piece over `Spec k[s]`. -/
theorem projectiveLineSOverlapYInclusion_comp_projectiveLineSYPiece :
    projectiveLineSOverlapYInclusion k ≫ projectiveLineSYPiece k =
      projectiveLineSOverlapPiece k := by
  rw [projectiveLineSOverlapYInclusion, projectiveLineSYPiece, projectiveLineSOverlapPiece,
    projectiveLineSOverlapInclusion, projectiveLineSXPiece, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine Polynomial.ringHom_ext ?_ ?_
  · intro a
    have hL : (IsLocalization.Away.lift (S := affineLineAwayOne k)
          (Polynomial.X - 1 : Polynomial k)
          (isUnit_yOnProjectiveLineSOverlap_X_sub_one k))
          (algebraMap (Polynomial k) (affineLineAwayOne k) (Polynomial.C a)) =
        yOnProjectiveLineSOverlap k (Polynomial.C a) := by
      rw [IsLocalization.Away.lift_eq]
    rw [RingHom.comp_apply, RingHom.comp_apply, affineLineSOnYChart_C, affineLineSOnXChart_C, hL,
      ← IsScalarTower.algebraMap_apply (Polynomial k) (affineLineAwayOne k)
        (affineLineAwayOneAwayX k)]
    simp [yOnProjectiveLineSOverlap,
      IsScalarTower.algebraMap_apply k (Polynomial k) (affineLineAwayOneAwayX k)]
  · rw [RingHom.comp_apply, RingHom.comp_apply, affineLineSOnYChart_X, affineLineSOnXChart_X,
      map_sub, map_neg, map_one, awayOneToOverlap_invSelf]
    have h2 := invSelf_xSubOne_mul k
    linear_combination h2

/-- The three morphisms to the projective line that glue to the third chart: on the two pieces
they are the complement of `1` in either standard chart. -/
def projectiveLineSChartMap :
    (i : ProjectiveLineSIndex) → (projectiveLineSCover k).X i ⟶ projectiveLine k
  | .xSide => Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial k) (affineLineAwayOne k))) ≫ projectiveLineXChart k
  | .ySide => Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial k) (affineLineAwayOne k))) ≫ projectiveLineYChart k
  | .overlap => projectiveLineSOverlapInclusion k ≫ (Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial k) (affineLineAwayOne k))) ≫ projectiveLineXChart k)

/-- The map `k[T, T⁻¹] ⟶ k[x][1/(x(x-1))]` sending `T` to `x`: the coordinate of the first chart
is invertible on the intersection of the two pieces. -/
private def laurentToProjectiveLineSOverlap :
    LaurentPolynomial k →+* affineLineAwayOneAwayX k :=
  IsLocalization.Away.lift (S := LaurentPolynomial k) (Polynomial.X : Polynomial k)
    (g := (algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)).comp
      (algebraMap (Polynomial k) (affineLineAwayOne k)))
    (IsUnit.of_mul_eq_one (IsLocalization.Away.invSelf
        (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X)) (by
      rw [RingHom.comp_apply, mul_comm]
      exact invSelf_xBar_mul k))

private theorem laurentToProjectiveLineSOverlap_comp_toLaurent :
    (laurentToProjectiveLineSOverlap k).comp (Polynomial.toLaurent (R := k)) =
      (algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)).comp
        (algebraMap (Polynomial k) (affineLineAwayOne k)) :=
  IsLocalization.Away.lift_comp (x := (Polynomial.X : Polynomial k)) _

private theorem laurentToProjectiveLineSOverlap_comp_inverseCoordinate :
    (laurentToProjectiveLineSOverlap k).comp
        (projectiveLineOverlapInverseCoordinate k).toRingHom =
      yOnProjectiveLineSOverlap k := by
  refine Polynomial.ringHom_ext ?_ ?_
  · intro a
    rw [RingHom.comp_apply]
    have hC : (projectiveLineOverlapInverseCoordinate k).toRingHom (Polynomial.C a) =
        Polynomial.toLaurent (Polynomial.C a) := by
      simp [projectiveLineOverlapInverseCoordinate]
    rw [hC, ← RingHom.comp_apply, laurentToProjectiveLineSOverlap_comp_toLaurent,
      RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply (Polynomial k) (affineLineAwayOne k)
        (affineLineAwayOneAwayX k)]
    simp [yOnProjectiveLineSOverlap,
      IsScalarTower.algebraMap_apply k (Polynomial k) (affineLineAwayOneAwayX k)]
  · have hX : (projectiveLineOverlapInverseCoordinate k).toRingHom Polynomial.X =
        LaurentPolynomial.T (-1) := by simp [projectiveLineOverlapInverseCoordinate]
    have hT : laurentToProjectiveLineSOverlap k (LaurentPolynomial.T 1) =
        algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)
          (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X) := by
      rw [← Polynomial.toLaurent_X, ← RingHom.comp_apply,
        laurentToProjectiveLineSOverlap_comp_toLaurent, RingHom.comp_apply]
    have key := map_eq_of_mul_eq_one (laurentToProjectiveLineSOverlap k)
      (T_neg_one_mul_T_one k) hT (v := IsLocalization.Away.invSelf
        (algebraMap (Polynomial k) (affineLineAwayOne k) Polynomial.X))
      (by rw [mul_comm]; exact invSelf_xBar_mul k)
    rw [RingHom.comp_apply, hX, key]
    simp [yOnProjectiveLineSOverlap]

/-- The two pieces agree on their intersection. -/
theorem projectiveLineSOverlapYInclusion_comp_projectiveLineSChartMap :
    projectiveLineSOverlapYInclusion k ≫ projectiveLineSChartMap k .ySide =
      projectiveLineSChartMap k .overlap := by
  have hy : projectiveLineSOverlapYInclusion k ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (Polynomial k) (affineLineAwayOne k))) =
      Spec.map (CommRingCat.ofHom (yOnProjectiveLineSOverlap k)) := by
    rw [projectiveLineSOverlapYInclusion, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      awayOneToOverlap_comp_algebraMap]
  have hx : projectiveLineSOverlapInclusion k ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (Polynomial k) (affineLineAwayOne k))) =
      Spec.map (CommRingCat.ofHom ((algebraMap (affineLineAwayOne k)
        (affineLineAwayOneAwayX k)).comp
          (algebraMap (Polynomial k) (affineLineAwayOne k)))) := by
    rw [projectiveLineSOverlapInclusion, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  show projectiveLineSOverlapYInclusion k ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial k) (affineLineAwayOne k))) ≫ projectiveLineYChart k =
    projectiveLineSOverlapInclusion k ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial k) (affineLineAwayOne k))) ≫ projectiveLineXChart k
  rw [← Category.assoc, ← Category.assoc, hy, hx,
    ← laurentToProjectiveLineSOverlap_comp_inverseCoordinate,
    ← laurentToProjectiveLineSOverlap_comp_toLaurent,
    CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc]
  exact congrArg (fun φ : Spec (.of (LaurentPolynomial k)) ⟶ projectiveLine k =>
    Spec.map (CommRingCat.ofHom (laurentToProjectiveLineSOverlap k)) ≫ φ)
    (isPullback_projectiveLineCharts k).w.symm

/-- The three morphisms to the projective line are compatible with the transition maps of the
cover. -/
theorem projectiveLineSChartMap_trans {i j : ProjectiveLineSIndex} (hij : i ⟶ j) :
    (projectiveLineSCover k).trans hij ≫ projectiveLineSChartMap k j =
      projectiveLineSChartMap k i := by
  have htrans : ∀ t : (projectiveLineSCover k).X i ⟶ (projectiveLineSCover k).X j,
      t ≫ (projectiveLineSCover k).f j = (projectiveLineSCover k).f i →
      (projectiveLineSCover k).trans hij = t := by
    intro t ht
    have : IsOpenImmersion ((projectiveLineSCover k).f j) :=
      (projectiveLineSCover k).map_prop j
    rw [← cancel_mono ((projectiveLineSCover k).f j), ht]
    exact Scheme.Cover.trans_map _ hij
  cases i <;> cases j
  · rw [htrans (𝟙 _) (Category.id_comp _), Category.id_comp]
  · exact absurd (leOfHom hij) (by rintro (h | h) <;> exact ProjectiveLineSIndex.noConfusion h)
  · exact absurd (leOfHom hij) (by rintro (h | h) <;> exact ProjectiveLineSIndex.noConfusion h)
  · exact absurd (leOfHom hij) (by rintro (h | h) <;> exact ProjectiveLineSIndex.noConfusion h)
  · rw [htrans (𝟙 _) (Category.id_comp _), Category.id_comp]
  · exact absurd (leOfHom hij) (by rintro (h | h) <;> exact ProjectiveLineSIndex.noConfusion h)
  · rw [htrans (projectiveLineSOverlapInclusion k) rfl]
    rfl
  · rw [htrans (projectiveLineSOverlapYInclusion k)
      (projectiveLineSOverlapYInclusion_comp_projectiveLineSYPiece k)]
    exact projectiveLineSOverlapYInclusion_comp_projectiveLineSChartMap k
  · rw [htrans (𝟙 _) (Category.id_comp _), Category.id_comp]

/-- The third chart of the projective line: the affine line with coordinate
`s = 1/(x-1) = y/(1-y)`, mapping onto the complement of the point `1`. -/
@[stacks 01JE "projective_line_affine_open_through_zero_and_infinity"]
def projectiveLineSChart : Spec (.of (Polynomial k)) ⟶ projectiveLine k :=
  (projectiveLineSCover k).glueMorphismsOfLocallyDirected (projectiveLineSChartMap k)
    (projectiveLineSChartMap_trans k)

/-- On `D(x-1) ⊂ X₁` the third chart is the inclusion of that open into the first chart;
equivalently, `s` restricts to `1/(x-1)` there. -/
@[stacks 01JE "projective_line_affine_open_coordinate_ring"]
theorem projectiveLineSXPiece_comp_projectiveLineSChart :
    projectiveLineSXPiece k ≫ projectiveLineSChart k =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (affineLineAwayOne k))) ≫
        projectiveLineXChart k :=
  (projectiveLineSCover k).map_glueMorphismsOfLocallyDirected _ _ .xSide

/-- On `D(y-1) ⊂ X₂` the third chart is the inclusion of that open into the second chart;
equivalently, `s` restricts to `y/(1-y)` there. -/
@[stacks 01JE "projective_line_affine_open_coordinate_ring"]
theorem projectiveLineSYPiece_comp_projectiveLineSChart :
    projectiveLineSYPiece k ≫ projectiveLineSChart k =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (affineLineAwayOne k))) ≫
        projectiveLineYChart k :=
  (projectiveLineSCover k).map_glueMorphismsOfLocallyDirected _ _ .ySide

end Chart

/-! ### The third chart is an open immersion -/

section OpenImmersion

open ProjectiveLineSIndex

variable (k : Type u) [CommRing k]

/-- The inclusion `D(x - 1) ⊂ Spec k[x]` is an open immersion. -/
instance isOpenImmersion_specMap_algebraMap_affineLineAwayOne :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial k) (affineLineAwayOne k)))) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X - 1 : Polynomial k)

/-- Every point of `Spec k[s]` lies in one of the two pieces: `s` and `s + 1` cannot both
vanish. -/
theorem exists_mem_projectiveLineSPiece (p : Spec (.of (Polynomial k))) :
    (∃ b, (projectiveLineSXPiece k).base b = p) ∨
      (∃ b, (projectiveLineSYPiece k).base b = p) := by
  by_cases hX : (Polynomial.X : Polynomial k) ∈ p.asIdeal
  · refine Or.inr ((mem_range_projectiveLineSYPiece k p).mpr ?_)
    intro hmem
    exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _
      (by simpa using Ideal.sub_mem _ hmem hX) isUnit_one)
  · exact Or.inl ((mem_range_projectiveLineSXPiece k p).mpr hX)

private theorem projectiveLineSChart_xSide (b : Spec (.of (affineLineAwayOne k))) :
    (projectiveLineSChart k).base ((projectiveLineSXPiece k).base b) =
      (projectiveLineSChartMap k .xSide).base b := by
  rw [← Scheme.Hom.comp_apply, projectiveLineSXPiece_comp_projectiveLineSChart]
  rfl

private theorem projectiveLineSChart_ySide (b : Spec (.of (affineLineAwayOne k))) :
    (projectiveLineSChart k).base ((projectiveLineSYPiece k).base b) =
      (projectiveLineSChartMap k .ySide).base b := by
  rw [← Scheme.Hom.comp_apply, projectiveLineSYPiece_comp_projectiveLineSChart]
  rfl

/-- The image of the third chart is the union of the images of the two pieces. -/
theorem range_projectiveLineSChart_eq_union :
    Set.range (projectiveLineSChart k).base =
      Set.range (projectiveLineSChartMap k .xSide).base ∪
        Set.range (projectiveLineSChartMap k .ySide).base := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨p, rfl⟩
    rcases exists_mem_projectiveLineSPiece k p with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact Or.inl ⟨b, (projectiveLineSChart_xSide k b).symm⟩
    · exact Or.inr ⟨b, (projectiveLineSChart_ySide k b).symm⟩
  · rintro z (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨_, projectiveLineSChart_xSide k b⟩
    · exact ⟨_, projectiveLineSChart_ySide k b⟩

/-- A point of `D(x-1)` in the first chart does not have `x - 1` in its prime ideal. -/
private theorem X_sub_one_notMem_comap (b : Spec (.of (affineLineAwayOne k))) :
    (Polynomial.X - 1 : Polynomial k) ∉
      (PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k)) b).asIdeal := by
  have hr : (PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k)) b) ∈
      Set.range (PrimeSpectrum.comap
        (algebraMap (Polynomial k) (affineLineAwayOne k))) := ⟨b, rfl⟩
  rw [PrimeSpectrum.localization_away_comap_range (affineLineAwayOne k)
    (Polynomial.X - 1 : Polynomial k), SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hr
  exact hr

/-- Conversely, a point of the first chart off `x = 1` comes from `D(x-1)`. -/
private theorem exists_comap_eq_of_X_sub_one_notMem (α : Spec (.of (Polynomial k)))
    (h : (Polynomial.X - 1 : Polynomial k) ∉ α.asIdeal) :
    ∃ b, PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k)) b = α := by
  have : α ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (Polynomial k) (affineLineAwayOne k))) := by
    rw [PrimeSpectrum.localization_away_comap_range (affineLineAwayOne k)
      (Polynomial.X - 1 : Polynomial k)]
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr h
  exact this

/-- **The two pieces meet only in their intersection.** On the projective line, a point of
`D(x-1) ⊂ X₁` equal to a point of `D(y-1) ⊂ X₂` lies in `D(x(x-1)) ⊂ X₁`. -/
theorem range_projectiveLineSChartMap_inter_subset :
    Set.range (projectiveLineSChartMap k .xSide).base ∩
        Set.range (projectiveLineSChartMap k .ySide).base ⊆
      Set.range (projectiveLineSChartMap k .overlap).base := by
  rintro z ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
  have hbz : (projectiveLineXChart k).base
      (PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k)) b) = z := hb
  have hbz' : (projectiveLineYChart k).base
      (PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k)) b') = z := hb'
  obtain ⟨w, hw1, -⟩ := (projectiveLineXChart_base_eq_projectiveLineYChart_base_iff k _ _).mp
    (hbz.trans hbz'.symm)
  have hXα : (Polynomial.X : Polynomial k) ∉
      (PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k)) b).asIdeal :=
    (mem_range_projectiveLinePuncturedChart_iff k _).mp ⟨w, hw1⟩
  have hX1α := X_sub_one_notMem_comap k b
  have hmem : (PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k)) b) ∈
      Set.range (PrimeSpectrum.comap
        (algebraMap (Polynomial k) (affineLineAwayOneAwayX k))) := by
    rw [PrimeSpectrum.localization_away_comap_range (affineLineAwayOneAwayX k)
      ((Polynomial.X : Polynomial k) * (Polynomial.X - 1)), SetLike.mem_coe,
      PrimeSpectrum.mem_basicOpen]
    intro hmul
    rcases (PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k))
      b).2.mem_or_mem hmul with h | h
    · exact hXα h
    · exact hX1α h
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  have htower : (algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)).comp
      (algebraMap (Polynomial k) (affineLineAwayOne k)) =
      algebraMap (Polynomial k) (affineLineAwayOneAwayX k) :=
    (IsScalarTower.algebraMap_eq (Polynomial k) (affineLineAwayOne k)
      (affineLineAwayOneAwayX k)).symm
  have hcomap : PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k))
      (PrimeSpectrum.comap (algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)) c) =
      PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k)) b := by
    rw [← PrimeSpectrum.comap_comp_apply, htower, hc]
  have hgo : (projectiveLineSChartMap k .overlap).base c =
      (projectiveLineXChart k).base
        (PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k))
          (PrimeSpectrum.comap
            (algebraMap (affineLineAwayOne k) (affineLineAwayOneAwayX k)) c)) := rfl
  rw [hgo, hcomap, hbz]

end OpenImmersion

/-! ### The affine open `ℙ¹ \ {1}` -/

section Field

open ProjectiveLineSIndex

variable (k : Type u) [Field k]

/-- A chart of the projective line is injective on points after restricting to `D(x - 1)`. -/
private theorem injective_base_awayOne_comp (φ : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
    [IsOpenImmersion φ] :
    Function.Injective (Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial k) (affineLineAwayOne k))) ≫ φ).base := by
  intro a b hab
  exact PrimeSpectrum.localization_comap_injective (affineLineAwayOne k)
    (Submonoid.powers (Polynomial.X - 1 : Polynomial k)) (φ.isOpenEmbedding.injective hab)

/-- The `x`-side morphism to the projective line is injective on points. -/
theorem projectiveLineSChartMap_xSide_injective :
    Function.Injective (projectiveLineSChartMap k .xSide).base :=
  injective_base_awayOne_comp k _

/-- The `y`-side morphism to the projective line is injective on points. -/
theorem projectiveLineSChartMap_ySide_injective :
    Function.Injective (projectiveLineSChartMap k .ySide).base :=
  injective_base_awayOne_comp k _

/-- Points of the two sides with the same image in the projective line have the same image in
`Spec k[s]`. -/
private theorem base_xSide_eq_base_ySide {b b' : Spec (.of (affineLineAwayOne k))}
    (hpq : (projectiveLineSChartMap k .xSide).base b =
      (projectiveLineSChartMap k .ySide).base b') :
    (projectiveLineSXPiece k).base b = (projectiveLineSYPiece k).base b' := by
  obtain ⟨c, hc⟩ := range_projectiveLineSChartMap_inter_subset k ⟨⟨b, rfl⟩, ⟨b', hpq.symm⟩⟩
  have hx : (projectiveLineSChartMap k .xSide).base
      ((projectiveLineSOverlapInclusion k).base c) =
      (projectiveLineSChartMap k .xSide).base b := hc.trans rfl
  have hy : (projectiveLineSChartMap k .ySide).base
      ((projectiveLineSOverlapYInclusion k).base c) =
      (projectiveLineSChartMap k .ySide).base b' := by
    refine Eq.trans ?_ (hc.trans hpq)
    exact congrArg
      (fun φ : Spec (.of (affineLineAwayOneAwayX k)) ⟶ projectiveLine k => φ.base c)
      (projectiveLineSOverlapYInclusion_comp_projectiveLineSChartMap k)
  have hfin : (projectiveLineSYPiece k).base ((projectiveLineSOverlapYInclusion k).base c) =
      (projectiveLineSOverlapPiece k).base c :=
    congrArg
      (fun φ : Spec (.of (affineLineAwayOneAwayX k)) ⟶ Spec (.of (Polynomial k)) => φ.base c)
      (projectiveLineSOverlapYInclusion_comp_projectiveLineSYPiece k)
  rw [← projectiveLineSChartMap_xSide_injective k hx,
    ← projectiveLineSChartMap_ySide_injective k hy, hfin]
  rfl

/-- The third chart is injective on points. -/
theorem projectiveLineSChart_base_injective :
    Function.Injective (projectiveLineSChart k).base := by
  intro p q hpq
  rcases exists_mem_projectiveLineSPiece k p with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
    rcases exists_mem_projectiveLineSPiece k q with ⟨b', rfl⟩ | ⟨b', rfl⟩
  · rw [projectiveLineSChart_xSide, projectiveLineSChart_xSide] at hpq
    rw [projectiveLineSChartMap_xSide_injective k hpq]
  · rw [projectiveLineSChart_xSide, projectiveLineSChart_ySide] at hpq
    exact base_xSide_eq_base_ySide k hpq
  · rw [projectiveLineSChart_ySide, projectiveLineSChart_xSide] at hpq
    exact (base_xSide_eq_base_ySide k hpq.symm).symm
  · rw [projectiveLineSChart_ySide, projectiveLineSChart_ySide] at hpq
    rw [projectiveLineSChartMap_ySide_injective k hpq]

/-- The third chart `Spec k[s] ⟶ ℙ¹` is an open immersion. -/
instance : IsOpenImmersion (projectiveLineSChart k) := by
  have hloc : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial k) (affineLineAwayOne k)))) :=
    IsOpenImmersion.of_isLocalization (Polynomial.X - 1 : Polynomial k)
  have hov : IsOpenImmersion (projectiveLineSOverlapInclusion k) := inferInstance
  refine IsOpenImmersion.of_openCover_source _ (projectiveLineSCover k)
    (projectiveLineSChart_base_injective k) ?_
  intro i
  have h : (projectiveLineSCover k).f i ≫ projectiveLineSChart k =
      projectiveLineSChartMap k i :=
    (projectiveLineSCover k).map_glueMorphismsOfLocallyDirected _ _ i
  rw [h]
  cases i <;> dsimp only [projectiveLineSChartMap]
  · exact @IsOpenImmersion.comp _ _ _ _ _ hloc inferInstance
  · exact @IsOpenImmersion.comp _ _ _ _ _ hloc inferInstance
  · exact @IsOpenImmersion.comp _ _ _ _ _ hov
      (@IsOpenImmersion.comp _ _ _ _ _ hloc inferInstance)

/-- The only point of an affine-line chart at which `x - 1` vanishes is the point `1`: the ideal
`(X - 1)` is maximal in `k[X]`. -/
theorem eq_affineLineOne_of_X_sub_one_mem (y : Spec (.of (Polynomial k)))
    (hy : (Polynomial.X - 1 : Polynomial k) ∈ y.asIdeal) : y = affineLineOne k := by
  refine PrimeSpectrum.ext ?_
  have hmax : (Ideal.span {(Polynomial.X - 1 : Polynomial k)}).IsMaximal := by
    simpa [← Ideal.submodule_span_eq] using
      PrincipalIdealRing.isMaximal_of_irreducible
        (by simpa using Polynomial.irreducible_X_sub_C (1 : k))
  have hle : Ideal.span {(Polynomial.X - 1 : Polynomial k)} ≤ y.asIdeal := by
    rw [Ideal.span_le]
    simpa using hy
  exact (hmax.eq_of_le y.2.ne_top hle).symm

/-- The coordinate does not vanish at the point `1`. -/
theorem X_notMem_affineLineOne :
    (Polynomial.X : Polynomial k) ∉ (affineLineOne k).asIdeal := by
  intro h
  rw [show (affineLineOne k).asIdeal =
    Ideal.span {(Polynomial.X - 1 : Polynomial k)} from rfl,
    Ideal.mem_span_singleton] at h
  obtain ⟨q, hq⟩ := h
  have h1 := congrArg (Polynomial.eval 1) hq
  simp at h1

/-- The function `x - 1` does not vanish at the origin of a chart. -/
theorem X_sub_one_notMem_affineLineOrigin :
    (Polynomial.X - 1 : Polynomial k) ∉ (affineLineOrigin k).asIdeal := by
  intro h
  rw [show (affineLineOrigin k).asIdeal =
    Ideal.span {(Polynomial.X : Polynomial k)} from rfl, Ideal.mem_span_singleton] at h
  obtain ⟨q, hq⟩ := h
  have h0 := congrArg (Polynomial.eval 0) hq
  simp at h0

/-- The image of the third chart is exactly the complement of the point `1`: `U = ℙ¹ \ {1}`. -/
@[stacks 01JE "projective_line_affine_open_through_zero_and_infinity"]
theorem range_projectiveLineSChart :
    Set.range (projectiveLineSChart k).base = {projectiveLineOne k}ᶜ := by
  rw [range_projectiveLineSChart_eq_union]
  refine Set.Subset.antisymm ?_ ?_
  · rintro z (⟨b, rfl⟩ | ⟨b, rfl⟩) <;> simp only [Set.mem_compl_iff, Set.mem_singleton_iff] <;>
      intro hz
    · have hα : PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k)) b =
          affineLineOne k := projectiveLineXChart_base_injective hz
      exact (hα ▸ X_sub_one_notMem_comap k b) (Ideal.subset_span rfl)
    · have hz' : (projectiveLineYChart k).base
          (PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k)) b) =
          (projectiveLineYChart k).base (affineLineOne k) := by
        rw [projectiveLineYChart_affineLineOne]
        exact hz
      have hα : PrimeSpectrum.comap (algebraMap (Polynomial k) (affineLineAwayOne k)) b =
          affineLineOne k := (projectiveLineYChart k).isOpenEmbedding.injective hz'
      exact (hα ▸ X_sub_one_notMem_comap k b) (Ideal.subset_span rfl)
  · intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    rcases mem_range_projectiveLineXChart_or_eq_infinity z with ⟨α, rfl⟩ | rfl
    · by_cases h1 : (Polynomial.X - 1 : Polynomial k) ∈ α.asIdeal
      · exact absurd (congrArg (projectiveLineXChart k).base
          (eq_affineLineOne_of_X_sub_one_mem k α h1)) hz
      · obtain ⟨b, hb⟩ := exists_comap_eq_of_X_sub_one_notMem k α h1
        exact Or.inl ⟨b, congrArg (projectiveLineXChart k).base hb⟩
    · obtain ⟨b, hb⟩ := exists_comap_eq_of_X_sub_one_notMem k (affineLineOrigin k)
        (X_sub_one_notMem_affineLineOrigin k)
      exact Or.inr ⟨b, congrArg (projectiveLineYChart k).base hb⟩

/-- `U = ℙ¹ \ {1}` is an affine open. -/
@[stacks 01JE "projective_line_affine_open_through_zero_and_infinity"]
theorem isAffineOpen_projectiveLineSChart :
    IsAffineOpen (projectiveLineSChart k).opensRange :=
  isAffineOpen_opensRange _

/-- The point `0` lies in `U = ℙ¹ \ {1}`. -/
@[stacks 01JE "projective_line_affine_open_through_zero_and_infinity"]
theorem projectiveLineZero_mem_opensRange_projectiveLineSChart :
    projectiveLineZero k ∈ (projectiveLineSChart k).opensRange := by
  show projectiveLineZero k ∈ Set.range (projectiveLineSChart k).base
  rw [range_projectiveLineSChart]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  exact X_sub_one_notMem_affineLineOrigin k
    ((projectiveLineXChart_base_injective h) ▸ Ideal.subset_span rfl)

/-- The point `∞` lies in `U = ℙ¹ \ {1}`. -/
@[stacks 01JE "projective_line_affine_open_through_zero_and_infinity"]
theorem projectiveLineInfinity_mem_opensRange_projectiveLineSChart :
    projectiveLineInfinity k ∈ (projectiveLineSChart k).opensRange := by
  show projectiveLineInfinity k ∈ Set.range (projectiveLineSChart k).base
  rw [range_projectiveLineSChart]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have h' : (projectiveLineYChart k).base (affineLineOrigin k) =
      (projectiveLineYChart k).base (affineLineOne k) := by
    rw [projectiveLineYChart_affineLineOne]
    exact h
  exact X_sub_one_notMem_affineLineOrigin k
    (((projectiveLineYChart k).isOpenEmbedding.injective h') ▸ Ideal.subset_span rfl)

/-- `U = ℙ¹ \ {1}` is isomorphic to `Spec k[s]`, and so `Γ(U, O_U) = k[s]`. -/
@[stacks 01JE "projective_line_affine_open_coordinate_ring"]
def projectiveLineSChartIso :
    Spec (.of (Polynomial k)) ≅ ((projectiveLineSChart k).opensRange).toScheme :=
  Scheme.Hom.isoOpensRange _

/-- An isomorphism of schemes induces one on global sections. -/
def sectionsIsoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) : Γ(X, ⊤) ≅ Γ(Y, ⊤) where
  hom := e.inv.appTop
  inv := e.hom.appTop
  hom_inv_id := by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]; simp
  inv_hom_id := by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]; simp

/-- `Γ(U, O_U)` is the polynomial ring `k[s]`, for the coordinate `s = 1/(x-1) = y/(1-y)` of
`AlgebraicGeometry.affineLineSOnXChart` and `AlgebraicGeometry.affineLineSOnYChart`. -/
@[stacks 01JE "projective_line_affine_open_coordinate_ring"]
def projectiveLineSChartSectionsIso :
    CommRingCat.of (Polynomial k) ≅ Γ(((projectiveLineSChart k).opensRange).toScheme, ⊤) :=
  (Scheme.ΓSpecIso (.of (Polynomial k))).symm ≪≫ sectionsIsoOfIso (projectiveLineSChartIso k)

end Field

end AlgebraicGeometry

end

end
