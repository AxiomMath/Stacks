module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineSpaceCharts
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineSpaceChartAlgebra
public import StacksFrontier.RingTheory.Norm.Projective
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAffineLine
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldTarget

/-!
# Representability of the charts `F_W`

Let `S` be an affine scheme with `R = Γ(S, 𝒪_S)`, let `n` be an index type, `d` a natural number
and `W_1, …, W_d ∈ R[x_i ; i ∈ n]`. This file proves that the subfunctor `F_W` of the degree-`d`
Hilbert functor of `𝔸(n; S)` (`Stacks.Hilbert.chartSubfunctor`) is representable by an affine
scheme over `S`.

The universal algebra `R_univ = Stacks.Hilbert.ChartAlgebra.Univ W` is presented by the coordinates
`v(m) ∈ R_univ^d` of all monomials `x^m` in the basis `W_l`, subject to `v(W_l) = e_l` and
`v(x^{m+m'}) = ∑_l v(m')_l v(x^m W_l)`.

## Main definitions

* `Stacks.Hilbert.chartScheme`: `Spec R_univ` over `S`, for the universal algebra
  `R_univ = Stacks.Hilbert.ChartAlgebra.Univ W`.
* `Stacks.Hilbert.univFamily`: the universal family over it, the spectrum of the universal
  quotient algebra `C_univ`, free over `R_univ` on the `W_l`.

## Main results

* `Stacks.Hilbert.IsChart.injective`: over an affine base the chart map of a chart is injective.
* `Stacks.Hilbert.eq_of_isChart_of_coords`: over an affine base a chart is determined by the
  coordinates of the monomials.
* `Stacks.Hilbert.chartSubfunctor_representableBy`: `F_W` is representable by
  `Stacks.Hilbert.chartScheme`.

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-! ### A surjection onto a module of the same rank is bijective -/

/-- A surjective linear map `A^d → M` onto a finite locally free module of rank `d` is
bijective. -/
theorem bijective_of_surjective_of_isFiniteLocallyFreeOfRank {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] {d : ℕ} (h : Module.IsFiniteLocallyFreeOfRank A M d)
    (φ : (Fin d → A) →ₗ[A] M) (hs : Function.Surjective φ) : Function.Bijective φ := by
  have hlf : Module.IsFiniteLocallyFree A M := by
    obtain ⟨ι, f, hspan, hb⟩ := h
    exact ⟨ι, f, hspan, fun i ↦ ⟨.of_basis (hb i).some, .of_basis (hb i).some⟩⟩
  obtain ⟨hfin, hproj⟩ := Module.finite_and_projective_of_isFiniteLocallyFree hlf
  refine Module.bijective_of_surjective_of_rankAtStalk_eq hs fun m hm ↦ ?_
  have : Nontrivial A := ⟨⟨0, 1, fun h01 ↦ hm.ne_top (by
    rw [Ideal.eq_top_iff_one, ← h01]; exact m.zero_mem)⟩⟩
  rw [Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank d h, Module.rankAtStalk_eq_finrank_of_free,
    Module.finrank_fin_fun]
  rfl

/-! ### Charts over an affine base -/

variable {S : Scheme.{u}} {n : Type u} {d : ℕ}

/-- The chart map as a linear map, for the algebra structure given by the structure
morphism. -/
theorem chartMap_eq_linearCombination {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) (c : Fin d → Γ(T.left, ⊤)) :
    letI := Z.structural.appTop.hom.toAlgebra
    chartMap Z W c =
      Fintype.linearCombination Γ(T.left, ⊤)
        (fun l ↦ Z.toAmbient.appTop (polyFun S n (W l))) c := by
  let := Z.structural.appTop.hom.toAlgebra
  simp [chartMap, Fintype.linearCombination_apply, Algebra.smul_def]
  rfl

/-- **Over an affine base the chart map of a chart is injective.** -/
theorem IsChart.injective {T : Over S} [IsAffine T.left]
    {Z : HilbertFamily (affineSpaceOver S n) T d} {W : Fin d → MvPolynomial n Γ(S, ⊤)}
    (hZ : IsChart Z W) : Function.Injective (chartMap Z W) := by
  let := Z.structural.appTop.hom.toAlgebra
  have hlf : Module.IsFiniteLocallyFreeOfRank Γ(T.left, ⊤) Γ(Z.ideal.subscheme, ⊤) d :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine Z.structural d
      rfl).mp inferInstance
  have heq : chartMap Z W = Fintype.linearCombination Γ(T.left, ⊤)
      (fun l ↦ Z.toAmbient.appTop (polyFun S n (W l))) :=
    funext (chartMap_eq_linearCombination Z W)
  have hs : Function.Surjective (Fintype.linearCombination Γ(T.left, ⊤)
      (fun l ↦ Z.toAmbient.appTop (polyFun S n (W l)))) := heq ▸ hZ
  rw [heq]
  exact (bijective_of_surjective_of_isFiniteLocallyFreeOfRank hlf _ hs).1

/-- Scaling the coefficients of the chart map. -/
theorem chartMap_smul {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) (a : Γ(T.left, ⊤)) (c : Fin d → Γ(T.left, ⊤)) :
    chartMap Z W (a • c) = Z.structural.appTop a * chartMap Z W c := by
  simp [chartMap, Finset.mul_sum, mul_assoc]

/-- The chart map is additive in finite sums. -/
theorem chartMap_sum {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) {ι : Type*} (s : Finset ι)
    (c : ι → Fin d → Γ(T.left, ⊤)) :
    chartMap Z W (∑ i ∈ s, c i) = ∑ i ∈ s, chartMap Z W (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, chartMap_add, ih]

/-- The chart map on a standard basis vector is the corresponding `W_l|_Z`. -/
theorem chartMap_single {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) (l : Fin d) :
    chartMap Z W (Pi.single l 1) = Z.toAmbient.appTop (polyFun S n (W l)) := by
  classical
  rw [chartMap, Finset.sum_eq_single l (fun k _ hk ↦ by simp [hk])
    (by simp)]
  simp

/-- The global functions of `T` as an algebra over the global functions of `S`. -/
abbrev algebraOver (T : Over S) : Algebra Γ(S, ⊤) Γ(T.left, ⊤) :=
  T.hom.appTop.hom.toAlgebra

/-- The restriction of a polynomial to a family whose monomials have coordinates `v` is given
by the coordinates of the polynomial. -/
theorem toAmbient_polyFun_eq_chartMap {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) {v : (n →₀ ℕ) → Fin d → Γ(T.left, ⊤)}
    (hv : ∀ m, Z.toAmbient.appTop (monomialFun S n m) = chartMap Z W (v m))
    (P : MvPolynomial n Γ(S, ⊤)) :
    letI := algebraOver T
    Z.toAmbient.appTop (polyFun S n P) = chartMap Z W (ChartAlgebra.coordMap v P) := by
  let := algebraOver T
  induction P using MvPolynomial.induction_on' with
  | monomial m r =>
    have : polyFun S n (MvPolynomial.monomial m r) =
        (𝔸(n; S) ↘ S).appTop r * monomialFun S n m := by
      simp only [monomialFun, polyFun, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
        map_one, one_mul]
    rw [this, map_mul, toAmbient_appTop_over, hv, ChartAlgebra.coordMap_monomial,
      ← chartMap_smul]
    rfl
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, map_add, chartMap_add]

/-- **The coordinates of the monomials on a chart form a datum.** -/
theorem isDatum_of_isChart {T : Over S} [IsAffine T.left]
    {Z : HilbertFamily (affineSpaceOver S n) T d} {W : Fin d → MvPolynomial n Γ(S, ⊤)}
    (hZ : IsChart Z W) {v : (n →₀ ℕ) → Fin d → Γ(T.left, ⊤)}
    (hv : ∀ m, Z.toAmbient.appTop (monomialFun S n m) = chartMap Z W (v m)) :
    letI := algebraOver T
    ChartAlgebra.IsDatum W v := by
  let := algebraOver T
  refine ⟨fun l ↦ hZ.injective ?_, fun m m' ↦ hZ.injective ?_⟩
  · rw [← toAmbient_polyFun_eq_chartMap Z W hv, chartMap_single]
  · rw [← hv, chartMap_sum]
    simp only [chartMap_smul, ← toAmbient_polyFun_eq_chartMap Z W hv]
    have hmul : monomialFun S n (m + m') = monomialFun S n m * monomialFun S n m' := by
      rw [monomialFun, monomialFun, monomialFun, ← map_mul, MvPolynomial.monomial_mul_monomial,
        one_mul]
    rw [hmul, map_mul, hv m', chartMap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_mul, map_mul, ← mul_assoc, mul_comm (Z.toAmbient.appTop (monomialFun S n m)),
      mul_assoc, monomialFun]

/-- **A chart over an affine base is determined by the coordinates of the monomials.** Two
families over an affine `T` satisfying the chart condition, on which every monomial has the
same coordinates, coincide. -/
theorem eq_of_isChart_of_coords [IsAffine S] {T : Over S} [IsAffine T.left]
    {Z Z' : HilbertFamily (affineSpaceOver S n) T d} {W : Fin d → MvPolynomial n Γ(S, ⊤)}
    (hZ : IsChart Z W) (hZ' : IsChart Z' W) (v : (n →₀ ℕ) → Fin d → Γ(T.left, ⊤))
    (hv : ∀ m, Z.toAmbient.appTop (monomialFun S n m) = chartMap Z W (v m))
    (hv' : ∀ m, Z'.toAmbient.appTop (monomialFun S n m) = chartMap Z' W (v m)) : Z = Z' := by
  let := algebraOver T
  have : IsAffineHom (affineSpaceOver S n).hom := inferInstanceAs (IsAffineHom (𝔸(n; S) ↘ S))
  have : IsAffine ((Over.pullback T.hom).obj (affineSpaceOver S n)).left :=
    inferInstanceAs (IsAffine (pullback _ _))
  have hpo := isPushout_appTop_of_isPullback
    (IsPullback.of_hasPullback (𝔸(n; S) ↘ S) T.hom)
  have key (s : Γ(((Over.pullback T.hom).obj (affineSpaceOver S n)).left, ⊤)) :
      ∃ c, Z.ideal.subschemeι.appTop s = chartMap Z W c ∧
        Z'.ideal.subschemeι.appTop s = chartMap Z' W c := by
    induction mem_closure_of_isPushout hpo s using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨⟨c, b⟩, rfl⟩ := hx
      obtain ⟨P, rfl⟩ := polyFun_surjective S n b
      refine ⟨c • ChartAlgebra.coordMap v P, ?_, ?_⟩
      · show Z.ideal.subschemeι.appTop (_ * _) = _
        rw [map_mul, chartMap_smul, ← toAmbient_polyFun_eq_chartMap Z W hv]
        rfl
      · show Z'.ideal.subschemeι.appTop (_ * _) = _
        rw [map_mul, chartMap_smul, ← toAmbient_polyFun_eq_chartMap Z' W hv']
        rfl
    | zero => exact ⟨0, by rw [map_zero, chartMap_zero], by rw [map_zero, chartMap_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨cx, hx, hx'⟩ := hx
      obtain ⟨cy, hy, hy'⟩ := hy
      exact ⟨cx + cy, by rw [map_add, hx, hy, chartMap_add],
        by rw [map_add, hx', hy', chartMap_add]⟩
  refine HilbertFamily.ext ?_
  rw [← Z.ideal.ker_subschemeι, ← Z'.ideal.ker_subschemeι, Scheme.ker_of_isAffine,
    Scheme.ker_of_isAffine]
  congr 1
  ext s
  obtain ⟨c, hc, hc'⟩ := key s
  rw [RingHom.mem_ker, RingHom.mem_ker]
  show Z.ideal.subschemeι.appTop s = 0 ↔ Z'.ideal.subschemeι.appTop s = 0
  rw [hc, hc', ← chartMap_zero Z W, ← chartMap_zero Z' W, hZ.injective.eq_iff,
    hZ'.injective.eq_iff]

/-! ### The universal chart -/

section Universal

variable (S) [IsAffine S] (n) (d) (W : Fin d → MvPolynomial n Γ(S, ⊤))

/-- The inverse of `S ≅ Spec Γ(S, 𝒪_S)` acts on global sections as the inverse of
`Γ(Spec R, 𝒪) ≅ R`. -/
theorem isoSpec_inv_appTop_apply (r : Γ(S, ⊤)) :
    S.isoSpec.inv.appTop r = (Scheme.ΓSpecIso Γ(S, ⊤)).inv r := by
  have h' := congrArg (fun φ ↦ φ.appTop.hom r) S.isoSpec.hom_inv_id
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply, Scheme.isoSpec_hom,
    Scheme.toSpecΓ_appTop] at h'
  calc S.isoSpec.inv.appTop r
      = (Scheme.ΓSpecIso Γ(S, ⊤)).inv ((Scheme.ΓSpecIso Γ(S, ⊤)).hom
          (S.isoSpec.inv.appTop r)) := (Iso.hom_inv_id_apply _ _).symm
    _ = (Scheme.ΓSpecIso Γ(S, ⊤)).inv r := congrArg _ h'

/-- Pulling back a global function along composable morphisms is pulling back along their
composite. -/
private theorem appTop_apply_comp_of_eq {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (e : f ≫ g = h) (r : Γ(Z, ⊤)) : f.appTop (g.appTop r) = h.appTop r := by
  subst e
  rfl

/-- The spectrum of a ring map pulls `ΓSpecIso.inv` back to `ΓSpecIso.inv` of the image. -/
private theorem appTop_specMap_ΓSpecIso_inv {A B : CommRingCat.{u}} (φ : A ⟶ B) (x : A) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv x) = (Scheme.ΓSpecIso B).inv (φ x) :=
  (congrArg (fun ψ ↦ ψ.hom x) (Scheme.ΓSpecIso_inv_naturality φ)).symm

/-- The universal algebra `R_univ` of the chart attached to `W`, `R = Γ(S, 𝒪_S)`. -/
abbrev UnivRing : Type u := ChartAlgebra.Univ W

/-- The universal quotient algebra over `R_univ`, free on the `W_l`. -/
def UnivQuot : Type u := ChartAlgebra.Quot (B := ChartAlgebra.Univ W)
  (ChartAlgebra.isDatum_univVec W)

/-- The universal quotient algebra is a commutative ring. -/
instance : CommRing (UnivQuot S n d W) :=
  inferInstanceAs (CommRing (ChartAlgebra.Quot (ChartAlgebra.isDatum_univVec W)))

/-- The universal quotient algebra is an algebra over the universal algebra. -/
instance : Algebra (UnivRing S n d W) (UnivQuot S n d W) :=
  inferInstanceAs (Algebra (ChartAlgebra.Univ W)
    (ChartAlgebra.Quot (ChartAlgebra.isDatum_univVec W)))

/-- The universal datum, in `R_univ`. -/
def univVec : (n →₀ ℕ) → Fin d → UnivRing S n d W := ChartAlgebra.univVec W

/-- The quotient map `R_univ[x] → C_univ`. -/
def univMk : MvPolynomial n (UnivRing S n d W) →+* UnivQuot S n d W :=
  Ideal.Quotient.mk (ChartAlgebra.kerIdeal (ChartAlgebra.isDatum_univVec W))

omit [IsAffine S] in
/-- The quotient map onto the universal quotient algebra is surjective. -/
theorem univMk_surjective : Function.Surjective (univMk S n d W) :=
  Ideal.Quotient.mk_surjective

omit [IsAffine S] in
/-- Constants map to the image of the universal algebra. -/
theorem univMk_C (u : UnivRing S n d W) :
    univMk S n d W (MvPolynomial.C u) = algebraMap (UnivRing S n d W) (UnivQuot S n d W) u :=
  rfl

/-- The basis of `C_univ` over `R_univ` given by the `W_l`. -/
def univBasis : Module.Basis (Fin d) (UnivRing S n d W) (UnivQuot S n d W) :=
  ChartAlgebra.basis (B := ChartAlgebra.Univ W) (ChartAlgebra.isDatum_univVec W)

omit [IsAffine S] in
/-- In `C_univ` a monomial is the combination of the `W_l` given by the universal datum. -/
theorem univMk_monomial (m : n →₀ ℕ) :
    univMk S n d W (MvPolynomial.monomial m 1) =
      ∑ l, algebraMap (UnivRing S n d W) (UnivQuot S n d W) (univVec S n d W m l) *
        univMk S n d W (MvPolynomial.map (algebraMap Γ(S, ⊤) (UnivRing S n d W)) (W l)) := by
  have := ChartAlgebra.mk_eq_sum (B := ChartAlgebra.Univ W) (ChartAlgebra.isDatum_univVec W)
    (MvPolynomial.monomial m 1)
  rw [ChartAlgebra.coordMap'_monomial, one_smul] at this
  simp only [Algebra.smul_def] at this
  exact this

/-- The representing scheme of `F_W`: the spectrum of the universal algebra, over `S`. -/
abbrev chartScheme : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (UnivRing S n d W))) ≫ S.isoSpec.inv)

/-- The representing scheme is the spectrum of the universal algebra. -/
theorem chartScheme_left : (chartScheme S n d W).left = Spec (.of (UnivRing S n d W)) := rfl

/-- The representing scheme is affine. -/
instance : IsAffine (chartScheme S n d W).left := inferInstanceAs (IsAffine (Spec _))

/-- The structure morphism of the representing scheme pulls back functions through
`R → R_univ`. -/
theorem chartScheme_hom_appTop (r : Γ(S, ⊤)) :
    (chartScheme S n d W).hom.appTop r =
      (Scheme.ΓSpecIso (.of (UnivRing S n d W))).inv (algebraMap Γ(S, ⊤) _ r) := by
  show (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (UnivRing S n d W))) ≫
    S.isoSpec.inv).appTop r = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, isoSpec_inv_appTop_apply]
  exact appTop_specMap_ΓSpecIso_inv _ _

/-- The structure morphism of the universal family. -/
def univStructure : Spec (.of (UnivQuot S n d W)) ⟶ (chartScheme S n d W).left :=
  Spec.map (CommRingCat.ofHom (algebraMap (UnivRing S n d W) (UnivQuot S n d W)))

/-- The structure morphism pulls back functions on the base through `R_univ → C_univ`. -/
theorem univStructure_appTop (x : UnivRing S n d W) :
    (univStructure S n d W).appTop ((Scheme.ΓSpecIso (.of (UnivRing S n d W))).inv x) =
      (Scheme.ΓSpecIso (.of (UnivQuot S n d W))).inv
        (algebraMap (UnivRing S n d W) (UnivQuot S n d W) x) :=
  appTop_specMap_ΓSpecIso_inv (CommRingCat.ofHom (algebraMap (UnivRing S n d W) _)) x

/-- The coordinates of the universal family. -/
def univCoords (i : n) : Γ(Spec (.of (UnivQuot S n d W)), ⊤) :=
  (Scheme.ΓSpecIso (.of (UnivQuot S n d W))).inv (univMk S n d W (MvPolynomial.X i))

/-- The universal family, as a morphism to the ambient space. -/
def univAmbient : Spec (.of (UnivQuot S n d W)) ⟶ 𝔸(n; S) :=
  AffineSpace.homOfVector (univStructure S n d W ≫ (chartScheme S n d W).hom) (univCoords S n d W)

/-- The universal family pulls back polynomials to their classes in `C_univ`. -/
theorem univAmbient_appTop_polyFun (P : MvPolynomial n Γ(S, ⊤)) :
    (univAmbient S n d W).appTop (polyFun S n P) =
      (Scheme.ΓSpecIso (.of (UnivQuot S n d W))).inv
        (univMk S n d W (MvPolynomial.map (algebraMap Γ(S, ⊤) (UnivRing S n d W)) P)) := by
  have hC (r : Γ(S, ⊤)) : (univAmbient S n d W).appTop ((𝔸(n; S) ↘ S).appTop r) =
      (Scheme.ΓSpecIso (.of (UnivQuot S n d W))).inv (algebraMap (UnivRing S n d W)
        (UnivQuot S n d W) (algebraMap Γ(S, ⊤) (UnivRing S n d W) r)) := by
    rw [univAmbient, appTop_apply_comp_of_eq (AffineSpace.homOfVector_over
      (univStructure S n d W ≫ (chartScheme S n d W).hom) (univCoords S n d W)),
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, chartScheme_hom_appTop,
      univStructure_appTop]
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [polyFun, MvPolynomial.eval₂Hom_C, hC, MvPolynomial.map_C, univMk_C]
  | add P Q hP hQ =>
    rw [map_add, map_add, hP, hQ, map_add (MvPolynomial.map _), map_add, map_add]
  | mul_X P i hP =>
    rw [map_mul, map_mul, hP, map_mul, MvPolynomial.map_X, map_mul, map_mul]
    congr 1
    rw [polyFun, MvPolynomial.eval₂Hom_X', univAmbient, AffineSpace.homOfVector_appTop_coord,
      univCoords]

/-- The ambient scheme `𝔸(n; R_univ)` of the universal family. -/
abbrev univAmbientSpace : Scheme.{u} :=
  ((Over.pullback (chartScheme S n d W).hom).obj (affineSpaceOver S n)).left

/-- The universal family, as a morphism to `𝔸(n; R_univ)`. -/
def univImmersion : Spec (.of (UnivQuot S n d W)) ⟶ univAmbientSpace S n d W :=
  pullback.lift (univAmbient S n d W) (univStructure S n d W) (AffineSpace.homOfVector_over _ _)

/-- The universal immersion followed by the projection to `𝔸(n; S)`. -/
theorem univImmersion_fst :
    univImmersion S n d W ≫ familyProjection _ _ = univAmbient S n d W :=
  pullback.lift_fst _ _ _

/-- The universal immersion followed by the projection to the base. -/
theorem univImmersion_snd : univImmersion S n d W ≫
    ((Over.pullback (chartScheme S n d W).hom).obj (affineSpaceOver S n)).hom =
      univStructure S n d W :=
  pullback.lift_snd _ _ _

/-- The universal family is a closed subscheme of `𝔸(n; R_univ)`. -/
instance isClosedImmersion_univImmersion : IsClosedImmersion (univImmersion S n d W) := by
  have : IsAffineHom (affineSpaceOver S n).hom := inferInstanceAs (IsAffineHom (𝔸(n; S) ↘ S))
  have : IsAffine (univAmbientSpace S n d W) := inferInstanceAs (IsAffine (pullback _ _))
  refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
  have hmem (c : UnivQuot S n d W) : (Scheme.ΓSpecIso (.of (UnivQuot S n d W))).inv c ∈
      (univImmersion S n d W).appTop.hom.range := by
    obtain ⟨p, rfl⟩ := univMk_surjective S n d W c
    induction p using MvPolynomial.induction_on with
    | C u =>
      refine ⟨((Over.pullback (chartScheme S n d W).hom).obj (affineSpaceOver S n)).hom.appTop
        ((Scheme.ΓSpecIso (.of (UnivRing S n d W))).inv u), ?_⟩
      have := congrArg (fun φ ↦ φ.appTop.hom ((Scheme.ΓSpecIso (.of (UnivRing S n d W))).inv u))
        (univImmersion_snd S n d W)
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [univMk_C, ← univStructure_appTop, ← this]
    | add p q hp hq =>
      rw [map_add, map_add]
      exact (univImmersion S n d W).appTop.hom.range.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, map_mul]
      refine (univImmersion S n d W).appTop.hom.range.mul_mem hp
        ⟨(familyProjection _ _).appTop (AffineSpace.coord S i), ?_⟩
      have := congrArg (fun φ ↦ φ.appTop.hom (AffineSpace.coord S i))
        (univImmersion_fst S n d W)
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
      change (univImmersion S n d W).appTop.hom _ = _
      rw [this, univAmbient, AffineSpace.homOfVector_appTop_coord, univCoords]
  intro y
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
    (.of (UnivQuot S n d W))).inv).2 y
  exact hmem c

/-- The structure morphism of the universal family is finite locally free of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_univStructure :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (univStructure S n d W) d :=
  (Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_iff_module _ _ d).mpr
    (Module.isFiniteLocallyFreeOfRank_of_basis (univBasis S n d W))

/-- **The universal family** over the representing scheme of `F_W`. -/
def univFamily : HilbertFamily (affineSpaceOver S n) (chartScheme S n d W) d where
  ideal := (univImmersion S n d W).ker
  isFiniteLocallyFreeOfRank := by
    have hfac : (univImmersion S n d W).ker.subschemeι ≫
        ((Over.pullback (chartScheme S n d W).hom).obj (affineSpaceOver S n)).hom =
          (asIso (univImmersion S n d W).toImage).symm.hom ≫ univStructure S n d W := by
      rw [← univImmersion_snd, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc]
      exact congrArg (· ≫ _) (Scheme.Hom.toImage_imageι _)
    rw [hfac]
    exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp _ _
      (isFiniteLocallyFreeOfRank_univStructure S n d W)

end Universal

/-! ### The universal family is a chart -/

section UniversalChart

variable (S) [IsAffine S] (n) (d) (W : Fin d → MvPolynomial n Γ(S, ⊤))

/-- The universal coordinates, as functions on the representing scheme. -/
def univCoordFun (m : n →₀ ℕ) (l : Fin d) : Γ((chartScheme S n d W).left, ⊤) :=
  (Scheme.ΓSpecIso (.of (UnivRing S n d W))).inv (univVec S n d W m l)

/-- The identification of the universal family with `Spec C_univ`. -/
abbrev univIso : Spec (.of (UnivQuot S n d W)) ⟶ (univFamily S n d W).ideal.subscheme :=
  (univImmersion S n d W).toImage

/-- The universal family is identified with `Spec C_univ`. -/
instance : IsIso (univIso S n d W) :=
  inferInstanceAs (IsIso (univImmersion S n d W).toImage)

/-- Under `univIso`, the structure morphism is the one of `Spec C_univ`. -/
theorem univIso_structural :
    univIso S n d W ≫ (univFamily S n d W).structural = univStructure S n d W := by
  rw [HilbertFamily.structural, ← Category.assoc]
  exact (congrArg (· ≫ _) (Scheme.Hom.toImage_imageι _)).trans (univImmersion_snd S n d W)

/-- Under `univIso`, the ambient projection is `univAmbient`. -/
theorem univIso_toAmbient :
    univIso S n d W ≫ (univFamily S n d W).toAmbient = univAmbient S n d W := by
  rw [HilbertFamily.toAmbient, ← Category.assoc]
  exact (congrArg (· ≫ _) (Scheme.Hom.toImage_imageι _)).trans (univImmersion_fst S n d W)

/-- Under `univIso`, functions on the ambient space pull back to the ones along `univAmbient`. -/
private theorem univIso_appTop_toAmbient_appTop (x : Γ(𝔸(n; S), ⊤)) :
    (univIso S n d W).appTop ((univFamily S n d W).toAmbient.appTop x) =
      (univAmbient S n d W).appTop x :=
  appTop_apply_comp_of_eq (univIso_toAmbient S n d W) x

/-- The chart map of the universal family, read in `C_univ`. -/
theorem univIso_appTop_chartMap (c : Fin d → UnivRing S n d W) :
    (univIso S n d W).appTop (chartMap (univFamily S n d W) W
      (fun l ↦ (Scheme.ΓSpecIso (.of (UnivRing S n d W))).inv (c l))) =
      (Scheme.ΓSpecIso (.of (UnivQuot S n d W))).inv (∑ l, algebraMap _ (UnivQuot S n d W) (c l) *
        univMk S n d W (MvPolynomial.map (algebraMap Γ(S, ⊤) (UnivRing S n d W)) (W l))) := by
  simp only [chartMap, map_sum, map_mul, univIso_appTop_toAmbient_appTop,
    univAmbient_appTop_polyFun]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [appTop_apply_comp_of_eq (univIso_structural S n d W), univStructure_appTop]

/-- **The universal family satisfies the chart condition.** -/
theorem isChart_univFamily : IsChart (univFamily S n d W) W := by
  intro y
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
    (.of (UnivQuot S n d W))).inv).2 ((univIso S n d W).appTop y)
  refine ⟨fun l ↦ (Scheme.ΓSpecIso (.of (UnivRing S n d W))).inv
    ((univBasis S n d W).repr b l), (AffineLine.bijective_appTop_of_isIso (univIso S n d W)).1 ?_⟩
  rw [univIso_appTop_chartMap, ← hb]
  congr 1
  conv_rhs => rw [← (univBasis S n d W).sum_repr b]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Algebra.smul_def]
  congr 1
  exact (ChartAlgebra.basis_apply (B := ChartAlgebra.Univ W) _ l).symm

/-- On the universal family the monomials have the universal coordinates. -/
theorem univFamily_monomial (m : n →₀ ℕ) :
    (univFamily S n d W).toAmbient.appTop (monomialFun S n m) =
      chartMap (univFamily S n d W) W (univCoordFun S n d W m) := by
  refine (AffineLine.bijective_appTop_of_isIso (univIso S n d W)).1 ?_
  rw [univIso_appTop_toAmbient_appTop, show univCoordFun S n d W m = fun l ↦
    (Scheme.ΓSpecIso (.of (UnivRing S n d W))).inv (univVec S n d W m l) from rfl,
    univIso_appTop_chartMap, monomialFun,
    univAmbient_appTop_polyFun,
    MvPolynomial.map_monomial, map_one, univMk_monomial]

end UniversalChart

/-! ### Morphisms to the representing scheme -/

section Classify

variable [IsAffine S] {W : Fin d → MvPolynomial n Γ(S, ⊤)}

/-- The universal family lies in `F_W`. -/
theorem univFamily_mem :
    univFamily S n d W ∈ (chartSubfunctor S n d W).obj (Opposite.op (chartScheme S n d W)) :=
  fun _ h _ _ ↦ (isChart_univFamily S n d W).baseChange h

/-- The base change of the universal family along a morphism to the representing scheme has, on
its monomials, the pulled back universal coordinates. -/
theorem baseChange_univFamily_monomial {T : Over S} (f : T ⟶ chartScheme S n d W)
    (m : n →₀ ℕ) :
    (baseChange _ f (univFamily S n d W)).toAmbient.appTop (monomialFun S n m) =
      chartMap (baseChange _ f (univFamily S n d W)) W
        (fun l ↦ f.left.appTop (univCoordFun S n d W m l)) := by
  rw [← baseChangeMap_appTop_chartMap, ← univFamily_monomial, baseChangeMap_appTop_toAmbient]

/-- The map on global sections `R_univ → Γ(T, 𝒪_T)` of a morphism to the representing
scheme. -/
def classify {T : Over S} (f : T ⟶ chartScheme S n d W) : UnivRing S n d W →+* Γ(T.left, ⊤) :=
  f.left.appTop.hom.comp (Scheme.ΓSpecIso (.of (UnivRing S n d W))).inv.hom

/-- The classifying map of a morphism over `S` is a map of `Γ(S, 𝒪_S)`-algebras. -/
theorem classify_algebraMap {T : Over S} (f : T ⟶ chartScheme S n d W) (r : Γ(S, ⊤)) :
    classify f (algebraMap Γ(S, ⊤) _ r) = T.hom.appTop r := by
  rw [← appTop_apply_comp_of_eq (Over.w f), chartScheme_hom_appTop]
  rfl

/-- The map on global sections of a morphism to the representing scheme, as an algebra map. -/
def classifyₐ {T : Over S} (f : T ⟶ chartScheme S n d W) :
    letI := algebraOver T
    UnivRing S n d W →ₐ[Γ(S, ⊤)] Γ(T.left, ⊤) :=
  letI := algebraOver T
  { classify f with commutes' := classify_algebraMap f }

/-- A morphism from a scheme to the representing scheme is determined by its classifying map. -/
theorem eq_of_classify_eq {T : Over S} {f f' : T ⟶ chartScheme S n d W}
    (h : ∀ m l, classify f (univVec S n d W m l) = classify f' (univVec S n d W m l)) :
    f = f' := by
  let := algebraOver T
  have h' : classifyₐ f = classifyₐ f' := ChartAlgebra.algHom_ext W h
  refine Over.OverMorphism.ext (ext_of_isAffine ?_)
  ext x
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (UnivRing S n d W))).inv).2 x
  exact congrArg (fun φ : UnivRing S n d W →ₐ[Γ(S, ⊤)] Γ(T.left, ⊤) ↦ φ y) h'

/-- The morphism to the representing scheme classified by a map `R_univ → Γ(T, 𝒪_T)` of
`R`-algebras. -/
def ofClassify {T : Over S} (φ : UnivRing S n d W →+* Γ(T.left, ⊤))
    (hφ : ∀ r, φ (algebraMap Γ(S, ⊤) _ r) = T.hom.appTop r) : T ⟶ chartScheme S n d W :=
  Over.homMk (T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) (by
    refine ext_of_isAffine ?_
    ext r
    change (T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫
      (chartScheme S n d W).hom).appTop r = T.hom.appTop r
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply, chartScheme_hom_appTop]
    have := congrArg (fun ψ ↦ ψ.hom (algebraMap Γ(S, ⊤) (UnivRing S n d W) r))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [← this, Scheme.toSpecΓ_appTop]
    exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(T.left, ⊤)) _).trans (hφ r))

/-- The morphism classified by a ring map has that ring map as its classifying map. -/
theorem classify_ofClassify {T : Over S} (φ : UnivRing S n d W →+* Γ(T.left, ⊤))
    (hφ : ∀ r, φ (algebraMap Γ(S, ⊤) _ r) = T.hom.appTop r) (x : UnivRing S n d W) :
    classify (ofClassify φ hφ) x = φ x := by
  show (T.left.toSpecΓ ≫ Spec.map _).appTop
    ((Scheme.ΓSpecIso (.of (UnivRing S n d W))).inv x) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_specMap_ΓSpecIso_inv,
    Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(T.left, ⊤)) _

/-- **Injectivity over an affine base.** Over an affine `T`, morphisms to the representing scheme
with the same base change of the universal family coincide. -/
theorem eq_of_baseChange_univFamily_eq {T : Over S} [IsAffine T.left]
    {f f' : T ⟶ chartScheme S n d W}
    (h : baseChange _ f (univFamily S n d W) = baseChange _ f' (univFamily S n d W)) : f = f' := by
  have hchart : IsChart (baseChange _ f (univFamily S n d W)) W :=
    isChart_of_mem_chartSubfunctor ((chartSubfunctor S n d W).map f.op univFamily_mem)
  refine eq_of_classify_eq fun m l ↦ ?_
  have e := baseChange_univFamily_monomial f' m
  rw [← h, baseChange_univFamily_monomial f m] at e
  exact congrFun (hchart.injective e) l

/-- **Surjectivity over an affine base.** Over an affine `T`, every family in `F_W(T)` is the
base change of the universal family along a morphism to the representing scheme. -/
theorem exists_baseChange_univFamily_eq {T : Over S} [IsAffine T.left]
    {Z : HilbertFamily (affineSpaceOver S n) T d}
    (hZ : Z ∈ (chartSubfunctor S n d W).obj (Opposite.op T)) :
    ∃ f : T ⟶ chartScheme S n d W, baseChange _ f (univFamily S n d W) = Z := by
  let := algebraOver T
  have hchart := isChart_of_mem_chartSubfunctor hZ
  have hsurj : ∀ m, ∃ c : Fin d → Γ(T.left, ⊤),
      chartMap Z W c = Z.toAmbient.appTop (monomialFun S n m) :=
    fun m ↦ hchart _
  choose v hv using hsurj
  have hdat : ChartAlgebra.IsDatum W v := isDatum_of_isChart hchart fun m ↦ (hv m).symm
  let φ := ChartAlgebra.lift W v hdat
  let f := ofClassify (S := S) (n := n) (d := d) (W := W) φ.toRingHom φ.commutes
  refine ⟨f, ?_⟩
  have hchart' : IsChart (baseChange _ f (univFamily S n d W)) W :=
    isChart_of_mem_chartSubfunctor ((chartSubfunctor S n d W).map f.op univFamily_mem)
  refine eq_of_isChart_of_coords hchart' hchart v (fun m ↦ ?_) fun m ↦ (hv m).symm
  rw [baseChange_univFamily_monomial]
  congr 1
  funext l
  show classify f (univVec S n d W m l) = v m l
  rw [classify_ofClassify]
  exact ChartAlgebra.lift_univVec W v hdat m l

end Classify

/-! ### Representability -/

section Represent

variable [IsAffine S] {W : Fin d → MvPolynomial n Γ(S, ⊤)}

/-- The affine open cover of a scheme over `S`, piece by piece as schemes over `S`. -/
abbrev coverOver (T : Over S) (j : T.left.affineCover.I₀) : Over S :=
  Over.mk (T.left.affineCover.f j ≫ T.hom)

/-- The inclusion of a piece of the affine open cover, as a morphism over `S`. -/
abbrev coverHom (T : Over S) (j : T.left.affineCover.I₀) : coverOver T j ⟶ T :=
  Over.homMk (T.left.affineCover.f j) rfl

/-- The pieces of the affine open cover are affine. -/
instance (T : Over S) (j : T.left.affineCover.I₀) : IsAffine (coverOver T j).left :=
  inferInstanceAs (IsAffine (T.left.affineCover.X j))

/-- **Injectivity.** Morphisms to the representing scheme with the same base change of the
universal family coincide. -/
theorem eq_of_baseChange_univFamily_eq' {T : Over S} {f f' : T ⟶ chartScheme S n d W}
    (h : baseChange _ f (univFamily S n d W) = baseChange _ f' (univFamily S n d W)) :
    f = f' := by
  refine Over.OverMorphism.ext (T.left.affineCover.hom_ext _ _ fun j ↦ ?_)
  exact congrArg CommaMorphism.left (eq_of_baseChange_univFamily_eq
    (f := coverHom T j ≫ f) (f' := coverHom T j ≫ f') (by rw [baseChange_comp, baseChange_comp, h]))

/-- **Surjectivity.** Every family in `F_W(T)` is the base change of the universal family along
a morphism to the representing scheme. -/
theorem exists_baseChange_univFamily_eq' {T : Over S}
    {Z : HilbertFamily (affineSpaceOver S n) T d}
    (hZ : Z ∈ (chartSubfunctor S n d W).obj (Opposite.op T)) :
    ∃ f : T ⟶ chartScheme S n d W, baseChange _ f (univFamily S n d W) = Z := by
  set 𝒰 := T.left.affineCover
  have hZj (j : 𝒰.I₀) := exists_baseChange_univFamily_eq
    ((chartSubfunctor S n d W).map (coverHom T j).op hZ)
  choose fj hfj using hZj
  have hcompat (j k : 𝒰.I₀) : pullback.fst (𝒰.f j) (𝒰.f k) ≫ (fj j).left =
      pullback.snd (𝒰.f j) (𝒰.f k) ≫ (fj k).left := by
    let P : Over S := Over.mk (pullback.fst (𝒰.f j) (𝒰.f k) ≫ 𝒰.f j ≫ T.hom)
    let p₁ : P ⟶ coverOver T j := Over.homMk (pullback.fst _ _) rfl
    let p₂ : P ⟶ coverOver T k := Over.homMk (pullback.snd _ _) (by
      show pullback.snd (𝒰.f j) (𝒰.f k) ≫ 𝒰.f k ≫ T.hom =
        pullback.fst (𝒰.f j) (𝒰.f k) ≫ 𝒰.f j ≫ T.hom
      rw [pullback.condition_assoc])
    have hp : p₁ ≫ coverHom T j = p₂ ≫ coverHom T k :=
      Over.OverMorphism.ext pullback.condition
    exact congrArg CommaMorphism.left
      (eq_of_baseChange_univFamily_eq' (f := p₁ ≫ fj j) (f' := p₂ ≫ fj k) (by
        rw [baseChange_comp, baseChange_comp, hfj, hfj]
        show baseChange _ p₁ (baseChange _ (coverHom T j) Z) =
          baseChange _ p₂ (baseChange _ (coverHom T k) Z)
        rw [← baseChange_comp, ← baseChange_comp, hp]))
  let g : T.left ⟶ (chartScheme S n d W).left := 𝒰.glueMorphisms (fun j ↦ (fj j).left) hcompat
  have hg (j : 𝒰.I₀) : 𝒰.f j ≫ g = (fj j).left := 𝒰.ι_glueMorphisms _ hcompat j
  have hgS : g ≫ (chartScheme S n d W).hom = T.hom := 𝒰.hom_ext _ _ fun j ↦ by
    rw [reassoc_of% (hg j)]
    exact Over.w (fj j)
  let f : T ⟶ chartScheme S n d W := Over.homMk g hgS
  refine ⟨f, hilbertFamily_ext_of_baseChange_eq _ (coverHom T) (fun j ↦ inferInstanceAs
    (Flat (𝒰.f j))) (fun t ↦ ⟨𝒰.idx t, 𝒰.covers t⟩) fun j ↦ ?_⟩
  have hf : coverHom T j ≫ f = fj j := Over.OverMorphism.ext (hg j)
  rw [← baseChange_comp, hf, hfj]
  rfl

/-- **Representability of the charts.** For `S` affine, the subfunctor `F_W` of the
degree-`d` Hilbert functor of `𝔸(n; S)` is representable by an affine scheme over `S`, the
spectrum of the universal algebra of a commutative algebra free on the `W_l`. -/
theorem chartSubfunctor_representableBy (W : Fin d → MvPolynomial n Γ(S, ⊤)) :
    ∃ H : Over S, Nonempty ((chartSubfunctor S n d W).toFunctor.RepresentableBy H) := by
  refine ⟨chartScheme S n d W, ⟨{
    homEquiv := Equiv.ofBijective
      (fun f ↦ ⟨baseChange _ f (univFamily S n d W),
        (chartSubfunctor S n d W).map f.op univFamily_mem⟩)
      ⟨fun f f' h ↦ eq_of_baseChange_univFamily_eq' (congrArg Subtype.val h),
        fun Z ↦ (exists_baseChange_univFamily_eq' Z.2).imp fun f hf ↦ Subtype.ext hf⟩
    homEquiv_comp := fun f g ↦ Subtype.ext (baseChange_comp _ f g _) }⟩⟩

end Represent

end Stacks.Hilbert

end
