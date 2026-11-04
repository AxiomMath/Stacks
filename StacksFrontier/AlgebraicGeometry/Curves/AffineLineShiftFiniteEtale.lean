module

public import StacksFrontier.AlgebraicGeometry.Curves.AffineLineBasicOpenCurve
public import StacksFrontier.RingTheory.Etale.ResidueFieldColimit
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Every open of the affine line is finite étale over the affine line

Let `k` be a field of characteristic `p > 0` and `g ∈ k[X]` monic. The `k`-algebra map

`k[y] ⟶ k[x]_g,  y ↦ x + g(x)^{-p}`

is finite étale: with `s = -g(x)⁻¹` one has `x = y + s^p`, so `k[x]_g` is generated over `k[y]` by
`s`, a root of the monic polynomial `F(T) = T · g(y + T^p) + 1`, and `k[x]_g ≅ k[y][T]/(F)`
(`Stacks.GenericFiniteEtale.affineLineShiftEquiv`). Since `p = 0` in `k`, the derivative of `F` is
`g(y + T^p)`, a unit modulo `F`, so `k[y][T]/(F)` is finite étale over `k[y]`.

Every open `U` of `𝔸¹_k` is a basic open `D(g)` (`k[X]` is a principal ideal domain), so `U` is
finite étale over `𝔸¹_k` (`Stacks.GenericFiniteEtale.exists_finite_etale_affineLine`).

## Main definitions

* `Stacks.GenericFiniteEtale.affineLineShift`: `y ↦ x + g(x)^{-p}`.

## Main results

* `Stacks.GenericFiniteEtale.finite_affineLineShift`: for `g` monic, `affineLineShift` is finite.
* `Stacks.GenericFiniteEtale.etale_affineLineShift`: for `g` monic, `affineLineShift` is étale.
* `Stacks.GenericFiniteEtale.exists_finite_etale_affineLine`: every nonempty open of `𝔸¹_k` is
  finite étale over `𝔸¹_k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace Stacks.GenericFiniteEtale

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- `(-a)^p = -a^p` in a ring receiving a ring map from a field of characteristic `p`. -/
theorem neg_pow_char_of_ringHom {A : Type*} [CommRing A] (i : k →+* A) (a : A) :
    (-a) ^ p = -a ^ p := by
  rw [neg_pow, ← map_one i, ← map_neg i, ← map_pow i, neg_one_pow_char k p, map_neg,
    map_one, neg_one_mul]

/-- **`y ↦ x + g(x)^{-p}`**, the `k`-algebra map `k[y] ⟶ k[x]_g`. -/
noncomputable def affineLineShift (g : k[X]) : k[X] →ₐ[k] Localization.Away g :=
  aeval (algebraMap k[X] (Localization.Away g) Polynomial.X + IsLocalization.Away.invSelf g ^ p)

/-- The polynomial `F(T) = T · g(y + T^p) + 1` over `k[y]`, of which `-g(x)⁻¹` is a root. -/
noncomputable def affineLineShiftPoly (g : k[X]) : k[X][X] :=
  Polynomial.X * (g.map C).comp (Polynomial.X ^ p + C Polynomial.X) + 1

variable {k p}

omit [CharP k p] in
/-- For `g` monic, the polynomial `F(T) = T · g(y + T^p) + 1` is monic. -/
theorem monic_affineLineShiftPoly {g : k[X]} (hg : g.Monic) :
    (affineLineShiftPoly k p g).Monic := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hq : (Polynomial.X ^ p + C (Polynomial.X : k[X]) : k[X][X]).Monic := monic_X_pow_add_C _ hp
  have hQ : ((g.map C).comp (Polynomial.X ^ p + C (Polynomial.X : k[X]))).Monic :=
    (hg.map C).comp hq (by rw [natDegree_X_pow_add_C]; exact hp)
  refine (monic_X.mul hQ).add_of_left ?_
  rw [degree_one, hQ.degree_mul, degree_X, degree_eq_natDegree hQ.ne_zero]
  exact_mod_cast Nat.zero_lt_one.trans_le (Nat.le_add_right 1 _)

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- The evaluation of `g(y + T^p)` at `t`. -/
theorem eval₂_comp_affineLineShiftPoly {S : Type*} [CommRing S] (φ : k[X] →+* S) (t : S)
    (g : k[X]) :
    ((g.map C).comp (Polynomial.X ^ p + C Polynomial.X)).eval₂ φ t =
      g.eval₂ (φ.comp C) (t ^ p + φ Polynomial.X) := by
  rw [eval₂_comp, eval₂_map]
  simp

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- The evaluation of `F(T) = T · g(y + T^p) + 1` at `t` is `t · g(t^p + y) + 1`. -/
theorem eval₂_affineLineShiftPoly {S : Type*} [CommRing S] (φ : k[X] →+* S) (t : S)
    (g : k[X]) :
    (affineLineShiftPoly k p g).eval₂ φ t =
      t * g.eval₂ (φ.comp C) (t ^ p + φ Polynomial.X) + 1 := by
  rw [affineLineShiftPoly, eval₂_add, eval₂_mul, eval₂_X, eval₂_one,
    eval₂_comp_affineLineShiftPoly]

omit [Fact (Nat.Prime p)] in
/-- The derivative of `F` is `g(y + T^p)`, since `p = 0` in `k`. -/
theorem derivative_affineLineShiftPoly (g : k[X]) :
    derivative (affineLineShiftPoly k p g) =
      (g.map C).comp (Polynomial.X ^ p + C Polynomial.X) := by
  rw [affineLineShiftPoly, derivative_add, derivative_one, add_zero, derivative_mul,
    derivative_X, one_mul, derivative_comp, derivative_add, derivative_C, add_zero,
    derivative_X_pow, CharP.cast_eq_zero k[X] p, map_zero, zero_mul, zero_mul, mul_zero, add_zero]

variable (k p) in
/-- The map `k[x]_g ⟶ k[y][T]/(F)`, `x ↦ y + T^p`, inverse to the evaluation at `-g(x)⁻¹`. -/
noncomputable def affineLineShiftInvAux (g : k[X]) :
    k[X] →+* AdjoinRoot (affineLineShiftPoly k p g) :=
  eval₂RingHom ((AdjoinRoot.of _).comp C) (AdjoinRoot.root _ ^ p + AdjoinRoot.of _ Polynomial.X)

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- In `k[y][T]/(F)`, the root `T` times the image of `g` under `x ↦ y + T^p` is `-1`. -/
theorem root_mul_affineLineShiftInvAux (g : k[X]) :
    AdjoinRoot.root (affineLineShiftPoly k p g) * affineLineShiftInvAux k p g g = -1 := by
  have h := AdjoinRoot.eval₂_root (affineLineShiftPoly k p g)
  rw [eval₂_affineLineShiftPoly] at h
  rw [← sub_eq_zero, sub_neg_eq_add]
  exact h

/-- In `k[y][T]/(F)`, the image of `g` under `x ↦ y + T^p` times `-T` is `1`. -/
private theorem affineLineShiftInvAux_mul_neg_root {K : Type u} [Field K] {q : ℕ} (g : K[X]) :
    affineLineShiftInvAux K q g g * -AdjoinRoot.root (affineLineShiftPoly K q g) = 1 := by
  rw [mul_neg, mul_comm, root_mul_affineLineShiftInvAux, neg_neg]

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- The map `affineLineShift` sends `y` to `x + g(x)^{-p}`. -/
theorem affineLineShift_X (g : k[X]) :
    affineLineShift k p g Polynomial.X =
      algebraMap k[X] (Localization.Away g) Polynomial.X + IsLocalization.Away.invSelf g ^ p :=
  aeval_X _

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- On constants, the map `affineLineShift` is the algebra map of `k`. -/
theorem affineLineShift_comp_C (g : k[X]) :
    (affineLineShift k p g).toRingHom.comp C = algebraMap k (Localization.Away g) :=
  RingHom.ext fun a => by simp [affineLineShift]

/-- For a `k[X]`-algebra `S` compatible with `k`, evaluating `g` at the image of `X` gives the
image of `g`. -/
theorem eval₂_algebraMap_X {S : Type*} [CommRing S] [Algebra k[X] S] [Algebra k S]
    [IsScalarTower k k[X] S] (g : k[X]) :
    g.eval₂ (algebraMap k S) (algebraMap k[X] S Polynomial.X) = algebraMap k[X] S g := by
  rw [IsScalarTower.algebraMap_eq k k[X] S, ← hom_eval₂, algebraMap_eq, eval₂_C_X]

/-- `-g(x)⁻¹` is a root of `F` in `k[x]_g`, along `affineLineShift`. -/
theorem eval₂_affineLineShiftPoly_neg_invSelf (g : k[X]) :
    (affineLineShiftPoly k p g).eval₂ (affineLineShift k p g).toRingHom
      (-IsLocalization.Away.invSelf g) = 0 := by
  rw [eval₂_affineLineShiftPoly, affineLineShift_comp_C,
    neg_pow_char_of_ringHom k p (algebraMap k _)]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, affineLineShift_X]
  rw [show -IsLocalization.Away.invSelf g ^ p +
      (algebraMap k[X] (Localization.Away g) Polynomial.X + IsLocalization.Away.invSelf g ^ p) =
      algebraMap k[X] (Localization.Away g) Polynomial.X by ring,
    eval₂_algebraMap_X, neg_mul, mul_comm, IsLocalization.Away.mul_invSelf, neg_add_cancel]

variable (k p) in
/-- The evaluation `k[y][T]/(F) ⟶ k[x]_g` at `T = -g(x)⁻¹`. -/
noncomputable def affineLineShiftLift (g : k[X]) :
    AdjoinRoot (affineLineShiftPoly k p g) →+* Localization.Away g :=
  AdjoinRoot.lift (affineLineShift k p g).toRingHom (-IsLocalization.Away.invSelf g)
    (eval₂_affineLineShiftPoly_neg_invSelf g)

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- The image of `g` under `x ↦ y + T^p` is a unit in `k[y][T]/(F)`. -/
theorem isUnit_affineLineShiftInvAux (g : k[X]) : IsUnit (affineLineShiftInvAux k p g g) :=
  IsUnit.of_mul_eq_one _ (affineLineShiftInvAux_mul_neg_root g)

variable (k p) in
/-- The map `k[x]_g ⟶ k[y][T]/(F)`, `x ↦ y + T^p`. -/
noncomputable def affineLineShiftInv (g : k[X]) :
    Localization.Away g →+* AdjoinRoot (affineLineShiftPoly k p g) :=
  IsLocalization.Away.lift g (isUnit_affineLineShiftInvAux g)

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- `affineLineShiftInv` extends `affineLineShiftInvAux` along `k[x] ⟶ k[x]_g`. -/
theorem affineLineShiftInv_algebraMap (g a : k[X]) :
    affineLineShiftInv k p g (algebraMap k[X] _ a) = affineLineShiftInvAux k p g a :=
  IsLocalization.Away.lift_eq _ _ _

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- `affineLineShiftInv` sends `g(x)⁻¹` to `-T`. -/
theorem affineLineShiftInv_invSelf (g : k[X]) :
    affineLineShiftInv k p g (IsLocalization.Away.invSelf g) = -AdjoinRoot.root _ := by
  have h1 : affineLineShiftInvAux k p g g *
      affineLineShiftInv k p g (IsLocalization.Away.invSelf g) = 1 := by
    rw [← affineLineShiftInv_algebraMap, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  exact (isUnit_affineLineShiftInvAux g).mul_left_cancel
    (h1.trans (affineLineShiftInvAux_mul_neg_root g).symm)

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- `affineLineShiftInvAux` sends a constant `a` to its image in `k[y][T]/(F)`. -/
theorem affineLineShiftInvAux_C (g : k[X]) (a : k) :
    affineLineShiftInvAux k p g (C a) = AdjoinRoot.of _ (C a) := by
  simp [affineLineShiftInvAux]

omit [Fact (Nat.Prime p)] [CharP k p] in
/-- `affineLineShiftInvAux` sends `x` to `T^p + y`. -/
theorem affineLineShiftInvAux_X (g : k[X]) :
    affineLineShiftInvAux k p g Polynomial.X =
      AdjoinRoot.root _ ^ p + AdjoinRoot.of _ Polynomial.X := by
  simp [affineLineShiftInvAux]

/-- `affineLineShiftLift` is a left inverse of `affineLineShiftInv`. -/
theorem affineLineShiftLift_comp_affineLineShiftInv (g : k[X]) :
    (affineLineShiftLift k p g).comp (affineLineShiftInv k p g) = RingHom.id _ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers g) (Polynomial.ringHom_ext (fun a => ?_) ?_)
  · simp only [RingHom.comp_apply, affineLineShiftInv_algebraMap, affineLineShiftInvAux_C,
      affineLineShiftLift, AdjoinRoot.lift_of, RingHom.id_apply]
    exact congr($(affineLineShift_comp_C (p := p) g) a).trans
      (IsScalarTower.algebraMap_apply k k[X] _ a)
  · simp only [RingHom.comp_apply, affineLineShiftInv_algebraMap, affineLineShiftInvAux_X,
      affineLineShiftLift, map_add, map_pow, AdjoinRoot.lift_root, AdjoinRoot.lift_of,
      RingHom.id_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, affineLineShift_X,
      neg_pow_char_of_ringHom k p (algebraMap k (Localization.Away g))]
    ring

/-- `affineLineShiftInv` composed with `affineLineShift` is the map `k[y] ⟶ k[y][T]/(F)`. -/
theorem affineLineShiftInv_comp_affineLineShift (g : k[X]) :
    (affineLineShiftInv k p g).comp (affineLineShift k p g).toRingHom = AdjoinRoot.of _ := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · rw [RingHom.comp_apply, ← RingHom.comp_apply _ C, affineLineShift_comp_C,
      IsScalarTower.algebraMap_apply k k[X] (Localization.Away g), affineLineShiftInv_algebraMap,
      algebraMap_eq, affineLineShiftInvAux_C]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, affineLineShift_X,
      map_add, map_pow, affineLineShiftInv_algebraMap, affineLineShiftInvAux_X,
      affineLineShiftInv_invSelf,
      neg_pow_char_of_ringHom k p ((AdjoinRoot.of (affineLineShiftPoly k p g)).comp C)]
    ring

/-- `affineLineShiftInv` is a left inverse of `affineLineShiftLift`. -/
theorem affineLineShiftInv_comp_affineLineShiftLift (g : k[X]) :
    (affineLineShiftInv k p g).comp (affineLineShiftLift k p g) = RingHom.id _ := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, show (affineLineShiftLift k p g).comp (AdjoinRoot.of _) =
        (affineLineShift k p g).toRingHom from
        RingHom.ext fun r => AdjoinRoot.lift_of (eval₂_affineLineShiftPoly_neg_invSelf g),
      affineLineShiftInv_comp_affineLineShift, RingHom.id_comp]
  · simp [affineLineShiftLift, AdjoinRoot.lift_root, affineLineShiftInv_invSelf]

variable (k p) in
/-- **`k[x]_g ≅ k[y][T]/(T · g(y + T^p) + 1)`**, `T ↦ -g(x)⁻¹`, `y ↦ x + g(x)^{-p}`. -/
noncomputable def affineLineShiftEquiv (g : k[X]) :
    AdjoinRoot (affineLineShiftPoly k p g) ≃+* Localization.Away g :=
  RingEquiv.ofRingHom (affineLineShiftLift k p g) (affineLineShiftInv k p g)
    (affineLineShiftLift_comp_affineLineShiftInv g) (affineLineShiftInv_comp_affineLineShiftLift g)

/-- `affineLineShiftEquiv` composed with `k[y] ⟶ k[y][T]/(F)` is `affineLineShift`. -/
theorem affineLineShiftEquiv_comp_algebraMap (g : k[X]) :
    (affineLineShiftEquiv k p g).toRingHom.comp (algebraMap k[X] _) =
      (affineLineShift k p g).toRingHom :=
  RingHom.ext fun _ => AdjoinRoot.lift_of (eval₂_affineLineShiftPoly_neg_invSelf g)

/-- **`y ↦ x + g(x)^{-p}` is finite** for `g` monic: `k[x]_g` is `k[y][T]/(F)` with `F` monic. -/
theorem finite_affineLineShift {g : k[X]} (hg : g.Monic) :
    (affineLineShift k p g).toRingHom.Finite := by
  rw [← affineLineShiftEquiv_comp_algebraMap]
  have := (monic_affineLineShiftPoly (p := p) hg).finite_adjoinRoot
  exact (RingHom.Finite.of_surjective _ (affineLineShiftEquiv k p g).surjective).comp
    (RingHom.finite_algebraMap.2 inferInstance)

/-- **`y ↦ x + g(x)^{-p}` is étale** for `g` monic: `k[x]_g` is `k[y][T]/(F)` with `F` monic and
`F' = g(y + T^p)` invertible modulo `F`. -/
theorem etale_affineLineShift {g : k[X]} (hg : g.Monic) :
    (affineLineShift k p g).toRingHom.Etale := by
  rw [← affineLineShiftEquiv_comp_algebraMap]
  refine RingHom.Etale.respectsIso.1 _ _ (RingHom.etale_algebraMap.2 ?_)
  refine Stacks.Etale.ResidueFieldColimit.etale_adjoinRoot (monic_affineLineShiftPoly hg) ?_
  rw [derivative_affineLineShiftPoly]
  convert isUnit_affineLineShiftInvAux (p := p) g using 1
  rw [affineLineShiftInvAux, coe_eval₂RingHom, ← eval₂_comp_affineLineShiftPoly,
    ← AdjoinRoot.aeval_eq, aeval_def, AdjoinRoot.algebraMap_eq]

/-- **`D(g) ⟶ 𝔸¹_k`, `y ↦ x + g(x)^{-p}`, is finite.** -/
instance isFinite_specMap_affineLineShift {g : k[X]} [Fact g.Monic] :
    IsFinite (Spec.map (CommRingCat.ofHom (affineLineShift k p g).toRingHom)) := by
  rw [IsFinite.SpecMap_iff]
  exact finite_affineLineShift Fact.out

/-- **`D(g) ⟶ 𝔸¹_k`, `y ↦ x + g(x)^{-p}`, is étale.** -/
instance etale_specMap_affineLineShift {g : k[X]} [Fact g.Monic] :
    Etale (Spec.map (CommRingCat.ofHom (affineLineShift k p g).toRingHom)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact etale_affineLineShift Fact.out

/-- **Every nonempty open of `𝔸¹_k` is `D(g)` for a monic `g`**: its closed complement is `V(I)`,
`I = (h)` since `k[X]` is a principal ideal domain, `h ≠ 0` since the open is nonempty, and
`D(h) = D(h / lc(h))`. -/
theorem exists_monic_range_eq_basicOpen {U : Scheme.{u}} [Nonempty U] (e : U ⟶ Spec (.of k[X]))
    [IsOpenImmersion e] :
    ∃ g : k[X], g.Monic ∧
      Set.range e.base = (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum k[X])) := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1
    e.isOpenEmbedding.isOpen_range.isClosed_compl
  set h := Submodule.IsPrincipal.generator I
  have hr : Set.range e.base = (PrimeSpectrum.zeroLocus {h})ᶜ := by
    rw [← compl_compl (Set.range _), hI, ← Ideal.span_singleton_generator I,
      PrimeSpectrum.zeroLocus_span]
    rfl
  have hh : h ≠ 0 := by
    intro h0
    obtain ⟨y⟩ := ‹Nonempty U›
    have hy := Set.mem_range_self (f := e.base) y
    rw [hr, h0, PrimeSpectrum.zeroLocus_singleton_zero] at hy
    exact hy (Set.mem_univ _)
  refine ⟨h * C (leadingCoeff h)⁻¹, monic_mul_leadingCoeff_inv hh, ?_⟩
  have hu : IsUnit (C (leadingCoeff h)⁻¹) :=
    isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hh)))
  have hU : PrimeSpectrum.basicOpen (C (leadingCoeff h)⁻¹) = ⊤ :=
    top_unique fun y _ hm => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  rw [hr]
  show (PrimeSpectrum.zeroLocus {h})ᶜ =
    ((PrimeSpectrum.basicOpen (h * C (leadingCoeff h)⁻¹) : Set (PrimeSpectrum k[X])))
  rw [PrimeSpectrum.basicOpen_mul, hU, inf_top_eq, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]

variable (p) in
include p in
/-- **Every nonempty open `U` of `𝔸¹_k` is finite étale over `𝔸¹_k`**, over `k`: with
`U = D(g)`, `g` monic, the map `y ↦ x + g(x)^{-p}`. -/
theorem exists_finite_etale_affineLine {U : Scheme.{u}} [Nonempty U] (e : U ⟶ Spec (.of k[X]))
    [IsOpenImmersion e] :
    ∃ π : U ⟶ Spec (.of k[X]), IsFinite π ∧ Etale π ∧
      π ≫ Spec.map (CommRingCat.ofHom (algebraMap k k[X])) =
        e ≫ Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := by
  obtain ⟨g, hg, hr⟩ := exists_monic_range_eq_basicOpen e
  have : Fact g.Monic := ⟨hg⟩
  have hr' : Set.range e.base = Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away g)))).base := by
    rw [hr]
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g).symm
  let i := IsOpenImmersion.isoOfRangeEq e _ hr'
  refine ⟨i.hom ≫ Spec.map (CommRingCat.ofHom (affineLineShift k p g).toRingHom), inferInstance,
    inferInstance, ?_⟩
  rw [← IsOpenImmersion.isoOfRangeEq_hom_fac e _ hr', Category.assoc, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine RingHom.ext fun a => ?_
  show affineLineShift k p g (algebraMap k k[X] a) = _
  rw [AlgHom.commutes, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

variable (k)

/-- **`𝔸¹_k` is smooth of relative dimension one over `k`.** -/
theorem smoothOfRelativeDimension_specMap_polynomial :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  show (algebraMap k k[X]).IsStandardSmoothOfRelativeDimension 1
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact isStandardSmoothOfRelativeDimension_polynomial k

/-- **`𝔸¹_k` is a curve over `k`.** -/
theorem isCurve_specMap_polynomial :
    IsCurve k (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) := by
  have := smoothOfRelativeDimension_specMap_polynomial k
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) :=
    SmoothOfRelativeDimension.smooth 1 _
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1
    (Spec.map (CommRingCat.ofHom (algebraMap k k[X])))
  refine (isCurve_iff k _).2 ⟨
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance }, ?_⟩
  simpa using hdim

/-- **`𝔸¹_k` is geometrically connected**: `𝔸¹_K = Spec K[X]` is irreducible. -/
theorem connectedSpace_pullback_specMap_polynomial (K : Type u) [Field K] [Algebra k K] :
    ConnectedSpace ↥(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k k[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have := isDomain_polynomial_tensorProduct k K
  have : IrreducibleSpace ↥(Spec (.of (TensorProduct k k[X] K))) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum _))
  have : Nonempty ↥(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k k[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    ⟨(pullbackSpecIso k k[X] K).inv.base (Nonempty.some inferInstance)⟩
  have : IrreducibleSpace ↥(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k k[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    (pullbackSpecIso k k[X] K).hom.isOpenEmbedding.irreducibleSpace
  infer_instance

end Stacks.GenericFiniteEtale
