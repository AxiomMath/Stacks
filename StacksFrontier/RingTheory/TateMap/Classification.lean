module

public import StacksFrontier.RingTheory.Different.Formula.LocalizedCompleteIntersectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.QuasiFiniteSyntomic.UniversalFamilyBaseChange
public import StacksFrontier.RingTheory.QuasiFinite.Basic
public import StacksFrontier.RingTheory.QuasiFinite.BaseChange
public import StacksFrontier.RingTheory.TateMap.ChartBaseChange
public import StacksFrontier.RingTheory.TateMap.UniversalNice

/-!
# Localized square presentations are locally base changes of a universal basic chart

Let `A` be a Noetherian ring and `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` quasi-finite over `A`.
Lemma 0FKA says that around every point of `Spec B` the morphism `Spec B → Spec A` is an open of
a base change of the universal family `Y_{n, d} → X_{n, d}` of Example 0FK8. This file proves its
ring-theoretic form: for every prime `q` of `B` there are `d ≥ 1`, a specialization
`φ : univBase n d → A` of the universal coefficients carrying the universal polynomials to the
`f_i`, and a polynomial `k` with `univChart n d k` quasi-finite, such that for `b = φ(k)` the
localization `B_b` is a chart base change of `univBase n d → univChart n d k`, and `b ∉ q`.

## Main definitions

* `Stacks.TateMap.lciOfQuot`: the map `A[x_1, …, x_n]/(f) → A[x_1, …, x_n, 1/h]/(f)`, a
  localization away from `h` (`Stacks.TateMap.isLocalization_lciOfQuot`).
* `Stacks.TateMap.lciRingHom`: the ring map underlying `Stacks.TateMap.lciMap`.
* `Stacks.TateMap.lciMap`: the `A`-algebra map `A[x_1, …, x_n, 1/k]/(f) → T` sending `x_i` to
  `x_i`, into a localization `T` of `A[x_1, …, x_n, 1/h]/(f)` in which `k` is a unit.
* `Stacks.TateMap.classificationTensorEquiv`: the identification
  `A ⊗_P P[x_1, …, x_n, 1/k]/(F) ≅ A[x_1, …, x_n, 1/φ(k)]/(f)`.
* `Stacks.TateMap.classificationAlgebra` and `Stacks.TateMap.classificationOf`: for a ring map
  `φ : P → A` carrying polynomials `F_i` to the `f_i`, the chart map
  `P[x_1, …, x_n, 1/k]/(F) → B'` and the chart base change it defines. With `P = univBase n d`
  and `F = univPoly n d` the source is the basic chart `univChart n d k`.

## Main results

* `Stacks.TateMap.isLocalization_away_of_mul`: localizing a localization away from a product.
* `Stacks.TateMap.isLocalization_away_lciMap`: such a `T` is a localization of
  `A[x_1, …, x_n, 1/k]/(f)` away from one element.
* `Stacks.TateMap.exists_quasiFiniteAt_lci_one` and `Stacks.TateMap.exists_quasiFinite_lci`:
  quasi-finiteness descends along the specialization, and spreads to a basic chart.
* `Stacks.TateMap.subsingleton_or_isDomain_isUnramifiedAt_bot`: a localized complete
  intersection of a domain unramified at its generic point is zero, or again such a domain.
* `Stacks.TateMap.exists_classification_of_map` and `Stacks.TateMap.exists_classification`: the
  classification exists near every prime.
* `Stacks.TateMap.univChart_subsingleton_or`: a basic chart of the universal family is zero, or a
  domain unramified at its generic point.

## References

* [Stacks Project, Tag 0FKA](https://stacks.math.columbia.edu/tag/0FKA)
* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.TateMap

open _root_.AlgebraicGeometry Stacks.Discriminant

/-! ### Localizing a localization away from a product -/

/-- If `S` is the localization of `Q` away from `y` and `T` is a localization of `Q` away from
`y * w` receiving a map from `S`, then `T` is the localization of `S` away from the image of
`w`. -/
theorem isLocalization_away_of_mul {Q S T : Type*} [CommRing Q] [CommRing S] [CommRing T]
    [Algebra Q S] [Algebra Q T] [Algebra S T] [IsScalarTower Q S T] (y w : Q)
    [IsLocalization.Away y S] [hT : IsLocalization.Away (y * w) T] :
    IsLocalization.Away (algebraMap Q S w) T := by
  let S' := Localization.Away (algebraMap Q S w)
  have : IsLocalization.Away (y * w) S' := IsLocalization.Away.mul' S S' y w
  let e : S' ≃ₐ[Q] T := IsLocalization.algEquiv (Submonoid.powers (y * w)) S' T
  have he : (e.toRingHom).comp (algebraMap S S') = algebraMap S T := by
    refine IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun q ↦ ?_)
    show e (algebraMap S S' (algebraMap Q S q)) = algebraMap S T (algebraMap Q S q)
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  let e' : S' ≃ₐ[S] T := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun x ↦ congr($he x)
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap Q S w)) e'

/-! ### Localized complete intersections as localizations of the quotient -/

section LCI

variable {A : Type u} [CommRing A] {n : ℕ} (h : MvPolynomial (Fin n) A)
  (f : Fin n → MvPolynomial (Fin n) A)

/-- The map `A[x_1, …, x_n]/(f_1, …, f_n) → A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`. -/
def lciOfQuot :
    (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) →ₐ[A]
      localizedCompleteIntersection A n h f :=
  Ideal.Quotient.liftₐ _ (IsScalarTower.toAlgHom A (MvPolynomial (Fin n) A) _) (by
    intro a ha
    refine (Ideal.span_le (I := RingHom.ker _)).mpr ?_ ha
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change algebraMap (MvPolynomial (Fin n) A) (localizedCompleteIntersection A n h f) (f i) = 0
    rw [algebraMap_localizedCompleteIntersection_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩))

/-- `lciOfQuot` sends the class of a polynomial `p` to its class in `A[x_1, …, x_n, 1/h]/(f)`. -/
@[simp]
theorem lciOfQuot_mk (p : MvPolynomial (Fin n) A) :
    lciOfQuot h f (Ideal.Quotient.mk _ p) =
      algebraMap (MvPolynomial (Fin n) A) (localizedCompleteIntersection A n h f) p :=
  rfl

/-- `A[x_1, …, x_n, 1/h]/(f)` is the localization of `A[x_1, …, x_n]/(f)` away from `h`. -/
theorem isLocalization_lciOfQuot :
    letI := (lciOfQuot h f).toRingHom.toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) h)
      (localizedCompleteIntersection A n h f) := by
  let := (lciOfQuot h f).toRingHom.toAlgebra
  have hloc := isLocalization_away_localizedQuotient A n h f
  let e := localizedQuotientEquiv A n h f
  have he : ∀ x : MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f),
      e.toRingEquiv (algebraMap _ (localizedQuotient A n h f) x) =
        algebraMap _ (localizedCompleteIntersection A n h f) x := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers _)
    (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) he)

variable (k g : MvPolynomial (Fin n) A) {T : Type*} [CommRing T] [Algebra A T]
  [Algebra (localizedCompleteIntersection A n h f) T]
  [IsScalarTower A (localizedCompleteIntersection A n h f) T]

/-- The ring map `A[x_1, …, x_n, 1/k]/(f) → T` sending `x_i` to `x_i`, for an
`A[x_1, …, x_n, 1/h]/(f)`-algebra `T` in which `k` is a unit. -/
def lciRingHom (hk : IsUnit (algebraMap (localizedCompleteIntersection A n h f) T
      (algebraMap (MvPolynomial (Fin n) A) _ k))) :
    localizedCompleteIntersection A n k f →+* T :=
  Ideal.Quotient.lift _ (IsLocalization.Away.lift k (g := (algebraMap
      (localizedCompleteIntersection A n h f) T).comp
        (algebraMap (MvPolynomial (Fin n) A) _)) hk) (by
    intro a ha
    refine (Ideal.span_le (I := RingHom.ker _)).mpr ?_ ha
    rintro _ ⟨i, rfl⟩
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (localizedRelations A n h f)))
        (algebraMap (MvPolynomial (Fin n) A) (Localization.Away h) (f i)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    rw [SetLike.mem_coe, RingHom.mem_ker, localizedRelations, IsLocalization.Away.lift_eq,
      RingHom.comp_apply, algebraMap_localizedCompleteIntersection_apply, h0, map_zero])

omit [Algebra A T] [IsScalarTower A (localizedCompleteIntersection A n h f) T] in
/-- `lciRingHom` sends the class of a polynomial `p` to the image in `T` of its class in
`A[x_1, …, x_n, 1/h]/(f)`. -/
theorem lciRingHom_algebraMap (hk : IsUnit (algebraMap (localizedCompleteIntersection A n h f) T
      (algebraMap (MvPolynomial (Fin n) A) _ k))) (p : MvPolynomial (Fin n) A) :
    lciRingHom h f k hk (algebraMap (MvPolynomial (Fin n) A) _ p) =
      algebraMap (localizedCompleteIntersection A n h f) T
        (algebraMap (MvPolynomial (Fin n) A) _ p) := by
  rw [algebraMap_localizedCompleteIntersection_apply]
  exact IsLocalization.Away.lift_eq k hk p

/-- The `A`-algebra map `A[x_1, …, x_n, 1/k]/(f) → T` sending `x_i` to `x_i`, for an
`A[x_1, …, x_n, 1/h]/(f)`-algebra `T` in which `k` is a unit. -/
def lciMap (hk : IsUnit (algebraMap (localizedCompleteIntersection A n h f) T
      (algebraMap (MvPolynomial (Fin n) A) _ k))) :
    localizedCompleteIntersection A n k f →ₐ[A] T where
  toRingHom := lciRingHom h f k hk
  commutes' a := by
    rw [IsScalarTower.algebraMap_apply A (MvPolynomial (Fin n) A)
      (localizedCompleteIntersection A n k f)]
    change lciRingHom h f k hk (algebraMap (MvPolynomial (Fin n) A) _ _) = _
    rw [lciRingHom_algebraMap, ← IsScalarTower.algebraMap_apply A (MvPolynomial (Fin n) A)
      (localizedCompleteIntersection A n h f),
      ← IsScalarTower.algebraMap_apply A (localizedCompleteIntersection A n h f) T]

/-- `lciMap` sends the class of a polynomial `p` to the image in `T` of its class in
`A[x_1, …, x_n, 1/h]/(f)`. -/
@[simp]
theorem lciMap_algebraMap (hk : IsUnit (algebraMap (localizedCompleteIntersection A n h f) T
      (algebraMap (MvPolynomial (Fin n) A) _ k))) (p : MvPolynomial (Fin n) A) :
    lciMap h f k hk (algebraMap (MvPolynomial (Fin n) A) _ p) =
      algebraMap (localizedCompleteIntersection A n h f) T
        (algebraMap (MvPolynomial (Fin n) A) _ p) :=
  lciRingHom_algebraMap h f k hk p

/-- Let `T` be the localization of `A[x_1, …, x_n, 1/h]/(f)` away from the image of `g`, and let
`k` be a unit in `T`. Then, through `lciMap`, `T` is the localization of `A[x_1, …, x_n, 1/k]/(f)`
away from the image of `h g`. -/
theorem isLocalization_away_lciMap
    [IsLocalization.Away
      (algebraMap (MvPolynomial (Fin n) A) (localizedCompleteIntersection A n h f) g) T]
    (hk : IsUnit (algebraMap (localizedCompleteIntersection A n h f) T
      (algebraMap (MvPolynomial (Fin n) A) _ k))) :
    letI := (lciMap h f k hk).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (MvPolynomial (Fin n) A)
      (localizedCompleteIntersection A n k f) (h * g)) T := by
  set Q := MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)
  let mk := Ideal.Quotient.mk (Ideal.span (Set.range f))
  let iH : Algebra Q (localizedCompleteIntersection A n h f) := (lciOfQuot h f).toRingHom.toAlgebra
  let iK : Algebra Q (localizedCompleteIntersection A n k f) := (lciOfQuot k f).toRingHom.toAlgebra
  let iT : Algebra Q T :=
    ((algebraMap (localizedCompleteIntersection A n h f) T).comp
      (lciOfQuot h f).toRingHom).toAlgebra
  let iKT : Algebra (localizedCompleteIntersection A n k f) T :=
    (lciMap h f k hk).toRingHom.toAlgebra
  have : IsScalarTower Q (localizedCompleteIntersection A n h f) T :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Q (localizedCompleteIntersection A n k f) T :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact (lciMap_algebraMap h f k hk p).symm
  have hH := isLocalization_lciOfQuot h f
  have hK := isLocalization_lciOfQuot k f
  have hg : IsLocalization.Away (algebraMap Q (localizedCompleteIntersection A n h f) (mk g)) T :=
    ‹IsLocalization.Away (algebraMap (MvPolynomial (Fin n) A) _ g) T›
  have h1 : IsLocalization.Away (mk h * mk g) T :=
    IsLocalization.Away.mul' (localizedCompleteIntersection A n h f) T (mk h) (mk g)
  have h2 : IsLocalization.Away (mk k * (mk h * mk g)) T :=
    IsLocalization.Away.mul_of_isUnit' _ _ hk
  have h3 := isLocalization_away_of_mul (S := localizedCompleteIntersection A n k f) (T := T)
    (mk k) (mk h * mk g)
  rwa [← map_mul] at h3

/-- A localized complete intersection whose unlocalized quotient `A[x_1, …, x_n]/(f)` is a domain
unramified at its generic point is either the zero ring, or again a domain unramified at its
generic point. -/
theorem subsingleton_or_isDomain_isUnramifiedAt_bot
    [IsDomain (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))]
    [Algebra.FiniteType A (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))]
    [Algebra.IsUnramifiedAt A (⊥ : Ideal (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)))] :
    Subsingleton (localizedCompleteIntersection A n h f) ∨
      ∃ (_ : IsDomain (localizedCompleteIntersection A n h f)),
        Algebra.IsUnramifiedAt A (⊥ : Ideal (localizedCompleteIntersection A n h f)) := by
  let := (lciOfQuot h f).toRingHom.toAlgebra
  have hloc := isLocalization_lciOfQuot h f
  have := IsScalarTower.of_algHom (lciOfQuot h f)
  by_cases hk : Ideal.Quotient.mk (Ideal.span (Set.range f)) h = 0
  · left
    have hu := IsLocalization.Away.algebraMap_isUnit (S := localizedCompleteIntersection A n h f)
      (Ideal.Quotient.mk (Ideal.span (Set.range f)) h)
    rw [hk, map_zero] at hu
    exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)
  right
  have hle : Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range f)) h) ≤
      nonZeroDivisors (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hk
  have hdom : IsDomain (localizedCompleteIntersection A n h f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  refine ⟨hdom, ?_⟩
  obtain ⟨c, hc0, hc⟩ := exists_smul_eq_zero_of_isUnramifiedAt_bot
    (A := A) (B := MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
  refine isUnramifiedAt_bot_of_smul_eq_zero (algebraMap _ _ c) ?_
    (smul_kaehler_localization_eq_zero
      (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range f)) h)) c hc)
  rw [← map_zero (algebraMap (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f))
    (localizedCompleteIntersection A n h f))]
  exact fun h ↦ hc0 (IsLocalization.injective _ hle h)

end LCI

/-! ### The chart base change attached to a classification -/

section ClassificationOf

variable {A P : Type u} [CommRing A] [CommRing P] {n : ℕ} {F : Fin n → MvPolynomial (Fin n) P}
  (k : MvPolynomial (Fin n) P) (φ : P →+* A) (h : MvPolynomial (Fin n) A)
  (f : Fin n → MvPolynomial (Fin n) A)
  (hf : ∀ i, MvPolynomial.map φ (F i) = f i)

/-- The identification `A ⊗_P P[x_1, …, x_n, 1/k]/(F) ≅ A[x_1, …, x_n, 1/φ(k)]/(f)`, for a ring
map `φ : P → A` carrying the polynomials `F_i` to the `f_i`. -/
def classificationTensorEquiv :
    letI := φ.toAlgebra
    A ⊗[P] localizedCompleteIntersection P n k F ≃ₐ[A]
      localizedCompleteIntersection A n (MvPolynomial.map φ k) f :=
  letI := φ.toAlgebra
  (localizedCompleteIntersectionBaseChange P A n k (F)).trans
    (localizedCompleteIntersectionCongr rfl (funext hf))

/-- `classificationTensorEquiv` sends `a ⊗ x` to `a` times the image of `x` under the base change
map `P[x_1, …, x_n, 1/k]/(F) → A[x_1, …, x_n, 1/φ(k)]/(f)`. -/
theorem classificationTensorEquiv_tmul (a : A) (x : localizedCompleteIntersection P n k F) :
    letI := φ.toAlgebra
    classificationTensorEquiv k φ f hf (a ⊗ₜ x) =
      a • localizedCompleteIntersectionCongr rfl (funext hf)
        (localizedCompleteIntersectionMap P A n k (F) x) := by
  let := φ.toAlgebra
  simp [classificationTensorEquiv, localizedCompleteIntersectionBaseChange_tmul]

variable (g : MvPolynomial (Fin n) A) (B' : Type u) [CommRing B'] [Algebra A B']
  [Algebra (localizedCompleteIntersection A n h f) B']
  [IsScalarTower A (localizedCompleteIntersection A n h f) B']
  [IsLocalization.Away (algebraMap (MvPolynomial (Fin n) A)
    (localizedCompleteIntersection A n h f) g) B']

/-- The `A`-algebra map `A ⊗_P P[x_1, …, x_n, 1/k]/(F) → B'` of a classification. -/
def classificationTensorMap (hk : IsUnit (algebraMap (localizedCompleteIntersection A n h f) B'
      (algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ k)))) :
    letI := φ.toAlgebra
    A ⊗[P] localizedCompleteIntersection P n k F →ₐ[A] B' :=
  letI := φ.toAlgebra
  (lciMap h f (MvPolynomial.map φ k) hk).comp (classificationTensorEquiv k φ f hf).toAlgHom

/-- The chart map `P[x_1, …, x_n, 1/k]/(F) → B'` of a classification: it sends `x_i` to `x_i`. -/
@[instance_reducible]
def classificationAlgebra (hk : IsUnit (algebraMap (localizedCompleteIntersection A n h f) B'
      (algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ k)))) :
    Algebra (localizedCompleteIntersection P n k F) B' :=
  letI := φ.toAlgebra
  ((classificationTensorMap k φ h f hf B' hk).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom).toAlgebra

/-- The chart map sends the class of a polynomial `p` over `P` to the class of `φ(p)`. -/
theorem classificationAlgebra_algebraMap (hk : IsUnit (algebraMap
      (localizedCompleteIntersection A n h f) B'
      (algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ k))))
    (p : MvPolynomial (Fin n) P) :
    letI := classificationAlgebra k φ h f hf B' hk
    algebraMap (localizedCompleteIntersection P n k F) B' (algebraMap _ _ p) =
      algebraMap (localizedCompleteIntersection A n h f) B'
        (algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ p)) := by
  let := φ.toAlgebra
  show classificationTensorMap k φ h f hf B' hk (1 ⊗ₜ _) = _
  show lciMap h f (MvPolynomial.map φ k) hk (classificationTensorEquiv k φ f hf (1 ⊗ₜ _)) = _
  rw [classificationTensorEquiv_tmul, one_smul, localizedCompleteIntersectionMap_algebraMap]
  have hc := localizedCompleteIntersectionCongr_algebraMap (S := A) (n := n)
    (h := MvPolynomial.map φ k) (h' := MvPolynomial.map φ k) (f' := f) rfl (funext hf)
    (MvPolynomial.map φ p)
  exact (congrArg (lciMap h f (MvPolynomial.map φ k) hk) hc).trans (lciMap_algebraMap _ _ _ _ _)

/-- Let `φ : P → A` carry the polynomials `F_i` to the `f_i`, let `k` be a polynomial over `P`,
and let `B'` be a localization of `B = A[x_1, …, x_n, 1/h]/(f)` away from a polynomial `g` in
which `φ(k)` is a unit. Then `B'` is a chart base change of `P → P[x_1, …, x_n, 1/k]/(F)` along
`φ`: it is the localization of `A ⊗_P P[x_1, …, x_n, 1/k]/(F)` away from the class of `h g`. -/
def classificationOf (hk : IsUnit (algebraMap (localizedCompleteIntersection A n h f) B'
      (algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ k)))) :
    letI := φ.toAlgebra
    letI := classificationAlgebra k φ h f hf B' hk
    ChartBaseChange P (localizedCompleteIntersection P n k F) A B' :=
  letI := φ.toAlgebra
  letI := classificationAlgebra k φ h f hf B' hk
  { algebra := (classificationTensorMap k φ h f hf B' hk).toRingHom.toAlgebra
    base_left := fun y ↦ by
      change classificationTensorMap k φ h f hf B' hk (y ⊗ₜ 1) = _
      have hy : algebraMap A (A ⊗[P] localizedCompleteIntersection P n k F) y = y ⊗ₜ 1 := by
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [← hy, AlgHom.commutes]
    base_right := fun _ ↦ rfl
    elt := (classificationTensorEquiv k φ f hf).symm
      (algebraMap (MvPolynomial (Fin n) A) _ (h * g))
    isLocalization := by
      letI := (lciMap h f (MvPolynomial.map φ k) hk).toRingHom.toAlgebra
      have H := isLocalization_away_lciMap h f (MvPolynomial.map φ k) g (T := B') hk
      have H' := IsLocalization.isLocalization_of_base_ringEquiv (S := B')
        (Submonoid.powers (algebraMap (MvPolynomial (Fin n) A)
          (localizedCompleteIntersection A n (MvPolynomial.map φ k) f) (h * g)))
        (classificationTensorEquiv k φ f hf).symm.toRingEquiv
      rw [Submonoid.map_powers] at H'
      exact H' }

end ClassificationOf

/-! ### Existence of a classification -/

/-- In a localized complete intersection with `h = 1`, every element is the class of a
polynomial. -/
theorem exists_algebraMap_eq_of_one {R : Type*} [CommRing R] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin n) R) (x : localizedCompleteIntersection R n 1 f) :
    ∃ p : MvPolynomial (Fin n) R, algebraMap (MvPolynomial (Fin n) R) _ p = x := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers (1 : MvPolynomial
    (Fin n) R)) z
  refine ⟨a, ?_⟩
  simp only [one_pow, map_one, mul_one] at ha
  rw [algebraMap_localizedCompleteIntersection_apply, ← ha]

/-- Let `B = A[x_1, …, x_n, 1/h]/(f)` be quasi-finite over `A`, let `q` be a prime of `B`, and let
`φ : P → A` carry polynomials `F_i` to the `f_i`, with `P[x_1, …, x_n]/(F)` of finite type over
`P`. Then the prime of `P[x_1, …, x_n]/(F)` below `q` (along the chart map `x_i ↦ x_i`) is a
point at which it is quasi-finite over `P`. -/
theorem exists_quasiFiniteAt_lci_one {A P : Type u} [CommRing A] [CommRing P] {n : ℕ}
    {F : Fin n → MvPolynomial (Fin n) P}
    [Algebra.FiniteType P (localizedCompleteIntersection P n 1 F)]
    (h : MvPolynomial (Fin n) A) (f : Fin n → MvPolynomial (Fin n) A)
    [Algebra.QuasiFinite A (localizedCompleteIntersection A n h f)]
    (q : Ideal (localizedCompleteIntersection A n h f)) [q.IsPrime]
    (φ : P →+* A) (hf : ∀ i, MvPolynomial.map φ (F i) = f i) :
    ∃ (q₀ : Ideal (localizedCompleteIntersection P n 1 F)) (_ : q₀.IsPrime),
      Algebra.QuasiFiniteAt P q₀ ∧
      ∀ p : MvPolynomial (Fin n) P,
        algebraMap (MvPolynomial (Fin n) A) (localizedCompleteIntersection A n h f)
          (MvPolynomial.map φ p) ∈ q →
        algebraMap (MvPolynomial (Fin n) P) (localizedCompleteIntersection P n 1 F) p ∈ q₀ := by
  let := φ.toAlgebra
  have h1 : IsUnit (algebraMap (localizedCompleteIntersection A n h f)
      (localizedCompleteIntersection A n h f) (algebraMap (MvPolynomial (Fin n) A)
        (localizedCompleteIntersection A n h f) (MvPolynomial.map φ 1))) := by
    simp
  have hone (R : Type u) [CommRing R] : IsLocalization.Away (1 : R) R :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin n) A)
      (localizedCompleteIntersection A n h f) 1) (localizedCompleteIntersection A n h f) := by
    rw [map_one]
    exact hone _
  let := classificationAlgebra (1 : MvPolynomial (Fin n) P) φ h f hf
    (localizedCompleteIntersection A n h f) h1
  have D : ChartBaseChange P (localizedCompleteIntersection P n 1 F) A
      (localizedCompleteIntersection A n h f) :=
    classificationOf (1 : MvPolynomial (Fin n) P) φ h f hf 1
      (localizedCompleteIntersection A n h f) h1
  let iD : Algebra (A ⊗[P] (localizedCompleteIntersection P n 1 F))
      (localizedCompleteIntersection A n h f) :=
    D.algebra
  have hloc : IsLocalization.Away D.elt (localizedCompleteIntersection A n h f) :=
    D.isLocalization
  have : @IsScalarTower A (A ⊗[P] (localizedCompleteIntersection P n 1 F))
      (localizedCompleteIntersection A n h f) Algebra.toSMul iD.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (D.base_left a).symm
  let q' := q.comap (algebraMap (A ⊗[P] (localizedCompleteIntersection P n 1 F))
    (localizedCompleteIntersection A n h f))
  have := hone A
  have : IsLocalization.Away
      (algebraMap A (A ⊗[P] (localizedCompleteIntersection P n 1 F)) 1 * D.elt)
      (localizedCompleteIntersection A n h f) := by
    rw [map_one, one_mul]; exact hloc
  have hq' : q'.IsPrime := Ideal.comap_isPrime _ q
  have hp : (q'.comap (algebraMap A (A ⊗[P] (localizedCompleteIntersection P n 1 F)))).IsPrime :=
    Ideal.comap_isPrime _ _
  have : q'.LiesOver (q'.comap (algebraMap A (A ⊗[P] (localizedCompleteIntersection P n 1 F)))) :=
    ⟨rfl⟩
  have helt : D.elt ∉ q' := by
    intro hm
    have hu : IsUnit (algebraMap (A ⊗[P] (localizedCompleteIntersection P n 1 F))
        (localizedCompleteIntersection A n h f) D.elt) :=
      IsLocalization.Away.algebraMap_isUnit D.elt
    exact (‹q.IsPrime›).ne_top (Ideal.eq_top_of_isUnit_mem q (Ideal.mem_comap.mp hm) hu)
  have hQ : q = Ideal.map (algebraMap (A ⊗[P] (localizedCompleteIntersection P n 1 F))
      (localizedCompleteIntersection A n h f)) q' :=
    (IsLocalization.map_under (Submonoid.powers D.elt) _ q).symm
  have hqf' : Algebra.QuasiFiniteAt A q' :=
    (quasiFiniteAt_localization_away_iff (R := A)
      (S := A ⊗[P] (localizedCompleteIntersection P n 1 F)) (Rf := A)
      (Sfg := localizedCompleteIntersection A n h f) (1 : A) D.elt _ q'
      (fun h ↦ hp.ne_top ((Ideal.eq_top_iff_one _).mpr h)) helt q hQ).mpr inferInstance
  let q₀ := q'.comap (Algebra.TensorProduct.includeRight (R := P) (A := A)
    (B := localizedCompleteIntersection P n 1 F)).toRingHom
  have hq₀ : q₀.IsPrime := Ideal.comap_isPrime _ _
  have hqf₀ : Algebra.QuasiFiniteAt P q₀ :=
    (Algebra.quasiFiniteAt_baseChange_iff A q₀ q' rfl).mp hqf'
  refine ⟨q₀, hq₀, hqf₀, fun p hp ↦ ?_⟩
  have hx : algebraMap (A ⊗[P] (localizedCompleteIntersection P n 1 F))
      (localizedCompleteIntersection A n h f) ((1 : A) ⊗ₜ
        algebraMap (MvPolynomial (Fin n) P) (localizedCompleteIntersection P n 1 F) p) ∈ q := by
    rw [D.base_right, classificationAlgebra_algebraMap]
    simpa using hp
  exact Ideal.mem_comap.mpr (Ideal.mem_comap.mpr hx)

/-- If `P[x_1, …, x_n]/(F)` is quasi-finite over `P` at a prime `q₀`, then for some polynomial
`k ∉ q₀` the basic chart `P[x_1, …, x_n, 1/k]/(F)` is quasi-finite over `P`. -/
theorem exists_quasiFinite_lci {P : Type u} [CommRing P] {n : ℕ}
    {F : Fin n → MvPolynomial (Fin n) P}
    (q₀ : Ideal (localizedCompleteIntersection P n 1 F)) [q₀.IsPrime]
    [Algebra.QuasiFiniteAt P q₀] :
    ∃ k : MvPolynomial (Fin n) P,
      Algebra.QuasiFinite P (localizedCompleteIntersection P n k F) ∧
      algebraMap (MvPolynomial (Fin n) P) (localizedCompleteIntersection P n 1 F) k ∉ q₀ := by
  have hfp1 : Algebra.FinitePresentation P (localizedCompleteIntersection P n 1 F) :=
    finitePresentation_localizedCompleteIntersection P n 1 (F)
  have hft1 : Algebra.FiniteType P (localizedCompleteIntersection P n 1 F) :=
    Algebra.FiniteType.of_finitePresentation
  have hZ : Algebra.ZariskisMainProperty P q₀ :=
    Algebra.ZariskisMainProperty.of_finiteType _
  obtain ⟨S', hS', r, hrq, hbij⟩ := hZ.exists_fg_and_exists_notMem_and_awayMap_bijective _
  have : Module.Finite P S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : Algebra.QuasiFinite P (Localization.Away r) := .trans _ S' _
  have hqfr : Algebra.QuasiFinite P (Localization.Away r.val) :=
    .of_surjective_algHom (Localization.awayMapₐ S'.val r) hbij.right
  obtain ⟨k, hk⟩ := exists_algebraMap_eq_of_one F r.val
  refine ⟨k, ?_, hk ▸ hrq⟩
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin n) P)
      (localizedCompleteIntersection P n 1 F) k) (Localization.Away r.val) := by
    rw [hk]; infer_instance
  have hkT : IsUnit (algebraMap (localizedCompleteIntersection P n 1 F) (Localization.Away r.val)
      (algebraMap (MvPolynomial (Fin n) P) (localizedCompleteIntersection P n 1 F) k)) :=
    IsLocalization.Away.algebraMap_isUnit _
  let iKT := (lciMap 1 F k hkT).toRingHom.toAlgebra
  have hloc' := isLocalization_away_lciMap 1 F k k
    (T := Localization.Away r.val) hkT
  have := IsScalarTower.of_algHom (lciMap 1 F k hkT)
  have hunits : Submonoid.powers (algebraMap (MvPolynomial (Fin n) P)
      (localizedCompleteIntersection P n k F) (1 * k)) ≤ IsUnit.submonoid _ := by
    rw [Submonoid.powers_le, IsUnit.mem_submonoid_iff, one_mul,
      algebraMap_localizedCompleteIntersection_apply]
    exact (IsLocalization.Away.algebraMap_isUnit k).map _
  let e := IsLocalization.atUnits _ _ (S := Localization.Away r.val) hunits
  exact (Algebra.QuasiFinite.iff_of_algEquiv (e.restrictScalars P)).mpr hqfr

/-- Let `B = A[x_1, …, x_n, 1/h]/(f)` be quasi-finite over `A`, let `q` be a prime of `B`, and let
`φ : univBase n d → A` carry the universal polynomials to the `f_i`. There is a polynomial `k`
over `univBase n d` with `univChart n d k` quasi-finite over `univBase n d` and the class of
`φ(k)` in `B` not in `q`. -/
theorem exists_classification_of_map {A : Type u} [CommRing A] {n : ℕ}
    (h : MvPolynomial (Fin n) A) (f : Fin n → MvPolynomial (Fin n) A)
    [Algebra.QuasiFinite A (localizedCompleteIntersection A n h f)]
    (q : Ideal (localizedCompleteIntersection A n h f)) [q.IsPrime] {d : ℕ}
    (φ : univBase.{u} n d →+* A) (hφ : ∀ i, MvPolynomial.map φ (univPoly n d i) = f i) :
    ∃ k : MvPolynomial (Fin n) (univBase.{u} n d),
      Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k) ∧
      algebraMap (MvPolynomial (Fin n) A) (localizedCompleteIntersection A n h f)
        (MvPolynomial.map φ k) ∉ q := by
  have : Algebra.FinitePresentation (univBase.{u} n d) (univChart.{u} n d 1) :=
    finitePresentation_localizedCompleteIntersection (univBase.{u} n d) n 1 (univPoly n d)
  obtain ⟨q₀, hq₀, hqf₀, hmem⟩ := exists_quasiFiniteAt_lci_one h f q φ hφ
  obtain ⟨k, hk, hkq⟩ := exists_quasiFinite_lci q₀
  exact ⟨k, hk, fun h ↦ hkq (hmem k h)⟩

/-- Let `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` be quasi-finite over `A` and let `q` be a prime of
`B`. There are a positive degree bound `d`, a specialization `φ : univBase n d → A` of the
universal coefficients carrying the universal polynomials to the `f_i`, and a polynomial `k` over
`univBase n d` such that the basic chart `univChart n d k` is quasi-finite over `univBase n d`
and the class of `φ(k)` in `B` is not in `q`. -/
theorem exists_classification {A : Type u} [CommRing A] {n : ℕ} (h : MvPolynomial (Fin n) A)
    (f : Fin n → MvPolynomial (Fin n) A)
    [Algebra.QuasiFinite A (localizedCompleteIntersection A n h f)]
    (q : Ideal (localizedCompleteIntersection A n h f)) [q.IsPrime] :
    ∃ (d : ℕ) (_ : NeZero d) (k : MvPolynomial (Fin n) (univBase.{u} n d))
      (φ : univBase.{u} n d →+* A),
      (∀ i, MvPolynomial.map φ (univPoly n d i) = f i) ∧
      Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k) ∧
      algebraMap (MvPolynomial (Fin n) A) (localizedCompleteIntersection A n h f)
        (MvPolynomial.map φ k) ∉ q := by
  obtain ⟨d, hd, φ₀, hφ₀⟩ := exists_universalCoefficientSpecialization n f
  let φ : univBase.{u} n d →+* A := φ₀.comp (univBaseEquiv.{u} n d).toRingHom
  have hf : ∀ i, MvPolynomial.map φ (univPoly n d i) = f i := by
    intro i
    rw [← hφ₀ i, ← univPolyRingEquiv_univPoly n d i, univPolyRingEquiv,
      MvPolynomial.mapEquiv_apply, MvPolynomial.map_map]
    rfl
  obtain ⟨k, hk, hkq⟩ := exists_classification_of_map h f q φ hf
  exact ⟨d, hd, k, φ, hf, hk, hkq⟩

/-- For a positive degree bound, a basic chart `univChart n d k` of the universal family is either
the zero ring, or a domain unramified over `univBase n d` at its generic point. -/
theorem univChart_subsingleton_or (n d : ℕ) [NeZero d]
    (k : MvPolynomial (Fin n) (univBase.{u} n d)) :
    Subsingleton (univChart n d k) ∨
      ∃ (_ : IsDomain (univChart n d k)),
        Algebra.IsUnramifiedAt (univBase.{u} n d) (⊥ : Ideal (univChart n d k)) :=
  have := isUnramifiedAt_bot_univQuot.{u} n d
  subsingleton_or_isDomain_isUnramifiedAt_bot k (univPoly n d)

end Stacks.TateMap
