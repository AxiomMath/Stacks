module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalProperties.Projective
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation

/-!
# Helpers for polynomial descent along an affine groupoid scheme

Flatness of a polynomial ring over a ring over which its coefficients are flat, the flat
polynomial cover of an algebra, the determinant of a scalar on an idempotent piece of constant
rank, the passage from powers descending on each idempotent piece to a single global power,
and the comparison of the fibre rank of an affine morphism with the stalk rank of its algebra
of global functions.

## Main results

* `Module.Flat.polynomial`: a polynomial ring is flat over a ring over which its coefficient
  ring is flat.
* `Algebra.exists_flat_surjective_cover`: every algebra is a quotient of a flat algebra.
* `ProjectiveDeterminant.idempotent_mul_det_lmul_algebraMap`: on a piece where the rank is `r`,
  the scalar determinant of multiplication by `algebraMap R B x` is `x ^ r`.
* `RingHom.exists_pow_eq_map_of_idempotents`: powers descending on finitely many idempotent
  pieces have a common positive power which descends globally.
* `AlgebraicGeometry.finrank_eq_rankAtStalk_of_isAffine` and
  `AlgebraicGeometry.finrank_source_eq_finrank_target`: the fibre ranks of an affine morphism,
  and their agreement at the source and the target of an arrow.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

universe u

namespace Module.Flat

/-- A polynomial ring is flat over any ring over which its coefficient ring is flat. -/
theorem polynomial {R D : Type u} [CommRing R] [CommRing D] [Algebra R D] [Module.Flat R D] :
    Module.Flat R (Polynomial D) :=
  have : Module.Flat D (Polynomial D) := Module.Flat.of_free
  Module.Flat.trans R D (Polynomial D)

end Module.Flat

namespace Algebra

/-- Every algebra is a quotient of a flat algebra. -/
theorem exists_flat_surjective_cover {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (_ : Module.Flat R D) (φ : D →ₐ[R] A),
      Function.Surjective φ :=
  ⟨MvPolynomial A R, inferInstance, inferInstance, Module.Flat.of_free,
    MvPolynomial.aeval (R := R) (fun a : A ↦ a),
    fun a ↦ ⟨MvPolynomial.X a, MvPolynomial.aeval_X _ _⟩⟩

end Algebra

namespace ProjectiveDeterminant

/-- On an idempotent piece of the base ring where a finite projective algebra has constant stalk
rank `r`, the scalar determinant of multiplication by a scalar is its `r`-th power. -/
theorem idempotent_mul_det_lmul_algebraMap {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B] (e : R) (he : e * e = e) (r : ℕ)
    (hr : ∀ p : PrimeSpectrum R, e ∉ p.asIdeal → Module.rankAtStalk B p = r) (x : R) :
    e * ProjectiveDeterminant.det (Algebra.lmul R B (algebraMap R B x)) = e * x ^ r := by
  classical
  have hmul : Algebra.lmul R B (algebraMap R B x) = x • (LinearMap.id : B →ₗ[R] B) := by
    ext b; simp [Algebra.smul_def]
  rw [hmul]
  apply Module.eq_of_localization_maximal
    (Mₚ := fun (P : Ideal R) [P.IsMaximal] ↦ Localization.AtPrime P)
    (f := fun P _ ↦ Algebra.linearMap R (Localization.AtPrime P))
  intro P hP
  let : P.IsPrime := hP.isPrime
  let Rp := Localization.AtPrime P
  let Q := LocalizedModule P.primeCompl B
  let : Module.Free Rp Q := Module.free_of_flat_of_isLocalRing
  have heP : IsIdempotentElem (algebraMap R Rp e) := by
    change algebraMap R Rp e * algebraMap R Rp e = algebraMap R Rp e
    rw [← map_mul, he]
  have hmap : LocalizedModule.map P.primeCompl (x • (LinearMap.id : B →ₗ[R] B)) =
      algebraMap R Rp x • (LinearMap.id : Q →ₗ[Rp] Q) := by
    refine LinearMap.ext fun y ↦ ?_
    induction y with
    | _ b s => simp [map_smul]
  have hloc := ProjectiveDeterminant.det_localization (R := R) (M := B) P
    (x • (LinearMap.id : B →ₗ[R] B))
  simp only [Algebra.linearMap_apply, map_mul]
  rw [hloc, hmap, ProjectiveDeterminant.det_eq_linearMap_det_of_basis (Module.finBasis Rp Q),
    LinearMap.det_smul, LinearMap.det_id, mul_one, map_pow]
  by_cases hPmem : e ∈ P
  · have hunit : IsUnit (1 - algebraMap R Rp e) := by
      have hcompl : (1 : R) - e ∈ P.primeCompl := fun hcomp ↦
        hP.isPrime.ne_top ((Ideal.eq_top_iff_one P).2 (by
          convert P.add_mem hPmem hcomp using 1; ring))
      simpa using IsLocalization.map_units (M := P.primeCompl) Rp ⟨1 - e, hcompl⟩
    have hzero : algebraMap R Rp e = 0 := by
      refine (IsUnit.mul_left_inj hunit).mp ?_
      calc
        algebraMap R Rp e * (1 - algebraMap R Rp e) =
            algebraMap R Rp e - algebraMap R Rp e * algebraMap R Rp e := by ring
        _ = 0 := by rw [heP.eq, sub_self]
        _ = 0 * (1 - algebraMap R Rp e) := by simp
    rw [hzero, zero_mul, zero_mul]
  · have hone : algebraMap R Rp e = 1 :=
      (IsIdempotentElem.iff_eq_one_of_isUnit
        (IsLocalization.map_units (M := P.primeCompl) Rp ⟨e, hPmem⟩)).mp heP
    have hrank : Module.finrank Rp Q = r := hr ⟨P, inferInstance⟩ hPmem
    rw [hone, one_mul, one_mul, hrank]

end ProjectiveDeterminant

namespace RingHom

/-- Powers which descend on finitely many idempotent pieces have a common positive power which
descends globally. -/
theorem exists_pow_eq_map_of_idempotents {R T : Type u} {ι : Type*} [CommRing R]
    [CommRing T] [Fintype ι] (φ : R →+* T) (x : T) (rank : ι → ℕ) (e : ι → R) (p : R)
    (hsum : ∑ i, e i = 1) (hid : ∀ i, e i * e i = e i) (hrank : ∀ i, 0 < rank i)
    (hlocal : ∀ i, φ (e i) * φ p = φ (e i) * x ^ rank i) :
    ∃ (n : ℕ) (_ : 0 < n) (q : R), φ q = x ^ n := by
  classical
  set n := ∏ i, rank i with hn
  have hpow (i : ι) (k : ℕ) : e i ^ (k + 1) = e i := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hid]
  refine ⟨n, Finset.prod_pos fun i _ ↦ hrank i, ∑ i, e i * (e i * p) ^ (n / rank i), ?_⟩
  rw [map_sum]
  simp only [map_mul, map_pow]
  have hmul (i : ι) : rank i * (n / rank i) = n :=
    Nat.mul_div_cancel' (Finset.dvd_prod_of_mem (fun j ↦ rank j) (Finset.mem_univ i))
  simp_rw [hlocal, mul_pow, ← pow_mul, hmul]
  have hterm (i : ι) : φ (e i) * (φ (e i) ^ (n / rank i) * x ^ n) = φ (e i) * x ^ n := by
    rw [← mul_assoc, ← pow_succ', ← map_pow, hpow]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← map_sum, hsum, map_one, one_mul]

end RingHom

namespace AlgebraicGeometry

/-- On an affine morphism, the fibre rank agrees with the stalk rank of the algebra of global
functions. -/
theorem finrank_eq_rankAtStalk_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (hfinite : RingHom.Finite f.appTop.hom) (hflat : RingHom.Flat f.appTop.hom)
    (y : Y) :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    f.finrank y = Module.rankAtStalk Γ(X, ⊤) (Y.isoSpec.hom y) := by
  let _ : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let _ : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := RingHom.finite_algebraMap.mp hfinite
  let _ : Module.Flat Γ(Y, ⊤) Γ(X, ⊤) := RingHom.flat_algebraMap_iff.mp hflat
  set fSpec : Spec (.of Γ(X, ⊤)) ⟶ Spec (.of Γ(Y, ⊤)) :=
    Spec.map (CommRingCat.ofHom f.appTop.hom) with hfSpec
  let _ : IsFinite fSpec := by rw [hfSpec, IsFinite.SpecMap_iff]; exact hfinite
  let _ : Flat fSpec := by rw [hfSpec, Flat.SpecMap_iff]; exact hflat
  have hsq : IsPullback (𝟙 X) ((X.isoSpec.hom ≫ fSpec) ≫ Y.isoSpec.inv)
      (X.isoSpec.hom ≫ fSpec) Y.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [Category.assoc]⟩
  have hnat : X.isoSpec.hom ≫ fSpec = f ≫ Y.isoSpec.hom := Scheme.isoSpec_hom_naturality f
  have hf : f = (X.isoSpec.hom ≫ fSpec) ≫ Y.isoSpec.inv := by
    rw [hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    f.finrank y = ((X.isoSpec.hom ≫ fSpec) ≫ Y.isoSpec.inv).finrank y := by rw [← hf]
    _ = (X.isoSpec.hom ≫ fSpec).finrank (Y.isoSpec.hom y) :=
      Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq y
    _ = fSpec.finrank (Y.isoSpec.hom y) :=
      congrFun (Scheme.Hom.finrank_comp_left_of_isIso X.isoSpec.hom fSpec) (Y.isoSpec.hom y)
    _ = Module.rankAtStalk Γ(X, ⊤) (Y.isoSpec.hom y) := by
      rw [hfSpec]
      exact Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, ⊤) Γ(X, ⊤) (Y.isoSpec.hom y)

/-- The source and the target of an arrow have fibres of the same rank. -/
theorem finrank_source_eq_finrank_target {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (z : G.arrows.left) :
    G.source.left.finrank (G.source.left z) = G.target.left.finrank (G.target.left z) := by
  obtain ⟨hs, hsflat, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation G.source.left).mp
      inferInstance
  obtain ⟨ht, htflat, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation G.target.left).mp
      inferInstance
  let _ : IsFinite ((Over.forget S).map G.source) := hs
  let _ : Flat ((Over.forget S).map G.source) := hsflat
  let _ : IsFinite ((Over.forget S).map G.target) := ht
  let _ : Flat ((Over.forget S).map G.target) := htflat
  exact (Scheme.Hom.finrank_of_isPullback _ ((Over.forget S).map G.comp) _ _
    (IsPullback.map (Over.forget S) G.comp_source_isPullback).flip z).symm.trans
    (Scheme.Hom.finrank_of_isPullback _ ((Over.forget S).map G.comp) _ _
      (IsPullback.map (Over.forget S) G.target_comp_isPullback) z)

end AlgebraicGeometry

end
