module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading

/-!
# The chart of `Proj Sym(M ⊕ R)` at the extra coordinate

Let `R` be a commutative ring and `N` an `R`-module which splits as `N = j(M) ⊕ R t₀`, with
projections `p : N → M` and `q : N → R`. Grade the symmetric algebra `Sym_R(N)` by degree. The
homogeneous localization of `Sym_R(N)` at the degree-one element `t₀` is the symmetric algebra of
`M`:

  `Sym_R(N)_{(t₀)} ≅ Sym_R(M)`, `x / t₀ⁿ ↦ x(t₀ = 1)`, `j(m) / t₀ ↤ m`.

Geometrically, the standard open `D₊(t₀)` of `Proj Sym_R(M ⊕ R)` is the affine space
`Spec Sym_R(M)`: this is the local form of the statement that a vector bundle is the complement
of the divisor at infinity in its projective completion.

The statement is made for an arbitrary graded ring `A` identified with `Sym_R(N)` by a ring
isomorphism `e` respecting the gradings, because the graded rings of sections of a quasi-coherent
symmetric algebra over an affine open are such rings without being symmetric algebras on the nose.

## Main definitions

* `Stacks.SymmetricAway.LineSplitting`: a splitting `N = j(M) ⊕ R t₀`.
* `Stacks.SymmetricAway.LineSplitting.dehomogenize`: the `R`-algebra map `Sym_R(N) → Sym_R(M)`
  setting `t₀ = 1`, i.e. sending `n` to `p(n) + q(n)`.
* `Stacks.SymmetricAway.lineChartEquiv`: the ring isomorphism `Sym_R(M) ≃+* A_{(t)}`.

## Main results

* `Stacks.SymmetricAway.lineChartEquiv_ι`: it sends `m` to the fraction `j(m) / t`.
* `Stacks.SymmetricAway.lineChartEquiv_algebraMap`: it sends a scalar to the corresponding
  degree-zero fraction.
* `Stacks.SymmetricAway.lineChartEquiv_symm_mk`: its inverse sends `x / tⁿ` to the
  dehomogenization of `x`.
-/

@[expose] public noncomputable section

open HomogeneousLocalization

namespace Stacks.SymmetricAway


/-- **A splitting `N = j(M) ⊕ R t₀`** of a module, recorded by the inclusion `j`, the element `t₀`
and the two projections `p : N → M` and `q : N → R`. -/
structure LineSplitting (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] where
  /-- The inclusion of the first summand. -/
  j : M →ₗ[R] N
  /-- The projection onto the first summand. -/
  p : N →ₗ[R] M
  /-- The projection onto the line. -/
  q : N →ₗ[R] R
  /-- The generator of the line. -/
  t₀ : N
  p_j (m : M) : p (j m) = m
  q_j (m : M) : q (j m) = 0
  p_t₀ : p t₀ = 0
  q_t₀ : q t₀ = 1
  j_p_add_q_smul (n : N) : j (p n) + q n • t₀ = n

section Dehomogenize

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (S : LineSplitting R M N)

/-- **Dehomogenization along a splitting `N = j(M) ⊕ R t₀`**: the `R`-algebra map
`Sym_R(N) → Sym_R(M)` sending a degree-one element `n` to `p(n) + q(n)`; it sets `t₀ = 1`. -/
def LineSplitting.dehomogenize : SymmetricAlgebra R N →ₐ[R] SymmetricAlgebra R M :=
  SymmetricAlgebra.lift
    (SymmetricAlgebra.ι R M ∘ₗ S.p + Algebra.linearMap R (SymmetricAlgebra R M) ∘ₗ S.q)

@[simp]
theorem LineSplitting.dehomogenize_ι (n : N) :
    S.dehomogenize (SymmetricAlgebra.ι R N n) =
      SymmetricAlgebra.ι R M (S.p n) + algebraMap R (SymmetricAlgebra R M) (S.q n) := by
  simp [LineSplitting.dehomogenize]

end Dehomogenize

section LineChart

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (S : LineSplitting R M N)
  {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  (e : A ≃+* SymmetricAlgebra R N)
  (he : ∀ (n : ℕ) (x : A), e x ∈ SymPow.symmetricPower n R N ↔ x ∈ 𝒜 n)
  {t : A} (ht : t ∈ 𝒜 1) (het : e t = SymmetricAlgebra.ι R N S.t₀)

include he in
theorem symm_mem_of_mem {n : ℕ} {y : SymmetricAlgebra R N}
    (hy : y ∈ SymPow.symmetricPower n R N) : e.symm y ∈ 𝒜 n :=
  (he n _).1 (by rwa [RingEquiv.apply_symm_apply])

include he in
theorem symm_algebraMap_mem (r : R) :
    e.symm (algebraMap R (SymmetricAlgebra R N) r) ∈ 𝒜 0 :=
  symm_mem_of_mem 𝒜 e he (by
    rw [SymPow.symmetricPower, pow_zero]
    exact Submodule.algebraMap_mem r)

include he in
theorem symm_ι_mem (n : N) : e.symm (SymmetricAlgebra.ι R N n) ∈ 𝒜 1 :=
  symm_mem_of_mem 𝒜 e he (by
    rw [SymPow.symmetricPower, pow_one]
    exact LinearMap.mem_range_self _ n)

/-- The structure map `R → A₀` that `e` induces. -/
def baseRingHom : R →+* 𝒜 0 where
  toFun r := ⟨e.symm (algebraMap R _ r), symm_algebraMap_mem 𝒜 e he r⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[simp]
theorem coe_baseRingHom (r : R) :
    (baseRingHom 𝒜 e he r : A) = e.symm (algebraMap R _ r) := rfl

/-- The value of a degree-zero fraction `c / 1` in the full localization. -/
theorem val_algebraMap_zero {P : Submonoid A} (c : 𝒜 0) :
    (algebraMap (𝒜 0) (HomogeneousLocalization 𝒜 P) c).val =
      algebraMap A (Localization P) (c : A) := by
  rw [algebraMap_eq]
  exact (val_mk _).trans (Localization.mk_one_eq_algebraMap _)

/-- The `R`-algebra structure on `A_{(t)}` that `e` induces. -/
abbrev awayAlgebra : Algebra R (Away 𝒜 t) :=
  ((algebraMap (𝒜 0) (Away 𝒜 t)).comp (baseRingHom 𝒜 e he)).toAlgebra

theorem val_awayAlgebra_algebraMap (r : R) :
    letI := awayAlgebra 𝒜 e he (t := t)
    (algebraMap R (Away 𝒜 t) r).val =
      algebraMap A (Localization.Away t) (e.symm (algebraMap R _ r)) := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, val_algebraMap_zero, coe_baseRingHom]

include ht in
/-- A degree-one fraction `c t / t` with `c` of degree zero is `c`. -/
theorem away_mk_mul_self (c : A) (hc : c ∈ 𝒜 0) (hct : c * t ∈ 𝒜 (1 • 1)) :
    Away.mk 𝒜 ht 1 (c * t) hct = algebraMap (𝒜 0) (Away 𝒜 t) ⟨c, hc⟩ := by
  apply val_injective
  rw [Away.val_mk, val_algebraMap_zero, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [mul_comm]⟩

include ht in
/-- A degree-zero fraction `c / t⁰` is `c`. -/
theorem away_mk_zero (c : A) (hc : c ∈ 𝒜 (0 • 1)) :
    Away.mk 𝒜 ht 0 c hc = algebraMap (𝒜 0) (Away 𝒜 t) ⟨c, by simpa using hc⟩ := by
  apply val_injective
  rw [Away.val_mk, val_algebraMap_zero, ← Localization.mk_one_eq_algebraMap]
  congr 1
  ext
  simp

/-- The `R`-linear map `M → A_{(t)}`, `m ↦ j(m) / t`, with `j(m)` read in `A` through `e`. -/
def chartLinearMap :
    letI := awayAlgebra 𝒜 e he (t := t)
    M →ₗ[R] Away 𝒜 t :=
  letI := awayAlgebra 𝒜 e he (t := t)
  { toFun m := Away.mk 𝒜 ht 1 (e.symm (SymmetricAlgebra.ι R N (S.j m)))
      (by simpa using symm_ι_mem 𝒜 e he (S.j m))
    map_add' a b := by
      apply val_injective
      simp only [Away.val_mk, map_add, val_add, Localization.add_mk_self]
    map_smul' r m := by
      apply val_injective
      rw [Algebra.smul_def, val_mul, val_awayAlgebra_algebraMap, Away.val_mk, Away.val_mk,
        RingHom.id_apply, map_smul, map_smul, Algebra.smul_def, map_mul,
        ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul] }

/-- **The ring map `Sym_R(M) → A_{(t)}`**, `m ↦ j(m) / t`. -/
def toAway : SymmetricAlgebra R M →+* Away 𝒜 t :=
  letI := awayAlgebra 𝒜 e he (t := t)
  (SymmetricAlgebra.lift (chartLinearMap S 𝒜 e he ht)).toRingHom

theorem toAway_ι (m : M) :
    toAway S 𝒜 e he ht (SymmetricAlgebra.ι R M m) =
      Away.mk 𝒜 ht 1 (e.symm (SymmetricAlgebra.ι R N (S.j m)))
        (by simpa using symm_ι_mem 𝒜 e he (S.j m)) := by
  let := awayAlgebra 𝒜 e he (t := t)
  exact SymmetricAlgebra.lift_ι_apply _ m

theorem toAway_algebraMap (r : R) :
    toAway S 𝒜 e he ht (algebraMap R _ r) =
      algebraMap (𝒜 0) (Away 𝒜 t) (baseRingHom 𝒜 e he r) := by
  let := awayAlgebra 𝒜 e he (t := t)
  exact (SymmetricAlgebra.lift (chartLinearMap S 𝒜 e he ht)).commutes r

/-- The dehomogenization `A → Sym_R(M)`, read through `e`. -/
def dehomogenizeHom : A →+* SymmetricAlgebra R M :=
  S.dehomogenize.toRingHom.comp e.toRingHom

theorem dehomogenizeHom_apply (x : A) :
    dehomogenizeHom S e x = S.dehomogenize (e x) := rfl

include het in
theorem dehomogenizeHom_t : dehomogenizeHom S e t = 1 := by
  simp [dehomogenizeHom, het, S.p_t₀, S.q_t₀]

/-- **The ring map `A_{(t)} → Sym_R(M)`**, `x / tⁿ ↦ x(t = 1)`. -/
def fromAway : Away 𝒜 t →+* SymmetricAlgebra R M :=
  (Localization.awayLift (dehomogenizeHom S e) t
      (isUnit_iff_exists_inv.mpr ⟨1, by rw [dehomogenizeHom_t S e het, one_mul]⟩)).comp
    (algebraMap (Away 𝒜 t) (Localization.Away t))

theorem fromAway_mk (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • 1)) :
    fromAway S 𝒜 e het (Away.mk 𝒜 ht n x hx) = dehomogenizeHom S e x := by
  rw [fromAway, RingHom.comp_apply, algebraMap_apply, Away.val_mk,
    Localization.awayLift_mk (dehomogenizeHom S e) t x 1
      (by rw [dehomogenizeHom_t S e het, one_mul]) n, one_pow, mul_one]

include ht in
theorem fromAway_algebraMap (c : 𝒜 0) :
    fromAway S 𝒜 e het (algebraMap (𝒜 0) (Away 𝒜 t) c) = dehomogenizeHom S e c := by
  have : algebraMap (𝒜 0) (Away 𝒜 t) c = Away.mk 𝒜 ht 0 c (by simp) := by
    rw [away_mk_zero 𝒜 ht]
  rw [this, fromAway_mk]

theorem fromAway_toAway (y : SymmetricAlgebra R M) :
    fromAway S 𝒜 e het (toAway S 𝒜 e he ht y) = y := by
  induction y using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [toAway_algebraMap, fromAway_algebraMap S 𝒜 e ht het, dehomogenizeHom_apply,
      coe_baseRingHom, RingEquiv.apply_symm_apply, AlgHom.commutes]
  | ι m =>
    rw [toAway_ι, fromAway_mk, dehomogenizeHom_apply, RingEquiv.apply_symm_apply,
      LineSplitting.dehomogenize_ι, S.p_j, S.q_j, map_zero, add_zero]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- A fraction whose numerator is a sum is the sum of the fractions. -/
private theorem away_mk_eq_add {n : ℕ} {x y z : A} (hx : x ∈ 𝒜 (n • 1)) (hy : y ∈ 𝒜 (n • 1))
    (hz : z ∈ 𝒜 (n • 1)) (h : z = x + y) :
    Away.mk 𝒜 ht n z hz = Away.mk 𝒜 ht n x hx + Away.mk 𝒜 ht n y hy := by
  apply val_injective
  simp only [Away.val_mk, val_add, Localization.add_mk_self, h]

include het in
/-- A degree-one fraction `x / t` is in the image of `toAway`. -/
theorem mk_one_mem_range (n : N) :
    Away.mk 𝒜 ht 1 (e.symm (SymmetricAlgebra.ι R N n))
        (by simpa using symm_ι_mem 𝒜 e he n) ∈ (toAway S 𝒜 e he ht).range := by
  refine ⟨SymmetricAlgebra.ι R M (S.p n) + algebraMap R _ (S.q n), ?_⟩
  rw [map_add, toAway_ι, toAway_algebraMap]
  have hsplit : e.symm (SymmetricAlgebra.ι R N n) =
      e.symm (SymmetricAlgebra.ι R N (S.j (S.p n))) + (baseRingHom 𝒜 e he (S.q n) : A) * t := by
    rw [coe_baseRingHom, ← e.symm_apply_apply t, het, ← map_mul, ← map_add, ← Algebra.smul_def,
      ← map_smul, ← map_add, S.j_p_add_q_smul]
  have hmem : (baseRingHom 𝒜 e he (S.q n) : A) * t ∈ 𝒜 (1 • 1) := by
    simpa using SetLike.mul_mem_graded (baseRingHom 𝒜 e he (S.q n)).2 ht
  rw [← away_mk_mul_self 𝒜 ht _ (baseRingHom 𝒜 e he (S.q n)).2 hmem]
  exact (away_mk_eq_add 𝒜 ht _ _ _ hsplit).symm

include het in
theorem toAway_surjective : Function.Surjective (toAway S 𝒜 e he ht) := by
  intro z
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 ht z
  have hx' : e x ∈ (LinearMap.range (SymmetricAlgebra.ι R N)) ^ n :=
    (he n x).2 (by simpa using hx)
  have hmem {i : ℕ} {y : SymmetricAlgebra R N}
      (hy : y ∈ (LinearMap.range (SymmetricAlgebra.ι R N)) ^ i) : e.symm y ∈ 𝒜 (i • 1) := by
    simpa using symm_mem_of_mem 𝒜 e he hy
  suffices H : ∀ (n : ℕ) (y : SymmetricAlgebra R N)
      (_ : y ∈ (LinearMap.range (SymmetricAlgebra.ι R N)) ^ n) (x : A) (hx : x ∈ 𝒜 (n • 1)),
      e x = y → Away.mk 𝒜 ht n x hx ∈ (toAway S 𝒜 e he ht).range from
    H n (e x) hx' x hx rfl
  intro n y hy
  induction hy using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    intro x hx hxy
    refine ⟨algebraMap R _ r, ?_⟩
    rw [toAway_algebraMap, away_mk_zero 𝒜 ht]
    congr 1
    ext
    simp [← hxy]
  | add y₁ y₂ i hy₁ hy₂ ih₁ ih₂ =>
    intro x hx hxy
    have h₁ := hmem hy₁
    have h₂ := hmem hy₂
    rw [away_mk_eq_add 𝒜 ht h₁ h₂ hx (by rw [← map_add, ← hxy, RingEquiv.symm_apply_apply])]
    exact add_mem (ih₁ _ h₁ (by simp)) (ih₂ _ h₂ (by simp))
  | mem_mul m hm i y hy ih =>
    intro x hx hxy
    obtain ⟨n', rfl⟩ := hm
    have h₁ := hmem hy
    have hprod : Away.mk 𝒜 ht (i + 1) x hx =
        Away.mk 𝒜 ht 1 (e.symm (SymmetricAlgebra.ι R N n'))
          (by simpa using symm_ι_mem 𝒜 e he n') * Away.mk 𝒜 ht i (e.symm y) h₁ := by
      apply val_injective
      simp only [Away.val_mk, val_mul, Localization.mk_mul, ← map_mul, ← hxy,
        RingEquiv.symm_apply_apply]
      congr 1
      ext
      simp [pow_succ, mul_comm]
    rw [hprod]
    exact mul_mem (mk_one_mem_range S 𝒜 e he ht het n') (ih _ h₁ (by simp))

/-- **`Sym_R(M) ≃+* A_{(t)}`**: the homogeneous localization at the extra coordinate `t` of a
graded ring identified with `Sym_R(M ⊕ R t₀)` is the symmetric algebra of `M`. -/
def lineChartEquiv : SymmetricAlgebra R M ≃+* Away 𝒜 t :=
  RingEquiv.ofRingHom (toAway S 𝒜 e he ht) (fromAway S 𝒜 e het)
    (RingHom.ext fun z => by
      obtain ⟨y, rfl⟩ := toAway_surjective S 𝒜 e he ht het z
      simp only [RingHom.comp_apply, RingHom.id_apply, fromAway_toAway S 𝒜 e he ht het y])
    (RingHom.ext fun y => fromAway_toAway S 𝒜 e he ht het y)

@[simp]
theorem lineChartEquiv_apply (y : SymmetricAlgebra R M) :
    lineChartEquiv S 𝒜 e he ht het y = toAway S 𝒜 e he ht y :=
  rfl

theorem lineChartEquiv_ι (m : M) :
    lineChartEquiv S 𝒜 e he ht het (SymmetricAlgebra.ι R M m) =
      Away.mk 𝒜 ht 1 (e.symm (SymmetricAlgebra.ι R N (S.j m)))
        (by simpa using symm_ι_mem 𝒜 e he (S.j m)) :=
  toAway_ι S 𝒜 e he ht m

theorem lineChartEquiv_algebraMap (r : R) :
    lineChartEquiv S 𝒜 e he ht het (algebraMap R _ r) =
      algebraMap (𝒜 0) (Away 𝒜 t) (baseRingHom 𝒜 e he r) :=
  toAway_algebraMap S 𝒜 e he ht r

theorem lineChartEquiv_symm_mk (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • 1)) :
    (lineChartEquiv S 𝒜 e he ht het).symm (Away.mk 𝒜 ht n x hx) =
      S.dehomogenize (e x) :=
  fromAway_mk S 𝒜 e ht het n x hx

end LineChart

end Stacks.SymmetricAway

end
