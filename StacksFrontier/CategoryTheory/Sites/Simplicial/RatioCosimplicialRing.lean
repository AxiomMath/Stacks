module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.Flat

/-!
# The cosimplicial ring of unit ratios

For `n ≥ 0` let `Rₙ` be the commutative ring generated over `ℤ` by elements `xᵢ` for the
vertices `i` of `⦋n⦌` and units `wᵢⱼ` for the pairs `i ≤ j`, subject to `xᵢ = wᵢⱼ xⱼ` and
`wᵢᵢ = 1`. A simplex map `θ` sends `xᵢ ↦ x_{θ i}` and `wᵢⱼ ↦ w_{θ i, θ j}`, which makes
`n ↦ Rₙ` a cosimplicial commutative ring.

This is the ring behind the counterexample to the positive assertion of Stacks 0D7K: both
degree-one faces `R₀ ⟶ R₁` are flat, since `R₁` is the ring of Laurent polynomials in `w₀₁`
over either of `x₀`, `x₁`, while in degree two the unit `w₀₂ - w₀₁ w₁₂` is not zero although it
kills `x₂`.

All names are in the namespace `CategoryTheory.RatioCosimplicialRing`.

## Main definitions

* `ratioRing`: the cosimplicial ring.

## Main results

* `flat_face`: the two degree-one faces `R₀ ⟶ R₁` are flat.
* `evalZero_eq_zero_of_mul`: if `(w₀₂ᵏ - w₁₂ᵏ w₀₁ᵏ) · a = 0` in `R₂` for `k ≥ 1` and `a` the image
  of `b ∈ R₀` along a vertex, then `b` vanishes at `x₀ = 0`.
-/

@[expose] public section

open CategoryTheory MvPolynomial

universe u

namespace CategoryTheory

namespace RatioCosimplicialRing

noncomputable section

/-- The generators in degree `n`: the vertices, and two copies of the pairs `i ≤ j`, for the
units and for their inverses. -/
abbrev Gen (n : ℕ) : Type u :=
  ULift.{u} (Fin (n + 1) ⊕ {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2} ⊕
    {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2})

/-- The vertex generator. -/
def gx {n : ℕ} (i : Fin (n + 1)) : Gen.{u} n := ⟨Sum.inl i⟩

/-- The unit generator. -/
def gw {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : Gen.{u} n := ⟨Sum.inr (Sum.inl ⟨(i, j), h⟩)⟩

/-- The inverse-unit generator. -/
def gv {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : Gen.{u} n := ⟨Sum.inr (Sum.inr ⟨(i, j), h⟩)⟩

/-- The action of a monotone map on generators. -/
def genMap {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) : Gen.{u} m → Gen.{u} n
  | ⟨Sum.inl i⟩ => gx (f i)
  | ⟨Sum.inr (Sum.inl ⟨(i, j), h⟩)⟩ => gw (f i) (f j) (f.monotone h)
  | ⟨Sum.inr (Sum.inr ⟨(i, j), h⟩)⟩ => gv (f i) (f j) (f.monotone h)

/-- A monotone map sends the vertex generator `xᵢ` to `x_{f i}`. -/
@[simp] theorem genMap_gx {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    genMap f (gx i) = gx.{u} (f i) := rfl

/-- A monotone map sends the unit generator `wᵢⱼ` to `w_{f i, f j}`. -/
@[simp] theorem genMap_gw {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i j : Fin (m + 1))
    (h : i ≤ j) : genMap f (gw i j h) = gw.{u} (f i) (f j) (f.monotone h) := rfl

/-- A monotone map sends the inverse-unit generator `vᵢⱼ` to `v_{f i, f j}`. -/
@[simp] theorem genMap_gv {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i j : Fin (m + 1))
    (h : i ≤ j) : genMap f (gv i j h) = gv.{u} (f i) (f j) (f.monotone h) := rfl

/-- The identity acts trivially on generators. -/
theorem genMap_id (n : ℕ) : genMap.{u} (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) = id := by
  funext g
  rcases g with ⟨g | g | g⟩
  · rfl
  · rcases g with ⟨⟨i, j⟩, h⟩; rfl
  · rcases g with ⟨⟨i, j⟩, h⟩; rfl

/-- The action on generators is compatible with composition. -/
theorem genMap_comp {l m n : ℕ} (f : Fin (l + 1) →o Fin (m + 1)) (f' : Fin (m + 1) →o Fin (n + 1)) :
    genMap.{u} (f'.comp f) = genMap f' ∘ genMap f := by
  funext g
  rcases g with ⟨g | g | g⟩
  · rfl
  · rcases g with ⟨⟨i, j⟩, h⟩; rfl
  · rcases g with ⟨⟨i, j⟩, h⟩; rfl

/-- The defining relations in degree `n`. -/
def rel (n : ℕ) : Set (MvPolynomial (Gen.{u} n) ℤ) :=
  {p | (∃ i j h, p = X (gx i) - X (gw i j h) * X (gx j)) ∨
    (∃ i j h, p = X (gw i j h) * X (gv i j h) - 1) ∨ (∃ i, p = X (gw i i le_rfl) - 1)}

/-- The ideal of relations. -/
abbrev relIdeal (n : ℕ) : Ideal (MvPolynomial (Gen.{u} n) ℤ) := Ideal.span (rel n)

/-- The ring in degree `n`. -/
abbrev Ring (n : ℕ) : Type u := MvPolynomial (Gen.{u} n) ℤ ⧸ relIdeal.{u} n

/-- A generator, in the ring. -/
abbrev mk {n : ℕ} (g : Gen.{u} n) : Ring.{u} n := Ideal.Quotient.mk _ (X g)

/-- The relation `xᵢ = wᵢⱼ xⱼ` in `Rₙ`. -/
theorem mk_x_eq (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    mk.{u} (gx i) = mk (gw i j h) * mk (gx j) := by
  rw [← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Or.inl ⟨i, j, h, rfl⟩)

/-- The relation `wᵢⱼ vᵢⱼ = 1` in `Rₙ`. -/
theorem mk_w_mul_v (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    mk.{u} (gw i j h) * mk (gv i j h) = 1 := by
  rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Or.inr (Or.inl ⟨i, j, h, rfl⟩))

/-- The relation `wᵢᵢ = 1` in `Rₙ`. -/
theorem mk_w_self (n : ℕ) (i : Fin (n + 1)) : mk.{u} (gw i i le_rfl) = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Or.inr (Or.inr ⟨i, rfl⟩))

/-- Renaming the generators along a monotone map sends relations to relations. -/
theorem rename_rel_le {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    relIdeal.{u} m ≤ (relIdeal.{u} n).comap (rename (genMap f)).toRingHom := by
  rw [Ideal.span_le]
  rintro p (⟨i, j, h, rfl⟩ | ⟨i, j, h, rfl⟩ | ⟨i, rfl⟩) <;>
    simp only [SetLike.mem_coe, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      map_sub, map_mul, map_one, rename_X, genMap_gx, genMap_gw, genMap_gv] <;>
    apply Ideal.subset_span
  · exact Or.inl ⟨_, _, _, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- The ring map attached to a monotone map. -/
def ringMap {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) : Ring.{u} m →+* Ring.{u} n :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (rename (genMap f)).toRingHom)
    (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact rename_rel_le f ha)

/-- The ring map of a monotone map acts on generators by `genMap`. -/
@[simp] theorem ringMap_mk {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (g : Gen.{u} m) :
    ringMap f (mk g) = mk (genMap f g) := by
  simp [ringMap, mk]

/-- Two ring maps out of `Rₙ` agreeing on the generators are equal. -/
theorem ringHom_ext {n : ℕ} {B : Type*} [CommRing B] {φ ψ : Ring.{u} n →+* B}
    (h : ∀ g, φ (mk g) = ψ (mk g)) : φ = ψ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply]
    exact RingHom.congr_fun (RingHom.ext_int (φ.comp ((Ideal.Quotient.mk _).comp C))
      (ψ.comp ((Ideal.Quotient.mk _).comp C))) r
  · exact h

/-- The ring map of the identity is the identity. -/
theorem ringMap_id (n : ℕ) : ringMap.{u} (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) =
    RingHom.id _ :=
  ringHom_ext fun g => by rw [ringMap_mk, genMap_id]; rfl

/-- The ring map of a composite is the composite of the ring maps. -/
theorem ringMap_comp {l m n : ℕ} (f : Fin (l + 1) →o Fin (m + 1))
    (f' : Fin (m + 1) →o Fin (n + 1)) :
    ringMap.{u} (f'.comp f) = (ringMap f').comp (ringMap f) :=
  ringHom_ext fun g => by
    rw [RingHom.comp_apply, ringMap_mk, ringMap_mk, ringMap_mk, genMap_comp]; rfl

/-- **The cosimplicial ring of unit ratios.** -/
def ratioRing : SimplexCategory ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of (Ring.{u} X.len)
  map θ := CommRingCat.ofHom (ringMap θ.toOrderHom)
  map_id X := CommRingCat.hom_ext (ringMap_id X.len)
  map_comp θ θ' := CommRingCat.hom_ext (ringMap_comp θ.toOrderHom θ'.toOrderHom)

/-- The cosimplicial ring acts on generators by `genMap`. -/
theorem ratioRing_map_mk {X Y : SimplexCategory} (θ : X ⟶ Y) (g : Gen.{u} X.len) :
    (ratioRing.{u}.map θ).hom (mk g) = mk (genMap θ.toOrderHom g) :=
  ringMap_mk _ _

/-! ### Maps out of the rings -/

section Lift

variable {n : ℕ} {B : Type*} [CommRing B] (val : Gen.{u} n → B)
  (hx : ∀ i j h, val (gx i) = val (gw i j h) * val (gx j))
  (hwv : ∀ i j h, val (gw i j h) * val (gv i j h) = 1)
  (hww : ∀ i, val (gw i i le_rfl) = 1)

/-- The ring map out of `Rₙ` with given values on the generators satisfying the relations. -/
def lift : Ring.{u} n →+* B :=
  Ideal.Quotient.lift _ (eval₂Hom (Int.castRingHom B) val) (fun a ha => by
    have : relIdeal.{u} n ≤ RingHom.ker (eval₂Hom (Int.castRingHom B) val) := by
      rw [Ideal.span_le]
      rintro p (⟨i, j, h, rfl⟩ | ⟨i, j, h, rfl⟩ | ⟨i, rfl⟩) <;>
        simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_one, eval₂Hom_X',
          sub_eq_zero]
      · exact hx i j h
      · exact hwv i j h
      · exact hww i
    exact this ha)

/-- The lift takes the given value on each generator. -/
@[simp] theorem lift_mk (g : Gen.{u} n) : lift val hx hwv hww (mk g) = val g := by
  simp [lift, mk]

end Lift

/-- The relation `vᵢᵢ = 1` in `Rₙ`. -/
theorem mk_v_self (n : ℕ) (i : Fin (n + 1)) : mk.{u} (gv i i le_rfl) = 1 := by
  simpa [mk_w_self] using mk_w_mul_v.{u} n i i le_rfl

/-- `wᵢⱼ = 1` when `i = j`. -/
theorem mk_w_eq_one {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) (e : i = j) :
    mk.{u} (gw i j h) = 1 := by
  subst e; exact mk_w_self n i

/-- `vᵢⱼ = 1` when `i = j`. -/
theorem mk_v_eq_one {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) (e : i = j) :
    mk.{u} (gv i j h) = 1 := by
  subst e; exact mk_v_self n i

/-- The unit `wᵢⱼ`. -/
def unitW {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : (Ring.{u} n)ˣ :=
  ⟨mk (gw i j h), mk (gv i j h), mk_w_mul_v n i j h, by rw [mul_comm]; exact mk_w_mul_v n i j h⟩

/-! ### Degree zero -/

/-- The vertex of degree zero, `t = x₀ ∈ R₀`. -/
abbrev t : Ring.{u} 0 := mk (gx 0)

/-- `R₀` maps to `ℤ[X]`, `x₀ ↦ X`. -/
def toPoly : Ring.{u} 0 →+* Polynomial ℤ :=
  lift (fun g => Sum.elim (fun _ => Polynomial.X) (fun _ => 1) g.down)
    (fun i j h => by simp [gx, gw]) (fun i j h => by simp [gw, gv]) (fun i => by simp [gw])

/-- `ℤ[X]` maps to `R₀`, `X ↦ x₀`. -/
def ofPoly : Polynomial ℤ →+* Ring.{u} 0 :=
  Polynomial.eval₂RingHom (Int.castRingHom _) t

/-- `ofPoly` is a left inverse of `toPoly`. -/
theorem ofPoly_toPoly (a : Ring.{u} 0) : ofPoly (toPoly a) = a := by
  have : ofPoly.{u}.comp toPoly = RingHom.id _ := by
    apply ringHom_ext
    rintro ⟨g | ⟨⟨i, j⟩, h⟩ | ⟨⟨i, j⟩, h⟩⟩
    · fin_cases g; simp [toPoly, ofPoly, gx, mk, t]
    · fin_cases i; fin_cases j
      simp only [toPoly, RingHom.comp_apply, lift_mk, RingHom.id_apply, Sum.elim_inr, map_one]
      exact (mk_w_self 0 0).symm
    · fin_cases i; fin_cases j
      simp only [toPoly, RingHom.comp_apply, lift_mk, RingHom.id_apply, Sum.elim_inr, map_one]
      exact (mk_v_self 0 0).symm
  exact RingHom.congr_fun this a

/-- `toPoly` is a left inverse of `ofPoly`. -/
theorem toPoly_ofPoly (p : Polynomial ℤ) : toPoly.{u} (ofPoly p) = p := by
  have : toPoly.{u}.comp ofPoly = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro r; simp [ofPoly]
    · simp [ofPoly, toPoly, t, gx]
  exact RingHom.congr_fun this p

/-- `R₀ ≅ ℤ[X]`. -/
def polyEquiv : Ring.{u} 0 ≃+* Polynomial ℤ :=
  RingEquiv.ofRingHom toPoly ofPoly
    (RingHom.ext toPoly_ofPoly) (RingHom.ext ofPoly_toPoly)

/-- `toPoly` sends `t = x₀` to `X`. -/
theorem toPoly_t : toPoly.{u} t = Polynomial.X := by simp [toPoly, t, gx]

/-- `R₀ ≅ ℤ[X]` is a domain. -/
instance : IsDomain (Ring.{u} 0) :=
  (MulEquiv.isDomain_iff polyEquiv.{u}.toMulEquiv).2 inferInstance

/-- `t = x₀` is nonzero in `R₀`. -/
theorem t_ne_zero : t.{u} ≠ 0 := by
  intro h
  have := congrArg toPoly.{u} h
  rw [toPoly_t, map_zero] at this
  exact Polynomial.X_ne_zero this

/-- `ε₀ : R₀ ⟶ ℤ`, the value at `x₀ = 0`. -/
def evalZero : Ring.{u} 0 →+* ℤ := (Polynomial.evalRingHom 0).comp toPoly

/-- An element of `R₀` vanishing at `x₀ = 0` is divisible by `t`. -/
theorem t_dvd_of_evalZero {a : Ring.{u} 0} (ha : evalZero a = 0) : t ∣ a := by
  have h : Polynomial.X ∣ toPoly a := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]; exact ha
  obtain ⟨q, hq⟩ := h
  refine ⟨ofPoly q, ?_⟩
  apply polyEquiv.{u}.injective
  show toPoly a = toPoly (t * ofPoly q)
  rw [map_mul, toPoly_t, toPoly_ofPoly, hq]

/-- An element of `R₀` divisible by every power of `t` is zero. -/
theorem eq_zero_of_forall_t_pow_dvd {a : Ring.{u} 0} (ha : ∀ k : ℕ, t ^ k ∣ a) : a = 0 := by
  apply polyEquiv.{u}.injective
  rw [map_zero]
  show toPoly a = 0
  by_contra hne
  set d := (toPoly a).natDegree with hd
  obtain ⟨q, hq⟩ := ha (d + 1)
  have hq' : toPoly a = Polynomial.X ^ (d + 1) * toPoly q := by
    rw [hq, map_mul, map_pow, toPoly_t]
  have hq0 : toPoly q ≠ 0 := by rintro h; rw [h, mul_zero] at hq'; exact hne hq'
  have := congrArg Polynomial.natDegree hq'
  rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hq0,
    Polynomial.natDegree_X_pow, ← hd] at this
  omega

/-! ### Degree one -/

open LaurentPolynomial

/-- The face `δ¹ᵢ : R₀ ⟶ R₁`. -/
abbrev face (i : Fin 2) : Ring.{u} 0 →+* Ring.{u} 1 := ringMap (SimplexCategory.δ i).toOrderHom

/-- The Laurent presentation of `R₁` over `R₀` along `δ¹ᵢ`: `xⱼ ↦ T^{(1 - i) - j} t` and
`wⱼₖ ↦ T^{k - j}`. -/
def toLaurent (i : Fin 2) : Ring.{u} 1 →+* (Ring.{u} 0)[T;T⁻¹] :=
  lift (fun g => Sum.elim (fun j : Fin 2 => T ((1 - (i : ℤ)) - j) * LaurentPolynomial.C t)
      (Sum.elim (fun p : {p : Fin 2 × Fin 2 // p.1 ≤ p.2} => T ((p.1.2 : ℤ) - p.1.1))
        (fun p : {p : Fin 2 × Fin 2 // p.1 ≤ p.2} => T ((p.1.1 : ℤ) - p.1.2))) g.down)
    (fun j k h => by
      simp only [gx, gw, Sum.elim_inl, Sum.elim_inr, ← mul_assoc, ← T_add]
      congr 2; ring)
    (fun j k h => by simp only [gw, gv, Sum.elim_inr, Sum.elim_inl, ← T_add]; simp)
    (fun j => by simp [gw])

/-- The face `δ¹₁` sends the vertex `0` to `0`. -/
theorem δ_one_zero : (SimplexCategory.δ (1 : Fin 2)).toOrderHom 0 = 0 := rfl
/-- The face `δ¹₀` sends the vertex `0` to `1`. -/
theorem δ_zero_zero : (SimplexCategory.δ (0 : Fin 2)).toOrderHom 0 = 1 := rfl

/-- `toLaurent` on a vertex generator: `xⱼ ↦ T^{(1 - i) - j} t`. -/
theorem toLaurent_gx (i : Fin 2) (j : Fin 2) :
    toLaurent.{u} i (mk (gx j)) = T ((1 - (i : ℤ)) - j) * LaurentPolynomial.C t := by
  simp [toLaurent, gx]

/-- `toLaurent` on a unit generator: `wⱼₖ ↦ T^{k - j}`. -/
theorem toLaurent_gw (i : Fin 2) (j k : Fin 2) (h : j ≤ k) :
    toLaurent.{u} i (mk (gw j k h)) = T ((k : ℤ) - j) := by
  simp [toLaurent, gw]

/-- `toLaurent` on an inverse-unit generator: `vⱼₖ ↦ T^{j - k}`. -/
theorem toLaurent_gv (i : Fin 2) (j k : Fin 2) (h : j ≤ k) :
    toLaurent.{u} i (mk (gv j k h)) = T ((j : ℤ) - k) := by
  simp [toLaurent, gv]

/-- Every generator is a vertex, a unit or an inverse-unit generator. -/
theorem gen_cases {n : ℕ} (g : Gen.{u} n) :
    (∃ i, g = gx i) ∨ (∃ i j h, g = gw i j h) ∨ (∃ i j h, g = gv i j h) := by
  rcases g with ⟨g | ⟨⟨i, j⟩, h⟩ | ⟨⟨i, j⟩, h⟩⟩
  · exact Or.inl ⟨g, rfl⟩
  · exact Or.inr (Or.inl ⟨i, j, h, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, j, h, rfl⟩)

/-- The exponent of `T` at the image of the vertex of `R₀` under `δ¹ᵢ` is zero. -/
theorem face_exponent (i : Fin 2) :
    (1 - (i : ℤ)) - ((SimplexCategory.δ i).toOrderHom 0 : ℕ) = 0 := by
  fin_cases i <;> rfl

/-- `Fin (0 + 1)` has at most one element. -/
instance : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))

/-- `toLaurent` after the face `δ¹ᵢ` is the inclusion of constants. -/
theorem toLaurent_comp_face (i : Fin 2) :
    (toLaurent.{u} i).comp (face i) = LaurentPolynomial.C := by
  apply ringHom_ext
  intro g
  obtain ⟨j, rfl⟩ | ⟨j, k, h, rfl⟩ | ⟨j, k, h, rfl⟩ := gen_cases g
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [RingHom.comp_apply, face, ringMap_mk, genMap_gx, toLaurent_gx]
    rw [face_exponent, T_zero, one_mul]
  · simp only [RingHom.comp_apply, face, ringMap_mk, genMap_gw, toLaurent_gw]
    rw [mk_w_eq_one h (Subsingleton.elim _ _), map_one, Subsingleton.elim j k, sub_self,
      T_zero]
  · simp only [RingHom.comp_apply, face, ringMap_mk, genMap_gv, toLaurent_gv]
    rw [mk_v_eq_one h (Subsingleton.elim _ _), map_one, Subsingleton.elim j k, sub_self,
      T_zero]

/-- The integer powers of a unit `v` of `R[T, T⁻¹]` with `v = T` are the powers of `T`. -/
theorem units_coe_zpow_eq_T {R : Type*} [CommRing R] (v : (R[T;T⁻¹])ˣ)
    (hv : (v : R[T;T⁻¹]) = T 1) (x : ℤ) : ((v ^ x : (R[T;T⁻¹])ˣ) : R[T;T⁻¹]) = T x := by
  have hinv : ((v⁻¹ : (R[T;T⁻¹])ˣ) : R[T;T⁻¹]) = T (-1) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hv, ← T_add]; simp
  induction x using Int.induction_on with
  | zero => simp
  | succ k ih => rw [zpow_add_one, Units.val_mul, ih, hv, ← T_add]
  | pred k ih => rw [zpow_sub_one, Units.val_mul, ih, hinv, ← T_add]; rfl

/-- The unit `w₀₁ ∈ R₁`. -/
abbrev w₀₁ : (Ring.{u} 1)ˣ := unitW 0 1 (by decide)

/-- The inverse of `toLaurent`: `T ↦ w₀₁`, along `δ¹ᵢ` on the coefficients. -/
def ofLaurent (i : Fin 2) : (Ring.{u} 0)[T;T⁻¹] →+* Ring.{u} 1 :=
  let := (face.{u} i).toAlgebra
  (AddMonoidAlgebra.lift (Ring.{u} 0) (Ring.{u} 1) ℤ
    ((Units.coeHom _).comp (zpowersHom _ w₀₁.{u}))).toRingHom

/-- `ofLaurent` on constants is the face `δ¹ᵢ`. -/
theorem ofLaurent_C (i : Fin 2) (a : Ring.{u} 0) :
    ofLaurent i (LaurentPolynomial.C a) = face i a := by
  let := (face.{u} i).toAlgebra
  show (AddMonoidAlgebra.lift (Ring.{u} 0) (Ring.{u} 1) ℤ _) (algebraMap _ _ a) = _
  rw [AlgHom.commutes]; rfl

/-- `ofLaurent` sends `T^x` to `w₀₁^x`. -/
theorem ofLaurent_T (i : Fin 2) (x : ℤ) :
    ofLaurent.{u} i (T x) = ((w₀₁.{u} ^ x : (Ring.{u} 1)ˣ) : Ring.{u} 1) := by
  let := (face.{u} i).toAlgebra
  show (AddMonoidAlgebra.lift (Ring.{u} 0) (Ring.{u} 1) ℤ _) (AddMonoidAlgebra.single x 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

/-- `ofLaurent` is a left inverse of `toLaurent`. -/
theorem ofLaurent_toLaurent (i : Fin 2) (a : Ring.{u} 1) : ofLaurent i (toLaurent i a) = a := by
  have : (ofLaurent.{u} i).comp (toLaurent i) = RingHom.id _ := by
    apply ringHom_ext
    intro g
    have hx := mk_x_eq.{u} 1 0 1 (by decide)
    obtain ⟨j, rfl⟩ | ⟨j, k, h, rfl⟩ | ⟨j, k, h, rfl⟩ := gen_cases g
    · simp only [RingHom.comp_apply, RingHom.id_apply, toLaurent_gx, map_mul, ofLaurent_C,
        ofLaurent_T, face, t, ringMap_mk, genMap_gx]
      fin_cases i <;> fin_cases j
      · show ((w₀₁ ^ (1 : ℤ) : (Ring.{u} 1)ˣ) : Ring.{u} 1) * mk (gx 1) = mk (gx 0)
        rw [zpow_one]; exact hx.symm
      · show ((w₀₁ ^ (0 : ℤ) : (Ring.{u} 1)ˣ) : Ring.{u} 1) * mk (gx 1) = mk (gx 1)
        rw [zpow_zero, Units.val_one, one_mul]
      · show ((w₀₁ ^ (0 : ℤ) : (Ring.{u} 1)ˣ) : Ring.{u} 1) * mk (gx 0) = mk (gx 0)
        rw [zpow_zero, Units.val_one, one_mul]
      · show ((w₀₁ ^ (-1 : ℤ) : (Ring.{u} 1)ˣ) : Ring.{u} 1) * mk (gx 0) = mk (gx 1)
        rw [zpow_neg_one, hx]
        exact Units.inv_mul_cancel_left w₀₁ _
    · simp only [RingHom.comp_apply, RingHom.id_apply, toLaurent_gw, ofLaurent_T]
      fin_cases j <;> fin_cases k
      · show ((w₀₁ ^ (0 : ℤ) : (Ring.{u} 1)ˣ) : Ring.{u} 1) = mk (gw 0 0 h)
        rw [zpow_zero, Units.val_one]; exact (mk_w_eq_one h rfl).symm
      · show ((w₀₁ ^ (1 : ℤ) : (Ring.{u} 1)ˣ) : Ring.{u} 1) = mk (gw 0 1 h)
        rw [zpow_one]; rfl
      · exact absurd h (by decide)
      · show ((w₀₁ ^ (0 : ℤ) : (Ring.{u} 1)ˣ) : Ring.{u} 1) = mk (gw 1 1 h)
        rw [zpow_zero, Units.val_one]; exact (mk_w_eq_one h rfl).symm
    · simp only [RingHom.comp_apply, RingHom.id_apply, toLaurent_gv, ofLaurent_T]
      fin_cases j <;> fin_cases k
      · show ((w₀₁ ^ (0 : ℤ) : (Ring.{u} 1)ˣ) : Ring.{u} 1) = mk (gv 0 0 h)
        rw [zpow_zero, Units.val_one]; exact (mk_v_eq_one h rfl).symm
      · show ((w₀₁ ^ (-1 : ℤ) : (Ring.{u} 1)ˣ) : Ring.{u} 1) = mk (gv 0 1 h)
        rw [zpow_neg_one]; rfl
      · exact absurd h (by decide)
      · show ((w₀₁ ^ (0 : ℤ) : (Ring.{u} 1)ˣ) : Ring.{u} 1) = mk (gv 1 1 h)
        rw [zpow_zero, Units.val_one]; exact (mk_v_eq_one h rfl).symm
  exact RingHom.congr_fun this a

/-- `toLaurent` is a left inverse of `ofLaurent`. -/
theorem toLaurent_ofLaurent (i : Fin 2) (p : (Ring.{u} 0)[T;T⁻¹]) :
    toLaurent i (ofLaurent i p) = p := by
  have : (toLaurent.{u} i).comp (ofLaurent i) = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro b
      show toLaurent i (ofLaurent i (LaurentPolynomial.C b)) = LaurentPolynomial.C b
      rw [ofLaurent_C, ← RingHom.comp_apply, toLaurent_comp_face]
    · intro x
      show toLaurent i (ofLaurent i (T x)) = T x
      rw [ofLaurent_T]
      rw [show toLaurent i ((w₀₁ ^ x : (Ring.{u} 1)ˣ) : Ring.{u} 1) =
          ((Units.map (toLaurent.{u} i : Ring.{u} 1 →* (Ring.{u} 0)[T;T⁻¹]) (w₀₁ ^ x) :
            ((Ring.{u} 0)[T;T⁻¹])ˣ) : (Ring.{u} 0)[T;T⁻¹]) from rfl, map_zpow]
      apply units_coe_zpow_eq_T
      show toLaurent i (mk (gw 0 1 _)) = T 1
      rw [toLaurent_gw]; rfl
  exact RingHom.congr_fun this p

/-- The face `δ¹ᵢ` is the inclusion of constants followed by `ofLaurent`. -/
theorem face_eq (i : Fin 2) : face.{u} i = (ofLaurent i).comp LaurentPolynomial.C :=
  RingHom.ext fun a => (ofLaurent_C i a).symm

/-- The inclusion of constants into Laurent polynomials is injective. -/
theorem laurentC_injective {R : Type*} [CommRing R] :
    Function.Injective (LaurentPolynomial.C : R →+* R[T;T⁻¹]) :=
  fun _ _ h => AddMonoidAlgebra.single_right_inj.mp h

/-- **The degree-one faces are flat.** -/
theorem flat_face (i : Fin 2) : (face.{u} i).Flat := by
  rw [face_eq]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective ⟨?_, ?_⟩)
  · exact RingHom.flat_algebraMap_iff.2 inferInstance
  · exact Function.LeftInverse.injective (g := toLaurent i) (toLaurent_ofLaurent i)
  · exact Function.LeftInverse.surjective (f := ofLaurent i) (ofLaurent_toLaurent i)

/-- `toLaurent` is injective. -/
theorem toLaurent_injective (i : Fin 2) : Function.Injective (toLaurent.{u} i) :=
  Function.LeftInverse.injective (ofLaurent_toLaurent i)

/-- Powers of `x₁` are nonzerodivisors in `R₁`. -/
theorem x₁_pow_mul_eq_zero {k : ℕ} {a : Ring.{u} 1} (h : mk (gx 1) ^ k * a = 0) : a = 0 := by
  apply toLaurent_injective 0
  have h' := congrArg (toLaurent.{u} 0) h
  rw [map_mul, map_pow, toLaurent_gx, map_zero] at h'
  rw [map_zero]
  refine (mul_eq_zero.1 h').resolve_left (pow_ne_zero _ ?_)
  have e : (1 - ((0 : Fin 2) : ℤ)) - ((1 : Fin 2) : ℕ) = 0 := rfl
  rw [e, T_zero, one_mul]
  exact fun hC => t_ne_zero ((map_eq_zero_iff _ laurentC_injective).1 hC)

/-! ### Degree two -/

/-- `ε : R₂ ⟶ ℤ[T, T⁻¹]`: `xᵢ ↦ 0`, `w₀₂ ↦ T`, and the other units to `1`. -/
def evalUnits : Ring.{u} 2 →+* ℤ[T;T⁻¹] :=
  lift (fun g => Sum.elim (fun _ : Fin 3 => (0 : ℤ[T;T⁻¹]))
      (Sum.elim (fun p : {p : Fin 3 × Fin 3 // p.1 ≤ p.2} => if p.1 = (0, 2) then T 1 else 1)
        (fun p : {p : Fin 3 × Fin 3 // p.1 ≤ p.2} => if p.1 = (0, 2) then T (-1) else 1)) g.down)
    (fun i j h => by simp [gx])
    (fun i j h => by
      simp only [gw, gv, Sum.elim_inr, Sum.elim_inl]
      split_ifs
      · rw [← T_add]; norm_num
      · rw [mul_one])
    (fun i => by
      simp only [gw, Sum.elim_inr, Sum.elim_inl]
      rw [if_neg]
      rintro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1] at h2
      exact absurd h2 (by decide))

/-- Along a vertex `R₀ ⟶ R₂`, `evalUnits` is evaluation at `x₀ = 0` followed by the inclusion of
constants. -/
theorem evalUnits_comp_ringMap (f : Fin 1 →o Fin 3) :
    evalUnits.{u}.comp (ringMap f) = LaurentPolynomial.C.comp ((Int.castRingHom ℤ).comp
      evalZero) := by
  apply ringHom_ext
  intro g
  have hne : (f 0, f 0) ≠ ((0 : Fin 3), (2 : Fin 3)) := by
    intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1] at h2
    exact absurd h2 (by decide)
  obtain ⟨j, rfl⟩ | ⟨j, k, h, rfl⟩ | ⟨j, k, h, rfl⟩ := gen_cases g
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [RingHom.comp_apply, RingHom.comp_apply, ringMap_mk, genMap_gx]
    simp [evalUnits, gx, evalZero, toPoly]
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    obtain rfl : k = 0 := Subsingleton.elim _ _
    rw [RingHom.comp_apply, RingHom.comp_apply, ringMap_mk, genMap_gw, mk_w_eq_one h rfl,
      map_one, map_one]
    simp only [evalUnits, lift_mk, gw, Sum.elim_inr, Sum.elim_inl, if_neg hne]
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    obtain rfl : k = 0 := Subsingleton.elim _ _
    rw [RingHom.comp_apply, RingHom.comp_apply, ringMap_mk, genMap_gv, mk_v_eq_one h rfl,
      map_one, map_one]
    simp only [evalUnits, lift_mk, gv, Sum.elim_inr, if_neg hne]

/-- `evalUnits` sends `w₀₂` to `T`. -/
theorem evalUnits_w₀₂ : evalUnits.{u} (mk (gw 0 2 (by decide))) = T 1 := by
  simp [evalUnits, gw]

/-- `evalUnits` sends `w₀₁` to `1`. -/
theorem evalUnits_w₀₁ : evalUnits.{u} (mk (gw 0 1 (by decide))) = 1 := by
  simp [evalUnits, gw]

/-- `evalUnits` sends `w₁₂` to `1`. -/
theorem evalUnits_w₁₂ : evalUnits.{u} (mk (gw 1 2 (by decide))) = 1 := by
  simp [evalUnits, gw]

/-- **The failure of the cocycle condition in degree two.** If
`(w₀₂ᵏ - w₁₂ᵏ w₀₁ᵏ) · a = 0` in `R₂` for `k ≥ 1` and `a` the image of an element `b` of `R₀`
along a vertex, then `b` vanishes at `x₀ = 0`. -/
theorem evalZero_eq_zero_of_mul {k : ℕ} (hk : k ≠ 0) (f : Fin 1 →o Fin 3) (b : Ring.{u} 0)
    (h : (mk (gw 0 2 (by decide)) ^ k - mk (gw 1 2 (by decide)) ^ k *
      mk (gw 0 1 (by decide)) ^ k) * ringMap f b = 0) : evalZero b = 0 := by
  have h' := congrArg evalUnits.{u} h
  rw [map_mul, ← RingHom.comp_apply, evalUnits_comp_ringMap, map_sub, map_mul, map_pow,
    map_pow, map_pow, evalUnits_w₀₂, evalUnits_w₀₁, evalUnits_w₁₂, map_zero] at h'
  simp only [one_pow, mul_one, T_pow, RingHom.comp_apply] at h'
  rcases mul_eq_zero.1 h' with h1 | h1
  · exfalso
    rw [sub_eq_zero, ← T_zero] at h1
    have := (AddMonoidAlgebra.single_left_inj (one_ne_zero (α := ℤ))).mp h1
    omega
  · simpa using (map_eq_zero_iff _ laurentC_injective).1 h1

end

end RatioCosimplicialRing

end CategoryTheory

end
