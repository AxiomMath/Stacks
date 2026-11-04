module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorPushforwardCounterexample

/-!
# Two punctured planes meeting at a point: a second scheme-level counterexample to Stacks 0GRN

**Stacks 0GRN** asserts that for `a : 𝒴 → 𝒳` and `b : 𝒵 → 𝒳` representable by schemes,
quasi-compact, quasi-separated and flat,
`a_{QCoh,*}𝒪_𝒴 ⊗_{𝒪_𝒳} b_{QCoh,*}𝒪_𝒵 = f_{QCoh,*}𝒪_{𝒴 ×_𝒳 𝒵}`. Here is a counterexample in
which the right hand side is zero while the left hand side is not. Let `k` be a field and

`A = k[x, y, z, w] / (xz, xw, yz, yw)`,

so that `X = Spec A` is the union of the two planes `P = {x = y = 0}` (coordinates `z, w`) and
`P' = {z = w = 0}` (coordinates `x, y`), meeting at the origin only. Let

`V = D(z) ∪ D(w) = P ∖ {0}` and `W = D(x) ∪ D(y) = P' ∖ {0}`,

two opens of `X`, quasi-compact, and disjoint because `xz = xw = yz = yw = 0`. So
`V ×_X W = ∅`, and the direct image of its structure sheaf is zero. But
`Γ(V, 𝒪) = k[z, w]` and `Γ(W, 𝒪) = k[x, y]` (a punctured plane has the functions of the plane),
and `Γ(V, 𝒪) ⊗_A Γ(W, 𝒪) = A / (x, y, z, w) = k ≠ 0`. The failure is the one of the cone example
of `StacksFrontier/AlgebraicGeometry/Stacks/TensorPushforwardCounterexample.lean`:
`H¹(V, 𝒪) ≠ 0`, and `Γ(V, 𝒪)` is not flat over `A`.

This file proves the scheme-level facts used by the stack-level statement in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/TensorPushforwardStackCounterexample.lean`:
the two opens are disjoint, and there are ring maps `Γ(V, 𝒪) → k` and `Γ(W, 𝒪) → k`, the
evaluations at the origin of the two planes, which agree on `Γ(X, 𝒪)`. The second fact gives a
nonzero `A`-bilinear map `Γ(V, 𝒪) × Γ(W, 𝒪) → k`.

## Main definitions

* `AlgebraicGeometry.TensorPushforwardPlanes.planesRing`: the ring `A`.
* `AlgebraicGeometry.TensorPushforwardPlanes.openV`, `openW`: the opens `V`, `W` of `Spec A`.
* `AlgebraicGeometry.TensorPushforwardPlanes.evalV`, `evalW`: the evaluations at the origin
  `Γ(V, 𝒪) → k` and `Γ(W, 𝒪) → k`.

## Main results

* `AlgebraicGeometry.TensorPushforwardPlanes.openV_inf_openW`: `V ∩ W = ∅`.
* `AlgebraicGeometry.TensorPushforwardPlanes.evalV_res_eq_evalW_res`: the two evaluations agree
  on the restrictions of the global sections of `Spec A`.
* `AlgebraicGeometry.TensorPushforwardPlanes.nontrivial_tensorProduct`: `Γ(V, 𝒪) ⊗_A Γ(W, 𝒪)` is
  nonzero.

## References

* [Stacks Project, Tag 0GRN](https://stacks.math.columbia.edu/tag/0GRN)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial TopologicalSpace Opposite TensorProduct

universe u

namespace AlgebraicGeometry.TensorPushforwardPlanes

open TensorPushforwardCounterexample

variable (k : Type u) [Field k]

/-- The ideal `(xz, xw, yz, yw)` of `k[x, y, z, w]`, the variables indexed `0, 1, 2, 3`. -/
def planesIdeal : Ideal (MvPolynomial (Fin 4) k) :=
  Ideal.span {X 0 * X 2, X 0 * X 3, X 1 * X 2, X 1 * X 3}

/-- The ring `A = k[x, y, z, w] / (xz, xw, yz, yw)` of the union of the planes `x = y = 0` and
`z = w = 0` of `𝔸⁴`. -/
abbrev planesRing : Type u := MvPolynomial (Fin 4) k ⧸ planesIdeal k

/-- The coordinate functions of `A`. -/
abbrev coord (i : Fin 4) : planesRing k := Ideal.Quotient.mk _ (X i)

/-- The product of a coordinate among `x, y` and one among `z, w` vanishes in `A`. -/
lemma coord_mul_coord {i j : Fin 4} (hi : i = 0 ∨ i = 1) (hj : j = 2 ∨ j = 3) :
    coord k i * coord k j = 0 := by
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.subset_span ?_
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp

/-- A ring map out of `A`, given by values of the four coordinates whose mixed products vanish. -/
def liftPlanes {R : Type u} [CommRing R] [Algebra k R] (v : Fin 4 → R)
    (hv : v 0 * v 2 = 0 ∧ v 0 * v 3 = 0 ∧ v 1 * v 2 = 0 ∧ v 1 * v 3 = 0) :
    planesRing k →+* R :=
  Ideal.Quotient.lift _ (aeval v).toRingHom (by
    have hle : planesIdeal k ≤ RingHom.ker (aeval v).toRingHom := by
      refine Ideal.span_le.2 ?_
      rintro g (rfl | rfl | rfl | rfl) <;> simp [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
    exact fun a ha => hle ha)

/-- The ring map `liftPlanes k v hv` sends the `i`-th coordinate of `A` to `v i`. -/
@[simp] lemma liftPlanes_coord {R : Type u} [CommRing R] [Algebra k R] (v : Fin 4 → R)
    (hv : v 0 * v 2 = 0 ∧ v 0 * v 3 = 0 ∧ v 1 * v 2 = 0 ∧ v 1 * v 3 = 0) (i : Fin 4) :
    liftPlanes k v hv (coord k i) = v i := by
  simp [liftPlanes]

/-- Two ring maps out of `A` agreeing on the coordinates are equal. -/
lemma ringHom_ext_planes {R : Type u} [CommRing R] {φ ψ : planesRing k →+* R}
    (h : ∀ i, φ (coord k i) = ψ (coord k i)) (hk : ∀ c : k, φ (Ideal.Quotient.mk _ (C c)) =
      ψ (Ideal.Quotient.mk _ (C c))) : φ = ψ :=
  Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c => hk c) (fun i => h i))

/-! ### The two opens -/

/-- The open `V = D(z) ∪ D(w)` of `Spec A`, the plane `x = y = 0` without the origin. -/
def openV : Opens (PrimeSpectrum (planesRing k)) :=
  PrimeSpectrum.basicOpen (coord k 2) ⊔ PrimeSpectrum.basicOpen (coord k 3)

/-- The open `W = D(x) ∪ D(y)` of `Spec A`, the plane `z = w = 0` without the origin. -/
def openW : Opens (PrimeSpectrum (planesRing k)) :=
  PrimeSpectrum.basicOpen (coord k 0) ⊔ PrimeSpectrum.basicOpen (coord k 1)

/-- For a coordinate `i` among `x, y` and `j` among `z, w`, `D(j) ∩ D(i) = ∅` in `Spec A`. -/
lemma basicOpen_inf_basicOpen {i j : Fin 4} (hi : i = 0 ∨ i = 1) (hj : j = 2 ∨ j = 3) :
    PrimeSpectrum.basicOpen (coord k j) ⊓ PrimeSpectrum.basicOpen (coord k i) = ⊥ := by
  rw [← PrimeSpectrum.basicOpen_mul, mul_comm, coord_mul_coord k hi hj,
    PrimeSpectrum.basicOpen_zero]

/-- **`V` and `W` are disjoint**: `D(z) ∩ D(x) = D(zx) = ∅`, and likewise for the other three
pairs. -/
lemma openV_inf_openW : openV k ⊓ openW k = ⊥ := by
  simp only [openV, openW, inf_sup_left, inf_sup_right,
    basicOpen_inf_basicOpen k (Or.inl rfl) (Or.inl rfl),
    basicOpen_inf_basicOpen k (Or.inl rfl) (Or.inr rfl),
    basicOpen_inf_basicOpen k (Or.inr rfl) (Or.inl rfl),
    basicOpen_inf_basicOpen k (Or.inr rfl) (Or.inr rfl), sup_idem]

/-! ### The punctured plane -/

/-- The open `D(s) ∪ D(t)` of the plane `Spec k[s, t]`, the complement of the origin. -/
def puncturedPlane : Opens (PrimeSpectrum (MvPolynomial (Fin 2) k)) :=
  PrimeSpectrum.basicOpen (X 0) ⊔ PrimeSpectrum.basicOpen (X 1)

/-- In `k[s, t]`, the variable `s` does not divide `t`. -/
lemma not_X_zero_dvd_X_one : ¬ (X 0 : MvPolynomial (Fin 2) k) ∣ X 1 := by
  rintro ⟨c, hc⟩
  have := congrArg (eval ![0, 1]) hc
  simp at this

/-- Every function on the punctured plane is a polynomial. -/
lemma algebraMap_puncturedPlane_bijective :
    Function.Bijective (algebraMap (MvPolynomial (Fin 2) k)
      ((Spec.structureSheaf (MvPolynomial (Fin 2) k)).obj.obj (op (puncturedPlane k)))) := by
  let := UniqueFactorizationMonoid.normalizationMonoid (α := MvPolynomial (Fin 2) k)
  refine Stacks.PicardUFD.algebraMap_bijective_two_basicOpens _ (X 0) (X 1)
    (X_ne_zero (R := k) (σ := Fin 2) 0) (X_ne_zero (R := k) (σ := Fin 2) 1) ?_
  intro p hp hp'
  have hp0 := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp
  have hp1 := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp'
  have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor p hp
  have hassoc : Associated p (X 0) :=
    hprime.associated_of_dvd (X_prime (σ := Fin 2) (R := k) (i := 0)) hp0
  exact not_X_zero_dvd_X_one k (hassoc.symm.dvd.trans hp1)

/-- The identification `k[s, t] ≅ Γ(𝔸² ∖ {0}, 𝒪)`. -/
def puncturedPlaneEquiv : MvPolynomial (Fin 2) k ≃+*
    (Spec.structureSheaf (MvPolynomial (Fin 2) k)).obj.obj (op (puncturedPlane k)) :=
  RingEquiv.ofBijective (algebraMap (MvPolynomial (Fin 2) k) _)
    (algebraMap_puncturedPlane_bijective k)

/-! ### The two plane projections and the evaluations at the origin -/

/-- The closed immersion of the plane `x = y = 0` into `X`, on rings: `A → k[s, t]`,
`x, y ↦ 0`, `z ↦ s`, `w ↦ t`. -/
def toPlaneV : planesRing k →+* MvPolynomial (Fin 2) k :=
  liftPlanes k ![0, 0, X 0, X 1] (by simp)

/-- The closed immersion of the plane `z = w = 0` into `X`, on rings: `A → k[s, t]`,
`x ↦ s`, `y ↦ t`, `z, w ↦ 0`. -/
def toPlaneW : planesRing k →+* MvPolynomial (Fin 2) k :=
  liftPlanes k ![X 0, X 1, 0, 0] (by simp)

/-- The evaluation of `A` at the origin. -/
def originEval : planesRing k →+* k :=
  liftPlanes k ![0, 0, 0, 0] (by simp)

/-- Evaluating `toPlaneV k` at the origin of `k[s, t]` is the evaluation of `A` at the origin. -/
lemma eval_zero_comp_toPlaneV : (eval ![0, 0]).comp (toPlaneV k) = originEval k := by
  refine ringHom_ext_planes k (fun i => ?_) (fun c => ?_)
  · fin_cases i <;> simp [toPlaneV, originEval]
  · simp [toPlaneV, originEval, liftPlanes]

/-- Evaluating `toPlaneW k` at the origin of `k[s, t]` is the evaluation of `A` at the origin. -/
lemma eval_zero_comp_toPlaneW : (eval ![0, 0]).comp (toPlaneW k) = originEval k := by
  refine ringHom_ext_planes k (fun i => ?_) (fun c => ?_)
  · fin_cases i <;> simp [toPlaneW, originEval]
  · simp [toPlaneW, originEval, liftPlanes]

/-- If a ring map `φ : A → k[s, t]` sends the coordinate `i` to the variable `X j`, then `D(X j)`
lies in the preimage of `D(coord k i)` under `Spec φ`. -/
lemma basicOpen_le_preimage (φ : planesRing k →+* MvPolynomial (Fin 2) k) (i : Fin 4)
    (j : Fin 2) (h : φ (coord k i) = X j) :
    PrimeSpectrum.basicOpen (X j : MvPolynomial (Fin 2) k) ≤
      Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ PrimeSpectrum.basicOpen (coord k i) := by
  rw [SpecMap_preimage_basicOpen]
  simp only [CommRingCat.hom_ofHom, h, le_refl]

/-- The punctured plane lies in the preimage of `V` under `Spec (toPlaneV k)`. -/
lemma puncturedPlane_le_preimage_openV :
    puncturedPlane k ≤ Spec.map (CommRingCat.ofHom (toPlaneV k)) ⁻¹ᵁ openV k :=
  sup_le ((basicOpen_le_preimage k _ 2 0 (by simp [toPlaneV])).trans
      (Scheme.Hom.preimage_mono _ le_sup_left))
    ((basicOpen_le_preimage k _ 3 1 (by simp [toPlaneV])).trans
      (Scheme.Hom.preimage_mono _ le_sup_right))

/-- The punctured plane lies in the preimage of `W` under `Spec (toPlaneW k)`. -/
lemma puncturedPlane_le_preimage_openW :
    puncturedPlane k ≤ Spec.map (CommRingCat.ofHom (toPlaneW k)) ⁻¹ᵁ openW k :=
  sup_le ((basicOpen_le_preimage k _ 0 0 (by simp [toPlaneW])).trans
      (Scheme.Hom.preimage_mono _ le_sup_left))
    ((basicOpen_le_preimage k _ 1 1 (by simp [toPlaneW])).trans
      (Scheme.Hom.preimage_mono _ le_sup_right))

/-- The evaluation at the origin of the plane `x = y = 0`, as a ring map `Γ(V, 𝒪) → k`: pull
back to the punctured plane, read the polynomial, evaluate at `0`. -/
def evalV : (Spec.structureSheaf (planesRing k)).obj.obj (op (openV k)) →+* k :=
  (eval ![0, 0]).comp ((puncturedPlaneEquiv k).symm.toRingHom.comp
    (sectionsMap (toPlaneV k) (openV k) (puncturedPlane k) (puncturedPlane_le_preimage_openV k)))

/-- The evaluation at the origin of the plane `z = w = 0`, as a ring map `Γ(W, 𝒪) → k`. -/
def evalW : (Spec.structureSheaf (planesRing k)).obj.obj (op (openW k)) →+* k :=
  (eval ![0, 0]).comp ((puncturedPlaneEquiv k).symm.toRingHom.comp
    (sectionsMap (toPlaneW k) (openW k) (puncturedPlane k) (puncturedPlane_le_preimage_openW k)))

/-- Pulling back along `φ : A → k[s, t]` to the punctured plane, reading the polynomial and
evaluating at `0` is the evaluation of `A` at the origin on the image of `A`, if `φ` is. -/
private lemma eval_symm_sectionsMap_algebraMap (φ : planesRing k →+* MvPolynomial (Fin 2) k)
    (U : Opens (PrimeSpectrum (planesRing k)))
    (hU : puncturedPlane k ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U)
    (h : (eval ![0, 0]).comp φ = originEval k) (a : planesRing k) :
    eval ![0, 0] ((puncturedPlaneEquiv k).symm
      (sectionsMap φ U (puncturedPlane k) hU (algebraMap _ _ a))) = originEval k a := by
  rw [sectionsMap_algebraMap,
    show algebraMap _ _ (φ a) = puncturedPlaneEquiv k (φ a) from rfl,
    RingEquiv.symm_apply_apply, ← h]
  rfl

/-- On the image of `A` in `Γ(V, 𝒪)`, `evalV k` is the evaluation of `A` at the origin. -/
lemma evalV_algebraMap (a : planesRing k) :
    evalV k (algebraMap (planesRing k) _ a) = originEval k a :=
  eval_symm_sectionsMap_algebraMap k _ _ _ (eval_zero_comp_toPlaneV k) a

/-- On the image of `A` in `Γ(W, 𝒪)`, `evalW k` is the evaluation of `A` at the origin. -/
lemma evalW_algebraMap (a : planesRing k) :
    evalW k (algebraMap (planesRing k) _ a) = originEval k a :=
  eval_symm_sectionsMap_algebraMap k _ _ _ (eval_zero_comp_toPlaneW k) a

/-- Restriction of sections of `Spec A` from `U` to `V ≤ U` commutes with the maps from `A`. -/
lemma res_algebraMap {U V : Opens (PrimeSpectrum (planesRing k))} (h : V ≤ U)
    (a : planesRing k) :
    (Spec.structureSheaf (planesRing k)).obj.map (homOfLE h).op (algebraMap _ _ a) =
      algebraMap (planesRing k) ((Spec.structureSheaf (planesRing k)).obj.obj (op V)) a := by
  rfl

/-- **The two evaluations at the origin agree on the global sections of `X`**: both restrict a
global function to the respective punctured plane and evaluate it at the origin, which is the
same point of `X`. -/
lemma evalV_res_eq_evalW_res (r : Γ(Spec (.of (planesRing k)), ⊤)) :
    evalV k ((Spec (.of (planesRing k))).presheaf.map (homOfLE le_top : openV k ⟶ ⊤).op r) =
      evalW k ((Spec (.of (planesRing k))).presheaf.map (homOfLE le_top : openW k ⟶ ⊤).op r) := by
  obtain ⟨a, rfl⟩ := (StructureSheaf.algebraMap_obj_top_bijective (R := planesRing k)).2 r
  exact ((congrArg (evalV k) (res_algebraMap k le_top a)).trans (evalV_algebraMap k a)).trans
    ((congrArg (evalW k) (res_algebraMap k le_top a)).trans (evalW_algebraMap k a)).symm

/-- The `A`-algebra structure on `k` of the origin. -/
@[instance_reducible]
def originAlgebra : Algebra (planesRing k) k := (originEval k).toAlgebra

/-- **`Γ(V, 𝒪) ⊗_A Γ(W, 𝒪)` is nonzero**, although `V ∩ W = ∅`: the two evaluations at the origin
give an `A`-algebra map from it onto `k`. -/
theorem nontrivial_tensorProduct :
    Nontrivial ((Spec.structureSheaf (planesRing k)).obj.obj (op (openV k)) ⊗[planesRing k]
      (Spec.structureSheaf (planesRing k)).obj.obj (op (openW k))) := by
  let := originAlgebra k
  let eV : (Spec.structureSheaf (planesRing k)).obj.obj (op (openV k)) →ₐ[planesRing k] k :=
    { toRingHom := evalV k, commutes' := evalV_algebraMap k }
  let eW : (Spec.structureSheaf (planesRing k)).obj.obj (op (openW k)) →ₐ[planesRing k] k :=
    { toRingHom := evalW k, commutes' := evalW_algebraMap k }
  let L := Algebra.TensorProduct.lift eV eW (fun _ _ => mul_comm _ _)
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have := congrArg L h
  rw [map_one, map_zero] at this
  exact one_ne_zero this

end AlgebraicGeometry.TensorPushforwardPlanes

end
