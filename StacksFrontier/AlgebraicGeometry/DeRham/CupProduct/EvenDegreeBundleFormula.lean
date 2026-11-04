module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.EvenDegreeRing
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.DeRhamCupProductUnit
public import
  StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismComposition
public import StacksFrontier.AlgebraicGeometry.DeRham.HypercohomologyBridge

/-!
# The projective bundle formula on the ring of even-degree de Rham cohomology

Let `P : H^m_{dR} ⟶ H^m_{dR}'` be a family of additive maps compatible with the unit and the cup
product, inducing the ring homomorphism `φ : ⨁ H^{2i}_{dR} ⟶ ⨁ H^{2i}_{dR}'`, and let
`ξ ∈ H^2_{dR}'`. A projective bundle formula in de Rham cohomology is the statement that in every
degree `k` the map

`(a_i)_{i < N} ↦ ∑_i ξ^i ∪ P(a_i)`,  `a_i ∈ H^{k - 2i}_{dR}`

is bijective. If this holds in every even degree and the de Rham cohomology of the source
vanishes in negative degrees, then

`(a_i)_{i < N} ↦ ∑_i ξ^i · φ(a_i)`,  `a_i ∈ ⨁ H^{2j}_{dR}`,

is bijective on the ring of even-degree de Rham cohomology.

## Main results

* `AlgebraicGeometry.SheafOfModules.of_one_pow_evenDeRham`: in the even-degree ring, the power
  `ξ^t` of a class of `H^2_{dR}` is the cup power of `ξ`.
* `AlgebraicGeometry.SheafOfModules.of_mul_apply_evenDeRham`: the components of a product with a
  homogeneous element.
* `AlgebraicGeometry.SheafOfModules.subsingleton_deRhamCohomology_of_neg`: de Rham cohomology
  vanishes in negative degrees.
* `AlgebraicGeometry.SheafOfModules.bijective_evenDeRhamBundleFormula`: if the degreewise bundle
  formula is bijective in every even degree, so is the even-degree one.

## References

* [Stacks Project, Section 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### Transport -/

/-- A transported class vanishes exactly when the class does. -/
theorem reindexDeRhamCohomology_eq_zero_iff {m n : ℤ} (h : m = n) (x : deRhamCohomology B D m) :
    reindexDeRhamCohomology B D h x = 0 ↔ x = 0 := by
  subst h
  rfl

/-- A component of an element of the even-degree ring, read at an equal index. -/
theorem evenDeRhamRing_apply_congr (x : evenDeRhamRing B D) {i j : ℕ} (h : i = j) :
    x j = reindexDeRhamCohomology B D (by rw [h]) (x i) := by
  subst h
  rfl

/-- A homogeneous element of the even-degree ring, read at an equal index. -/
theorem of_evenDeRham_congr {i j : ℕ} (h : i = j) (x : evenDeRhamCohomology B D i) :
    DirectSum.of (evenDeRhamCohomology B D) i x =
      DirectSum.of (evenDeRhamCohomology B D) j (reindexDeRhamCohomology B D (by rw [h]) x) := by
  subst h
  rfl

/-- The product of two homogeneous elements of the even-degree ring. -/
theorem of_mul_of_evenDeRham {i j : ℕ} (x : evenDeRhamCohomology B D i)
    (y : evenDeRhamCohomology B D j) :
    DirectSum.of (evenDeRhamCohomology B D) i x * DirectSum.of (evenDeRhamCohomology B D) j y =
      DirectSum.of (evenDeRhamCohomology B D) (i + j)
        (reindexDeRhamCohomology B D (two_mul_add_cast i j) (deRhamCohomologyCup B D _ _ x y)) :=
  DirectSum.of_mul_of x y

/-! ### Powers and components -/

/-- **The powers of a class of `H^2_{dR}` in the even-degree ring are its cup powers**:
`ξ^t = ξ ∪ ⋯ ∪ ξ ∈ H^{2t}_{dR}`. -/
theorem of_one_pow_evenDeRham (ξ : deRhamCohomology B D ((2 : ℕ) : ℤ)) (t : ℕ) :
    (DirectSum.of (evenDeRhamCohomology B D) 1 ξ) ^ t =
      DirectSum.of (evenDeRhamCohomology B D) t (deRhamCohomologyPow B D 2 ξ t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [pow_succ', ih, of_mul_of_evenDeRham, of_evenDeRham_congr B D (Nat.add_comm 1 t),
      reindexDeRhamCohomology_reindexDeRhamCohomology, deRhamCohomologyPow_succ]

/-- **The components of a product with a homogeneous element**: the component of `x · y` in
degree `i + j`, for `x ∈ H^{2i}_{dR}`, is `x ∪ y_j`. -/
theorem of_mul_apply_evenDeRham {i : ℕ} (x : evenDeRhamCohomology B D i)
    (y : evenDeRhamRing B D) (j : ℕ) :
    (DirectSum.of (evenDeRhamCohomology B D) i x * y) (i + j) =
      reindexDeRhamCohomology B D (two_mul_add_cast i j) (deRhamCohomologyCup B D _ _ x (y j)) := by
  classical
  induction y using DirectSum.induction_on with
  | zero =>
    rw [mul_zero, DirectSum.zero_apply, DirectSum.zero_apply, deRhamCohomologyCup_zero_right,
      reindexDeRhamCohomology_zero]
  | add y y' hy hy' =>
    rw [mul_add, DirectSum.add_apply, hy, hy', DirectSum.add_apply, deRhamCohomologyCup_add_right,
      reindexDeRhamCohomology_add]
  | of k z =>
    rw [of_mul_of_evenDeRham]
    by_cases hk : k = j
    · subst hk
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (by omega), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hk),
        deRhamCohomologyCup_zero_right, reindexDeRhamCohomology_zero]

/-- The components of a product with a homogeneous element of higher degree vanish. -/
theorem of_mul_apply_evenDeRham_of_lt {i : ℕ} (x : evenDeRhamCohomology B D i)
    (y : evenDeRhamRing B D) {n : ℕ} (hn : n < i) :
    (DirectSum.of (evenDeRhamCohomology B D) i x * y) n = 0 := by
  classical
  induction y using DirectSum.induction_on with
  | zero => rw [mul_zero, DirectSum.zero_apply]
  | add y y' hy hy' => rw [mul_add, DirectSum.add_apply, hy, hy', add_zero]
  | of k z =>
    rw [of_mul_of_evenDeRham, DirectSum.of_eq_of_ne _ _ _ (by omega)]

/-! ### Vanishing in negative degrees -/

/-- De Rham cohomology vanishes in negative degrees. -/
theorem subsingleton_deRhamCohomology_of_neg (k : ℤ) (hk : k < 0) :
    Subsingleton (deRhamCohomology B D k) :=
  (hypercohomologyIsoDeRhamCohomology B D k).toLinearEquiv.toEquiv.subsingleton_congr.mp
    (ModuleCat.subsingleton_of_isZero
      (Stacks.Cech.Hypercohomology.isZero_hypercohomology _ _ 0 k hk))

/-! ### The bundle formula -/

variable {X' : RingedSpace.{u, u}} {A' : TopCat.Sheaf CommRingCat.{u} X'.carrier}
  {φ' : A' ⟶ X'.sheaf}
  (B' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X'.carrier) (moduleOfDifferentials.{u, u, u} φ'))
  (D' : DeRhamDifferential B')

/-- The components of the image of an even-degree ring homomorphism. -/
theorem evenDeRhamRingHom_apply
    (P : ∀ m : ℤ, deRhamCohomology B D m →+ deRhamCohomology B' D' m) (hone hmul)
    (x : evenDeRhamRing B D) (j : ℕ) :
    evenDeRhamRingHom B D B' D' P hone hmul x j = P _ (x j) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero]
  | add x x' hx hx' => rw [map_add, DirectSum.add_apply, hx, hx', DirectSum.add_apply, map_add]
  | of k z =>
    rw [evenDeRhamRingHom_of]
    by_cases hk : k = j
    · subst hk
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hk), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hk),
        map_zero]

/-- The degree `2i + (2n - 2i)` of a summand of the degreewise bundle formula is `2n`. -/
theorem two_mul_add_sub_cast (i n : ℕ) :
    ((2 * i : ℕ) : ℤ) + (((2 * n : ℕ) : ℤ) - ((2 * i : ℕ) : ℤ)) = ((2 * n : ℕ) : ℤ) := by
  omega

/-- For `i ≤ n` the degree `2n - 2i` is the even degree `2(n - i)`. -/
theorem two_mul_sub_cast {i n : ℕ} (h : i ≤ n) :
    ((2 * (n - i) : ℕ) : ℤ) = ((2 * n : ℕ) : ℤ) - ((2 * i : ℕ) : ℤ) := by
  omega

/-- **The degreewise projective bundle formula in degree `2n`**:
`(a_i)_{i < N} ↦ ∑_i ξ^i ∪ P(a_i)` with `a_i ∈ H^{2n - 2i}_{dR}`. -/
def degreewiseBundleFormula (P : ∀ m : ℤ, deRhamCohomology B D m →+ deRhamCohomology B' D' m)
    (ξ : deRhamCohomology B' D' ((2 : ℕ) : ℤ)) (N n : ℕ)
    (a : ∀ i : Fin N, deRhamCohomology B D (((2 * n : ℕ) : ℤ) - ((2 * (i : ℕ) : ℕ) : ℤ))) :
    evenDeRhamCohomology B' D' n :=
  ∑ i : Fin N, reindexDeRhamCohomology B' D' (two_mul_add_sub_cast i n)
    (deRhamCohomologyCup B' D' _ _ (deRhamCohomologyPow B' D' 2 ξ i) (P _ (a i)))

section BundleFormula

variable (P : ∀ m : ℤ, deRhamCohomology B D m →+ deRhamCohomology B' D' m)
  (hone : P 0 (deRhamOneClass B D) = deRhamOneClass B' D')
  (hmul : ∀ (m n : ℤ) (x : deRhamCohomology B D m) (y : deRhamCohomology B D n),
    P (m + n) (deRhamCohomologyCup B D m n x y) = deRhamCohomologyCup B' D' m n (P m x) (P n y))
  (ξ : deRhamCohomology B' D' ((2 : ℕ) : ℤ)) (N : ℕ)

/-- The tuple of the degreewise bundle formula in degree `2n` read off a tuple of the even-degree
ring: the component of `a_i` in degree `n - i`, and `0` for `i > n`. -/
def degreewiseTuple (a : Fin N → evenDeRhamRing B D) (n : ℕ) (i : Fin N) :
    deRhamCohomology B D (((2 * n : ℕ) : ℤ) - ((2 * (i : ℕ) : ℕ) : ℤ)) :=
  if h : (i : ℕ) ≤ n then reindexDeRhamCohomology B D (two_mul_sub_cast h) (a i (n - i)) else 0

/-- **The even-degree bundle formula, read in degree `n`, is the degreewise one in degree
`2n`.** -/
theorem evenDeRhamBundleFormula_apply (a : Fin N → evenDeRhamRing B D) (n : ℕ) :
    (∑ i : Fin N, (DirectSum.of (evenDeRhamCohomology B' D') 1 ξ) ^ (i : ℕ) *
        evenDeRhamRingHom B D B' D' P hone hmul (a i)) n =
      degreewiseBundleFormula B D B' D' P ξ N n (degreewiseTuple B D N a n) := by
  rw [DirectSum.sum_apply, degreewiseBundleFormula]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [of_one_pow_evenDeRham, degreewiseTuple]
  split_ifs with h
  · rw [evenDeRhamRing_apply_congr B' D' _ (Nat.add_sub_cancel' h), of_mul_apply_evenDeRham,
      reindexDeRhamCohomology_reindexDeRhamCohomology, evenDeRhamRingHom_apply,
      reindexDeRhamCohomology_apply, deRhamCohomologyCup_reindex_right,
      reindexDeRhamCohomology_reindexDeRhamCohomology]
  · rw [of_mul_apply_evenDeRham_of_lt B' D' _ _ (by omega), map_zero,
      deRhamCohomologyCup_zero_right, reindexDeRhamCohomology_zero]

/-- The tuple of the even-degree ring concentrated in one degree `n` that a tuple of the degreewise
bundle formula in degree `2n` defines: `a_i ∈ H^{2n - 2i}` placed in degree `n - i` for `i ≤ n`. -/
def evenTuple (n : ℕ)
    (b : ∀ i : Fin N, deRhamCohomology B D (((2 * n : ℕ) : ℤ) - ((2 * (i : ℕ) : ℕ) : ℤ)))
    (i : Fin N) : evenDeRhamRing B D :=
  if h : (i : ℕ) ≤ n then
    DirectSum.of (evenDeRhamCohomology B D) (n - i)
      (reindexDeRhamCohomology B D (two_mul_sub_cast h).symm (b i))
  else 0

/-- **The even-degree bundle formula sends `evenTuple n b` to the degreewise formula of `b`**,
placed in degree `n`, as soon as the classes of negative degree vanish. -/
theorem evenDeRhamBundleFormula_evenTuple
    (hneg : ∀ k : ℤ, k < 0 → Subsingleton (deRhamCohomology B D k)) (n : ℕ)
    (b : ∀ i : Fin N, deRhamCohomology B D (((2 * n : ℕ) : ℤ) - ((2 * (i : ℕ) : ℕ) : ℤ))) :
    ∑ i : Fin N, (DirectSum.of (evenDeRhamCohomology B' D') 1 ξ) ^ (i : ℕ) *
        evenDeRhamRingHom B D B' D' P hone hmul (evenTuple B D N n b i) =
      DirectSum.of (evenDeRhamCohomology B' D') n
        (degreewiseBundleFormula B D B' D' P ξ N n b) := by
  rw [degreewiseBundleFormula, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [of_one_pow_evenDeRham, evenTuple]
  split_ifs with h
  · rw [evenDeRhamRingHom_of, of_mul_of_evenDeRham,
      of_evenDeRham_congr B' D' (Nat.add_sub_cancel' h),
      reindexDeRhamCohomology_reindexDeRhamCohomology, reindexDeRhamCohomology_apply,
      deRhamCohomologyCup_reindex_right, reindexDeRhamCohomology_reindexDeRhamCohomology]
  · have : Subsingleton (deRhamCohomology B D (((2 * n : ℕ) : ℤ) - ((2 * (i : ℕ) : ℕ) : ℤ))) :=
      hneg _ (by omega)
    rw [map_zero, mul_zero, Subsingleton.elim (b i) 0, map_zero, deRhamCohomologyCup_zero_right,
      reindexDeRhamCohomology_zero, map_zero]

/-- **The projective bundle formula on the ring of even-degree de Rham cohomology.** If in every
even degree `2n` the map `(a_i)_{i < N} ↦ ∑_i ξ^i ∪ P(a_i)`, `a_i ∈ H^{2n - 2i}_{dR}`, is
bijective, then so is `(a_i)_{i < N} ↦ ∑_i ξ^i · φ(a_i)` on `N` copies of `⨁ H^{2j}_{dR}`; here
`φ` is the ring homomorphism induced by `P` and the de Rham cohomology of the source vanishes in
negative degrees. -/
theorem bijective_evenDeRhamBundleFormula
    (hneg : ∀ k : ℤ, k < 0 → Subsingleton (deRhamCohomology B D k))
    (hdeg : ∀ n : ℕ, Function.Bijective (degreewiseBundleFormula B D B' D' P ξ N n)) :
    Function.Bijective fun a : Fin N → evenDeRhamRing B D =>
      ∑ i : Fin N, (DirectSum.of (evenDeRhamCohomology B' D') 1 ξ) ^ (i : ℕ) *
        evenDeRhamRingHom B D B' D' P hone hmul (a i) := by
  classical
  let F : (Fin N → evenDeRhamRing B D) →+ evenDeRhamRing B' D' :=
    ∑ i : Fin N, (AddMonoidHom.mulLeft
      ((DirectSum.of (evenDeRhamCohomology B' D') 1 ξ) ^ (i : ℕ))).comp
        ((evenDeRhamRingHom B D B' D' P hone hmul).toAddMonoidHom.comp (Pi.evalAddMonoidHom _ i))
  have hF : ∀ a, F a = ∑ i : Fin N, (DirectSum.of (evenDeRhamCohomology B' D') 1 ξ) ^ (i : ℕ) *
      evenDeRhamRingHom B D B' D' P hone hmul (a i) := fun a ↦ by
    simp [F]
  refine ⟨fun a a' e ↦ ?_, fun z ↦ ?_⟩
  · have e' : F (a - a') = 0 := by rwa [map_sub, sub_eq_zero, hF, hF]
    rw [← sub_eq_zero]
    funext i
    refine DFinsupp.ext fun j ↦ ?_
    have hn : degreewiseTuple B D N (a - a') (i + j) = 0 := by
      refine (hdeg (i + j)).1 ?_
      rw [← evenDeRhamBundleFormula_apply B D B' D' P hone hmul ξ N, ← hF, e',
        DirectSum.zero_apply, degreewiseBundleFormula]
      exact (Finset.sum_eq_zero fun i _ ↦ by
        rw [Pi.zero_apply, map_zero, deRhamCohomologyCup_zero_right,
          reindexDeRhamCohomology_zero]).symm
    have hi := congrFun hn i
    rw [degreewiseTuple, dite_eq_left (Nat.le_add_right _ _), Pi.zero_apply] at hi
    rw [Pi.zero_apply, DirectSum.zero_apply,
      evenDeRhamRing_apply_congr B D _ (Nat.add_sub_cancel_left (n := (i : ℕ)) (m := j)),
      reindexDeRhamCohomology_eq_zero_iff]
    rwa [reindexDeRhamCohomology_eq_zero_iff] at hi
  · have hsurj : ∀ z, z ∈ F.range := by
      intro z
      induction z using DirectSum.induction_on with
      | zero => exact F.range.zero_mem
      | add z z' hz hz' => exact F.range.add_mem hz hz'
      | of n y =>
        obtain ⟨b, hb⟩ := (hdeg n).2 y
        refine ⟨evenTuple B D N n b, ?_⟩
        rw [hF, evenDeRhamBundleFormula_evenTuple B D B' D' P hone hmul ξ N hneg, hb]
    obtain ⟨a, ha⟩ := hsurj z
    exact ⟨a, (hF a).symm.trans ha⟩

end BundleFormula

end AlgebraicGeometry.SheafOfModules
