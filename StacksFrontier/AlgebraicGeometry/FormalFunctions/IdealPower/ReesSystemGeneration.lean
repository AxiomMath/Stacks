module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksFrontier.RingTheory.Filtration.IdealPowerSystemNoetherian

/-!
# Generation in high degrees of an ideal-power system over its Rees algebra

Let `A` be a commutative ring, `I ⊆ A` an ideal and `S` a `Stacks.RingTheory.ReesSystem` for
the identity of `A`: an inverse system of `A`-modules `M 0 ← M 1 ← ⋯` over a module `M₀`, with
multiplication maps `Iᵏ ⊗ M n → M (k + n)` obeying the graded-module laws over the Rees algebra
`⨁ₙ Iⁿ`. The motivating example is `M n = Hᵖ(X, Iⁿℱ)` over `M₀ = Hᵖ(X, ℱ)`.

`Stacks.RingTheory.IdealPowerSystem.exists_uniform_bound` already extracts from Noetherianity of
such a system the two clauses of [Stacks, Tag 02OA] that mention only the projections to `M₀` —
part (2) of the source at `n = 0` and part (3). The remaining clauses all speak about the
transition maps *between* the members of the system, and the source's proof of them uses one
compatibility that `IdealPowerSystem` does not assume: the diagrams

```
Iᵏ ⊗ M m  →  M (k + m)
   ↓             ↓
Iᵏ ⊗ M m' →  M (k + m')
```

commute for `m' ≤ m`. This file adds that compatibility as a hypothesis
(`ReesSystem.IsFiltrationCompatible`) and derives from it the generation statement that drives
the rest of the lemma: homogeneous generators of degree at most `c` make the products
`Iʳ · M c` span `M (r + c)`.

## Main definitions

* `Stacks.RingTheory.ReesSystem.smulOf` is the multiplication map with its coefficient read in
  `Iᵏ` itself rather than in the extension `(I.map (RingHom.id A))ᵏ` that the underlying
  `IdealPowerSystem` is taken for.
* `Stacks.RingTheory.ReesSystem.IsFiltrationCompatible` is the compatibility of the
  multiplication maps with the transition maps, together with the identity
  `tr (a · y) = a • y` back to the original degree.
* `Stacks.RingTheory.ReesSystem.smulSpan` is the submodule `Iʳ · M c ⊆ M (r + c)` spanned by the
  products.

## Main results

* `Stacks.RingTheory.ReesSystem.top_le_smulSpan`: the products `Iʳ · M c` span `M (r + c)` when
  homogeneous elements of degrees at most `c` generate the system.
* `Stacks.RingTheory.ReesSystem.mulTensor_surjective`: **part (1) of [Stacks, Tag 02OA]** in the
  abstract, the surjectivity of `Iʳ ⊗_A M c → M (r + c)`.
* `Stacks.RingTheory.ReesSystem.range_tr_le_pow_smul`: **part (2) of [Stacks, Tag 02OA]** in the
  abstract, for every degree `n` and not only for `n = 0`.
* `Stacks.RingTheory.ReesSystem.exists_uniform_bound_mul`: the three clauses above with one
  constant, obtained from the Noetherianity of the system.

## Implementation notes

The source indexes part (2) by the source degree `n + m`; here the shift is written first, so
the transition map is `S.tr : M (m + n) → M n`. The two readings differ only by commutativity of
addition, but writing the shift first makes the degree of a product `Iᵏ · M n` literally
`k + n`, which is the index the multiplication map of `IdealPowerSystem` produces, and so no
transport along an index equality is needed in the statements.

Where a transport cannot be avoided — `genSubmodule` is indexed by the truncated difference
`n - d i` — it is carried by a transition map between equal degrees rather than by `eqToHom` or
a cast: `tr_congr_sigma` turns an equality in `Σ n, M n` into an equality of transported
elements, and `tr_eq_self` says the transport is the identity when the degrees agree. This is
the same device `ReesSystem` itself uses for its graded-module laws.

The coefficients of the multiplication maps are read in `Iᵏ` throughout. The ideal of the
underlying `IdealPowerSystem` is the extension `I.map (RingHom.id A)`, which is `I` by
`Ideal.map_id`; `smulOf` is the one place where that identification is made, and the
graded-module laws of `ReesSystem` are already stated with coefficients in `Iᵏ`.

Generation is not reduced to an induction over the elements of `Iʳ · Iˡ`. Instead the set of
coefficients whose multiple lies in the span is exhibited as the image of a submodule of
`↥(Iᵏ)` in `A`, and `Submodule.mul_le` reduces the containment to the products — which is
exactly where associativity of the multiplication maps is used.

## References

* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public section

universe u v w

namespace Stacks.RingTheory

variable {A : Type u} [CommRing A] {I : Ideal A}
  {M : ℕ → Type v} [∀ n, AddCommGroup (M n)] [∀ n, Module A (M n)]
  {M₀ : Type w} [AddCommGroup M₀] [Module A M₀]

namespace IdealPowerSystem

variable {J : Ideal A} (S : IdealPowerSystem J M M₀)

/-- Two transition maps into the same degree agree on elements that are identified in
`Σ n, M n`. This is the device that replaces transport along an equality of degrees. -/
theorem tr_congr_sigma {n j j' : ℕ} (h : n ≤ j) (h' : n ≤ j') {u : M j} {u' : M j'}
    (e : (⟨j, u⟩ : Σ k, M k) = ⟨j', u'⟩) :
    S.tr h u = S.tr h' u' := by
  have hj : j = j' := congrArg Sigma.fst e
  subst hj
  have hu : u = u' := by simpa using e
  subst hu
  rfl

/-- Transition maps out of equal degrees have the same range. -/
theorem range_tr_congr {n j j' : ℕ} (h : n ≤ j) (h' : n ≤ j') (e : j = j') :
    LinearMap.range (S.tr h) = LinearMap.range (S.tr h') := by
  subst e; rfl

end IdealPowerSystem

namespace ReesSystem

/-- Mapping an ideal along the identity ring homomorphism does not change its powers. -/
theorem pow_map_ringHom_id (I : Ideal A) (k : ℕ) :
    (I.map (RingHom.id A)) ^ k = I ^ k := by
  rw [Ideal.map_id]

variable (S : ReesSystem (RingHom.id A) I M M₀)

/-- A coefficient of `Iᵏ`, read in the ideal `I.map (RingHom.id A)` that the underlying
`IdealPowerSystem` is taken for. -/
def coeffOfPow (k : ℕ) (a : ↥(I ^ k)) : ↥((I.map (RingHom.id A)) ^ k) :=
  ⟨(a : A), (pow_map_ringHom_id I k).ge a.2⟩

/-- **Multiplication by an element of `Iᵏ`** as an `A`-linear map `M n → M (k + n)`: the
multiplication map of the system, with its coefficient read in `Iᵏ` itself. -/
def smulOf (k n : ℕ) : ↥(I ^ k) →ₗ[A] M n →ₗ[A] M (k + n) where
  toFun a := S.mul k n (coeffOfPow (I := I) k a)
  map_add' a b := by
    rw [show coeffOfPow (I := I) k (a + b)
      = coeffOfPow (I := I) k a + coeffOfPow (I := I) k b from Subtype.ext rfl, map_add]
  map_smul' r a := by
    rw [show coeffOfPow (I := I) k (r • a)
      = r • coeffOfPow (I := I) k a from Subtype.ext rfl, map_smul]
    rfl

/-- `smulOf k n a` is the multiplication map of the system with coefficient `a`. -/
theorem smulOf_apply {k n : ℕ} (a : ↥(I ^ k)) (y : M n) :
    S.smulOf k n a y = S.mul k n (coeffOfPow (I := I) k a) y := rfl

/-- The multiplication map of the underlying `IdealPowerSystem`, read as `smulOf`. -/
theorem mul_eq_smulOf {k n : ℕ} (a : ↥((I.map (RingHom.id A)) ^ k)) (y : M n)
    (ha : (a : A) ∈ I ^ k) :
    S.mul k n a y = S.smulOf k n ⟨(a : A), ha⟩ y :=
  congrArg (fun b : ↥((I.map (RingHom.id A)) ^ k) ↦ S.mul k n b y) (Subtype.ext rfl)

/-- Multiplication maps with the same coefficient and equal degrees agree in `Σ n, M n`. -/
theorem smulOf_congr_sigma {k k' n : ℕ} (e : k = k') (a : ↥(I ^ k)) (a' : ↥(I ^ k'))
    (ha : (a : A) = (a' : A)) (y : M n) :
    (⟨k + n, S.smulOf k n a y⟩ : Σ j, M j) = ⟨k' + n, S.smulOf k' n a' y⟩ := by
  subst e
  exact congrArg (fun b : ↥(I ^ k) ↦ (⟨k + n, S.smulOf k n b y⟩ : Σ j, M j)) (Subtype.ext ha)

/-- A transition map between equal degrees is the identity. -/
theorem tr_eq_self {n : ℕ} (h : n ≤ n) (y : M n) : S.tr h y = y := by
  simpa using S.tr_of_eq h rfl y

/-- **Associativity of the multiplication maps**, in the form used below: a coefficient that is
a product splits the multiplication in two. Both sides are read at a common degree `j` through
a transition map, so no transport along `k + l + n = k + (l + n)` appears. -/
theorem tr_smulOf_mul {k l n j : ℕ} (a : ↥(I ^ k)) (b : ↥(I ^ l)) (c : ↥(I ^ (k + l)))
    (hc : (c : A) = (a : A) * (b : A)) (y : M n)
    (hj : j ≤ k + l + n) (hj' : j ≤ k + (l + n)) :
    S.tr hj (S.smulOf (k + l) n c y) =
      S.tr hj' (S.smulOf k (l + n) a (S.smulOf l n b y)) :=
  S.toIdealPowerSystem.tr_congr_sigma hj hj' (S.mul_mul k l n a b c y hc)

/-- The two compatibilities of the multiplication maps with the transition maps that the
remaining clauses of [Stacks, Tag 02OA] use beyond the laws of `ReesSystem`. Both hold for the
system `n ↦ Hᵖ(X, Iⁿℱ)` because every multiplication map there is `Hᵖ` of multiplication by one
function on the base, read between two members of the filtration. -/
structure IsFiltrationCompatible
    (S : ReesSystem (RingHom.id A) I M M₀) : Prop where
  /-- Lowering the degree after multiplying is multiplying after lowering the degree. -/
  tr_smulOf : ∀ (k m m' : ℕ) (h : m' ≤ m) (a : ↥(I ^ k)) (y : M m),
    S.tr (Nat.add_le_add_left h k) (S.smulOf k m a y) = S.smulOf k m' a (S.tr h y)
  /-- Returning to the original degree after multiplying is the module action. -/
  tr_smulOf_self : ∀ (k n : ℕ) (a : ↥(I ^ k)) (y : M n),
    S.tr (Nat.le_add_left n k) (S.smulOf k n a y) = (a : A) • y

/-! ### Generation in high degrees -/

/-- The submodule `Iʳ · M c` of `M (r + c)` spanned by the products. -/
def smulSpan (r c : ℕ) : Submodule A (M (r + c)) :=
  Submodule.span A (Set.range fun p : ↥(I ^ r) × M c ↦ S.smulOf r c p.1 p.2)

/-- A product `a • y` with `a ∈ Iʳ` and `y ∈ M c` lies in `Iʳ · M c`. -/
theorem smulOf_mem_smulSpan {r c : ℕ} (a : ↥(I ^ r)) (y : M c) :
    S.smulOf r c a y ∈ S.smulSpan r c :=
  Submodule.subset_span (Set.mem_range_self (a, y))

/-- **One summand of a graded subobject generated in degrees at most `c` lies in `Iʳ · M c`.**

This is the whole of the source's argument for its clause (1): the generating element `z` has
degree `e ≤ c`, so a coefficient of `I ^ q` with `q + e = r + c` splits as a product of one
element of `Iʳ` and one of `I ^ (q - r)`, and multiplying by the latter already carries `z` into
degree `c`. -/
theorem tr_mul_mem_smulSpan (hcomp : IsFiltrationCompatible S) {e q r c : ℕ}
    (hrq : r ≤ q) (hq : q + e = r + c) (a : ↥((I.map (RingHom.id A)) ^ q)) (z : M e)
    (h : r + c ≤ q + e) :
    S.tr h (S.mul q e a z) ∈ S.smulSpan r c := by
  obtain ⟨s, rfl⟩ : ∃ s, q = r + s := ⟨q - r, by omega⟩
  obtain rfl : c = s + e := by omega
  -- the coefficients whose multiple lands in the span, as a submodule of `↥((I.map id) ^ q)`
  have hmul : I ^ r * I ^ s ≤ Submodule.map ((I.map (RingHom.id A)) ^ (r + s)).subtype
      (Submodule.comap ((S.tr h).comp ((S.mul (r + s) e).flip z)) (S.smulSpan r (s + e))) := by
    refine Submodule.mul_le.2 fun b hb b' hb' ↦ ?_
    have hbbI : b * b' ∈ I ^ (r + s) := by
      rw [pow_add]; exact Submodule.mul_mem_mul hb hb'
    have hbbJ : b * b' ∈ (I.map (RingHom.id A)) ^ (r + s) := by
      rw [pow_map_ringHom_id]; exact hbbI
    refine ⟨⟨b * b', hbbJ⟩, ?_, rfl⟩
    -- the product coefficient splits, and the second factor already reaches degree `s + e`
    have h1 : S.tr h (S.mul (r + s) e ⟨b * b', hbbJ⟩ z) =
        S.tr h (S.smulOf (r + s) e ⟨b * b', hbbI⟩ z) :=
      congrArg (S.tr h) (S.mul_eq_smulOf _ _ hbbI)
    have h2 : S.tr h (S.smulOf (r + s) e ⟨b * b', hbbI⟩ z) =
        S.tr (le_refl (r + (s + e)))
          (S.smulOf r (s + e) ⟨b, hb⟩ (S.smulOf s e ⟨b', hb'⟩ z)) :=
      S.tr_smulOf_mul ⟨b, hb⟩ ⟨b', hb'⟩ ⟨b * b', hbbI⟩ rfl z h (le_refl _)
    have h3 : S.tr (le_refl (r + (s + e)))
          (S.smulOf r (s + e) ⟨b, hb⟩ (S.smulOf s e ⟨b', hb'⟩ z)) =
        S.smulOf r (s + e) (⟨b, hb⟩ : ↥(I ^ r))
          (S.tr (le_refl (s + e)) (S.smulOf s e ⟨b', hb'⟩ z)) :=
      hcomp.tr_smulOf r (s + e) (s + e) (le_refl _) ⟨b, hb⟩ _
    change S.tr h (S.mul (r + s) e ⟨b * b', hbbJ⟩ z) ∈ S.smulSpan r (s + e)
    rw [h1, h2, h3]
    exact S.smulOf_mem_smulSpan _ _
  have ha : (a : A) ∈ I ^ r * I ^ s := by
    rw [← pow_add, ← pow_map_ringHom_id]
    exact a.2
  obtain ⟨z', hz', hza⟩ := hmul ha
  obtain rfl : z' = a := Subtype.ext hza
  exact hz'

/-- **The products `Iʳ · M c` span `M (r + c)`** as soon as homogeneous elements of degrees at
most `c` generate the system. This is the generation statement from which the source deduces
parts (1), (2), (4) and (5) of [Stacks, Tag 02OA]. -/
theorem top_le_smulSpan (hcomp : IsFiltrationCompatible S)
    {t : ℕ} {d : Fin t → ℕ} {x : ∀ i, M (d i)} {c : ℕ}
    (hgen : ∀ n, (⊤ : Submodule A (M n)) ≤ S.genSubmodule d x n) (hc : ∀ i, d i ≤ c) (r : ℕ) :
    (⊤ : Submodule A (M (r + c))) ≤ S.smulSpan r c := by
  refine (hgen (r + c)).trans (iSup_le fun i ↦ Submodule.span_le.2 ?_)
  rintro _ ⟨a, rfl⟩
  have hdc : d i ≤ c := hc i
  exact S.tr_mul_mem_smulSpan hcomp (by omega) (by omega) a (x i) _

/-- **[Stacks, Tag 02OA], part (1)** in the abstract: the multiplication map
`Iʳ ⊗_A M c → M (r + c)` is surjective, for every `r`, as soon as homogeneous elements of
degrees at most `c` generate the system. The source's indexing by `n ≥ c` is this one with
`r = n - c`. -/
theorem mulTensor_surjective (hcomp : IsFiltrationCompatible S)
    {t : ℕ} {d : Fin t → ℕ} {x : ∀ i, M (d i)} {c : ℕ}
    (hgen : ∀ n, (⊤ : Submodule A (M n)) ≤ S.genSubmodule d x n) (hc : ∀ i, d i ≤ c) (r : ℕ) :
    Function.Surjective (TensorProduct.lift (S.smulOf r c)) := by
  intro z
  have hz : z ∈ S.smulSpan r c := S.top_le_smulSpan hcomp hgen hc r Submodule.mem_top
  rw [smulSpan] at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      exact ⟨p.1 ⊗ₜ p.2, TensorProduct.lift.tmul _ _⟩
  | zero => exact ⟨0, map_zero _⟩
  | add y y' _ _ hy hy' =>
      obtain ⟨w, hw⟩ := hy
      obtain ⟨w', hw'⟩ := hy'
      exact ⟨w + w', by rw [map_add, hw, hw']⟩
  | smul a y _ hy =>
      obtain ⟨w, hw⟩ := hy
      exact ⟨a • w, by rw [map_smul, hw]⟩

/-! ### The image of a transition map -/

/-- The image of a transition map `M (r + c) → M n` with `n ≤ c` lies in `Iʳ · M n`. -/
private theorem range_tr_le_pow_smul_of_le (hcomp : IsFiltrationCompatible S)
    {t : ℕ} {d : Fin t → ℕ} {x : ∀ i, M (d i)} {c : ℕ}
    (hgen : ∀ n, (⊤ : Submodule A (M n)) ≤ S.genSubmodule d x n) (hc : ∀ i, d i ≤ c)
    {n r : ℕ} (hnc : n ≤ c) (h : n ≤ r + c) :
    LinearMap.range (S.tr h) ≤ I ^ r • (⊤ : Submodule A (M n)) := by
  have hmap : Submodule.map (S.tr h) (S.smulSpan r c) ≤ I ^ r • (⊤ : Submodule A (M n)) := by
    rw [smulSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    rw [← S.tr_tr hnc (Nat.le_add_left c r), hcomp.tr_smulOf_self r c p.1 p.2, map_smul]
    exact Submodule.smul_mem_smul p.1.2 Submodule.mem_top
  rintro _ ⟨w, rfl⟩
  exact hmap ⟨w, S.top_le_smulSpan hcomp hgen hc r Submodule.mem_top, rfl⟩

/-- **[Stacks, Tag 02OA], part (2)** in the abstract, in every degree: the image of
`M (m + n) → M n` lies in `I ^ (m - (c - n)) · M n` whenever `c ≤ m + n`, where `c` bounds the
degrees of a homogeneous generating family of the system. The source's exponent is `m - e` with
`e = max (0, c - n)`, which is `m - (c - n)` in truncated subtraction. -/
theorem range_tr_le_pow_smul (hcomp : IsFiltrationCompatible S)
    {t : ℕ} {d : Fin t → ℕ} {x : ∀ i, M (d i)} {c : ℕ}
    (hgen : ∀ n, (⊤ : Submodule A (M n)) ≤ S.genSubmodule d x n) (hc : ∀ i, d i ≤ c)
    (n m : ℕ) (hcnm : c ≤ m + n) :
    LinearMap.range (S.tr (Nat.le_add_left n m)) ≤
      I ^ (m - (c - n)) • (⊤ : Submodule A (M n)) := by
  rcases le_or_gt c n with hcn | hnc
  · -- `c ≤ n`: the exponent is `m`, and the generators also have degree at most `n`
    rw [show m - (c - n) = m by omega]
    exact S.range_tr_le_pow_smul_of_le hcomp hgen (fun i ↦ (hc i).trans hcn) le_rfl _
  · -- `n < c`: the generators have degree at most `c`, and `m + n = (m + n - c) + c`
    have hrc : m + n = (m + n - c) + c := by omega
    have hnrc : n ≤ (m + n - c) + c := by omega
    rw [S.toIdealPowerSystem.range_tr_congr (Nat.le_add_left n m) hnrc hrc,
      show m - (c - n) = m + n - c by omega]
    exact S.range_tr_le_pow_smul_of_le hcomp hgen hc hnc.le hnrc

/-! ### The comparison maps -/

/-- **The comparison map `Iⁿ M₀ → M (n - c)` of [Stacks, Tag 02OA] part (4)**, written at
`n = r + c`.

It sends `η` to the image under `M (r + c) → M r` of any preimage of `η` under
`proj : M (r + c) → M₀`. A preimage exists because `Iⁿ M₀` lies in the image of that map
(`hrange`), and the result does not depend on the choice because part (3) of the source
identifies the kernel of `proj` with the kernel of the transition map (`hker`). -/
noncomputable def comparison {r c : ℕ}
    (hrange : I ^ (r + c) • (⊤ : Submodule A M₀) ≤ LinearMap.range (S.proj (r + c)))
    (hker : LinearMap.ker (S.proj (r + c)) = LinearMap.ker (S.tr (Nat.le_add_right r c))) :
    ↥(I ^ (r + c) • (⊤ : Submodule A M₀)) →ₗ[A] M r :=
  (Submodule.liftQ _ (S.tr (Nat.le_add_right r c)) hker.le).comp
    (((LinearMap.quotKerEquivRange (S.proj (r + c))).symm.toLinearMap).comp
      (Submodule.inclusion hrange))

/-- **The defining property of the comparison map**: it is computed by any preimage under the
projection to `M₀`. -/
theorem comparison_apply {r c : ℕ}
    (hrange : I ^ (r + c) • (⊤ : Submodule A M₀) ≤ LinearMap.range (S.proj (r + c)))
    (hker : LinearMap.ker (S.proj (r + c)) = LinearMap.ker (S.tr (Nat.le_add_right r c)))
    (η : ↥(I ^ (r + c) • (⊤ : Submodule A M₀))) (z : M (r + c))
    (hz : S.proj (r + c) z = (η : M₀)) :
    S.comparison hrange hker η = S.tr (Nat.le_add_right r c) z := by
  have h1 : Submodule.inclusion hrange η =
      (⟨S.proj (r + c) z, LinearMap.mem_range_self _ z⟩ :
        ↥(LinearMap.range (S.proj (r + c)))) :=
    Subtype.ext hz.symm
  have h2 : (LinearMap.quotKerEquivRange (S.proj (r + c))).symm
      (Submodule.inclusion hrange η) = (LinearMap.ker (S.proj (r + c))).mkQ z := by
    rw [h1]
    exact LinearMap.quotKerEquivRange_symm_apply_image (S.proj (r + c)) z _
  change (Submodule.liftQ _ (S.tr (Nat.le_add_right r c)) hker.le)
      ((LinearMap.quotKerEquivRange (S.proj (r + c))).symm
        (Submodule.inclusion hrange η)) = _
  rw [h2]
  rfl

/-- **The second composition of [Stacks, Tag 02OA] part (4)**: `Iⁿ M₀ → M (n - c) → M₀` is the
inclusion of `Iⁿ M₀`, so after corestriction to `Iⁿ⁻²ᶜ M₀` it is the canonical inclusion. -/
theorem proj_comparison {r c : ℕ}
    (hrange : I ^ (r + c) • (⊤ : Submodule A M₀) ≤ LinearMap.range (S.proj (r + c)))
    (hker : LinearMap.ker (S.proj (r + c)) = LinearMap.ker (S.tr (Nat.le_add_right r c)))
    (η : ↥(I ^ (r + c) • (⊤ : Submodule A M₀))) :
    S.proj r (S.comparison hrange hker η) = (η : M₀) := by
  obtain ⟨z, hz⟩ := hrange η.2
  rw [S.comparison_apply hrange hker η z hz, S.proj_tr, hz]

/-- **The first composition of [Stacks, Tag 02OA] part (4)**: `M (r + 2c) → Iʳ⁺ᶜ M₀ → M r` is
the transition map of the system. -/
theorem comparison_proj {r c : ℕ}
    (hrange : I ^ (r + c) • (⊤ : Submodule A M₀) ≤ LinearMap.range (S.proj (r + c)))
    (hker : LinearMap.ker (S.proj (r + c)) = LinearMap.ker (S.tr (Nat.le_add_right r c)))
    (z : M (r + c + c)) (hz : S.proj (r + c + c) z ∈ I ^ (r + c) • (⊤ : Submodule A M₀)) :
    S.comparison hrange hker ⟨S.proj (r + c + c) z, hz⟩ =
      S.tr (show r ≤ r + c + c by omega) z := by
  have hw : S.proj (r + c) (S.tr (Nat.le_add_right (r + c) c) z) = S.proj (r + c + c) z :=
    S.proj_tr _ z
  rw [S.comparison_apply hrange hker _ _ hw, S.tr_tr]

/-! ### One constant for every clause -/

/-- **The abstract core of [Stacks, Tag 02OA]** for a Noetherian system whose multiplication
maps are compatible with its transition maps and whose projections hit every `Iⁿ M₀`: one
constant `c` at once makes the multiplication `Iʳ ⊗ M c → M (r + c)` surjective, bounds the
image of every transition map `M (m + n) → M n` by `I ^ (m - (c - n)) · M n`, bounds the image
of `M r → M₀` by `Iʳ⁻ᶜ M₀`, identifies the kernel of `M k → M₀` with the kernel of
`M k → M m` for `m + c ≤ k`, and produces the comparison maps `Iʳ⁺ᶜ M₀ → M r` whose two
composites with the projections are the canonical maps.

The third and fourth clauses are `IdealPowerSystem.exists_uniform_bound`, restated here with
the same constant as the others. -/
theorem exists_uniform_bound_mul [IsNoetherianRing A] (hcomp : IsFiltrationCompatible S)
    (hrange : ∀ n : ℕ, I ^ n • (⊤ : Submodule A M₀) ≤ LinearMap.range (S.proj n))
    (hfin : S.IsReesFinite) :
    ∃ c : ℕ,
      (∀ r : ℕ, Function.Surjective (TensorProduct.lift (S.smulOf r c))) ∧
      (∀ n m : ℕ, c ≤ m + n → LinearMap.range (S.tr (Nat.le_add_left n m)) ≤
        I ^ (m - (c - n)) • (⊤ : Submodule A (M n))) ∧
      (∀ r : ℕ, c ≤ r → LinearMap.range (S.proj r) ≤
        I ^ (r - c) • (⊤ : Submodule A M₀)) ∧
      (∀ (m k : ℕ) (hmk : m + c ≤ k), LinearMap.ker (S.proj k) =
        LinearMap.ker (S.tr (show m ≤ k from le_trans (Nat.le_add_right m c) hmk))) ∧
      (∀ r : ℕ, ∃ ν : ↥(I ^ (r + c) • (⊤ : Submodule A M₀)) →ₗ[A] M r,
        (∀ η : ↥(I ^ (r + c) • (⊤ : Submodule A M₀)), S.proj r (ν η) = (η : M₀)) ∧
        (∀ (z : M (r + c + c))
            (hz : S.proj (r + c + c) z ∈ I ^ (r + c) • (⊤ : Submodule A M₀)),
          ν ⟨S.proj (r + c + c) z, hz⟩ =
            S.tr ((Nat.le_add_right r c).trans (Nat.le_add_right (r + c) c)) z)) := by
  have hnoe := S.isNoetherianSystem_of_isReesFinite hfin
  obtain ⟨t₁, d₁, x, -, hgen₁⟩ := hnoe S.topSubsystem
  obtain ⟨t₂, d₂, y, hy, hgen₂⟩ := hnoe S.kerSubsystem
  have hgen₁' : ∀ n, (⊤ : Submodule A (M n)) ≤ S.genSubmodule d₁ x n := hgen₁
  have hgen₂' : ∀ n, LinearMap.ker (S.proj n) ≤ S.genSubmodule d₂ y n := hgen₂
  have hyker : ∀ i, S.proj (d₂ i) (y i) = 0 := fun i ↦ LinearMap.mem_ker.mp (hy i)
  set c := max (Finset.univ.sup d₁) (Finset.univ.sup d₂) with hcdef
  have hc₁ : ∀ i, d₁ i ≤ c := fun i ↦
    le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_left _ _)
  have hc₂ : ∀ i, d₂ i ≤ c := fun i ↦
    le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_right _ _)
  have hkerAt : ∀ r : ℕ, LinearMap.ker (S.proj (r + c)) =
      LinearMap.ker (S.tr (Nat.le_add_right r c)) := fun r ↦
    S.toIdealPowerSystem.ker_proj_eq_ker_tr hyker hgen₂' hc₂ r (r + c) (le_refl (r + c))
  refine ⟨c, fun r ↦ S.mulTensor_surjective hcomp hgen₁' hc₁ r,
    fun n m hcnm ↦ S.range_tr_le_pow_smul hcomp hgen₁' hc₁ n m hcnm,
    fun r hr ↦ (S.toIdealPowerSystem.range_proj_le hgen₁' hc₁ r hr).trans
      (le_of_eq (by rw [pow_map_ringHom_id])),
    fun m k hmk ↦ S.toIdealPowerSystem.ker_proj_eq_ker_tr hyker hgen₂' hc₂ m k hmk,
    fun r ↦ ⟨S.comparison (hrange (r + c)) (hkerAt r),
      fun η ↦ S.proj_comparison _ _ η, fun z hz ↦ S.comparison_proj _ _ z hz⟩⟩

end ReesSystem

end Stacks.RingTheory

end
