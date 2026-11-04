module

public import StacksFrontier.RingTheory.HilbertFunction.Polynomiality
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Data.Rat.Star
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.AffineMonoid.UniqueSums

-- ===== merged from StacksDraft.Ch10.Sec58.Tag00K3 =====

/-!
# The Hilbert function of a graded quotient of a polynomial ring

Throughout, `k` is a field and `d ≥ 1` is a positive integer. Let
`S = k[X_1, …, X_d]` be the polynomial ring in `d` variables, regarded as a
graded `k`-algebra with the standard grading in which each variable `X_i` has
degree `1`. For an integer `n ≥ 0`, the degree-`n` graded piece `S_n` is the
`k`-vector space of homogeneous polynomials of degree `n` (together with `0`);
for `n < 0` we set `S_n = 0`.

We formalize the following (Stacks Lemma 10.58.10, Tag 00K3):

  Let `k` be a field, let `d ≥ 1`, and let `S = k[X_1, …, X_d]` with the standard
  grading. Let `I ⊆ S` be a *nonzero* graded ideal and set `M = S / I`. Then the
  Hilbert function `H_M(n) = dim_k(M_n)` is a numerical polynomial whose degree is
  strictly less than `d - 1`.

In particular there exist a polynomial `P ∈ ℚ[T]` with `deg P < d - 1` and an
integer `N` such that `dim_k(M_n) = P(n)` for all `n ≥ N`. (Here `deg P < d - 1`
allows `P` to be the zero polynomial, whose degree is taken to be `-∞`; this is
modeled in Lean by `Polynomial.degree`, which sends the zero polynomial to `⊥`.)
When `d = 1`, the bound `deg P < 0` forces `P = 0`, equivalently
`dim_k(M_n) = 0` for all sufficiently large `n`.
-/

@[expose] public section
-- needed file-wide: `FinModule.cls_eq_of_linearEquiv`, `FinModule.cls_add_of_ses`,
-- `KPrime0.hom_ext`, `xpow_four_term_class` and `hilbertFun_xpow_step_identity` all rewrite
-- through the `FinModule`/`KPrime0` quotient wrappers and the graded-piece subgroup coercions,
-- which only unfold with defeq transparency relaxed.  See also the note before
-- `section MainPieces`, which depends on this option holding for the whole file.
set_option backward.isDefEq.respectTransparency false
universe u

namespace Stacks.HilbertFunction.PolynomialQuotient

/-! ## Background and setup

We model `S = k[X_1, …, X_d]` as `MvPolynomial (Fin d) k`. The standard grading is
the total-degree grading, whose degree-`n` piece is the `k`-submodule
`MvPolynomial.homogeneousSubmodule (Fin d) k n` of homogeneous polynomials of
degree `n`. The total-degree grading makes `S` a graded algebra via
`MvPolynomial.gradedAlgebra` (registered as an instance below so that
`Ideal.IsHomogeneous` can refer to it). -/

/-- The total-degree grading turns `k[X_1, …, X_d]` into a graded algebra.
This is `MvPolynomial.gradedAlgebra`, registered here as an instance so that the
homogeneity predicate `Ideal.IsHomogeneous` is available for ideals of
`MvPolynomial (Fin d) k`. -/
@[ega "0 15.1.1" "special case"]
noncomputable instance instGradedAlgebra (k : Type*) [Field k] (d : ℕ) :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin d) k) :=
  MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {d : ℕ}

/-- The degree-`n` graded piece of
`S = k[X_1, …, X_d]`: the `k`-vector space of homogeneous polynomials of degree
`n`. -/
noncomputable def gradedPieceS (k : Type*) [Field k] (d : ℕ) (n : ℕ) :
    Submodule k (MvPolynomial (Fin d) k) :=
  MvPolynomial.homogeneousSubmodule (Fin d) k n

/-- For an ideal `I ⊆ S`, its
degree-`n` graded piece, viewed as a `k`-vector space: the intersection of `I`
(restricted to a `k`-submodule) with the degree-`n` piece `S_n`. When `I` is a
graded ideal this is the `n`-th graded piece of `I` in the usual sense. -/
noncomputable def gradedPieceI (I : Ideal (MvPolynomial (Fin d) k)) (n : ℕ) :
    Submodule k (MvPolynomial (Fin d) k) :=
  (I.restrictScalars k) ⊓ gradedPieceS k d n

/-- The Hilbert function of `M = S / I`,
defined by `H_M(n) = dim_k(M_n) = dim_k(S_n) - dim_k(I_n)`. Since `I_n ⊆ S_n` and
both are finite dimensional, the truncated subtraction on `ℕ` agrees with the
honest difference `dim_k(M_n)`. -/
noncomputable def hilbertFunction (I : Ideal (MvPolynomial (Fin d) k)) (n : ℕ) : ℕ :=
  Module.finrank k (gradedPieceS k d n) - Module.finrank k (gradedPieceI I n)

/-! ## Correctness statements for the definitions

These auxiliary statements pin down the definitions above and connect them to the
standard descriptions of the Hilbert function. -/

/-- Correctness of `gradedPieceS`: the degree-`n` piece has dimension
`binomial(n + d - 1, n)`, the standard dimension count for the number of
monomials of total degree `n` in `d` variables (equivalently the number of
weak compositions of `n` into `d` parts). We use the form `(n + d - 1).choose n`
rather than `(n + d - 1).choose (d - 1)` because the former is valid for *all*
`d ≥ 0`: for `d = 0` it gives dimension `1` when `n = 0` (the constants `k`) and
`0` when `n > 0`, matching `S = k[]`, whereas `(n + d - 1).choose (d - 1)` would
incorrectly give `1` for `d = 0`, `n > 0`. The two forms agree for `d ≥ 1`. -/
theorem finrank_gradedPieceS (k : Type*) [Field k] (d : ℕ) (n : ℕ) :
    Module.finrank k (gradedPieceS k d n) = (n + d - 1).choose n := by
  -- STRATEGY (self-contained combinatorics, independent of `I`):
  -- `gradedPieceS k d n = homogeneousSubmodule (Fin d) k n`, and by
  -- `MvPolynomial.homogeneousSubmodule_eq_finsupp_supported` this equals
  -- `Finsupp.supported k k {f : Fin d →₀ ℕ | Finsupp.degree f = n}`.
  -- The monomials `{X^f | Finsupp.degree f = n}` form a `k`-basis of this submodule
  -- (a free module on the index set `s := {f | f.degree = n}`); use
  -- `Finsupp.supportedEquivFinsupp s : ↥(Finsupp.supported k k s) ≃ₗ[k] (↥s →₀ k)`
  -- together with `Finsupp.basisSingleOne`/`Module.Basis.ofVectorSpace`-style
  -- `Finsupp` basis to get `finrank k = Fintype.card ↥s = s.toFinset.card`.
  -- Then it remains to count weak compositions:
  --   `Fintype.card {f : Fin d →₀ ℕ // Finsupp.degree f = n} = (n + d - 1).choose n`.
  -- This count is `Nat.multichoose d n` (number of multisets of size `n` from `d`
  -- elements): `Sym.card_sym_eq_multichoose (Fin d) n` gives
  -- `Fintype.card (Sym (Fin d) n) = (Fintype.card (Fin d)).multichoose n = d.multichoose n`,
  -- and `Nat.multichoose_eq d n : d.multichoose n = (d + n - 1).choose n`; finally
  -- `(d + n - 1).choose n = (n + d - 1).choose n` by `add_comm`. The remaining glue
  -- is the bijection `{f : Fin d →₀ ℕ // f.degree = n} ≃ Sym (Fin d) n` (a finsupp
  -- valued in ℕ with total `n` ⇄ the multiset of its variables with multiplicity),
  -- which can be assembled from `Finsupp`/`Multiset` API (`Finsupp.toMultiset`,
  -- `Multiset.toFinsupp`) restricted to total degree `n`.
  -- NOTE: `d = 0` edge case is consistent: for `d = 0`, `S = k[]`, `S_0 = k`
  -- (dim 1 = `(0-1).choose 0 = 1` with ℕ truncated subtraction giving `0.choose 0`)
  -- and `S_n = 0` for `n > 0` (`(n-1).choose n = 0`).
  unfold gradedPieceS
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  let myEquiv :
    { f : Fin d →₀ ℕ // f ∈ {f : Fin d →₀ ℕ | Finsupp.degree f = n} } ≃ Sym (Fin d) n :=
    { toFun := fun f =>
        ⟨Finsupp.toMultiset f.val, by
          have h : (Finsupp.toMultiset f.val).card = Finsupp.degree f.val :=
            Finsupp.card_toMultiset f.val
          rw [h]; exact f.property⟩
      invFun := fun s =>
        ⟨Multiset.toFinsupp s.val, by
          show Finsupp.degree (Multiset.toFinsupp s.val) = n
          have h :
            Finsupp.degree (Multiset.toFinsupp s.val) =
              (Finsupp.toMultiset (Multiset.toFinsupp s.val)).card := by
            rw [Finsupp.card_toMultiset]; rfl
          rw [h, Multiset.toFinsupp_toMultiset]
          exact s.property⟩
      left_inv := fun f => by
        apply Subtype.ext
        simp
      right_inv := fun s => by
        apply Subtype.ext
        simp }
  let : Fintype { f : Fin d →₀ ℕ // f ∈ {f : Fin d →₀ ℕ | Finsupp.degree f = n} } :=
    Fintype.ofEquiv _ myEquiv.symm
  have hcard :
    Fintype.card { f : Fin d →₀ ℕ // f ∈ {f : Fin d →₀ ℕ | Finsupp.degree f = n} } =
      (n + d - 1).choose n := by
    rw [Fintype.card_congr myEquiv, Sym.card_sym_eq_multichoose, Fintype.card_fin,
      Nat.multichoose_eq, add_comm]
  rw [← hcard]
  exact
    (LinearEquiv.finrank_eq
          (AddMonoidAlgebra.supportedEquivFinsupp {f : Fin d →₀ ℕ | Finsupp.degree f = n})).trans
      (Module.finrank_finsupp_self k)

/-- Correctness of `hilbertFunction`: it really computes `dim_k (S_n / I_n)`, the
dimension of the `n`-th graded piece `M_n = S_n / I_n` of the quotient module
`M = S / I`. -/
theorem hilbertFunction_eq_finrank_quotient (I : Ideal (MvPolynomial (Fin d) k)) (n : ℕ) :
    hilbertFunction I n =
      Module.finrank k
        ((gradedPieceS k d n) ⧸
          (Submodule.comap (gradedPieceS k d n).subtype (gradedPieceI I n))) := by
  -- STRATEGY (rank–nullity on the inclusion `gradedPieceI I n ⊆ gradedPieceS k d n`):
  -- Write `Sn := gradedPieceS k d n`, `In := gradedPieceI I n`. By definition
  -- `gradedPieceI I n = I.restrictScalars k ⊓ Sn ≤ Sn`, so
  -- `p := Submodule.comap Sn.subtype In` is a submodule of `↥Sn` and
  --   `Module.finrank k ↥p = Module.finrank k ↥In`
  -- via the linear equivalence `Sn.subtype` restricted to `In` (an injection of
  -- `In` into `↥Sn` with image `p`); use `Submodule.comap_subtype_equiv_of_le`
  -- (needs `In ≤ Sn`) or `LinearEquiv.finrank_eq` on
  -- `Submodule.comapSubtypeEquivOfLe`.
  -- `↥Sn` is finite dimensional (it sits inside `S_n`, dimension `(n+d-1).choose n`),
  -- so by `Submodule.finrank_quotient_add_finrank p`:
  --   finrank (↥Sn ⧸ p) + finrank p = finrank ↥Sn.
  -- Therefore
  --   finrank (↥Sn ⧸ p) = finrank ↥Sn - finrank p = finrank Sn - finrank In,
  -- where the ℕ truncated subtraction is exact because `finrank p = finrank In ≤
  -- finrank Sn`. The left side is the goal's RHS, the right side is
  -- `hilbertFunction I n` by definition. Key lemmas:
  -- `Submodule.finrank_quotient_add_finrank`, `LinearEquiv.finrank_eq`,
  -- `Submodule.comapSubtypeEquivOfLe`, and `inf_le_right` for `In ≤ Sn`.
  set Sn := gradedPieceS k d n with hSn
  set In := gradedPieceI I n with hIn
  have hle : In ≤ Sn := by
    rw [hIn, hSn, gradedPieceI]
    exact inf_le_right
  set p := Submodule.comap Sn.subtype In with hp
  have : FiniteDimensional k Sn := by
    rw [hSn, gradedPieceS, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    have hfin : Finite {x : Fin d →₀ ℕ | Finsupp.degree x = n} := by
      apply
        Finite.of_injective (f := fun (x : {x : Fin d →₀ ℕ | Finsupp.degree x = n}) (i : Fin d) =>
          (⟨(x : Fin d →₀ ℕ) i, by
              have hx : Finsupp.degree (x : Fin d →₀ ℕ) = n := x.property
              have hle : (x : Fin d →₀ ℕ) i ≤ Finsupp.degree (x : Fin d →₀ ℕ) :=
                Finsupp.le_degree i _
              omega⟩ :
            Fin (n + 1)))
      intro a b hab
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      have := congrFun hab i
      simpa using congrArg Fin.val this
    have : Fintype {x : Fin d →₀ ℕ | Finsupp.degree x = n} := Fintype.ofFinite _
    exact
      LinearEquiv.finiteDimensional
        (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
            {x : Fin d →₀ ℕ | Finsupp.degree x = n}).symm
  have hpIn : Module.finrank k p = Module.finrank k In :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)
  have hrn := Submodule.finrank_quotient_add_finrank p
  unfold hilbertFunction
  rw [← hSn, ← hIn, ← hpIn]
  omega

/-! ## Decomposition lemmas for the main theorem

The main theorem is reduced to the lemmas below. The proof idea (Stacks) is:
pick a nonzero homogeneous `f ∈ I` of degree `e`; multiplication by `f` injects
`S_{n-e}` into `I_n`, so `dim I_n ≥ dim S_{n-e}`, giving an upper bound on `H_M`
by a binomial difference of degree `< d-1`; combine with the background fact that
`H_M` is a numerical polynomial to bound the *degree* of its representing
polynomial. -/

/-- If `I` is a homogeneous
ideal containing a nonzero homogeneous element of degree `e`, then for every
`n ≥ e` the dimension of the degree-`n` piece `I_n` is at least the dimension of
`S_{n-e}`. Concretely there is an integer `e` (the degree of a chosen nonzero
homogeneous generator) with, for all `n ≥ e`,
`finrank (gradedPieceI I n) ≥ (n - e + d - 1).choose (n - e)`.

INFORMAL ARGUMENT. Since `I ≠ 0` is homogeneous, `I` has a nonzero homogeneous
element `f` of some degree `e` (extract from a nonzero element via its
homogeneous components: a nonzero element has a nonzero homogeneous component,
which lies in `I` by homogeneity). For `n ≥ e`, multiplication by `f`,
`g ↦ f * g`, is a `k`-linear map `S_{n-e} → S_n`. It lands in `I_n`: `f * g ∈ I`
since `f ∈ I`, and `f * g` is homogeneous of degree `e + (n-e) = n`, so
`f * g ∈ I ∩ S_n = I_n`. It is *injective* because `MvPolynomial (Fin d) k` is an
integral domain (`k` a field) and `f ≠ 0`, so `f * g = 0 ⟹ g = 0`. An injective
`k`-linear map gives `finrank (I_n) ≥ finrank (S_{n-e})`
(`LinearMap.finrank_le_finrank_of_injective` / `Submodule.finrank_mono` on the
range), and `finrank (S_{n-e}) = (n - e + d - 1).choose (n - e)` by
`finrank_gradedPieceS`. -/
theorem exists_finrank_gradedPieceI_ge (I : Ideal (MvPolynomial (Fin d) k))
    (hI_hom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin d) k) I)
    (hI_ne : I ≠ ⊥) :
    ∃ e : ℕ,
      ∀ n : ℕ, e ≤ n → (n - e + d - 1).choose (n - e) ≤ Module.finrank k (gradedPieceI I n) := by
  -- helper: finiteness of gradedPieceS
  have hSfin : ∀ m : ℕ, Module.Finite k (gradedPieceS k d m) := by
    intro m
    have degree_eq_card : ∀ (f : Fin d →₀ ℕ), Finsupp.degree f = (Finsupp.toMultiset f).card :=
      fun f => by
      rw [Finsupp.card_toMultiset]; rfl
    let myEquiv :
      { f : Fin d →₀ ℕ // f ∈ {f : Fin d →₀ ℕ | Finsupp.degree f = m} } ≃ Sym (Fin d) m :=
      { toFun := fun ⟨f, hf⟩ =>
          ⟨Finsupp.toMultiset f, by
            rw [← degree_eq_card]; exact hf⟩
        invFun := fun s =>
          ⟨Multiset.toFinsupp s.val, by
            rw [Set.mem_ofPred_eq, degree_eq_card, Multiset.toFinsupp_toMultiset];
            exact s.property⟩
        left_inv := by
          rintro ⟨f, hf⟩; simp
        right_inv := by
          rintro ⟨s, hs⟩; simp }
    let : Fintype ↥{f : Fin d →₀ ℕ | Finsupp.degree f = m} := Fintype.ofEquiv _ myEquiv.symm
    rw [gradedPieceS, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    exact
      Module.Finite.equiv
        (AddMonoidAlgebra.supportedEquivFinsupp (S := k) (R := k)
            {f : Fin d →₀ ℕ | Finsupp.degree f = m}).symm
  rw [Submodule.ne_bot_iff] at hI_ne
  obtain ⟨p, hpI, hp0⟩ := hI_ne
  -- find a nonzero homogeneous component
  have hex :
    ∃ e : ℕ,
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin d) k) p e :
          MvPolynomial (Fin d) k) ≠
        0 := by
    by_contra h
    push Not at h
    apply hp0
    have hz : DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin d) k) p = 0 := by
      apply DFinsupp.ext
      intro e
      apply Subtype.ext
      rw [h e]; rfl
    have h2 :=
      congrArg (DirectSum.decomposeAddEquiv (MvPolynomial.homogeneousSubmodule (Fin d) k)).symm hz
    simpa using h2
  obtain ⟨e, hfe⟩ := hex
  set f : MvPolynomial (Fin d) k :=
    (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin d) k) p e :
      MvPolynomial (Fin d) k) with
    hf_def
  have hfI : f ∈ I := hI_hom e hpI
  have hfhom : f.IsHomogeneous e := by
    have := (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin d) k) p e).property
    rwa [MvPolynomial.mem_homogeneousSubmodule] at this
  refine ⟨e, fun n hen => ?_⟩
  have : Module.Finite k (gradedPieceS k d n) := hSfin n
  have : Module.Finite k (gradedPieceI I n) := by
    have hle : gradedPieceI I n ≤ gradedPieceS k d n := inf_le_right
    exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  -- the multiplication-by-`f` map `S_{n-e} → I_n`
  have hdeg : e + (n - e) = n := by omega
  let φ : gradedPieceS k d (n - e) →ₗ[k] gradedPieceI I n :=
    { toFun := fun g =>
        ⟨f * (g : MvPolynomial (Fin d) k), by
          refine ⟨Ideal.mul_mem_right _ _ hfI, ?_⟩
          have hmul := hfhom.mul ((MvPolynomial.mem_homogeneousSubmodule _ _).mp g.property)
          rw [hdeg] at hmul
          exact (MvPolynomial.mem_homogeneousSubmodule n _).mpr hmul⟩
      map_add' := fun g h => Subtype.ext (by simp [mul_add])
      map_smul' := fun c g => Subtype.ext (by simp) }
  have hinj : Function.Injective φ := by
    intro g h hgh
    apply Subtype.ext
    have heq : f * (g : MvPolynomial (Fin d) k) = f * (h : MvPolynomial (Fin d) k) := by
      simpa [φ] using Subtype.ext_iff.mp hgh
    exact mul_left_cancel₀ hfe heq
  have hrank := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [finrank_gradedPieceS] at hrank

/-- With `e` as in
`exists_finrank_gradedPieceI_ge`, for all `n ≥ e` the Hilbert function is bounded
by the binomial difference
`H_M(n) ≤ (n + d - 1).choose n - (n - e + d - 1).choose (n - e)`.

INFORMAL ARGUMENT. By definition `H_M(n) = finrank S_n - finrank I_n` (truncated
ℕ subtraction). Using `finrank_gradedPieceS` for `finrank S_n = (n+d-1).choose n`
and the lower bound `finrank I_n ≥ (n-e+d-1).choose(n-e)` from
`exists_finrank_gradedPieceI_ge`, monotonicity of truncated subtraction
(`Nat.sub_le_sub_left`) gives the claim. -/
theorem hilbertFunction_le_choose_diff (I : Ideal (MvPolynomial (Fin d) k))
    (hI_hom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin d) k) I)
    (hI_ne : I ≠ ⊥) :
    ∃ e : ℕ,
      ∀ n : ℕ,
        e ≤ n → hilbertFunction I n ≤ (n + d - 1).choose n - (n - e + d - 1).choose (n - e) := by
  -- Take `e` from `exists_finrank_gradedPieceI_ge`. Unfold `hilbertFunction`,
  -- rewrite `finrank (gradedPieceS k d n) = (n+d-1).choose n` via
  -- `finrank_gradedPieceS`, and apply `Nat.sub_le_sub_left` with the lower bound
  -- on `finrank (gradedPieceI I n)`.
  obtain ⟨e, he⟩ := exists_finrank_gradedPieceI_ge I hI_hom hI_ne
  refine ⟨e, fun n hn => ?_⟩
  unfold hilbertFunction
  rw [finrank_gradedPieceS]
  exact Nat.sub_le_sub_left (he n hn) ((n + d - 1).choose n)

/-- For any `e` and `d ≥ 1`, the function
`n ↦ (n + d - 1).choose (d - 1) - (n - e + d - 1).choose (d - 1)` agrees, for
`n ≥ e`, with a polynomial `Q ∈ ℚ[T]` of degree `≤ d - 2` (i.e. `< d - 1`); when
`d = 1` or `e = 0` it is identically `0`.

INFORMAL ARGUMENT. Over ℚ, `m ↦ (m + d - 1).choose (d - 1)` is the polynomial
`B_d(m) = (m+d-1)(m+d-2)···(m+1)/(d-1)!`, monic of degree `d - 1` in `m`. The
difference `B_d(n) - B_d(n - e)` is `B_d(X) - B_d(X - e)` evaluated at `n`; since
`B_d` has degree `d - 1` and leading term `X^{d-1}/(d-1)!`, the degree-`(d-1)`
terms cancel (`X^{d-1} - (X-e)^{d-1}` has degree `d - 2`), so the difference has
degree `≤ d - 2 = (d-1) - 1 < d - 1`. For `d = 1`, `B_1 ≡ 1`, so the difference
is `1 - 1 = 0`. Note for `n ≥ e ≥ 1` and `d ≥ 1` the ℕ binomials equal these ℚ
values: `(n + d - 1).choose (d-1)` with `n + d - 1 ≥ d - 1`, and the `n` and
`d-1` forms of `choose` agree (`(n+d-1).choose n = (n+d-1).choose (d-1)` since
`(n+d-1) - n = d - 1`). -/
theorem exists_polynomial_choose_diff (e : ℕ) (hd : 1 ≤ d) :
    ∃ Q : Polynomial ℚ,
      Q.degree < ((d - 1 : ℕ) : WithBot ℕ) ∧
        ∀ n : ℕ,
          e ≤ n →
            ((((n + d - 1).choose (d - 1) : ℕ) : ℚ) - (((n - e + d - 1).choose (d - 1) : ℕ) : ℚ)) =
              Q.eval (n : ℚ) := by
  -- Build `B : ℚ[X]` with `B.eval m = (m+d-1).choose (d-1)` for all `m : ℕ`,
  -- e.g. `B = ∏ i in Finset.range (d-1), (X + (i+1))  /  (d-1)!` (the ascending
  -- factorial). `Polynomial.ascPochhammer`/`Polynomial.descPochhammer` and
  -- `Nat.choose`–`ascPochhammer` bridge lemmas give `B.eval n = (n+d-1).choose (d-1)`.
  -- Set `Q := B.comp X - B.comp (X - C e)`. Then:
  --   * `Q.eval n = B(n) - B(n-e)` for `n ≥ e` (compatibility of ℚ-subtraction).
  --   * `B` has degree `d-1` with leading coeff `1/(d-1)!`; `B.comp (X - C e)` has
  --     the same degree and leading coeff, so the `X^{d-1}` terms cancel in `Q`,
  --     giving `Q.degree ≤ d-2 < d-1` (`Polynomial.degree_sub_lt` when degrees and
  --     leading coeffs agree). For `d = 1`, `B = C 1`, so `Q = 0`, `degree = ⊥`.
  set B : Polynomial ℚ :=
    Polynomial.C (((d - 1).factorial : ℚ))⁻¹ *
      (ascPochhammer ℚ (d - 1)).comp (Polynomial.X + 1) with
    hB
  have hBeval : ∀ m : ℕ, B.eval (m : ℚ) = ((m + d - 1).choose (d - 1) : ℚ) := by
    intro m
    rw [hB, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    have hcast : ((m : ℚ) + 1) = ((m + 1 : ℕ) : ℚ) := by
      push_cast; ring
    rw [hcast, ← ascPochhammer_eval_cast ℚ (d - 1) (m + 1), ascPochhammer_nat_eq_ascFactorial]
    have harith :
      (m + d - 1).choose (d - 1) = (m + 1).ascFactorial (d - 1) / (d - 1).factorial := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      congr 1
      rw [show m + d - 1 = m + (d - 1) by omega]
      exact Nat.add_descFactorial_eq_ascFactorial m (d - 1)
    rw [harith, Nat.cast_div (Nat.factorial_dvd_ascFactorial (m + 1) (d - 1))]
    · rw [div_eq_inv_mul]
    · exact_mod_cast (Nat.factorial_ne_zero (d - 1))
  have hdegB : B.degree = ((d - 1 : ℕ) : WithBot ℕ) := by
    have hc : (((d - 1).factorial : ℚ))⁻¹ ≠ 0 := by simp [Nat.factorial_ne_zero]
    rw [hB, Polynomial.degree_C_mul hc, Polynomial.degree_comp]
    · have hap : (ascPochhammer ℚ (d - 1)).degree = ((d - 1 : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree (monic_ascPochhammer ℚ (d - 1)).ne_zero,
          ascPochhammer_natDegree]
      have hx1 : (Polynomial.X + 1 : Polynomial ℚ).degree = 1 := by
        rw [show (Polynomial.X + 1 : Polynomial ℚ) = Polynomial.X - Polynomial.C (-1) by
            rw [map_neg, map_one, sub_neg_eq_add],
          Polynomial.degree_X_sub_C]
      rw [hap, hx1, mul_one]
    · rw [show (Polynomial.X + 1 : Polynomial ℚ) = Polynomial.X - Polynomial.C (-1) by
          rw [map_neg, map_one, sub_neg_eq_add],
        Polynomial.degree_X_sub_C]
      norm_num
  have hdegcomp : (B.comp (Polynomial.X - Polynomial.C (e : ℚ))).degree = B.degree := by
    rcases eq_or_ne B 0 with h | h
    · simp [h]
    rw [Polynomial.degree_comp]
    · rw [Polynomial.degree_X_sub_C, mul_one]
    · rw [Polynomial.degree_X_sub_C]; norm_num
  have hlccomp : (B.comp (Polynomial.X - Polynomial.C (e : ℚ))).leadingCoeff = B.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp]
    · rw [(Polynomial.monic_X_sub_C (e : ℚ)).leadingCoeff, one_pow, mul_one]
    · rw [Polynomial.natDegree_X_sub_C]; norm_num
  refine ⟨B - B.comp (Polynomial.X - Polynomial.C (e : ℚ)), ?_, ?_⟩
  · rcases eq_or_ne (B - B.comp (Polynomial.X - Polynomial.C (e : ℚ))) 0 with hQ | hQ
    · rw [hQ]; simp only [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · have hBne : B ≠ 0 := by
        intro h0; apply hQ; rw [h0]; simp
      have hlt := Polynomial.degree_sub_lt_left hdegcomp.symm hBne hlccomp.symm
      rwa [hdegB] at hlt
  · intro n hn
    rw [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    rw [hBeval n]
    have hne : ((n : ℚ) - (e : ℚ)) = ((n - e : ℕ) : ℚ) := by rw [Nat.cast_sub hn]
    rw [hne, hBeval (n - e)]

/-- Auxiliary: the rational binomial polynomial `X·(X-1)···(X-i+1)/i!`, whose
evaluation at `q : ℚ` equals `Ring.choose q i`. -/
noncomputable def binomialPoly (i : ℕ) : Polynomial ℚ :=
  Polynomial.C (1 / (i.factorial : ℚ)) * descPochhammer ℚ i

open Polynomial in
/-- Evaluation of the rational binomial polynomial equals `Ring.choose`. -/
theorem binomialPoly_eval (i : ℕ) (q : ℚ) : (binomialPoly i).eval q = Ring.choose q i := by
  unfold binomialPoly
  rw [eval_mul, eval_C]
  have hdp : (descPochhammer ℚ i).eval q = (i.factorial : ℚ) * Ring.choose q i := by
    rw [← descPochhammer_map (algebraMap ℤ ℚ), ← eval₂_eq_eval_map, ← aeval_def, aeval_eq_smeval,
      Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  rw [hdp]; field_simp

open Polynomial Filter in
/-- If a rational polynomial is eventually nonnegative along the integers, its
leading coefficient is nonnegative. -/
theorem leadingCoeff_nonneg_of_eventually_nonneg (P : Polynomial ℚ)
    (h : ∀ᶠ n : ℤ in atTop, 0 ≤ P.eval (n : ℚ)) :
    0 ≤ P.leadingCoeff := by
  by_contra hlt
  rw [not_le] at hlt
  rcases le_or_gt P.degree 0 with hd | hd
  · obtain ⟨n, hn⟩ := h.exists
    have hconst : P.eval (n : ℚ) = P.leadingCoeff := by
      conv_lhs => rw [eq_C_of_degree_le_zero hd]
      conv_rhs => rw [eq_C_of_degree_le_zero hd]
      rw [eval_C, leadingCoeff_C]
    rw [hconst] at hn
    exact absurd hn (not_le.mpr hlt)
  · have htb : Tendsto (fun x => eval x P) atTop atBot :=
      tendsto_atBot_of_leadingCoeff_nonpos P hd hlt.le
    have hcomp : Tendsto (fun n : ℤ => eval (n : ℚ) P) atTop atBot :=
      htb.comp tendsto_intCast_atTop_atTop
    have hev : ∀ᶠ n : ℤ in atTop, eval (n : ℚ) P < 0 := hcomp.eventually_lt_atBot 0
    obtain ⟨n, hn1, hn2⟩ := (h.and hev).exists
    exact absurd hn1 (not_le.mpr hn2)

open Polynomial Filter in
/-- If a rational polynomial is eventually nonpositive along the integers, its
leading coefficient is nonpositive. -/
theorem leadingCoeff_nonpos_of_eventually_nonpos (P : Polynomial ℚ)
    (h : ∀ᶠ n : ℤ in atTop, P.eval (n : ℚ) ≤ 0) :
    P.leadingCoeff ≤ 0 := by
  by_contra hlt
  rw [not_le] at hlt
  rcases le_or_gt P.degree 0 with hd | hd
  · obtain ⟨n, hn⟩ := h.exists
    have hconst : P.eval (n : ℚ) = P.leadingCoeff := by
      conv_lhs => rw [eq_C_of_degree_le_zero hd]
      conv_rhs => rw [eq_C_of_degree_le_zero hd]
      rw [eval_C, leadingCoeff_C]
    rw [hconst] at hn
    exact absurd hn (not_le.mpr hlt)
  · have htt : Tendsto (fun x => eval x P) atTop atTop :=
      tendsto_atTop_of_leadingCoeff_nonneg P hd hlt.le
    have hcomp : Tendsto (fun n : ℤ => eval (n : ℚ) P) atTop atTop :=
      htt.comp tendsto_intCast_atTop_atTop
    have hev : ∀ᶠ n : ℤ in atTop, 0 < eval (n : ℚ) P := hcomp.eventually_gt_atTop 0
    obtain ⟨n, hn1, hn2⟩ := (h.and hev).exists
    exact absurd hn1 (not_le.mpr hn2)

open Polynomial Filter in
/-- If `0 ≤ P` and `P ≤ Q` eventually along the integers, then `deg P ≤ deg Q`. -/
theorem degree_le_of_eventually_le (P Q : Polynomial ℚ) (h0 : ∀ᶠ n : ℤ in atTop, 0 ≤ P.eval (n : ℚ))
    (hle : ∀ᶠ n : ℤ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) : P.degree ≤ Q.degree := by
  by_contra hdeg
  rw [not_le] at hdeg
  have hDlead : (P - Q).leadingCoeff = P.leadingCoeff := leadingCoeff_sub_of_degree_lt hdeg
  have hPne : P ≠ 0 := by
    intro hP0
    rw [hP0, degree_zero] at hdeg
    exact absurd hdeg (by simp)
  have hDle : ∀ᶠ n : ℤ in atTop, (P - Q).eval (n : ℚ) ≤ 0 := by
    filter_upwards [hle] with n hn
    rw [eval_sub]; linarith
  have h1 : P.leadingCoeff ≤ 0 := by
    rw [← hDlead]; exact leadingCoeff_nonpos_of_eventually_nonpos (P - Q) hDle
  have h2 : 0 ≤ P.leadingCoeff := leadingCoeff_nonneg_of_eventually_nonneg P h0
  have : P.leadingCoeff = 0 := le_antisymm h1 h2
  rw [leadingCoeff_eq_zero] at this
  exact hPne this

open Polynomial Filter in
/-- If `f : ℤ → ℤ` is an eventually nonnegative numerical polynomial with `f n ≤ Q(n)`
for `n ≫ 0`, where `Q ∈ ℚ[T]` has `deg Q < d - 1`, then `f` agrees for large `n` with a
polynomial `P ∈ ℚ[T]` of degree `< d - 1`. -/
theorem isNumericalPolynomial_degree_lt_of_le (f : ℤ → ℤ) (hf : IsNumericalPolynomial f)
    (hf_nonneg : ∀ᶠ n : ℤ in Filter.atTop, 0 ≤ f n) (Q : Polynomial ℚ)
    (hQ : Q.degree < ((d - 1 : ℕ) : WithBot ℕ))
    (hle : ∀ᶠ n : ℤ in Filter.atTop, (f n : ℚ) ≤ Q.eval (n : ℚ)) :
    ∃ (P : Polynomial ℚ) (N : ℕ),
      P.degree < ((d - 1 : ℕ) : WithBot ℕ) ∧ ∀ n : ℕ, N ≤ n → (f n : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨r, a, ha⟩ := hf
  set P : Polynomial ℚ := ∑ i : Fin (r + 1), C (a i : ℚ) * binomialPoly ↑i with hP
  have hPeval : ∀ᶠ n : ℤ in atTop, (f n : ℚ) = P.eval (n : ℚ) := by
    filter_upwards [ha] with n hn
    rw [hn, hP, eval_finsetSum]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [eval_mul, eval_C, binomialPoly_eval, zsmul_eq_mul]
    push_cast
    rw [mul_comm]
    congr 1
    simpa using Ring.map_choose (Int.castRingHom ℚ) n i
  have h0P : ∀ᶠ n : ℤ in atTop, 0 ≤ P.eval (n : ℚ) := by
    filter_upwards [hf_nonneg, hPeval] with n hnn heq
    rw [← heq]; exact_mod_cast hnn
  have hPQ : ∀ᶠ n : ℤ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ) := by
    filter_upwards [hle, hPeval] with n hn heq
    rw [← heq]; exact hn
  have hdegPQ : P.degree ≤ Q.degree := degree_le_of_eventually_le P Q h0P hPQ
  rw [eventually_atTop] at hPeval
  obtain ⟨N₀, hN₀⟩ := hPeval
  refine ⟨P, N₀.toNat, lt_of_le_of_lt hdegPQ hQ, fun n hn => ?_⟩
  have hcast : N₀ ≤ (n : ℤ) := by
    calc
      N₀ ≤ (N₀.toNat : ℤ) := Int.self_le_toNat N₀
      _ ≤ (n : ℤ) := by exact_mod_cast hn
  exact hN₀ n hcast

end Stacks.HilbertFunction.PolynomialQuotient
