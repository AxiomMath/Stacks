module

public import StacksFrontier.AlgebraicGeometry.ProjShared.RelevantCover

/-!
# The locus on `Proj 𝒜` cut out by ratios of homogeneous elements of degree difference `d`

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring and let `d` be a natural number. Tag 01MU identifies
the largest open of `Proj 𝒜` on which every twist `𝒪(dn)` is invertible and every
multiplication map `𝒪(dn) ⊗ 𝒪(dm) → 𝒪(dn + dm)` is an isomorphism with the open subset

`W_d = ⋃ D₊(f g)`,  `f`, `g` homogeneous,  `deg f = deg g + d`,

the point being that on `D₊(fg)` the ratio `f/g = f²/(fg)` is a degree-`d` unit of the
localization and its powers generate every `𝒪(dn)`. This file is about the right-hand side only:
it defines `W_d` and proves the lattice facts about it that do not mention the twisting sheaves,
so that a proof of the Tag 01MU identity only has to supply the sheaf-theoretic half.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjShared.ratioLocus`: the open `W_d`.

## Main results

* `Stacks.AlgebraicGeometry.ProjShared.mem_ratioLocus_iff`: the pointwise description.
* `Stacks.AlgebraicGeometry.ProjShared.ratioLocus_zero`: `W_0 = Proj 𝒜`.
* `Stacks.AlgebraicGeometry.ProjShared.basicOpen_mul_le_ratioLocus`: the defining inclusion
  `D₊(fg) ⊆ W_d` for `deg f = deg g + d`.
* `Stacks.AlgebraicGeometry.ProjShared.basicOpen_le_basicOpen_of_pow_eq_mul_pow` and
  `Stacks.AlgebraicGeometry.ProjShared.basicOpen_le_ratioLocus_of_pow_eq_mul_pow`: the converse
  inclusion of Tag 01MU, reduced to the algebraic relation `g^N = a f^M` that its proof
  produces.
* `Stacks.AlgebraicGeometry.ProjShared.basicOpen_le_ratioLocus`: `D₊(h) ⊆ W_d` for `h`
  homogeneous of a degree dividing `d`.
* `Stacks.AlgebraicGeometry.ProjShared.ratioLocus_mono_dvd`: `W_d ⊆ W_{d'}` when `d ∣ d'`.
* `Stacks.AlgebraicGeometry.ProjShared.ratioLocus_eq_top_of_iSup_basicOpen_eq_top`: if the
  standard opens of the elements of `𝒜 d` already cover, then `W_d = Proj 𝒜`.
* `Stacks.AlgebraicGeometry.ProjShared.ratioLocus_eq_top_of_adjoin_degree_one`: if `A` is
  generated over `𝒜 0` by `𝒜 1`, then `W_d = Proj 𝒜` for every `d`.

## Implementation notes

The witnesses for `basicOpen_le_ratioLocus` are powers of a single element. For `h ∈ 𝒜 n` and
`d = n k`, taking
`g = h` of degree `e = n` and `f = h^{1+k}` of degree `n(1+k) = e + d` gives
`f g = h^{2+k}`, whose standard open is `D₊(h)` because the exponent is positive; no case
distinction on `k` is needed, so the lemma also covers `d = 0`. Monotonicity in `d` along
divisibility replaces a pair `(f, g)` by `(f^k, g^k)`, which multiplies both the common degree
and the difference by `k`; the degenerate factor `k = 0` is handled by `ratioLocus_zero`, which
is witnessed by `f = g = 1`.

The last result is the form in which the identity is used downstream: a graded ring generated in
degree one has all of `Proj 𝒜` as its invertible locus, for every `d`, which is why `𝒪(n)` is
invertible on such a `Proj`. It is deduced from Mathlib's
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'`, so the hypothesis is the algebra-generation one
and not a spanning condition on an ideal.

The grading lives in a `SetLike` type `σ : Type w` independent of `A : Type u`, as in Mathlib's
`Proj` and in the Stacks source; nothing here assumes `𝒜` is a family of submodules or that `A`
is an algebra over a field.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
-/

@[expose] public section

open AlgebraicGeometry HomogeneousIdeal TopologicalSpace

namespace Stacks.AlgebraicGeometry.ProjShared

universe u w

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The union of the standard opens `D₊(f g)` for homogeneous `f`, `g` with
`deg f = deg g + d`. This is the open subset appearing as part (2) of Tag 01MU. -/
public def ratioLocus (d : ℕ) : (Proj 𝒜).Opens :=
  ⨆ (e : ℕ) (f : 𝒜 (e + d)) (g : 𝒜 e), Proj.basicOpen 𝒜 ((f : A) * (g : A))

/-- A point lies in the locus exactly when some pair of homogeneous elements `f`, `g` with
`deg f = deg g + d` both lie outside its homogeneous prime. -/
public theorem mem_ratioLocus_iff (d : ℕ) (x : Proj 𝒜) :
    x ∈ ratioLocus 𝒜 d ↔ ∃ (e : ℕ) (f g : A), f ∈ 𝒜 (e + d) ∧ g ∈ 𝒜 e ∧
      f ∉ x.asHomogeneousIdeal ∧ g ∉ x.asHomogeneousIdeal := by
  simp only [ratioLocus, TopologicalSpace.Opens.mem_iSup, Proj.basicOpen_mul,
    TopologicalSpace.Opens.mem_inf, Proj.mem_basicOpen, Subtype.exists]
  exact ⟨fun ⟨e, f, hf, g, hg, hfx, hgx⟩ => ⟨e, f, g, hf, hg, hfx, hgx⟩,
    fun ⟨e, f, g, hf, hg, hfx, hgx⟩ => ⟨e, f, hf, g, hg, hfx, hgx⟩⟩

/-- For `d = 0` the locus is everything: take `f = g = 1`. -/
@[simp]
public theorem ratioLocus_zero : ratioLocus 𝒜 0 = ⊤ := by
  refine top_le_iff.mp fun x _ => (mem_ratioLocus_iff 𝒜 0 x).mpr
    ⟨0, 1, 1, by simpa using SetLike.one_mem_graded 𝒜, SetLike.one_mem_graded 𝒜, ?_, ?_⟩
  all_goals exact fun hmem => x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hmem)

/-- A pair `(f, g)` of homogeneous elements with `deg f = deg g + d` puts its standard open
inside the locus. This is the defining inclusion, in the form in which it is applied. -/
public theorem basicOpen_mul_le_ratioLocus {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 (e + d))
    (hg : g ∈ 𝒜 e) : Proj.basicOpen 𝒜 (f * g) ≤ ratioLocus 𝒜 d := by
  intro x hx
  rw [Proj.basicOpen_mul] at hx
  exact (mem_ratioLocus_iff 𝒜 d x).mpr ⟨e, f, g, hf, hg, hx.1, hx.2⟩

/-- If a power of `g` is a multiple of a positive power of `f`, then `g` vanishes wherever `f`
does. This is the step by which Tag 01MU's proof passes from `x ∈ D₊(g)` to `x ∈ D₊(f)`, after
the relation `g^{d + e + deg g} = a f^{deg g}` has been produced. -/
public theorem basicOpen_le_basicOpen_of_pow_eq_mul_pow {f g a : A} {M N : ℕ} (hM : 0 < M)
    (h : g ^ N = a * f ^ M) : Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f := by
  intro x hx
  rw [Proj.mem_basicOpen] at hx ⊢
  exact fun hf => hx (x.isPrime.mem_of_pow_mem N
    (h ▸ Ideal.mul_mem_left _ a (Ideal.pow_mem_of_mem _ hf M hM)))

/-- Tag 01MU's converse inclusion, with the sheaf-theoretic input reduced to the algebraic
relation it produces: homogeneous `f`, `g` with `deg f = deg g + d` and a relation
`g^N = a f^M` with `M > 0` put `D₊(g)` inside the locus. -/
public theorem basicOpen_le_ratioLocus_of_pow_eq_mul_pow {d e : ℕ} {f g a : A} {M N : ℕ}
    (hM : 0 < M) (hrel : g ^ N = a * f ^ M) (hf : f ∈ 𝒜 (e + d)) (hg : g ∈ 𝒜 e) :
    Proj.basicOpen 𝒜 g ≤ ratioLocus 𝒜 d := by
  refine le_trans ?_ (basicOpen_mul_le_ratioLocus 𝒜 hf hg)
  rw [Proj.basicOpen_mul]
  exact le_inf (basicOpen_le_basicOpen_of_pow_eq_mul_pow 𝒜 hM hrel) le_rfl

/-- A `k`-th power of a homogeneous element of degree `n` is homogeneous of any degree `m`
equal to `k * n`. -/
private theorem pow_mem_graded_of_eq {n m : ℕ} {h : A} (hh : h ∈ 𝒜 n) (k : ℕ) (hm : k * n = m) :
    h ^ k ∈ 𝒜 m :=
  hm ▸ SetLike.pow_mem_graded k hh

/-- The standard open of a homogeneous element whose degree divides `d` is contained in
the locus: its powers supply the pair `(f, g)`. -/
public theorem basicOpen_le_ratioLocus {n d : ℕ} (hnd : n ∣ d)
    {h : A} (hh : h ∈ 𝒜 n) : Proj.basicOpen 𝒜 h ≤ ratioLocus 𝒜 d := by
  obtain ⟨k, rfl⟩ := hnd
  exact fun x hx => (mem_ratioLocus_iff 𝒜 (n * k) x).mpr
    ⟨n, h ^ (1 + k), h, pow_mem_graded_of_eq 𝒜 hh (1 + k) (by ring), hh,
      fun hmem => hx (x.isPrime.mem_of_pow_mem (1 + k) hmem), hx⟩

/-- The locus grows along divisibility of `d`: replacing `(f, g)` by `(f^k, g^k)` multiplies
both the common degree and the degree difference by `k`. -/
public theorem ratioLocus_mono_dvd {d d' : ℕ} (hdd : d ∣ d') :
    ratioLocus 𝒜 d ≤ ratioLocus 𝒜 d' := by
  obtain ⟨k, rfl⟩ := hdd
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  intro x hx
  obtain ⟨e, f, g, hf, hg, hfx, hgx⟩ := (mem_ratioLocus_iff 𝒜 d x).mp hx
  refine (mem_ratioLocus_iff 𝒜 (d * k) x).mpr ⟨k * e, f ^ k, g ^ k, ?_, ?_, ?_, ?_⟩
  · exact pow_mem_graded_of_eq 𝒜 hf k (by ring)
  · exact pow_mem_graded_of_eq 𝒜 hg k rfl
  · exact fun hmem => hfx (x.isPrime.mem_of_pow_mem k hmem)
  · exact fun hmem => hgx (x.isPrime.mem_of_pow_mem k hmem)

/-- If the standard opens of the homogeneous elements of degree `d` already cover `Proj 𝒜`, the
locus for `d` is everything. -/
public theorem ratioLocus_eq_top_of_iSup_basicOpen_eq_top {d : ℕ}
    (h : (⨆ f : 𝒜 d, Proj.basicOpen 𝒜 (f : A)) = ⊤) : ratioLocus 𝒜 d = ⊤ :=
  top_le_iff.mp <| h.ge.trans <|
    iSup_le fun f => basicOpen_le_ratioLocus 𝒜 dvd_rfl f.2

/-- A graded ring generated in degree one over its degree-zero part has all of `Proj 𝒜` as its
locus, for every `d`. -/
public theorem ratioLocus_eq_top_of_adjoin_degree_one
    (hgen : Algebra.adjoin (𝒜 0) (Set.range fun f : 𝒜 1 => (f : A)) = ⊤) (d : ℕ) :
    ratioLocus 𝒜 d = ⊤ :=
  top_le_iff.mp <|
    (Proj.iSup_basicOpen_eq_top' 𝒜 (fun f : 𝒜 1 => (f : A)) (fun f => ⟨1, f.2⟩) hgen).ge.trans <|
      iSup_le fun f => basicOpen_le_ratioLocus 𝒜 (one_dvd d) f.2

end Stacks.AlgebraicGeometry.ProjShared

end
