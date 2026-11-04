module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.ChartGluing

/-!
# The global functions divisible by the exceptional divisor on both charts

Let `A` be a commutative ring with an algebra map to a commutative ring `K`, let `x y : A` and
let `t s : K` satisfy `t * s = 1` and `x * t = y` (images in `K`), so that
`B = Algebra.adjoin A {t}` and `C = Algebra.adjoin A {s}` are the two standard affine blowup
charts `A[𝔪/x]`, `A[𝔪/y]` read inside `K`, as in the sibling files
`CartierDescent.ChartSubalgebra` and `CartierDescent.ChartGluing`.

This file isolates the ideal of `A` cut out by divisibility by `x ^ d` on the first chart and by
`y ^ d` on the second — the global sections of `𝒪_X(-dE)` read inside `A` — and records the two
facts about it that the colength drop of [Stacks, Tag 0AGT] needs: it contains `I` whenever
`I·B` and `I·C` are divisible, and it is a proper ideal as soon as `x ^ d` is not invertible on
the first chart. The gluing lemma of the sibling file is restated with its glued element placed
in that ideal.

## Main definitions

* `Stacks.ResolutionOfSurfaces.CartierDescent.chartDivisibleIdeal` — the elements of `A` whose
  image in `K` is `w ^ d` times an element of a subalgebra.
* `Stacks.ResolutionOfSurfaces.CartierDescent.gluedIdeal` — the intersection of the two, for the
  two charts.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.mem_chartDivisibleIdeal_iff` — membership.
* `Stacks.ResolutionOfSurfaces.CartierDescent.le_chartDivisibleIdeal` — the ideal contains `I`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.chartDivisibleIdeal_ne_top` — it is proper.
* `Stacks.ResolutionOfSurfaces.CartierDescent.le_gluedIdeal`,
  `Stacks.ResolutionOfSurfaces.CartierDescent.gluedIdeal_ne_top`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.exists_mem_gluedIdeal_sub_mem` — the gluing lemma
  with the glued element exhibited in `gluedIdeal`.

## Implementation notes

`chartDivisibleIdeal w d S` is defined as the preimage under `A →ₗ[A] K` of the image of the
subalgebra under multiplication by `w ^ d`, which makes it an ideal of `A` with no hand-built
`Submodule` structure; `mem_chartDivisibleIdeal_iff` turns that into an existential statement.

Properness is where the dimension of the surface enters downstream: `x ^ d` fails to be
invertible on `A[𝔪/x]` exactly because that chart modulo `x` is a polynomial ring over the
residue field, which is the content of the sibling file `CartierDescent.ChartFibre`. Nothing of
that is needed here, so the statement takes the non-invertibility as a hypothesis.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public section

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

variable {A K : Type u} [CommRing A] [CommRing K] [Algebra A K]

/-- The ideal of elements of `A` whose image in `K` is `w ^ d` times an element of the
subalgebra `S`: the global sections of the `d`-th power of a divisor cut out by `w` on the
chart `S`, read inside `A`. -/
public def chartDivisibleIdeal (w : K) (d : ℕ) (S : Subalgebra A K) : Ideal A :=
  Submodule.comap (Algebra.linearMap A K)
    (Submodule.map (LinearMap.mulLeft A (w ^ d)) (Subalgebra.toSubmodule S))

/-- Membership in `chartDivisibleIdeal`. -/
public theorem mem_chartDivisibleIdeal_iff (w : K) (d : ℕ) (S : Subalgebra A K) (a : A) :
    a ∈ chartDivisibleIdeal w d S ↔ ∃ v ∈ S, algebraMap A K a = w ^ d * v := by
  constructor
  · rintro ha
    obtain ⟨v, hv, hva⟩ := (Submodule.mem_comap.1 ha)
    exact ⟨v, (Subalgebra.mem_toSubmodule _).1 hv, hva.symm⟩
  · rintro ⟨v, hv, hav⟩
    exact Submodule.mem_comap.2 ⟨v, (Subalgebra.mem_toSubmodule _).2 hv, hav.symm⟩

/-- **The divisibility ideal contains `I`** as soon as the extended ideal `I·S` is divisible by
`w ^ d` on the chart `S`: the image of `a ∈ I` is the generator `a * 1` of `I·S`. -/
public theorem le_chartDivisibleIdeal (I : Ideal A) (w : K) (d : ℕ) (S : Subalgebra A K)
    (h : ∀ z ∈ chartIdealSpan I S, ∃ v ∈ S, z = w ^ d * v) :
    I ≤ chartDivisibleIdeal w d S := by
  intro a ha
  rw [mem_chartDivisibleIdeal_iff]
  refine h _ ?_
  have hmem := algebraMap_mul_mem_chartIdealSpan (I := I) (S := S) ha (one_mem S)
  simpa using hmem

/-- **The divisibility ideal is proper** when `w ^ d` is not a factor of `1` on the chart. -/
public theorem chartDivisibleIdeal_ne_top (w : K) (d : ℕ) (S : Subalgebra A K)
    (h : ¬ ∃ v ∈ S, (1 : K) = w ^ d * v) : chartDivisibleIdeal w d S ≠ ⊤ := by
  intro htop
  refine h ?_
  have h1 : (1 : A) ∈ chartDivisibleIdeal w d S := htop ▸ Submodule.mem_top
  obtain ⟨v, hv, hav⟩ := (mem_chartDivisibleIdeal_iff w d S 1).1 h1
  exact ⟨v, hv, by simpa using hav⟩

/-- The elements of `A` divisible by `x ^ d` on the first chart and by `y ^ d` on the second:
the global sections of `𝒪_X(-dE)` on the blowup, read inside `A`. -/
public def gluedIdeal (ξ η : K) (d : ℕ) (S T : Subalgebra A K) : Ideal A :=
  chartDivisibleIdeal ξ d S ⊓ chartDivisibleIdeal η d T

/-- Membership in `gluedIdeal`. -/
public theorem mem_gluedIdeal_iff (ξ η : K) (d : ℕ) (S T : Subalgebra A K) (a : A) :
    a ∈ gluedIdeal ξ η d S T ↔
      (∃ v ∈ S, algebraMap A K a = ξ ^ d * v) ∧ (∃ v ∈ T, algebraMap A K a = η ^ d * v) := by
  rw [gluedIdeal, Submodule.mem_inf, mem_chartDivisibleIdeal_iff, mem_chartDivisibleIdeal_iff]

/-- **The glued ideal contains `I`** when the extended ideals on both charts are divisible. -/
public theorem le_gluedIdeal (I : Ideal A) (ξ η : K) (d : ℕ) (S T : Subalgebra A K)
    (hS : ∀ z ∈ chartIdealSpan I S, ∃ v ∈ S, z = ξ ^ d * v)
    (hT : ∀ z ∈ chartIdealSpan I T, ∃ v ∈ T, z = η ^ d * v) :
    I ≤ gluedIdeal ξ η d S T :=
  le_inf (le_chartDivisibleIdeal I ξ d S hS) (le_chartDivisibleIdeal I η d T hT)

/-- **The glued ideal is proper** when `ξ ^ d` is not a factor of `1` on the first chart. -/
public theorem gluedIdeal_ne_top (ξ η : K) (d : ℕ) (S T : Subalgebra A K)
    (h : ¬ ∃ v ∈ S, (1 : K) = ξ ^ d * v) : gluedIdeal ξ η d S T ≠ ⊤ := fun htop =>
  chartDivisibleIdeal_ne_top ξ d S h (top_le_iff.1 (htop.ge.trans inf_le_left))

/-- **The gluing lemma, with the glued element placed in `gluedIdeal`.** A pair of sections
divisible by `x ^ d` on the first chart and by `y ^ d` on the second which agree modulo `I` on
the overlap comes from an element of `A` lying in the glued ideal. -/
public theorem exists_mem_gluedIdeal_sub_mem [IsDomain K]
    (hinj : Function.Injective (algebraMap A K))
    {x y : A} {t s : K} (hts : t * s = 1) (hxt : algebraMap A K x * t = algebraMap A K y)
    (hx : x ≠ 0)
    (hreg : ∀ a : A, a * y ∈ Ideal.span ({x} : Set A) → a ∈ Ideal.span ({x} : Set A))
    (I : Ideal A) (d : ℕ) (β γ : K)
    (hβ : β ∈ Algebra.adjoin A ({t} : Set K)) (hγ : γ ∈ Algebra.adjoin A ({s} : Set K))
    (hIB : ∀ z ∈ chartIdealSpan I (Algebra.adjoin A ({t} : Set K)),
      ∃ β' ∈ Algebra.adjoin A ({t} : Set K), z = algebraMap A K x ^ d * β')
    (hIC : ∀ z ∈ chartIdealSpan I (Algebra.adjoin A ({s} : Set K)),
      ∃ γ' ∈ Algebra.adjoin A ({s} : Set K), z = algebraMap A K y ^ d * γ')
    (hbc : algebraMap A K x ^ d * β - algebraMap A K y ^ d * γ ∈
      chartIdealSpan I (Algebra.adjoin A ({t, s} : Set K))) :
    ∃ a ∈ gluedIdeal (algebraMap A K x) (algebraMap A K y) d
        (Algebra.adjoin A ({t} : Set K)) (Algebra.adjoin A ({s} : Set K)),
      algebraMap A K a - algebraMap A K x ^ d * β ∈
          chartIdealSpan I (Algebra.adjoin A ({t} : Set K)) ∧
        algebraMap A K a - algebraMap A K y ^ d * γ ∈
          chartIdealSpan I (Algebra.adjoin A ({s} : Set K)) := by
  obtain ⟨a, hb, hc, hdx, hdy⟩ :=
    exists_algebraMap_sub_mem_and_mem_smul hinj hts hxt hx hreg I d β γ hβ hγ hIB hIC hbc
  exact ⟨a, (mem_gluedIdeal_iff _ _ _ _ _ _).2 ⟨hdx, hdy⟩, hb, hc⟩

end Stacks.ResolutionOfSurfaces.CartierDescent

end
