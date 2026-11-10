module

public import StacksFrontier.RingTheory.QuasiFinite.AffineSpaceDimension
import StacksFrontier.RingTheory.RelativeDimension.QuasiFinite
public import StacksFrontier.RingTheory.RelativeDimension.BaseChange
public import StacksFrontier.RingTheory.Spectrum.Prime.SpectralComap
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import StacksFrontier.RingTheory.RelativeDimension.QuasiFiniteAffineSpace

@[expose] public section

/-!
# Upper semicontinuity of the relative dimension of a finite type ring map

Let `R → S` be of finite type and let `n : ℕ`.  This file proves Stacks 00QH: the set of primes
`𝔮` of `S` at which the fibre of `Spec S → Spec R` has dimension at most `n`,

`{𝔮 ∈ Spec S | dim_𝔮(S/R) ≤ n}`,

is open in `Spec S`.

Fix `𝔮` in the set.  Its relative dimension is a natural number
`m ≤ n`: it is not `-∞` because the fibre through `𝔮` contains `𝔮`, and not `+∞` because it is
at most `n`.  By Stacks 00QE there is a `g ∉ 𝔮` such that `S_g` is quasi-finite over the
polynomial algebra `R[t_1, …, t_m]`.  The basic open `D(g)` is the required neighbourhood:
for `𝔮' ∈ D(g)` lying over `𝔭'`, the relative dimension at `𝔮'` is the dimension at `𝔮'` of
the fibre of `Spec S_g → Spec R` over `𝔭'`, because `Spec S_g → Spec S` is an open embedding
carrying that fibre onto a neighbourhood of `𝔮'` in the fibre of `Spec S → Spec R`; that
dimension at a point is at most the dimension of the whole fibre, which is
`dim(κ(𝔭') ⊗_R S_g)`; and `κ(𝔭') ⊗_R S_g` is quasi-finite over `κ(𝔭')[t_1, …, t_m]`, being the
base change of `R[t_1, …, t_m] → S_g` along `R → κ(𝔭')`, so Stacks 00QG bounds its dimension
by `m ≤ n`.

## Main results

* `Stacks.RelativeDimension.Semicontinuity.solution`: the statement of Stacks 00QH.

## Implementation notes

*The base change of the fibre.*  The identification of `κ(𝔭) ⊗_R T` with
`κ(𝔭)[t_i] ⊗_{R[t_i]} T`, for `T` an `R[t_i]`-algebra, is only needed as a ring isomorphism,
since it is used to compare Krull dimensions; it is assembled from
`Algebra.TensorProduct.cancelBaseChange` and `MvPolynomial.algebraTensorAlgEquiv`, the latter
upgraded to an `R[t_i]`-algebra equivalence by `AlgEquiv.ofRingEquiv`.

*Stacks 00QE.*  It is `quasiFinite_over_polynomial_of_relativeDimension` in
`StacksFrontier.RingTheory.RelativeDimension.QuasiFinite`.  Its relative dimension is read at a
point of `Spec (S ⊗_R κ(𝔭))` rather than at a prime of `S`, so it is transported along
`PrimeSpectrum.preimageHomeomorphFiber` by `relativeDimensionAt_eq_of_fiber` and
`comap_fiberMap_preimageHomeomorphFiber`; the result at a prime of `S` is
`exists_quasiFinite_mvPolynomial_away`, in
`StacksFrontier.RingTheory.RelativeDimension.QuasiFiniteAffineSpace`.

## References

* [StacksProject 00QH](https://stacks.math.columbia.edu/tag/00QH)
* [StacksProject 00QE](https://stacks.math.columbia.edu/tag/00QE)
* [StacksProject 00QG](https://stacks.math.columbia.edu/tag/00QG)
* [StacksProject 0055](https://stacks.math.columbia.edu/tag/0055)
-/

@[expose] public section

namespace Stacks.RelativeDimension.Semicontinuity

open scoped TensorProduct

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ### The dimension of a space at a point -/

/-- An element of `WithBot ℕ∞` other than `-∞` is nonnegative. -/
theorem zero_le_of_ne_bot {x : WithBot ℕ∞} (h : x ≠ ⊥) : 0 ≤ x := by
  cases x with
  | bot => simp at h
  | coe a => simp

/-- An element of `WithBot ℕ∞` which is nonnegative and at most a natural number `n` is a
natural number `m ≤ n`. -/
theorem exists_nat_eq_of_zero_le_of_le_nat {x : WithBot ℕ∞} {n : ℕ} (h₀ : 0 ≤ x)
    (h : x ≤ (n : WithBot ℕ∞)) : ∃ m : ℕ, x = (m : WithBot ℕ∞) ∧ m ≤ n := by
  cases x with
  | bot => simp at h₀
  | coe a =>
    cases a with
    | top =>
      rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) by norm_cast] at h
      simp only [WithBot.coe_le_coe, top_le_iff, ENat.natCast_ne_top] at h
    | coe b => exact ⟨b, by norm_cast, mod_cast h⟩

/-! ### The dimension of a fibre of a quasi-finite cover of affine space -/

/-- A fibre of an algebra which is quasi-finite over a polynomial algebra `R[t_i ; i ∈ σ]` in
finitely many variables has Krull dimension at most `#σ`.

The fibre `κ(𝔭) ⊗_R T` is `κ(𝔭)[t_i] ⊗_{R[t_i]} T`, the base change of `R[t_i] → T` along
`R[t_i] → κ(𝔭)[t_i]`, hence quasi-finite over the polynomial algebra `κ(𝔭)[t_i]` over the field
`κ(𝔭)`; Stacks 00QG then bounds its dimension by `#σ`. -/
private theorem ringKrullDim_fiber_le_natCard {R T σ : Type*} [CommRing R] [CommRing T]
    [Algebra R T] [Finite σ] [Algebra (MvPolynomial σ R) T]
    [IsScalarTower R (MvPolynomial σ R) T] [Algebra.QuasiFinite (MvPolynomial σ R) T]
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    ringKrullDim (𝔭.Fiber T) ≤ (Nat.card σ : WithBot ℕ∞) := by
  have hmap : ∀ x : MvPolynomial σ R,
      (MvPolynomial.algebraTensorAlgEquiv R 𝔭.ResidueField)
          ((Algebra.TensorProduct.comm R (MvPolynomial σ R) 𝔭.ResidueField)
            (algebraMap (MvPolynomial σ R) (MvPolynomial σ R ⊗[R] 𝔭.ResidueField) x))
        = algebraMap (MvPolynomial σ R) (MvPolynomial σ 𝔭.ResidueField) x := fun x ↦ by
    simp [Algebra.TensorProduct.algebraMap_apply]
  let eP : (MvPolynomial σ R ⊗[R] 𝔭.ResidueField) ≃ₐ[MvPolynomial σ R]
      MvPolynomial σ 𝔭.ResidueField :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm R (MvPolynomial σ R) 𝔭.ResidueField).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv R 𝔭.ResidueField).toRingEquiv) hmap
  have e : 𝔭.Fiber T ≃+* (MvPolynomial σ 𝔭.ResidueField) ⊗[MvPolynomial σ R] T :=
    (Algebra.TensorProduct.comm R 𝔭.ResidueField T).toRingEquiv.trans
      (((Algebra.TensorProduct.cancelBaseChange R (MvPolynomial σ R) (MvPolynomial σ R) T
            𝔭.ResidueField).symm.toRingEquiv).trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := MvPolynomial σ R) (A₁ := T))
            eP).toRingEquiv.trans
          (Algebra.TensorProduct.comm (MvPolynomial σ R) T
            (MvPolynomial σ 𝔭.ResidueField)).toRingEquiv))
  exact (ringKrullDim_eq_of_ringEquiv e).trans_le
    (ringKrullDim_le_natCard_of_quasiFinite_mvPolynomial 𝔭.ResidueField)

/-! ### Locality of the relative dimension -/

/-- The relative dimension at a prime `𝔮` of `S` outside `V(g)` is at most the dimension of the
whole fibre of `Spec S_g → Spec R` through `𝔮`.

`Spec S_g → Spec S` is an open embedding onto `D(g)`, so it carries the fibre of
`Spec S_g → Spec R` over `𝔭 = R ∩ 𝔮` open-embeddingly into the fibre of `Spec S → Spec R` over
`𝔭`, taking the point above `𝔮` to `𝔮`; the dimension at a point is unchanged by an open
embedding and is at most the dimension of the whole space. -/
public theorem relativeDimensionAt_le_ringKrullDim_fiber {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (g : S) (Sg : Type*) [CommRing Sg] [Algebra S Sg]
    [IsLocalization.Away g Sg] [Algebra R Sg] [IsScalarTower R S Sg] (𝔮 : PrimeSpectrum S)
    (𝔭 : PrimeSpectrum R) (h𝔭 : PrimeSpectrum.comap (algebraMap R S) 𝔮 = 𝔭)
    (hg : 𝔮 ∈ PrimeSpectrum.basicOpen g) :
    Algebra.relativeDimensionAt R 𝔮.asIdeal ≤ ringKrullDim (𝔭.asIdeal.Fiber Sg) := by
  subst h𝔭
  obtain ⟨qg, hqg⟩ : 𝔮 ∈ Set.range (PrimeSpectrum.comap (algebraMap S Sg)) := by
    rwa [PrimeSpectrum.localization_away_comap_range Sg g]
  have hcomp : PrimeSpectrum.comap (algebraMap R Sg)
      = PrimeSpectrum.comap (algebraMap R S) ∘ PrimeSpectrum.comap (algebraMap S Sg) := by
    rw [IsScalarTower.algebraMap_eq R S Sg, ← PrimeSpectrum.comap_comp]
  have hB : PrimeSpectrum.comap (algebraMap R Sg) ⁻¹' {PrimeSpectrum.comap (algebraMap R S) 𝔮}
      = PrimeSpectrum.comap (algebraMap S Sg) ⁻¹'
          (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R S) 𝔮}) := by
    rw [hcomp, Set.preimage_comp]
  have hmem : qg ∈ PrimeSpectrum.comap (algebraMap S Sg) ⁻¹'
      (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        {PrimeSpectrum.comap (algebraMap R S) 𝔮}) := by
    simp only [Set.mem_preimage, hqg, Set.mem_singleton_iff]
  have hpt : (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        {PrimeSpectrum.comap (algebraMap R S) 𝔮}).restrictPreimage
      (PrimeSpectrum.comap (algebraMap S Sg)) ⟨qg, hmem⟩ = ⟨𝔮, rfl⟩ := Subtype.ext hqg
  calc Algebra.relativeDimensionAt R 𝔮.asIdeal
      = topologicalKrullDimAt ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R S) 𝔮})
          ((PrimeSpectrum.comap (algebraMap R S) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R S) 𝔮}).restrictPreimage
              (PrimeSpectrum.comap (algebraMap S Sg)) ⟨qg, hmem⟩) := by
        rw [hpt, Algebra.relativeDimensionAt]
    _ = topologicalKrullDimAt ↥(PrimeSpectrum.comap (algebraMap S Sg) ⁻¹'
          (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R S) 𝔮})) ⟨qg, hmem⟩ :=
        ((PrimeSpectrum.localization_away_isOpenEmbedding Sg g).restrictPreimage
          (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R S) 𝔮})).topologicalKrullDimAt_eq _
    _ ≤ topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap S Sg) ⁻¹'
          (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R S) 𝔮})) :=
        topologicalKrullDimAt_le_topologicalKrullDim _
    _ = ringKrullDim ((PrimeSpectrum.comap (algebraMap R S) 𝔮).asIdeal.Fiber Sg) := by
        rw [← hB, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
        exact IsHomeomorph.topologicalKrullDim_eq _
          (PrimeSpectrum.preimageHomeomorphFiber R Sg
            (PrimeSpectrum.comap (algebraMap R S) 𝔮)).isHomeomorph

/-! ### Stacks 00QH -/

/-- **The fibres of a principal neighbourhood.** Let `R → S` be of finite type and let `𝔮` be a
prime of `S` with `dim_𝔮(S/R) ≤ n`. There is a `g ∈ S`, `g ∉ 𝔮`, such that every fibre of
`Spec(S_g) → Spec(R)` has dimension at most `n`: after inverting `g` the algebra `S_g` is
quasi-finite over `R[t_1, …, t_m]`, `m = dim_𝔮(S/R)` (Lemma 00QE), and the fibres of such an
algebra have dimension at most `m` (Lemma 00QG). -/
public theorem _root_.Algebra.exists_notMem_ringKrullDim_fiber_le {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (𝔮 : Ideal S) [𝔮.IsPrime] {n : ℕ}
    (h𝔮 : Algebra.relativeDimensionAt R 𝔮 ≤ (n : WithBot ℕ∞)) :
    ∃ g ∉ 𝔮, ∀ (p : Ideal R) [p.IsPrime],
      ringKrullDim (p.Fiber (Localization.Away g)) ≤ (n : WithBot ℕ∞) := by
  obtain ⟨m, hm, hmn⟩ := exists_nat_eq_of_zero_le_of_le_nat
    (by rw [Algebra.relativeDimensionAt]; exact topologicalKrullDimAt_nonneg _) h𝔮
  obtain ⟨g, hg, ψ, hqf⟩ := exists_quasiFinite_mvPolynomial_away (R := R) 𝔮 hm
  let _ : Algebra (MvPolynomial (Fin m) R) (Localization.Away g) := ψ.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin m) R) (Localization.Away g) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (ψ.commutes x).symm
  have : Algebra.QuasiFinite (MvPolynomial (Fin m) R) (Localization.Away g) := hqf
  refine ⟨g, hg, fun p _ ↦ (ringKrullDim_fiber_le_natCard (σ := Fin m) p).trans ?_⟩
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  exact_mod_cast hmn

/-- **Stacks 00QH.** Let `R → S` be a finite type ring map and let `n : ℕ`. The set of primes `𝔮`
of `S` at which the fibre of `Spec S → Spec R` has dimension at most `n` is open in `Spec S`. -/
public theorem solution {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (n : ℕ) :
    IsOpen {𝔮 : PrimeSpectrum S |
      Algebra.relativeDimensionAt R 𝔮.asIdeal ≤ (n : WithBot ℕ∞)} := by
  refine isOpen_iff_forall_mem_open.mpr fun 𝔮 h𝔮 ↦ ?_
  obtain ⟨g, hg, hfib⟩ := Algebra.exists_notMem_ringKrullDim_fiber_le (R := R) 𝔮.asIdeal h𝔮
  exact ⟨(PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)), fun 𝔮' h𝔮' ↦
    (relativeDimensionAt_le_ringKrullDim_fiber g (Localization.Away g) 𝔮' _ rfl h𝔮').trans
      (hfib _), (PrimeSpectrum.basicOpen g).isOpen, hg⟩

end Stacks.RelativeDimension.Semicontinuity

end

/-!
# Upper semicontinuity of the relative dimension of a finite type ring map

Let `R → S` be a ring map of finite type and let `n : ℕ`. For a prime `𝔮` of `S` lying over the
prime `𝔭 = R ∩ 𝔮` of `R`, the relative dimension `dim_𝔮(S/R)` is the dimension of the fibre
`Spec (S ⊗_R κ(𝔭))` at the point corresponding to `𝔮` (Stacks 00QD). The set of primes at which
the fibre has dimension at most `n`,

`{𝔮 ∈ Spec S | dim_𝔮(S/R) ≤ n}`,

is open in `Spec S`. Equivalently: every prime `𝔮` with `dim_𝔮(S/R) = n` has an open
neighbourhood `V` in `Spec S` with `dim_{𝔮'}(S/R) ≤ n` for all `𝔮' ∈ V`, so the relative
dimension can only jump up under specialization.

The reason is that relative dimension `n` at `𝔮` is a normal form: after inverting a single
`g ∈ S`, `g ∉ 𝔮`, the algebra `S_g` becomes quasi-finite over the polynomial algebra
`R[t_1, …, t_n]` (Lemma 00QE). On the basic open `D(g)` the fibres of `S_g` are then quasi-finite
covers of affine `n`-space over the residue fields, hence of dimension at most `n` (Lemma 00QG),
and the dimension of a fibre at a point is at most the dimension of the whole fibre.

## Main results

* `Algebra.isOpen_setOf_relativeDimensionAt_le`: Stacks 00QH.

## Implementation notes

*The `∃ V` of the source is replaced by openness of the sublevel set, which is the same
statement.* The source fixes `𝔮` with `dim_𝔮(S/R) = n` and asserts that some open `V ∋ 𝔮` has
`dim_{𝔮'}(S/R) ≤ n` throughout; the remark following the lemma in the source reads it as "the set
of points where the fibre has dimension `≤ n` is open in `Spec(S)`", which is the form stated
here. The two are equivalent, and neither direction loses information. Openness gives the
source's `V`, namely the sublevel set itself, which is the largest admissible one. Conversely, if
`dim_𝔮(S/R) ≤ (n : WithBot ℕ∞)` then `dim_𝔮(S/R) = (m : WithBot ℕ∞)` for some `m ≤ n`: it is not
`⊥`, because the fibre through `𝔮` contains `𝔮` and so is nonempty
(`topologicalKrullDim_eq_bot_iff_isEmpty`), and it is not `⊤` since `⊤ ≤ (n : WithBot ℕ∞)` fails;
the source's lemma at `m` then produces an open `V ∋ 𝔮` inside the sublevel set, so `𝔮` is an
interior point. Stating the open set rather than a neighbourhood of one prime is also the form in
which Lemma 00QI compares it with base change, and it is Mathlib's idiom for semicontinuity of
an integer-valued invariant.

*The bound is a natural number.* `n : ℕ` is coerced into `WithBot ℕ∞`, the value type of
`Algebra.relativeDimensionAt`, as in the source, where `n` is the value of a relative dimension
and the tag's companion Lemma 00QI writes `n ≥ 0`. The statement happens to hold for a bound in
all of `WithBot ℕ∞`, the two extra cases being `⊥`, where the sublevel set is empty by the
nonemptiness of fibres just used, and `⊤`, where it is everything; neither carries content.

*Relative dimension.* `dim_𝔮(S/R)` is `Algebra.relativeDimensionAt R 𝔮` (tag 00QD), the dimension
at `𝔮` of the fibre of `Spec S → Spec R` through `𝔮`, taken there as the subspace
`comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S`, homeomorphic to `Spec (S ⊗_R κ(𝔭))`. The prime `𝔭`
is not an argument: it is `𝔮.under R`, as the source's `𝔭` is.

*Finite type is the source's hypothesis and belongs here.* The source's Definition 00QD defines
`dim_𝔮(S/R)` only for `R → S` of finite type; `Algebra.relativeDimensionAt` drops the hypothesis
from the definition, which does not use it, and leaves it to the lemmas, of which this is one. It
is what makes the fibres of finite type over `κ(𝔭)`, hence finite-dimensional, and it is used
essentially in the source's route through Lemma 00QE (Noether normalization of the fibre) and
Lemma 00QG. It is not decoration in the sense of tag 00QF, where the conclusion turned out to hold
verbatim without it: no proof of the present statement for a general ring map is known, and no
counterexample either.

Faithfulness to [StacksProject 00QH]:

1. No hypothesis is idle. `n` occurs in the conclusion as the bound. `Algebra.FiniteType R S` is
   the source's hypothesis on the ring map, is what makes relative dimension the source's notion
   (Definition 00QD is stated for finite type maps), and is what the source's proof consumes
   through 00QE; the conclusion is a statement about the `R`-algebra structure on `S`, which every
   remaining datum enters.
2. The scalars and base are the source's. The relative dimension is taken over `R` itself: the
   fibre is the fibre of `Spec S → Spec R` over `𝔭 = R ∩ 𝔮` for the given `Algebra R S`, not over
   a localization, a quotient or a base change of `R`, and the topology in which the set is open
   is that of `Spec S`, not of a fibre — inside a single fibre the sublevel sets of the dimension
   at a point are open in any topological space, and the content of the tag is precisely that the
   set is open across fibres.
3. Nothing is left merely to exist. The source's open neighbourhood `V` is pinned as the sublevel
   set `{𝔮 | dim_𝔮(S/R) ≤ n}` itself, the largest set the source's conclusion can name, and the
   relative dimension is the named function `Algebra.relativeDimensionAt R` of `𝔮`, not a
   dimension of some chosen model of the fibre.
4. The instantiation is not degenerate. For `R = k[x] → S = k[x, y]/(xy)` and `n = 0` the set is
   the basic open `D(x)`: the fibre over `𝔭 = (f)` with `f ≠ x` irreducible, and over `𝔭 = (0)`,
   is `κ(𝔭)[y]/(y) = κ(𝔭)`, of dimension `0`, while the fibre over `(x)` is the line `k[y]`, of
   dimension `1` at each of its points. So the set is neither empty nor all of `Spec S` — it
   misses exactly the closed set `V(x)` — and the openness asserted is not the triviality
   `IsOpen ∅` or `IsOpen Set.univ`. With `n = 1` the same example gives `Set.univ`, and the
   quasi-finite case `n = 0`, `R = ℤ → S = ℤ[x]/(x² - 2)`, gives `Set.univ` as well.

## References

* [StacksProject 00QH](https://stacks.math.columbia.edu/tag/00QH)
* [StacksProject 00QD](https://stacks.math.columbia.edu/tag/00QD)
* [StacksProject 00QE](https://stacks.math.columbia.edu/tag/00QE)
* [StacksProject 00QG](https://stacks.math.columbia.edu/tag/00QG)
* [StacksProject 0055](https://stacks.math.columbia.edu/tag/0055)

## Tags

relative dimension, fibre, dimension of fibres, upper semicontinuity, open locus, finite type
ring map
-/

@[expose] public section

namespace Algebra

/-- **Stacks 00QH.** Let `R → S` be a finite type ring map and let `n : ℕ`. The set of primes `𝔮`
of `S` at which the fibre of `Spec S → Spec R` has dimension at most `n`, that is
`dim_𝔮(S/R) ≤ n`, is open in `Spec S`. Equivalently, every prime `𝔮` with `dim_𝔮(S/R) = n` has an
open neighbourhood `V` in `Spec S` such that `dim_{𝔮'}(S/R) ≤ n` for all `𝔮' ∈ V`. -/
@[stacks 00QH "The source's open neighbourhood `V` of a single prime `𝔮` with `dim_𝔮(S/R) = n` is
pinned as the sublevel set `{𝔮 | dim_𝔮(S/R) ≤ n}`, whose openness the remark following the lemma
in the source gives as an equivalent reading of it; `dim_𝔮(S/R)` is `Algebra.relativeDimensionAt R
𝔮` (tag 00QD). See the module docstring."]
public theorem isOpen_setOf_relativeDimensionAt_le {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (n : ℕ) :
    IsOpen {𝔮 : PrimeSpectrum S |
      Algebra.relativeDimensionAt R 𝔮.asIdeal ≤ (n : WithBot ℕ∞)} :=
  Stacks.RelativeDimension.Semicontinuity.solution n

end Algebra

end

/-!
# The locus of relative dimension at most `n` is a quasi-compact open

This file proves Stacks 00QJ: for a ring map `R → S` of finite presentation and `n : ℕ`, the set
`V_n = {𝔮 ∈ Spec S | dim_𝔮(S/R) ≤ n}` is a quasi-compact open subset of `Spec S`.

Openness needs only finite type and is Stacks 00QH. For
quasi-compactness, choose a finite presentation `S = R[x_i]/(f_1, …, f_m)`, let `R₀ ⊆ R` be the
`ℤ`-subalgebra generated by the coefficients of the `f_j` and let `S₀ = R₀[x_i]/(f_1, …, f_m)`,
so that `S = R ⊗_{R₀} S₀`. Since `R₀` is a finite type `ℤ`-algebra it is Noetherian, hence so is
`S₀`, and therefore `Spec S₀` is a Noetherian space and *every* subset of it is quasi-compact —
in particular the corresponding `V_{0, n} ⊆ Spec S₀`, which is open by Stacks 00QH over `R₀`. By
Stacks 00QI relative dimension is unchanged by the base change, so `V_n` is the inverse image of
`V_{0, n}` under `Spec S → Spec S₀`. That map is spectral, so `V_n` is quasi-compact.

## Main results

* `Stacks.RelativeDimension.CompactLocus.solution`: Stacks 00QJ.

## Implementation notes

*Stacks 00QI enters as an equality of loci.* `Algebra.IsPushout.relativeDimensionAt_comap_eq`
states it pointwise, as
`dim_{f(𝔮)}(S₀/R₀) = dim_𝔮(S/R)`; the source states it as the equality of sublevel sets, which is
the form the topological argument consumes, and that form is
`setOf_relativeDimensionAt_le_eq_preimage` here.

*The descent to `R₀`.* It is Mathlib's `Algebra.Presentation.Core`, the `ℤ`-subalgebra of `R`
generated by the coefficients of the relations of a presentation, together with
`Algebra.Presentation.ModelOfHasCoeffs`, the same polynomial ring modulo the same relations read
over that subalgebra; `Algebra.Presentation.tensorModelOfHasCoeffsEquiv` is the source's
`S = R ⊗_{R₀} S₀`. Only the `S₀`-algebra structure on `S` has to be added, and it is added as a
map of `R₀`-algebras: `Algebra.TensorProduct.includeRight` followed by that equivalence. Reading
it over `R₀` rather than as a bare ring map is what makes `IsScalarTower R₀ S₀ S` the map's own
`AlgHom.commutes` and the pushout square `IsBaseChange.of_equiv` applied to the equivalence, so no
tensor product is unfolded and the right factor of `R ⊗_{R₀} S₀` needs no algebra structure of its
own.

*`Spec S → Spec S₀` is spectral* because a quasi-compact open of a spectrum is the complement of
the zero locus of a finite set (`PrimeSpectrum.isCompact_isOpen_iff`) and taking inverse images
replaces that finite set by its image (`PrimeSpectrum.preimage_comap_zeroLocus`). The general
statement `IsSpectralMap (PrimeSpectrum.comap f)` is not in Mathlib, which has it only for
morphisms of schemes (`AlgebraicGeometry.Scheme.Hom.isSpectralMap`); it is proved here as a
private lemma.

*A Noetherian spectrum is all that is used, not a Noetherian ring.* Quasi-compactness of
`V_{0, n}` is `TopologicalSpace.NoetherianSpace.isCompact`, which needs no openness, so the base
change lemma is stated for an `S₀` whose *spectrum* is a Noetherian space (Stacks 005A); over the
Noetherian ring `S₀` of the descent that hypothesis is found by instance search. Openness of
`V_{0, n}` is still used, since a spectral map is only asked to pull back quasi-compact *opens*.

## References

* [StacksProject 00QJ](https://stacks.math.columbia.edu/tag/00QJ)
* [StacksProject 00QH](https://stacks.math.columbia.edu/tag/00QH)
* [StacksProject 00QI](https://stacks.math.columbia.edu/tag/00QI)
* [StacksProject 005A](https://stacks.math.columbia.edu/tag/005A)
-/

@[expose] public section

namespace Stacks.RelativeDimension.CompactLocus

open Algebra TopologicalSpace

section IsPushout

variable (R₀ S₀ R S : Type*) [CommRing R₀] [CommRing S₀] [CommRing R] [CommRing S]
  [Algebra R₀ S₀] [Algebra R₀ R] [Algebra R S] [Algebra S₀ S] [Algebra R₀ S]
  [IsScalarTower R₀ R S] [IsScalarTower R₀ S₀ S] [hp : Algebra.IsPushout R₀ S₀ R S]
  [Algebra.FiniteType R₀ S₀] (n : ℕ)

include hp

/-- **Stacks 00QI as an equality of loci.** If `S = R ⊗_{R₀} S₀`, then `{𝔮 | dim_𝔮(S/R) ≤ n}` is
the inverse image of `{𝔮₀ | dim_𝔮₀(S₀/R₀) ≤ n}` under `Spec S → Spec S₀`. -/
private theorem setOf_relativeDimensionAt_le_eq_preimage :
    {𝔮 : PrimeSpectrum S | relativeDimensionAt R 𝔮.asIdeal ≤ (n : WithBot ℕ∞)} =
      PrimeSpectrum.comap (algebraMap S₀ S) ⁻¹'
        {𝔮₀ : PrimeSpectrum S₀ | relativeDimensionAt R₀ 𝔮₀.asIdeal ≤ (n : WithBot ℕ∞)} := by
  ext 𝔮
  simp only [Set.mem_ofPred_eq, Set.mem_preimage,
    Algebra.IsPushout.relativeDimensionAt_comap_eq R₀ S₀ R S 𝔮]

/-- Quasi-compactness of `V_n` for a base change of a finite type algebra whose spectrum is a
Noetherian space: `V_n` is the inverse image of `V_{0, n} = {𝔮₀ | dim_𝔮₀(S₀/R₀) ≤ n}` under the
spectral map `Spec S → Spec S₀`, and `V_{0, n}` is quasi-compact because *every* subset of
`Spec S₀` is, and open by Stacks 00QH. -/
private theorem isCompact_setOf_relativeDimensionAt_le_of_isPushout
    [NoetherianSpace (PrimeSpectrum S₀)] :
    IsCompact {𝔮 : PrimeSpectrum S |
      relativeDimensionAt R 𝔮.asIdeal ≤ (n : WithBot ℕ∞)} := by
  rw [setOf_relativeDimensionAt_le_eq_preimage R₀ S₀ R S n]
  exact (NoetherianSpace.isCompact _).preimage_of_isOpen (PrimeSpectrum.isSpectralMap_comap _)
    (isOpen_setOf_relativeDimensionAt_le n)

end IsPushout

/-- Quasi-compactness of `V_n` from a presentation of `S` over `R` with finitely many variables and
relations, by descending it to the `ℤ`-subalgebra `R₀ = P.Core` of `R` generated by the
coefficients of its relations: `R₀` is a finite type `ℤ`-algebra, hence Noetherian, and so is the
model `S₀` of the presentation over `R₀`, for which `S = R ⊗_{R₀} S₀`. -/
private theorem isCompact_setOf_relativeDimensionAt_le_of_presentation
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Finite ι] [Finite σ]
    (P : Algebra.Presentation R S ι σ) (n : ℕ) :
    IsCompact {𝔮 : PrimeSpectrum S |
      relativeDimensionAt R 𝔮.asIdeal ≤ (n : WithBot ℕ∞)} := by
  set S₀ := P.ModelOfHasCoeffs P.Core
  set e := P.tensorModelOfHasCoeffsEquiv P.Core
  let g : S₀ →ₐ[P.Core] S :=
    (e.toAlgHom.restrictScalars P.Core).comp Algebra.TensorProduct.includeRight
  let _ : Algebra S₀ S := g.toRingHom.toAlgebra
  have : IsScalarTower P.Core S₀ S := .of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : Algebra.IsPushout P.Core S₀ R S :=
    (Algebra.IsPushout.comm ..).mpr ⟨IsBaseChange.of_equiv e.toLinearEquiv fun _ ↦ rfl⟩
  have : IsNoetherianRing P.Core := Algebra.FiniteType.isNoetherianRing ℤ P.Core
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing P.Core S₀
  exact isCompact_setOf_relativeDimensionAt_le_of_isPushout P.Core S₀ R S n

/-- **Stacks 00QJ.** Let `R → S` be a ring map of finite presentation and let `n : ℕ`. The set of
primes `𝔮` of `S` at which the fibre of `Spec S → Spec R` has dimension at most `n` is a
quasi-compact open subset of `Spec S`. -/
public theorem solution {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (n : ℕ) :
    IsCompact {𝔮 : PrimeSpectrum S |
        Algebra.relativeDimensionAt R 𝔮.asIdeal ≤ (n : WithBot ℕ∞)} ∧
      IsOpen {𝔮 : PrimeSpectrum S |
        Algebra.relativeDimensionAt R 𝔮.asIdeal ≤ (n : WithBot ℕ∞)} :=
  ⟨isCompact_setOf_relativeDimensionAt_le_of_presentation
      (Algebra.Presentation.ofFinitePresentation R S) n,
    Algebra.isOpen_setOf_relativeDimensionAt_le n⟩

end Stacks.RelativeDimension.CompactLocus

end

/-!
# The locus of relative dimension at most `n` of a finitely presented ring map

Let `R → S` be a ring map of finite presentation and let `n : ℕ`. For a prime `𝔮` of `S` lying
over `𝔭 = R ∩ 𝔮`, the relative dimension `dim_𝔮(S/R)` is the dimension of the fibre
`Spec (S ⊗_R κ(𝔭))` at the point corresponding to `𝔮` (Stacks 00QD). The source's

`V_n = {𝔮 ∈ Spec S | dim_𝔮(S/R) ≤ n}`

is then a *quasi-compact* open subset of `Spec S`.

Openness needs only finite type and is Stacks 00QH. Quasi-compactness is where finite
presentation enters, by reduction to a Noetherian base: choose a presentation
`S = R[x_1, …, x_r]/(f_1, …, f_m)`, let `R_0 ⊆ R` be the `ℤ`-subalgebra generated by the
coefficients of the `f_i` and put `S_0 = R_0[x_1, …, x_r]/(f_1, …, f_m)`, so that
`S = R ⊗_{R_0} S_0` and `R_0`, hence `S_0`, is Noetherian. By Stacks 00QI the set `V_n` is the
inverse image of the corresponding `V_{0, n} ⊆ Spec S_0` under `Spec S → Spec S_0`; `V_{0, n}` is
quasi-compact because `Spec S_0` is a Noetherian space, and quasi-compactness is inherited by the
inverse image along the affine — hence quasi-compact — map `Spec S → Spec S_0`.

## Main results

* `Algebra.isCompact_isOpen_setOf_relativeDimensionAt_le`: Stacks 00QJ.

## Implementation notes

*"Quasi-compact open" is `IsCompact V ∧ IsOpen V`.* Mathlib's `IsCompact` is quasi-compactness:
no separation is assumed, so it is the source's notion and not a strengthening of it. The two
conjuncts are given in this order, and as a conjunction rather than as two theorems, because that
is the form the API for quasi-compact opens of a spectrum consumes them in:
`PrimeSpectrum.isCompact_isOpen_iff` rewrites exactly this conjunction into
`∃ t : Finset S, (zeroLocus t)ᶜ = V`, the concrete content a user wants — `V_n` is the complement
of the zero locus of finitely many elements, hence a finite union of basic opens — and
`IsCompact.isRetrocompact` turns the same pair into `IsRetrocompact V_n`, which is how the source
uses such sets later. (`PrespectralSpace.isTopologicalBasis` states the same conjunction with the
conjuncts the other way round, as `{U | IsOpen U ∧ IsCompact U}`.) Both conjuncts are asserted
because the source's claim is that `V_n` is quasi-compact *and* open; the first is the new content
of this tag, the second is Stacks 00QH's `Algebra.isOpen_setOf_relativeDimensionAt_le`, available
here because finite presentation implies finite type. The set is repeated rather than abbreviated
by a hypothesis or a local definition, so that the statement matches that theorem syntactically
and no unfolding is needed to combine them.

*Finite presentation is used, and is not implied by the conclusion being interesting.* Over a
Noetherian `R` the ring `S` is Noetherian too, `Spec S` is a Noetherian space and every open
subset of it is quasi-compact, so the first conjunct has content only over a non-Noetherian base
— which is exactly where finite type is weaker than finite presentation and where the source's
descent to `R_0` is needed. The hypothesis is therefore not decoration on top of 00QH: dropping
it to `Algebra.FiniteType R S` would leave openness intact but is not known to preserve
quasi-compactness.

*The bound is a natural number.* `n : ℕ` is coerced into `WithBot ℕ∞`, the value type of
`Algebra.relativeDimensionAt`, as in the source's `n ≥ 0` and as in Stacks 00QH.
The statement happens to hold for a bound anywhere in `WithBot ℕ∞`, the extra cases being `⊥`,
where `V` is empty because a fibre through `𝔮` contains `𝔮` and so is nonempty, and `⊤`, where
`V` is all of `Spec S`, which is quasi-compact (`PrimeSpectrum.compactSpace`); neither carries
content.

*Relative dimension.* `dim_𝔮(S/R)` is `Algebra.relativeDimensionAt R 𝔮` (tag 00QD): the
dimension at `𝔮` of the fibre of `Spec S → Spec R` through `𝔮`, realized there as the subspace
`comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S` in place of the homeomorphic `Spec (S ⊗_R κ(𝔭))`.
The prime `𝔭` is not an argument: it is `𝔮.under R`, as the source's `𝔭` is.

Faithfulness to [StacksProject 00QJ]:

1. No hypothesis is idle. `n` occurs in the conclusion as the bound; `Algebra.FinitePresentation
   R S` is the source's hypothesis on the ring map, gives openness through
   `Algebra.FiniteType R S` and 00QH, and is what the source's proof consumes for
   quasi-compactness through the descent to a Noetherian `R_0` and 00QI; the conclusion is a
   statement about the `R`-algebra structure on `S`, which every remaining datum enters.
2. The scalars and base are the source's. The relative dimension is taken over `R` itself: the
   fibre is the fibre of `Spec S → Spec R` over `𝔭 = R ∩ 𝔮` for the given `Algebra R S`, not over
   a localization, a quotient or a base change of `R`; and the topology in which `V_n` is open and
   quasi-compact is that of `Spec S`, not that of a fibre or of `Spec R_0`.
3. Nothing is left merely to exist. `V_n` is pinned as the sublevel set
   `{𝔮 | dim_𝔮(S/R) ≤ n}` of the named function `Algebra.relativeDimensionAt R`, and both
   conjuncts are asserted of that set itself — not of some quasi-compact open contained in or
   containing it, and not of a dimension of some chosen model of the fibre.
4. The instantiation is not degenerate. For `R = k[t]`, `S = k[t, x]/(t x)` and `n = 0` the set is
   the basic open `V_0 = D(t)`: the fibre over `(f)` with `f ≠ t` irreducible, and over `(0)`, is
   `κ(𝔭)[x]/(x) = κ(𝔭)`, of dimension `0`, whereas the fibre over `(t)` is the affine line
   `Spec k[x]`, of dimension `1` at each of its points. So `V_0` is
   neither `∅` nor `Set.univ` — it misses exactly the closed set `V(t)` — and both asserted
   properties are non-trivial instances rather than `IsCompact ∅` or `IsOpen Set.univ`. For a
   witness in which quasi-compactness is not inherited from a Noetherian space, take the
   non-Noetherian `R = k[t_1, t_2, t_3, …]` and `S = R[x]/(t_1 x)`, again of finite presentation:
   `V_0 = D(t_1)` is a nonempty proper open subset of a non-Noetherian `Spec S`, quasi-compact
   because it is a basic open (`PrimeSpectrum.isCompact_basicOpen`).

## References

* [StacksProject 00QJ](https://stacks.math.columbia.edu/tag/00QJ)
* [StacksProject 00QD](https://stacks.math.columbia.edu/tag/00QD)
* [StacksProject 00QH](https://stacks.math.columbia.edu/tag/00QH)
* [StacksProject 00QI](https://stacks.math.columbia.edu/tag/00QI)

## Tags

relative dimension, fibre, dimension of fibres, quasi-compact open, finite presentation
-/

@[expose] public section

namespace Algebra

/-- **Stacks 00QJ.** Let `R → S` be a ring map of finite presentation and let `n : ℕ`. The set
`V_n = {𝔮 ∈ Spec S | dim_𝔮(S/R) ≤ n}` of primes at which the fibre of `Spec S → Spec R` has
dimension at most `n` is a quasi-compact open subset of `Spec S`. -/
@[stacks 00QJ "\"Quasi-compact open\" is `IsCompact V ∧ IsOpen V`, in the order and form
`PrimeSpectrum.isCompact_isOpen_iff` consumes; the second conjunct is tag 00QH for the underlying
finite type ring map, the first is the content here. `dim_𝔮(S/R)` is
`Algebra.relativeDimensionAt R 𝔮` (tag 00QD). See the module docstring."]
public theorem isCompact_isOpen_setOf_relativeDimensionAt_le {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (n : ℕ) :
    IsCompact {𝔮 : PrimeSpectrum S |
        Algebra.relativeDimensionAt R 𝔮.asIdeal ≤ (n : WithBot ℕ∞)} ∧
      IsOpen {𝔮 : PrimeSpectrum S |
        Algebra.relativeDimensionAt R 𝔮.asIdeal ≤ (n : WithBot ℕ∞)} :=
  Stacks.RelativeDimension.CompactLocus.solution n

end Algebra

end
