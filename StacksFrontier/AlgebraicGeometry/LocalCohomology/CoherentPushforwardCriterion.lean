module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CompletionAssociatedPrimeDepth
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs

/-!
# The dimension bound at a non-generic point of an integral scheme

Let `Z` be an integral locally Noetherian scheme and let `w` be a point of `Z` other than its
generic point. Write `A = 𝒪_{Z,w}` and `Â` for the completion of `A` at its maximal ideal. This
file proves that every associated component of `Â` has dimension at least one:
`dim(Â/𝔭) ≥ 1` for every associated prime `𝔭` of `Â`. Consequently such a component has
dimension exactly one as soon as it does not have dimension at least two.

The argument is purely local: `w` is not the generic point, so `A` has Krull dimension at least
one, hence is not a field; a nonzero element of its maximal ideal is then a regular element
because `A` is a domain, so `A` has depth at least one; depth is unchanged by completion
([Stacks, Tag 07NW]) and is bounded by `dim(Â/𝔭)` at an associated prime
([Stacks, Tag 0BK4]).

## Main results

* `Stacks.LocalCohomology.one_le_depth_of_isSMulRegular`: a finite nontrivial module over a
  local ring on which some element of the maximal ideal acts regularly has depth at least one.
* `Stacks.LocalCohomology.one_le_depth_of_maximalIdeal_ne_bot`: a Noetherian local domain which
  is not a field has depth at least one.
* `Stacks.LocalCohomology.one_le_ringKrullDim_quotient_adicCompletion`: at an associated prime
  of the completion, `dim(Â/𝔭)` is bounded below by the depth of `A`.
* `Stacks.LocalCohomology.one_le_ringKrullDim_stalk_of_ne_genericPoint`: the local ring of an
  integral scheme at a non-generic point has Krull dimension at least one.
* `Stacks.LocalCohomology.one_le_ringKrullDim_quotient_adicCompletion_stalk`: the dimension
  bound at a non-generic point of an integral locally Noetherian scheme.
* `Stacks.LocalCohomology.ringKrullDim_quotient_adicCompletion_stalk_eq_one`: an associated
  component of the completed local ring at a non-generic point which fails `2 ≤ dim(Â/𝔭)` has
  `dim(Â/𝔭) = 1`.
* `Stacks.LocalCohomology.ne_genericPoint_of_notMem_range`: a point outside the image of an open
  immersion with irreducible source into an irreducible scheme is not the generic point.
* `Stacks.LocalCohomology.ringKrullDim_quotient_adicCompletion_stalk_eq_one_of_notMem_range`:
  the previous two combined, with the point given as lying outside the image of an open immersion
  rather than as differing from the generic point.

## Implementation notes

Associated primes are taken in the Stacks Project's sense (`IsAssociatedPrimeStacks`, the
annihilator of a single element); the passage to Mathlib's `associatedPrimes` is
`Stacks.LocalCohomology.mem_associatedPrimes_of_isAssociatedPrimeStacks`.

Krull dimensions live in `WithBot ℕ∞`, so the final arithmetic step — that `1 ≤ d` and `d < 2`
force `d = 1` — is done by case analysis on the bottom and top elements rather than by `omega`.

The specialization order on the points of a scheme is used only through
`AlgebraicGeometry.Scheme.le_iff_specializes` and `Order.coheight_add_one_le`, so no
antisymmetry of that order is needed: the strict inequality `w < genericPoint Z` is produced
from `Inseparable.eq` in the T0 space `Z`.

## References

* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 0BK4](https://stacks.math.columbia.edu/tag/0BK4)
* [Stacks Project, Tag 07NW](https://stacks.math.columbia.edu/tag/07NW)
* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace Stacks.LocalCohomology

/-! ### Depth at least one -/

/-- A finite nontrivial module over a local ring on which some element of the maximal ideal acts
regularly has depth at least one along the maximal ideal: that one element is a regular sequence
of length one, and its terms lie in the maximal ideal. -/
theorem one_le_depth_of_isSMulRegular {A : Type*} [CommRing A] [IsLocalRing A] {M : Type*}
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] {a : A}
    (ha : a ∈ maximalIdeal A) (hreg : IsSMulRegular M a) :
    1 ≤ Module.depth A (maximalIdeal A) M := by
  have hmem : ∀ r ∈ [a], r ∈ maximalIdeal A := by
    intro r hr
    rw [List.mem_singleton] at hr
    exact hr ▸ ha
  have hseq : RingTheory.Sequence.IsRegular M [a] :=
    RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M hmem
      ((RingTheory.Sequence.isWeaklyRegular_singleton_iff M a).mpr hreg)
  rw [Module.depth]
  split_ifs with h
  · exact le_top
  · exact le_iSup₂_of_le [a] ⟨hmem, hseq⟩ (by simp)

/-- A Noetherian local domain which is not a field has depth at least one: any nonzero element
of the maximal ideal is a nonzerodivisor, hence a regular sequence of length one. -/
theorem one_le_depth_of_maximalIdeal_ne_bot {A : Type*} [CommRing A] [IsDomain A]
    [IsLocalRing A] (h : maximalIdeal A ≠ ⊥) :
    1 ≤ Module.depth A (maximalIdeal A) A := by
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ maximalIdeal A, a ≠ 0 := by
    by_contra hc
    refine h (le_antisymm (fun a ha => ?_) bot_le)
    rw [Submodule.mem_bot]
    by_contra ha0
    exact hc ⟨a, ha, ha0⟩
  have hreg : IsSMulRegular A a := fun b c (hbc : a • b = a • c) =>
    mul_left_cancel₀ ha0 hbc
  exact one_le_depth_of_isSMulRegular ha hreg

/-! ### The dimension of an associated component of the completion -/

/-- The depth of a Noetherian local ring bounds below the dimension of every associated
component of its completion at the maximal ideal.

This is [Stacks, Tag 0BK4] applied to `Â` as a module over itself, transported back along the
invariance of depth under completion, [Stacks, Tag 07NW]. -/
theorem one_le_ringKrullDim_quotient_adicCompletion {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A]
    (hdepth : 1 ≤ Module.depth A (maximalIdeal A) A)
    {p : Ideal (AdicCompletion (maximalIdeal A) A)}
    (hp : IsAssociatedPrimeStacks (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal A) A) p) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ p) := by
  have hdepthR : 1 ≤ Module.depth (AdicCompletion (maximalIdeal A) A)
      (maximalIdeal (AdicCompletion (maximalIdeal A) A))
      (AdicCompletion (maximalIdeal A) A) :=
    hdepth.trans_eq depth_adicCompletion_maximalIdeal
  refine le_trans ?_ (Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    (mem_associatedPrimes_of_isAssociatedPrimeStacks hp))
  exact_mod_cast hdepthR

/-! ### The geometric input: a non-generic point has positive-dimensional local ring -/

/-- The local ring of an integral scheme at a point other than its generic point has Krull
dimension at least one: the point specializes from the generic point and is distinct from it, so
its coheight in the specialization order is at least one, and the Krull dimension of a stalk is
that coheight ([Stacks, Tag 02IZ]). -/
theorem one_le_ringKrullDim_stalk_of_ne_genericPoint {Z : Scheme.{u}} [IsIntegral Z] (w : Z)
    (hw : w ≠ genericPoint Z) : (1 : WithBot ℕ∞) ≤ ringKrullDim (Z.presheaf.stalk w) := by
  have hwle : w ≤ genericPoint Z := by
    rw [Scheme.le_iff_specializes]
    exact genericPoint_specializes w
  have hstrict : w < genericPoint Z := by
    refine ⟨hwle, fun hrev => ?_⟩
    have hinsep : Inseparable w (genericPoint Z) :=
      inseparable_iff_specializes_and.mpr ⟨hrev, genericPoint_specializes w⟩
    exact hw hinsep.eq
  have hcoheight : (1 : ℕ∞) ≤ Order.coheight w :=
    le_trans (by simp) (Order.coheight_add_one_le hstrict)
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
  exact_mod_cast hcoheight

/-- **The dimension bound of [Stacks, Tag 0BK3] at a non-generic point.** Let `Z` be an integral
locally Noetherian scheme and `w` a point of `Z` other than its generic point. Every associated
prime `𝔭` of the completion `Â` of `A = 𝒪_{Z,w}` at its maximal ideal satisfies
`1 ≤ dim(Â/𝔭)`. -/
theorem one_le_ringKrullDim_quotient_adicCompletion_stalk {Z : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] {w : Z} (hw : w ≠ genericPoint Z)
    {p : Ideal (AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w))}
    (hp : IsAssociatedPrimeStacks
      (AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w))
      (AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w)) p) :
    (1 : WithBot ℕ∞) ≤
      ringKrullDim (AdicCompletion (maximalIdeal (Z.presheaf.stalk w))
        (Z.presheaf.stalk w) ⧸ p) := by
  have hdim := one_le_ringKrullDim_stalk_of_ne_genericPoint w hw
  have hmax : maximalIdeal (Z.presheaf.stalk w) ≠ ⊥ := fun hbot => by
    rw [ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hbot)] at hdim
    norm_num at hdim
  exact one_le_ringKrullDim_quotient_adicCompletion
    (one_le_depth_of_maximalIdeal_ne_bot hmax) hp

/-- An associated component of the completed local ring of an integral locally Noetherian scheme
at a non-generic point which fails the criterion `2 ≤ dim(Â/𝔭)` of [Stacks, Tag 0BK3] has
dimension exactly one. -/
theorem ringKrullDim_quotient_adicCompletion_stalk_eq_one {Z : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] {w : Z} (hw : w ≠ genericPoint Z)
    {p : Ideal (AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w))}
    (hp : IsAssociatedPrimeStacks
      (AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w))
      (AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w)) p)
    (hlt : ¬ (2 : WithBot ℕ∞) ≤
      ringKrullDim (AdicCompletion (maximalIdeal (Z.presheaf.stalk w))
        (Z.presheaf.stalk w) ⧸ p)) :
    ringKrullDim (AdicCompletion (maximalIdeal (Z.presheaf.stalk w))
      (Z.presheaf.stalk w) ⧸ p) = 1 := by
  have hpos := one_le_ringKrullDim_quotient_adicCompletion_stalk hw hp
  have hlt' := lt_of_not_ge hlt
  cases hd : ringKrullDim (AdicCompletion (maximalIdeal (Z.presheaf.stalk w))
      (Z.presheaf.stalk w) ⧸ p) with
  | bot => rw [hd] at hpos; simp at hpos
  | coe d =>
      rw [hd] at hpos hlt'
      have h1 : (1 : ℕ∞) ≤ d := by exact_mod_cast hpos
      have h2 : d < 2 := WithBot.coe_lt_coe.mp (by simpa using hlt')
      cases d with
      | top => simp at h2
      | coe n =>
          have hn1 : 1 ≤ n := by exact_mod_cast h1
          have hn2 : n < 2 := by exact_mod_cast h2
          have hn : n = 1 := by omega
          simp [hn]

/-! ### Points outside an open subscheme -/

/-- A point outside the image of an open immersion with irreducible source into an irreducible
scheme is not the generic point: the generic point of the source maps to the generic point of
the target, so the latter does lie in the image. -/
theorem ne_genericPoint_of_notMem_range {W Z : Scheme.{u}} [IrreducibleSpace W]
    [IrreducibleSpace Z] (j : W ⟶ Z) [IsOpenImmersion j] {w : Z}
    (hw : w ∉ Set.range j.base) : w ≠ genericPoint Z := by
  rintro rfl
  exact hw ⟨genericPoint W, genericPoint_eq_of_isOpenImmersion j⟩

/-- **The dimension bound of [Stacks, Tag 0BK3] at a point outside an open subscheme.** Let `Z`
be an integral locally Noetherian scheme and `j : W ⟶ Z` an open immersion with irreducible
source. At a point `w` of `Z` outside the image of `j`, an associated component of the completed
local ring `Â` of `A = 𝒪_{Z,w}` which fails `2 ≤ dim(Â/𝔭)` has `dim(Â/𝔭) = 1`. -/
theorem ringKrullDim_quotient_adicCompletion_stalk_eq_one_of_notMem_range {W Z : Scheme.{u}}
    [IsIntegral Z] [IsLocallyNoetherian Z] [IrreducibleSpace W] (j : W ⟶ Z) [IsOpenImmersion j]
    {w : Z} (hw : w ∉ Set.range j.base)
    {p : Ideal (AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w))}
    (hp : IsAssociatedPrimeStacks
      (AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w))
      (AdicCompletion (maximalIdeal (Z.presheaf.stalk w)) (Z.presheaf.stalk w)) p)
    (hlt : ¬ (2 : WithBot ℕ∞) ≤
      ringKrullDim (AdicCompletion (maximalIdeal (Z.presheaf.stalk w))
        (Z.presheaf.stalk w) ⧸ p)) :
    ringKrullDim (AdicCompletion (maximalIdeal (Z.presheaf.stalk w))
      (Z.presheaf.stalk w) ⧸ p) = 1 :=
  ringKrullDim_quotient_adicCompletion_stalk_eq_one
    (ne_genericPoint_of_notMem_range j hw) hp hlt

end Stacks.LocalCohomology

end
