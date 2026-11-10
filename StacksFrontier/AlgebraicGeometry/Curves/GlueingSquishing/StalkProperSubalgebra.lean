module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryFactorization

/-!
# A proper intermediate subalgebra of the stalk extension of [Stacks, Tag 0C1L]

The splitting hypothesis `hsplit` of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` needs an intermediate `𝒜` with
`𝒪_X ⊊ 𝒜 ⊊ f_*𝒪_{X'}`: the *lower* strictness is what the capture clause of
`Stacks.GlueSquishFactor.exists_split_isAlmostIso_of_section` supplies, and the *upper*
strictness — properness of `𝒜 ⊂ f_*𝒪_{X'}` — is what no producer in the tree supplies; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SubalgebraProducer` and of
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsAdditivity`.

**This file settles the question at the stalk.** With `A = 𝒪_{X, x}` and `B = (f_*𝒪_{X'})_x`, the
source's intermediate subalgebra `A + m_A B` is **always proper** as soon as `A ≠ B`, and it is
strictly above `A` exactly when `m_A B` is not contained in `A`. So a proper intermediate
`A`-subalgebra of `B` exists unless `m_A B ⊆ A`, and in that remaining case the fibre
`B ⧸ m_A B` is what [Stacks, Tag 0C1I] classifies — which is the dichotomy the source's
trichotomy on `A ⊂ A + m_A B ⊂ B` amounts to, with no minimality hypothesis assumed.

The construction of `A + m_A B` and the Nakayama step are
`Stacks.GlueSquishFactor.addMapMaximalIdeal` and
`Stacks.GlueSquishFactor.bot_eq_top_of_forall_sub_mem`, both already in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryFactorization`; what is added
here is the properness, which they were not used for.

## Main results

* `Stacks.GlueSquishFactor.addMapMaximalIdeal_ne_top` — **`A + m_A B ≠ B`** whenever `A ≠ B`.
  This is the contrapositive of Nakayama, read as properness rather than as an exclusion inside
  a trichotomy.
* `Stacks.GlueSquishFactor.bot_lt_addMapMaximalIdeal` — `A ⊊ A + m_A B` as soon as some element
  of `m_A B` is not in the image of `A`.
* `Stacks.GlueSquishFactor.exists_subalgebra_bot_lt_lt_top` — **a proper intermediate subalgebra
  exists** under that hypothesis: `A ⊊ A + m_A B ⊊ B`.
* `Stacks.GlueSquishFactor.forall_exists_algebraMap_eq_or_exists_subalgebra` — **the dichotomy**:
  either `m_A B ⊆ A`, or there is an `A`-subalgebra strictly between `A` and `B`. No minimality
  is assumed, so this strictly strengthens
  `Stacks.GlueSquishFactor.exists_algebraMap_eq_of_mem_map_maximalIdeal`, which reaches the first
  alternative only by assuming the second away.

## What this does *not* give, and what it does

A proper quasi-coherent subalgebra `𝒜 ⊂ f_*𝒪_{X'}` **for an arbitrary stalk subalgebra**. The
subalgebra produced here lives in `Subalgebra 𝒪_{X,x} (f_*𝒪_{X'})_x`, and this file does not
carry an arbitrary one up to a quasi-coherent `𝒪_X`-subalgebra of `f_*𝒪_{X'}`.

**That passage is available elsewhere in the library**, together with a stalk API for
`Stacks.RelativeSpec.AlgebraSheaf.Subalg` and its correspondence with the subalgebras of a stalk:
`Stacks.RelativeSpec.AlgebraSheaf.germPreimage` in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.StalkSubalgebraSpreadOut` is the concrete
subalgebra cut out by a subalgebra of one stalk — the sections whose germ at `x` lies in `E` —
and `Stacks.GlueSquishFactor.exists_isFinite_subalg_ne_top_of_subalgebra_lt` spreads an arbitrary
`𝒪_{X,x} ⊊ E ⊊ (f_*𝒪_{X'})_x` out to a finite quasi-coherent subalgebra proper at both ends over
an affine open around `x`. What the dichotomy below contributes there is the hypothesis that
makes the spread-out subalgebra quasi-coherent, `m_x·(f_*𝒪_{X'})_x ⊆ E`: its first branch gives it
for every `E`, and in its second branch `𝒪_{X,x} + m_x·(f_*𝒪_{X'})_x` is an `E` that satisfies it.

**For the one subalgebra this file produces the passage is explicit.** `𝒪_{X,x} + m_x·(f_*𝒪_{X'})_x`
is spread out to the quasi-coherent
`𝒪_X + ℐ_x · f_*𝒪_{X'}` by `Stacks.GlueSquishFactor.idealSmulSubalg` in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SpreadOutSubalgebra`, which is
`Stacks.AlgebraicGeometry.SubalgebraGeneratedByModule.genSubalg` composed with
`Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul` at `n = 1`: neither of the two
constructions is by itself an ideal-times-algebra construction, but their *composition* is exactly
that. Its properness over an affine open around `x`
is `Stacks.GlueSquishFactor.ne_top_obj_idealSmulSubalg`, which is
`Stacks.GlueSquishFactor.addMapMaximalIdeal_ne_top` carried along the germ maps; its lower
properness is `Stacks.GlueSquishFactor.exists_mem_obj_idealSmulSubalg_notMem_range` in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.LowerProperSubalgebra`; and the points of
the support of the two quotients that the measure asks for are
`Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel_both` in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsSupport`. The wanted sheaf
does not have stalk `𝒪_{X, y}` elsewhere; see the module docstring of `...SpreadOutSubalgebra`.

## No stacks attribute

**No `@[stacks]` attribute is attached, and none is earned.** This is an input to the splitting
hypothesis of `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`, which is still
unproved.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0C1I](https://stacks.math.columbia.edu/tag/0C1I)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

universe v

namespace Stacks.GlueSquishFactor

variable (A B : Type v) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]

/-- **`A + m_A B` is a proper subalgebra of `B`.** If it were all of `B`, every element of `B`
would be congruent to an element of `A` modulo `m_A B`, and Nakayama
(`Stacks.GlueSquishFactor.bot_eq_top_of_forall_sub_mem`) would give `A = B`.

The source uses this only to *exclude* the middle case of its trichotomy on
`A ⊂ A + m_A B ⊂ B`; read the other way round it is the one properness statement the splitting
hypothesis of [Stacks, Tag 0C1L] needs, and it holds with no minimality assumed. -/
theorem addMapMaximalIdeal_ne_top [Module.Finite A B] (hne : (⊥ : Subalgebra A B) ≠ ⊤) :
    addMapMaximalIdeal A B ≠ ⊤ := fun htop =>
  hne (bot_eq_top_of_forall_sub_mem A B fun b =>
    show b ∈ addMapMaximalIdeal A B from htop ▸ Algebra.mem_top)

/-- **`A + m_A B` is strictly larger than `A`** as soon as some element of `m_A B` is not in the
image of `A`: that element lies in `A + m_A B` with the witness `0`. -/
theorem bot_lt_addMapMaximalIdeal {b : B}
    (hb : b ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (hnb : ∀ a : A, algebraMap A B a ≠ b) :
    (⊥ : Subalgebra A B) < addMapMaximalIdeal A B := by
  refine lt_of_le_of_ne bot_le fun hcon => ?_
  have hbE : b ∈ addMapMaximalIdeal A B := ⟨0, by simpa using hb⟩
  rw [← hcon] at hbE
  obtain ⟨a, ha⟩ := (Algebra.mem_bot (R := A) (A := B)).mp hbE
  exact hnb a ha

/-- **A proper intermediate subalgebra of the stalk extension.** For `B` module-finite over the
local ring `A`, if `m_A B` has an element outside the image of `A` then `A + m_A B` sits strictly
between `A` and `B`.

With `A = 𝒪_{X, x}` and `B = (f_*𝒪_{X'})_x` this is the subalgebra the induction of
[Stacks, Tag 0C1L] splits along at a single bad point; carrying it up to a quasi-coherent
subalgebra of `f_*𝒪_{X'}` is the step this file does not take, see its implementation notes. -/
theorem exists_subalgebra_bot_lt_lt_top [Module.Finite A B] (hne : (⊥ : Subalgebra A B) ≠ ⊤)
    {b : B} (hb : b ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (hnb : ∀ a : A, algebraMap A B a ≠ b) :
    ∃ E : Subalgebra A B, ⊥ < E ∧ E < ⊤ :=
  ⟨addMapMaximalIdeal A B, bot_lt_addMapMaximalIdeal A B hb hnb,
    lt_of_le_of_ne le_top (addMapMaximalIdeal_ne_top A B hne)⟩

/-- **The dichotomy at the stalk of [Stacks, Tag 0C1L].** For `B` module-finite over the local
ring `A` with `A ≠ B`: either `m_A B` is contained in the image of `A`, or there is an
`A`-subalgebra of `B` strictly between `A` and `B`.

This is the source's trichotomy on `A ⊂ A + m_A B ⊂ B` with nothing assumed away. It strictly
strengthens `Stacks.GlueSquishFactor.exists_algebraMap_eq_of_mem_map_maximalIdeal`, which reaches
the first alternative only under the hypothesis `hmin` that excludes the second; and the second
alternative is the only thing the splitting step of [Stacks, Tag 0C1L] is missing at the stalk,
properness of the intermediate subalgebra being `addMapMaximalIdeal_ne_top`. -/
theorem forall_exists_algebraMap_eq_or_exists_subalgebra [Module.Finite A B]
    (hne : (⊥ : Subalgebra A B) ≠ ⊤) :
    (∀ b ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B), ∃ a : A, algebraMap A B a = b) ∨
      ∃ E : Subalgebra A B, ⊥ < E ∧ E < ⊤ := by
  by_cases hall : ∀ b ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B),
      ∃ a : A, algebraMap A B a = b
  · exact Or.inl hall
  · obtain ⟨b, hb, hnb⟩ := by simpa only [not_forall, not_exists] using hall
    exact Or.inr (exists_subalgebra_bot_lt_lt_top A B hne hb (by simpa using hnb))

end Stacks.GlueSquishFactor

end
