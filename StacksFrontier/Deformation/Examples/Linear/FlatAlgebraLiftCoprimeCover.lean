module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Span
public import StacksFrontier.Deformation.FlatAlgebraLiftLocalizationRelative

/-!
# The converse of Stacks 0DZ7 at a principal multiplicative set is a two-element gluing principle

Stacks 0DZ7 compares flat lifts of a finite type flat `A`-algebra `B` with flat lifts of a
localization `S⁻¹B`, under the hypotheses that `A → B_h` is syntomic for every `h` in an ideal
`𝔟` of `B` (`hsyn`) and that `S` meets no prime of `B` containing `𝔟` (`hSb`). Its forward
implication is unconditional
(`Deformation.hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift`); its converse at a
nilpotent kernel is open, and the implementation notes of
`StacksFrontier/Deformation/FlatAlgebraLiftLocalization.lean` identify what remains of it as a
Zariski local-global principle for flat lifts.

This file carries out that identification, at a **principal** `S`, and makes it an
*equivalence*: the converse of Stacks 0DZ7 for `S = {gⁿ}` is logically equivalent to a
statement in which `S`, `𝔟`, `hsyn` and `hSb` have all been eliminated in favour of a single
**comaximal pair** `f, g ∈ B` — a two-element Zariski cover `Spec B = D(f) ∪ D(g)` with `D(f)`
syntomic over `A`:

> **(G)** Let `A' → A` be a surjection of Noetherian rings with nilpotent kernel, let `B` be a
> finite type flat `A`-algebra and let `f, g ∈ B` satisfy `(f) + (g) = B` with `A → B_h`
> syntomic for every `h ∈ (f)`. If `B_g` has a flat lift to `A'`, then so does `B`.

Both members of the cover then carry a flat lift of their own: `D(g)` by hypothesis, and `D(f)`
because `B_f` is syntomic, so Stacks 07M8 lifts it along any nilpotent thickening
(`Deformation.hasFlatAlgebraLift_of_syntomic`). So (G) says exactly that two lifts given on the
two members of a two-element affine cover, with **no compatibility assumed on the overlap**,
assemble to a lift on the whole.

## Main results

* `Deformation.Examples.CoprimeCover.FlatAlgebraLiftAwayStatement` — the converse of
  Stacks 0DZ7, quantified over all data, with `S` the powers of a single element.
* `Deformation.Examples.CoprimeCover.FlatAlgebraLiftCoprimeCoverStatement` — the statement (G).
* `Deformation.Examples.CoprimeCover.flatAlgebraLiftAwayStatement_iff_coprimeCoverStatement` —
  the two are equivalent.
* `Deformation.Examples.CoprimeCover.hasFlatAlgebraLift_of_coprimeCover_of_sqZero` — (G) holds
  at a square-zero kernel, so the reduction is not vacuous.
* `Deformation.Examples.CoprimeCover.hasFlatAlgebraLift_localization_iff_of_coprimeCoverStatement`
  — (G) implies the whole biconditional of Stacks 0DZ7 at a principal `S`.
* `Deformation.Examples.CoprimeCover.exists_isPrime_under_eq_of_le_of_forall_isPrime` — every
  prime containing `𝔟` is the contraction of a prime of `S⁻¹B`, so the non-syntomic locus
  survives the localization intact.

## What this settles and what it does not

What is new here is not that a Zariski principle is involved — the implementation notes of
`StacksFrontier/Deformation/FlatAlgebraLiftLocalization.lean` say so in prose, for an
`(r + 1)`-element cover of `Spec P'` by the complement of `V(J')` together with the
`D(g_i)` of generators of `J'`, and say it is not formalized. What is new is that

* the cover can be taken to have **two** members, because `hSb` lets the ideal `𝔟` be replaced
  by a principal subideal `(f)` with `f` comaximal to the one element being inverted
  (`Deformation.Examples.CoprimeCover.exists_mem_sup_span_singleton_eq_top_of_forall_isPrime`);
* the principle can be stated about the **algebra** `B` over `A`, with no presentation, no
  module and no `Ext`;
* the reduction is an **equivalence** rather than a sufficient condition, so a refutation of
  Stacks 0DZ7 at a principal `S` and a refutation of (G) are the same thing; and
* the two members of the cover are **not interchangeable**: `D(f)` is syntomic, hence
  unobstructed at every stage of the filtration of the kernel, while `D(g)` carries only one
  given lift. That asymmetry is what the gluing has to exploit; see the implementation notes, and
  `StacksFrontier/Deformation/Examples/Linear/CoprimeCoverDivisibleCorrection.lean` for the
  local-global algebra it yields.

A search strategy is also closed off, and it is the one that looks most promising from outside:
that a counterexample should have `S⁻¹B` be "more syntomic" than `B`, the localization having
removed the locus where the degree-one obstruction lives. It cannot. The condition `hSb` says
that no prime containing `𝔟` meets `S`, so **every** prime of the non-syntomic locus survives in
`S⁻¹B` and contracts back to itself — that is
`Deformation.Examples.CoprimeCover.exists_isPrime_under_eq_of_le_of_forall_isPrime`. Inverting
`S` discards part of the syntomic locus and none of the other, so the two sides of the tag have
the same bad points and a counterexample has to come from the gluing and not from a change of
locus. The reduction above says the same thing in different words: in (G) the localized side has
become the member `D(g)` of a cover, and `D(g)` contains the whole of the locus where `B` may
fail to be syntomic: that locus lies in `V(f)`, and `V(f) ⊆ D(g)` by comaximality.

What this does **not** do is decide (G). (G) is the one clause left open, and it is open at
exactly the kernels where the tag is open:
`Deformation.Examples.CoprimeCover.hasFlatAlgebraLift_of_coprimeCover_of_sqZero` proves it for a
square-zero kernel, and nothing here proves or refutes it for a nilpotent kernel of index three or
more. What the implementation notes below no longer claim is that the obstruction to deciding it is
the non-additivity of the obstruction variation: that obstacle is removed in
`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverDivisibleCorrection.lean`, and what remains
is an `Ext` interface this repository does not have.

## Implementation notes

**Why `𝔟` may be taken principal, and why that is only true at a principal `S`.** The
condition `hSb` says that no prime containing `𝔟` contains any element of `S`. Applied to the
single element `g` it gives `𝔟 + (g) = B`, hence a decomposition `1 = f + c·g` with `f ∈ 𝔟`;
and then `(f) + (g) = B` while `(f) ⊆ 𝔟`, so `hsyn` still holds on `(f)`. For a general `S` the
element `f` produced this way depends on the element of `S` inverted, and a single principal
subideal comaximal to every element of `S` at once need not exist. Passing from a principal `S`
to a general one is the filtered-colimit step described in the implementation notes of
`StacksFrontier/Deformation/FlatAlgebraLiftLocalization.lean`, and is not done here.

**Where the gluing stops.** Two flat lifts over `A'` given on `D(f)` and on `D(g)` restrict to
two flat lifts of `B_{fg}` over `A'`, and to glue them one must be carried onto the other. Along
a square-zero kernel the lifts of a fixed algebra on a fixed open form a torsor under a module
`T¹`, and the comparison class on the overlap can be split between the two members because the
Čech complex of a quasi-coherent module on an affine scheme is exact in positive degree: for a
`B`-module `E` and comaximal `f, g`, the map `E_f ⊕ E_g → E_{fg}` is surjective. That is the
content of the square-zero case, which is proved here as
`Deformation.Examples.CoprimeCover.hasFlatAlgebraLift_of_coprimeCover_of_sqZero`.

Beyond square zero the correction has to be chosen before the next stage of the filtration is
reached, and a correction that glues need not preserve liftability: on `D(f)` it does, the
algebra being syntomic there and hence unobstructed for *every* lift at every stage, but on
`D(g)` the only datum is one lift that happens to exist, and the corrected lift is a different
one whose obstruction is the variation `∂ = δ + sq` of the original's. The map `∂` is not
additive — `StacksFrontier/Deformation/ObstructionVariationQuadratic.lean` proves that the
unobstructed classes are not a coset of a submodule — so the whole correction cannot be pushed
onto the syntomic member.

Non-additivity of `∂` is nevertheless not what stops the gluing, and
`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverDivisibleCorrection.lean` says why. The
share of the correction that the Čech splitting leaves on `D(g)` can be chosen divisible by any
prescribed power of `f`, because comaximality supplies a partition of unity `1 = u f^N + v gᵏ` for
every `N` and not only for `N = 0`
(`Deformation.Examples.CoprimeCover.exists_eq_add_pow_smul`); and the obstruction module of the
lifting problem is annihilated by one power of `f`, being finitely generated over `B` and vanishing
over the syntomic `D(f)`
(`Deformation.Examples.CoprimeCover.exists_forall_pow_smul_eq_zero_of_forall_eq_zero`). A
correction divisible by that power is killed by `∂` outright — the additive term picks up a factor
`f^n` and the quadratic one `f^{2n}`, and one factor already annihilates the target
(`Deformation.Examples.CoprimeCover.obstructionVariation_pow_smul_eq_zero`) — so the share left on
`D(g)` does not change the obstruction there, and `∂` is not merely linear on the available
corrections but zero on them
(`Deformation.Examples.CoprimeCover.exists_eq_add_obstructionVariation_eq_zero`).

**What this file still does not decide is (G)**, and what is missing is now the deformation theory
rather than the local-global algebra: the torsor of lifts, the obstruction class, its variation by
a Bockstein plus a cup-square, the vanishing of `Ext²` over a local complete intersection and the
naturality of all four under localization. No `Ext` API in this repository presents them; the
argument they would assemble is written out in the implementation notes of
`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverDivisibleCorrection.lean`.

**Degenerate corners.** A counterexample to (G) must have both `f` and `g` non-units. For `f` a
unit, `(f) = B` so `hsyn` makes `A → B` itself syntomic and `B` lifts by Stacks 07M8; that is
`Deformation.Examples.CoprimeCover.hasFlatAlgebraLift_localization_iff_of_isUnit`, delegated to
`Deformation.hasFlatAlgebraLift_localization_iff_of_one_mem`. For `g` a unit, `B_g = B` and the
implication is its own conclusion. The remaining constraints inherited from the tag's analysis
are unchanged by the reduction: by
`Deformation.hasFlatAlgebraLift_localization_iff_of_split` the surjection `A' → A` can admit no
ring section, and by `Deformation.hasFlatAlgebraLift_localization_iff_of_sqZero` its kernel
cannot have square zero.

## References

* [Stacks Project, Tag 0DZ7](https://stacks.math.columbia.edu/tag/0DZ7)
* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
-/

@[expose] public noncomputable section

universe u

namespace Deformation.Examples.CoprimeCover

/-! ### Comaximality from the tag's condition on `S` -/

/-- An ideal `𝔟` and an element `s` lying in no prime containing `𝔟` are comaximal: otherwise
`𝔟 + (s)` is proper, hence contained in a maximal — and so prime — ideal, which then contains
both `𝔟` and `s`. -/
theorem sup_span_singleton_eq_top_of_forall_isPrime {B : Type u} [CommRing B] (b : Ideal B)
    (s : B) (hs : ∀ q : Ideal B, q.IsPrime → b ≤ q → s ∉ q) :
    b ⊔ Ideal.span {s} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  exact hs m hm.isPrime (le_sup_left.trans hle)
    (hle (Submodule.mem_sup_right (Ideal.mem_span_singleton_self s)))

/-- **The ideal `𝔟` of Stacks 0DZ7 may be replaced by a principal subideal, once `S` is the
powers of a single element.** If `s` lies in no prime containing `𝔟`, then some `f ∈ 𝔟` is
already comaximal to `s`. Since `(f) ≤ 𝔟`, the syntomic hypothesis `hsyn` of the tag survives
the replacement, while the condition `hSb` becomes comaximality of the pair `f, s`. -/
theorem exists_mem_sup_span_singleton_eq_top_of_forall_isPrime {B : Type u} [CommRing B]
    (b : Ideal B) (s : B) (hs : ∀ q : Ideal B, q.IsPrime → b ≤ q → s ∉ q) :
    ∃ f ∈ b, Ideal.span {f} ⊔ Ideal.span {s} = ⊤ := by
  have h1 : (1 : B) ∈ b ⊔ Ideal.span {s} := by
    rw [sup_span_singleton_eq_top_of_forall_isPrime b s hs]; exact Submodule.mem_top
  obtain ⟨f, hf, y, hy, hsum⟩ := Submodule.mem_sup.mp h1
  exact ⟨f, hf, (Ideal.eq_top_iff_one _).mpr
    (Submodule.mem_sup.mpr ⟨f, Ideal.mem_span_singleton_self f, y, hy, hsum⟩)⟩

/-- **Comaximality is the condition `hSb` of Stacks 0DZ7 at a principal multiplicative set.** If
`f` and `g` are comaximal then no prime containing `(f)` contains any power of `g`: such a prime
would contain `g`, hence `(f) + (g) = B`, hence `1`. -/
theorem forall_notMem_powers_of_sup_span_singleton_eq_top {B : Type u} [CommRing B] (f g : B)
    (hfg : Ideal.span {f} ⊔ Ideal.span {g} = ⊤) :
    ∀ q : Ideal B, q.IsPrime → Ideal.span {f} ≤ q → ∀ t ∈ Submonoid.powers g, t ∉ q := by
  rintro q hq hfq t ⟨n, rfl⟩ htq
  have hgq : g ∈ q := hq.mem_of_pow_mem n htq
  refine hq.ne_top (top_le_iff.mp ?_)
  rw [← hfg]
  exact sup_le hfq ((Ideal.span_singleton_le_iff_mem _).mpr hgq)

/-! ### The non-syntomic locus survives the localization -/

/-- **Every prime containing `𝔟` survives in `S⁻¹B`.** The condition `hSb` of Stacks 0DZ7 says
that no prime containing `𝔟` meets `S`. Such a prime is therefore disjoint from `S`, so its
image in `S⁻¹B` is prime and contracts back to it.

So the locus `V(𝔟)`, off which `hsyn` asserts syntomy, is carried into `Spec S⁻¹B` in its
entirety: localizing at `S` discards part of the *syntomic* locus and none of the non-syntomic
one. In particular no counterexample to Stacks 0DZ7 can work by making `S⁻¹B` "more syntomic"
than `B` — inverting `S` cannot remove the locus where the obstruction lives, because `hSb` is
precisely the condition that it does not. That is why the tag is plausible, and it is where the
comparison gets its content: the two sides differ only over the syntomic locus, where both are
unobstructed. -/
theorem exists_isPrime_under_eq_of_le_of_forall_isPrime
    {B : Type u} [CommRing B] (S : Submonoid B) (C : Type u) [CommRing C] [Algebra B C]
    [IsLocalization S C] (b : Ideal B)
    (hSb : ∀ q : Ideal B, q.IsPrime → b ≤ q → ∀ s ∈ S, s ∉ q)
    (q : Ideal B) (hq : q.IsPrime) (hbq : b ≤ q) :
    ∃ Q : Ideal C, Q.IsPrime ∧ Q.under B = q := by
  have hdisj : Disjoint (S : Set B) (q : Set B) :=
    Set.disjoint_left.mpr fun s hs hsq => hSb q hq hbq s hs hsq
  exact ⟨Ideal.map (algebraMap B C) q,
    IsLocalization.isPrime_of_isPrime_disjoint S C q hq hdisj,
    IsLocalization.under_map_of_isPrime_disjoint S C hq hdisj⟩

/-! ### The two statements -/

/-- **The converse of Stacks 0DZ7 at a principal multiplicative set.** For every surjection
`A' → A` of Noetherian rings with nilpotent kernel, every finite type flat `A`-algebra `B`,
every `s ∈ B` and every ideal `𝔟` of `B` with `A → B_h` syntomic for all `h ∈ 𝔟` and no prime
containing `𝔟` meeting the powers of `s`: a flat lift of `B_s` to `A'` gives one of `B`.

This is `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_at` with its
hypothesis `h0DZ2` removed and `S` specialized to `Submonoid.powers s`; the forward implication
of the tag is unconditional, so this Prop is all of Stacks 0DZ7 that is open at a principal
`S`. -/
def FlatAlgebraLiftAwayStatement : Prop :=
  ∀ (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B],
    Function.Surjective (algebraMap A' A) →
    IsNilpotent (RingHom.ker (algebraMap A' A)) →
    ∀ [Algebra.FiniteType A B] [Module.Flat A B] (s : B) (C : Type u) [CommRing C]
      [Algebra B C] [IsLocalization (Submonoid.powers s) C] [Algebra A C] [IsScalarTower A B C]
      (b : Ideal B),
    (∀ h ∈ b, Algebra.Syntomic A (Localization.Away h)) →
    (∀ q : Ideal B, q.IsPrime → b ≤ q → ∀ t ∈ Submonoid.powers s, t ∉ q) →
    HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B

/-- **The two-element Zariski gluing principle for flat algebra lifts, with one syntomic
member.** For every surjection `A' → A` of Noetherian rings with nilpotent kernel, every finite
type flat `A`-algebra `B` and every comaximal pair `f, g ∈ B` with `A → B_h` syntomic for all
`h ∈ (f)`: a flat lift of `B_g` to `A'` gives one of `B`.

Comaximality of `f, g` says `Spec B = D(f) ∪ D(g)`. The member `D(f)` carries a flat lift of its
own, `B_f` being syntomic and Stacks 07M8 lifting a syntomic algebra along any nilpotent
thickening (`Deformation.hasFlatAlgebraLift_of_syntomic`), and `D(g)` carries the hypothesised
one. So the statement asserts that two lifts on the two members of a two-element affine cover,
with nothing assumed about their restrictions to the overlap, assemble to a lift on
`Spec B`. -/
def FlatAlgebraLiftCoprimeCoverStatement : Prop :=
  ∀ (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B],
    Function.Surjective (algebraMap A' A) →
    IsNilpotent (RingHom.ker (algebraMap A' A)) →
    ∀ [Algebra.FiniteType A B] [Module.Flat A B] (f g : B),
    (∀ h ∈ Ideal.span {f}, Algebra.Syntomic A (Localization.Away h)) →
    Ideal.span {f} ⊔ Ideal.span {g} = ⊤ →
    ∀ (C : Type u) [CommRing C] [Algebra B C] [IsLocalization (Submonoid.powers g) C]
      [Algebra A C] [IsScalarTower A B C],
    HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B

/-! ### The equivalence -/

/-- **The gluing principle implies the converse of Stacks 0DZ7 at a principal multiplicative
set.** Given the tag's data, `hSb` at the element `s` itself produces an `f ∈ 𝔟` comaximal to
`s`, and `(f) ≤ 𝔟` keeps the syntomic hypothesis; the gluing principle at the pair `f, s` is
then the conclusion. So the ideal `𝔟`, the condition `hSb` and the multiplicative set are all
eliminable from the open converse. -/
theorem flatAlgebraLiftAwayStatement_of_coprimeCoverStatement
    (hG : FlatAlgebraLiftCoprimeCoverStatement.{u}) : FlatAlgebraLiftAwayStatement.{u} := by
  intro A' A B _ _ _ _ _ _ _ hsurjA hnilA _ _ s C _ _ _ _ _ b hsyn hSb hC
  obtain ⟨f, hfb, hfs⟩ := exists_mem_sup_span_singleton_eq_top_of_forall_isPrime b s
    (fun q hq hbq => hSb q hq hbq s (Submonoid.mem_powers s))
  exact hG A' A B hsurjA hnilA f s
    (fun h hh => hsyn h (((Ideal.span_singleton_le_iff_mem _).mpr hfb) hh)) hfs C hC

/-- **The converse of Stacks 0DZ7 at a principal multiplicative set implies the gluing
principle.** A comaximal pair `f, g` is the tag's data at `𝔟 = (f)` and `S` the powers of `g`:
the syntomic hypothesis is verbatim, and `hSb` is comaximality by
`Deformation.Examples.CoprimeCover.forall_notMem_powers_of_sup_span_singleton_eq_top`. -/
theorem flatAlgebraLiftCoprimeCoverStatement_of_awayStatement
    (hS : FlatAlgebraLiftAwayStatement.{u}) : FlatAlgebraLiftCoprimeCoverStatement.{u} := by
  intro A' A B _ _ _ _ _ _ _ hsurjA hnilA _ _ f g hsyn hfg C _ _ _ _ _ hC
  exact hS A' A B hsurjA hnilA g C (Ideal.span {f}) hsyn
    (forall_notMem_powers_of_sup_span_singleton_eq_top f g hfg) hC

/-- **What is left of Stacks 0DZ7 at a principal multiplicative set is exactly a two-element
Zariski gluing principle.** The forward implication of the tag being unconditional
(`Deformation.hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift`), the open content of the
tag at `S = {gⁿ}` is the converse, and that converse is equivalent to the statement about a
comaximal pair with one syntomic member — in which the multiplicative set, the ideal `𝔟`, the
condition `hSb` and all localization language have disappeared.

In particular a counterexample to Stacks 0DZ7 at a principal `S` and a counterexample to the
gluing principle are the same object, and the gluing principle is the statement to attack. -/
theorem flatAlgebraLiftAwayStatement_iff_coprimeCoverStatement :
    FlatAlgebraLiftAwayStatement.{u} ↔ FlatAlgebraLiftCoprimeCoverStatement.{u} :=
  ⟨flatAlgebraLiftCoprimeCoverStatement_of_awayStatement,
    flatAlgebraLiftAwayStatement_of_coprimeCoverStatement⟩

/-! ### What is proved in the new coordinates -/

/-- **The gluing principle holds at a square-zero kernel.** This is
`Deformation.hasFlatAlgebraLift_localization_iff_of_sqZero` read through the translation above,
and it is what makes the reduction non-vacuous: the clause left open is the same clause that is
open for the tag, namely the passage from a square-zero kernel to a nilpotent one. -/
theorem hasFlatAlgebraLift_of_coprimeCover_of_sqZero
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    [Algebra.FiniteType A B] [Module.Flat A B] (f g : B)
    (hsyn : ∀ h ∈ Ideal.span {f}, Algebra.Syntomic A (Localization.Away h))
    (hfg : Ideal.span {f} ⊔ Ideal.span {g} = ⊤)
    (C : Type u) [CommRing C] [Algebra B C] [IsLocalization (Submonoid.powers g) C]
    [Algebra A C] [IsScalarTower A B C] :
    HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B :=
  (hasFlatAlgebraLift_localization_iff_of_sqZero A' A B hsurjA hzeroA (Submonoid.powers g) C
    (Ideal.span {f}) hsyn (forall_notMem_powers_of_sup_span_singleton_eq_top f g hfg)).mpr

/-- **The gluing principle is empty when the syntomic member is everything.** If `f` is a unit
then `(f) = B`, so the syntomic hypothesis asserts syntomy of `A → B` itself and both sides of
the comparison hold by Stacks 07M8. So a counterexample to the gluing principle, and hence to
Stacks 0DZ7 at a principal multiplicative set, must have `f` a non-unit — and `g` a non-unit
too, since for `g` a unit the localization `B_g` is `B` and the implication is its own
conclusion. -/
theorem hasFlatAlgebraLift_localization_iff_of_isUnit
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A)) (f g : B)
    (hsyn : ∀ h ∈ Ideal.span {f}, Algebra.Syntomic A (Localization.Away h))
    (hf : IsUnit f)
    (C : Type u) [CommRing C] [Algebra B C] [IsLocalization (Submonoid.powers g) C]
    [Algebra A C] [IsScalarTower A B C] :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A C :=
  hasFlatAlgebraLift_localization_iff_of_one_mem A' A B hsurjA (Submonoid.powers g) C
    (Ideal.span {f}) hsyn
    (by rw [Ideal.span_singleton_eq_top.mpr hf]; exact Submodule.mem_top)

/-- **Stacks 0DZ7 at a principal multiplicative set, granted the gluing principle.** The forward
implication is `Deformation.hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift`, which needs
nothing beyond surjectivity of `A' → A`; the converse is the gluing principle through
`Deformation.Examples.CoprimeCover.flatAlgebraLiftAwayStatement_of_coprimeCoverStatement`.

This carries no Stacks attribute: its hypothesis `hG` is an open statement, so it records a
reduction and not a proof of the tag. -/
theorem hasFlatAlgebraLift_localization_iff_of_coprimeCoverStatement
    (hG : FlatAlgebraLiftCoprimeCoverStatement.{u})
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B]
    (s : B) (C : Type u) [CommRing C] [Algebra B C] [IsLocalization (Submonoid.powers s) C]
    [Algebra A C] [IsScalarTower A B C]
    (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (hSb : ∀ q : Ideal B, q.IsPrime → b ≤ q → ∀ t ∈ Submonoid.powers s, t ∉ q) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A C :=
  ⟨hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift A' A B hsurjA
      (Submonoid.powers s) C,
    flatAlgebraLiftAwayStatement_of_coprimeCoverStatement hG A' A B hsurjA hnilA s C b hsyn hSb⟩

end Deformation.Examples.CoprimeCover

end
