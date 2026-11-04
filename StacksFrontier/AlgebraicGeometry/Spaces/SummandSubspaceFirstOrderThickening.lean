module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# Subspaces of a thickening cut out by a sub-ideal of its defining ideal

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`Z ⊆ X` be a thickening of order `n` with defining ideal sheaf `𝓘_Z ⊆ 𝒪_X`.  Given a
quasi-coherent sheaf of ideals `N ⊆ 𝓘_Z`, this file produces the closed subspace `Z' ⊆ X`
that `N` cuts out, shows that it contains `Z`, and shows that it is again a thickening of
order `n`.

This is the space-level form of the step in [Stacks Project, Tag 06D8] that reads

> Let `Z' ⊂ Z''` be the closed subscheme cut out by `𝒞_{Z/X} ⊂ 𝓘` viewed as a quasi-coherent
> sheaf of ideals on `Z''`.  It is clear that `Z'` is a first order thickening of `Z`.

There `Z ⊂ Z''` is the universal first-order thickening of `Z` over `X'`, `𝓘` is its defining
ideal sheaf, and `𝒞_{Z/X} ⊆ 𝓘` is one of the two summands of a chosen splitting
`𝓘 = i^*𝒞_{X/X'} ⊕ 𝒞_{Z/X}`.  The source says *closed subscheme* because `Z` is affine and
[Stacks Project, Tag 05ZR] makes `Z''` a scheme; the construction below needs no such passage,
because the surjectivity half of [Stacks Project, Tag 03MB] is available for algebraic spaces
in `AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite`.

What the summand hypothesis of the source contributes here is exactly two things: the
containment `N ⊆ 𝓘_Z`, and quasi-coherence of `N`.  Both are hypotheses below, so the
construction is stated for an arbitrary quasi-coherent sub-ideal and the splitting enters only
through its consequences.

## Main results

* `Submodule.pow_le_pow_of_le`: a power of a sheaf of submodules is monotone in the submodule.
* `AlgebraicGeometry.Space.surjective_pointsMap_homOfLe`: the comparison morphism from a
  thickening subspace into a larger subfunctor is surjective on points, so the pair `Z ⊆ Z'`
  produced below satisfies the topological clause of [Stacks Project, Tag 05ZK], part (1).
* `AlgebraicGeometry.Space.isNthOrderThickening_of_le`: a closed subspace containing a
  thickening of order `n` is a thickening of order `n`.  The defining ideal can only shrink,
  and a power that already vanishes keeps vanishing.
* `AlgebraicGeometry.Space.exists_closedSubspace_definingIdealSheaf_eq_of_le`: the closed
  subspace cut out by a quasi-coherent sheaf of ideals contained in the defining ideal sheaf of
  a closed subspace contains that closed subspace.
* `AlgebraicGeometry.Space.exists_isNthOrderThickening_definingIdealSheaf_eq_of_le`: **the
  construction.**  A quasi-coherent sheaf of ideals inside the defining ideal sheaf of a
  thickening of order `n` cuts out a thickening of order `n` containing it.
* `AlgebraicGeometry.Space.exists_isFirstOrderThickening_definingIdealSheaf_eq_of_le`: the same
  for first-order thickenings, the case [Stacks Project, Tag 06D8] uses.

## Implementation notes

No `@[stacks]` attribute is placed by this file.  The statements are not any tag of the source:
they are the space-level replacement for a sentence inside the proof of Tag 06D8, and Tag 06D8
itself needs much more than this.

The order condition `AlgebraicGeometry.Space.IsNthOrderThickening` is stated chartwise as the
vanishing of a power of `AlgebraicGeometry.Space.definingIdealAt`, so the monotonicity argument
is a chartwise statement about ideals of a commutative ring and nothing sheaf-theoretic is
needed for it.  The surjectivity on points that a thickening also demands is transported along
`AlgebraicGeometry.Space.pointsMap_comp`, the inclusion of the smaller closed subspace
factoring through the larger one.

**Why both chartwise ideals are rewritten before the power lemma is applied.**
`AlgebraicGeometry.Space.definingIdealAt` is defined without a declared result type, from a
body whose `let`-bound ambient space and inclusion appear in the inferred type.  Unifying that
type against the `Submodule ?A ?A` of a general monotonicity lemma therefore has to evaluate
the definition, and that exhausts the heartbeat budget at `whnf` — on the
statement alone, with every spelling of the lemma: one type variable or two, the `Ideal`
spelling and the `Submodule` spelling, the hypothesis supplied first and the ideals generalized
to local constants first.  Rewriting both sides with
`AlgebraicGeometry.Space.definingIdealAt_eq_ker` first, so that the ideals are visibly ideals
of a ring of regular functions, makes the same step cost a fraction of a second; that is also
the idiom `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Order.lean` itself uses whenever it
computes with these powers.  Stating the inequality costs nothing — only instantiating a
general lemma at the unrewritten spelling does.

A `ClosedSubspaces` element is a subtype over a `Prop`, so the closed subspace rebuilt from a
subfunctor together with a freshly produced closedness proof is definitionally the original
one; the proofs below rely on that and do not transport along `Subtype.ext`.

## References

* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

/-- **A power of a sheaf of submodules is monotone in the submodule.**  `Submodule.mul_le` and
`Submodule.mul_mem_mul` applied along the recursion `M ^ (k + 1) = M ^ k * M` that defines the
power.

Stated for submodules of a commutative semiring over itself, which is what `Ideal` unfolds to,
because the consumers below are ideals of a ring of regular functions. -/
theorem Submodule.pow_le_pow_of_le {A : Type u} [CommSemiring A] {M N : Submodule A A}
    (h : M ≤ N) : ∀ k : ℕ, M ^ k ≤ N ^ k
  | 0 => le_rfl
  | k + 1 =>
      Submodule.mul_le.2 fun _ hm _ hn =>
        Submodule.mul_mem_mul (Submodule.pow_le_pow_of_le h k hm) (h hn)

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The comparison morphism of two nested closed subspaces of a thickening is surjective on
points.**  A point of the larger subfunctor and the point of the smaller one lying over its
image in the ambient space have the same image in the ambient space, and the inclusion of the
larger subfunctor is injective on points because it is a monomorphism.

This is the surjectivity clause of [Stacks Project, Tag 05ZK], part (1), for the inclusion
`G ⊆ H` rather than for `H ⊆ X`. -/
theorem surjective_pointsMap_homOfLe (G H : Subfunctor X.1) [Mono H.ι]
    (hG : IsThickening B S hS X G) (hGH : G ≤ H) :
    Function.Surjective (pointsMap B S hS G.toFunctor (Subfunctor.homOfLe hGH)) := by
  intro y
  obtain ⟨z, hz⟩ := hG.2 (pointsMap B S hS H.toFunctor H.ι y)
  refine ⟨z, pointsMap_injective_of_mono B S hS H.ι ?_⟩
  have hι : Subfunctor.homOfLe hGH ≫ H.ι = G.ι := Subfunctor.homOfLe_ι hGH
  have h := pointsMap_comp B S hS G.toFunctor (Subfunctor.homOfLe hGH) H.ι
  rw [hι] at h
  exact (congrFun h z).symm.trans hz

/-- **A power of the defining ideal that vanishes for a closed subspace vanishes for every
larger one.**  The defining ideal of the larger closed subspace is contained in that of the
smaller one, by the inclusion-reversal clause of [Stacks Project, Tag 03MB].

The two closed subspaces are given as a subfunctor together with a closedness proof, rather
than as elements of `AlgebraicGeometry.Space.ClosedSubspaces`, because that is the shape
`AlgebraicGeometry.Space.IsNthOrderThickening` presents its order condition in. -/
theorem definingIdealAt_pow_eq_bot_of_le {n : ℕ} (G H : Subfunctor X.1)
    (hG : IsClosedSubspace B S hS G) (hH : IsClosedSubspace B S hS H) (hGH : G ≤ H)
    (h : ∀ U : SmallEtale B S hS X.1,
      definingIdealAt B S hS X ⟨G, hG⟩ (op U) ^ (n + 1) = ⊥)
    (U : SmallEtale B S hS X.1) :
    definingIdealAt B S hS X ⟨H, hH⟩ (op U) ^ (n + 1) = ⊥ := by
  have hle := definingIdealAt_antitone B S hS X ⟨G, hG⟩ ⟨H, hH⟩ hGH U
  have hb := h U
  rw [definingIdealAt_eq_ker B S hS X ⟨H, hH⟩ U] at hle ⊢
  rw [definingIdealAt_eq_ker B S hS X ⟨G, hG⟩ U] at hle hb
  exact le_antisymm ((Submodule.pow_le_pow_of_le hle (n + 1)).trans hb.le) bot_le

/-- **A closed subspace containing a thickening of order `n` is a thickening of order `n`.** -/
theorem isNthOrderThickening_of_le {n : ℕ} (G H : Subfunctor X.1)
    (hH : IsClosedSubspace B S hS H)
    (hG : IsNthOrderThickening B S hS n X G) (hGH : G ≤ H) :
    IsNthOrderThickening B S hS n X H :=
  ⟨isThickening_of_le B S hS X hG.1 hH hGH,
    definingIdealAt_pow_eq_bot_of_le B S hS X G H hG.1.1 hH hGH hG.2⟩

/-- **A quasi-coherent sheaf of ideals inside the defining ideal sheaf of a closed subspace cuts
out a closed subspace containing it.**  The subspace is produced by the surjectivity half of
[Stacks Project, Tag 03MB], and the containment is its injectivity half read backwards. -/
theorem exists_closedSubspace_definingIdealSheaf_eq_of_le (Z : ClosedSubspaces B S hS X.1)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite)
    (hNZ : N ≤ definingIdealSheaf B S hS X Z) :
    ∃ Z' : ClosedSubspaces B S hS X.1,
      definingIdealSheaf B S hS X Z' = N ∧ Z.1 ≤ Z'.1 := by
  obtain ⟨Z', hZ'⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X N hN
  refine ⟨Z', hZ', le_of_definingIdealSheaf_le B S hS X Z Z' ?_⟩
  rw [hZ']
  exact hNZ

/-- **The subspace cut out by a quasi-coherent sub-ideal of a thickening of order `n`.**  Let
`Z ⊆ X` be a thickening of order `n` and let `N ⊆ 𝓘_Z` be a quasi-coherent sheaf of ideals
contained in its defining ideal sheaf.  Then `N` is the defining ideal sheaf of a closed
subspace `Z' ⊆ X` which contains `Z` and is itself a thickening of order `n`.

This is the space-level replacement for the passage to a closed subscheme of a scheme in the
proof of [Stacks Project, Tag 06D8]. -/
theorem exists_isNthOrderThickening_definingIdealSheaf_eq_of_le {n : ℕ}
    (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsNthOrderThickening B S hS n X Z.1)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite)
    (hNZ : N ≤ definingIdealSheaf B S hS X Z) :
    ∃ Z' : ClosedSubspaces B S hS X.1,
      definingIdealSheaf B S hS X Z' = N ∧ Z.1 ≤ Z'.1 ∧
        IsNthOrderThickening B S hS n X Z'.1 := by
  obtain ⟨Z', hN', hle⟩ :=
    exists_closedSubspace_definingIdealSheaf_eq_of_le B S hS X Z N hN hNZ
  exact ⟨Z', hN', hle, isNthOrderThickening_of_le B S hS X Z.1 Z'.1 Z'.2 hZ hle⟩

/-- **The subspace cut out by a quasi-coherent sub-ideal of a first-order thickening.**  The
case `n = 1` of `AlgebraicGeometry.Space.exists_isNthOrderThickening_definingIdealSheaf_eq_of_le`,
which is the one the proof of [Stacks Project, Tag 06D8] uses: there `Z ⊆ X` is the universal
first-order thickening of `Z` over `X'` and `N` is the summand `𝒞_{Z/X}` of its defining ideal
sheaf. -/
theorem exists_isFirstOrderThickening_definingIdealSheaf_eq_of_le
    (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite)
    (hNZ : N ≤ definingIdealSheaf B S hS X Z) :
    ∃ Z' : ClosedSubspaces B S hS X.1,
      definingIdealSheaf B S hS X Z' = N ∧ Z.1 ≤ Z'.1 ∧
        IsFirstOrderThickening B S hS X Z'.1 :=
  exists_isNthOrderThickening_definingIdealSheaf_eq_of_le B S hS X Z hZ N hN hNZ

end AlgebraicGeometry.Space

end
