module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation

/-!
# Implications between the types of affine formal algebraic space

Stacks 0AID singles out five types of McQuillan affine formal algebraic space by a condition
on the weakly admissible topological ring presenting it: classical, weakly adic, adic, adic\*
and Noetherian. Stacks 0AIK records the implications between them, together with the
implications relating them to countable indexedness:

1. Noetherian implies adic\*;
2. adic\* implies adic;
3. adic implies weakly adic;
4. weakly adic implies classical;
5. weakly adic implies countably indexed;
6. countably indexed implies McQuillan.

This file proves items (1)-(5). Items (1)-(4) are the corresponding implications between the
types of linearly topologized ring, read through a ring presenting `X`: in a Noetherian ring
every ideal — in particular an ideal of definition — is finitely generated, adic\* is adic with
an extra condition, an adic ring is weakly adic, and a weakly adic ring is admissible.

Item (5) is the argument of the source. A weakly adic ring `A` has a countable fundamental
system of open ideals, namely the closures of the powers of a single ideal; intersecting them
with one weak ideal of definition of `A` makes them weak ideals of definition, still cofinal.
The resulting monotone sequence is therefore a final functor into the index of the canonical
weak-ideal presentation of `X`, so restricting that presentation along it presents `X` as the
colimit of a sequence of affine schemes and thickenings.

Item (6) is in `StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan`.

## Main results

* `AlgebraicGeometry.FormalSpace.isAdicStar_of_isNoetherian`,
  `AlgebraicGeometry.FormalSpace.isAdic_of_isAdicStar`,
  `AlgebraicGeometry.FormalSpace.isWeaklyAdic_of_isAdic` and
  `AlgebraicGeometry.FormalSpace.isClassical_of_isWeaklyAdic`: items (1)-(4).
* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isWeaklyAdic`: item (5).

## Implementation notes

The five predicates of Stacks 0AID all contain the McQuillan condition
`AlgebraicGeometry.FormalSpace.HasSomeSurjectivePresentation`, which already contains
affineness, so none of these statements needs a separate hypothesis that `X` is an affine
formal algebraic space; in item (5) that is why the conclusion is the bare presentation
condition `AlgebraicGeometry.IsCountablyIndexed` of Stacks 0AIJ.

Each predicate of Stacks 0AID quantifies existentially over a presenting ring, and items
(1)-(4) keep the ring supplied by the hypothesis: the conditions on the ring are what weaken,
not the ring.

## References

* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0GXF](https://stacks.math.columbia.edu/tag/0GXF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AIK, item (1).** A Noetherian affine formal algebraic space is adic\*: its
presenting ring is adic, and an ideal of definition of a Noetherian ring is finitely
generated. -/
@[stacks 0AIK "noetherian_adic_star"]
theorem isAdicStar_of_isNoetherian {X : FppfSheaf B S hS} (hX : IsNoetherian B S hS X) :
    IsAdicStar B S hS X := by
  obtain ⟨hSome, A, hCR, hTS, hTR, hLT, hpres, hNoeth, hAdic⟩ := hX
  obtain ⟨I, hIdef, -⟩ := hAdic.1
  have : _root_.IsNoetherian A A := isNoetherianRing_iff.mp hNoeth
  exact ⟨hSome, A, hCR, hTS, hTR, hLT, hpres, hAdic, I, hIdef,
    _root_.IsNoetherian.noetherian (R := A) (M := A) I⟩

/-- **Stacks 0AIK, item (2).** An adic\* affine formal algebraic space is adic: adic\* is
adicness of the presenting ring together with the extra demand that some ideal of definition
be finitely generated. -/
@[stacks 0AIK "adic_star_adic"]
theorem isAdic_of_isAdicStar {X : FppfSheaf B S hS} (hX : IsAdicStar B S hS X) :
    IsAdic B S hS X := by
  obtain ⟨hSome, A, hCR, hTS, hTR, hLT, hpres, hAdic, -⟩ := hX
  exact ⟨hSome, A, hCR, hTS, hTR, hLT, hpres, hAdic⟩

/-- **Stacks 0AIK, item (3).** An adic affine formal algebraic space is weakly adic, because
an adic linearly topologized ring is weakly adic. -/
@[stacks 0AIK "adic_weakly_adic"]
theorem isWeaklyAdic_of_isAdic {X : FppfSheaf B S hS} (hX : IsAdic B S hS X) :
    IsWeaklyAdic B S hS X := by
  obtain ⟨hSome, A, hCR, hTS, hTR, hLT, hpres, hAdic⟩ := hX
  exact ⟨hSome, A, hCR, hTS, hTR, hLT, hpres, TopologicalRing.isWeaklyAdic_of_isAdic A hAdic⟩

/-- **Stacks 0AIK, item (4).** A weakly adic affine formal algebraic space is classical,
because a weakly adic linearly topologized ring is admissible (Stacks 0GXF). -/
@[stacks 0AIK "weakly_adic_classical"]
theorem isClassical_of_isWeaklyAdic {X : FppfSheaf B S hS} (hX : IsWeaklyAdic B S hS X) :
    IsClassical B S hS X := by
  obtain ⟨hSome, A, hCR, hTS, hTR, hLT, hpres, hWAdic⟩ := hX
  have : TopologicalRing.IsWeaklyAdic A := hWAdic
  exact ⟨hSome, A, hCR, hTS, hTR, hLT, hpres,
    TopologicalRing.isAdmissible_of_isWeaklyAdic A⟩

/-- **Stacks 0AIK, item (5).** A weakly adic affine formal algebraic space is countably
indexed.

Let `A` be the presenting ring, `W` one of its weak ideals of definition, and `I` an ideal
whose closed powers are open and form a fundamental system of neighbourhoods of `0`, which is
what weak adicness of `A` provides. The ideals `W ⊓ (I ^ n)‾` are then weak ideals of
definition, they decrease in `n`, and every weak ideal of definition contains one of them,
being open. So the sequence they form is a final functor into the index of the canonical
weak-ideal presentation of `X`, and restricting that presentation along it exhibits `X` as the
colimit of a sequence of affine schemes whose transition morphisms are thickenings. -/
@[stacks 0AIK "weakly_adic_countable"]
theorem isCountablyIndexed_of_isWeaklyAdic {X : FppfSheaf B S hS}
    (hX : IsWeaklyAdic B S hS X) : IsCountablyIndexed B S hS X := by
  obtain ⟨-, A, hCR, hTS, hTR, hLT, ⟨hWA, ⟨P⟩⟩, hWAdic⟩ := hX
  have : TopologicalRing.IsWeaklyAdic A := hWAdic
  obtain ⟨I, hIopen, hIbasis⟩ := TopologicalRing.IsWeaklyPreAdic.exists_ideal (A := A)
  obtain ⟨W, hW⟩ := hWA.1
  let c : ℕ → WeakIdeals A := fun n ↦
    ⟨W ⊓ (I ^ n).topologicalClosure,
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right hW (hIopen n)⟩
  have hc : Monotone c := by
    intro n m hnm
    change (c m).1 ≤ (c n).1
    exact inf_le_inf_left W
      (Submodule.topologicalClosure_mono (Ideal.pow_le_pow_right hnm))
  let e := hc.functor
  have hcof : ∀ K : WeakIdeals A, ∃ n : ℕ, K ≤ c n := by
    intro K
    obtain ⟨n, -, hn⟩ := hIbasis.mem_iff.mp (K.2.1.mem_nhds K.1.zero_mem)
    refine ⟨n, ?_⟩
    change (c n).1 ≤ K.1
    exact le_trans inf_le_right fun _ hx ↦ hn hx
  let _ : Functor.Final e := hc.final_functor_iff.mpr hcof
  refine ⟨e ⋙ P.diagram, fun ⦃_ _⦄ f ↦ ?_, ?_⟩
  · exact weak_quotient_transition_isThickening B S hS A X P (e.map f)
  · exact ⟨P.colimitIso ≪≫ (Functor.Final.colimitIso e _).symm⟩

end AlgebraicGeometry.FormalSpace

end
