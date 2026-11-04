module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Chow groups decompose along a decomposition into open and closed pieces

Let `X` be a scheme locally of finite type over the base scheme of chapter 42 of the Stacks
Project and let `X = \coprod_{i \in I} X_i` be a decomposition into open and closed subschemes.
The proofs of Stacks 0FDZ and Stacks 02UC both use

  `CH_k(X) = \prod_{i \in I} CH_k(X_i)`

and dismiss it as immediate from the definitions. At the level of *cycles* it is, and that is
proved unconditionally in `StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Cycles` as
`Stacks.Chow.cycleGroupClopenEquiv`. At the level of *Chow groups* one more thing is needed,
namely that the subgroup of cycles rationally equivalent to zero decomposes as well. That is
carried here as the hypothesis `Stacks.Chow.RationalEquivalenceDecomposes`, exactly as Stacks
02S1 and Stacks 02S2 are carried as hypotheses elsewhere in this development, and
`Stacks.Chow.chowGroupClopenEquiv` derives the product decomposition of the Chow groups from it.

Two unconditional facts about a piece of such a decomposition are proved along the way, because
both are needed by the proof of Stacks 0FDZ itself. First, the inclusion of a piece is a **closed
immersion** — it is an open immersion whose range is closed — hence proper, so cycles push forward
along it and Stacks 02S2 for that pushforward is the already-proved
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion` rather than
a hypothesis. Second, every integral closed subscheme of `X` lies in **exactly one** piece, which
is what partitions the generators of the group of cycles and hence the families of integral
subschemes that witness rational equivalence.

## Main definitions

* `Stacks.Chow.RationalEquivalenceDecomposes` — the assertion that a `k`-cycle is rationally
  equivalent to zero precisely when each of its restrictions to the pieces is.
* `Stacks.Chow.chowGroupClopenRestrict` — the induced map `A_k(X) ⟶ ∏_i A_k(X_i)`.
* `Stacks.Chow.chowGroupClopenEquiv` — the isomorphism `A_k(X) ≅ ∏_i A_k(X_i)`.

## Main results

* `Stacks.Chow.IsClopenDecomposition.isClosedImmersion_ι`,
  `Stacks.Chow.IsClopenDecomposition.isProper_ι` — the inclusion of a piece is a closed
  immersion, hence proper.
* `Stacks.Chow.IsClopenDecomposition.properPushforwardFactorsThroughRationalEquivalence_ι` —
  Stacks 02S2 holds unconditionally for the pushforward along the inclusion of a piece.
* `Stacks.Chow.IsClopenDecomposition.existsUnique_support_subset` — an integral closed subscheme
  of `X` is contained in exactly one piece.
* `Stacks.Chow.rationalEquivalenceDecomposes_mp` — the **forward** half of
  `Stacks.Chow.RationalEquivalenceDecomposes`, from Stacks 02S1 along the piece inclusions.
* `Stacks.Chow.chowGroupClopenRestrict_bijective` — the map on Chow groups is bijective.

## Implementation notes

### Exactly what `Stacks.Chow.RationalEquivalenceDecomposes` still needs

The **forward** half is not new mathematics. The projection to a piece is flat pullback along the
inclusion of that piece (`Stacks.Chow.cycleGroupOpensRestrict_eq_flatPullback`), so the assertion
that it preserves rational equivalence is Stacks 02S1 for an open immersion — the standing
hypothesis `Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalence` that this development
threads everywhere, instantiated at the piece inclusions. That reduction is
`Stacks.Chow.rationalEquivalenceDecomposes_mp`.

The **reverse** half is proved unconditionally. It is `Stacks.Chow.rationalEquivalenceDecomposes_mpr`
(`Chow/ChowToolkit/RationalEquivalenceFinsum.lean:198`), which takes **no hypothesis at all** —
not 02S2, not 02S1, not 02RZ. So `chowGroupClopenEquiv` follows from Stacks 02S1 at the piece
inclusions alone, i.e. from the standing
`Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalence` this development already threads
everywhere, and `Stacks.Chow.rationalEquivalenceDecomposes_of_flatPullbackFactors` packages
exactly that.

The reverse half rests on **Stacks 02RZ**
(`Stacks.Chow.rationallyEquivalentToZero_finsum_of_closedSupports`) rather than on transporting
data along isomorphisms piece by piece. Most of 02RZ is already in the library:
`Chow/CycleAdditivity.lean`'s `rationallyEquivalentToZero_finsum` is the whole
combinatorial half, via the carrier-remembering `IsRationallyEquivalentToZeroWithin`. The remaining
ingredient is that a pushforward along a closed immersion is witnessed *inside the
image* — visible in `ProperPushforwardChow/Reduction.lean`'s proof, whose conclusion merely
discards the carrier.

One restriction, and it is forced rather than chosen: the reverse half needs `I : Type u`, because
`IsRationallyEquivalentToZero` quantifies its witness index over `Type u` and the assembled
witness is a sigma over `I`. Level 1 (`cycleGroupClopenEquiv`) remains universe-free.

### The shape of the hypothesis

`Stacks.Chow.RationalEquivalenceDecomposes` is quantified over the cycle and is an `iff`, i.e. it
is the full statement that the subgroup of cycles rationally equivalent to zero is the preimage of
the product of those subgroups. Only the forward implication is needed to *construct*
`Stacks.Chow.chowGroupClopenRestrict`; the reverse is exactly its injectivity. Keeping both in one
hypothesis means a consumer that has established the decomposition of rational equivalence gets
the isomorphism, not merely a map.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u v

namespace Stacks.Chow

variable {X : Scheme.{u}} {I : Type v} {U : I → X.Opens}

/-! ### The inclusion of a piece -/

namespace IsClopenDecomposition

/-- The inclusion of a piece of a decomposition into open and closed subschemes is a **closed**
immersion: it is an open immersion, hence a preimmersion, and its range is the piece, which is
closed by `Stacks.Chow.IsClopenDecomposition.isClopen`. -/
@[ega "IV 4.9.6" "more general"]
theorem isClosedImmersion_ι (h : IsClopenDecomposition U) (i : I) :
    IsClosedImmersion (U i).ι :=
  IsClosedImmersion.of_isPreimmersion _ <| by
    rw [Scheme.Opens.range_ι]
    exact (h.isClopen i).1

/-- The inclusion of a piece of a decomposition into open and closed subschemes is proper, being a
closed immersion. So cycles push forward along it, by `Stacks.Chow.properPushforward`. -/
theorem isProper_ι (h : IsClopenDecomposition U) (i : I) : IsProper (U i).ι :=
  let := h.isClosedImmersion_ι i
  inferInstance

/-- **Stacks 02S2 for the inclusion of a piece.** Proper pushforward along the inclusion of a
piece of a decomposition into open and closed subschemes factors through rational equivalence,
unconditionally: the inclusion is a closed immersion, and Stacks 02S2 for closed immersions is
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`.

This is the map `(Y_{a(i)} → Y)_*` that the proof of Stacks 0FDZ applies to a cycle on a piece;
obtain the instance argument from `Stacks.Chow.IsClopenDecomposition.isProper_ι`. What that proof
then does with the resulting cycle — restrict it back to the pieces — is computed in
`StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.PiecePushforward`. -/
theorem properPushforwardFactorsThroughRationalEquivalence_ι (h : IsClopenDecomposition U)
    (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : I) [IsProper (U i).ι]
    (k : ℤ) :
    ProperPushforwardFactorsThroughRationalEquivalence C ((U i).ι ≫ f) f (U i).ι rfl k :=
  let := h.isClosedImmersion_ι i
  properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion (U i).ι C
    ((U i).ι ≫ f) f rfl k

/-- An integral closed subscheme of `X`, presented by its ideal sheaf, is contained in exactly one
piece of a decomposition into open and closed subschemes: its support is irreducible and nonempty,
being the range of the inclusion of an integral scheme.

This is what partitions the generators of the group of cycles, and the families of integral closed
subschemes witnessing rational equivalence, among the pieces. -/
theorem existsUnique_support_subset (h : IsClopenDecomposition U) (W : X.IdealSheafData)
    [IsIntegral W.subscheme] : ∃! i : I, (W.support : Set X) ⊆ (U i : Set X) := by
  have hirr : IsIrreducible (W.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ W.subschemeι.continuous.continuousOn
  exact h.existsUnique_isPreirreducible hirr.2 hirr.1

end IsClopenDecomposition

/-! ### Rational equivalence, and the decomposition of the Chow groups -/

/-- The assertion that rational equivalence decomposes along a decomposition of `X` into open and
closed subschemes: a `k`-cycle on `X` is rationally equivalent to zero precisely when each of its
restrictions to the pieces is.

Carried as a hypothesis; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.ChowGroup` for exactly what proving it
requires. The corresponding statement for cycles themselves needs no hypothesis: it is
`Stacks.Chow.cycleGroupClopenEquiv`. -/
def RationalEquivalenceDecomposes (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (h : IsClopenDecomposition U) (k : ℤ) : Prop :=
  ∀ c : CycleGroup C f k,
    c ∈ rationalEquivalences C f k ↔
      ∀ i, cycleGroupClopenEquiv C f h k c i ∈ rationalEquivalences C ((U i).ι ≫ f) k

/-- **The forward half of `Stacks.Chow.RationalEquivalenceDecomposes`, from Stacks 02S1 along the
piece inclusions.** A cycle rationally equivalent to zero restricts to one on each piece, because
the restriction is flat pullback along the inclusion of that piece.

So establishing `Stacks.Chow.RationalEquivalenceDecomposes` in full needs only the converse; see
the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.ChowGroup`. -/
theorem rationalEquivalenceDecomposes_mp (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (h : IsClopenDecomposition U) (k : ℤ)
    (hfac : ∀ i, FlatPullbackFactorsThroughRationalEquivalence C ((U i).ι ≫ f) f (U i).ι rfl 0
      (relativeDimension_opensι (U i)) k)
    {c : CycleGroup C f k} (hc : c ∈ rationalEquivalences C f k) (i : I) :
    cycleGroupClopenEquiv C f h k c i ∈ rationalEquivalences C ((U i).ι ≫ f) k :=
  cycleGroupOpensRestrict_mem_rationalEquivalences C f (U i) k (hfac i) hc

/-- The map `A_k(X) ⟶ ∏_i A_k(X_i)` induced by restriction of cycles to the pieces of a
decomposition of `X` into open and closed subschemes. -/
def chowGroupClopenRestrict (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (h : IsClopenDecomposition U) (k : ℤ)
    (hdec : RationalEquivalenceDecomposes C f h k) :
    chowGroup C f k →+ ∀ i, chowGroup C ((U i).ι ≫ f) k :=
  QuotientAddGroup.lift (rationalEquivalences C f k)
    (AddMonoidHom.pi fun i ↦
      (QuotientAddGroup.mk' (rationalEquivalences C ((U i).ι ≫ f) k)).comp
        (cycleGroupOpensRestrict C f (U i) k))
    fun c hc ↦ funext fun i ↦ (QuotientAddGroup.eq_zero_iff _).2 ((hdec c).mp hc i)

/-- The map `chowGroupClopenRestrict` sends the class of a cycle `c` to the family of classes of
its restrictions to the pieces. -/
@[simp]
theorem chowGroupClopenRestrict_mk (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (h : IsClopenDecomposition U) (k : ℤ)
    (hdec : RationalEquivalenceDecomposes C f h k) (c : CycleGroup C f k) (i : I) :
    chowGroupClopenRestrict C f h k hdec
        (QuotientAddGroup.mk' (rationalEquivalences C f k) c) i =
      QuotientAddGroup.mk' (rationalEquivalences C ((U i).ι ≫ f) k)
        (cycleGroupOpensRestrict C f (U i) k c) :=
  rfl

/-- **Chow groups decompose along a decomposition into open and closed subschemes**, granted that
rational equivalence does: the map `A_k(X) ⟶ ∏_i A_k(X_i)` is bijective.

Injectivity is the reverse implication of `Stacks.Chow.RationalEquivalenceDecomposes`;
surjectivity needs no hypothesis beyond the decomposition of cycles, since a family of classes is
hit by the class of the cycle glued from any family of representatives. -/
theorem chowGroupClopenRestrict_bijective (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (h : IsClopenDecomposition U) (k : ℤ)
    (hdec : RationalEquivalenceDecomposes C f h k) :
    Function.Bijective (chowGroupClopenRestrict C f h k hdec) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun α hα ↦ ?_, fun β ↦ ?_⟩
  · induction α using QuotientAddGroup.induction_on with
    | H c =>
      exact (QuotientAddGroup.eq_zero_iff c).2 ((hdec c).mpr fun i ↦
        (QuotientAddGroup.eq_zero_iff _).1 (congrFun hα i))
  · choose c hc using fun i ↦
      QuotientAddGroup.mk'_surjective (rationalEquivalences C ((U i).ι ≫ f) k) (β i)
    refine ⟨QuotientAddGroup.mk' (rationalEquivalences C f k)
      ((cycleGroupClopenEquiv C f h k).symm c), funext fun i ↦ ?_⟩
    rw [chowGroupClopenRestrict_mk, show cycleGroupOpensRestrict C f (U i) k
      ((cycleGroupClopenEquiv C f h k).symm c) = c i from
      congrFun ((cycleGroupClopenEquiv C f h k).apply_symm_apply c) i]
    exact hc i

/-- **Chow groups decompose along a decomposition into open and closed subschemes:**
`CH_k(X) = ∏_i CH_k(X_i)`, granted that rational equivalence decomposes.

This is the identity that the proofs of Stacks 0FDZ and Stacks 02UC use without comment. The
assemble map `Ψ` of Stacks 0FDZ is its inverse. -/
def chowGroupClopenEquiv (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (h : IsClopenDecomposition U) (k : ℤ)
    (hdec : RationalEquivalenceDecomposes C f h k) :
    chowGroup C f k ≃+ ∀ i, chowGroup C ((U i).ι ≫ f) k :=
  AddEquiv.ofBijective (chowGroupClopenRestrict C f h k hdec)
    (chowGroupClopenRestrict_bijective C f h k hdec)

/-- The underlying map of `chowGroupClopenEquiv` is `chowGroupClopenRestrict`. -/
@[simp]
theorem chowGroupClopenEquiv_apply (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (h : IsClopenDecomposition U) (k : ℤ)
    (hdec : RationalEquivalenceDecomposes C f h k) (α : chowGroup C f k) :
    chowGroupClopenEquiv C f h k hdec α = chowGroupClopenRestrict C f h k hdec α :=
  rfl

end Stacks.Chow

end
