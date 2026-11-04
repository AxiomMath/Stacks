module

public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementChow
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ChowQcqs.Basic

/-!
# Consuming Chow's lemma in Stacks 0DBF part (2)

Stacks 0DBF part (2) is proved in
`StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementChow` from the single hypothesis

```
∀ (X Y : Scheme) (f : X ⟶ Y), IsAffine Y → IsProper f → HasChowModification f
```

which is Chow's lemma (Stacks 0202) for a proper morphism onto an affine scheme. Stacks 0202
itself, however, is stated for a *separated, finite-type, quasi-compact* morphism over a
*quasi-compact, quasi-separated* base, and its conclusion is phrased in terms of
`AlgebraicGeometry.projectiveSpaceOver` rather than `AlgebraicGeometry.ProjectiveSpace`, which
is what `AlgebraicGeometry.HasChowModification` is written with. This file closes the two
remaining gaps between the two phrasings and then plugs in Stacks 0202, which this development
proves as `AlgebraicGeometry.hasChowModification_of_compactSpace_quasiSeparatedSpace`, to obtain
part (2) with no hypothesis.

The first gap is only apparent. This development carries two constructions of the integral model
of projective space — `AlgebraicGeometry.ProjectiveSpaceZ` and
`AlgebraicGeometry.projectiveSpaceAtUniverse` — in two files that do not refer to each other,
and consequently two constructions of projective space over a base. They unfold to the same
`Proj`, so the two phrasings of the conclusion of Chow's lemma are definitionally equal;
`AlgebraicGeometry.hasChowModification_iff_projectiveSpaceOver` records this, since it is not
otherwise visible from either file.

The second gap is a genuine, if small, implication: a proper morphism onto an affine scheme is
separated, of finite type and quasi-compact, and an affine scheme is quasi-compact and
quasi-separated, so all five hypotheses of Stacks 0202 hold at the point where part (2) uses it.

## Main definitions

* `AlgebraicGeometry.ChowLemmaStatement`: Chow's lemma exactly as Stacks 0202 states it, as a
  proposition, so that the two results below can take it as a hypothesis.

## Main results

* `AlgebraicGeometry.hasChowModification_iff_projectiveSpaceOver`: the conclusion of Chow's
  lemma phrased with `AlgebraicGeometry.projectiveSpaceOver` is the conclusion phrased with
  `AlgebraicGeometry.ProjectiveSpace`, i.e. `AlgebraicGeometry.HasChowModification`.
* `AlgebraicGeometry.ChowLemmaStatement.hasChowModification_of_isProper`: Chow's lemma as
  Stacks 0202 states it implies Chow's lemma for a proper morphism onto an affine scheme, which
  is the form in which Stacks 0DBF part (2) consumes it.
* `AlgebraicGeometry.exists_standardPHCovering_refinement_bind_of_chowLemmaStatement`:
  Stacks 0DBF part (2), with Chow's lemma as Stacks 0202 states it as an explicit hypothesis.
* `AlgebraicGeometry.chowLemmaStatement`: that hypothesis, discharged.
* `AlgebraicGeometry.exists_standardPHCovering_refinement_bind`: Stacks 0DBF part (2).

## Implementation notes

`AlgebraicGeometry.ChowLemmaStatement` binds the five hypotheses of Stacks 0202 as instance
arguments, in the order and shape Stacks 0202 uses, so that a proof of Stacks 0202 produces a
term of this type by `fun f => ‹Stacks 0202› f`.

Only `AlgebraicGeometry.exists_standardPHCovering_refinement_bind` carries the Stacks 0DBF
attribute. The hypothesis-carrying forms above it are kept because they are what the proof
factors through, but their hypothesis is redundant, and so is the one on
`AlgebraicGeometry.exists_standardPHCovering_refinement_bind_of_chowLemma` and
`AlgebraicGeometry.exists_standardPHCovering_refinement_bind_of_extension`.

## References

* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- **Chow's lemma, as Stacks 0202 states it**: every separated, quasi-compact morphism of finite
type over a quasi-compact, quasi-separated base admits a Chow modification.

The hypotheses are bound as instance arguments in the shape Stacks 0202 uses, so a proof of
Stacks 0202 yields a term of this type by applying it to the morphism; `chowLemmaStatement` is
that term. -/
def ChowLemmaStatement : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f], HasChowModification f

/-- **The two phrasings of the conclusion of Chow's lemma agree.** Stacks 0202 produces an
immersion into `AlgebraicGeometry.projectiveSpaceOver n S`, whereas
`AlgebraicGeometry.HasChowModification` asks for an immersion into
`AlgebraicGeometry.ProjectiveSpace n S`; the two schemes are the same pullback of the same
`Proj`, and the structure morphism of `AlgebraicGeometry.ProjectiveSpace n S` is the first
pullback projection by `AlgebraicGeometry.ProjectiveSpace.over_hom`, so the two statements are
definitionally equal.

Neither of the two files defining these schemes mentions the other, so this equality is not
visible from either; it is recorded here because it is what lets a proof of Stacks 0202 be used
for `AlgebraicGeometry.HasChowModification` without transport along an isomorphism. -/
theorem hasChowModification_iff_projectiveSpaceOver {X S : Scheme.{u}} (f : X ⟶ S) :
    HasChowModification f ↔
      ∃ (n : ℕ) (X' : Scheme.{u}) (π : X' ⟶ X) (i : X' ⟶ projectiveSpaceOver n S),
        IsProper π ∧ Surjective π ∧ IsImmersion i ∧
          π ≫ f = i ≫ pullback.fst (terminal.from S)
            (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
  Iff.rfl

/-- **Chow's lemma holds for a proper morphism onto an affine scheme.** This is the form in which
Stacks 0DBF part (2) consumes Chow's lemma, and it discharges all five hypotheses of
Stacks 0202: a proper morphism is separated, locally of finite type and quasi-compact, and an
affine scheme is a compact and quasi-separated space. -/
theorem ChowLemmaStatement.hasChowModification_of_isProper (hchow : ChowLemmaStatement.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsProper f] : HasChowModification f :=
  hchow f

/-- **Stacks Project, Tag 0DBF, part (2), granted Chow's lemma as Stacks 0202 states it.** The
composite `E.bind F` of a standard ph covering `E` of an affine scheme `T` with standard ph
coverings `F i` of its members has a refinement which is a standard ph covering of `T`.

This is `AlgebraicGeometry.exists_standardPHCovering_refinement_bind_of_chowLemma` with its
hypothesis replaced by `AlgebraicGeometry.ChowLemmaStatement`, which is Stacks 0202 verbatim.
The replacement is a *strengthening of the hypothesis*, since Chow's lemma for separated
finite-type quasi-compact morphisms over a quasi-compact quasi-separated base implies Chow's
lemma for proper morphisms onto affine schemes but not conversely; the point of the statement is
not that it is a sharper theorem — it is not — but that its hypothesis is the proposition a
proof of Stacks 0202 produces, so nothing remains to be checked when Stacks 0202 is available.

This statement carries no Stacks 0DBF attribute, since its hypothesis is redundant: the
unconditional part (2) is `exists_standardPHCovering_refinement_bind` below. -/
theorem exists_standardPHCovering_refinement_bind_of_chowLemmaStatement
    (hchow : ChowLemmaStatement.{u}) {T : Scheme.{u}} [IsAffine T]
    (E : PreZeroHypercover.{v} T) (hE : StandardPHCovering E.f)
    (F : ∀ i, PreZeroHypercover.{w} (E.X i))
    (hF : ∀ i, @StandardPHCovering (F i).I₀ (E.X i) (hE.isAffine i) (F i).X (F i).f) :
    ∃ G : PreZeroHypercover.{max v w} T,
      StandardPHCovering G.f ∧ Nonempty (G.Hom (E.bind F)) :=
  exists_standardPHCovering_refinement_bind_of_chowLemma E hE F hF
    fun _ _ f _ _ => hchow.hasChowModification_of_isProper f

/-- **Chow's lemma, as Stacks 0202 states it, is a theorem of this development.**
`AlgebraicGeometry.hasChowModification_of_compactSpace_quasiSeparatedSpace` is Stacks 0202 with
exactly the binders of `AlgebraicGeometry.ChowLemmaStatement`. -/
theorem chowLemmaStatement : ChowLemmaStatement.{u} :=
  fun f => hasChowModification_of_compactSpace_quasiSeparatedSpace f

/-- **Stacks Project, Tag 0DBF, part (2).** Let `T` be an affine scheme, let `E` be a standard
ph covering of `T`, and for each member `E.X i` let `F i` be a standard ph covering of it. Then
the composite family `E.bind F`, whose members are the `(F i).X j ⟶ E.X i ⟶ T`, has a
refinement by a standard ph covering of `T`.

This consumes Chow's lemma (Stacks 0202) through `AlgebraicGeometry.chowLemmaStatement`. -/
@[stacks 0DBF "part (2)"]
theorem exists_standardPHCovering_refinement_bind {T : Scheme.{u}} [IsAffine T]
    (E : PreZeroHypercover.{v} T) (hE : StandardPHCovering E.f)
    (F : ∀ i, PreZeroHypercover.{w} (E.X i))
    (hF : ∀ i, @StandardPHCovering (F i).I₀ (E.X i) (hE.isAffine i) (F i).X (F i).f) :
    ∃ G : PreZeroHypercover.{max v w} T,
      StandardPHCovering G.f ∧ Nonempty (G.Hom (E.bind F)) :=
  exists_standardPHCovering_refinement_bind_of_chowLemmaStatement chowLemmaStatement E hE F hF

end AlgebraicGeometry

end
