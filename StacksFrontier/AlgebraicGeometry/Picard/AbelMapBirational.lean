module

public import StacksFrontier.AlgebraicGeometry.Divisors.Modification.InvertibleFiltration
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericStalkCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# Clause (6) of Tag 0BA0: the Abel map in degree `g` is birational

Let `k` be a separably closed field and let `X` be a smooth projective curve of genus `g` over
`k`. Clause (6) of [Stacks, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0) asserts that the
morphism

`γ_g : Hilb^g_{X/k} ⟶ Pic^g_{X/k}`

of clause (4) is birational.

The source proves it in one sentence: *"Our proof of the representability of the Picard functor
of `X/k` in Proposition 0B9Z and Lemma 0B9S shows that `γ_g` induces an open immersion on a
nonempty open of `Hilb^g_{X/k}`."* Both schemes are varieties, hence irreducible, and a nonempty
open of an irreducible scheme is dense; so `γ_g` restricts to an isomorphism between dense opens,
which is birationality.

That last implication is what is proved here, for an arbitrary morphism of irreducible schemes:
an isomorphism onto an open of the target, defined on a nonempty open of the source, makes the
morphism birational — both in the morphism sense of
`AlgebraicGeometry.IsBirational` ([Stacks, Tag 01RO]) and in the sense that source and target are
birational over the base ([Stacks, Tag 0A20] (2)).

## Main results

* `AlgebraicGeometry.isBirational_of_isOpenImmersion_ι_comp`: **Tag 0BA0, clause (6)**, in the
  morphism spelling `AlgebraicGeometry.IsBirational`.
* `AlgebraicGeometry.birationalOver_of_isOpenImmersion_ι_comp`: **Tag 0BA0, clause (6)**, in the
  spelling `AlgebraicGeometry.Scheme.BirationalOver` of the two schemes over their common base.

## What is carried, and why

Neither `Hilb^d_{X/k}` nor `Pic^d_{X/k}` is available as a scheme in this library: the first is
the representability of the Hilbert functor of points, [Stacks, Tag 0B97], carried as a
hypothesis wherever it is used (`AlgebraicGeometry.RepresentsHilbertFunctorOfRank`,
`AlgebraicGeometry.exists_representsHilbertFunctorOfRank_of_isAffine`), and the second is the
representability of the Picard functor, [Stacks, Tag 0B9Z], which the library does not have at
all — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Picard/DegreeAtLeastGenus.lean`. So the two schemes and the
morphism `γ_g` of clause (4) between them are *carried*: they appear below as two irreducible
schemes `H`, `P` and a morphism `γ : H ⟶ P`, exactly as the degree decomposition of clause (1) is
carried in `StacksFrontier/AlgebraicGeometry/GroupScheme/Subgroups/Clopen.lean` for clause (3).

Carried alongside them is the source's own input, the open immersion on a nonempty open:
`U : H.Opens` with `Nonempty U` and `IsOpenImmersion (U.ι ≫ γ)`. This is the sentence of the
source quoted above, which the library cannot discharge because it is read off the *proof* of Tag
0B9Z. Nothing here asserts that such a `U` exists.

These results are therefore **conditional**: they say that `γ_g` is birational *given* the two
schemes, the morphism, and the nonempty open on which it is an open immersion. The irreducibility
of `H` and `P` is not a carry in the same sense — it is part of clause (1), which makes
`Pic^d_{X/k}` a variety, and of Tag 0B9H, which makes `Hilb^d_{X/k}` a smooth variety
(`AlgebraicGeometry.smoothOfRelativeDimension_of_represents`); but since the schemes themselves
are hypotheses, so is their irreducibility.

Surjectivity of `γ_g` — clause (5) at `d = g`, proved on `k`-points as
`AlgebraicGeometry.exists_isEffectiveCartierDivisor_of_genus_le_invertibleCurveDegree` — is *not*
needed: dominance of `U.ι ≫ γ` already follows from irreducibility of `P`, its range being a
nonempty open.

## Implementation notes

The degree `g` does not appear below. It enters clause (6) only through the carried hypotheses:
the source establishes the open immersion on a nonempty open for `d = g` and for no other degree,
and once that is granted the birationality argument is insensitive to the degree. Writing `d = g`
into the statement would leave it unused, which is why it is recorded here instead.

The first result reuses `Stacks.Divisors.isBirational_of_isOpenImmersion_factorization`, which
already proves birationality of a morphism through which a dominant open immersion factors; the
second reuses `AlgebraicGeometry.birationalOver_iff_exists_nonempty_open_iso`, the irreducible
case of [Stacks, Tag 0BAD]. Dominance of an open immersion with nonempty source into an
irreducible scheme is one line and is taken inline, as at
`StacksFrontier/AlgebraicGeometry/Divisors/Modification/InvertibleFiltration.lean`; the named form is
`Stacks.Chow.isDominant_of_isOpenImmersion'`, whose module is not imported here.

The base of the second result is an arbitrary scheme rather than `Spec k`; the tag's case is
`S = Spec k`, and nothing in the argument uses the base.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 01RO](https://stacks.math.columbia.edu/tag/01RO)
* [Stacks Project, Tag 0A20](https://stacks.math.columbia.edu/tag/0A20)
* [Stacks Project, Tag 0BAD](https://stacks.math.columbia.edu/tag/0BAD)
* [Stacks Project, Tag 0B97](https://stacks.math.columbia.edu/tag/0B97)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0B9H](https://stacks.math.columbia.edu/tag/0B9H)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {H P : Scheme.{u}} [IrreducibleSpace H] [IrreducibleSpace P]

/-- An open immersion with nonempty source into an irreducible scheme is dominant. -/
private theorem isDominant_of_isOpenImmersion_of_nonempty {X : Scheme.{u}} [Nonempty X]
    (f : X ⟶ P) [IsOpenImmersion f] : IsDominant f :=
  ⟨f.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

/-- **Stacks Project, Tag 0BA0, clause (6).** Let `γ : H ⟶ P` be a morphism of irreducible
schemes — the Abel map `γ_g : Hilb^g_{X/k} ⟶ Pic^g_{X/k}` of clause (4) — and let `U` be a
nonempty open of `H` on which `γ` is an open immersion. Then `γ` is birational.

Both `U ⟶ H` and `U ⟶ P` are open immersions with nonempty source into an irreducible scheme,
hence dominant; so they carry the generic point of `U` to the generic points of `H` and `P` and
`γ` matches those, inducing an isomorphism on the local ring there.

The two schemes, the morphism and the open are hypotheses, not conclusions: `Hilb^g_{X/k}` and
`Pic^g_{X/k}` are the representability of [Stacks, Tag 0B97] and [Stacks, Tag 0B9Z], which this
library does not have, and the open immersion on a nonempty open is read off the proof of the
latter.

This is a partial step towards [Stacks, Tag 0BA0], which is registered on its full statement. -/
@[ega "I 6.5.5" "necessity in (ii)"]
theorem isBirational_of_isOpenImmersion_ι_comp (γ : H ⟶ P) (U : H.Opens) [Nonempty U]
    [IsOpenImmersion (U.ι ≫ γ)] : IsBirational γ :=
  have : IrreducibleSpace U.toScheme :=
    have hpre : IsPreirreducible (U : Set H) :=
      (PreirreducibleSpace.isPreirreducible_univ (X := (H : Type u))).open_subset U.2
        (Set.subset_univ _)
    let x := Classical.arbitrary (α := (U : Type u))
    isIrreducible_iff_irreducibleSpace.mp ⟨⟨x.1, x.2⟩, hpre⟩
  have := isDominant_of_isOpenImmersion_of_nonempty U.ι
  have := isDominant_of_isOpenImmersion_of_nonempty (U.ι ≫ γ)
  Stacks.Divisors.isBirational_of_isOpenImmersion_factorization U.ι (U.ι ≫ γ) γ rfl

/-- **Stacks Project, Tag 0BA0, clause (6)**, in the spelling of [Stacks, Tag 0A20] (2): the
source and target of the Abel map are birational over their common base.

The isomorphism of dense opens is `γ` restricted to `U`, with target the open image of `U`: both
opens are nonempty, hence dense by irreducibility, and the isomorphism lies over the base because
`γ` does. The hypotheses are those of
`AlgebraicGeometry.isBirational_of_isOpenImmersion_ι_comp`, together with the two structure
morphisms; the base is arbitrary, the tag's case being `S = Spec k`.

This is a partial step towards [Stacks, Tag 0BA0], which is registered on its full statement. -/
theorem birationalOver_of_isOpenImmersion_ι_comp (γ : H ⟶ P) (U : H.Opens) [Nonempty U]
    [IsOpenImmersion (U.ι ≫ γ)] {S : Scheme.{u}} (sH : H ⟶ S) (sP : P ⟶ S)
    (hγ : γ ≫ sP = sH) : Scheme.BirationalOver sH sP := by
  obtain ⟨x⟩ := ‹Nonempty U›
  refine (birationalOver_iff_exists_nonempty_open_iso sH sP).2
    ⟨U, (U.ι ≫ γ).opensRange, ⟨x.1, x.2⟩, ⟨(U.ι ≫ γ).base x, x, rfl⟩,
      (U.ι ≫ γ).isoOpensRange, ?_⟩
  rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Category.assoc, hγ]

end AlgebraicGeometry

end
