module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DualTelescope
public import StacksFrontier.Algebra.DifferentialGraded.Module.Product
public import StacksCore.Tactic.StacksAttribute

/-! # The telescope of a tower of quotients, at the graded product

Let `(A, d)` be a differential graded algebra and let `I` be a right differential graded
`A`-module presented as the limit of a tower of quotients `⋯ → Q 1 → Q 0` whose transition maps
are admissible epimorphisms. This file states Stacks Tag 09KR as an *existence* statement: the
sequence

`0 → I → ∏ᵢ Q i → ∏ᵢ Q i → 0`

of differential graded `A`-modules exists and is admissible short exact, the first map being the
family of quotient maps and the second the identity minus the map induced by the transitions.

## Main results

* `DifferentialGradedModule.exists_isAdmissibleShortExact_uliftProduct`: Stacks Tag 09KR.

## Implementation notes

All of the mathematics is in `DifferentialGradedModule.exists_isAdmissibleShortExact_telescope`
(`Module/DualTelescope.lean`), which proves the same conclusion for *any* object `P` with maps
`π i : P ⟶ Q i` that are jointly injective and degreewise jointly surjective. That theorem
cannot carry the tag, because it takes the product as data and so asserts nothing about the
existence of the sequence; nothing could supply the data while the graded product was `private`.
Here the data is supplied by `DifferentialGradedModule.uliftProduct`, whose projections satisfy
the two hypotheses by `uliftProduct.eq_zero_of_π_eq_zero` and
`uliftProduct.exists_mem_grading`, and the tag goes on the resulting specialisation.

*Why the hypotheses are the tower and not a `PropertyIFiltration`.* Stacks 09KR takes a
filtration as in property (I) and uses exactly its conditions (1) and (2): that
`I = lim I/F_iI`, which is `hsep` together with `hcomplete`, and that the transition maps
`I/F_{i+1}I → I/F_iI` are admissible epimorphisms, which is `hadm`. Those are precisely the
hypotheses below, with `Q i = I/F_iI`. They are *not* available from
`DifferentialGradedModule.PropertyIFiltration`, which records condition (2) in the other of its
two inequivalent forms — that the inclusions `F_{i+1}I → F_iI` are admissible monomorphisms, see
the implementation notes of `Module/PropertyI.lean` — so a statement phrased over that structure
would be weaker than the tag, not stronger. Presenting the tower directly is therefore the
faithful reading, and what is left undone is only the construction of the quotient objects
`I/F_iI` themselves, which carries no information this lemma uses.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules all live in a single universe `u`, following the Stacks Tag 09JJ formalization.
The tower is indexed by `ℕ`, so its product is `uliftProduct`, the product over `ULift.{u} ℕ`.

## References

* [Stacks Project, Tag 09KR](https://stacks.math.columbia.edu/tag/09KR), and
  [Tag 09KL](https://stacks.math.columbia.edu/tag/09KL), of which it is the dual.
-/

@[expose] public section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- **Stacks 09KR.** *"Let `(A, d)` be a differential graded algebra. Let `I` be a differential
graded `A`-module. If `F_•` is a filtration as in property (I), then we obtain an admissible
short exact sequence `0 → I → ∏ I/F_iI → ∏ I/F_iI → 0` of differential graded `A`-modules."*

The filtration enters only through the tower of quotients `Q i = I/F_iI` it determines, together
with conditions (1) and (2) of property (I): the quotient maps `p i : I ⟶ Q i` are compatible
with the transitions `t i : Q (i + 1) ⟶ Q i` (`hp`), the transitions are admissible
epimorphisms (`hadm`, condition (2)), and `I = lim Q i`, which is injectivity of
`I → lim Q i` (`hsep`) together with its surjectivity in each degree (`hcomplete`, the limit
being formed in differential graded modules and hence degreewise).

The product is `DifferentialGradedModule.uliftProduct Q`, the first map is the family of
quotient maps and the second is the identity minus the map induced by the transitions; each is
pinned down by what it does on the projections. -/
@[stacks 09KR]
theorem exists_isAdmissibleShortExact_uliftProduct {I : DifferentialGradedModule A}
    (Q : ℕ → DifferentialGradedModule A) (p : ∀ i, I ⟶ Q i) (t : ∀ i, Q (i + 1) ⟶ Q i)
    (hp : ∀ (i : ℕ) (x : I.M), (t i).toFun ((p (i + 1)).toFun x) = (p i).toFun x)
    (hadm : ∀ i, IsAdmissibleEpi (t i))
    (hsep : ∀ x : I.M, (∀ i, (p i).toFun x = 0) → x = 0)
    (hcomplete : ∀ (n : ℤ) (q : ∀ i, (Q i).M), (∀ i, q i ∈ (Q i).grading n) →
      (∀ i, (t i).toFun (q (i + 1)) = q i) → ∃ y ∈ I.grading n, ∀ i, (p i).toFun y = q i) :
    ∃ (α : I ⟶ uliftProduct Q) (β : uliftProduct Q ⟶ uliftProduct Q),
      (∀ (i : ℕ) (x : I.M), (uliftProduct.π Q i).toFun (α.toFun x) = (p i).toFun x) ∧
      (∀ (i : ℕ) (y : (uliftProduct Q).M), (uliftProduct.π Q i).toFun (β.toFun y)
        = (uliftProduct.π Q i).toFun y - (t i).toFun ((uliftProduct.π Q (i + 1)).toFun y)) ∧
      IsAdmissibleShortExact α β :=
  exists_isAdmissibleShortExact_telescope Q p t (uliftProduct.π Q) hp hadm hsep hcomplete
    (uliftProduct.eq_zero_of_π_eq_zero Q) (uliftProduct.exists_mem_grading Q)

end DifferentialGradedModule

end
