module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport

/-!
# Algebraic stacks presented by a smooth groupoid in algebraic spaces

Let `S` be a scheme contained in a big fppf site. Two statements are proved here, both about the
presentation of an algebraic stack by a groupoid in algebraic spaces.

The first is the construction the section **Stacks 04TJ** is about: from a smooth groupoid in
algebraic spaces `G = (U, R, s, t, c)` over an algebraic space over `S`, the quotient stack
`[U/R]` of Stacks 044Q together with its algebraicity, bundled as a single object. Algebraicity
is Stacks 04TK (`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth`).
The bundling is not into the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of Stacks 03YP:
that is built on `CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, whereas a quotient
stack is a stackification and so has hom sets one universe up.

The second is **Stacks 076V**, the criterion for a category fibred in groupoids over the *common*
underlying category of the big fppf and big étale sites to be an algebraic stack: it is enough to
be a stack for the étale topology, to have a diagonal representable by algebraic spaces, and to
have a surjective smooth scheme atlas. As the source's proof observes, the second and third
conditions "are independent of the topology": they involve only 2-fibre products of categories
fibred in groupoids, 1-morphisms representable by algebraic spaces, and what it means for such a
1-morphism to be surjective and smooth. They are therefore stated here exactly as the
corresponding clauses of `AlgebraicGeometry.Stack.IsAlgebraicStack` (Stacks 026O) state them, and
the whole content of the lemma is the passage from the étale stack condition to the fppf one.

## Main definitions

* `AlgebraicGeometry.Stack.LargeAlgebraicStack`: an algebraic stack over `S` at the universes a
  quotient stack lives at.
* `AlgebraicGeometry.Stack.smoothGroupoidAlgebraicStack`: **Stacks 04TJ**.

## Main results

* `AlgebraicGeometry.Stack.smoothGroupoidAlgebraicStack_val`: its underlying category over the
  site is the quotient stack.
* `AlgebraicGeometry.Stack.isStackInGroupoids_quotientStack_of_isSmooth`: the stack clause and
  the diagonal clause of Stacks 026O for the quotient stack of a smooth groupoid, which are the
  section's Lemma 94.17.1 and the stack clause of Stacks 044Q.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_isStackInGroupoids_etale`: **Stacks 076V**.

## Implementation notes

**What Stacks 076V carries, and why none of it is the conclusion.** The source's proof runs
through the presentation of `𝒳` by a groupoid in algebraic spaces built out of the given atlas:
part (1) of Stacks 04T4 produces an algebraic space `R` representing the self-intersection
`(Sch/U) ×_𝒳 (Sch/U)`, parts (4) and (5) put a groupoid in algebraic spaces on the pair of
representing spaces and produce the canonical 1-morphism out of its quotient stack, part (6) says
that 1-morphism is fully faithful, and the argument of Stacks 04T5 part (2) — with the refinement
claim of Stacks 055V and Stacks 046N for the comparison of the étale with the fppf stackification
— upgrades it to an equivalence over the site. Three hypotheses carry exactly that chain:

* `_eR` is **part (1) of Stacks 04T4** for the given atlas, stated against the arrow space of the
  carried groupoid, which simultaneously pins that arrow space down. This library states the
  eight conditions of Stacks 045G but proves none of the seven equivalences
  (`StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal`), and part (1) of Stacks 04T4 is
  the implication from condition (1) to condition (8) applied twice, so it is unavailable: see
  `AlgebraicGeometry.Stack.SelfIntersection.isRepresentableByAlgebraicSpace_relation`, which
  reduces it to that implication and to nothing else.
* `_hobjects` is **part (4) of Stacks 04T4**: the object space of the carried groupoid is the
  algebraic space the atlas represents.
* `e` is **part (6) of Stacks 04T4 together with part (2) of Stacks 04T5**, read at the étale
  index: the quotient stack of the carried groupoid is equivalent, over the site, to `𝒳`. The
  fppf-index form of this is a theorem of this library,
  `AlgebraicGeometry.Stack.SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth`, but
  it takes algebraicity of `𝒳` as a hypothesis and so cannot serve here.

None of the three is the conclusion restated. `_eR` and `_hobjects` say nothing at all about `𝒳`
beyond the representability of one 2-fibre product. The equivalence `e` identifies `𝒳` with the
quotient stack of a groupoid in algebraic spaces that is *not* assumed smooth; for such a
groupoid `[U/R]` need not be an algebraic stack at all, so `e` does not contain algebraicity of
`𝒳`. In particular it supplies neither of the other two clauses of Stacks 026O: the diagonal
clause and the surjective smooth scheme atlas are the lemma's own hypotheses (2) and (3), passed
through unchanged, and the smoothness of the atlas is never used to produce them.

**What is discharged** is the fppf stack clause, both of its conjuncts. The quotient stack of
*any* groupoid in algebraic spaces satisfies descent for the fppf topology by Stacks 044Q
(`AlgebraicGeometry.Stack.isStack_quotientStack`), and Stacks 042W
(`CategoryTheory.BasedCategory.isStack_iff_of_equivalence`) transports that along `e`; the
family-indexed conjunct then follows by the implication 026F ⟹ 02ZI of Stacks 02ZJ from the
fibred-in-groupoids witness. That witness is where the étale stack hypothesis is used: `𝒳` is
taken as a bare `CategoryTheory.BasedCategory`, so clause (1) of Stacks 026O is supplied by
`CategoryTheory.Functor.IsStackInGroupoids.isFiberedInGroupoids` of the étale hypothesis and by
nothing else.

The étale topology on the slice is the localization at `S` of
`AlgebraicGeometry.etaleTopology`, the chosen étale topology on the underlying category of the
big fppf site, which is what makes "the common underlying category of `Sch_fppf` and
`Sch_étale`" of the source into a single category here. The existential over the atlas in clause
(3) of Stacks 026O is taken apart into the explicit arguments `U`, `f`, `hfrep` and `hfprop`,
since the carried hypotheses have to refer to that atlas.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 04TJ](https://stacks.math.columbia.edu/tag/04TJ)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 076V](https://stacks.math.columbia.edu/tag/076V)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-! ### The algebraic stack associated to a smooth groupoid -/

section SmoothGroupoid

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {A : AlgebraicSpaces C S hS}

/-- An algebraic stack over `S` at the universes the quotient stack of a groupoid in algebraic
spaces lives at: a category fibred in groupoids over the big fppf site of `S` together with the
proof that it is an algebraic stack in the sense of Stacks 026O.

The 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of Stacks 03YP is this subtype at the
object and morphism universes `u` and `u + 1`; a quotient stack is a stackification, so its hom
sets are not small and it lives one universe up. -/
abbrev LargeAlgebraicStack (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S) :=
  { 𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS) //
    IsAlgebraicStack.{u, w} C S hS 𝒳.val }

/-- **Stacks 04TJ.** The algebraic stack associated to a smooth groupoid in algebraic spaces
`G = (U, R, s, t, c)` over an algebraic space over `S`: the quotient stack `[U/R]` of Stacks
044Q, fibred in groupoids over the big fppf site of `S`, together with the proof that it is an
algebraic stack over `S`.

The underlying category over the site is the quotient stack on the nose
(`AlgebraicGeometry.Stack.smoothGroupoidAlgebraicStack_val`); the algebraicity component is
Stacks 04TK. -/
@[stacks 04TJ "the section's construction: the algebraic stack associated to a smooth groupoid \
in algebraic spaces, as one object bundling the quotient stack with its algebraicity. The \
quotient stack and its fibredness in groupoids are Stacks 044Q; algebraicity is Stacks 04TK"]
noncomputable def smoothGroupoidAlgebraicStack
    {G : GroupoidInAlgebraicSpaces C S hS A}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    LargeAlgebraicStack.{u, w} C S hS :=
  ⟨CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G),
    isAlgebraicStack_quotientStack_of_isSmooth.{u, w} hG⟩

/-- The category over the site underlying the algebraic stack of a smooth groupoid is the
quotient stack of Stacks 044Q. -/
theorem smoothGroupoidAlgebraicStack_val
    {G : GroupoidInAlgebraicSpaces C S hS A}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    (smoothGroupoidAlgebraicStack.{u, w} hG).val.val = quotientStack G :=
  rfl

/-- The quotient stack of a smooth groupoid in algebraic spaces is a stack in groupoids for the
fppf topology, and its diagonal is representable by algebraic spaces: the two clauses of Stacks
026O that the section's Lemma 94.17.1 and the stack clause of Stacks 044Q supply, read off the
algebraic stack of `AlgebraicGeometry.Stack.smoothGroupoidAlgebraicStack`. -/
theorem isStackInGroupoids_quotientStack_of_isSmooth
    {G : GroupoidInAlgebraicSpaces C S hS A}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    (quotientStack G).p.IsStackInGroupoids.{w} (BigFppfOver.topology C S hS) ∧
      ∃ h : (quotientStack G).p.IsFiberedInGroupoids,
        IsRepresentableByAlgebraicSpaces C S hS
          (diagonalBasedFunctor C S hS (CatFiberedInGroupoids.mk (quotientStack G) h)) := by
  obtain ⟨h, hst, hd, -⟩ := isAlgebraicStack_quotientStack_of_isSmooth.{u, w} hG
  exact ⟨hst.2, h, hd⟩

end SmoothGroupoid

/-! ### The étale criterion for an algebraic stack -/

section EtaleCriterion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 076V.** Let `𝒳` be a category over the common underlying category of the big fppf
and big étale sites of `S` such that

1. `𝒳` is a stack in groupoids for the étale topology,
2. the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces, and
3. there are a scheme `U` over `S` and a 1-morphism `(Sch/U) ⟶ 𝒳` which is representable by
   algebraic spaces, surjective and smooth.

Then `𝒳` is an algebraic stack over `S` in the sense of Stacks 026O.

Conditions (2) and (3) are stated exactly as the corresponding clauses of
`AlgebraicGeometry.Stack.IsAlgebraicStack`, which is legitimate because, as the source's proof
notes, both are independent of the topology. Three hypotheses carry the chain Stacks 04T4 (1),
(4), (6) and Stacks 04T5 (2) that the source's proof goes through; see the implementation notes
for why none of them is the conclusion restated. -/
@[stacks 076V "the criterion, with hypotheses (2) and (3) in the topology-independent form of \
the corresponding clauses of Stacks 026O. Carried as explicit hypotheses are part (1) of Stacks \
04T4 (`_eR`: the self-intersection of the atlas is representable by the arrow space of the \
carried groupoid), part (4) of Stacks 04T4 (`_hobjects`: its object space is the space the atlas \
represents) and part (6) of Stacks 04T4 together with part (2) of Stacks 04T5 read at the étale \
index (`e`: the quotient stack of the carried groupoid is equivalent over the site to `𝒳`); the \
carried groupoid is not assumed smooth, so none of the three contains algebraicity of `𝒳`. What \
is discharged is the fppf stack clause, by Stacks 044Q for the quotient stack of a groupoid in \
algebraic spaces, Stacks 042W to transport it along the equivalence and Stacks 02ZJ for the \
family-indexed conjunct, together with clause (1) of Stacks 026O out of the étale hypothesis"]
theorem isAlgebraicStack_of_isStackInGroupoids_etale
    (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (hstack : 𝒳.p.IsStackInGroupoids.{w} ((etaleTopology B).over (B.obj hS)))
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS
      (diagonalBasedFunctor B S hS (CatFiberedInGroupoids.mk 𝒳 hstack.isFiberedInGroupoids)))
    (U : BigFppfOver B S hS)
    (f : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳)
    (hfrep : IsRepresentableByAlgebraicSpaces B S hS f)
    (hfprop : ∀ (V : BigFppfOver B S hS)
        (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.obj)
        (_hy : y ⋙ 𝒳.p = Over.map V.hom)
        (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map V.hom)
            (schemeFibredCategory B S hS U).val.p 𝒳.p y f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        (let g := (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
         Space.IsSurjective B S hS g ∧ Space.IsSmooth B S hS g))
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (_eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeFibredCategory B S hS U)
        (CatFiberedInGroupoids.mk 𝒳 hstack.isFiberedInGroupoids) f).val.p
      (presheafOfCategories (G.arrows.obj ⋙ typeToCat)).p)
    (_hobjects : G.objects = Space.representedAlgebraicSpace B S hS U)
    (e : BasedCategory.Equivalence (quotientStack G) 𝒳) :
    IsAlgebraicStack.{u, w} B S hS 𝒳 := by
  have hX : 𝒳.p.IsStack (BigFppfOver.topology B S hS) :=
    (BasedCategory.isStack_iff_of_equivalence e (BigFppfOver.topology B S hS)).mp
      (isStack_quotientStack G)
  exact ⟨hstack.isFiberedInGroupoids,
    ⟨hX, hX.isStackInGroupoids hstack.isFiberedInGroupoids⟩, hdiag, U, f, hfrep, hfprop⟩

end EtaleCriterion

end AlgebraicGeometry.Stack

end
