module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothDiagramRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationCancellation
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindexSnd

/-!
# The étale-smooth diagram test is invariant under a 2-isomorphism (Stacks 0CIF, 0CIG, 0CIT)

Every separation or relative condition of this library transports along a 2-isomorphism of the
1-morphism it is asserted of: `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_iso` for the
Deligne–Mumford condition of **Stacks 04YW**,
`AlgebraicGeometry.Stack.hasRelativeProperty_congr_twoIso` for the relative property of
**Stacks 03YK**, and `AlgebraicGeometry.Stack.isRelativelyEtale_congr_twoIso` for étaleness in
the sense of **Stacks 04XB**. The universal étale-smooth diagram test of **Stacks 0CIF** — and
with it the induced property of **Stacks 0CIG**, unramifiedness of **Stacks 0CIT** and étaleness
of **Stacks 0CIL** — did not, and this file supplies that transport.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_congr_twoIso`: condition (1) of
  **Stacks 0CIF** is invariant under a 2-isomorphism of the 1-morphism being tested.
* `AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_congr_twoIso`: the same for the property
  of **Stacks 0CIG** induced by a property of morphisms of algebraic spaces.
* `AlgebraicGeometry.Stack.isUnramified_congr_twoIso`: the same for **Stacks 0CIT**.
* `AlgebraicGeometry.Stack.isEtale_congr_twoIso`: the same for **Stacks 0CIL**.

## How it is proved

The diagram test at `f : 𝒳 ⟶ 𝒴` quantifies over 2-commutative squares

    U ---h---> V
    |          |
    a          b
    v          v
    𝒳 ---f---> 𝒴

of algebraic spaces over `f`, and its étaleness premise quantifies over the 2-fibre products of
the cospan `(b, f)` and the comparison 1-morphisms from the square's cone
(`AlgebraicGeometry.Stack.diagramCone`) into them. Both of those depend on `f` *on the nose*: a
2-commutative square over `(b, f)` is not a square over `(b, f')`, because its filler is a
2-morphism `fst ≫ b ≅ snd ≫ f`. So the content of the transport is that the whole category of
2-commutative squares over `(b, f)` moves to the one over `(b, f')`, carrying 2-fibre products to
2-fibre products and comparison 1-morphisms to comparison 1-morphisms *without changing the
1-morphism being tested for étaleness*.

That is exactly `CategoryTheory.Bicategory.TwoCommSq.reindexSnd` together with
`CategoryTheory.Bicategory.isTwoFibreProduct_reindexSnd` of
`StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex` — reindexing the *second* leg of the
cospan, which is where `f` sits — and
`CategoryTheory.Bicategory.TwoCommSq.PreHom.reindexSnd`, which carries a comparison 1-morphism
across the reindexing and leaves it alone. The given diagram over `f'` is reindexed backwards to
a diagram over `f`, its filler being the one the reindexing produces; the hypothesis applied to
that diagram asks for étaleness of the comparisons into the 2-fibre products of `(b, f)`, and
each of those is reindexed forwards into a 2-fibre product of `(b, f')` on which the premise
already holds. No 2-cell algebra occurs here: it is all inside `reindexFst_compat_iff`, the one
computation of the reindexing file.

The reindexing is set up so that the diagram over `f` is *defined* as the reindexing of the given
one rather than written out as a composite of fillers, which keeps the two squares equal by
structure eta instead of by unfolding a chain of `Iso.trans`.

## Implementation notes

No declaration here carries a `@[stacks]` attribute. None of the four is an assertion of its
source tag: they are the invariance statements that the sources use silently, and their
siblings — `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_iso`,
`AlgebraicGeometry.Stack.hasRelativeProperty_congr_twoIso`,
`AlgebraicGeometry.Stack.isRelativelySmooth_congr_twoIso` and
`AlgebraicGeometry.Stack.isRelativelyEtale_congr_twoIso` — are untagged for the same reason.

`AlgebraicGeometry.Stack.IsUnramified` and `AlgebraicGeometry.Stack.IsEtale` are spelled out
rather than defined through `AlgebraicGeometry.Stack.HasEtaleSmoothLocalProperty`, so their two
statements are not instances of the third; each is the conjunction of
`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_iso` with the diagram-test transport at its own
property, which is how they are proved.

Invariance under *precomposition with an equivalence* is a different and harder statement, and is
not proved here: see the module documentation of
`StacksFrontier.AlgebraicGeometry.Stacks.FibreUnramifiedFromChart`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIG](https://stacks.math.columbia.edu/tag/0CIG)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Condition (1) of Stacks 0CIF is invariant under a 2-isomorphism of the 1-morphism.** Two
2-isomorphic 1-morphisms of algebraic stacks over `S` pass the universal étale-smooth diagram
test at a property `P` of morphisms of algebraic spaces together.

A 2-commutative square over the cospan `(b, f)` has a filler `fst ≫ b ≅ snd ≫ f`, so it depends
on `f` on the nose, and the content is that the category of such squares moves along the
2-isomorphism: `CategoryTheory.Bicategory.TwoCommSq.reindexSnd` reindexes the second leg of the
cospan, `CategoryTheory.Bicategory.isTwoFibreProduct_reindexSnd` carries 2-fibre products to
2-fibre products, and `CategoryTheory.Bicategory.TwoCommSq.PreHom.reindexSnd` carries a
comparison 1-morphism across without changing it. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_congr_twoIso
    (P : MorphismProperty (AlgebraicSpaces B S hS)) {f f' : 𝒳 ⟶ 𝒴} (e : f ≅ f')
    (hf : HasPropertyOnEveryEtaleSmoothDiagram B S hS P f) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f' := by
  intro U V hU hV a b h η hb hk
  -- the 2-isomorphism of the underlying 1-morphisms of categories fibred in groupoids
  have ε : f.hom ≅ f'.hom := algStackHomIso B S hS e
  -- the diagram over `f` is the reindexing backwards of the given diagram over `f'`
  refine hf U V hU hV a b h
    ((diagramCone B S hS f'.hom a.hom b.hom h η).reindexSnd ε.symm).iso hb ?_
  intro Q hQ k
  -- and each 2-fibre product of `(b, f)` is reindexed forwards into one of `(b, f')`
  exact hk (Q.reindexSnd ε) (Bicategory.isTwoFibreProduct_reindexSnd ε hQ)
    (Bicategory.TwoCommSq.PreHom.reindexSnd
      (T := diagramCone B S hS f'.hom a.hom b.hom h η) (S := Q) ε k)

/-- **The property of Stacks 0CIG induced by a property of morphisms of algebraic spaces is
invariant under a 2-isomorphism of the 1-morphism.** Both conjuncts transport: the
Deligne–Mumford one by `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_iso` and the universal
étale-smooth diagram test by
`AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_congr_twoIso`. -/
theorem hasEtaleSmoothLocalProperty_congr_twoIso
    (P : MorphismProperty (AlgebraicSpaces B S hS)) {f f' : 𝒳 ⟶ 𝒴} (e : f ≅ f')
    (hf : HasEtaleSmoothLocalProperty B S hS P f) :
    HasEtaleSmoothLocalProperty B S hS P f' :=
  ⟨AlgebraicStacks.isDM_of_iso B S hS e hf.1,
    hasPropertyOnEveryEtaleSmoothDiagram_congr_twoIso B S hS P e hf.2⟩

/-- **Unramifiedness of Stacks 0CIT is invariant under a 2-isomorphism of the 1-morphism.** Two
2-isomorphic 1-morphisms of algebraic stacks over `S` are unramified together. -/
theorem isUnramified_congr_twoIso {f f' : 𝒳 ⟶ 𝒴} (e : f ≅ f')
    (hf : IsUnramified B S hS f) : IsUnramified B S hS f' :=
  ⟨AlgebraicStacks.isDM_of_iso B S hS e hf.1,
    hasPropertyOnEveryEtaleSmoothDiagram_congr_twoIso B S hS _ e hf.2⟩

/-- **Étaleness of Stacks 0CIL is invariant under a 2-isomorphism of the 1-morphism.** Two
2-isomorphic 1-morphisms of algebraic stacks over `S` are étale together. -/
theorem isEtale_congr_twoIso {f f' : 𝒳 ⟶ 𝒴} (e : f ≅ f')
    (hf : IsEtale B S hS f) : IsEtale B S hS f' :=
  ⟨AlgebraicStacks.isDM_of_iso B S hS e hf.1,
    hasPropertyOnEveryEtaleSmoothDiagram_congr_twoIso B S hS _ e hf.2⟩

/-- **Unramifiedness of Stacks 0CIT is invariant under an equivalence of the source, for a
1-morphism representable by algebraic spaces.** Let `q : 𝒰 ⟶ 𝒵` and `q' : 𝒰' ⟶ 𝒵` be
1-morphisms of algebraic stacks over `S` with a common target, and let `c : 𝒰' ⟶ 𝒰` be an
equivalence of the underlying categories with `c ≫ q ≅ q'`. If `q` is representable by algebraic
spaces and unramified, then `q'` is unramified.

This is the statement that `AlgebraicGeometry.Stack.isDM_of_equivalence` is for the
Deligne–Mumford condition, at unramifiedness. Both conjuncts transport: the Deligne–Mumford one
by that very statement, and the universal étale-smooth diagram test through its identification
with the relative property of **Stacks 03YK** at unramifiedness
(`AlgebraicGeometry.Stack.hasRelativeProperty_unramified_of_isUnramified` and
`AlgebraicGeometry.Stack.isUnramified_of_hasRelativeProperty_unramified`), which is invariant
under a square of equivalences by **Stacks 0457**
(`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`). Representability of `q'` is not a
hypothesis: it transports from that of `q` by Stacks 0457 as well.

The representability hypothesis is what that identification asks for, and it is not known to be
removable: the étale-smooth diagram test quantifies over the 2-fibre products of the cospan
`(b, q)`, and an equivalence `c : 𝒰' ⟶ 𝒰` does not reindex them — the cospans `(b, q)` and
`(b, q')` have second legs with *different sources*, so
`CategoryTheory.Bicategory.TwoCommSq.reindexSnd`, which carries the 2-iso case, does not apply
and the comparison `𝒰' ×_𝒵 V ≃ 𝒰 ×_𝒵 V` would have to be built. See the module documentation of
`StacksFrontier.AlgebraicGeometry.Stacks.FibreUnramifiedFromChart`. -/
theorem isUnramified_of_equivalence_of_isRepresentableByAlgebraicSpaces
    {𝒰 𝒰' 𝒵 : AlgebraicStacks.{u, w} B S hS} (q : 𝒰 ⟶ 𝒵) (q' : 𝒰' ⟶ 𝒵)
    (c : 𝒰'.val.val ⥤ᵇ 𝒰.val.val) (γ : BasedFunctor.comp c q.hom.hom ≅ q'.hom.hom)
    (hc : Functor.IsEquivalence c.toFunctor)
    (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom.hom)
    (h : IsUnramified B S hS q) :
    IsUnramified B S hS q' := by
  have ha := hc
  have hb : Functor.IsEquivalence (BasedFunctor.id 𝒵.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒵.val.val.obj))
  -- the target is not moved, so the right-hand 1-morphism of the square is the identity
  have γ' : BasedFunctor.comp c q.hom.hom ≅
      BasedFunctor.comp q'.hom.hom (BasedFunctor.id 𝒵.val.val) := γ
  have hq' : IsRepresentableByAlgebraicSpaces B S hS q'.hom.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
      q'.hom.hom q.hom.hom c (BasedFunctor.id 𝒵.val.val) γ').1 hq
  refine isUnramified_of_hasRelativeProperty_unramified B S hS q' hq'
    (isDM_of_equivalence B S hS q q' c γ hc h.1) ?_
  exact relativeProperty_of_equivalences B S hS (Space.unramifiedMorphismProperty B S hS)
    q'.hom.hom q.hom.hom c (BasedFunctor.id 𝒵.val.val) γ'
    (hasRelativeProperty_unramified_of_isUnramified B S hS q hq h)

end AlgebraicGeometry.Stack

end
