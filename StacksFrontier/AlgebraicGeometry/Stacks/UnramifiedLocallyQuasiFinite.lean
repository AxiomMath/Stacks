module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleFlatUnramifiedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications

/-!
# An unramified 1-morphism of algebraic stacks is locally quasi-finite (Stacks 0H2Z)

**Stacks 0H2Z** asserts that an unramified 1-morphism of algebraic stacks (**Stacks 0CIT**) is
locally quasi-finite (**Stacks 06PU**). Local quasi-finiteness is the conjunction of three
conditions: the quasi-DM condition of **Stacks 04YW**, local finite type in the sense of
**Stacks 06FS** part (1), and discreteness of the space of points of the fibre over every
field-valued point of the target.

This file proves the quasi-DM conjunct of the conclusion and the smooth-diagram step from which
the local finite type conjunct is read off. The full statement, all three conjuncts, is
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_of_isUnramified`, in
`StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedIsLocallyQuasiFinite`, together with its
corollary `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isUnramified`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_isUnramified`: the quasi-DM conjunct of
  **Stacks 0H2Z**, unconditionally.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasPropertyOnSomeSmoothDiagram_of_isUnramified`: the
  existential smooth-diagram test of **Stacks 06FM** at any property that unramified morphisms of
  algebraic spaces over `S` have, for an unramified 1-morphism admitting the **Stacks 0CIA**
  diagram.

## Implementation notes

The source deduces Stacks 0H2Z from the characterization of unramified 1-morphisms
(**Stacks 0CIY**), the characterization of locally quasi-finite ones (**Stacks 06UF**), and the
corresponding implication for morphisms of algebraic spaces (**Stacks 05W0**). That route is not
available here: the library's Stacks 06UF,
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isQuasiDM_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange`, carries only the quasi-DM
conjunct of its implication (4) ⟹ (1), the local finite type and field-valued-fibre
conjuncts being explicitly *not* carried there. So the two conjuncts proved this way are obtained
directly from the definition of unramifiedness instead.

The quasi-DM conjunct is Stacks 050E part (2): unramifiedness contains the Deligne–Mumford
condition, and a Deligne–Mumford 1-morphism is quasi-DM.

Local finite type is read off one diagram of algebraic spaces over `f`, exactly as the
corresponding step of **Stacks 0CJ1**, (1) ⟹ (2) is —
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isLocallyOfFinitePresentation_isFlat_isUnramified_of_isEtale`.
`AlgebraicGeometry.Stack.IsUnramified` is the *universal étale-smooth* diagram test of
**Stacks 0CIF** while `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFiniteType` is the
*universal smooth* test of **Stacks 06FM**, so the two are tested on different families of
diagrams and no implication between them is true by definition. Turning the universal
étale-smooth test into the existential one is exactly the existence of one diagram over `f` with
smooth right-hand vertical 1-morphism, surjective left-hand vertical 1-morphism and étale
comparisons — `AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram`, which for a
Deligne–Mumford `f` is **Stacks 0CIA**. That tag is in this library only with the structure
theorem **Stacks 06N3** as an explicit hypothesis
(`AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM`), so discharging the diagram
here would only relocate the same unproved input and it stays a named hypothesis, as it does at
Stacks 0CJ1. Once it is in hand, the diagram is also a smooth one in the sense of Stacks 06FM —
its left leg is smooth by `AlgebraicGeometry.Stack.isRelativelySmooth_of_etaleSmoothDiagram` and
surjective on objects because it is surjective on points — and its top morphism is unramified,
hence locally of finite type by **Stacks 05VZ**; the universal smooth test is then recovered from
the existential one by Stacks 06FM.

**What the third conjunct would need.** For a field-valued point `Spec(k) ⟶ 𝒴` the fibre
`𝒵 = 𝒳 ×_𝒴 Spec(k)` is unramified over `Spec(k)` by **Stacks 0CIV**, and the argument for
discreteness of `|𝒵|` runs through a *surjective étale* chart of `𝒵` itself: on the étale-smooth
diagram of **Stacks 0CIF** taken over the identity chart of `Spec(k)` the top morphism
`U ⟶ Spec(k)` is unramified, hence locally quasi-finite by **Stacks 05W0** and so `|U|` is
discrete by `AlgebraicGeometry.Space.discreteTopology_points_of_isLocallyQuasiFinite`, while the
left leg is smooth and surjective and therefore open and surjective on points by **Stacks 04XL**,
so discreteness descends. The diagram over the *prescribed* chart is
`AlgebraicGeometry.Stack.exists_etaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram`, which
asks for a surjective étale presentation by a scheme of the apex of the canonical 2-fibre product
of that chart with `𝒵 ⟶ Spec(k)`; supplying it needs **Stacks 0CIA** at the fibre, i.e. the same
`ExistsEtalePresentationOfIsAbsolutelyDM`, together with the absolute Deligne–Mumford condition on
the fibre. None of that is assembled here.

## References

* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 05VZ](https://stacks.math.columbia.edu/tag/05VZ)
* [Stacks Project, Tag 05W0](https://stacks.math.columbia.edu/tag/05W0)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06UF](https://stacks.math.columbia.edu/tag/06UF)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CIV](https://stacks.math.columbia.edu/tag/0CIV)
* [Stacks Project, Tag 0CIY](https://stacks.math.columbia.edu/tag/0CIY)
* [Stacks Project, Tag 0CJ1](https://stacks.math.columbia.edu/tag/0CJ1)
* [Stacks Project, Tag 0H2Z](https://stacks.math.columbia.edu/tag/0H2Z)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The quasi-DM conjunct of Stacks 0H2Z.** An unramified 1-morphism of algebraic stacks over
`S` is quasi-DM, with a representable relative diagonal.

Unramifiedness in the sense of **Stacks 0CIT** contains the Deligne–Mumford condition, and a
Deligne–Mumford 1-morphism is quasi-DM by **Stacks 050E**, part (2); the relative diagonal of a
1-morphism of algebraic stacks is always representable by algebraic spaces. -/
@[stacks 0H2Z "the quasi-DM conjunct of local quasi-finiteness, unconditionally. The local finite
  type conjunct is `isLocallyOfFiniteType_of_isUnramified`; the field-valued-fibre conjunct is
  NOT carried"]
theorem isQuasiDM_of_isUnramified {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : Stack.IsUnramified B S hS f) :
    IsQuasiDMWithRepresentableDiagonal B S hS f :=
  (isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS f).2 (isQuasiDM_of_isDM B S hS hf.1)

/-- The existential smooth-diagram test of **Stacks 06FM** holds at any property that unramified
morphisms of algebraic spaces over `S` have, for an unramified 1-morphism of algebraic stacks
admitting a diagram as in `AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram`.

The given diagram passes the universal étale-smooth test, so its top morphism is unramified and
has the property; its right leg is smooth by hypothesis, its left leg is smooth by
`AlgebraicGeometry.Stack.isRelativelySmooth_of_etaleSmoothDiagram` and surjective on objects
because it is surjective on points. -/
theorem hasPropertyOnSomeSmoothDiagram_of_isUnramified
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hex : Stack.HasSurjectiveEtaleSmoothDiagram.{u, w} B S hS f)
    (hf : Stack.IsUnramified B S hS f)
    (hP : ∀ {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS V →
      ∀ g : U ⟶ V, Space.IsUnramified B S hS g → P g) :
    Stack.HasPropertyOnSomeSmoothDiagram B S hS P f.hom := by
  obtain ⟨U, V, hU, hV, a, b, h, η, hasurj, hb, hk⟩ := hex
  have hasm : Stack.IsRelativelySmooth B S hS a.hom :=
    Stack.isRelativelySmooth_of_etaleSmoothDiagram B S hS f hU hV a b h η hb hk
  refine ⟨U, V, hU, hV, a.hom, b.hom, h, ⟨η⟩, hasm, ?_, hb,
    hP hV h (hf.2 U V hU hV a b h η hb hk)⟩
  exact (Stack.isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1}
      B S hS a.hom hasm.1).mpr
    ((Stack.pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1}
      B S hS a hasm.1).mp hasurj)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
