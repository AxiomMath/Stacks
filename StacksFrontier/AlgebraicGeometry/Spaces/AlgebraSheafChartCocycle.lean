module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartTransition

/-!
# The cocycle laws of the chart transition of an algebra sheaf

`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartTransition` builds the transition
comparison `𝒜|_V ⟶ (chartSchemeMap g)_* 𝒜|_W` of the chart restrictions of a sheaf of
`𝒪_X`-algebras along a morphism `g : W ⟶ V` of étale scheme charts of an algebraic space `X`,
and records as absent the two laws that make the family of comparisons a *datum* rather than a
family of unrelated maps: that the transition at an identity chart morphism is the identity, and
that the transition at a composite is the composite of the transitions.  This file supplies both.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition_id` and
  `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition_comp`: **the two cocycle
  laws of the transition comparison.**  The second says
  `𝒜|_V ⟶ (chartSchemeMap (h ≫ g))_* 𝒜|_Z` is
  `𝒜|_V ⟶ (chartSchemeMap g)_* 𝒜|_W ⟶ (chartSchemeMap g)_* (chartSchemeMap h)_* 𝒜|_Z`, the
  second map being the direct image along `chartSchemeMap g` of the transition at `h`.
* `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransitionNatTrans_id`: the first
  law for the natural-transformation form, which is the shape glueing data consumes.  The
  composition law is *not* restated in that form; see the implementation notes.
* `AlgebraicGeometry.Space.chartOpensPushforwardTransition_id` and
  `AlgebraicGeometry.Space.chartOpensPushforwardTransition_comp`: the two laws for the underlying
  comparison of chart restrictions of a sheaf of commutative rings, which is where the content
  sits; the algebra-level laws are these read through
  `CategoryTheory.Under.UnderMorphism.ext`.
* `AlgebraicGeometry.Space.chartOpensRestrict_id` and
  `AlgebraicGeometry.Space.chartOpensRestrict_comp`: functoriality of the restriction of a chart
  morphism to an open of the target and its preimage.  This is the whole mathematical content:
  by `AlgebraicGeometry.Space.chartSchemeMap_chartOpensRestrict` the underlying morphism of
  schemes is `chartSchemeMap g ∣_ O`, and the two laws are then
  `AlgebraicGeometry.morphismRestrict_id` and `AlgebraicGeometry.morphismRestrict_comp`.
* `Stacks.AffineAlgebraEquivalence.algebraPushforward_id` and
  `Stacks.AffineAlgebraEquivalence.algebraPushforward_comp`: the direct image of algebra sheaves
  along an identity is the identity functor, and along a composite is the composite of the direct
  images — both *equalities of functors*, holding by `rfl`.

## Implementation notes

**The laws carry no `eqToHom`.**  One might expect each law to carry an
`CategoryTheory.eqToHom` on the preimage of the open, because `chartSchemeMap` is functorial
only up to the equalities `CategoryTheory.Functor.map_id` and `CategoryTheory.Functor.map_comp`,
and the preimage of an open along a composite is the iterated preimage only along those same
equalities.  That is not so.  `chartSchemeMap` is a composite of two
functors applied to a morphism, and for these two functors `Functor.map_id` and
`Functor.map_comp` hold by `rfl`, which is `AlgebraicGeometry.Space.chartSchemeMap_id` and
`AlgebraicGeometry.Space.chartSchemeMap_comp` below; the preimage of an open along a composite
of morphisms of schemes is the iterated preimage by `rfl` as well, Mathlib's
`TopologicalSpace.Opens.map_comp_eq` being an equality of functors rather than an isomorphism.
Both laws are therefore equations between morphisms whose *types* are already definitionally
equal, and no transport appears in either statement.

The same note's last clause — that
`Stacks.AffineAlgebraEquivalence.algebraPushforward` "of a composite has to be compared with the
composite of the direct images, which no declaration in the tree does" — is accurate as to
declarations and misleading as to difficulty: the comparison is the identity.  The docstring of
`Stacks.AffineAlgebraEquivalence.algebraPullbackComp`, in
`StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.AffineBaseChange`, already asserts it —
"direct image of algebra sheaves is *equal* on the nose to its composite,
`algebraPushforward j ⋙ algebraPushforward g = algebraPushforward (j ≫ g)`, because the direct
image of sheaves of rings is precomposition with the inverse image of opens and the comorphism
of a composite is the composite of the comorphisms" — and uses it to produce the left-adjoint
comparison of base change, but states it nowhere.
`Stacks.AffineAlgebraEquivalence.algebraPushforward_comp` is that statement.

**Why the laws are proved at the sheaf of rings and not at the sections.**  Each law reduces, at
a Zariski open `O` of the larger chart, to functoriality of the presheaf `𝒜` applied to
`AlgebraicGeometry.Space.chartOpensRestrict`.  Proving the algebra-level law by descending to
that level directly — `CategoryTheory.Under.UnderMorphism.ext`, then
`CategoryTheory.Sheaf.hom_ext`, then `CategoryTheory.NatTrans.ext`, then the section-level
identity — exhausts the 200000-heartbeat limit at `whnf`: the right-hand side is then a section
of a composite of `CategoryTheory.Under.post` and `CategoryTheory.Under.map` whose comorphism
component has to be unfolded through the algebra structure map before the two sides meet.  Proved
at the sheaf of rings and lifted by `CategoryTheory.Under.UnderMorphism.ext` alone, the single
remaining defeq check is between two morphisms of sheaves of rings and the proof is one `exact`.

**The composition law has no natural-transformation form here, and the obstruction is
elaboration rather than mathematics.**  `CategoryTheory.NatTrans.ext` applied to the
natural-transformation statement of the composition law exhausts the 200000-heartbeat limit at
`whnf` before any goal is produced: the two sides are natural transformations into
`restrictToChartSchemeFunctor Z ⋙ algebraPushforward (chartSchemeMap (h ≫ g))` and into
`(restrictToChartSchemeFunctor Z ⋙ algebraPushforward (chartSchemeMap h)) ⋙
algebraPushforward (chartSchemeMap g)`, which are definitionally equal but only after
`AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeFunctor` — a functor defined by four
fields, two of them proofs — is unfolded on both sides.  The identity law has no such problem,
its codomain being the same functor on both sides, and it is stated.  Nothing is lost: a natural
transformation is determined by its components, and
`AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition_comp` is exactly the
statement at each component.

**What these laws do and do not supply.**  They make the chart restrictions of `𝒜` together with
their transitions a lax-functorial family on the small étale site of `X`, which is the
compatibility a glueing datum needs *in the direct-image direction*.  They do **not** make the
family a descent datum: `AlgebraicGeometry.Space.Descent.DescentData` asks for gluing
*isomorphisms* over the fibre products, and the transition is a morphism whose inverse-image
transpose is invertible exactly for the quasi-coherent algebras — Stacks 03DX(2) together with
Stacks 03LY, which `StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartTransition` records as
not proved for algebras and which remains unproved for them here.  (That invertibility is **not**
Stacks 03M0, which is the characterisation of quasi-coherence itself; the misattribution is
recorded in `StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartCartesian`.)  Nothing in this
file carries Stacks 081V, Stacks 03M3 or any other tag: these are laws of an input to the
construction of the relative spectrum over an algebraic space, not an assertion of any tag.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

/-- **The direct image of algebra sheaves along an identity is the identity functor.**  An
equality of functors, not an isomorphism: the direct image of a sheaf of rings along the identity
is precomposition with the inverse image of opens along the identity, which is the identity
functor on opens, and the comorphism of the identity is the identity. -/
theorem algebraPushforward_id (T : AlgebraicGeometry.Scheme.{u}) :
    algebraPushforward (𝟙 T) = Functor.id (Stacks.RelativeSpec.AlgebraSheaf T) :=
  rfl

/-- **The direct image of algebra sheaves along a composite is the composite of the direct
images.**  An equality of functors, not an isomorphism.

The docstring of `Stacks.AffineAlgebraEquivalence.algebraPullbackComp` already asserts this —
"the direct image of sheaves of rings is precomposition with the inverse image of opens and the
comorphism of a composite is the composite of the comorphisms" — and uses it to identify the two
left adjoints there; this is the statement itself. -/
theorem algebraPushforward_comp {U T S : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ T)
    (g : T ⟶ S) :
    algebraPushforward (j ≫ g) = algebraPushforward j ⋙ algebraPushforward g :=
  rfl

/-- The underlying map of sheaves of rings of the direct image of a morphism of algebra sheaves
is the direct image of its underlying map of sheaves of rings. -/
theorem algebraPushforward_map_right {T S : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ S)
    {A C : Stacks.RelativeSpec.AlgebraSheaf T} (ψ : A ⟶ C) :
    ((algebraPushforward g).map ψ).right =
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map ψ.right :=
  rfl

end Stacks.AffineAlgebraEquivalence

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The morphism of chart schemes is functorial on the nose -/

/-- The morphism of chart schemes of an identity morphism of étale charts is the identity.  This
holds by `rfl`, and not only up to `CategoryTheory.Functor.map_id`: `chartSchemeMap` is two
functors applied in succession, and both preserve identities definitionally. -/
theorem chartSchemeMap_id (V : SmallEtale B S hS F) :
    chartSchemeMap (𝟙 V) = 𝟙 (chartScheme V) :=
  rfl

/-- The morphism of chart schemes of a composite of morphisms of étale charts is the composite.
This holds by `rfl`, and not only up to `CategoryTheory.Functor.map_comp`. -/
theorem chartSchemeMap_comp {U V W : SmallEtale B S hS F} (h : W ⟶ V) (g : V ⟶ U) :
    chartSchemeMap (h ≫ g) = chartSchemeMap h ≫ chartSchemeMap g :=
  rfl

/-! ### Functoriality of the restriction of a chart morphism to an open -/

/-- Morphisms between Zariski opens of charts are equal when their underlying morphisms of schemes
are. -/
private theorem chartOpens_hom_ext {U V : SmallEtale B S hS F} {O : (chartScheme U).Opens}
    {P : (chartScheme V).Opens} {f g : (chartOpens B S hS U).obj O ⟶ (chartOpens B S hS V).obj P}
    (h : chartSchemeMap f = chartSchemeMap g) : f = g := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  apply Over.OverMorphism.ext
  exact B.inclusion.map_injective h

/-- **The restriction of an identity morphism of charts to an open is the identity.**  Under
`AlgebraicGeometry.Space.chartSchemeMap_chartOpensRestrict` the underlying morphism of schemes is
`𝟙 (chartScheme V) ∣_ O`, and `AlgebraicGeometry.morphismRestrict_id` is the whole proof. -/
theorem chartOpensRestrict_id (V : SmallEtale B S hS F) (O : (chartScheme V).Opens) :
    chartOpensRestrict B S hS (𝟙 V) O = 𝟙 _ := by
  exact chartOpens_hom_ext B S hS (morphismRestrict_id O)

/-- **The restriction of a composite of morphisms of charts to an open is the composite of the
restrictions**, the inner one taken at the preimage of the open.  Under
`AlgebraicGeometry.Space.chartSchemeMap_chartOpensRestrict` the underlying morphisms of schemes
are the restrictions of the chart morphisms, and
`AlgebraicGeometry.morphismRestrict_comp` is the whole proof. -/
theorem chartOpensRestrict_comp {U V W : SmallEtale B S hS F} (h : W ⟶ V) (g : V ⟶ U)
    (O : (chartScheme U).Opens) :
    chartOpensRestrict B S hS (h ≫ g) O =
      chartOpensRestrict B S hS h (chartSchemeMap g ⁻¹ᵁ O) ≫
        chartOpensRestrict B S hS g O := by
  exact chartOpens_hom_ext B S hS (morphismRestrict_comp _ _ _)

/-! ### The cocycle laws for a sheaf of commutative rings -/

variable {X : AlgebraicSpaces B S hS}

/-- **The transition comparison of the chart restrictions of a sheaf of commutative rings at an
identity chart morphism is the identity.**  The two sides have the same type because the direct
image along `chartSchemeMap (𝟙 V) = 𝟙 (chartScheme V)` is the identity functor, by
`Stacks.AffineAlgebraEquivalence.algebraPushforward_id`'s ring-level counterpart. -/
theorem chartOpensPushforwardTransition_id (V : SmallEtale B S hS X.1)
    (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    (chartOpensPushforwardTransition B S hS (𝟙 V)).app A = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext O
  obtain ⟨O⟩ := O
  exact (A.obj.congr_map (congrArg Quiver.Hom.op
    (chartOpensRestrict_id B S hS V O))).trans (A.obj.map_id _)

/-- **The transition comparison of the chart restrictions of a sheaf of commutative rings at a
composite of chart morphisms is the composite of the comparisons**, the outer one followed by the
direct image along `chartSchemeMap g` of the inner one.

On sections over a Zariski open `O` of the largest chart both sides are the restriction map of
`A` along `AlgebraicGeometry.Space.chartOpensRestrict`, and the law is
`AlgebraicGeometry.Space.chartOpensRestrict_comp` carried through the presheaf. -/
theorem chartOpensPushforwardTransition_comp {V W Z : SmallEtale B S hS X.1}
    (h : Z ⟶ W) (g : W ⟶ V)
    (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    (chartOpensPushforwardTransition B S hS (h ≫ g)).app A =
      (chartOpensPushforwardTransition B S hS g).app A ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap g).base).map
          ((chartOpensPushforwardTransition B S hS h).app A) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext O
  obtain ⟨O⟩ := O
  exact (A.obj.congr_map (congrArg Quiver.Hom.op
    (chartOpensRestrict_comp B S hS h g O))).trans (A.obj.map_comp _ _)

/-! ### The cocycle laws for a sheaf of algebras -/

/-- **The first cocycle law of the algebra-level chart transition: the transition at an identity
chart morphism is the identity.**

The statement typechecks with no transport because the direct image of algebra sheaves along
`chartSchemeMap (𝟙 V)` is the identity functor, by
`AlgebraicGeometry.Space.chartSchemeMap_id` and
`Stacks.AffineAlgebraEquivalence.algebraPushforward_id`. -/
theorem AlgebraSheaf.restrictToChartSchemeTransition_id
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1) :
    A.restrictToChartSchemeTransition B S hS (𝟙 V) = 𝟙 _ := by
  apply Under.UnderMorphism.ext
  exact chartOpensPushforwardTransition_id B S hS V A.right

/-- **The second cocycle law of the algebra-level chart transition: the transition at a composite
of chart morphisms is the composite of the transitions.**

For `h : Z ⟶ W` and `g : W ⟶ V` morphisms of étale scheme charts of `X`, the comparison
`𝒜|_V ⟶ (chartSchemeMap (h ≫ g))_* 𝒜|_Z` is the comparison `𝒜|_V ⟶ (chartSchemeMap g)_* 𝒜|_W`
followed by the direct image along `chartSchemeMap g` of the comparison
`𝒜|_W ⟶ (chartSchemeMap h)_* 𝒜|_Z`.

The two sides have definitionally equal types, with no `CategoryTheory.eqToHom` on the preimage
of anything: `AlgebraicGeometry.Space.chartSchemeMap_comp` and
`Stacks.AffineAlgebraEquivalence.algebraPushforward_comp` are both `rfl`.  See the implementation
notes of this file, which correct the note of
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartTransition` on this point. -/
theorem AlgebraSheaf.restrictToChartSchemeTransition_comp
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) {V W Z : SmallEtale B S hS X.1}
    (h : Z ⟶ W) (g : W ⟶ V) :
    A.restrictToChartSchemeTransition B S hS (h ≫ g) =
      A.restrictToChartSchemeTransition B S hS g ≫
        (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap g)).map
          (A.restrictToChartSchemeTransition B S hS h) := by
  apply Under.UnderMorphism.ext
  exact chartOpensPushforwardTransition_comp B S hS h g A.right

/-- The first cocycle law for the natural-transformation form of the transition, which is the
shape glueing data consumes. -/
theorem AlgebraSheaf.restrictToChartSchemeTransitionNatTrans_id (V : SmallEtale B S hS X.1) :
    AlgebraSheaf.restrictToChartSchemeTransitionNatTrans B S hS (𝟙 V) = 𝟙 _ :=
  NatTrans.ext (funext fun A => AlgebraSheaf.restrictToChartSchemeTransition_id B S hS A V)

end AlgebraicGeometry.Space

end
