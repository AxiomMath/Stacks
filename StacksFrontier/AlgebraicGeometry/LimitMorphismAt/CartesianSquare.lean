module

public import StacksFrontier.AlgebraicGeometry.FlatGoodDiagram.Comparison

/-!
# A commuting square of morphisms of image systems over a limit of Noetherian schemes

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, and let

```
X¹ ⟶ X³
↓     ↓
X² ⟶ X⁴
```

be a commuting square of schemes quasi-separated and of finite type over `S`, with `p : X¹ ⟶ X³`,
`q : X¹ ⟶ X²`, `a : X³ ⟶ X⁴` and `b : X² ⟶ X⁴`. Choosing a good diagram for each corner presents
each `X^j` as the limit of its inverse system of scheme-theoretic images, and `p`, `q`, `a`, `b`
are realized by morphisms `p_i`, `q_i`, `a_i`, `b_i` of those systems on a common tail. The two
composites `a_i ∘ p_i` and `b_i ∘ q_i` then agree at every sufficiently late stage.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.ofEq`: a morphism of image systems
  inducing `f` on the limits is one inducing any morphism equal to `f`.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.eventually_comp_eq_comp_morphismAt`: the two
  composites agree at every sufficiently late stage.

## Route

The two composites are morphisms of the image systems of the good diagrams for `X¹` and `X⁴`
inducing `p ≫ a` and `q ≫ b` on the limits, and the square commutes, so they induce the same
morphism; the eventual-uniqueness half of Stacks 0CNR,
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.eventually_eq_morphismAt_of_dominant`,
identifies them at all sufficiently late stages. Only the commutativity of the square is used,
not its cartesianness.

The four morphisms of systems are taken over one index `i₀` above the indices of all four good
diagrams, which is the index the source calls `max (i₅, i₆, i₇, i₈)`; a morphism of systems
defined over an earlier index restricts to the tail above `i₀` by
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.restrict'`.

## Universe situation

The index type is at a universe independent of the universe of the schemes and carries no
smallness or cofinality hypothesis, as in the eventual-uniqueness statement this rests on.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR)
* [Stacks Project, Tag 0CNW](https://stacks.math.columbia.edu/tag/0CNW), whose first conclusion
  has the eventual commutation proved here as its first half

## Not done here

The remaining halves of Stacks 0CNW are the assertion that the induced morphism
`(q_i, p_i) : X¹_i ⟶ X²_i ×_{X⁴_i} X³_i` is eventually a closed immersion, and, when `a` and `b`
are flat and of finite presentation, eventually an isomorphism. Both need the cartesian square
to be presented by the good diagram whose model is `W² ×_{W⁴} W³`, together with the
independence of the systems from the choice of model (Stacks 0CNS, of which
`AlgebraicGeometry.LimitNoetherianSituation.exists_eventual_iso_imageSystem'` and
`AlgebraicGeometry.LimitNoetherianSituation.eventually_natural_imageSystem_comparison'` are the
objectwise and naturality consequences); neither the fibre product of two image systems over a
third nor that presentation is constructed anywhere in this library.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

namespace MorphismAt

/-- A morphism of image systems inducing `f` on the limits is a morphism of image systems
inducing any morphism equal to `f`. -/
noncomputable def ofEq {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    {f g : X ⟶ Y} {GX : GoodDiagram D pX} {GY : GoodDiagram D pY} {i₀ : I}
    {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀} (h : f = g)
    (F : MorphismAt D f GX GY i₀ hX hY) : MorphismAt D g GX GY i₀ hX hY where
  maps := F.maps
  over_base := F.over_base
  induces j := (F.induces j).trans (congrArg (· ≫ _) h)

/-- The maps of `ofEq h F` are the maps of `F`. -/
@[simp]
lemma ofEq_maps {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    {f g : X ⟶ Y} {GX : GoodDiagram D pX} {GY : GoodDiagram D pY} {i₀ : I}
    {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀} (h : f = g)
    (F : MorphismAt D f GX GY i₀ hX hY) : (ofEq h F).maps = F.maps :=
  rfl

end MorphismAt

/-- **Stacks Project, Tag 0CNW, the eventual commutation.** Given a commuting square of schemes
quasi-separated and of finite type over the limit `S`, good diagrams for its four corners and
morphisms `p_i`, `q_i`, `a_i`, `b_i` of the resulting image systems realizing the four morphisms
of the square on a common tail, the two composites `a_i ∘ p_i` and `b_i ∘ q_i` agree at every
sufficiently late stage. -/
@[stacks 0CNW "eventual commutation of the two composites of systems"]
theorem eventually_comp_eq_comp_morphismAt (D : LimitNoetherianSituation.{v, u} I)
    {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
    {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
    {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄} (hsq : p ≫ a = q ≫ b)
    {G₁ : GoodDiagram D s₁} {G₂ : GoodDiagram D s₂} {G₃ : GoodDiagram D s₃}
    {G₄ : GoodDiagram D s₄} {i₀ : I} {h₁ : G₁.index ≤ i₀} {h₂ : G₂.index ≤ i₀}
    {h₃ : G₃.index ≤ i₀} {h₄ : G₄.index ≤ i₀}
    (P : MorphismAt D p G₁ G₃ i₀ h₁ h₃) (Q : MorphismAt D q G₁ G₂ i₀ h₁ h₂)
    (A : MorphismAt D a G₃ G₄ i₀ h₃ h₄) (B : MorphismAt D b G₂ G₄ i₀ h₂ h₄) :
    ∃ (i₉ : I) (_ : i₀ ≤ i₉), ∀ j : Over (op i₀), i₉ ≤ unop j.left →
      P.maps.app j ≫ A.maps.app j = Q.maps.app j ≫ B.maps.app j :=
  MorphismAt.eventually_eq_morphismAt_of_dominant (MorphismAt.ofEq hsq (P.comp' A)) (Q.comp' B)

end AlgebraicGeometry.LimitNoetherianSituation
