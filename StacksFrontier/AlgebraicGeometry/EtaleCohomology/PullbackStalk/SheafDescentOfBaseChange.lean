module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonDescentBaseChange

/-!
# Effective descent along a morphism from base change along itself

Let `F` be a pseudofunctor from the locally discrete bicategory on `Cᵒᵖ` to `Cat` and let
`f : X ⟶ Y` be a morphism with a chosen fibre product `XX = X ×_Y X`. Suppose the inverse images
along `f`, along the structure morphism `XX.p : X ×_Y X ⟶ Y`, along the second projection
`XX.p₂` and along the structure morphism of `(X ×_Y X) ×_X (X ×_Y X)` have right adjoints, that
the fibres over `X` and `Y` have equalizers, and that the inverse image along `f` preserves finite
limits and reflects isomorphisms. This file proves that descent along `f` is effective as soon as
two base-change `2`-cells are invertible: the one of the square of `f` against itself, and the one
of the square of `XX.p` against `f`.

The argument is the base-change argument of
`CategoryTheory.Pseudofunctor.isIso_singletonPullFunctor_map_counit`, run for the base change of
`f` along `f` itself. That base change `XX.p₂ : X ×_Y X ⟶ X` has a section, the diagonal, so
descent along it is effective with no hypothesis at all; hence the counit of the adjunction
`CategoryTheory.Pseudofunctor.singletonDescentAdjunction` becomes invertible after inverse image
along the first projection `XX.p₁`. That projection has a section as well, so descent along it is
effective too, and a morphism of the fibre over `X` whose inverse image along it is invertible is
itself invertible: the counit is invertible. The unit is then invertible because its image under
the inverse image along `f` is, by a triangle identity, and that inverse image reflects
isomorphisms.

This is the categorical content of the source's proofs of Stacks 0GEZ and Stacks 0GF0, which the
source runs as a reduction to geometric points: the two base-change `2`-cells are what the
base-change theorems for integral, resp. proper, morphisms supply, and reflection of isomorphisms
is what surjectivity supplies. No reduction to points is needed here, because the base change of
`f` along itself is already split.

## Main results

* `CategoryTheory.Pseudofunctor.isIso_singletonDescentAdjunction_counit_of_isIso_mateEquiv`: the
  counit is invertible;
* `CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_of_isIso_mateEquiv`: **descent along
  `f` is effective.**

## Implementation notes

Everything here is stated for an arbitrary pseudofunctor. The file sits beside the small étale
descent files only because the split case it uses,
`CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_of_section`, is proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent`.

The chosen fibre product of the base change `XX.p₂` with itself is
`CategoryTheory.Limits.ChosenPullback.baseChangedSelf`, whose structure morphism is `ZZ.p₂` only
up to an equation; the right adjoint and the base-change hypothesis are stated for `ZZ.p₂`, the
second projection of a chosen fibre product, and transported along that equation inside the
proof, where the pseudofunctor is abstract and the transport costs nothing.

Nothing here carries a Stacks attribute: this is category-theoretic substrate.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v v' u u'

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {X Y : C} (f : X ⟶ Y) (XX : ChosenPullback f f) (ZZ : ChosenPullback XX.p f)
  {R : F.obj (.mk (.op X)) ⥤ F.obj (.mk (.op Y))}
  (af : (F.map f.op.toLoc).toFunctor ⊣ R)
  {T : F.obj (.mk (.op XX.pullback)) ⥤ F.obj (.mk (.op Y))}
  (af₁ : (F.map XX.p.op.toLoc).toFunctor ⊣ T)
  {Rq : F.obj (.mk (.op XX.pullback)) ⥤ F.obj (.mk (.op X))}
  (aq : (F.map XX.p₂.op.toLoc).toFunctor ⊣ Rq)
  {Tq : F.obj (.mk (.op ZZ.pullback)) ⥤ F.obj (.mk (.op X))}
  (aq₁ : (F.map ZZ.p₂.op.toLoc).toFunctor ⊣ Tq)

/-- Descent along the second projection of a chosen fibre product of `f` with itself is
effective: the diagonal is a section of it. -/
theorem isEquivalence_toDescentData_chosenPullback_p₂ :
    (F.toDescentData (fun _ : Unit ↦ XX.p₂)).IsEquivalence :=
  DescentData.isEquivalence_toDescentData_of_section F XX.p₂
    (XX.isPullback.lift (𝟙 X) (𝟙 X) rfl) (XX.isPullback.lift_snd _ _ _)

/-- Descent along the first projection of a chosen fibre product of `f` with itself is
effective: the diagonal is a section of it. -/
theorem isEquivalence_toDescentData_chosenPullback_p₁ :
    (F.toDescentData (fun _ : Unit ↦ XX.p₁)).IsEquivalence :=
  DescentData.isEquivalence_toDescentData_of_section F XX.p₁
    (XX.isPullback.lift (𝟙 X) (𝟙 X) rfl) (XX.isPullback.lift_fst _ _ _)

variable [HasEqualizers (F.obj (.mk (.op Y)))] [HasEqualizers (F.obj (.mk (.op X)))]
  [PreservesFiniteLimits (F.map f.op.toLoc).toFunctor]

/-- **The counit of singleton descent along `f` is invertible** once the base-change `2`-cells of
the square of `f` against itself and of the square of `XX.p` against `f` are. -/
theorem isIso_singletonDescentAdjunction_counit_of_isIso_mateEquiv
    (hβ : ∀ M, IsIso ((mateEquiv af aq (commSqTwoSquare F XX.condition)).app M))
    (hγ : ∀ N, IsIso ((mateEquiv af₁ aq₁ (commSqTwoSquare F ZZ.condition)).app N))
    (D : F.DescentData (fun _ : Unit ↦ f)) :
    IsIso ((singletonDescentAdjunction F f XX af af₁).counit.app D) := by
  have := isEquivalence_toDescentData_chosenPullback_p₂ F f XX
  -- The self fibre product of `XX.p₂` is presented by `ZZ`, with structure morphism `ZZ.p₂`
  -- only up to an equation; transport the adjunction and the hypothesis along it.
  have key : ∀ (k : ZZ.pullback ⟶ X) (hk : k = ZZ.p₂) (w : ZZ.p₁ ≫ XX.p = k ≫ f) (N),
      IsIso ((mateEquiv af₁ (hk ▸ aq₁ : (F.map k.op.toLoc).toFunctor ⊣ Tq)
        (commSqTwoSquare F w)).app N) := by
    rintro k rfl w N
    exact hγ N
  have hp := ChosenPullback.baseChangedSelf_p f f XX XX ZZ
  have hj : ZZ.p₁ ≫ XX.p = (ChosenPullback.baseChangedSelf f f XX XX ZZ).p ≫ f :=
    hp ▸ ZZ.condition
  apply descentData_isIso_of_components
  intro ⟨⟩
  refine isIso_of_descent_components F (fun _ : Unit ↦ XX.p₁)
    (isEquivalence_toDescentData_chosenPullback_p₁ F f XX) _ ?_
  intro ⟨⟩
  have := isIso_singletonPullFunctor_map_counit F f f XX XX
    (ChosenPullback.baseChangedSelf f f XX XX ZZ) XX.condition ZZ.p₁ hj
    (ChosenPullback.baseChangedSelf_p₁_fst f f XX XX ZZ)
    (ChosenPullback.baseChangedSelf_p₂_fst f f XX XX ZZ) af af₁ aq (hp ▸ aq₁) hβ
    (key _ hp hj) D
  exact (DescentData.component F (fun _ : Unit ↦ XX.p₂) ()).map_isIso
    ((singletonPullFunctor F f f XX XX.condition).map
      ((singletonDescentAdjunction F f XX af af₁).counit.app D))

/-- **Effective descent along `f` from two base-change `2`-cells.** If the inverse image along
`f` preserves finite limits and reflects isomorphisms, and the base-change `2`-cells of the square
of `f` against itself and of the square of the structure morphism `X ×_Y X ⟶ Y` against `f` are
invertible, then the canonical functor from the fibre over `Y` to descent data for `{f}` is an
equivalence. -/
theorem isEquivalence_toDescentData_of_isIso_mateEquiv
    [(F.map f.op.toLoc).toFunctor.ReflectsIsomorphisms]
    (hβ : ∀ M, IsIso ((mateEquiv af aq (commSqTwoSquare F XX.condition)).app M))
    (hγ : ∀ N, IsIso ((mateEquiv af₁ aq₁ (commSqTwoSquare F ZZ.condition)).app N)) :
    (F.toDescentData (fun _ : Unit ↦ f)).IsEquivalence := by
  let adj := singletonDescentAdjunction F f XX af af₁
  have hε : ∀ D, IsIso (adj.counit.app D) :=
    isIso_singletonDescentAdjunction_counit_of_isIso_mateEquiv F f XX ZZ af af₁ aq aq₁ hβ hγ
  have hη : ∀ G, IsIso (adj.unit.app G) := by
    intro G
    have h₁ : IsIso ((F.toDescentData (fun _ : Unit ↦ f)).map (adj.unit.app G) ≫
        adj.counit.app ((F.toDescentData (fun _ : Unit ↦ f)).obj G)) := by
      rw [adj.left_triangle_components G]
      exact IsIso.id _
    have h₂ : IsIso ((F.toDescentData (fun _ : Unit ↦ f)).map (adj.unit.app G)) :=
      IsIso.of_isIso_comp_right _ (adj.counit.app ((F.toDescentData (fun _ : Unit ↦ f)).obj G))
    have h₃ : IsIso ((F.map f.op.toLoc).toFunctor.map (adj.unit.app G)) :=
      (DescentData.component F (fun _ : Unit ↦ f) ()).map_isIso
        ((F.toDescentData (fun _ : Unit ↦ f)).map (adj.unit.app G))
    exact isIso_of_reflects_iso _ (F.map f.op.toLoc).toFunctor
  exact adj.toEquivalence.isEquivalence_functor

end Pseudofunctor

end CategoryTheory

end
