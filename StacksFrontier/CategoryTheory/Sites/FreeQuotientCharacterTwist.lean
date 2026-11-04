module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCharacterTwistTorsor
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistLocalFreeness
public import StacksFrontier.CategoryTheory.Sites.FreeActionOrbitQuotientTorsor

/-!
# The rank one twist attached to a character of a free action with quotient the base

Let `C` be a site with a final object `T`, let a group `G` act by automorphisms on an object
`W` of `C`, let the action be free, let `q : W ⟶ T` exhibit `T` as the quotient `W/G`, and let
`χ : G → ℤˣ` be a character. **Stacks 0727** attaches to this data a sheaf of `ℤ`-modules
`ℤ(χ)` on the base which is locally free of rank one and satisfies

```
H⁰(W, F|_W)^χ = H⁰(T, F ⊗_ℤ ℤ(χ))
```

for every abelian sheaf `F` on the base. This file states that conclusion as one piece of data,
`CategoryTheory.CharacterTwistOfQuotient`, and constructs it from the hypotheses of the source:
a free action together with the identification of the base as the quotient. No torsor property
is assumed — that `W` is a `G`-torsor over the base is the first sentence of the source's proof
and is supplied by `CategoryTheory.IsOrbitQuotient.isTorsorObject`.

The three constituents of the conclusion are the twist `CategoryTheory.characterTwist`, the
covering of the base by `W` together with the trivialization of the twist over `W`
(`CategoryTheory.characterTwistOverIso`), which is the source's *locally free of rank 1, as
checked after restricting to `U' = W`*, and the identification of sections
(`CategoryTheory.IsTorsorObject.twistTensorSectionsEquiv`).

## Main definitions

* `CategoryTheory.CharacterTwistOfQuotient` is the conclusion of Stacks 0727: a sheaf of
  `ℤ`-modules on the base, a covering of the base by `W` on which it is isomorphic to the
  constant sheaf `ℤ`, and the identification of the `χ`-semi-invariant sections of an abelian
  sheaf over `W` with the global sections of its tensor product with that sheaf.

## Main results

* `CategoryTheory.characterTwistOfQuotient`: **Stacks 0727**, the twist exists for a free action
  whose quotient is the base.

## Implementation notes

Finiteness of the group, which the source assumes, is not needed for the conclusion as stated
here: it enters Stacks 0727 only through the geometry of the quotient — that `W/G` is an
algebraic space with étale quotient morphism, so that `W` is an object of the étale site of
`W/G` — which is the ambient situation rather than part of the conclusion. The statement is
therefore recorded at an arbitrary group, which is a generalization of the source.

The geometry of the quotient that Stacks 0727 asserts before it reaches the twist — that the
quotient morphism of a free action is surjective and étale, so that `W` is an object of the
étale site of `W/G` covering it — is, on the big fppf site of a scheme,
`AlgebraicGeometry.Space.isSurjective_toOrbitQuotient` and
`AlgebraicGeometry.Space.isEtale_toOrbitQuotient`.

Local freeness of rank one is recorded as the pair of a covering of the base by `W` and an
isomorphism, over the localization of the site at `W`, between the constant sheaf `ℤ` and the
restriction of the twist. That is the source's own reading: it establishes rank one *after
restricting to `U'`*, with `U' = W` the surjective étale covering it has just produced.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public section

open CategoryTheory.Limits Opposite

universe w u₁ u

namespace CategoryTheory

variable {C : Type u₁} [Category.{u + 1} C] {W : C} {G : Type w} [Group G]

/-- **The conclusion of Stacks 0727**: a sheaf of `ℤ`-modules `ℤ(χ)` on the base `T` of a site,
locally free of rank one, whose tensor product with an abelian sheaf `F` has global sections
the sections of `F` over `W` that transform according to the character `χ`.

Local freeness of rank one is the pair `coversBase`, `trivialization`: the morphisms into `W`
cover the base, and over the localization of the site at `W` the twist is the constant sheaf
`ℤ`. -/
structure CharacterTwistOfQuotient (W : C) (act : G →* Aut W) (χ : G →* ℤˣ)
    (J : GrothendieckTopology C) (T : C) [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (J.over W) AddCommGrpCat.{u + 1}] where
  /-- The sheaf `ℤ(χ)` of `ℤ`-modules on the base. -/
  twist : Sheaf J AddCommGrpCat.{u + 1}
  /-- `W` covers the base: the arrows into `T` whose source admits a morphism to `W` form a
  covering sieve. This is the source's surjective étale `U' ⟶ U`, with `U' = W`. -/
  coversBase : splittingSieve W T ∈ J T
  /-- `ℤ(χ)` is free of rank one over `W`: its restriction to the localization of the site at
  `W` is the constant sheaf `ℤ`. -/
  trivialization :
    (constantSheaf (J.over W) AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≅
      (J.overPullback AddCommGrpCat.{u + 1} W).obj twist
  /-- `H⁰(W, F|_W)^χ = H⁰(T, F ⊗_ℤ ℤ(χ))` for every abelian sheaf `F` on the base. -/
  sectionsEquiv (F : Sheaf J AddCommGrpCat.{u + 1}) :
    characterSections W act χ F.obj ≃+
      ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.presheafTensor F.obj twist.obj)).obj.obj (op T)

variable [UnivLE.{max u₁ (u + 1), u + 1}] {act : G →* Aut W} {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify (J.over W) AddCommGrpCat.{u + 1}]
  [(J.over W).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasLimitsOfSize.{u + 1, max u₁ (u + 1)} AddCommGrpCat.{u + 1}]

/-- **Stacks 0727.** Let `C` be a site with final object `T`, let a group `G` act freely by
automorphisms on an object `W` of `C`, let `q : W ⟶ T` exhibit `T` as the quotient `W/G` and
let `χ : G → ℤˣ` be a character. Then there is a sheaf of `ℤ`-modules `ℤ(χ)` on the base which
is locally free of rank one — trivial over the covering of the base by `W` — and satisfies
`H⁰(W, F|_W)^χ = H⁰(T, F ⊗_ℤ ℤ(χ))` for every abelian sheaf `F` on the base.

That `W` is a `G`-torsor over the base is *not* assumed: it is the first sentence of the
source's proof, and is proved from freeness and the quotient identification in
`CategoryTheory.IsOrbitQuotient.isTorsorObject`. -/
@[stacks 0727]
noncomputable def characterTwistOfQuotient {T : C} {q : W ⟶ T} (hfree : ActsFreelyOnObject act J)
    (hq : IsOrbitQuotient act J q) (hT : IsTerminal T) (χ : G →* ℤˣ) :
    CharacterTwistOfQuotient W act χ J T where
  twist := characterTwist W act χ J
  coversBase := (hq.isTorsorObject hT hfree).splittingSieve_mem T
  trivialization := characterTwistOverIso (hq.isTorsorObject hT hfree) χ
  sectionsEquiv F :=
    ((hq.isTorsorObject hT hfree).twistTensorSectionsEquiv χ hT F).trans
      ((((sheafToPresheaf J AddCommGrpCat.{u + 1}).mapIso
        (characterTwistTensorIso χ F.obj act)).app (op T)).addCommGroupIsoToAddEquiv)

end CategoryTheory

end
