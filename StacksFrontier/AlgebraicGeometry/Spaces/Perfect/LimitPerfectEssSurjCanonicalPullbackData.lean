module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom.CanonicalSystem
public import StacksFrontier.CategoryTheory.PullbackData.LimitHomSystem

/-!
# The canonical pseudofunctoriality of derived pullback as a pullback-pseudofunctor datum

`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` is the canonical
pseudofunctoriality of the derived pullback on the small étale topoi of algebraic spaces, and
`CategoryTheory.PullbackData` is the shape in which the hom-level maps of Stacks 09RI are
written: `CategoryTheory.PullbackData.LimitSystem.projHom` is conjugation by
`CategoryTheory.PullbackData.triangle`, which is built from the datum's composition comparison.

The library already has one such datum for the derived pullback,
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, whose composition comparison is the
universal comparison of the total left derived functor along the composite, and the identity of
that comparison with the one of
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` is **nowhere in the tree**.  So
the hom-level map of Stacks 09RI written with
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, and the comparisons of
`…DerivedPullbackComposition.canonical` in which the
elementary-distinguished-square step's hypothesis `hc` and the bridge of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectDescentBridgeOverlap.lean` are
written, are two unrelated morphisms.

**This file makes that identification unnecessary**, by reading
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` *itself* as a
`CategoryTheory.PullbackData`.  Everything Stacks 09RI is stated with — the transition maps, the
maps to the limit, the colimit statement — is parametric in the datum, so the whole of it is
available with the comparisons the square step uses, and no comparison of two constructions of
`Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` is needed anywhere.

## Main definitions

* `AlgebraicGeometry.Space.canonicalPullbackData`: the canonical pseudofunctoriality of derived
  pullback, as a `CategoryTheory.PullbackData` on the category of algebraic spaces with fibres
  the derived categories of `𝒪`-modules.

## Main results

* `AlgebraicGeometry.Space.canonicalPullbackData_triangle`: the comparison of a presented
  factorisation of this datum is the inverse of the identification of that factorisation of
  `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`.
* `AlgebraicGeometry.Space.projHom_canonicalPullbackData`: **the map to the limit of
  Stacks 09RI, for this datum, written out** — the derived pullback along the projection,
  conjugated by the identification of the factorisation `p_j ≫ k_j = k`.  This is exactly the
  shape of the hypothesis `hfac` of
  `AlgebraicGeometry.Space.hc_edsBridgeComparison_of_factorHom`, so the bridge consumes this map
  with no respelling.

## The hypotheses carried

None.  `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` is unconditional and so is
everything below.  No coherence of the datum is proved or used here: the descent of an
isomorphism from the limit to a stage
(`AlgebraicGeometry.Space.DescentSituation.exists_stageIso_of_homProjection_eq`) is arranged
never to compose two comparisons of different factorisations, so it needs only that conjugation
by a fixed isomorphism preserves identities and composition.

## What is not here

*The identification of the two data.*  Whether
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData.compIso` is the inverse of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackCompIsoOfTwoIso` — equivalently whether the
universal comparison of the total left derived functor along a composite agrees, across the
2-isomorphism of Stacks 03G8, with the composition comparison of Stacks 0D6D — is still open.
It is not needed by anything below and it is not assumed.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe w u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The canonical pseudofunctoriality of the derived pullback of `𝒪`-modules on algebraic
spaces, as a pullback-pseudofunctor datum**: the inverse image along `f` is `Lf^*`, the unit law
and the composition comparison are those of
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`.

This is `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` with the composition comparison
of Stacks 0D6D in place of the universal comparison of the total left derived functor along the
composite; see this file's module documentation for why both are wanted and why no comparison of
the two is needed. -/
def canonicalPullbackData : PullbackData (AlgebraicSpaces B S hS) (derivedModules B S hS) where
  pull f := smallEtaleDerivedModulePullback B S hS f
  idIso X := (DerivedPullbackComposition.canonical B S hS).idIso X
  compIso f g := ((DerivedPullbackComposition.canonical B S hS).iso f g (f ≫ g) rfl).symm

/-- The inverse image of `AlgebraicGeometry.Space.canonicalPullbackData` is the derived
pullback. -/
theorem canonicalPullbackData_pull {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (canonicalPullbackData B S hS).pull f = smallEtaleDerivedModulePullback B S hS f :=
  rfl

/-- **The comparison of a presented factorisation** `f ≫ g = k` **of
`AlgebraicGeometry.Space.canonicalPullbackData` is the inverse of the identification of that
factorisation of `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`.**  This is what
lets the bridge of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectDescentBridgeOverlap.lean`, whose
isomorphisms are the latter, consume the hom-level maps of Stacks 09RI, which are conjugation by
the former. -/
theorem canonicalPullbackData_triangle {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : f ≫ g = k) :
    (canonicalPullbackData B S hS).triangle h =
      ((DerivedPullbackComposition.canonical B S hS).iso f g k h).symm := by
  subst h
  exact PullbackData.triangle_rfl (canonicalPullbackData B S hS) f g

variable {B S hS} {J : Type w} [Preorder J] {b : AlgebraicSpaces B S hS}
  (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) b J)
  (X Y : derivedModules B S hS b) (j : J)

/-- **The map to the limit of Stacks 09RI for
`AlgebraicGeometry.Space.canonicalPullbackData`, written out**: the derived pullback along the
projection `p_j : T ⟶ T_j`, conjugated by the identification of the factorisation
`p_j ≫ k_j = k` of `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` at the source
and at the target.

This is the shape of the hypothesis `hfac` of
`AlgebraicGeometry.Space.hc_edsBridgeComparison_of_factorHom`, whose
`AlgebraicGeometry.Space.edsBridgeInterComp` is that identification for the factorisation
`r_P ≫ t_P = s_P` of the maps of intersections. -/
theorem projHom_canonicalPullbackData
    (φ : ((canonicalPullbackData B S hS).pull (Sys.toBase j)).obj X ⟶
      ((canonicalPullbackData B S hS).pull (Sys.toBase j)).obj Y) :
    Sys.projHom (canonicalPullbackData B S hS) X Y j φ =
      (((DerivedPullbackComposition.canonical B S hS).iso (Sys.proj j) (Sys.toBase j)
            Sys.limitToBase (Sys.proj_toBase j)).app X).inv ≫
        (smallEtaleDerivedModulePullback B S hS (Sys.proj j)).map φ ≫
        (((DerivedPullbackComposition.canonical B S hS).iso (Sys.proj j) (Sys.toBase j)
          Sys.limitToBase (Sys.proj_toBase j)).app Y).hom := by
  rw [PullbackData.LimitSystem.projHom, PullbackData.factorHom,
    canonicalPullbackData_triangle B S hS]
  exact (Functor.conjHom_symm _ φ).symm

/-- **The transition map of Stacks 09RI for
`AlgebraicGeometry.Space.canonicalPullbackData`, written out**: the derived pullback along the
transition morphism `t_{ij} : T_j ⟶ T_i`, conjugated by the identification of the factorisation
`t_{ij} ≫ k_i = k_j`. -/
theorem trans_canonicalPullbackData (i : J) (h : i ≤ j)
    (φ : ((canonicalPullbackData B S hS).pull (Sys.toBase i)).obj X ⟶
      ((canonicalPullbackData B S hS).pull (Sys.toBase i)).obj Y) :
    Sys.trans (canonicalPullbackData B S hS) X Y i j h φ =
      (((DerivedPullbackComposition.canonical B S hS).iso (Sys.transition h) (Sys.toBase i)
            (Sys.toBase j) (Sys.transition_toBase h)).app X).inv ≫
        (smallEtaleDerivedModulePullback B S hS (Sys.transition h)).map φ ≫
        (((DerivedPullbackComposition.canonical B S hS).iso (Sys.transition h) (Sys.toBase i)
          (Sys.toBase j) (Sys.transition_toBase h)).app Y).hom := by
  rw [PullbackData.LimitSystem.trans, PullbackData.factorHom,
    canonicalPullbackData_triangle B S hS]
  exact (Functor.conjHom_symm _ φ).symm

end AlgebraicGeometry.Space

end
