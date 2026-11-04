module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued

/-!
# Formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A *formal algebraic space* over `S`
(Stacks 0AIM) is an fppf sheaf on the big fppf site of `S` which satisfies the set-theoretic
condition of Stacks 0AIS and admits an atlas by affine formal algebraic spaces: a family of
maps `Xᵢ ⟶ X` with each `Xᵢ` an affine formal algebraic space, each map representable by
algebraic spaces and étale, and the induced map `∐ Xᵢ ⟶ X` surjective as a map of sheaves.

The atlas is indexed by a type in `Type (u + 1)`, its coproduct is taken in the sheaf category,
and surjectivity of `∐ Xᵢ ⟶ X` is `CategoryTheory.Sheaf.IsLocallySurjective`, which for sheaves
of sets is equivalent to that morphism being an epimorphism.

A morphism of formal algebraic spaces over `S` is a morphism of the underlying sheaves; it is a
*monomorphism* (Stacks 0AQB) exactly when it is a monomorphism of sheaves, `CategoryTheory.Mono`,
which for sheaves of sets is injectivity on sections over every object of the site.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace`: an fppf sheaf over `S` is a formal
  algebraic space.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AQB](https://stacks.math.columbia.edu/tag/0AQB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-- An fppf sheaf on the big fppf site of `S` is a *formal algebraic space* over `S` when it
satisfies the set-theoretic condition of Stacks 0AIS and admits an atlas by affine formal
algebraic spaces: a family of maps into it whose sources are affine formal algebraic spaces,
each of which is representable by algebraic spaces and étale, and whose induced map from the
coproduct is a surjection of sheaves. -/
@[stacks 0AIM]
abbrev IsFormalAlgebraicSpace (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : FppfSheaf B S hS) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  SatisfiesSetTheoreticCondition B S hS X ∧
    ∃ (I : Type (u + 1)) (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X),
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i)) ∧
      (∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi) ∧
      Sheaf.IsLocallySurjective (Sigma.desc f)

end AlgebraicGeometry.FormalSpace

add_to_stacks 0AQB "monomorphism of the underlying sheaves" CategoryTheory.Mono
add_to_sga "1 V 3.6" CategoryTheory.Mono
add_to_sga "3 VIIB 2.4.1" CategoryTheory.Mono
add_to_sga "3 VIII 3.4" CategoryTheory.Mono
add_to_sga "4 I 10.4" CategoryTheory.Mono
add_to_sga "4 II 3.2" CategoryTheory.Mono
add_to_ega "IV 8.11.5.1" CategoryTheory.Mono

end
