module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsIdComparison

/-!
# The unit law of Stacks 03LU at a morphism presented as an identity

`AlgebraicGeometry.Space.modulePullbackIdIso` is the unit law of [Stacks Project, Tag 03LU]: the
inverse image of `𝒪`-modules along `𝟙 X` is the identity functor.  A consumer, however, rarely
meets the literal `𝟙 X`: it meets a morphism `f : X ⟶ X` which some lemma *says* is the
identity — for instance `AlgebraicGeometry.Space.representedSpaceMap B S hS (𝟙 T)`, which is the
identity of the represented algebraic space by `representedSpaceMap_id` and **not** by `rfl`.

This file states the unit law at such an `f`, with the equality `f = 𝟙 X` as a hypothesis, on
both the direct and the inverse image.  The inverse image along `f` is identified with the
identity functor by transporting along the hypothesis and then applying the unit law, and the
same two steps on the direct image side are what the adjoint description of the unit law asks
for.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardIdIsoOfEq`: the direct image along a morphism
  presented as an identity is the identity functor.

## Main results

* `AlgebraicGeometry.Space.leftAdjointIdIso_modulePullbackAdjunction_of_eq`: **the comparison of
  the inverse image along a morphism presented as an identity with the identity functor is the
  transport followed by the unit law of [Stacks Project, Tag 03LU].**

## Implementation notes

The equation of isomorphisms is `subst` on the hypothesis followed by the definitional identity
`AlgebraicGeometry.Space.modulePullbackIdIso_eq`.  Substituting is available precisely because
the hypothesis is taken at a *variable* morphism: a consumer instantiates it at its own
geometric morphism and the transport appears in the statement, never inside a proof about a
geometric term.  That is the same discipline as
`AlgebraicGeometry.Space.modulePullbackEqToHom`, whose own notes record that taking the
congruence at the functor rather than at one module is what keeps the proof terms small.

**Closing the equation of isomorphisms by `simp` is a kernel deterministic timeout**, and so is
reading it at a module by `congr_app` alone; the route that works is `subst` with explicit
rewrites, and then `Stacks.CategoryTheory.trans_hom_app` applied as a term with both
isomorphisms given explicitly.  That is the discipline the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalChangeOfAmbientAgreement.lean` record.

**A sharper rule holds here, and it cuts the other way from the one recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonUnit.lean`.**  There, giving an
anonymous object a *name* is what lets the kernel's conversion check take its first step.  Here
the opposite holds for a composite of isomorphisms: with the composite
`eqToIso (congrArg (modulePullback B S hS) hf) ≪≫ modulePullbackIdIso B S hS X` behind a `def`,
splitting its forward map at a module — even as a term application of the generic lemma with
every argument explicit — is a kernel deterministic timeout; with the same composite written
out inline as `≪≫` in the statement, the identical term application is free, at 0.2 s for the
file.  So the equation of isomorphisms above is stated against the inline composite and no name
is introduced for it.  A name for the composite would have to be unfolded by the kernel at
exactly the point where it is comparing two `Iso` structures, and unfolding it there sends the
check into `AlgebraicGeometry.Space.modulePullback`'s construction by sheafification.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.CategoryTheory

/-- **The forward map of a composite of two isomorphisms of functors, read at an object.**

Proved by `rfl` at a geometric instance it is a kernel deterministic timeout — the kernel reduces
`AlgebraicGeometry.Space.modulePullback` towards its construction by sheafification — while
applied as a term at plain variables it is free.  This is the same discipline as
`Stacks.CategoryTheory.trans4_hom` of
`StacksFrontier/CategoryTheory/ChangeOfAmbientConormal.lean`, and concretely: the equation
below, stated at the two geometric factors and closed by `congr_app` alone, is that timeout. -/
theorem trans_hom_app {C : Type*} [Category* C] {D : Type*} [Category* D] {F G H : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (X : C) :
    (a ≪≫ b).hom.app X = a.hom.app X ≫ b.hom.app X :=
  rfl

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} (f : X ⟶ X) (hf : f = 𝟙 X)

/-- **The direct image of `𝒪`-modules along a morphism presented as an identity is the identity
functor.**  The transport along `hf` followed by the unit law
`AlgebraicGeometry.Space.modulePushforwardIdIso` of [Stacks Project, Tag 03LU]. -/
def modulePushforwardIdIsoOfEq :
    modulePushforward B S hS f ≅ 𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
  eqToIso (congrArg (modulePushforward B S hS) hf) ≪≫ modulePushforwardIdIso B S hS X

/-- **The comparison of the inverse image along a morphism presented as an identity with the
identity functor is the transport followed by the unit law of [Stacks Project, Tag 03LU].**

The comparison on the left is `CategoryTheory.Adjunction.leftAdjointIdIso` of the adjunction at
`f` against `AlgebraicGeometry.Space.modulePushforwardIdIsoOfEq`, which is the shape in which a
mate calculus produces it; the right-hand side is the shape a consumer states its own results
in.  Substituting `f = 𝟙 X` makes both the definitional
`AlgebraicGeometry.Space.modulePullbackIdIso_eq`. -/
theorem leftAdjointIdIso_modulePullbackAdjunction_of_eq :
    Adjunction.leftAdjointIdIso (modulePullbackAdjunction B S hS f)
        (modulePushforwardIdIsoOfEq B S hS f hf) =
      eqToIso (congrArg (modulePullback B S hS) hf) ≪≫ modulePullbackIdIso B S hS X := by
  subst hf
  rw [modulePushforwardIdIsoOfEq, eqToIso_refl, eqToIso_refl, Iso.refl_trans, Iso.refl_trans,
    modulePullbackIdIso_eq]

/-- **The comparison of the inverse image along a morphism presented as an identity with the
identity functor, read at a module**: it is the transport along the hypothesis followed by the
unit law of [Stacks Project, Tag 03LU].

This is the shape a consumer meets, derived from the equation of isomorphisms, which is where it
is cheap — see the implementation notes. -/
theorem leftAdjointIdIso_modulePullbackAdjunction_of_eq_hom_app
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (Adjunction.leftAdjointIdIso (modulePullbackAdjunction B S hS f)
          (modulePushforwardIdIsoOfEq B S hS f hf)).hom.app M =
      (eqToIso (congrArg (modulePullback B S hS) hf)).hom.app M ≫
        (modulePullbackIdIso B S hS X).hom.app M :=
  (congr_app (congrArg Iso.hom
      (leftAdjointIdIso_modulePullbackAdjunction_of_eq B S hS f hf)) M).trans
    (Stacks.CategoryTheory.trans_hom_app
      (eqToIso (congrArg (modulePullback B S hS) hf)) (modulePullbackIdIso B S hS X) M)

end AlgebraicGeometry.Space

end
