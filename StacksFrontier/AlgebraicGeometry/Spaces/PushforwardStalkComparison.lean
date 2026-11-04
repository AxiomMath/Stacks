module

public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedComplexDerivedStalk

/-!
# The canonical comparison between the stalks of a direct image and of a sheaf

Let `f : Y ⟶ X` be a relatively representable morphism of algebraic spaces over a scheme `S`
and let `ȳ` be a geometric point of `Y` with image `x̄ = f(ȳ)`. For an abelian sheaf `F` on the
small étale site of `Y` there is a canonical map `(f_*F)_{x̄} ⟶ F_ȳ`, natural in `F`: the stalk
at `x̄` of a sheaf on `X` is the stalk at `ȳ` of its inverse image, Stacks 04K2 part (4), and
the counit `f^{-1}f_*F ⟶ F` of the adjunction between inverse and direct image maps the latter
to the stalk of `F`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkMap` is that comparison, as a
  morphism of functors `f_* ⋙ (-)_{x̄} ⟶ (-)_ȳ`.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleAbelianPushforwardStalkMap_of_isClosedImmersion`:
  for a closed immersion the comparison is an isomorphism, because the counit is, Stacks 04E5
  part (2).
* `AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkIso_hom`: for a closed immersion the
  comparison is the isomorphism
  `AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkIso`.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- **The canonical map from the stalk of a direct image to the stalk of the sheaf.** For a
relatively representable morphism `f : Y ⟶ X` of algebraic spaces over `S` and a geometric
point `ȳ` of `Y` with image `x̄ = f(ȳ)`, the map `(f_*F)_{x̄} ⟶ F_ȳ`, natural in the abelian
sheaf `F` on the small étale site of `Y`.

It is the composite of the identification `(f_*F)_{x̄} = (f^{-1}f_*F)_ȳ` of Stacks 04K2
part (4) with the stalk at `ȳ` of the counit `f^{-1}f_*F ⟶ F`. -/
def smallEtaleAbelianPushforwardStalkMap (f : Y ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom) (y : GeometricPoint B S hS Y.1) :
    smallEtaleAbelianPushforward.{u + 1} B S hS f hf ⋙
        smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y) ⟶
      smallEtaleAbelianStalk B S hS y :=
  Functor.whiskerLeft _ (smallEtaleAbelianInverseImageStalkIso B S hS f hf y).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (smallEtaleAbelianInverseImageAdjunction B S hS f hf).counit
      (smallEtaleAbelianStalk B S hS y) ≫
    (Functor.leftUnitor _).hom

/-- **The comparison on stalks is an isomorphism along a closed immersion.** For a closed
immersion `i : Z ⟶ X` of algebraic spaces over `S` and a geometric point `z̄` of `Z`, the
canonical map `(i_*F)_{i(z̄)} ⟶ F_{z̄}` is an isomorphism: the direct image along a closed
immersion is fully faithful, so the counit of the adjunction is invertible, Stacks 04E5
part (2). -/
instance isIso_smallEtaleAbelianPushforwardStalkMap_of_isClosedImmersion
    {Z : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (z : GeometricPoint B S hS Z.1) :
    IsIso (smallEtaleAbelianPushforwardStalkMap B S hS i hi.rep z) := by
  have := (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).full
  have :=
    (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).faithful
  have : IsIso (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful
      (h := smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep)
  unfold smallEtaleAbelianPushforwardStalkMap
  infer_instance

/-- **The closed-immersion stalk comparison is the canonical one.** The isomorphism
`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkIso` of a closed immersion is the
canonical map `(i_*F)_{i(z̄)} ⟶ F_{z̄}` on stalks. -/
theorem smallEtaleAbelianPushforwardStalkIso_hom {Z : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (z : GeometricPoint B S hS Z.1) :
    (smallEtaleAbelianPushforwardStalkIso B S hS i hi z
        (geometricPointMap i.hom z) rfl).hom =
      smallEtaleAbelianPushforwardStalkMap B S hS i hi.rep z :=
  rfl

end AlgebraicGeometry.Space

end
