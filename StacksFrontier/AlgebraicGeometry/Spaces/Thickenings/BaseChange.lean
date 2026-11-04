module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# Base change of a thickening of an algebraic space

Let `X' ⟶ Y'` be a morphism of algebraic spaces over a scheme `S` and let `Y ⊂ Y'` be a
thickening, that is a closed subspace whose inclusion is bijective on points. Its inverse
image `Y ×_{Y'} X' ⊂ X'` is then a thickening of `X'`, and the inclusion of the inverse image
sits in a canonical commutative square over the inclusion of `Y`.

## Main definitions

* `AlgebraicGeometry.Space.thickeningBaseChangeHom` is that commutative square, as a morphism
  in the arrow category of presheaves on the big fppf site.

## Main results

* `AlgebraicGeometry.Space.isThickening_preimage`: the inverse image of a thickening is a
  thickening.
* `CategoryTheory.Subfunctor.fromPreimage_comp`: the projections out of iterated inverse images
  compose, with no transport along an equality of subfunctors.
* `AlgebraicGeometry.Space.closedSubspacePreimage_comp` and
  `AlgebraicGeometry.Space.subspaceProjection_comp`: the same two laws for a closed subspace of
  an algebraic space and a composable pair of morphisms, both on the nose.

## Implementation notes

A closed subspace is a subfunctor of its ambient algebraic space, and its inverse image along
a morphism is the pointwise preimage `CategoryTheory.Subfunctor.preimage`, which
`CategoryTheory.Subfunctor.isPullback_preimage` identifies with the fibre product. Closedness
of the inverse image is Stacks 083Q; what is proved here is that bijectivity on points is
inherited, which is base change of a surjective morphism of algebraic spaces (Stacks 03MH)
applied to the square that the identification supplies.

Parts of the source lemma that measure the *order* of the thickening — that a base change of a
first-order, finite-order or `n`th-order thickening again has that order — are not stated here,
because they are phrased through the chartwise defining ideal of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Order.lean`, which this file does not import.
They are proved in `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/BaseChangeOrder.lean`, as
`AlgebraicGeometry.Space.isNthOrderThickening_preimage` and its first- and finite-order
corollaries, which carry the remaining parts of the tag.

**The composition laws hold on the nose.**  Iterating the construction along `ψ : V ⟶ U` and
`φ : U ⟶ X` produces no comparison data: the subfunctor `(ψ ≫ φ)⁻¹(Z)` *is* `ψ⁻¹(φ⁻¹(Z))` and
the projection to `Z` *is* the composite of the two projections, both by `rfl`, since the
sections of an inverse image are a set-theoretic preimage and `Set.preimage_comp` is `rfl`.
The three laws below are therefore stated as plain equalities with no `CategoryTheory.eqToHom`.
They are the two bookkeeping ingredients of the functoriality in the étale source of
[Stacks Project, Tag 04CO], whose remaining ingredients are the pasting law
`AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` and the compatibility of the
Stacks 03LW comparison with composition,
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction`.

## References

* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Subfunctor

/-- **The projections out of iterated inverse images compose.**  For a subfunctor `G` of `F` and
morphisms `f : F'' ⟶ F'` and `g : F' ⟶ F`, the projection of the inverse image of `G.preimage g`
along `f`, followed by the projection of the inverse image of `G` along `g`, is the projection of
the inverse image of `G` along `f ≫ g`.

The two sides have the *same* source: `CategoryTheory.Subfunctor.preimage_comp` identifies
`G.preimage (f ≫ g)` with `(G.preimage g).preimage f`, and that identification holds by `rfl`,
because the sections of an inverse image are a set-theoretic preimage and `Set.preimage_comp` is
itself `rfl`.  So no transport along an equality of subfunctors is needed to state the law, and
none appears in a restriction map built from it. -/
theorem fromPreimage_comp {C : Type*} [Category C] {F F' F'' : C ⥤ Type u}
    (G : Subfunctor F) (f : F'' ⟶ F') (g : F' ⟶ F) :
    (G.preimage g).fromPreimage f ≫ G.fromPreimage g = G.fromPreimage (f ≫ g) :=
  rfl

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inverse image of a closed subspace along a composite is the iterated inverse image.**
For morphisms `ψ : V ⟶ U` and `φ : U ⟶ X` of algebraic spaces and a closed subspace `Z ⊆ X`, the
closed subspace `(ψ ≫ φ)⁻¹(Z)` of `V` is the closed subspace `ψ⁻¹(φ⁻¹(Z))`.

This is `CategoryTheory.Subfunctor.preimage_comp` carried to closed subspaces: the underlying
subfunctors agree by `rfl`, and `AlgebraicGeometry.Space.IsClosedSubspace` is a proposition, so
the two closedness witnesses — one of them nested inside the other — agree by proof irrelevance
and the two elements of `AlgebraicGeometry.Space.ClosedSubspaces` are equal on the nose. -/
theorem closedSubspacePreimage_comp {V U X : AlgebraicSpaces B S hS} (ψ : V ⟶ U) (φ : U ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) :
    (⟨Z.1.preimage (ψ ≫ φ).hom,
        isClosedSubspace_preimage B S hS (ψ ≫ φ).hom Z.1 X.2 V.2 Z.2⟩ :
      ClosedSubspaces B S hS V.1) =
    ⟨(Z.1.preimage φ.hom).preimage ψ.hom,
        isClosedSubspace_preimage B S hS ψ.hom (Z.1.preimage φ.hom) U.2 V.2
          (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2)⟩ :=
  rfl

/-- **The projections of the inverse images of a closed subspace compose.**  For morphisms
`ψ : V ⟶ U` and `φ : U ⟶ X` of algebraic spaces and a closed subspace `Z ⊆ X`, the projection
`ψ⁻¹(φ⁻¹(Z)) ⟶ φ⁻¹(Z)` followed by the projection `φ⁻¹(Z) ⟶ Z` is the projection
`(ψ ≫ φ)⁻¹(Z) ⟶ Z`, as morphisms of algebraic spaces.

This is `CategoryTheory.Subfunctor.fromPreimage_comp` read in the category of algebraic spaces,
whose morphisms are those of the underlying presheaves.  Together with
`AlgebraicGeometry.Space.closedSubspacePreimage_comp` it is the input that the pasting law
`AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` consumes when the two stacked squares
are the squares `AlgebraicGeometry.Space.conormalEtaleRestrictionSquare` of `ψ` and of `φ`. -/
theorem subspaceProjection_comp {V U X : AlgebraicSpaces B S hS} (ψ : V ⟶ U) (φ : U ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) :
    (ObjectProperty.homMk ((Z.1.preimage φ.hom).fromPreimage ψ.hom) :
        (⟨((Z.1.preimage φ.hom).preimage ψ.hom).toFunctor,
            (isClosedSubspace_preimage B S hS ψ.hom (Z.1.preimage φ.hom) U.2 V.2
              (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2)).1⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨(Z.1.preimage φ.hom).toFunctor,
            (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
          AlgebraicSpaces B S hS)) ≫
      (ObjectProperty.homMk (Z.1.fromPreimage φ.hom) :
        (⟨(Z.1.preimage φ.hom).toFunctor,
            (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) =
    ObjectProperty.homMk (Z.1.fromPreimage (ψ ≫ φ).hom) :=
  rfl

/-- **Stacks 09ZX.** The commutative square expressing that the inclusion of the inverse image
of a subfunctor `Y` of `Y'` along `f : X' ⟶ Y'` lies over the inclusion of `Y`: a morphism in
the arrow category from `(Y ×_{Y'} X' ⟶ X')` to `(Y ⟶ Y')`. -/
@[stacks 09ZX "morphism of thickenings"]
def thickeningBaseChangeHom {Y' X' : AlgebraicSpaces B S hS} (Y : Subfunctor Y'.1)
    (f : X' ⟶ Y') :
    Arrow.mk (Y.preimage f.hom).ι ⟶ Arrow.mk Y.ι :=
  Arrow.homMk' (Y.fromPreimage f.hom) f.hom (Subfunctor.fromPreimage_ι Y f.hom)

/-- **Stacks 09ZX.** The inverse image of a thickening `Y ⊂ Y'` along a morphism of algebraic
spaces `f : X' ⟶ Y'` is a thickening of `X'`. -/
@[stacks 09ZX "base change of a thickening"]
theorem isThickening_preimage {Y' X' : AlgebraicSpaces B S hS} (Y : Subfunctor Y'.1)
    (f : X' ⟶ Y') (hY : IsThickening B S hS Y' Y) :
    IsThickening B S hS X' (Y.preimage f.hom) := by
  have hpre : IsClosedSubspace B S hS (Y.preimage f.hom) :=
    isClosedSubspace_preimage B S hS f.hom Y Y'.property X'.property hY.1
  refine ⟨hpre, ?_⟩
  let Y₀ : AlgebraicSpaces B S hS := ⟨Y.toFunctor, hY.1.1⟩
  let X₀ : AlgebraicSpaces B S hS := ⟨(Y.preimage f.hom).toFunctor, hpre.1⟩
  let q : X₀ ⟶ Y₀ := ObjectProperty.homMk (Y.fromPreimage f.hom)
  let p : X₀ ⟶ X' := ObjectProperty.homMk (Y.preimage f.hom).ι
  let g : Y₀ ⟶ Y' := ObjectProperty.homMk Y.ι
  have hpull : IsPullback q p g f :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _)
      (Subfunctor.isPullback_preimage f.hom Y)
  exact isSurjective_of_isPullback B S hS hpull hY.2

add_to_stacks 09ZX "cartesian square" CategoryTheory.Subfunctor.isPullback_preimage

end AlgebraicGeometry.Space

end
