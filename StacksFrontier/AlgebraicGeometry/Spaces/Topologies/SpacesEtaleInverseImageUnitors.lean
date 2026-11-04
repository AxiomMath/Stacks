module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeUnitors

/-!
# The unit coherences of the spaces-étale inverse image

Stacks 03G2 attaches to a morphism `f : X ⟶ Y` of algebraic spaces over `S` a base-change
functor on the spaces-étale sites (part (1)), a composition isomorphism for it (part (2)), and
hence a morphism of the spaces-étale topoi (part (3)). On the *inverse* images the resulting
comparison data are the adjoint mates of the direct-image ones: the composition isomorphism
`AlgebraicGeometry.Space.spacesEtaleInverseImage_comp` with its pentagon
`AlgebraicGeometry.Space.spacesEtaleInverseImage_comp_assoc`, and the *identity* datum on
inverse images together with its two unitor coherences, which are constructed here as the mates
of the direct-image unit data. With them the inverse-image side of Stacks 03G2 carries the full
set of pseudofunctor comparison data and coherences, stated directly rather than only
implicitly inside `AlgebraicGeometry.Space.spacesEtalePseudofunctor`.

The proofs are instantiations: `CategoryTheory.LocallyDiscrete.lId`,
`CategoryTheory.LocallyDiscrete.lComp_comp_id` and
`CategoryTheory.LocallyDiscrete.lComp_id_comp` transfer an identity datum and its two unitor
coherences from a coherent family of right adjoints to the family of left adjoints, and the
direct-image family together with
`AlgebraicGeometry.Space.spacesEtaleSheafPushforwardId`,
`AlgebraicGeometry.Space.spacesEtaleSheafPushforward_comp_id` and
`AlgebraicGeometry.Space.spacesEtaleSheafPushforward_id_comp` is exactly such a family. This
mirrors how `AlgebraicGeometry.Space.spacesEtaleInverseImage_comp_assoc` is obtained from
`AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp_assoc`.

A functor on the spaces-étale (or big fppf) site whose value at `y : T ⟶ Y` involves the
inverse image `y⁻¹` has, for its functoriality, exactly these three isomorphisms as its
`Functor.map_id` and `Functor.map_comp` witnesses.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleInverseImage_id`: the identity datum for the
  spaces-étale inverse images, i.e. the adjoint mate of
  `AlgebraicGeometry.Space.spacesEtaleSheafPushforwardId`.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleInverseImage_comp_id` and
  `AlgebraicGeometry.Space.spacesEtaleInverseImage_id_comp`: the two unitor coherences for the
  spaces-étale inverse images;
* `AlgebraicGeometry.Space.spacesEtalePseudofunctor_mapId` and
  `AlgebraicGeometry.Space.spacesEtalePseudofunctor_mapComp`: the identity and composition
  comparisons of `AlgebraicGeometry.Space.spacesEtalePseudofunctor` are the two isomorphisms
  above, so the two unitor coherences are literally that pseudofunctor's unitors.

## Implementation notes

None of the assertions of Stacks 03G2 is a unit coherence: the source states the base-change
functor, its composition isomorphism and the induced morphism of topoi, and no coherence among
them. The statements here are the further coherences a pseudofunctor needs, and carry no tag.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The identity datum for the spaces-étale inverse images.** The inverse image of
spaces-étale sheaves along an identity morphism of algebraic spaces is the identity functor.
Unlike for the direct images, where
`AlgebraicGeometry.Space.spacesEtaleSheafPushforwardId` comes from the site-level identity
comparison by precomposition, there is no such description here: the inverse image is only
given as a left adjoint, so this isomorphism is the adjoint mate of the direct-image one. -/
noncomputable abbrev spacesEtaleInverseImage_id (X : AlgebraicSpaces B S hS) :
    spacesEtaleInverseImage B S hS (𝟙 X) ≅ 𝟭 (spacesEtaleSheafCat B S hS X) :=
  LocallyDiscrete.lId (spacesEtaleSheafCat B S hS)
    (fun {_ _} f => spacesEtaleInverseImage B S hS f)
    (fun {_ _} f => spacesEtaleSheafPushforward B S hS f)
    (fun {_ _} f => spacesEtaleAdjunction B S hS f)
    (fun X => spacesEtaleSheafPushforwardId B S hS X) X

/-- **The first unitor coherence for the spaces-étale inverse images**: comparing the inverse
image along `p ≫ 𝟙` with the inverse image along `𝟙` followed by the inverse image along `p`,
and then discarding the identity, is the identification of the two morphisms. This is the
adjoint mate of `AlgebraicGeometry.Space.spacesEtaleSheafPushforward_comp_id`. -/
theorem spacesEtaleInverseImage_comp_id {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y) :
    (spacesEtaleInverseImage_comp B S hS p (𝟙 Y)).hom ≫
        Functor.whiskerRight (spacesEtaleInverseImage_id B S hS Y).hom
            (spacesEtaleInverseImage B S hS p) ≫
          (Functor.leftUnitor (spacesEtaleInverseImage B S hS p)).hom =
      eqToHom (congrArg (fun k : X ⟶ Y => spacesEtaleInverseImage B S hS k)
        (Category.comp_id p)) :=
  LocallyDiscrete.lComp_comp_id (spacesEtaleSheafCat B S hS)
    (fun {_ _} f => spacesEtaleInverseImage B S hS f)
    (fun {_ _} f => spacesEtaleSheafPushforward B S hS f)
    (fun {_ _} f => spacesEtaleAdjunction B S hS f)
    (fun X => spacesEtaleSheafPushforwardId B S hS X)
    (fun {_ _ _} f g => spacesEtaleSheafPushforwardComp B S hS f g)
    (fun {_ _} p => spacesEtaleSheafPushforward_comp_id B S hS p) p

/-- **The second unitor coherence for the spaces-étale inverse images**: comparing the inverse
image along `𝟙 ≫ p` with the inverse image along `p` followed by the inverse image along `𝟙`,
and then discarding the identity, is the identification of the two morphisms. This is the
adjoint mate of `AlgebraicGeometry.Space.spacesEtaleSheafPushforward_id_comp`. -/
theorem spacesEtaleInverseImage_id_comp {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y) :
    (spacesEtaleInverseImage_comp B S hS (𝟙 X) p).hom ≫
        Functor.whiskerLeft (spacesEtaleInverseImage B S hS p)
            (spacesEtaleInverseImage_id B S hS X).hom ≫
          (Functor.rightUnitor (spacesEtaleInverseImage B S hS p)).hom =
      eqToHom (congrArg (fun k : X ⟶ Y => spacesEtaleInverseImage B S hS k)
        (Category.id_comp p)) :=
  LocallyDiscrete.lComp_id_comp (spacesEtaleSheafCat B S hS)
    (fun {_ _} f => spacesEtaleInverseImage B S hS f)
    (fun {_ _} f => spacesEtaleSheafPushforward B S hS f)
    (fun {_ _} f => spacesEtaleAdjunction B S hS f)
    (fun X => spacesEtaleSheafPushforwardId B S hS X)
    (fun {_ _ _} f g => spacesEtaleSheafPushforwardComp B S hS f g)
    (fun {_ _} p => spacesEtaleSheafPushforward_id_comp B S hS p) p

/-- The identity comparison of `AlgebraicGeometry.Space.spacesEtalePseudofunctor` is
`AlgebraicGeometry.Space.spacesEtaleInverseImage_id`. -/
theorem spacesEtalePseudofunctor_mapId (X : AlgebraicSpaces B S hS) :
    (spacesEtalePseudofunctor B S hS).mapId (.mk (Opposite.op X)) =
      Cat.Hom.isoMk (spacesEtaleInverseImage_id B S hS X) :=
  rfl

/-- The composition comparison of `AlgebraicGeometry.Space.spacesEtalePseudofunctor` is
`AlgebraicGeometry.Space.spacesEtaleInverseImage_comp`. -/
theorem spacesEtalePseudofunctor_mapComp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePseudofunctor B S hS).mapComp g.op.toLoc f.op.toLoc =
      Cat.Hom.isoMk (spacesEtaleInverseImage_comp B S hS f g) :=
  rfl

end AlgebraicGeometry.Space

end
