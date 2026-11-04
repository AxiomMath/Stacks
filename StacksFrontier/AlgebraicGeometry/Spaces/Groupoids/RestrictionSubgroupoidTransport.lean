module

public import StacksFrontier.AlgebraicGeometry.Groupoids.OpenArrowSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Splittings
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RestrictionSubgroupoidFinite

/-!
# From an open finite subgroupoid of the restricted realization to one of the restriction

Let `G` be a groupoid scheme, let `p` be a morphism to its scheme of objects, and let `R'` be a
groupoid scheme realizing the restriction of `G` along `p`.  An open finite subgroupoid `P` of
the restriction of the realization of `G` cuts out, by
`Stacks.Groupoids.GroupoidScheme.arrowOpens`, an open subscheme of the chosen arrow scheme
`AlgebraicGeometry.restrictionArrows G p`; its inverse image along the comparison isomorphism
`CategoryTheory.eqToHom` of the arrow scheme of `R'` with that chosen one is an open subscheme
of the arrow scheme of `R'`.  This file shows that the source and the target of `R'` are finite
on that open subscheme, and concludes that as soon as the open subscheme is stable under the
groupoid operations it is an open finite subgroupoid of `R'` in the sense of conditions (a) and
(b) of Stacks 04RK.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isFinite_openArrowSource_preimage`: the restricted source of
  the realization of the restriction is finite on the inverse image.
* `Stacks.Groupoids.GroupoidScheme.isFinite_openArrowTarget_preimage`: the same for the target.
* `Stacks.Groupoids.GroupoidScheme.nonempty_openFiniteSubgroupoid_of_isArrowSubgroupoid`: an
  open finite subgroupoid of the realization of the restriction exists as soon as the inverse
  image is stable under the groupoid operations.

## Implementation notes

The two finiteness statements share all of their content, which is isolated as a statement about
an arbitrary morphism `ψ` out of the chosen arrow scheme and an arbitrary structure morphism `π`
of `R'` expressed through `ψ` as the fields `source_eq` and `target_eq` of
`AlgebraicGeometry.GroupoidScheme.Restriction` express the source and the target.  Substituting
that expression for `π` is what makes the comparison isomorphism `φ` visible in the goal.

The inclusion of the inverse image followed by `φ` and the inclusion of the open subscheme
itself are two open immersions into the chosen arrow scheme with the same image, so they differ
by an isomorphism; since `φ` is an isomorphism this is `AlgebraicGeometry.Scheme.Hom.preimageIso`
and no range computation is needed.  Finiteness then moves across that isomorphism and across
the comparison isomorphism of the object schemes by stability of finite morphisms under
composition, every isomorphism being finite.

That `φ` is an isomorphism is read off the image of `CategoryTheory.eqToHom` under
`CategoryTheory.Over.forget`, which is the underlying morphism of schemes by definition.

## References

* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left) {X : Over S}
  (hX : C.Contains X.left) (p : X ⟶ G.objects) (U' : AlgebraicSpaces C S hS)
  (g : U' ⟶ (G.realization C hS hU hR hP).objects)
  (e : yoneda.obj (schemeSiteObject C hS hX) ≅ U'.obj)
  (he : e.hom ≫ g.hom = yoneda.map (schemeSiteMap C hS hX hU p))
  (hA : C.Contains (pullback p G.target).left)
  (hB : C.Contains (pullback G.source p).left)
  (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)

/-! ### Finiteness on the inverse image of an open of the chosen arrow scheme -/

/-- **A structure morphism of a groupoid scheme realizing a restriction is finite on the inverse
image of an open subscheme of the chosen arrow scheme on which the corresponding projection of
the chosen arrow scheme is finite.**  The hypothesis `hπ` is the shape of the fields `source_eq`
and `target_eq` of `AlgebraicGeometry.GroupoidScheme.Restriction`. -/
private theorem isFinite_openOverι_comp_preimage
    (R' : AlgebraicGeometry.GroupoidScheme.Restriction G p)
    (Q : (AlgebraicGeometry.restrictionArrows G p).left.Opens)
    (ψ : AlgebraicGeometry.restrictionArrows G p ⟶ X)
    (π : R'.groupoid.arrows ⟶ R'.groupoid.objects)
    (hπ : π = eqToHom R'.arrows_eq ≫ ψ ≫ eqToHom R'.objects_eq.symm)
    (hfin : AlgebraicGeometry.IsFinite (Q.ι ≫ ψ.left)) :
    AlgebraicGeometry.IsFinite
      (openOverι R'.groupoid.arrows ((eqToHom R'.arrows_eq).left ⁻¹ᵁ Q) ≫ π).left := by
  subst hπ
  have hiso : ∀ {A B : Over S} (h : A = B), IsIso (eqToHom h).left := fun h =>
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom h)))
  have hθ : (Scheme.Hom.preimageIso (eqToHom R'.arrows_eq).left Q).hom ≫ Q.ι =
      ((eqToHom R'.arrows_eq).left ⁻¹ᵁ Q).ι ≫ (eqToHom R'.arrows_eq).left :=
    Scheme.Hom.preimageIso_hom_ι (eqToHom R'.arrows_eq).left Q
  have hrw : ((eqToHom R'.arrows_eq).left ⁻¹ᵁ Q).ι ≫ (eqToHom R'.arrows_eq).left ≫ ψ.left ≫
        (eqToHom R'.objects_eq.symm).left =
      (Scheme.Hom.preimageIso (eqToHom R'.arrows_eq).left Q).hom ≫
        (Q.ι ≫ ψ.left) ≫ (eqToHom R'.objects_eq.symm).left := by
    simp only [← Category.assoc]
    rw [hθ]
  have hkey : AlgebraicGeometry.IsFinite
      (((eqToHom R'.arrows_eq).left ⁻¹ᵁ Q).ι ≫ (eqToHom R'.arrows_eq).left ≫ ψ.left ≫
        (eqToHom R'.objects_eq.symm).left) := by
    rw [hrw]
    exact MorphismProperty.comp_mem _ _ _ inferInstance
      (MorphismProperty.comp_mem _ _ _ hfin inferInstance)
  exact hkey

/-! ### The two finiteness conditions and the resulting open finite subgroupoid -/

/-- **The source of a groupoid scheme realizing the restriction is finite on the inverse image of
the open subscheme cut out by the arrows of an open finite subgroupoid of the restriction of the
realization.** -/
theorem isFinite_openArrowSource_preimage
    (R' : AlgebraicGeometry.GroupoidScheme.Restriction G p)
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid) :
    AlgebraicGeometry.IsFinite
      (openArrowSource ((eqToHom R'.arrows_eq).left ⁻¹ᵁ
        arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA P.arrows P.arrows_open)).left := by
  have hfin : Space.IsFinite C S hS (P.arrows.ι ≫
      (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP) g).hom) :=
    P.source_finite
  exact isFinite_openOverι_comp_preimage G p R'
    (arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA P.arrows P.arrows_open)
    (AlgebraicGeometry.restrictionSource G p) R'.groupoid.source R'.source_eq
    (isFinite_arrowOpens_source G C hS hU hR hP hX p U' g e he hA hB hRA
      P.arrows P.arrows_open hfin)

/-- **The target of a groupoid scheme realizing the restriction is finite on the inverse image of
the open subscheme cut out by the arrows of an open finite subgroupoid of the restriction of the
realization.** -/
theorem isFinite_openArrowTarget_preimage
    (R' : AlgebraicGeometry.GroupoidScheme.Restriction G p)
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid) :
    AlgebraicGeometry.IsFinite
      (openArrowTarget ((eqToHom R'.arrows_eq).left ⁻¹ᵁ
        arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA P.arrows P.arrows_open)).left := by
  have hfin : Space.IsFinite C S hS (P.arrows.ι ≫
      (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP) g).hom) :=
    P.target_finite
  exact isFinite_openOverι_comp_preimage G p R'
    (arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA P.arrows P.arrows_open)
    (AlgebraicGeometry.restrictionTarget G p) R'.groupoid.target R'.target_eq
    (isFinite_arrowOpens_target G C hS hU hR hP hX p U' g e he hA hB hRA
      P.arrows P.arrows_open hfin)

/-- **An open finite subgroupoid of the restriction of the realization of a groupoid scheme gives
one of any groupoid scheme realizing the restriction**, as soon as the open subscheme it cuts out
on the arrow scheme of that realization is stable under the groupoid operations. -/
theorem nonempty_openFiniteSubgroupoid_of_isArrowSubgroupoid
    (R' : AlgebraicGeometry.GroupoidScheme.Restriction G p)
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid)
    (hclos : Stacks.Groupoids.GroupoidScheme.IsArrowSubgroupoid
      ((eqToHom R'.arrows_eq).left ⁻¹ᵁ
        arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA P.arrows P.arrows_open)) :
    Nonempty (Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid R'.groupoid) :=
  ⟨openFiniteSubgroupoidOfOpens _ hclos
    (isFinite_openArrowSource_preimage G C hS hU hR hP hX p U' g e he hA hB hRA R' P)
    (isFinite_openArrowTarget_preimage G C hS hU hR hP hX p U' g e he hA hB hRA R' P)⟩

end Stacks.Groupoids.GroupoidScheme

end
