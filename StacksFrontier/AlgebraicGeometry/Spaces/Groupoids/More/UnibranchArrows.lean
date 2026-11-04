module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.GeometricallyUnibranch
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.GeometricArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Translation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.RestrictionFieldExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.UnibranchTransport

/-!
# Geometric unibranchness of the arrow space of a groupoid over a field

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces whose object space is the spectrum of a
field `k`.  Geometric unibranchness of `R` at every point of `|R|` is carried by geometric
unibranchness of the arrow spaces of the restrictions of the groupoid along the algebraically
closed field extensions of `k`, at the points of the arrows whose source and target are
automorphisms.

This is the first reduction in the proof of [Stacks Project, Tag 06E4]: a point `r` of `|R|` is
the image of an arrow `r'` of such a restriction whose source and target are automorphisms of
`Spec k'` (Tag 06E2), the canonical morphism from the arrow space of the restriction to `R` is
flat (Tag 06E1), and geometric unibranchness descends along a flat morphism (Tag 06DQ).

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.extensionSiteObject`: the spectrum of an
  extension field, as an object of the big fppf site over the base.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowPoint`: the point of the arrow
  space of a restriction determined by an arrow over the extension field.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_restrictions`:
  the reduction of Tag 06E4 to the arrow spaces of the restrictions of the groupoid along the
  algebraically closed field extensions.

## Implementation notes

The arrows of the restriction are quantified over as *sections over the extension field
spectrum*, which is the form in which Tag 06E2 produces its arrow, rather than as morphisms of
algebraic spaces out of the object space.

Two further steps of the source proof are **not** carried out here.  The second reduction,
which trades the point of `r'` for the point of the identity arrow using that left translation
by `r'` is an automorphism of the restricted arrow space (Tag 06E3,
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.translationByArrow_isIso`), would weaken the
hypothesis below from all arrows with invertible source and target to the identity alone.  The
local input is geometric unibranchness of the restricted arrow space at the identity, the
computation with the étale local rings of `R` and `R ×_{s, U, t} R` in the last two paragraphs
of the source proof; as a statement about rings that computation is
`StacksDraft.existsUnique_minimalPrimes_of_compositionLaw_indEtale_base`, but what is still
missing is the identification of the étale local ring of `R ×_{s, U, t} R` at `(e, e)` with a
strict henselization of a localization of `B ⊗_k B`, for `B` the local ring of an étale chart
of `R` at `e`.  Both are the reason no `@[stacks 06E4]` attribute appears in this file.

## References

* [Stacks Project, Tag 06E4](https://stacks.math.columbia.edu/tag/06E4)
* [Stacks Project, Tag 06E1](https://stacks.math.columbia.edu/tag/06E1)
* [Stacks Project, Tag 06E2](https://stacks.math.columbia.edu/tag/06E2)
* [Stacks Project, Tag 06E3](https://stacks.math.columbia.edu/tag/06E3)
* [Stacks Project, Tag 06DQ](https://stacks.math.columbia.edu/tag/06DQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {S : Scheme.{u}} (C : BigFppfSite.{u}) (hS : C.Contains S)
  {k : Type u} [Field k] (hk : C.Contains (Spec (.of k)))
  (structureMap : Spec (.of k) ⟶ S)
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (hU : G.objects = Space.fieldSpace C hS hk structureMap)

/-- The spectrum of an extension field `k'` of `k`, as an object of the big fppf site over the
base, with the structure morphism inherited from that of `Spec k`. -/
noncomputable abbrev extensionSiteObject {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k') : BigFppfOver C S hS :=
  Over.mk (⟨Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap⟩ :
    C.obj hk' ⟶ C.obj hS)

/-- The point of `|R'|` determined by an arrow of the restriction of `G` along an extension
field, read as a section of the restricted arrow space over the spectrum of that field. -/
noncomputable def restrictionArrowPoint {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k')
    (r : (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj.obj
        (Opposite.op (extensionSiteObject C hS structureMap hk' i))) :
    Space.points C S hS (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj :=
  Space.FieldValuedPoint.class C S hS _
    { carrier := k'
      contained := hk'
      toBase := Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap
      value := r }

/-- **The first reduction of Stacks 06E4.** Let `G` be a groupoid in algebraic spaces whose
object space is the spectrum of a field `k`.  Suppose that for every algebraically closed field
extension `k'/k` whose spectrum lies in the site, the arrow space of the restriction of `G`
along `Spec k' ⟶ Spec k` is geometrically unibranch at the point of every arrow whose source
and target are automorphisms of `Spec k'`.  Then the arrow space of `G` is geometrically
unibranch.

A point of `|R|` comes from such an arrow of such a restriction by Tag 06E2, the canonical
morphism from the arrows of the restriction to `R` is flat by Tag 06E1, and geometric
unibranchness descends along a flat morphism by Tag 06DQ. -/
theorem isGeometricallyUnibranch_arrows_of_restrictions
    (hres : ∀ (k' : Type u) (_ : Field k') (_ : IsAlgClosed k') (i : k →+* k')
      (hk' : C.Contains (Spec (.of k')))
      (r : (restrictionArrows G
        (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj.obj
          (Opposite.op (extensionSiteObject C hS structureMap hk' i))),
      IsIso ((restrictionSource G
          (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).hom.app
        (Opposite.op (extensionSiteObject C hS structureMap hk' i)) r) →
      IsIso ((restrictionTarget G
          (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).hom.app
        (Opposite.op (extensionSiteObject C hS structureMap hk' i)) r) →
      Space.IsGeometricallyUnibranchAt C S hS (restrictionArrows G
          (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj
        (restrictionArrowPoint C hS hk structureMap G hU hk' i r)) :
    Space.IsGeometricallyUnibranch C S hS G.arrows.obj := by
  intro x
  obtain ⟨k', field', alg', i, hk', r', hclass, hsrc, htgt⟩ :=
    exists_isIso_source_target_over_isAlgClosed C hS structureMap hk B G hU x
  set g := Space.restrictionObjectMap C hS hk hk' structureMap i G hU
  have hflat : Space.IsFlat C S hS (restrictionArrowsToArrows G g).hom :=
    Space.isFlat_of_restrictionDiagramMap C hS hk hk' structureMap i G hU _
      Space.RestrictionDiagramMap.restrictedArrowsToArrows
  have hub := hres k' field' alg' i hk' r' hsrc htgt
  have hdescend := Space.isGeometricallyUnibranchAt_of_isFlatAt C S hS
    (restrictionArrows G g).property G.arrows.property
    (restrictionArrowsToArrows G g).hom
    (restrictionArrowPoint C hS hk structureMap G hU hk' i r')
    ((Space.isFlat_iff_forall_isFlatAt C S hS _).mp hflat _) hub
  have heq : Space.pointsMap C S hS _ (restrictionArrowsToArrows G g).hom
      (restrictionArrowPoint C hS hk structureMap G hU hk' i r') = x := hclass
  rwa [heq] at hdescend

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
