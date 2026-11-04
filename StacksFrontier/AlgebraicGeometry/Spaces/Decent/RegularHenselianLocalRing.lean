module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodCofiltered
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularLocalRings
public import StacksFrontier.RingTheory.Henselian.HenselizationCompletion

/-!
# Regularity of the henselian local ring of a decent algebraic space

The henselian local ring of a decent algebraic space at a point is a henselization of the local
ring of an elementary étale neighborhood at its distinguished point, and regularity of a
Noetherian local ring is unchanged on passing to a henselization. Regularity of the space at the
point — which is regularity of the local ring of any étale scheme chart above it — is therefore
regularity of the henselian local ring.

## Main results

* `AlgebraicGeometry.Space.isRegularAt_iff_isRegularLocalRing_henselianLocalRing`: a locally
  Noetherian decent algebraic space is regular at a point exactly when its henselian local ring
  there is a regular local ring.

## References

* [Stacks Project, Tag 0AH9](https://stacks.math.columbia.edu/tag/0AH9)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 06LN](https://stacks.math.columbia.edu/tag/06LN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- An algebraic space which is decent and locally Noetherian is regular at a point exactly when
its henselian local ring there is a regular local ring: that ring is a henselization of the local
ring of an elementary étale neighborhood at its distinguished point, and regularity of a
Noetherian local ring is invariant under henselization. -/
theorem isRegularAt_iff_isRegularLocalRing_henselianLocalRing
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hDecent : IsDecentSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (x : points B S hS X) :
    IsRegularAt B S hS X x ↔
      IsRegularLocalRing
        (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) := by
  obtain ⟨E, -, -, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hX hDecent x
  have hEetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf E.toSpace :=
    (isEtale_iff_presheaf_of_yoneda B S hS E.toSpace).1 E.etale_toSpace
  have hENoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj E.scheme) :=
    (exists_atlas_iff_forall_etale B S hS X
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) hX).mp hN E.scheme E.toSpace hEetale
  let : IsLocallyNoetherian E.scheme.left.1 := hENoeth
  let : IsLocalRing (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) :=
    henselianLocalRing_isLocalRing B S hS X hX x hDecent
  let := stalkAlgebra B S hS X hX x hDecent E
  let := henselianLocalRing_isHenselization B S hS X hX x hDecent E
  have hiff := StacksDraft.isRegularLocalRing_iff_of_isHenselization
    (R := E.scheme.left.1.presheaf.stalk E.point)
    (H := (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)))
  let p : FieldValuedPoint B S hS (yoneda.obj E.scheme) :=
    ⟨E.scheme.left.1.residueField E.point, E.residueField_contained,
      E.scheme.left.1.fromSpecResidueField E.point ≫ E.scheme.hom.1,
      residueFieldMap B S hS E.scheme E.point E.residueField_contained⟩
  have hp : schemePoint B S hS E.scheme p = E.point :=
    E.scheme.left.1.fromSpecResidueField_apply E.point _
  rw [← hiff]
  constructor
  · intro h
    have hreg := h E.scheme E.toSpace hEetale p E.map_point
    rwa [hp] at hreg
  · intro h
    refine (isRegularAt_iff_exists_etale_chart B S hS X hX x).mpr
      ⟨E.scheme, E.toSpace, hEetale, p, E.map_point, ?_⟩
    rwa [hp]

end AlgebraicGeometry.Space

end
