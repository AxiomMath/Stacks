module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The small étale site of Stacks 021B has enough geometric points

Mathlib proves that the geometric points of a scheme `S` form a conservative family of points
of *its own* small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`, whose objects are
all schemes étale over `S`.  The small étale site of Stacks 021B,
`AlgebraicGeometry.SmallEtale.topology`, is a different site: its objects are cut down by the
size cutoff of an ambient big étale site `B`, and its covering families are cut down by `B`'s
covering bound.  This file transfers the conservativity statement to that site.

Both restrictions have to be dealt with.  The restriction on objects is harmless because the
*fibre* of a geometric point is computed from lifts to objects of the site, and an affine
neighbourhood of a lift always fits below the cutoff — this is already recorded in
`AlgebraicGeometry.geometricPointSitePoint`.  The restriction on coverings is the content of
`AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective`: a jointly surjective family
is refined by a *selected* one, so it still generates a covering sieve.

The conservativity criterion used is SGA 4 IV 6.5 (a), Mathlib's
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.mk'`: a family of points is
conservative as soon as every sieve on which all the fibre functors act surjectively is a
covering sieve.  Here surjectivity of the fibre functors is exactly joint surjectivity on
underlying spaces, because a geometric point of `S` over the image of a point `t` of an object
`X` of the site lifts to `X` through `t` — étale morphisms admit lifts through separably closed
points.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.ofPoint`: the geometric point of `S` at a point of its
  underlying space, built from an algebraic closure of the residue field there.
* `AlgebraicGeometry.geometricSitePoints`: the family of points of the small étale site of `S`
  given by those geometric points.

## Main results

* `AlgebraicGeometry.isConservativeFamilyOfPoints_geometricSitePoints`: **the geometric points
  of `S` form a conservative family of points of the small étale site of Stacks 021B.**
* `AlgebraicGeometry.SmallEtale.topology_hasEnoughPoints`: that site has enough points, so the
  fibre functors at geometric points jointly reflect isomorphisms, monomorphisms and
  epimorphisms of sheaves in any suitable coefficient category.

## References

* [Stacks Project, Tag 00YK](https://stacks.math.columbia.edu/tag/00YK)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The geometric point of `S` at a point `x` of its underlying space: the spectrum of an
algebraic closure of the residue field at `x`, mapping to `S` by the residue-field
embedding. -/
public noncomputable def GeometricPoint.ofPoint (S : Scheme.{u}) (x : S) : GeometricPoint S where
  residueField := AlgebraicClosure (S.residueField x)
  hom := (Scheme.SpecToEquivOfField (AlgebraicClosure (S.residueField x)) S).symm
    ⟨x, CommRingCat.ofHom (algebraMap (S.residueField x) (AlgebraicClosure (S.residueField x)))⟩

/-- `AlgebraicGeometry.GeometricPoint.ofPoint` lies over the point it was built from. -/
@[simp]
public theorem GeometricPoint.ofPoint_liesOver (S : Scheme.{u}) (x : S) :
    (GeometricPoint.ofPoint S x).LiesOver x := by
  dsimp [GeometricPoint.ofPoint, GeometricPoint.LiesOver, Scheme.SpecToEquivOfField]
  apply Scheme.fromSpecResidueField_apply

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Sheaves of sets on the small étale site of Stacks 021B can be sheafified, the site being
essentially small.

The abelian-coefficient counterpart is
`AlgebraicGeometry.hasSheafify_smallEtaleTopology` of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk`; neither instance subsumes the other, since
that one needs `EssentiallySmall` in the coefficient universe and this one fixes the
coefficients at `Type u`. -/
public noncomputable instance hasSheafify_smallEtaleTopology_type :
    HasSheafify (SmallEtale.topology B S hS) (Type u) :=
  hasSheafifyEssentiallySmallSite _ _

/-- The family of points of the small étale site of `S` attached to the geometric points of `S`
at the points of its underlying space. -/
public noncomputable def geometricSitePoints :
    ObjectProperty (GrothendieckTopology.Point.{u} (SmallEtale.topology B S hS)) :=
  ObjectProperty.ofObj fun x : S ↦ geometricPointSitePoint B S hS (.ofPoint S x)

/-- The family of geometric points is indexed by the points of `S`, hence small. -/
public instance small_geometricSitePoints :
    ObjectProperty.Small.{u} (geometricSitePoints B S hS) :=
  inferInstanceAs (ObjectProperty.Small.{u} (ObjectProperty.ofObj _))

/-- **The geometric points of `S` form a conservative family of points of the small étale site
of Stacks 021B.**

By SGA 4 IV 6.5 (a) it suffices to show that a sieve on which every geometric fibre functor
acts surjectively is a covering sieve.  Given a point `t` of the underlying scheme of an object
`X` of the site, the geometric point of `S` at the image of `t` lifts to `X` through `t`,
because the structure morphism of `X` is étale and the source of the geometric point is the
spectrum of a separably closed field.  Surjectivity then yields an arrow of the sieve whose
image contains `t`, so the arrows of the sieve are jointly surjective, and
`AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective` makes it a covering sieve
despite the covering bound of the ambient big étale site. -/
@[sga "4½ Arcata 2.3.2" "partial"]
public theorem isConservativeFamilyOfPoints_geometricSitePoints :
    (geometricSitePoints B S hS).IsConservativeFamilyOfPoints := by
  refine .mk' fun {X} R hR ↦ SmallEtale.mem_topology_of_jointlySurjective fun t ↦ ?_
  set s : GeometricPoint S := .ofPoint S ((B.inclusion.map X.obj.hom) t) with hs
  obtain ⟨l, hl, hlt⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    (B.inclusion.map X.obj.hom) s.hom t
    (by rw [hs]; exact (GeometricPoint.ofPoint_liesOver ..).symm)
  obtain ⟨Y, g, hg, y, hy⟩ := hR
    ⟨geometricPointSitePoint B S hS s, ObjectProperty.ofObj_apply _ _⟩ ⟨l, hl⟩
  refine ⟨Y, g, hg, y.1 default, ?_⟩
  have hfac : y.1 ≫ (SmallEtale.toScheme B S hS).map g = l := congrArg Subtype.val hy
  rw [← hlt, ← hfac]
  rfl

/-- **The small étale site of Stacks 021B has enough points**, the geometric points of `S`
forming a small conservative family. -/
public instance topology_hasEnoughPoints :
    GrothendieckTopology.HasEnoughPoints.{u} (SmallEtale.topology B S hS) where
  exists_objectProperty :=
    ⟨geometricSitePoints B S hS, small_geometricSitePoints B S hS,
      isConservativeFamilyOfPoints_geometricSitePoints B S hS⟩

/-- **A map of sheaves of sets on the small étale site of Stacks 021B is an isomorphism exactly
when it is bijective on the stalk at every geometric point.**

The "only if" direction holds at every geometric point because the stalk functor is a left
adjoint; the "if" direction needs only the geometric points at the points of the underlying
space of `S`, which are the conservative family
`AlgebraicGeometry.isConservativeFamilyOfPoints_geometricSitePoints`.

`AlgebraicGeometry.GeometricPoint.isIso_iff_forall_bijective_stalkFunctor` is the same criterion
for Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology`, whose objects are *all* schemes
étale over `S`; this one is for the site of Stacks 021B, cut down by the size cutoff and the
covering bound of an ambient big étale site. -/
@[sga "2 XIV 1.9" "special case", sga "4 VIII 3.13" "E = X", sga "4½ Arcata 2.3.2" "special case"]
public theorem isIso_iff_forall_bijective_sheafFiber
    {F G : Sheaf (SmallEtale.topology B S hS) (Type u)} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ s : GeometricPoint S,
      Function.Bijective ((geometricPointSitePoint B S hS s).sheafFiber.map φ) := by
  refine ⟨fun _ s ↦ ?_, fun h ↦ ?_⟩
  · rw [← isIso_iff_bijective]
    infer_instance
  · rw [(isConservativeFamilyOfPoints_geometricSitePoints B S
      hS).jointlyReflectIsomorphisms_type.isIso_iff]
    intro Φ
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).1 Φ.property
    rw [← hx, isIso_iff_bijective]
    exact h _

end AlgebraicGeometry

end
