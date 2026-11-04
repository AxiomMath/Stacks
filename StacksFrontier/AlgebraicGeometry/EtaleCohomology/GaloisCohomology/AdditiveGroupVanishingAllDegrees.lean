module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AdditiveSheafAssociatedStructure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.AdditiveGroupVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The additive chain of [Stacks, Tag 03QV] in every degree and every characteristic

Let `K` be a field.  For every `i ≥ 1`,

  `0 = H^i(Spec K, 𝒪) = H^i_étale(Spec(K)_étale, 𝐆_a) = H^i(Gal(Kˢᵉᵖ/K), Kˢᵉᵖ)`,

`Kˢᵉᵖ` on the right being the Galois module with addition as group law.  This is the second
displayed chain of equalities of [Stacks, Tag 03QV], and it is proved here the way the source
proves it: the first term vanishes because `Spec K` is affine and the structure sheaf is
quasi-coherent ([Stacks, Tag 01XB]), the first equality is the comparison of Zariski with étale
cohomology for a quasi-coherent module ([Stacks, Tag 03P2]) read at `𝐆_a` through the
identification of `𝐆_a` with the associated sheaf of the structure module ([Stacks, Tag 03P6]),
and the second equality is part (3) of [Stacks, Tag 03QU] at `𝐆_a`.

Nothing is assumed of the characteristic.  This is what the Galois-cohomological route of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/GaloisCohomology/AdditiveGroupVanishing.lean`
cannot reach: there the vanishing is proved from cochains in degrees one and two, and from
rational coefficients ([Stacks, Tag 0DV3] part (2)) in every degree but only in characteristic
zero, the additive group of a field of characteristic `p` being killed by `p`.  The route taken
here is insensitive to that, because it never computes Galois cohomology at all -- it computes
the cohomology of an affine scheme and transports.

## Main definitions

* `AlgebraicGeometry.hgroupStructureSheafAddEquivSheafHAdditiveSheaf`: **the first equality**
  `H^i(X, 𝒪) ≅ H^i_étale(X_étale, 𝐆_a)`, in positive degree, for an arbitrary scheme.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_additiveSheaf_of_isAffine`: **the middle term**
  `H^i_étale(X_étale, 𝐆_a) = 0` for `i ≥ 1` and `X` affine.
* `AlgebraicGeometry.isZero_continuousGroupCohomology_sepClosureAdd`: **the last term**
  `H^i(Gal(Kˢᵉᵖ/κ), Kˢᵉᵖ) = 0` for `i ≥ 1`, in every characteristic.
* `AlgebraicGeometry.isZero_continuousGroupCohomology_sepClosureAdd_ofAlgebraicClosure`: the
  same with no choice of big étale site or geometric point in the statement.

## Implementation notes

**The coefficient universe is where the work is.**  The quasi-coherent comparison of
[Stacks, Tag 03P2] on the small étale site of `X : Scheme.{u}` is stated at coefficients
`AddCommGrpCat.{u}`, the morphism universe of the site, while `𝐆_a` and the Galois comparison of
[Stacks, Tag 03QU] live at `AddCommGrpCat.{u + 1}`, the object universe -- the stalk at a
geometric point being a colimit over a category whose objects are in `Type (u + 1)`.  The two are
reconciled by `AlgebraicGeometry.smallEtaleSheafHUliftAddEquiv`, which says that raising the
coefficient universe does not change the cohomology, applied to the un-raised `𝐆_a`
`AlgebraicGeometry.additiveSheafBase`.

**The local instances.**  Sheafification and the `Ext` universe at coefficients
`AddCommGrpCat.{u + 1}` are not found by instance search -- the general instances are indexed by
`max (u + 1) v` and search cannot solve `max (u + 1) ?v = u + 1` -- so they are supplied by name.
They are `AlgebraicGeometry.hasSheafify_smallEtale_objectUniverse`,
`AlgebraicGeometry.hasExt_sheaf_smallEtale_objectUniverse` and
`AlgebraicGeometry.hasExt_sheaf_smallEtale_morphismUniverse`, all declared in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleCoefficientLift.lean` and re-enabled
here with `attribute [local instance]`.

## References

* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV): the example whose
  additive chain of equalities this is.
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2): the first equality.
* [Stacks Project, Tag 03P6](https://stacks.math.columbia.edu/tag/03P6): `𝐆_a` as the structure
  sheaf read additively.
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU): part (3) at `𝐆_a`, the
  second equality.
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB): the vanishing of the
  first term.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.CoefficientLift

universe u

namespace AlgebraicGeometry

section Etale

variable (X : Scheme.{u})

-- Sheafification of abelian groups at the object universe of the small étale site, and `Ext`
-- of abelian sheaves at the object and at the morphism universe of that site.  All three are
-- `local` where they are declared, so the attribute is re-enabled here.
attribute [local instance] hasSheafify_smallEtale_objectUniverse
  hasExt_sheaf_smallEtale_objectUniverse hasExt_sheaf_smallEtale_morphismUniverse
  Stacks.Topology.hasExt_sheafOpens

/-- **The first equality of the additive chain of [Stacks, Tag 03QV]**: in positive degree the
Zariski cohomology of the structure sheaf of a scheme is the étale cohomology of `𝐆_a`,

  `H ^ (n + 1)(X, 𝒪) ≅ H ^ (n + 1)(X_étale, 𝐆_a)`,

the right-hand side at the coefficient universe in which [Stacks, Tag 03QU] part (3) compares
étale with Galois cohomology.  Nothing is assumed of the scheme.

This is [Stacks, Tag 03P2] for the structure module, read at `𝐆_a` through
`AlgebraicGeometry.additiveSheafBaseIsoSmallEtaleAssociatedSheaf` -- the identification of `𝐆_a`
with the associated sheaf of the structure module, which is [Stacks, Tag 03P6] -- and carried
from the morphism universe of the site to its object universe by
`AlgebraicGeometry.smallEtaleSheafHUliftAddEquiv`. -/
public def hgroupStructureSheafAddEquivSheafHAdditiveSheaf (n : ℕ) :
    Hgroup X.ringCatSheaf ⊤ (n + 1) (Scheme.unitModule X) ≃+
      Sheaf.H.{u + 1, u + 1} (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} X) (n + 1) :=
  (hgroupIsoSmallEtaleGlobalCohomology X (Scheme.unitModule X) n).addCommGroupIsoToAddEquiv.trans
    (((sheafHIsoCongr (additiveSheafBaseIsoSmallEtaleAssociatedSheaf X) (n + 1)).symm).trans
      ((smallEtaleSheafHUliftAddEquiv X (additiveSheafBase X) (n + 1)).trans
        (sheafHIsoCongr (additiveSheafBaseUliftIso X) (n + 1))))

/-- **`H^i_étale(X_étale, 𝐆_a) = 0` in every degree `i ≥ 1` for an affine scheme**, at the
coefficient universe in which [Stacks, Tag 03QU] part (3) compares étale with Galois cohomology.

`𝐆_a` is the associated sheaf of the structure module
(`AlgebraicGeometry.additiveSheafBaseIsoSmallEtaleAssociatedSheaf`), whose positive-degree étale
cohomology over an affine scheme vanishes by [Stacks, Tag 03P2] together with [Stacks, Tag 01XB];
that statement is at the morphism universe of the site and is carried to the object universe by
`AlgebraicGeometry.smallEtaleSheafHUliftAddEquiv`. -/
@[sga "1 XI 6.9" "partial", sga "3 XXII 5.9.6" "special case"]
public theorem subsingleton_sheafH_additiveSheaf_of_isAffine [IsAffine X] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} X) q) :=
  (subsingleton_sheafH_congr (additiveSheafBaseUliftIso X) q).mp
    ((subsingleton_smallEtaleSheafH_ulift_iff X (additiveSheafBase X) q).mpr
      (subsingleton_sheafH_additiveSheafBase_of_isAffine X q hq))

end Etale

section Galois

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

include B hK in
/-- **`H^q(Gal(Kˢᵉᵖ/κ), Kˢᵉᵖ) = 0` in every degree `q ≥ 1`**, `κ` being the residue field at the
image of the geometric point and `Kˢᵉᵖ` its separable closure written additively.  **Nothing is
assumed of the characteristic.**

This is the last term of the additive chain of [Stacks, Tag 03QV].  It is obtained from the
vanishing of the étale cohomology of `𝐆_a` over `Spec K`, which is affine, through part (3) of
[Stacks, Tag 03QU] at `𝐆_a`. -/
public theorem isZero_continuousGroupCohomology_sepClosureAdd (q : ℕ) (hq : 0 < q) :
    IsZero (continuousGroupCohomology.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar) q (sepClosureAddGModule K sbar)) :=
  (subsingleton_additiveSheafH_iff_isZero B K hK sbar q).mp
    (subsingleton_sheafH_additiveSheaf_of_isAffine (Spec (.of K)) q hq)

end Galois

section Absolute

variable (K : Type u) [Field K]

/-- **`H^q(Gal(Kˢᵉᵖ/K), Kˢᵉᵖ) = 0` in every degree `q ≥ 1` and every characteristic**, with no
choice of big étale site or geometric point in the statement: the geometric point is the one
attached to an algebraic closure of `K`, at which the residue field of `Spec K` is a copy of `K`
and `Kˢᵉᵖ` is a separable closure of it.

This is the last term of the additive chain
`0 = H^i(Spec K, 𝒪) = H^i_étale(Spec(K)_étale, 𝐆_a) = H^i(G, Kˢᵉᵖ)` of [Stacks, Tag 03QV]; the
first term is `AlgebraicGeometry.isZero_hgroup_structureSheaf_spec_field` and the middle one is
`AlgebraicGeometry.subsingleton_sheafH_additiveSheaf_of_isAffine`. -/
public theorem isZero_continuousGroupCohomology_sepClosureAdd_ofAlgebraicClosure
    (q : ℕ) (hq : 0 < q) :
    IsZero (continuousGroupCohomology.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup (GeometricPoint.ofAlgebraicClosure K)) q
      (sepClosureAddGModule K (GeometricPoint.ofAlgebraicClosure K))) :=
  isZero_continuousGroupCohomology_sepClosureAdd (BigEtaleSite.containing (Spec (.of K))) K
    (BigEtaleSite.contains_containing _) (GeometricPoint.ofAlgebraicClosure K) q hq

end Absolute

end AlgebraicGeometry

end
