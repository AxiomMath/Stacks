module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SpecializationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of an object of the derived category at a geometric point, as derived global sections

Let `X` be a scheme and `x : Spec Ω ⟶ X` a geometric point, `Ω` a separably closed field. For an
abelian sheaf `F` on the small étale site of `X` there is the canonical comparison

`F_x ⟶ Γ(x, x⁻¹F)`

of `AlgebraicGeometry.geometricStalkToPullbackSectionsAb`, which Stacks 03Q1 identifies as an
isomorphism. This file carries that comparison to the unbounded derived categories: for an object
`K` of `D(X_étale)` there is a canonical map

`K_x ⟶ RΓ(x, x⁻¹K)`

in `D(Ab)`, natural in `K`, whose source is the stalk of `K` at `x` and whose target is the
unbounded derived global sections on `Spec Ω` of the restriction of `K` to the geometric point.

It also records the identification of the two inverse images of abelian étale sheaves the library
carries, `Stacks.EtaleCohomology.smallEtalePullbackAb` and
`Stacks.EtaleCohomology.etaleAbelianInverseImage`, on sheaves and on unbounded derived categories.
The two direct images are the same functor on the nose, but the two inverse images are not: one is
the abstract left adjoint of the direct image, the other the left Kan extension followed by
sheafification. The map above is stated with the first and the derived base change map of
Stacks 0A2A with the second, so the identification is what lets the two be composed.

## Main definitions

* `AlgebraicGeometry.derivedGeometricStalkToPullbackSections` — the canonical map
  `K_x ⟶ RΓ(x, x⁻¹K)` on unbounded derived categories of abelian sheaves on small étale sites.
* `Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleAbelianInverseImage` and
  `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage` — the
  identification of the two inverse images of abelian étale sheaves, on sheaves and on unbounded
  derived categories.

## Main results

* `AlgebraicGeometry.derivedGeometricStalkToPullbackSections_fac_app` — on every complex of
  abelian sheaves the derived comparison factors the degreewise comparison on sheaves through
  the unit of the derivation of global sections on the geometric point, which determines it.

## Implementation notes

*The descent.* It is the one of `Stacks.DerivedFunctor.exactDerivedDesc`, the same device that
produces `AlgebraicGeometry.vanishingCyclesMap` and
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction`. Its three inputs are present
here without any hypothesis. The stalk at a geometric point is exact — it preserves finite limits
because the étale neighbourhoods of the point are cofiltered and abelian groups satisfy AB5, and
it preserves finite colimits because it has the skyscraper sheaf functor as a right adjoint — so
its action on unbounded derived categories is a right derived functor of itself,
`Stacks.DerivedFunctor.isRightDerivedFunctor_mapDerivedCategory`. Inverse image is exact as well,
so it too acts degreewise. Global sections on `Spec Ω` are not exact and are not assumed to be:
they are derived, and the existence of that derivation is carried as an instance argument. The map
is therefore the unique transformation of derived categories whose composite with the
identification of the two actions of the stalk is the degreewise comparison followed by the unit
of the derivation.

*The map is not claimed to be an isomorphism.* On sheaves that is the content of Stacks 03Q1,
the invertibility of `AlgebraicGeometry.geometricStalkToPullbackSectionsAb`. Granted it, the
derived statement needs in addition that global sections on the small étale site of `Spec Ω` are
exact — equivalently that the étale cohomology of a separably closed point vanishes in positive
degrees — so that `RΓ(x, -)` is the degreewise action of `Γ(x, -)` and the descent of an
isomorphism is an isomorphism.

*Relation to Stacks 0GJN.* The map is close to `AlgebraicGeometry.vanishingCyclesMap`, which is
the same descent applied to `AlgebraicGeometry.etaleStalkToSectionsAb` for a scheme `T` over the
strict henselization of `X` at `x`. It is not an instance of it: that map is indexed by a big
étale site containing `X` and by a morphism to the strict henselization, both of which the
comparison with sections on the geometric point does without. The two agree in spirit — the
geometric point is a scheme over the strict henselization, through
`AlgebraicGeometry.geometricPointToStrictHenselization` — but identifying them would require the
transitivity of restriction of germs through the strict henselization, which is a separate
statement about the underived maps.

*The two inverse images.* `Stacks.EtaleCohomology.smallEtalePullbackAb` is
`CategoryTheory.Functor.sheafPullback`, the left adjoint named by the `IsRightAdjoint` instance of
the direct image, while `Stacks.EtaleCohomology.etaleAbelianInverseImage` is
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`, the left Kan extension along the
opposite base-change functor followed by sheafification. Mathlib keeps them apart and relates them
by `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso`; the identification below
is the same `CategoryTheory.Adjunction.leftAdjointUniq`, taken for the two adjunctions this
library actually names, and is carried to derived categories by
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`, both inverse images being
exact. No such identification is needed for direct images:
`Stacks.EtaleCohomology.etaleAbelianDirectImage` and
`Stacks.EtaleCohomology.smallEtalePushforwardAb` are the same term, and so are their derivations.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### The two inverse images of abelian étale sheaves -/

section InverseImageComparison

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The two inverse images of abelian sheaves on the small étale sites which this library
carries agree: `Stacks.EtaleCohomology.smallEtalePullbackAb` is the abstract left adjoint of the
direct image, `Stacks.EtaleCohomology.etaleAbelianInverseImage` is the left Kan extension along
the opposite base-change functor followed by sheafification, and both are left adjoint to the
same direct image, so they are canonically isomorphic. -/
public def smallEtalePullbackAbIsoEtaleAbelianInverseImage :
    smallEtalePullbackAb f ≅ etaleAbelianInverseImage.{u, u + 1} f :=
  Adjunction.leftAdjointUniq (smallEtaleAdjunctionAb f)
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f)

/-- The identification of the two inverse images of abelian étale sheaves, on unbounded derived
categories: both are exact, so each acts degreewise, and isomorphic exact functors induce
isomorphic functors on derived categories. -/
public def smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage :
    smallEtaleDerivedPullbackAb f ≅ etaleAbelianDerivedInverseImage.{u, u + 1} f :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
    (smallEtalePullbackAbIsoEtaleAbelianInverseImage f)

end InverseImageComparison

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-! ### The derived comparison of the stalk with sections on the geometric point -/

section DerivedPullbackSections

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
  [((Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1}) (.up ℤ))]

/-- The canonical map `K_x ⟶ RΓ(x, x⁻¹K)` from the stalk at a geometric point `x` of `X` of an
object `K` of the unbounded derived category of abelian sheaves on the small étale site of `X`, to
the unbounded derived global sections on the geometric point of the restriction of `K` to it,
natural in `K`.

This is the derived analogue of `AlgebraicGeometry.geometricStalkToPullbackSectionsAb`, the
comparison `F_x ⟶ Γ(x, x⁻¹F)` on abelian sheaves which Stacks 03Q1 identifies as an isomorphism.
The stalk functor is exact, so its action on unbounded derived categories is a right derived
functor of itself, and the comparison on sheaves extends uniquely to one of derived categories.
No hypothesis on `X` or on `K` enters, and no isomorphism is inverted. -/
public def derivedGeometricStalkToPullbackSections :
    smallEtaleDerivedStalkAb x ⟶
      smallEtaleDerivedPullbackAb x ⋙ smallEtaleDerivedGlobalSections (Spec (.of Ω)) :=
  Stacks.DerivedFunctor.exactDerivedDesc (smallEtaleStalkAb x) (smallEtalePullbackAb x)
    (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1})
    (smallEtaleDerivedGlobalSections (Spec (.of Ω)))
    (smallEtaleDerivedGlobalSectionsUnit (Spec (.of Ω)))
    (geometricStalkToPullbackSectionsAb x)

/-- On every complex of abelian sheaves on the small étale site of `X`, the canonical map from the
derived stalk to derived global sections on the geometric point factors the degreewise comparison
`AlgebraicGeometry.geometricStalkToPullbackSectionsAb` through the unit of the derivation of
global sections on the geometric point, read through the identifications of the degreewise actions
of the stalk and of inverse image with their actions on derived categories.

Since the degreewise action of the stalk functor is a right derived functor of itself, this
property determines the map. -/
public theorem derivedGeometricStalkToPullbackSections_fac_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleStalkAb x).mapDerivedCategoryFactorsh.inv.app J ≫
        (derivedGeometricStalkToPullbackSections x).app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtaleStalkAb x) (smallEtalePullbackAb x)
          (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1})
          (geometricStalkToPullbackSectionsAb x)).app J) ≫
        (smallEtaleDerivedGlobalSectionsUnit (Spec (.of Ω))).app
            (((smallEtalePullbackAb x).mapHomotopyCategory (.up ℤ)).obj J) ≫
          (smallEtaleDerivedGlobalSections (Spec (.of Ω))).map
            ((smallEtalePullbackAb x).mapDerivedCategoryFactorsh.inv.app J) :=
  Stacks.DerivedFunctor.exactDerivedDesc_fac_app (smallEtaleStalkAb x) (smallEtalePullbackAb x)
    (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1})
    (smallEtaleDerivedGlobalSections (Spec (.of Ω)))
    (smallEtaleDerivedGlobalSectionsUnit (Spec (.of Ω)))
    (geometricStalkToPullbackSectionsAb x) J

end DerivedPullbackSections

end AlgebraicGeometry

end
