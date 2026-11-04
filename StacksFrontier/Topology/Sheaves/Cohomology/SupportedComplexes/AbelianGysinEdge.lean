module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CounitGysinEdge
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianSupportedSectionsCounit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Gysin edge morphism for sheaves of abelian groups

Let `Z` be a closed subset of a ringed space `X`, let `i : Z ⟶ X` be its inclusion and let `c` be
an integer.  For an object `K` of `D(Ab(X))` whose abelian local cohomology sheaves
`ℋ ^i_Z(K) = H ^i(R𝓗^{ab}_Z(K))` vanish in the degrees `i < c`, this file constructs the
**abelian Gysin edge morphism**

`i_*ℋ ᶜ_Z(K)[-c] ⟶ K`

of `D(Ab(X))`, and proves it natural in `K`.

This is the abelian counterpart of `Stacks.DeRham.CohomologicalGysin.supportedGysinEdge`, the
edge morphism [Stacks, Tag 0G8A] is built from, which exists only for sheaves of **modules** on a
ringed space.  The square of [Stacks, Tag 0G8B] compares that morphism, carried along the
forgetful functor to abelian sheaves, against a morphism of abelian sheaves that is the forgetful
image of nothing — a de Rham differential is not `𝒪_X`-linear — so an edge morphism living on the
abelian side is what that square has to be stated against.

Nothing new is constructed: the whole content is that the recipe of `supportedGysinEdge` is
available at a variable abelian category as `Stacks.CounitGysinEdge.edge`, and that the abelian
side supplies the three inputs that recipe asks for — the derived supported sections
`Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsOnClosed`, the exact direct
image `Stacks.Cohomology.SupportedComplexes.abelianClosedPushforward`, and the counit
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportPushCounit`.

## Main definitions

* `abelianSupportedGysinEdge`: **the abelian Gysin edge morphism `i_*ℋ ᶜ_Z(K)[-c] ⟶ K`.**

## Main results

* `abelianSupportedGysinEdge_naturality`: **it is natural in the coefficient complex**, among the
  objects satisfying the vanishing hypothesis.
* `abelianSupportedGysinEdge_eq_edge`: it *is* `Stacks.CounitGysinEdge.edge` at the three abelian
  inputs, by `rfl`.  This is the form a chase against the module-side edge morphism uses, both
  edge morphisms then being the same construction at different data.

## Implementation notes

**Carried hypotheses: none beyond `hZ : IsClosed Z` and the vanishing.**  Closedness is used only
where `Stacks.Cohomology.AbelianSupportedCounit.derivedAbelianSupportedPushforward` already needs
it: the direct image from `Z` is exact, so it is applied through
`CategoryTheory.Functor.mapDerivedCategory` rather than derived, and the two exactness lemmas
`abelianClosedPushforward_preservesFiniteLimits` and
`abelianClosedPushforward_preservesFiniteColimits` are `lemma`s rather than instances and are
supplied by `letI` exactly as they are there.  The
vanishing is the hypothesis of [Stacks, Tag 0G8A] itself, read on abelian sheaves.

The counit is `abelianSupportPushCounit`, whose source `derivedAbelianSupportedPushforward` is
*defined* as the composite the generic construction expects, so it is accepted where that
composite is, without a transport.

**No declaration here carries a `@[stacks ...]` attribute.**  The edge morphism is a construction
of this library; the tagged statement it serves is [Stacks, Tag 0G8A], recorded on
`Stacks.DeRham.CohomologicalGysin.gysinCohomologyMap`.

## References

* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G8B](https://stacks.math.columbia.edu/tag/0G8B)
* [Stacks Project, Lemma 20.34.4 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.SupportedComplexes

universe u

namespace Stacks.Cohomology.AbelianSupportedCounit

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport.abelianSheaves_isGrothendieckAbelian

open DerivedCategory

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **The abelian local cohomology sheaf of a complex**: for `K` in `D(Ab(X))` and `c : ℤ`, the
degree-`c` cohomology sheaf `ℋ ᶜ_Z(K)` of `R𝓗^{ab}_Z(K)`, a sheaf of abelian groups on `Z`.  This
is the abelian counterpart of
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplex`. -/
@[sga "4 V 6.3" "special case"]
public abbrev abelianLocalCohomologySheafOfComplex (c : ℤ)
    (K : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})) :
    Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u} :=
  (homologyFunctor (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) c).obj
    ((derivedAbelianSupportedSectionsOnClosed X Z hZ).obj K)

include hZ in
/-- **The abelian Gysin edge morphism `i_*ℋ ᶜ_Z(K)[-c] ⟶ K`** of `D(Ab(X))`: the comparison
`ℋ ᶜ_Z(K)[-c] ⟶ R𝓗^{ab}_Z(K)` supplied by the vanishing of the abelian local cohomology sheaves
in the degrees below `c`, pushed forward along the inclusion of the closed subset, followed by the
abelian counit `abelianSupportPushCounit` of [Stacks, Tag 0A3B].

This is `Stacks.CounitGysinEdge.edge` at the abelian data, hence literally the construction of
`Stacks.DeRham.CohomologicalGysin.supportedGysinEdge` with the modules replaced by abelian
sheaves. -/
public def abelianSupportedGysinEdge (c : ℤ)
    (K : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))
    (hvan : ∀ i : ℤ, i < c → IsZero (abelianLocalCohomologySheafOfComplex X Z hZ i K)) :
    (singleFunctor (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) c).obj
        ((abelianClosedPushforward Z).obj
          (abelianLocalCohomologySheafOfComplex X Z hZ c K)) ⟶ K :=
  letI := abelianClosedPushforward_preservesFiniteLimits X Z hZ
  letI := abelianClosedPushforward_preservesFiniteColimits X Z hZ
  haveI : ((derivedAbelianSupportedSectionsOnClosed X Z hZ).obj K).IsGE c :=
    (DerivedCategory.isGE_iff _ c).2 hvan
  Stacks.CounitGysinEdge.edge (derivedAbelianSupportedSectionsOnClosed X Z hZ)
    (abelianClosedPushforward Z) (abelianSupportPushCounit X Z hZ) c K

include hZ in
/-- **The abelian Gysin edge morphism is `Stacks.CounitGysinEdge.edge` at the abelian data**, by
`rfl`.  A chase comparing it with the module-side `supportedGysinEdge` goes through this, both
morphisms then being the generic construction at different inputs. -/
public theorem abelianSupportedGysinEdge_eq_edge (c : ℤ)
    (K : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))
    (hvan : ∀ i : ℤ, i < c → IsZero (abelianLocalCohomologySheafOfComplex X Z hZ i K)) :
    letI := abelianClosedPushforward_preservesFiniteLimits X Z hZ
    letI := abelianClosedPushforward_preservesFiniteColimits X Z hZ
    haveI : ((derivedAbelianSupportedSectionsOnClosed X Z hZ).obj K).IsGE c :=
      (DerivedCategory.isGE_iff _ c).2 hvan
    abelianSupportedGysinEdge X Z hZ c K hvan =
      Stacks.CounitGysinEdge.edge (derivedAbelianSupportedSectionsOnClosed X Z hZ)
        (abelianClosedPushforward Z) (abelianSupportPushCounit X Z hZ) c K :=
  rfl

include hZ in
/-- **The abelian Gysin edge morphism is natural in the coefficient complex.**  For `g : K ⟶ K'` a
morphism of `D(Ab(X))` whose source and target both satisfy the vanishing hypothesis, the square
formed by the two edge morphisms `i_*ℋ ᶜ_Z(-)[-c] ⟶ -`, by `g` and by `i_*ℋ ᶜ_Z(g)` placed in
degree `c` commutes.

This is `Stacks.CounitGysinEdge.edge_naturality` at the abelian data: the naturality of Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, that of the edge morphism out of the
bottom cohomology object, and that of the abelian counit. -/
public theorem abelianSupportedGysinEdge_naturality (c : ℤ)
    {K K' : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})}
    (hvan : ∀ i : ℤ, i < c → IsZero (abelianLocalCohomologySheafOfComplex X Z hZ i K))
    (hvan' : ∀ i : ℤ, i < c → IsZero (abelianLocalCohomologySheafOfComplex X Z hZ i K'))
    (g : K ⟶ K') :
    (singleFunctor (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) c).map
          ((abelianClosedPushforward Z).map
            ((homologyFunctor
                (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) c).map
              ((derivedAbelianSupportedSectionsOnClosed X Z hZ).map g))) ≫
        abelianSupportedGysinEdge X Z hZ c K' hvan' =
      abelianSupportedGysinEdge X Z hZ c K hvan ≫ g := by
  let := abelianClosedPushforward_preservesFiniteLimits X Z hZ
  let := abelianClosedPushforward_preservesFiniteColimits X Z hZ
  have := (DerivedCategory.isGE_iff _ c).2 hvan
  have := (DerivedCategory.isGE_iff _ c).2 hvan'
  exact Stacks.CounitGysinEdge.edge_naturality
    (derivedAbelianSupportedSectionsOnClosed X Z hZ) (abelianClosedPushforward Z)
    (abelianSupportPushCounit X Z hZ) c g

end Stacks.Cohomology.AbelianSupportedCounit

end
