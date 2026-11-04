module

public import StacksFrontier.Homology.Tor.DerivedTensorRestrictScalars
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductFromOnePointTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointDerivedTensorComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The global Künneth map with no parameter

Let `a : X ⟶ S` and `b : Y ⟶ S` be spaces over a base, let `p : W ⟶ X`, `q : W ⟶ Y` and
`f : W ⟶ S` satisfy `p ≫ a = f = q ≫ b`, and set `A = Γ(S, 𝒪_S)`.  Equation 36.23.0.2 of the
Stacks project is the canonical map

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(W, Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

in `D(A)`.  `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap`
constructs it from a global cup product on the base carried as a parameter.  This file discharges
that parameter: the last datum it rested on is assembled here, so the map, its naturality in both
complexes, and its specialization to the fibre product of two schemes are available with no
hypothesis and no stand-in.

The datum is `Stacks.Cohomology.DerivedSectionsLeftAdjoint.BaseTensorComparison`, a comparison of
bifunctors `E(x ⊗^𝐋_A y) ⟶ E x ⊗^𝐋_{𝒪_{({*}, A)}} E y` for the identification `E` of `D(A)` with
the derived category of modules on the coefficient point.  `E` is restriction of scalars along the
ring isomorphism `π^♯` followed by the one-point identification, and the comparison is now
available for each factor:

* for the one-point identification it is
  `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorComparison`;
* for the restriction of scalars it is
  `CochainComplex.DerivedTensor.RestrictScalars.restrictScalarsDerivedTensorComparison`.

## Main definitions

* `Stacks.Cohomology.GlobalKunneth.baseTensorComparison` — the datum, assembled from the two
  factors.
* `Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical` — the global cup product `μ` of
  Cohomology, Section 0FKU on an arbitrary ringed space, with no parameter.
* `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapCanonical` — **the global Künneth map of
  Tag 0G7V with no parameter.**
* `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapSchemeCanonical` — the same map for a
  cartesian square of schemes, at the fibre product `X ×_S Y` with its two projections, which is
  the situation of the source.

## Main results

* `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapCanonical_eq` — it is `kunnethGlobalMap` at
  the canonical cup product, so nothing about the construction changes; only the parameter is
  gone.
* `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapCanonical_naturality` and
  `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapSchemeCanonical_naturality` — the map is
  natural in the two derived modules jointly, for arbitrary `K` and `M` and with no
  quasi-compactness, quasi-separatedness, quasi-coherence or Tor-independence hypothesis.

## Implementation notes

*Nothing is carried.*  Every input is a declaration of this repository: the comparison of the two
derived tensor products along the restriction of scalars of
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.basePointRingEquiv`, the one-point comparison, the
derived-pullback monoidality of Tag 079U (inside
`onePointComparisonOfBaseTensorComparison`), the adjunction
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedBaseAdjunction` of Tag 079W and Tag 0D5W,
the relative Künneth map of Tag 0FLP and the Leray isomorphism of Tag 0D5W.  No `Classical.choice`
is applied to an existence statement.

*Why the assembly is a whiskering of two comparisons.*  `baseToPoint` is `ρ ⋙ E₀` by `rfl`, with
`ρ` the restriction of scalars and `E₀` the one-point identification, so a comparison of
bifunctors for the composite is the comparison for `ρ` whiskered by `E₀`, followed by the
comparison for `E₀` whiskered by `ρ × ρ` — the same split as in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductFromOnePointTensor`,
one level down.

## References

* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeftAdjoint
open Stacks.Cohomology.DerivedSectionsOnAPoint
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.GlobalKunneth

attribute [local instance] HasDerivedCategory.standard

section Spaces

variable (S : RingedSpace.{u, u})

/-! ### The last datum -/

/-- `π^♯` on the whole space, read as an isomorphism of the two *commutative* rings
`A = Γ(S, 𝒪_S)` and `Γ({*}, 𝒪)`: the same isomorphism as
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.basePointRingEquiv`, at the spelling of the rings
that carries their commutative structure, which is the one the derived tensor product of Tag
064M is stated for. -/
def basePointCommRingEquiv : ↥(baseRing (basePoint S)) ≃+* ↥(baseRing S) :=
  basePointRingEquiv S

/-- **The one-point tensor comparison on the base, assembled.**  `baseToPoint` is restriction of
scalars along the ring isomorphism `π^♯` followed by the one-point identification, so its tensor
comparison is the comparison for the restriction of scalars whiskered by the one-point
identification, followed by the one-point comparison whiskered by the restriction of scalars in
each variable. -/
def baseTensorComparison : BaseTensorComparison S :=
  Functor.whiskerRight
      (CochainComplex.DerivedTensor.RestrictScalars.restrictScalarsDerivedTensorComparison
        (basePointCommRingEquiv S)) (basePointExtension S) ≫
    Functor.whiskerLeft (((basePointRestrict S).functor.mapDerivedCategory).prod
      ((basePointRestrict S).functor.mapDerivedCategory))
      (onePointTensorComparison ↥(baseRing S))

/-- **The global cup product of Cohomology, Section 0FKU with no parameter**, on an arbitrary
ringed space: `RΓ(S, U) ⊗^𝐋_A RΓ(S, V) ⟶ RΓ(S, U ⊗^𝐋_{𝒪_S} V)` as a morphism of bifunctors. -/
def globalCupProductCanonical : GlobalCupProduct S :=
  globalCupProductOfBaseTensorComparison S (baseTensorComparison S)

/-- The canonical global cup product is the one the one-point comparison produces. -/
theorem globalCupProductCanonical_eq :
    globalCupProductCanonical S =
      globalCupProductOfBaseTensorComparison S (baseTensorComparison S) :=
  rfl

/-! ### The global Künneth map with no parameter -/

section Maps

variable {S}
variable {X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)

/-- **The global Künneth map of Tag 0G7V, with no parameter.**

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(W, Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

in `D(A)` for `A = Γ(S, 𝒪_S)`, where `p ≫ a = f = q ≫ b`; the source takes `W = X ×_S Y` with its
two projections.  It is defined for arbitrary `K ∈ D(𝒪_X)` and `M ∈ D(𝒪_Y)`, over an arbitrary
base, and it is built from the canonical global cup product of Section 0FKU on the base together
with the relative Künneth map of Tag 0FLP and the Leray isomorphism of Tag 0D5W. -/
@[stacks 0G7V "the map, for arbitrary K ∈ D(𝒪_X) and M ∈ D(𝒪_Y) over an arbitrary base"]
def kunnethGlobalMapCanonical (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((tensorBase S).obj ((sectionsOverBase a).obj K)).obj ((sectionsOverBase b).obj M) ⟶
      (sectionsOverBase f).obj
        (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj K)).obj
          ((derivedPullback q).obj M)) :=
  kunnethGlobalMap a b p q f hp hq (globalCupProductCanonical S) K M

/-- The map with no parameter is `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMap` at the
canonical global cup product: the construction of Tag 0G7V is reused, not repeated. -/
theorem kunnethGlobalMapCanonical_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    kunnethGlobalMapCanonical a b p q f hp hq K M =
      kunnethGlobalMap a b p q f hp hq (globalCupProductCanonical S) K M :=
  rfl

/-- **The global Künneth map with no parameter is natural in both complexes jointly.** -/
@[stacks 0G7V "naturality in both complexes, with no parameter"]
theorem kunnethGlobalMapCanonical_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (k : K ⟶ K') (m : M ⟶ M') :
    (Functor.uncurry.obj (tensorBase S)).map
          ((sectionsOverBase a).map k ×ₘ (sectionsOverBase b).map m) ≫
        kunnethGlobalMapCanonical a b p q f hp hq K' M' =
      kunnethGlobalMapCanonical a b p q f hp hq K M ≫
        (sectionsOverBase f).map
          ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            ((derivedPullback p).map k ×ₘ (derivedPullback q).map m)) :=
  kunnethGlobalMap_naturality a b p q f hp hq (globalCupProductCanonical S) k m

end Maps

end Spaces

/-! ### The fibre product of two schemes -/

section Schemes

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The global Künneth map of Tag 0G7V at the fibre product of two schemes, with no
parameter.**  For schemes `a : X ⟶ S` and `b : Y ⟶ S` over a base and `A = Γ(S, 𝒪_S)`, the
canonical map

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(X ×_S Y, Lp^*K ⊗^𝐋_{𝒪_{X ×_S Y}} Lq^*M)`

in `D(A)`, where `p` and `q` are the two projections of `X ×_S Y`.  The base scheme is arbitrary
and `K`, `M` are arbitrary; quasi-compactness, quasi-separatedness, quasi-coherence and
Tor-independence enter only in Tag 0FLQ, which asserts that this map is an isomorphism. -/
@[stacks 0G7V "the map at X ×_S Y, for arbitrary K and M over an arbitrary base scheme"]
def kunnethGlobalMapSchemeCanonical (K : DerivedCategory X.Modules)
    (M : DerivedCategory Y.Modules) :
    ((tensorBase S.toRingedSpace).obj ((sectionsOverBase a.toLRSHom.toShHom).obj K)).obj
        ((sectionsOverBase b.toLRSHom.toShHom).obj M) ⟶
      (sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf).obj
            ((derivedPullback (pullback.fst a b).toLRSHom.toShHom).obj K)).obj
          ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj M)) :=
  kunnethGlobalMapScheme a b (globalCupProductCanonical S.toRingedSpace) K M

/-- The map at the fibre product with no parameter is
`Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapScheme` at the canonical global cup product. -/
theorem kunnethGlobalMapSchemeCanonical_eq (K : DerivedCategory X.Modules)
    (M : DerivedCategory Y.Modules) :
    kunnethGlobalMapSchemeCanonical a b K M =
      kunnethGlobalMapScheme a b (globalCupProductCanonical S.toRingedSpace) K M :=
  rfl

/-- **The global Künneth map at the fibre product of two schemes, with no parameter, is natural in
both complexes.** -/
@[stacks 0G7V "naturality at the fibre product of two schemes, with no parameter"]
theorem kunnethGlobalMapSchemeCanonical_naturality {K K' : DerivedCategory X.Modules}
    {M M' : DerivedCategory Y.Modules} (k : K ⟶ K') (m : M ⟶ M') :
    (Functor.uncurry.obj (tensorBase S.toRingedSpace)).map
          ((sectionsOverBase a.toLRSHom.toShHom).map k ×ₘ
            (sectionsOverBase b.toLRSHom.toShHom).map m) ≫
        kunnethGlobalMapSchemeCanonical a b K' M' =
      kunnethGlobalMapSchemeCanonical a b K M ≫
        (sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).map
          ((Functor.uncurry.obj
              (derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf)).map
            ((derivedPullback (pullback.fst a b).toLRSHom.toShHom).map k ×ₘ
              (derivedPullback (pullback.snd a b).toLRSHom.toShHom).map m)) :=
  kunnethGlobalMapScheme_naturality a b (globalCupProductCanonical S.toRingedSpace) k m

end Schemes

end Stacks.Cohomology.GlobalKunneth

end
