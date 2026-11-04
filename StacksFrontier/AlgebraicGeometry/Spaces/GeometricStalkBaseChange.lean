module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularSections
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointFiberStalk

/-!
# Base change of a stalk from an étale scheme chart to a geometric point

Let `X` be an algebraic space over a scheme `S`, let `F` be an `𝒪_X`-module, let `x̄` be a
geometric point of `X` and let `φ : (U, ū) → (X, x̄)` be a small étale neighbourhood whose chart
`U` is a scheme.  Writing `u` for the image in `U` of the chosen lift `ū`, Stacks 05VP compares
the ordinary (Zariski) stalk of `φ^* F` at `u` with the geometric stalk of `F` at `x̄`:
`(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} = F_{x̄}`.

This file supplies both sides of that equation and the ring map along which it base changes.
The map is faithfully flat, because `𝒪_{X, x̄}` is the strict henselization of `𝒪_{U, u}`
(Stacks 04KF), which is what makes the tensor product in the statement meaningful.

## Main definitions

* `AlgebraicGeometry.Space.chartLocalRing` is the local ring `𝒪_{U, u}` of the chart.
* `AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing` is the canonical map
  `𝒪_{U, u} → 𝒪_{X, x̄}`, the ring map along which Stacks 05VP base changes.
* `AlgebraicGeometry.Space.chartStalkBaseChange` is the base-change functor
  `- ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}`.
* `AlgebraicGeometry.Space.chartZariskiModuleStalk` is the Zariski stalk `(φ^* F)_u` of the
  restriction of `F` to the chart, as a module over `𝒪_{U, u}`.
* `AlgebraicGeometry.Space.chartStalkTensorEtaleLocalRing` is the left-hand side
  `(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` of Stacks 05VP.  It is an object of the same category
  `ModuleCat 𝒪_{X, x̄}` as `AlgebraicGeometry.Space.geometricModuleStalk`, so the equation of
  Stacks 05VP is well formed as it stands, with no universe adjustment between its sides.

## Main results

* `AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_germ`: the canonical map sends the
  ordinary germ at `u` of a regular function on the chart to the germ of the same function at
  `x̄`.  So it is the identity in germs, and is the comparison map Stacks 05VP speaks of rather
  than some other map of local rings.
* `AlgebraicGeometry.Space.faithfullyFlat_chartLocalRingToEtaleLocalRing`: the canonical map is
  faithfully flat, with `AlgebraicGeometry.Space.flat_chartLocalRingToEtaleLocalRing` and
  `AlgebraicGeometry.Space.injective_chartLocalRingToEtaleLocalRing` as consequences.  Flatness
  says exactly that the base change of Stacks 05VP is exact.

## Implementation notes

The ring `𝒪_{U, u}` lives in `CommRingCat.{u}` while `𝒪_{X, x̄}` lives in `CommRingCat.{u + 1}`,
the latter being a colimit indexed by the small étale neighbourhoods of `x̄`.  The comparison is
therefore a bare `RingHom` between types in different universes rather than a morphism of one
category of rings, and `ModuleCat.extendScalars` is applied to it, which allows its source and
target rings to lie in independent universes.

The canonical map is built from Stacks 04KF in the form
`AlgebraicGeometry.Space.strictHenselizationEquivEtaleLocalRing`, composed with the structure
map of the henselization tower `AlgebraicGeometry.geometricHenselizationTower`.  The tower is
constructed rather than assumed, so the map depends on no choice beyond the neighbourhood.
Faithful flatness is read off the same tower through
`IsLocalRing.IsHenselization.faithfullyFlat` and transported along the comparison as a linear
equivalence over `𝒪_{U, u}`.

The Zariski stalk is the stalk of `AlgebraicGeometry.Space.restrictToChart` at the point of the
Zariski site given by `TopologicalSpace.Opens.pointGrothendieckTopology`, taken with
`Stacks.moduleStalkLarge`, whose module universe is independent of the universe of schemes.
Writing it as a stalk at a point of a site is what keeps that independence: the base ring of
`Stacks.moduleStalkLarge` is the fibre of the structure sheaf at that point, and
`TopologicalSpace.Opens.pointFiberStalkIso` identifies it with `𝒪_{U, u}`, along which the
scalars are restricted.  The alternative — building the module structure on the colimit of
sections by hand with `CategoryTheory.Limits.IsColimit.module` — is what forces the
transparency and heartbeat options that `Mathlib.Algebra.Category.ModuleCat.Stalk` carries on
its own Zariski instances, and those instances are in any case stated only for a module
universe equal to the universe of the space.

The comparison between the two sides is carried elsewhere:
`AlgebraicGeometry.Space.chartStalkTensorComparison` is the map, and
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison` is Stacks 05VP, that it is an
isomorphism for a quasi-coherent module.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite TopologicalSpace

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- The local ring `𝒪_{U, u}` of the scheme underlying a small étale neighbourhood of a
geometric point, at the point under the chosen lift of that geometric point. -/
noncomputable abbrev chartLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) : CommRingCat.{u} :=
  (chartScheme V.chart).presheaf.stalk (chartPoint B S hS X V)

/-- The henselization tower of `𝒪_{U, u}` taken over the separable closure of its residue field
inside the residue field of the geometric point.  Its strict henselization is `𝒪_{X, x̄}`. -/
noncomputable abbrev chartHenselizationTower {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    HenselizationTower ↥(chartLocalRing B S hS X V)
      (separableClosure (ResidueField ↥(chartLocalRing B S hS X V))
        (chartGeometricPoint V).residueField) :=
  geometricHenselizationTower (chartScheme V.chart) (chartGeometricPoint V)

/-- The point of the Zariski site of the chart at which the ordinary stalk is taken. -/
noncomputable abbrev chartZariskiPoint {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    GrothendieckTopology.Point.{u} (Opens.grothendieckTopology (chartScheme V.chart)) :=
  Opens.pointGrothendieckTopology (chartPoint B S hS X V)

/-- The identification of the fibre of the structure sheaf of the chart at
`AlgebraicGeometry.Space.chartZariskiPoint` with the local ring `𝒪_{U, u}`. -/
noncomputable abbrev chartZariskiFiberIso {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    ((chartZariskiPoint B S hS X V).presheafFiber (A := CommRingCat.{u})).obj
        (chartScheme V.chart).presheaf ≅ chartLocalRing B S hS X V :=
  Opens.pointFiberStalkIso (chartPoint B S hS X V) (chartScheme V.chart).presheaf

include hX

/-- The comparison of `𝒪_{X, x̄}` with the strict henselization of `𝒪_{U, u}` in the tower
`AlgebraicGeometry.Space.chartHenselizationTower`, which is Stacks 04KF. -/
noncomputable abbrev chartStrictHenselizationEquiv {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    (chartHenselizationTower B S hS X V).strictHenselization ≃+* ↥(etaleLocalRing B S hS X x) :=
  strictHenselizationEquivEtaleLocalRing hX V (bigEtaleSiteOfFppfSite B)
    V.chart.obj.left.left.property (chartHenselizationTower B S hS X V)

/-- The canonical map `𝒪_{U, u} → 𝒪_{X, x̄}` of Stacks 05VP: the structure map of `𝒪_{U, u}`
into its strict henselization, followed by the identification of that strict henselization with
the étale local ring at the geometric point. -/
@[stacks 05VP "the canonical map O_{U, u} → O_{X, xbar}"]
noncomputable def chartLocalRingToEtaleLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    ↥(chartLocalRing B S hS X V) →+* ↥(etaleLocalRing B S hS X x) :=
  (chartStrictHenselizationEquiv B S hS X hX V).toRingHom.comp
    (algebraMap ↥(chartLocalRing B S hS X V)
      (chartHenselizationTower B S hS X V).strictHenselization)

/-- The canonical map `𝒪_{U, u} → 𝒪_{X, x̄}` sends the ordinary germ at `u` of a regular
function on the chart to the germ of the same function at the geometric point. -/
@[stacks 05VP "the comparison map is the identity on germs of regular functions"]
theorem chartLocalRingToEtaleLocalRing_germ {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (a : Γ(chartScheme V.chart, ⊤)) :
    chartLocalRingToEtaleLocalRing B S hS X hX V
        ((chartScheme V.chart).presheaf.germ ⊤ (chartPoint B S hS X V) trivial a) =
      etaleLocalRingGerm B S hS X x (op V) a :=
  strictHenselizationEquivEtaleLocalRing_germ hX V (bigEtaleSiteOfFppfSite B)
    V.chart.obj.left.left.property (chartHenselizationTower B S hS X V) a

/-- **The base change of Stacks 05VP is faithfully flat.** The canonical map
`𝒪_{U, u} → 𝒪_{X, x̄}` is faithfully flat: the étale local ring is the strict henselization of
the chart's local ring, and a strict henselization is faithfully flat over the ring it
henselizes. -/
@[stacks 05VP "the base-change map is faithfully flat"]
theorem faithfullyFlat_chartLocalRingToEtaleLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    (chartLocalRingToEtaleLocalRing B S hS X hX V).FaithfullyFlat := by
  have hFF : Module.FaithfullyFlat ↥(chartLocalRing B S hS X V)
      (chartHenselizationTower B S hS X V).strictHenselization :=
    IsLocalRing.IsHenselization.faithfullyFlat
      (L := separableClosure (ResidueField ↥(chartLocalRing B S hS X V))
        (chartGeometricPoint V).residueField)
  let _ : Algebra ↥(chartLocalRing B S hS X V) ↥(etaleLocalRing B S hS X x) :=
    (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra
  let e : (chartHenselizationTower B S hS X V).strictHenselization ≃ₐ[
      ↥(chartLocalRing B S hS X V)] ↥(etaleLocalRing B S hS X x) :=
    { chartStrictHenselizationEquiv B S hS X hX V with commutes' := fun _ => rfl }
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv.symm

/-- The canonical map `𝒪_{U, u} → 𝒪_{X, x̄}` is flat, so the base change of Stacks 05VP along
it is exact. -/
@[stacks 05VP "the base-change map is flat"]
theorem flat_chartLocalRingToEtaleLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    (chartLocalRingToEtaleLocalRing B S hS X hX V).Flat :=
  (faithfullyFlat_chartLocalRingToEtaleLocalRing B S hS X hX V).flat

/-- The canonical map `𝒪_{U, u} → 𝒪_{X, x̄}` is injective. -/
theorem injective_chartLocalRingToEtaleLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    Function.Injective (chartLocalRingToEtaleLocalRing B S hS X hX V) :=
  (faithfullyFlat_chartLocalRingToEtaleLocalRing B S hS X hX V).injective

/-- The base-change functor `- ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` of Stacks 05VP, taking a module over the
local ring of the chart to a module over the étale local ring at the geometric point. -/
@[stacks 05VP "the base-change functor - ⊗_{O_{U, u}} O_{X, xbar}"]
noncomputable def chartStalkBaseChange {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    ModuleCat.{max u m} ↥(chartLocalRing B S hS X V) ⥤
      ModuleCat.{max (u + 1) m} ↥(etaleLocalRing B S hS X x) :=
  ModuleCat.extendScalars (chartLocalRingToEtaleLocalRing B S hS X hX V)

/-- The ordinary (Zariski) stalk `(φ^* F)_u` of the restriction of an `𝒪_X`-module to an étale
scheme chart, as a module over the local ring `𝒪_{U, u}` of the chart.

It is the stalk of `AlgebraicGeometry.Space.restrictToChart` at the point
`AlgebraicGeometry.Space.chartZariskiPoint` of the Zariski site of the chart, with its scalars
restricted along `AlgebraicGeometry.Space.chartZariskiFiberIso`. -/
@[stacks 05VP "the Zariski stalk of the chart restriction, the left factor of the tensor"]
noncomputable def chartZariskiModuleStalk {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX) :
    ModuleCat.{max u m} ↥(chartLocalRing B S hS X V) :=
  (ModuleCat.restrictScalars (chartZariskiFiberIso B S hS X V).inv.hom).obj
    (Stacks.moduleStalkLarge (chartZariskiPoint B S hS X V)
      (show Sheaf (Opens.grothendieckTopology (chartScheme V.chart)) CommRingCat.{u} from
        (chartScheme V.chart).sheaf)
      (restrictToChart B S hS hX F V.chart))

/-- The left-hand side `(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` of Stacks 05VP: the Zariski stalk of
the chart restriction, base changed along the canonical map to the étale local ring.

Its type is the category in which `AlgebraicGeometry.Space.geometricModuleStalk` also lands, so
the equation of Stacks 05VP relates two objects of one category. -/
@[stacks 05VP "the left-hand side (phi^* F)_u ⊗_{O_{U, u}} O_{X, xbar}"]
noncomputable def chartStalkTensorEtaleLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX) :
    ModuleCat.{max (u + 1) m} ↥(etaleLocalRing B S hS X x) :=
  (chartStalkBaseChange.{u, m} B S hS X hX V).obj
    (chartZariskiModuleStalk B S hS X hX V F)

end AlgebraicGeometry.Space

end
