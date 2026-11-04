module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap

/-!
# The mate layer of the derived base change map at any model of the derived category

This file constructs the derived base change map of [Stacks, Tag 08HY] for a commutative square
of ringed spaces, where each of the four derived categories of sheaves of modules is given by a
binder `[HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing ·))]` at one shared
universe `w`, so that it is available at any model, for instance at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. The derived pullbacks and pushforwards
enter as adjunctions `Lf ⊣ Rf` and `Lf' ⊣ Rf'` together with isomorphisms identifying both
iterated pullbacks with a common functor `Lc`, and the base change map is the mate of the
resulting comparison.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMapAtModel`: the base change map
  `Lg^* (Rf_* K) ⟶ Rf'_* (Lg'^* K)` as the mate of the comparison of the iterated pullbacks.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMapAtModel_eq`: it is the transpose
  of the pullback of the counit, transported across the composition isomorphisms.
* `Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMapAtModel_naturality`: it is natural.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe w u

namespace Stacks.Cohomology.DerivedBaseChange

noncomputable section

namespace Mate

variable {X' X S' S : RingedSpace.{u, u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X'))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S'))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S))]
  {Lf : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
  {Lg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
  {Lf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Lg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Lc : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
  {Rf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- The comparison `Lg^* ⋙ Lf'^* ⟶ Lf^* ⋙ Lg'^*` of the two iterated derived pullbacks around
the square, read as a two-square: the composite of `eg` with the inverse of `ef`. -/
def derivedPullbackSquareAtModel : TwoSquare Lg Lf Lf' Lg' :=
  TwoSquare.mk _ _ _ _ (eg.hom ≫ ef.inv)

/-- The canonical derived base change morphism of functors
`Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`: the mate of the comparison of the two iterated derived
pullbacks. -/
def derivedBaseChangeSquareAtModel : TwoSquare Rf Lg' Lg Rf' :=
  mateEquiv adjf adjf' (derivedPullbackSquareAtModel eg ef)

/-- The canonical derived base change map `Lg^* (Rf_* K) ⟶ Rf'_* (Lg'^* K)` at an object of the
unbounded derived category. -/
def derivedBaseChangeMapAtModel (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K) :=
  (derivedBaseChangeSquareAtModel adjf adjf' eg ef).app K

/-- Under the adjunction `Lf'^* ⊣ Rf'_*`, the base change map is the derived pullback of the
counit, transported across the two composition isomorphisms. -/
@[simp]
theorem derivedBaseChangeMapAtModel_adjoint
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (adjf'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm
        (derivedBaseChangeMapAtModel adjf adjf' eg ef K) =
      eg.hom.app (Rf.obj K) ≫ ef.inv.app (Rf.obj K) ≫ Lg'.map (adjf.counit.app K) := by
  simp [derivedBaseChangeMapAtModel, derivedBaseChangeSquareAtModel, Adjunction.homEquiv_counit,
    derivedPullbackSquareAtModel]

/-- The derived base change map is the transpose, under `Lf'^* ⊣ Rf'_*`, of the derived
pullback along `g'` of the derived counit `Lf^* (Rf_* K) ⟶ K`, transported across the two
composition isomorphisms. -/
theorem derivedBaseChangeMapAtModel_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMapAtModel adjf adjf' eg ef K =
      adjf'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)
        (eg.hom.app (Rf.obj K) ≫ ef.inv.app (Rf.obj K) ≫
          Lg'.map (adjf.counit.app K)) := by
  rw [← derivedBaseChangeMapAtModel_adjoint, Equiv.apply_symm_apply]

/-- The derived base change map is natural in the complex. -/
theorem derivedBaseChangeMapAtModel_naturality
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (u : K ⟶ L) :
    Lg.map (Rf.map u) ≫ derivedBaseChangeMapAtModel adjf adjf' eg ef L =
      derivedBaseChangeMapAtModel adjf adjf' eg ef K ≫ Rf'.map (Lg'.map u) :=
  (derivedBaseChangeSquareAtModel adjf adjf' eg ef).naturality u

end Mate

end

end Stacks.Cohomology.DerivedBaseChange
