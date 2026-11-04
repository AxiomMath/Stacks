module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of a finite locally free module along a morphism of algebraic spaces

Let `a : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `N` be a
quasi-coherent `𝒪_Y`-module on the small étale site which is finite locally free. Then the
inverse image `a^*N` of Stacks 03LU is finite locally free. This is the clause of Stacks 03DO
for the property 03DL (2) along the morphism of small étale ringed topoi of Stacks 03LU.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePullback_of_isEtale`: the case of an
  étale morphism, where the inverse image is étale restriction.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePullback_representedSpaceMap`: the
  case of a morphism of representable algebraic spaces.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePullback`: the inverse image of a
  quasi-coherent finite locally free module along an arbitrary morphism of algebraic spaces is
  finite locally free.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The case of an étale morphism -/

/-- The étale restriction of a finite locally free `𝒪_Y`-module along an étale morphism
`f : X ⟶ Y` of algebraic spaces is finite locally free. -/
theorem isFiniteLocallyFreeOnSite_etaleModulePullback_of_isEtale
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((etaleModulePullback B S hS f hf).obj M) := by
  refine
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite
      (smallEtaleRingedSite B S hS X.1 X.2) ((etaleModulePullback B S hS f hf).obj M)).2
      ⟨ULift.{u + 1} (smallEtaleRingedSite B S hS X.1 X.2).C, fun i => i.down,
        Stacks.SheafOfModules.coversTop_ulift_self
          (smallEtaleRingedSite B S hS X.1 X.2).J, fun i => ?_⟩
  exact (isFiniteLocallyFreeOnSite_over_etaleModulePullback_iff B S hS f hf M i.down).2
    (hM.over _)

/-- The inverse image of a finite locally free `𝒪_Y`-module along an étale morphism `f : X ⟶ Y`
of algebraic spaces is finite locally free. -/
@[stacks 03DO "the finite locally free property, clause 03DL (2), along an étale morphism of
  algebraic spaces"]
theorem isFiniteLocallyFreeOnSite_modulePullback_of_isEtale
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePullback B S hS f).obj M) :=
  SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS f hf).app M).symm
    (isFiniteLocallyFreeOnSite_etaleModulePullback_of_isEtale B S hS f hf M hM)

/-! ### The Zariski module of a quasi-coherent module on a representable algebraic space -/

section Represented

variable (T : BigFppfOver B S hS)
  (N : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
  (hN : N.IsQuasicoherentOnSite)

/-- A quasi-coherent module on the small étale site of a representable algebraic space, as an
object of the category of quasi-coherent modules there. -/
def representedQcoh :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS T)).FullSubcategory :=
  ⟨N, hN⟩

/-- The quasi-coherent module on the small étale site of the scheme underlying `T` that the
comparison of Stacks 03DX (2) carries to a quasi-coherent module on the small étale site of
`yoneda.obj T`. -/
noncomputable abbrev representedSchemeEtaleQcoh :=
  (representedQuasicoherentEquivalence B S hS T).inverse.obj (representedQcoh B S hS T N hN)

/-- The quasi-coherent Zariski module on the scheme underlying `T` that the comparison of
Stacks 03DX (2) carries to a quasi-coherent module on the small étale site of `yoneda.obj T`. -/
noncomputable abbrev representedSchemeQcoh :=
  (representedQuasicoherentSchemeEquivalence B S hS T).inverse.obj
    (representedQcoh B S hS T N hN)

/-- The underlying Zariski module of `AlgebraicGeometry.Space.representedSchemeQcoh`. -/
noncomputable abbrev representedSchemeModule := (representedSchemeQcoh B S hS T N hN).obj

/-- The counit of the comparison of Stacks 03DX (2) at a representable algebraic space: a
quasi-coherent module on the small étale site of `yoneda.obj T` is the reading there of a
module on the small étale site of the scheme underlying `T`. -/
noncomputable def representedSmallEtaleModuleCounitIso :=
  (ObjectProperty.ι _).mapIso
    ((representedQuasicoherentEquivalence B S hS T).counitIso.app
      (representedQcoh B S hS T N hN))

/-- The counit of the comparison of Stacks 03DX (2) between Zariski modules on a scheme and
modules on its small étale site, at the Zariski module of
`AlgebraicGeometry.Space.representedSchemeModule`. -/
noncomputable def associatedModuleRepresentedSchemeModuleIso :=
  (ObjectProperty.ι _).mapIso
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
      T.left.property).counitIso.app (representedSchemeEtaleQcoh B S hS T N hN))

/-- The Zariski module of a finite locally free quasi-coherent module on a representable algebraic
space is finite locally free. -/
theorem isFiniteLocallyFree_representedSchemeModule
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite N) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (representedSchemeModule B S hS T N hN) := by
  have : SheafOfModules.IsQuasicoherent (representedSchemeModule B S hS T N hN) :=
    (representedSchemeQcoh B S hS T N hN).property
  refine (_root_.AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property _).1 ?_
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (associatedModuleRepresentedSchemeModuleIso B S hS T N hN).symm ?_
  refine (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS T _).1 ?_
  exact SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (representedSmallEtaleModuleCounitIso B S hS T N hN).symm h

/-- The identification of a quasi-coherent module on the small étale site of a representable
algebraic space with the associated module of its Zariski module. -/
noncomputable def associatedModuleRepresentedSchemeModuleSpaceIso :
    (representedSmallEtaleModuleEquivalence B S hS T).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
          (representedSchemeModule B S hS T N hN)) ≅
      N :=
  (representedSmallEtaleModuleEquivalence B S hS T).functor.mapIso
      (associatedModuleRepresentedSchemeModuleIso B S hS T N hN) ≪≫
    representedSmallEtaleModuleCounitIso B S hS T N hN

end Represented

/-! ### The case of a morphism of representable algebraic spaces -/

/-- The inverse image of a quasi-coherent finite locally free module along the morphism of
representable algebraic spaces attached to a morphism `g` of the big fppf category is finite
locally free. -/
@[stacks 03DO "the finite locally free property, clause 03DL (2), along a morphism of
  representable algebraic spaces"]
theorem isFiniteLocallyFreeOnSite_modulePullback_representedSpaceMap
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (N : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    (hN : N.IsQuasicoherentOnSite)
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite N) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj N) := by
  have : SheafOfModules.IsQuasicoherent (representedSchemeModule B S hS T N hN) :=
    (representedSchemeQcoh B S hS T N hN).property
  have hpb : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (B.inclusion.map g.left)).obj
        (representedSchemeModule B S hS T N hN)) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ _
      (isFiniteLocallyFree_representedSchemeModule B S hS T N hN h)
  have : SheafOfModules.IsQuasicoherent
      ((Scheme.Modules.pullback (B.inclusion.map g.left)).obj
        (representedSchemeModule B S hS T N hN)) :=
    Stacks.SheafOfModules.schemePullback_isQuasicoherent _ _
  have hB : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj
          ((Scheme.Modules.pullback (B.inclusion.map g.left)).obj
            (representedSchemeModule B S hS T N hN)))) :=
    (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS T' _).2
      (_root_.AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T') T'.left.property _ hpb)
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    ((modulePullback B S hS (representedSpaceMap B S hS g)).mapIso
      (associatedModuleRepresentedSchemeModuleSpaceIso B S hS T N hN)) ?_
  exact SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (representedAssociatedModulePullbackIso B S hS g
      (relativelyRepresentable_yoneda_map B S hS g)
      (representedSchemeModule B S hS T N hN)).symm hB

/-! ### The general case -/

/-- The inverse image `a^*N` of Stacks 03LU of a quasi-coherent finite locally free `𝒪_Y`-module
along a morphism `a : X ⟶ Y` of algebraic spaces over `S` is finite locally free. -/
@[stacks 03DO "the finite locally free property, clause 03DL (2), for the morphism of small
  étale ringed topoi of an arbitrary morphism of algebraic spaces, stated for a quasi-coherent
  module: the source assumes no such hypothesis, and it is carried here because the reduction to
  the representable case runs through the comparison of Stacks 03DX (2), which needs it"]
theorem isFiniteLocallyFreeOnSite_modulePullback {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (hN : N.IsQuasicoherentOnSite)
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite N) :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePullback B S hS a).obj N) := by
  refine
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite
      (smallEtaleRingedSite B S hS X.1 X.2) ((modulePullback B S hS a).obj N)).2
      ⟨{W : SmallEtale B S hS X.1 // HasAffineChartDiagram B S hS a W},
        affineChartDiagramCharts B S hS a, coversTop_affineChartDiagramCharts B S hS a,
        fun i => ?_⟩
  obtain ⟨-, V, q, hq, -⟩ := i.2
  have hNV : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((modulePullback B S hS (chartToSpace B S hS Y V)).obj N) :=
    isFiniteLocallyFreeOnSite_modulePullback_of_isEtale B S hS _
      (isEtale_chartToSpace B S hS Y V) N h
  have hNVqc : ((modulePullback B S hS (chartToSpace B S hS Y V)).obj N).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isEtale B S hS _
      (isEtale_chartToSpace B S hS Y V) N hN
  have hrep : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((modulePullback B S hS (chartSpaceMapOver B S hS q)).obj
        ((modulePullback B S hS (chartToSpace B S hS Y V)).obj N)) :=
    isFiniteLocallyFreeOnSite_modulePullback_representedSpaceMap B S hS q _ hNVqc hNV
  have hfac : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((modulePullback B S hS (chartToSpace B S hS X i.1)).obj
        ((modulePullback B S hS a).obj N)) :=
    SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      ((modulePullbackCommSquareIso B S hS
        (chartSpaceMapOver_comp_chartToSpace B S hS a q hq)).app N) hrep
  refine (isFiniteLocallyFreeOnSite_chartSmallEtaleRestriction_iff B S hS X
    ((modulePullback B S hS a).obj N) i.1).1 ?_
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (chartSmallEtaleRestrictionFunctorObjIso X ((modulePullback B S hS a).obj N) i.1).symm ?_
  exact SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X i.1)
      (isEtale_chartToSpace B S hS X i.1)).app _) hfac

end AlgebraicGeometry.Space

end
