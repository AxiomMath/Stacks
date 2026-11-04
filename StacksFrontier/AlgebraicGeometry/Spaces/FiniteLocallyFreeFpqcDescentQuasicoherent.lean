module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafQuasicoherentSmooth
import StacksCore.Tactic.StacksAttribute

/-!
# Fpqc descent of finite local freeness for quasi-coherent modules on algebraic spaces

Let `X` be an algebraic space over a scheme `S` and let `𝓕` be a quasi-coherent `𝒪_X`-module. If
`{f i : X i ⟶ X}` is an fpqc covering of `X` and every pullback `(f i)^*𝓕` is finite locally free,
then `𝓕` is finite locally free.

## Main results

* `Space.isFiniteLocallyFreeOnSite_of_pullback_isFpqcCovering_of_isQuasicoherentOnSite`: a
  quasi-coherent module whose pullbacks along an fpqc covering are finite locally free is finite
  locally free.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 060X](https://stacks.math.columbia.edu/tag/060X)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `X` be an algebraic space over `S`, let `𝓕` be a quasi-coherent `𝒪_X`-module and let
`{f i : X i ⟶ X}` be an fpqc covering of `X` such that every pullback `(f i)^*𝓕` is finite locally
free. Then `𝓕` is finite locally free. -/
@[stacks 060X]
theorem isFiniteLocallyFreeOnSite_of_pullback_isFpqcCovering_of_isQuasicoherentOnSite
    {I : Type v} {X : AlgebraicSpaces B S hS} {Xi : I → AlgebraicSpaces B S hS}
    (f : ∀ i, Xi i ⟶ X) (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom)
    (F : Modules.{u, u} B S hS X.obj X.property) (hF : F.IsQuasicoherentOnSite)
    (hFlf : ∀ i, SheafOfModules.IsFiniteLocallyFreeOnSite
      ((modulePullback B S hS (f i)).obj F)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite F := by
  refine isFiniteLocallyFreeOnSite_of_pullback_isFpqcCovering B S hS f hf F ?_ hFlf
  intro A _
  refine ⟨chartSchemeModule B S hS X F hF A, isQuasicoherent_chartSchemeModule B S hS X F hF A,
    isFiniteLocallyFreeOnSite_over_of_isFiniteLocallyFree_chartSchemeModule B S hS X F hF A,
    ?_⟩
  intro T' g i a ha hfi
  set abar :
      (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ⟶ Xi i :=
    ObjectProperty.homMk a with habar
  have : SheafOfModules.IsQuasicoherent (chartSchemeModule B S hS X F hF A) :=
    isQuasicoherent_chartSchemeModule B S hS X F hF A
  have : SheafOfModules.IsQuasicoherent
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj
        (chartSchemeModule B S hS X F hF A)) :=
    Stacks.SheafOfModules.schemePullback_isQuasicoherent _ _
  have hA : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((modulePullback B S hS abar).obj ((modulePullback B S hS (f i)).obj F)) :=
    isFiniteLocallyFreeOnSite_modulePullback_of_isFiniteLocallyFreeOnSite B S hS abar _ hfi
  have hcomp : representedSpaceMap B S hS g ≫ chartToSpace B S hS X A = abar ≫ f i :=
    ObjectProperty.hom_ext _ ha.symm
  have hB : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((modulePullback B S hS (chartToSpace B S hS X A)).obj F)) := by
    refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS g)
        (chartToSpace B S hS X A)).app F).symm ?_
    rw [hcomp]
    exact SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      ((modulePullbackCompIso B S hS abar (f i)).app F) hA
  have eF : (representedSmallEtaleModuleEquivalence B S hS
        ((SmallEtale.toOver B S hS X.obj).obj A)).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          (chartScheme A) ((SmallEtale.toOver B S hS X.obj).obj A).left.property).obj
          (chartSchemeModule B S hS X F hF A)) ≅
      (modulePullback B S hS (chartToSpace B S hS X A)).obj F :=
    (representedSmallEtaleModuleEquivalence B S hS
          ((SmallEtale.toOver B S hS X.obj).obj A)).functor.mapIso
        (associatedModuleChartSchemeModuleIso B S hS X F hF A) ≪≫
      representedSmallEtaleChartSchemeEtaleModuleIso B S hS X F hF A ≪≫
      chartSmallEtaleRestrictionFunctorObjIso X F A ≪≫
      ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X A)
        (isEtale_chartToSpace B S hS X A)).app F).symm
  refine SmallEtale.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_associatedModule
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T') T'.left.property _ ?_
  refine (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS T' _).1 ?_
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (representedAssociatedModulePullbackIso B S hS g
      (relativelyRepresentable_yoneda_map B S hS g)
      (chartSchemeModule B S hS X F hF A)) ?_
  exact SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    ((modulePullback B S hS (representedSpaceMap B S hS g)).mapIso eF).symm hB

end AlgebraicGeometry.Space

end
