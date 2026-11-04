module

public import StacksFrontier.Algebra.Homology.DerivedCategory.HomWindow
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtalePerfectConverse
public import StacksFrontier.AlgebraicGeometry.Duality.DetectingBoundednessOfAPerfectComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect

/-!
# A window of Hom-vanishing against a perfect object on the small étale site of a scheme

Let `T` be a quasi-compact and quasi-separated scheme and let `K` be a perfect object of
`D(T_étale, 𝒪)` with quasi-coherent cohomology sheaves.  Then `K` has a window of Hom-vanishing
against the objects of `D(T_étale, 𝒪)` with quasi-coherent cohomology, in the sense of
`Stacks.HomWindow.HasHomWindow`.  This is [Stacks, Tag 09M4] part (1) for the scheme `T`, read on
its small étale site.

## Main results

* `AlgebraicGeometry.SmallEtale.hasHomWindow_of_isPerfect`: the window.

## Implementation notes

By Stacks 071Q, `ε^* : D_QCoh(𝒪_T) ⥤ D_QCoh(T_étale, 𝒪)` is an equivalence, so `K ≅ ε^*K₀` for
some `K₀ ∈ D_QCoh(𝒪_T)`; `K₀` is perfect by the converse direction of Stacks 08HG
(`AlgebraicGeometry.SmallEtale.isPerfectZariski_of_isPerfectSmallEtale`), read on the ringed
space by `Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite`, and
`Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_qcqs` (Stacks 09M4 part (1))
gives a window for `K₀`.  That window serves for `K`: an object `L` of `D_QCoh(T_étale, 𝒪)` is
`ε^*L₀` for `L₀ = Rε_*L`, the cohomology sheaves of `L₀` vanish where those of `L` do because
`ε^*` commutes with cohomology and detects the vanishing of a module (Stacks 08H8), and `ε^*` is
fully faithful on `D_QCoh`.

This file is kept apart from the algebraic-space files that consume it: their import closure
carries an `Abelian (SheafOfModules …)` instance at a `max` module universe against which the
derived category of `𝒪_{T_étale}`-modules does not elaborate.

The derived categories are the standard models, `CategoryTheory.HasDerivedCategory.standard`
being a local instance of high priority as in the scheme statement of Stacks 09M4 applied here.

## References

* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.HomWindow

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.SmallEtale

/-- The `𝒪`-modules on the small étale site of a scheme form an abelian category, at the module
universe of the structure sheaf.  This is `SheafOfModules.instAbelian`, named so that it can be
made a local instance of high priority: the import closure of this file also carries an
`Abelian (SheafOfModules …)` instance at a `max` module universe, and instance search tries that
one first and gets stuck on the universe constraint `u + 1 =?= max (u + 1) ?v`. -/
noncomputable abbrev smallEtaleModulesAbelian (E : BigEtaleSite.{u}) (T : Scheme.{u})
    (hT : E.Contains T) : Abelian (SheafOfModules.{u} (structureSheaf E T hT)) :=
  SheafOfModules.instAbelian _

/-- `smallEtaleModulesAbelian` at the spelling `AlgebraicGeometry.RingedSite.ringSheaf` of the
structure sheaf, in which the perfectness predicate of Stacks 08G5 asks for its derived category.
The two spellings are equal by `smallEtaleRingedSite_ringSheaf`, which is `rfl`. -/
noncomputable abbrev smallEtaleRingedSiteModulesAbelian (E : BigEtaleSite.{u}) (T : Scheme.{u})
    (hT : E.Contains T) :
    Abelian (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite E T hT).O)) :=
  smallEtaleModulesAbelian E T hT

attribute [local instance 100000] smallEtaleModulesAbelian smallEtaleRingedSiteModulesAbelian

variable (E : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : E.Contains T)
  [CompactSpace T] [QuasiSeparatedSpace T]

/-- **A window for a perfect object on the small étale site of a scheme.**  Let `T` be a
quasi-compact and quasi-separated scheme and let `K` be a perfect object of `D(T_étale, 𝒪)` with
quasi-coherent cohomology sheaves.  Then `K` has a window of Hom-vanishing against the objects of
`D(T_étale, 𝒪)` with quasi-coherent cohomology.

By Stacks 071Q, `K ≅ ε^*K₀` for an object `K₀` of `D_QCoh(𝒪_T)`, which is perfect by Stacks
08HG; Stacks 09M4 gives a window `[a, b]` for `K₀`.  An object `L` of `D_QCoh(T_étale, 𝒪)` is
`ε^*L₀` for some `L₀ ∈ D_QCoh(𝒪_T)`, whose cohomology sheaves vanish where those of `L` do —
`ε^*` commutes with cohomology and detects the vanishing of a module (Stacks 08H8) — and
`ε^*` is fully faithful on `D_QCoh`, so `Hom(K, L) = Hom(K₀, L₀)` vanishes. -/
theorem hasHomWindow_of_isPerfect
    (K : DerivedCategory (SheafOfModules.{u} (structureSheaf E T hT)))
    (hK : (smallEtaleRingedSite E T hT).IsPerfect K)
    (hKq : ∀ i : ℤ, qcohOnSite E T hT
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheaf E T hT)) i).obj K)) :
    HasHomWindow (qcohOnSite E T hT) K := by
  let e := derivedAssociatedModuleEquivalenceQcoh.{u + 1} E T hT
  let K' : (DerivedCategoryB.derivedCategoryB (qcohOnSite E T hT)).FullSubcategory := ⟨K, hKq⟩
  let K₀ := e.inverse.obj K'
  let eM (M : (DerivedCategoryB.derivedCategoryB (qcohOnSite E T hT)).FullSubcategory) :
      (associatedModuleOfSheaf E T hT).mapDerivedCategory.obj (e.inverse.obj M).obj ≅ M.obj :=
    (DerivedCategoryB.derivedCategoryB (qcohOnSite E T hT)).ι.mapIso (e.counitIso.app M)
  have hK₀ : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := T.toRingedSpace) K₀.obj := by
    refine (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite _ _).2 ?_
    exact isPerfectZariski_of_isPerfectSmallEtale E T hT K₀.obj
      (RingedSite.IsPerfect.of_iso (smallEtaleRingedSite E T hT) hK (eM K').symm)
  obtain ⟨a, b, hab, hwin⟩ :=
    Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_qcqs T K₀.obj hK₀
  refine ⟨a, b, hab, fun L hL hz => ?_⟩
  let L' : (DerivedCategoryB.derivedCategoryB (qcohOnSite E T hT)).FullSubcategory := ⟨L, hL⟩
  let L₀ := e.inverse.obj L'
  have hz₀ : ∀ i : ℤ, a ≤ i → i ≤ b →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} T.ringCatSheaf) i).obj
        L₀.obj) := by
    intro i hai hib
    exact isZero_of_isZero_associatedModule_general E T hT _ ((hz i hai hib).of_iso
      (((Functor.mapDerivedCategoryHomologyIso (associatedModuleOfSheaf E T hT) i).app
        L₀.obj).symm ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso (eM L')))
  have hsub : Subsingleton (K₀.obj ⟶ L₀.obj) := hwin L₀.obj (fun i => L₀.property i) hz₀
  refine ⟨fun x y => ?_⟩
  have hxy : e.inverse.map (ObjectProperty.homMk x : K' ⟶ L') =
      e.inverse.map (ObjectProperty.homMk y : K' ⟶ L') :=
    InducedCategory.hom_ext (Subsingleton.elim _ _)
  exact congrArg (fun z : K' ⟶ L' => z.hom) (e.inverse.map_injective hxy)

end AlgebraicGeometry.SmallEtale

end
