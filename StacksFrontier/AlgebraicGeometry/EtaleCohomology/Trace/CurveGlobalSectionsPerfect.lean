module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectSingle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectBounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectFlatStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfUnderlyingAbelian

/-!
# `RΓ(X_{k̄}, K)` is perfect for `K` in `D_ctf` on a projective curve

Let `X` be a projective curve over a field `k`, `k̄` an algebraic closure of `k`, `Λ` a finite
ring, not necessarily commutative, and `K` an object of `D_ctf(X_étale, Λ)`. Then
`RΓ(X_{k̄}, K|_{X_{k̄}})` is a perfect complex of `Λ`-modules: this is [Stacks, Tag 03TV].

## Main results

* `Stacks.EtaleCohomology.isPerfect_etaleModuleDerivedGlobalSections_fieldBaseChange_of_isCtf`:
  [Stacks, Tag 03TV].

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **Stacks 03TV.** Let `X` be a projective curve over a field `k`, `k̄` an algebraic closure of
`k`, `Λ` a finite ring and `K ∈ D_ctf(X, Λ)`. Then `RΓ(X_{k̄}, K) ∈ D_perf(Λ)`: the derived global
sections of the restriction of `K` to `X_{k̄}` form a perfect complex of `Λ`-modules. -/
theorem isPerfect_etaleModuleDerivedGlobalSections_fieldBaseChange_of_isCtf
    (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ] [Finite Λ] {k : Type u} [Field k]
    (gk : X.obj ⟶ Spec (.of k)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
    [Algebra.IsAlgebraic k kbar] (hcurve : IsCurve k gk) (hproj : IsProjective gk)
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X.obj))
    (hK : IsCtf.{u, r} B X Λ (DerivedCategory.Plus.ι.obj K)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk gk) kbar)).obj
        ((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj (Over.mk gk) kbar)).mapDerivedCategoryPlus.obj K))) := by
  let Y := fieldBaseChange (Over.mk gk) kbar
  have hY : B.Contains Y := ProjectiveCurveBaseChange.contains_fieldBaseChange gk kbar B
    X.property hcurve.toLocallyOfFiniteType hcurve.toQuasiCompact
  let Y' : B.Scheme := B.obj Y hY
  let f : Y' ⟶ X := ObjectProperty.homMk (fieldBaseChangeProj (Over.mk gk) kbar)
  have hp : IsProper (pullback.snd (Over.mk gk).hom (specAlgebraMap k kbar)) :=
    ProjectiveCurveBaseChange.isProper_snd gk kbar hproj
  have hc0 : CompactSpace Y :=
    @QuasiCompact.compactSpace_of_compactSpace Y (Spec (.of kbar))
      (pullback.snd (Over.mk gk).hom (specAlgebraMap k kbar)) inferInstance inferInstance
  have hq0 : QuasiSeparatedSpace Y :=
    @quasiSeparatedSpace_of_quasiSeparated Y (Spec (.of kbar))
      (pullback.snd (Over.mk gk).hom (specAlgebraMap k kbar))
      (quasiSeparatedSpace_of_isAffine (Spec (.of kbar)))
      (@IsSeparated.instQuasiSeparated _ _ _ hp.toIsSeparated)
  have hc : CompactSpace Y'.obj := hc0
  have hq : QuasiSeparatedSpace Y'.obj := hq0
  obtain ⟨C, a, b, ha, hb, hC, ⟨e⟩⟩ := hK Y' f hc hq
  let eL : DerivedCategory.Plus.Qh.obj (Functor.plusObj C ⟨a, ha⟩) ≅
      (etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk gk) kbar)).mapDerivedCategoryPlus.obj K :=
    DerivedCategory.Plus.ι.preimageIso ((DerivedCategory.quotientCompQhIso _).app C ≪≫ e)
  refine StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso
    ((etaleModuleDerivedGlobalSections.{u, r} Λ Y).mapIso eL.symm)) ?_
  let good : EtaleModules.{u, r} Λ Y → Prop := fun G =>
    IsConstructibleFlatEtaleModule B Y' Λ G ∧ ∀ y : Y,
      Module.Finite Λ (((Stacks.SheafTwist.geometricSitePoint.{u, r} Y y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G) ∧
      Module.Projective Λ (((Stacks.SheafTwist.geometricSitePoint.{u, r} Y y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G)
  have := etaleModules_enoughInjectives.{u, r} Λ Y
  refine StacksDraft.Perfect.isPerfect_rightDerivedFunctorPlus_of_bounded
    (etaleModuleGlobalSections.{u, r} Λ Y) good (fun {G G'} eG hG => ⟨hG.1.of_iso B Y' Λ eG,
      fun y => Stacks.SheafTwist.finite_projective_sheafFiber_of_iso Y y eG (hG.2 y)⟩)
    (fun G hG => Stacks.SheafTwist.isPerfect_etaleModuleDerivedGlobalSections_single gk kbar hcurve
      hproj B hY G hG.2
      (AlgebraicGeometry.isConstructibleAbelianSheaf_forget₂_of_isConstructibleFlatModuleSheaf B Λ
        Y' _ hG.1)) C a b (fun i => ⟨hC i,
      Stacks.SheafTwist.finite_projective_sheafFiber_of_isConstructibleFlat B Y' Λ C hC i⟩)

end Stacks.EtaleCohomology

end
