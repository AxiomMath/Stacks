module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.QuasiFiniteConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibleHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReduction
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Rf_!` of a quasi-finite separated morphism preserves constructible torsion complexes

Let `B` be a big étale site, `f : X ⟶ Y` a separated, quasi-finite morphism of finite
presentation of schemes of `B` with `Y` quasi-compact and quasi-separated, `j` any
compactification of `f`, and `Λ` a Noetherian ring. Then for `K` in `D⁺(X_étale, Λ)` with
constructible torsion cohomology sheaves, every cohomology sheaf of `Rf_! K` (computed through `j`)
is constructible. This is Stacks 0GK3 for the derived lower shriek `Rf_! = R f̄_* ∘ j_!` of
Stacks 0F7H.

## Main results

* `isConstructibleEtaleModule_homology_derivedDirectImage_of_isFinite`:
  `Rt_*` of a finite morphism of finite presentation keeps constructible cohomology.
* `isConstructibleEtaleModule_homology_derivedLowerShriek_of_isFinite_factorization`:
  the result through the finite compactification of Zariski's main theorem.
* `isConstructibleEtaleModule_homology_derivedLowerShriek_of_quasiFinite`:
  the result through any compactification.

## Implementation notes

By Zariski's main theorem (Stacks 0F2N) `f` factors as a quasi-compact open immersion
`j' : X ⟶ X'` followed by a finite morphism of finite presentation `π : X' ⟶ Y`, which is a
compactification of `f`. Through it, `R^p π_*(j'_! F)` vanishes for `p > 0` and is `π_* j'_! F`
for `p = 0`, constructible by Stacks 03S8 and 095R
(`isConstructibleEtaleModule_rightDerived_directImage_extensionByZero_of_isFinite`); the
dévissage `isConstructibleEtaleModule_homology_derivedLowerShriek_of_sheaf` passes from sheaves
to complexes. Independence of the compactification on `D⁺_tors` (Stacks 0F7I,
`Stacks.EtaleCohomology.derivedLowerShriekCompactificationIso`) moves the result from `j'` to
`j`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **`Rt_*` of a finite morphism of finite presentation keeps constructible cohomology.** For
`t : X ⟶ Y` finite and of finite presentation in `B` and `K` in `D⁺(X_étale, Λ)` with constructible
cohomology sheaves, every cohomology sheaf of `Rt_* K` is constructible: `R^p t_*` vanishes for
`p > 0` (Stacks 095U) and `t_*` keeps constructibility (Stacks 095R), and the 015J dévissage passes
to complexes. -/
@[sga "4½ Th_finitude 1.3" "(X), special case"]
theorem isConstructibleEtaleModule_homology_derivedDirectImage_of_isFinite (B : BigEtaleSite.{u})
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] {X Y : B.Scheme} (t : X ⟶ Y)
    [IsFinite (B.inclusion.map t)] [LocallyOfFinitePresentation (B.inclusion.map t)]
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
      ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) (n : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ n).obj
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (B.inclusion.map t)).obj K)) := by
  have hP : (IsBigSiteConstructibleEtaleModule B X Λ).IsClosedUnderIsomorphisms :=
    ⟨fun e h => IsBigSiteConstructibleEtaleModule.of_iso B Λ e h⟩
  have hQ := isWeakSerreClass_isBigSiteConstructibleEtaleModule B Y Λ
  refine ((etaleModuleDirectImage.{u, 0} Λ
    (B.inclusion.map t)).derivedCategoryBPlus_rightDerivedFunctorPlus_obj
    (IsBigSiteConstructibleEtaleModule B X Λ) (IsBigSiteConstructibleEtaleModule B Y Λ)
    (fun M hM p => ?_) K hK).2 n
  rcases p with _ | p
  · exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
      ((etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map t)).rightDerivedZeroIsoSelf.app M).symm
      (isConstructibleEtaleModule_directImage_of_isFinite B Λ t hM)
  · exact isConstructibleEtaleModule_of_isZero B Λ Y
      (isZero_rightDerived_etaleModuleDirectImage_of_isIntegralHom Λ (B.inclusion.map t) _
        (p + 1) (by omega))

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X.obj ⟶ Y.obj) [IsSeparated f]
  [LocallyQuasiFinite f] [QuasiCompact f] [LocallyOfFinitePresentation f]
  [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj] (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks 0GK3 for `Rf_!`, through the compactification of Zariski's main theorem.** A
separated quasi-finite morphism `f` of finite presentation to a quasi-compact quasi-separated
scheme has a compactification `j` whose proper part is finite (Stacks 0F2N), and through it
`Rf_!` takes complexes with constructible torsion cohomology sheaves to complexes with
constructible cohomology sheaves. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_isFinite_factorization :
    ∃ j : CompactificationOf (Over.mk f), IsFinite j.toBase ∧
      ∀ (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj)),
        (∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
            ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∧
          IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) →
        ∀ n : ℤ, IsBigSiteConstructibleEtaleModule B Y Λ
          ((DerivedCategory.Plus.homologyFunctor _ n).obj
            ((derivedLowerShriek.{u, 0} f j Λ).obj K)) := by
  obtain ⟨T, j', π, hj', hj'qc, hπ, hπfp, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_finitePresentation_factorization f
  have hT : B.Contains T := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact π Y.property
  let T' : B.Scheme := B.obj T hT
  have : IsProper π := inferInstance
  let jc : CompactificationOf (Over.mk f) :=
    ⟨StructuredArrow.mk (Y := Over.mk π) (Over.homMk (U := Over.mk f) j' hfac.symm),
      ⟨hj', inferInstanceAs (IsProper π)⟩⟩
  refine ⟨jc, hπ, fun K hK n => ?_⟩
  let Z := closedComplement j'
  have hZ : B.Contains Z :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (closedComplementι j') hT
  let jB : X ⟶ T' := ObjectProperty.homMk j'
  let iB : B.obj Z hZ ⟶ T' := ObjectProperty.homMk (closedComplementι j')
  let πB : T' ⟶ Y := ObjectProperty.homMk π
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiCompact π := hπfp.2.1
  have : QuasiSeparated π := hπfp.2.2
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated π
  have : IsOpenImmersion (B.inclusion.map jB) := hj'
  have : IsClosedImmersion (B.inclusion.map iB) :=
    inferInstanceAs (IsClosedImmersion (closedComplementι j'))
  have : IsFinite (B.inclusion.map πB) := hπ
  have : LocallyOfFinitePresentation π := hπfp.1
  have : LocallyOfFinitePresentation (B.inclusion.map πB) :=
    inferInstanceAs (LocallyOfFinitePresentation π)
  have : CompactSpace T'.obj := inferInstanceAs (CompactSpace T)
  have : QuasiSeparatedSpace T'.obj := inferInstanceAs (QuasiSeparatedSpace T)
  refine isConstructibleEtaleModule_homology_derivedLowerShriek_of_sheaf B f jc Λ
    (fun F hF _ p => ?_) K hK n
  exact isConstructibleEtaleModule_rightDerived_directImage_extensionByZero_of_isFinite B Λ
    jB iB (range_eq_compl_range_closedComplementι j') πB hF p

/-- **Stacks 0GK3 for `Rf_!`, through any compactification.** Let `f : X ⟶ Y` be separated,
quasi-finite and of finite presentation, with `Y` quasi-compact and quasi-separated, let `j` be
a compactification of `f` and `Λ` a Noetherian ring. If `K` in `D⁺(X_étale, Λ)` has
constructible torsion cohomology sheaves, so does `Rf_! K = R f̄_*(j_! K)` have constructible
cohomology sheaves. The compactification is moved to the finite one of Zariski's main theorem by
Stacks 0F7I, `Stacks.EtaleCohomology.derivedLowerShriekCompactificationIso`. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_quasiFinite
    (j : CompactificationOf (Over.mk f))
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
        ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∧
      IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (n : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ
      ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((derivedLowerShriek.{u, 0} f j Λ).obj K)) := by
  obtain ⟨jc, -, hjc⟩ :=
    isConstructibleEtaleModule_homology_derivedLowerShriek_of_isFinite_factorization B f Λ
  let e := derivedLowerShriekCompactificationIso f jc j Λ
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
    ((DerivedCategory.Plus.homologyFunctor _ n).mapIso
      (e.app ⟨K, fun q => (hK q).2⟩)) (hjc K hK n)

end Stacks.EtaleCohomology

end
