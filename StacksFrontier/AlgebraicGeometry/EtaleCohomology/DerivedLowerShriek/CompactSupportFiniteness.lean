module
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.AlgebraicallyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.RingTheory.Etale.Basic

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Constructibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteTypeStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.AlgebraicallyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage

/-!
# Finiteness of cohomology with compact support

Let `k` be an algebraically closed field, `X` a separated scheme of finite type over `k` and `Λ` a
Noetherian ring. [Stacks, Tag 0GLH] says that `H^i_c(X, K)` is a finite `Λ`-module for every `K`
in `D⁺_{tors, c}(X_étale, Λ)`, or in `D_c(X_étale, Λ)` if `Λ` is torsion.

## Main results

* `Stacks.EtaleCohomology.module_finite_etaleModuleGlobalSections_of_isConstructibleEtaleModule`:
  global sections over the spectrum of an algebraically closed field of a constructible sheaf of
  `Λ`-modules form a finite `Λ`-module.
* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnboundedIsoOfIsSepClosed`: over a
  separably closed field `RΓ(Spec k, -)` is global sections applied degreewise.
* `Stacks.EtaleCohomology.module_finite_compactlySupportedCohomologyGroupUnbounded`:
  [Stacks, Tag 0GLH], granted Tags 095T, 095U and 0GKZ.

## References

* [Stacks Project, Tag 0GLH](https://stacks.math.columbia.edu/tag/0GLH)
* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
* [Stacks Project, Tag 0GKC](https://stacks.math.columbia.edu/tag/0GKC)
* [Stacks Project, Tag 04JN](https://stacks.math.columbia.edu/tag/04JN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat moduleCat_hasLimitsOfSize

section GlobalSections

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ] (K : Type u) [Field K] [IsAlgClosed K]

omit [IsNoetherianRing Λ] in
/-- **A constructible sheaf on the spectrum of an algebraically closed field has finite global
sections.** -/
theorem module_finite_etaleModuleGlobalSections_of_isConstructibleEtaleModule
    (F : EtaleModules.{u, r} Λ (Spec (.of K))) (hF : IsConstructibleEtaleModule Λ F) :
    Module.Finite Λ ((etaleModuleGlobalSections.{u, r} Λ (Spec (.of K))).obj F) := by
  let B := BigEtaleSite.containing (Spec (.of K))
  have hK : B.Contains (Spec (.of K)) := BigEtaleSite.contains_containing _
  let FB := (etaleModuleToBoundedSite Λ B hK).obj F
  have hfg := isFG_etaleStalk_of_isConstructibleModuleSheaf B Λ (B.obj (Spec (.of K)) hK) FB
    ((isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hK F).1 hF)
    (_root_.AlgebraicGeometry.canonicalGeometricPoint K)
  rw [ModuleCat.isFG_iff] at hfg
  let e₁ : etaleStalk B (Spec (.of K)) hK (_root_.AlgebraicGeometry.canonicalGeometricPoint K)
        FB.obj ≅
      FB.obj.obj (op (SmallEtale.final B (Spec (.of K)) hK)) :=
    colimit.isoColimitCocone ⟨_, colimitOfDiagramTerminal
      (_root_.AlgebraicGeometry.canonicalPointFiberTerminalIndex B K hK) _⟩
  let T := (SmallEtale.toEtaleSite B (Spec (.of K)) hK).obj (SmallEtale.final B (Spec (.of K)) hK)
  have : IsIso T.hom := by
    change IsIso (B.inclusion.map (𝟙 (B.obj (Spec (.of K)) hK)))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  let e₂ : (etaleModuleGlobalSections.{u, r} Λ (Spec (.of K))).obj F ≅ F.obj.obj (op T) :=
    (Sheaf.ΓNatIsoSheafSections _ _ (isTerminalOfIsIsoHom T)).app F
  exact Module.Finite.equiv (e₁ ≪≫ e₂.symm).toLinearEquiv

end GlobalSections

section DerivedGlobalSections

variable (Λ : Type r) [Ring Λ] (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- Over a separably closed field, global sections of sheaves of `Λ`-modules is an equivalence. -/
theorem isEquivalence_etaleModuleGlobalSections_of_isSepClosed :
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))).IsEquivalence :=
  isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{max (u + 1) r} Λ)

/-- **Over a separably closed field `RΓ(Spec Ω, -)` is global sections applied degreewise.** -/
def etaleModuleDerivedGlobalSectionsUnboundedIsoOfIsSepClosed :
    haveI := isEquivalence_etaleModuleGlobalSections_of_isSepClosed.{u, r} Λ Ω
    etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of Ω)) ≅
      (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))).mapDerivedCategory :=
  haveI := isEquivalence_etaleModuleGlobalSections_of_isSepClosed.{u, r} Λ Ω
  haveI := Functor.isRightDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ (Spec (.of Ω))) (ComplexShape.up ℤ))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))).mapDerivedCategory
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))).mapDerivedCategoryFactors
  Functor.rightDerivedUnique _ _
    (etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ (Spec (.of Ω)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))).mapDerivedCategoryFactors.inv
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ (Spec (.of Ω))) (ComplexShape.up ℤ))

/-- Over a separably closed field, `H^i(RΓ(Spec Ω, L)) ≅ Γ(Spec Ω, H^i(L))`. -/
def homologyEtaleModuleDerivedGlobalSectionsUnboundedIsoOfIsSepClosed
    (L : DerivedCategory (EtaleModules.{u, r} Λ (Spec (.of Ω)))) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj
        ((etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of Ω))).obj L) ≅
      (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))).obj
        ((DerivedCategory.homologyFunctor _ i).obj L) :=
  haveI := isEquivalence_etaleModuleGlobalSections_of_isSepClosed.{u, r} Λ Ω
  (DerivedCategory.homologyFunctor _ i).mapIso
      ((etaleModuleDerivedGlobalSectionsUnboundedIsoOfIsSepClosed.{u, r} Λ Ω).app L) ≪≫
    ((etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))).mapDerivedCategoryHomologyIso i).app L

end DerivedGlobalSections

section Theorem

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **[Stacks, Tag 0GLH], granted the proper base change theorem, Tag 095U and Tag 0GKZ.** Let `k`
be an algebraically closed field, `X` a separated scheme of finite type over `k` with structure
morphism `f`, and `Λ` a Noetherian ring. Let `K` be an object of `D⁺_{tors, c}(X_étale, Λ)`, or of
`D_c(X_étale, Λ)` in case `Λ` is torsion. Then `H^i_c(X, K)` is a finite `Λ`-module for every
`i`, `H^i_c(X, K) = H^i(RΓ(Spec k, Rf_! K))` being computed through any compactification `j` of
`f` (Tag 0GJZ). The ring `Λ` lives in `Type (u + 1)`.

Named arguments (as for `constructible_derivedLowerShriekUnbounded`):
* `h095T` is Stacks Tag 095T;
* `h095U` is Stacks Tag 095U;
* `h0GKZ` is Stacks Tag 0GKZ
  (`Stacks.EtaleCohomology.isConstructibleEtaleComplex_derivedLowerShriekUnbounded_affineLine`). -/
theorem module_finite_compactlySupportedCohomologyGroupUnbounded
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, u + 1} p).rightDerived q).obj F))
    (h0GKZ : ∀ (Y : Scheme.{u}) [IsAffine Y]
      (j : CompactificationOf (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)))
      (F : EtaleModules.{u, u + 1} Λ 𝔸(ULift.{u} (Fin 1); Y)),
      IsConstructibleEtaleModule Λ F → IsTorsionEtaleModule Λ 𝔸(ULift.{u} (Fin 1); Y) F →
      IsConstructibleEtaleComplex Λ
        ((derivedLowerShriekUnbounded.{u, u + 1} (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) j Λ).obj
          ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ 𝔸(ULift.{u} (Fin 1); Y)) 0).obj
            F)))
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, u + 1} Λ X))
    (hK : IsTorsionConstructibleEtaleComplexPlus Λ K ∨
      (IsAddTorsion Λ ∧ IsConstructibleEtaleComplex Λ K)) (i : ℤ) :
    Module.Finite Λ ((compactlySupportedCohomologyGroupUnbounded.{u, u + 1} k f j Λ i).obj K) := by
  have : LocallyOfFinitePresentation f := LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 ‹_›
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have h := constructible_derivedLowerShriekUnbounded Λ h095T h095U h0GKZ f j
  have hL :
      IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} f j Λ).obj K) := by
    rcases hK with hK | ⟨hΛ, hK⟩
    · exact fun n ↦ ((h.1 K hK).2 n).2
    · exact h.2 hΛ K hK
  have := module_finite_etaleModuleGlobalSections_of_isConstructibleEtaleModule Λ k _ (hL i)
  exact Module.Finite.equiv
    (homologyEtaleModuleDerivedGlobalSectionsUnboundedIsoOfIsSepClosed.{u, u + 1}
      Λ k _ i).symm.toLinearEquiv

end Theorem

end Stacks.EtaleCohomology

end
