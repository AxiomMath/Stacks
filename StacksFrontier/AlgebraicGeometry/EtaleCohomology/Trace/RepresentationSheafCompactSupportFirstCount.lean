module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRepresentationCoindFirstCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCompactSupportCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationCohomologyNotProjectiveLine
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteTypePermutation

/-!
# `H¹_c(X_k̄, ℱ_P)` and `H¹(X_k̄, ℱ_P)` of a permutation module, through a cover

Let `X` be a geometrically connected smooth curve over `k`, `Γ = π₁(X, η̄)`, `H ⊆ Γ` an open
normal subgroup and `P = N[Γ/H]` the permutation module of a finite `Λ`-module `N`. Restricted to
`G = π₁(X_k̄, η̄)` (whose image is normal, Tag 0BTX), `P` is the permutation module
`(N^I)[G/(G ∩ H)]` (Mackey), so `ℱ_P|_{X_k̄} = φ_*(N^I)` for the connected cover `φ : V ⟶ X_k̄`
with group `G ∩ H`. Hence `H¹_c(X_k̄, ℱ_P) = H¹(V̄, j_! N^I)` and `H¹(X_k̄, ℱ_P) = H¹(V, N^I)` for
the smooth projective compactification `V̄` of `V`: the count `#H¹_c ≤ #H¹` for `ℱ_P` (Tag 03VM)
becomes one for constant coefficients on a smooth curve.

## Main results

* `AlgebraicGeometry.exists_cover_compactSupportRepresentationHomology_one_linearEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology
  Stacks.Frobenius

universe u

/-- Enough injectives for sheaves of `Λ`-modules at coefficient universe `0`, pinned. -/
local instance (priority := 3000) etaleModulesEnoughInjectivesFirstCountX (Λ : Type) [Ring Λ]
    (Y : AlgebraicGeometry.Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

namespace AlgebraicGeometry

attribute [local instance] compactSpace_etaleFundamentalGroup

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))
  [ConnectedSpace X.1] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] [CompactSpace X.1]
  [QuasiSeparatedSpace X.1]

/-- **`H¹_c(X_k̄, ℱ_P)` and `H¹(X_k̄, ℱ_P)` for a permutation module `P = N[Γ/H]`**, `H` open
normal, are `H¹(V̄, j_! E)` and `H¹(V, E)` for a smooth curve `V` and an open immersion `V ⟶ V̄`
into a smooth proper curve, which depend only on `H`, and `E = N^I` with `I = Γ/(π₁(X_k̄)H)`
(Mackey), for every finite ring `Λ` and finite `Λ`-module `N`. -/
theorem exists_cover_compactSupportRepresentationHomology_one_linearEquiv
    (H : OpenSubgroup (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    [H.toSubgroup.Normal] :
    ∃ (V Vb : Scheme.{u}) (qV : V ⟶ Spec (.of kbar)) (qb : Vb ⟶ Spec (.of kbar)) (jV : V ⟶ Vb)
      (_ : IsCurve kbar qV) (_ : Smooth qV) (_ : IsCurve kbar qb) (_ : Smooth qb)
      (_ : IsProper qb) (_ : IsOpenImmersion jV), ∀ (Λ : Type) [Ring Λ] [Finite Λ]
        (Q : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)),
      Nonempty (((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 1).obj
          ((finiteTypeContinuousModuleCoind Λ H).obj
            ((finiteTypeContinuousModuleTrivial Λ _).obj Q))
          ≃ₗ[Λ]
        ((etaleModuleGlobalSections.{u, 0} Λ Vb).rightDerived 1).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ jV).obj
            ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
              ((ModuleCat.uliftFunctor.{0, u + 1} Λ).obj ((ModuleCat.isFG Λ).ι.obj
                (mackeyCoefficient Λ (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
                  (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) H Q)))))) ∧
      Nonempty (((geometricRepresentationCohomology.{u, 0} B X _ Λ f kbar).functor 1).obj
          ((finiteTypeContinuousModuleCoind Λ H).obj
            ((finiteTypeContinuousModuleTrivial Λ _).obj Q))
          ≃ₗ[Λ]
        ((etaleModuleGlobalSections.{u, 0} Λ V).rightDerived 1).obj
          ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            ((ModuleCat.uliftFunctor.{0, u + 1} Λ).obj ((ModuleCat.isFG Λ).ι.obj
              (mackeyCoefficient Λ (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
                (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) H Q))))) := by
  have hK := contains_fieldBaseChange_of_isCurve B X f kbar
  have : (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar hK).hom
      y).toMonoidHom.range.Normal :=
    normal_range_etaleFundamentalGroupMap_of_isPullback_isAlgClosed k kbar f
      (fieldBaseChangeObjProj B X f kbar hK).hom
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) (IsPullback.of_hasPullback _ _) y
  have := (geometricSmoothModel f j kbar).isCurve
  have := (geometricSmoothModel f j kbar).smooth
  have := (geometricSmoothModel f j kbar).isProper
  have := (geometricSmoothModel f j kbar).isOpenImmersion
  let φ := etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar hK).hom y
  obtain ⟨V, Vb, qV, qb, jV, h1, h2, h3, h4, h5, h6, hcov⟩ :=
    exists_cover_rightDerived_coindTrivial_linearEquiv B (fieldBaseChangeObj B X f kbar hK) y
      (mackeyOpenSubgroup φ H) (geometricSmoothModel f j kbar).q (geometricSmoothModel f j kbar).j
  refine ⟨V, Vb, qV, qb, jV, h1, h2, h3, h4, h5, h6, fun Λ _ _ Q ↦ ?_⟩
  have : Fintype Λ := Fintype.ofFinite Λ
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := hcov Λ (mackeyCoefficient Λ φ H Q)
  let s := (representationSheafFieldBaseChangeIso B X f kbar Λ y).app
      ((finiteTypeContinuousModuleCoind Λ H).obj ((finiteTypeContinuousModuleTrivial Λ _).obj Q)) ≪≫
    (representationSheaf B (fieldBaseChangeObj B X f kbar hK) y Λ).mapIso
      (finiteTypeContinuousModuleResCoindTrivialIso Λ φ H Q)
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · exact (((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerived
      1).mapIso ((etaleModuleExtensionByZero.{u, 0} Λ
        (geometricSmoothModel f j kbar).j).mapIso s)).toLinearEquiv.trans e1
  · exact (((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).rightDerived
      1).mapIso s).toLinearEquiv.trans e2

end AlgebraicGeometry

end
