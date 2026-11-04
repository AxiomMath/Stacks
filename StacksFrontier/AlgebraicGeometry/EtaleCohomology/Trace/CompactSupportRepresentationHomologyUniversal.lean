module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGroupHomologyComparison

/-!
# `(M, ρ) ↦ H_c^{2-i}(X_k̄, ℱ_ρ)` is a universal homological δ-functor

Let `T` be the homological δ-functor `Tᵢ(ρ) = H_c^{2-i}(X_k̄, ℱ_ρ)`. It is coeffaceable:

* in degree one by the count for permutation modules
  (`AlgebraicGeometry.coeffacement_compactSupportRepresentationHomology_zero`);
* in degree two: if `X_k̄` is not proper then `T₂ = H⁰_c(X_k̄, -) = 0` (Tag 03VL); if it is proper,
  `T₂(M) = H⁰(X_k̄, ℱ_M) = M^{π₁(X_k̄)}` and
  `H₂(π₁(X_k̄), M) = H²(X_k̄, ℱ_{M^∨})^∨ = ((M^∨)_{π₁})^∨` have the same number of elements, so
  coeffacing `M` for the homology `H` coeffaces it for `T`, the comparison `γ₁ : T₁ ≅ H₁` matching
  the kernels in the long exact sequences;
* in degrees `≥ 3` trivially, `T` vanishing there.

## Main results

* `AlgebraicGeometry.subsingleton_compactSupportRepresentationHomology_two_of_not_isProper`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology
  Stacks.Frobenius Stacks.ContinuousCohomology

universe u

/-- Enough injectives for sheaves of `Λ`-modules at coefficient universe `0`, pinned. -/
local instance (priority := 3000) etaleModulesEnoughInjectivesCompactUniversal (Λ : Type) [Ring Λ]
    (Y : AlgebraicGeometry.Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Enough injectives for continuous discrete modules at the module universe of the group,
pinned. -/
local instance (priority := 3000) enoughInjectives_continuousModule_compactUniversal (Λ : Type)
    [Ring Λ] (G : Type (u + 1)) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ G) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u + 1, 0} Λ G

namespace AlgebraicGeometry

attribute [local instance] compactSpace_etaleFundamentalGroup

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [IsAlgClosure k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))

omit [IsAlgClosure k kbar] in
/-- **`H⁰_c(X_k̄, ℱ_ρ) = 0` when `X_k̄` is not proper** (Tag 03VL). -/
theorem subsingleton_compactSupportRepresentationHomology_two_of_not_isProper
    (hnp : ¬ IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)))
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    Subsingleton (((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 2).obj M) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have := isIntegral_fieldBaseChange f kbar
  let : ConnectedSpace (fieldBaseChangeObj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).1 :=
    connectedSpace_fieldBaseChange f kbar
  have hK := contains_fieldBaseChange_of_isCurve B X f kbar
  let N := (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
    (fieldBaseChangeObjProj B X f kbar hK).hom y)).obj M
  let HK := (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B
    (fieldBaseChangeObj B X f kbar hK) y Λ).inverse.obj N
  have e : (geometricRepresentationSheaf B X _ Λ f kbar).obj M ≅
      (sheafCompose (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
        (ModuleCat.uliftFunctor.{0, u + 1} Λ)).obj HK.obj :=
    (representationSheafPullbackIso B (fieldBaseChangeObjProj B X f kbar hK) Λ y).app M ≪≫
      (representationSheafIsoEtaleSite B (fieldBaseChangeObj B X f kbar hK) y Λ).app _
  have hf : ¬ IsProper ((geometricSmoothModel f j kbar).j ≫ (geometricSmoothModel f j kbar).q) := by
    rwa [geometricSmoothModel_j_comp_q]
  have h := subsingleton_globalSections_extensionByZero_uliftFunctor.{u, 0} Λ
    (geometricSmoothModel f j kbar).j kbar (geometricSmoothModel f j kbar).q hf HK.obj HK.property
  have e' : ((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 2).obj M ≅
      (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj
          ((sheafCompose (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
            (ModuleCat.uliftFunctor.{0, u + 1} Λ)).obj HK.obj)) :=
    (etaleModuleGlobalSections.{u, 0} Λ
        (geometricSmoothModel f j kbar).Vb).rightDerivedZeroIsoSelf.app _ ≪≫
      (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).mapIso
        ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).mapIso e)
  exact subsingleton_of_moduleIso Λ e'.symm h

section Proper

variable [CompactSpace X.1] [QuasiSeparatedSpace X.1] (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
  {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  (hcomp : letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    IsIso (geometricComparison B X Λ f kbar (contains_fieldBaseChange_of_isCurve B X f kbar) y))
  (hcompOp : letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    IsIso (geometricComparison B X Λᵐᵒᵖ f kbar (contains_fieldBaseChange_of_isCurve B X f kbar) y))

include hcomp j in
/-- **`#H⁰_c(X_k̄, ℱ_M) = #M^{π₁(X_k̄)}`, finite**, for `X_k̄` proper. -/
theorem finite_and_natCard_compactSupportRepresentationHomology_two_of_isProper
    (hp : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)))
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Finite (((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 2).obj M) ∧
      Nat.card (((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 2).obj M) =
        Nat.card ((continuousModuleRingInvariants.{0, u + 1, u + 1} Λ _).obj
          ((finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar) y)).obj M)) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have hK := contains_fieldBaseChange_of_isCurve B X f kbar
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb)
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ (pullback f (specAlgebraMap k kbar)))
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar))
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  have hp' : IsProper (pullback.snd f (specAlgebraMap k kbar)) := hp
  let G := (geometricRepresentationSheaf B X _ Λ f kbar).obj M
  let e : ((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 2).obj M ≅
      ((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk f) kbar)).rightDerived 0).obj G :=
    (Stacks.DerivedIndexing.rightDerivedIso _ 0).app _ ≪≫
      geometricSmoothModelProperRightDerivedPlusIso f j kbar Λ hp' G ((0 : ℕ) : ℤ) ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso _ 0).app G).symm
  have hbij := bijective_app_of_iso Λ (asIso (geometricComparison B X Λ f kbar hK y)) 0 M
  let M' := (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f kbar hK y)).obj M
  let e0 := ((continuousModuleRingInvariants.{0, u + 1, u + 1} Λ _).rightDerivedZeroIsoSelf).app M'
  have := finite_geometricGroupCohomology_zero B X f kbar Λ y M
  have : Finite (((etaleModuleGlobalSections.{u, 0} Λ
      (fieldBaseChange (Over.mk f) kbar)).rightDerived 0).obj G) :=
    Finite.of_equiv _ (Equiv.ofBijective _ hbij)
  exact ⟨Finite.of_equiv _ e.toLinearEquiv.toEquiv.symm,
    (Nat.card_congr e.toLinearEquiv.toEquiv).trans
      ((Nat.card_congr (Equiv.ofBijective _ hbij)).symm.trans
        (Nat.card_congr e0.toLinearEquiv.toEquiv))⟩

include hn hζ hcompOp j in
/-- **`#H₂(π₁(X_k̄), M) = #(M^∨)_{π₁(X_k̄)}`** for `X_k̄` proper: `H²(π₁, M^∨) = H²(X_k̄, ℱ_{M^∨})`
(over `Λᵐᵒᵖ`) is `H²_c` and Tag 03VK computes it. -/
theorem natCard_geometricGroupHomology_two_of_isProper
    (hp : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)))
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Nat.card (((geometricGroupHomology B X f kbar Λ y).functor 2).obj M) =
      Nat.card ((restrictedCoinvariantsFunctor Λᵐᵒᵖ (geometricFundamentalGroupMap B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar) y)).obj
          ((finiteTypeContinuousModuleDual Λ _).obj (Opposite.op M))) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have hK := contains_fieldBaseChange_of_isCurve B X f kbar
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λᵐᵒᵖ (geometricSmoothModel f j kbar).Vb)
  let := HasDerivedCategory.standard
    (EtaleModules.{u, 0} Λᵐᵒᵖ (pullback f (specAlgebraMap k kbar)))
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λᵐᵒᵖ (fieldBaseChange (Over.mk f) kbar))
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} Λᵐᵒᵖ)
  have hp' : IsProper (pullback.snd f (specAlgebraMap k kbar)) := hp
  have hc : Fintype.card Λᵐᵒᵖ = Fintype.card Λ := Fintype.card_congr MulOpposite.opEquiv.symm
  have hnOp : IsUnit ((Fintype.card Λᵐᵒᵖ : ℕ) : kbar) := by rwa [hc]
  have hζOp : IsPrimitiveRoot ζ (Fintype.card Λᵐᵒᵖ) := by rwa [hc]
  let DM := (finiteTypeContinuousModuleDual Λ _).obj (Opposite.op M)
  have := finite_geometricGroupCohomology B X f kbar Λᵐᵒᵖ y j hnOp hcompOp DM 2
  let G := (geometricRepresentationSheaf B X _ Λᵐᵒᵖ f kbar).obj DM
  let e : ((etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ (fieldBaseChange (Over.mk f) kbar)).rightDerived
      2).obj G ≅ ((compactSupportRepresentationHomology B X _ Λᵐᵒᵖ f j kbar).functor 0).obj DM :=
    (Stacks.DerivedIndexing.rightDerivedIso _ 2).app G ≪≫
      (geometricSmoothModelProperRightDerivedPlusIso f j kbar Λᵐᵒᵖ hp' G ((2 : ℕ) : ℤ)).symm ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso _ 2).app _).symm
  have hbij := bijective_app_of_iso Λᵐᵒᵖ (asIso (geometricComparison B X Λᵐᵒᵖ f kbar hK y)) 2 DM
  have h0 : Nat.card (((geometricGroupHomology B X f kbar Λ y).functor 2).obj M) =
      Nat.card (((geometricGroupCohomology B X Λᵐᵒᵖ f kbar hK y).functor 2).obj DM) :=
    CharacterModule.natCard_eq (((geometricGroupCohomology B X Λᵐᵒᵖ f kbar hK y).functor 2).obj DM)
  exact h0.trans <| (Nat.card_congr (Equiv.ofBijective _ hbij)).trans <|
    (Nat.card_congr e.toLinearEquiv.toEquiv).trans <| Nat.card_congr
      (compactSupportRepresentationHomologyZeroCoinvariantsIsoApp B X f kbar Λᵐᵒᵖ y j hnOp hζOp
        DM).toLinearEquiv.toEquiv

omit [Smooth f] [IsAlgClosed kbar] [IsAlgClosure k kbar] [CompactSpace X.1]
  [QuasiSeparatedSpace X.1] in
/-- **`#M^{π₁(X_k̄)} = #(M^∨)_{π₁(X_k̄)}`**: invariant characters of `M^∨` are characters of its
coinvariants, and `M ≅ (M^∨)^∨`. -/
theorem natCard_invariants_eq_natCard_coinvariants_dual
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Nat.card ((continuousModuleRingInvariants.{0, u + 1, u + 1} Λ _).obj
        ((finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar) y)).obj M)) =
      Nat.card ((restrictedCoinvariantsFunctor Λᵐᵒᵖ (geometricFundamentalGroupMap B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar) y)).obj
          ((finiteTypeContinuousModuleDual Λ _).obj (Opposite.op M))) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  let φ :=
    geometricFundamentalGroupMap B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar) y
  let σ := finiteTypeContinuousModuleRepresentation Λ _ ((finiteTypeContinuousModuleRes Λ φ).obj M)
  have : Module.Finite Λ M.obj.obj.obj.V := M.property
  have : Finite M.obj.obj.obj.V := Module.finite_of_finite Λ
  have hrep : finiteTypeContinuousModuleRepresentation Λᵐᵒᵖ _
      ((finiteTypeContinuousModuleRes Λᵐᵒᵖ φ).obj
        ((finiteTypeContinuousModuleDual Λ _).obj (Opposite.op M))) = characterRepresentation σ :=
    MonoidHom.ext fun g ↦ LinearMap.ext fun c ↦ (characterRepresentation_apply_of_eq σ
      (finiteTypeContinuousModuleRepresentation Λ _ M) φ.toMonoidHom (fun _ ↦ rfl) g c).symm
  have h1 : Nat.card ((continuousModuleRingInvariants.{0, u + 1, u + 1} Λ _).obj
      ((finiteTypeContinuousModuleToRes Λ φ).obj M)) = Nat.card {v // ∀ g, σ g v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ Iff.rfl)
  show _ = Nat.card (Stacks.Trace.coinvariants (finiteTypeContinuousModuleRepresentation Λᵐᵒᵖ _
      ((finiteTypeContinuousModuleRes Λᵐᵒᵖ φ).obj
        ((finiteTypeContinuousModuleDual Λ _).obj (Opposite.op M)))))
  rw [hrep, h1]
  have : Finite ((finiteTypeContinuousModuleRes Λ φ).obj M).obj.obj.obj.V :=
    inferInstanceAs (Finite M.obj.obj.obj.V)
  exact natCard_invariants_eq_natCard_coinvariants_characterRepresentation σ

include hn hζ hcomp hcompOp j in
/-- **`T₂ = H⁰_c(X_k̄, -)` is coeffaceable.** -/
theorem coeffacement_compactSupportRepresentationHomology_one
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Nonempty ((compactSupportRepresentationHomology B X _ Λ f j kbar).Coeffacement M 1) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  by_cases hp : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
  · have := coeffaceable_geometricGroupHomology B X f kbar Λ y j hn hcompOp
    obtain ⟨c⟩ := Stacks.CategoryHomology.HomologicalDeltaFunctor.Coeffaceable.nonempty
      (H := geometricGroupHomology B X f kbar Λ y) M 1
    let T := compactSupportRepresentationHomology B X
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
      Λ f j kbar
    let γ := compactSupportGroupHomologyComparison B X f kbar Λ y j hn hζ hcompOp
    let S := ShortComplex.mk (kernel.ι c.π) c.π (kernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel S (kernelIsKernel c.π))
        (inferInstanceAs (Mono (kernel.ι c.π))) (inferInstanceAs (Epi c.π))
    obtain ⟨hfin, hT2⟩ :=
      finite_and_natCard_compactSupportRepresentationHomology_two_of_isProper B X f kbar Λ y j
        hcomp hp M
    have := hfin
    have hcard : Nat.card ((T.functor 2).obj S.X₃) ≤
        Nat.card (LinearMap.ker ((T.functor 1).map S.f).hom) := by
      have hk : Nat.card (LinearMap.ker ((T.functor 1).map S.f).hom) =
          Nat.card
            (LinearMap.ker (((geometricGroupHomology B X f kbar Λ y).functor 1).map S.f).hom) :=
        natCard_ker_eq_of_comp_eq _ _
          (LinearEquiv.ofBijective _ (bijective_compactSupportGroupHomologyComparison_app_one
            B X f kbar Λ y j hn hζ hcompOp S.X₁))
          (LinearEquiv.ofBijective _ (bijective_compactSupportGroupHomologyComparison_app_one
            B X f kbar Λ y j hn hζ hcompOp S.X₂))
          (congrArg ModuleCat.Hom.hom ((γ.app 1).naturality S.f)).symm
      rw [hk, Stacks.CategoryHomology.HomologicalDeltaFunctor.natCard_ker_map_f_eq_of_map_g_eq_zero
        _ hS 1 c.map_π,
        natCard_geometricGroupHomology_two_of_isProper B X f kbar Λ y j hn hζ hcompOp hp,
        ← natCard_invariants_eq_natCard_coinvariants_dual B X f kbar Λ y M]
      exact hT2.le
    exact ⟨⟨c.P, c.π, Stacks.CategoryHomology.HomologicalDeltaFunctor.map_g_eq_zero_of_natCard_le
      T hS 1 hcard⟩⟩
  · have := subsingleton_compactSupportRepresentationHomology_two_of_not_isProper B X f kbar Λ y j
      hp M
    exact ⟨⟨M, 𝟙 M, ModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)⟩⟩

include hn hζ hcomp hcompOp j in
/-- **`(M, ρ) ↦ H_c^{2-i}(X_k̄, ℱ_ρ)` is coeffaceable.** -/
theorem coeffaceable_compactSupportRepresentationHomology :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (compactSupportRepresentationHomology B X
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j kbar).Coeffaceable := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  exact Stacks.CategoryHomology.HomologicalDeltaFunctor.coeffaceable_ofDeltaFunctorTwoSub _ _
    (fun M ↦ by
      obtain ⟨c⟩ :=
        coeffacement_compactSupportRepresentationHomology_zero B X f kbar Λ y j hn hcompOp M
      exact ⟨c.P, c.π, c.epi, c.map_π⟩)
    (fun M ↦ by
      obtain ⟨c⟩ := coeffacement_compactSupportRepresentationHomology_one B X f kbar Λ y j hn hζ
        hcomp hcompOp M
      exact ⟨c.P, c.π, c.epi, c.map_π⟩)

include hn hζ hcomp hcompOp j in
/-- **The functors `(M, ρ) ↦ H_c^{2-i}(X_k̄, ℱ_ρ)` are the left derived functors of
`(M, ρ) ↦ H_c^2(X_k̄, ℱ_ρ)`**: they form a universal homological δ-functor. -/
theorem isUniversal_compactSupportRepresentationHomology :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (compactSupportRepresentationHomology B X
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j kbar).IsUniversal := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have := coeffaceable_compactSupportRepresentationHomology B X f kbar Λ y j hn hζ hcomp hcompOp
  exact Stacks.CategoryHomology.HomologicalDeltaFunctor.isUniversal_of_coeffaceable _

include hn hζ hcomp hcompOp j in
/-- **`H_c^{2-i}(X_k̄, ℱ_ρ) ≅ H_i(π₁(X_k̄, η̄), M)`** as homological δ-functors, extending Tag 03VK
in degree zero. -/
def compactSupportGroupHomologyIso :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    compactSupportRepresentationHomology B X
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j kbar ≅
      geometricGroupHomology B X f kbar Λ y :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  haveI := isUniversal_compactSupportRepresentationHomology B X f kbar Λ y j hn hζ hcomp hcompOp
  haveI := isUniversal_geometricGroupHomology B X f kbar Λ y j hn hcompOp
  Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.isoOfIso
    (compactSupportRepresentationHomologyZeroCoinvariantsIso B X f kbar Λ y j hn hζ ≪≫
      (restrictedHomologyZeroIso Λ _).symm)

end Proper

end AlgebraicGeometry

end
