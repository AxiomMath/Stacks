module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCompactSupportFirstCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCompactSupportCoeffacement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationComparisonIso
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictedHomologyDelta
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.ElementwiseEffaceableFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveCompactSupportFirstCount

/-!
# Coeffacing `(M, ρ) ↦ H_c^1(X_k̄, ℱ_ρ)`

Let `Λ` be a finite ring, not necessarily commutative, `T` the homological δ-functor
`Tᵢ(ρ) = H_c^{2-i}(X_k̄, ℱ_ρ)` and `H` the homology `Hᵢ(M) = H^i(π₁(X_k̄), M^∨)^∨` of the
geometric fundamental group, `M^∨` being a left `Λᵐᵒᵖ`-module. A finite module `M` with
continuous action, on which the open normal subgroup `U` acts trivially, is a quotient of the
permutation module `P = M[Γ/U]` (`f ↦ Σ_x x • f(x)`), and `P^∨ ≅ M^∨[Γ/U]` over `Λᵐᵒᵖ`. Coeffacing
`P` for `H` in degree one by `π : P'' ⟶ P` with kernel `K`, the long exact sequences and Tag 03VK
give `#ker T₀(K → P'') = #ker H₀(K → P'') = #H₁(P) = #H¹(π₁(X_k̄), P^∨) = #H¹(X_k̄, ℱ_{M^∨[Γ/U]})`,
the last by the cohomological half of Tag 03VM over `Λᵐᵒᵖ`. Both `T₁(P)` and that group are
computed on one cover `V` of `X_k̄` (depending only on `U`) with constant coefficients `M^I` and
`(M^∨)^I`; as `M ≃ M^∨` as groups (`CharacterModule.nonempty_addEquiv`), the count for constant
coefficients gives `#T₁(P) ≤ #H¹(X_k̄, ℱ_{M^∨[Γ/U]})`, hence `T₁(π) = 0`, so `P'' ⟶ P ⟶ M`
coeffaces `M` for `T` in degree one.

## Main results

* `AlgebraicGeometry.finite_and_natCard_compactSupportRepresentationHomology_one_le` — the count
  `#H¹_c(X_k̄, ℱ_P) ≤ #H¹(X_k̄, ℱ_P)` for permutation modules, from the cover and the count for
  constant coefficients
  (`Stacks.EtaleCohomology.finite_and_finite_and_natCard_rightDerived_one_extensionByZero_le`).
* `AlgebraicGeometry.finite_and_natCard_compactSupportRepresentationHomology_one_le_of_addEquiv` —
  the same count against the permutation module of an isomorphic group over another finite ring.
* `AlgebraicGeometry.coeffacement_compactSupportRepresentationHomology_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology
  Stacks.Frobenius Stacks.ContinuousCohomology

universe u

/-- Sheafification for sheaves of `Λ`-modules at the module universe `u + 1`, pinned. -/
local instance (priority := 3000) etaleModulesHasSheafifyCoeffaceable (Λ : Type) [Ring Λ]
    (Y : AlgebraicGeometry.Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

/-- Enough injectives for sheaves of `Λ`-modules at coefficient universe `0`, pinned. -/
local instance (priority := 3000) etaleModulesEnoughInjectivesCoeffaceable (Λ : Type) [Ring Λ]
    (Y : AlgebraicGeometry.Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

namespace AlgebraicGeometry

attribute [local instance] compactSpace_etaleFundamentalGroup

/-- **`H¹(V, E_V)` depends only on the group underlying the finite module `E`**, in sheaves of
modules over any ring. -/
def rightDerivedOneConstantSheafAddEquiv (V : Scheme.{u}) (Λ Λ' : Type) [Ring Λ] [Ring Λ']
    (E : ModuleCat.{u + 1} Λ) (E' : ModuleCat.{u + 1} Λ') [Finite E] [Finite E'] (e : E ≃+ E') :
    ((etaleModuleGlobalSections.{u, 0} Λ V).rightDerived 1).obj
        ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) ≃+
      ((etaleModuleGlobalSections.{u, 0} Λ' V).rightDerived 1).obj
        ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj E') :=
  letI := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ V)
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  letI := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ' V)
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ')
  ((Stacks.DerivedIndexing.rightDerivedIso _ 1).app _).toLinearEquiv.toAddEquiv.trans <|
    (constantModuleCohomologyAddEquivSheafH Λ E V 1).trans <|
    (sheafHEtaleConstantAddEquivOfAddEquiv V
      ((Shrink.addEquiv.{0} (α := E)).trans
        (e.trans (Shrink.addEquiv.{0} (α := E')).symm)) 1).trans <|
    (constantModuleCohomologyAddEquivSheafH Λ' E' V 1).symm.trans
      ((Stacks.DerivedIndexing.rightDerivedIso _ 1).app _).toLinearEquiv.toAddEquiv.symm

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [IsAlgClosure k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))
  [ConnectedSpace X.1] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] [CompactSpace X.1]
  [QuasiSeparatedSpace X.1]

omit [IsAlgClosure k kbar] [Fintype Λ] in
/-- **`#H¹_c(X_k̄, ℱ_P) ≤ #H¹(X_k̄, ℱ_{P'})`, both finite**, for permutation modules `P = Q[Γ/H]`
over `Λ` and `P' = Q'[Γ/H]` over a finite ring `Λ'`, `H` open normal, `#Λ` invertible in `k̄`,
whenever `Q ≃ Q'` as groups. -/
theorem finite_and_natCard_compactSupportRepresentationHomology_one_le_of_addEquiv
    [Finite Λ] (hΛ : IsUnit (Nat.card Λ : kbar))
    (H : OpenSubgroup (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) [H.toSubgroup.Normal]
    (Q : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ))
    (Λ' : Type) [Ring Λ'] [Finite Λ']
    (Q' : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ'))
    (eQ : Q.obj ≃+ Q'.obj) :
    Finite (((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 1).obj
        ((finiteTypeContinuousModuleCoind Λ H).obj
          ((finiteTypeContinuousModuleTrivial Λ _).obj Q))) ∧
      Finite (((geometricRepresentationCohomology.{u, 0} B X _ Λ' f kbar).functor 1).obj
        ((finiteTypeContinuousModuleCoind Λ' H).obj
          ((finiteTypeContinuousModuleTrivial Λ' _).obj Q'))) ∧
      Nat.card (((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 1).obj
        ((finiteTypeContinuousModuleCoind Λ H).obj
          ((finiteTypeContinuousModuleTrivial Λ _).obj Q))) ≤
      Nat.card (((geometricRepresentationCohomology.{u, 0} B X _ Λ' f kbar).functor 1).obj
        ((finiteTypeContinuousModuleCoind Λ' H).obj
          ((finiteTypeContinuousModuleTrivial Λ' _).obj Q'))) := by
  obtain ⟨V, Vb, qV, qb, jV, h1, h2, h3, h4, h5, h6, hcov⟩ :=
    exists_cover_compactSupportRepresentationHomology_one_linearEquiv B X f kbar y j H
  obtain ⟨⟨e1⟩, -⟩ := hcov Λ Q
  obtain ⟨-, ⟨e2'⟩⟩ := hcov Λ' Q'
  have : Module.Finite Λ Q.obj := Q.property
  have : Finite Q.obj := Module.finite_of_finite Λ
  have : Module.Finite Λ' Q'.obj := Q'.property
  have : Finite Q'.obj := Module.finite_of_finite Λ'
  let φ := etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y
  let E := (ModuleCat.uliftFunctor.{0, u + 1} Λ).obj ((ModuleCat.isFG Λ).ι.obj
    (mackeyCoefficient Λ φ H Q))
  let E' := (ModuleCat.uliftFunctor.{0, u + 1} Λ').obj ((ModuleCat.isFG Λ').ι.obj
    (mackeyCoefficient Λ' φ H Q'))
  have : Finite E := inferInstanceAs (Finite (ULift (mackeyIndex φ H → Q.obj)))
  have : Finite E' := inferInstanceAs (Finite (ULift (mackeyIndex φ H → Q'.obj)))
  let eE : E ≃+ E' := AddEquiv.ulift.trans
    ((AddEquiv.piCongrRight fun _ ↦ eQ).trans AddEquiv.ulift.symm)
  obtain ⟨hf1, hf2, hle⟩ :=
    finite_and_finite_and_natCard_rightDerived_one_extensionByZero_le qV qb jV Λ E hΛ
  let c := rightDerivedOneConstantSheafAddEquiv V Λ Λ' E E' eE
  have := hf2
  refine ⟨Finite.of_equiv _ e1.toEquiv.symm,
    Finite.of_equiv _ (c.toEquiv.trans e2'.toEquiv.symm), ?_⟩
  rw [Nat.card_congr e1.toEquiv, Nat.card_congr e2'.toEquiv, ← Nat.card_congr c.toEquiv]
  exact hle

omit [IsAlgClosure k kbar] [Fintype Λ] in
/-- **`#H¹_c(X_k̄, ℱ_P) ≤ #H¹(X_k̄, ℱ_P)`, both finite**, for a permutation module `P = N[Γ/H]`,
`H` open normal, `#Λ` invertible in `k̄`. -/
theorem finite_and_natCard_compactSupportRepresentationHomology_one_le
    [Finite Λ] (hΛ : IsUnit (Nat.card Λ : kbar))
    (H : OpenSubgroup (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) [H.toSubgroup.Normal]
    (Q : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)) :
    Finite (((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 1).obj
        ((finiteTypeContinuousModuleCoind Λ H).obj
          ((finiteTypeContinuousModuleTrivial Λ _).obj Q))) ∧
      Finite (((geometricRepresentationCohomology.{u, 0} B X _ Λ f kbar).functor 1).obj
        ((finiteTypeContinuousModuleCoind Λ H).obj
          ((finiteTypeContinuousModuleTrivial Λ _).obj Q))) ∧
      Nat.card (((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 1).obj
        ((finiteTypeContinuousModuleCoind Λ H).obj
          ((finiteTypeContinuousModuleTrivial Λ _).obj Q))) ≤
      Nat.card (((geometricRepresentationCohomology.{u, 0} B X _ Λ f kbar).functor 1).obj
        ((finiteTypeContinuousModuleCoind Λ H).obj
          ((finiteTypeContinuousModuleTrivial Λ _).obj Q))) :=
  finite_and_natCard_compactSupportRepresentationHomology_one_le_of_addEquiv B X f kbar Λ y j hΛ
    H Q Λ Q (AddEquiv.refl _)

/-- **`T₁ = H¹_c(X_k̄, -)` is coeffaceable**, given the cohomological comparison
`H^i(π₁(X_k̄), -) ≅ H^i(X_k̄, ℱ_-)` over `Λᵐᵒᵖ`: every `M` has a coeffacement in degree one. -/
theorem coeffacement_compactSupportRepresentationHomology_zero
    (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
    (hcompOp : IsIso (geometricComparison B X Λᵐᵒᵖ f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar) y))
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    Nonempty ((compactSupportRepresentationHomology B X _ Λ f j kbar).Coeffacement M 0) := by
  have hK := contains_fieldBaseChange_of_isCurve B X f kbar
  let φ := geometricFundamentalGroupMap B X f kbar hK y
  let E := geometricGroupCohomology B X Λᵐᵒᵖ f kbar hK y
  let T := compactSupportRepresentationHomology B X
    (y.map (fieldBaseChangeObjProj B X f kbar hK).hom) Λ f j kbar
  let Hgh := restrictedHomologyDelta Λ φ
  have : E.ElementwiseEffaceable :=
    elementwiseEffaceable_restrictedCohomologyDelta Λᵐᵒᵖ φ
      (isInducing_geometricFundamentalGroupMap B X f kbar hK y)
  -- the open normal subgroup acting trivially and the permutation module
  obtain ⟨H₀, hH₀n, hH₀o, htriv⟩ :=
    exists_isOpen_normal_subgroup_ρ_eq_one_finiteType Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar hK).hom)) M
  let H : OpenSubgroup (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
    hK).hom)) := ⟨H₀, hH₀o⟩
  have : H.toSubgroup.Normal := hH₀n
  let Q : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ) := ⟨M.obj.obj.obj.V, M.property⟩
  let P := (finiteTypeContinuousModuleCoind Λ H).obj ((finiteTypeContinuousModuleTrivial Λ _).obj Q)
  let πM : P ⟶ M := finiteTypeContinuousModuleUntwistSum Λ H M htriv
  have : Epi πM := epi_finiteTypeContinuousModuleUntwistSum Λ H M htriv
  have : Module.Finite Λ Q.obj := Q.property
  have : Finite Q.obj := Module.finite_of_finite Λ
  obtain ⟨eQ⟩ := CharacterModule.nonempty_addEquiv Q.obj
  let P' := (finiteTypeContinuousModuleCoind Λᵐᵒᵖ H).obj
    ((finiteTypeContinuousModuleTrivial Λᵐᵒᵖ _).obj (dualCoefficient Λ Q))
  obtain ⟨hT1fin, hHet1fin, hle⟩ :=
    finite_and_natCard_compactSupportRepresentationHomology_one_le_of_addEquiv B X f kbar Λ y j
      (by rwa [Nat.card_eq_fintype_card]) H Q Λᵐᵒᵖ (dualCoefficient Λ Q) eQ
  -- `E¹(P^∨) ≅ E¹(P') ≅ H¹(X_k̄, ℱ_{P'})`
  have hbij := bijective_app_of_iso Λᵐᵒᵖ (asIso (geometricComparison B X Λᵐᵒᵖ f kbar hK y)) 1 P'
  let sd := finiteTypeContinuousModuleDualCoindTrivialIso Λ H Q
  let eE : (E.functor 1).obj ((finiteTypeContinuousModuleDual Λ _).obj (Opposite.op P)) ≅
      (E.functor 1).obj P' := (E.functor 1).mapIso sd
  have := hHet1fin
  have hE1P : Finite ((E.functor 1).obj P') := Finite.of_injective _ hbij.1
  have : Finite ((E.functor 1).obj ((finiteTypeContinuousModuleDual Λ _).obj (Opposite.op P))) :=
    Finite.of_injective _ (ConcreteCategory.bijective_of_isIso eE.hom).1
  -- coeffacing `P` for the homology `H` in degree one
  obtain ⟨I, ι, hι, hEι⟩ :=
    DeltaFunctor.ElementwiseEffaceable.exists_mono_map_eq_zero_of_finite (F := E)
      ((finiteTypeContinuousModuleDual Λ _).obj (Opposite.op P)) 0
  have := hι
  have : (finiteTypeContinuousModuleDualEquivalence Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar hK).hom))).functor.Additive :=
    finiteTypeContinuousModuleDual_additive Λ _
  let c := Stacks.CategoryHomology.HomologicalDeltaFunctor.coeffacementOfDual E
    (finiteTypeContinuousModuleDualEquivalence Λ _) P 0 ι hι hEι
  let S := ShortComplex.mk (kernel.ι c.π) c.π (kernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel S (kernelIsKernel c.π))
      (inferInstanceAs (Mono (kernel.ι c.π))) (inferInstanceAs (Epi c.π))
  have : Finite ((T.functor 1).obj P) := hT1fin
  -- the count
  have hcard : Nat.card ((T.functor 1).obj S.X₃) ≤
      Nat.card (LinearMap.ker ((T.functor 0).map S.f).hom) := by
    rw [natCard_ker_compactSupportRepresentationHomology_map_zero B X f kbar Λ y j hn S.f]
    have h0 : Nat.card (LinearMap.ker (geometricCoinvariantsMap B X f kbar Λ y S.f)) =
        Nat.card (LinearMap.ker ((Hgh.functor 0).map S.f).hom) :=
      (natCard_ker_eq_of_comp_eq ((Hgh.functor 0).map S.f).hom
        (geometricCoinvariantsMap B X f kbar Λ y S.f)
        ((restrictedHomologyZeroIso Λ φ).app S.X₁).toLinearEquiv
        ((restrictedHomologyZeroIso Λ φ).app S.X₂).toLinearEquiv
        (congrArg ModuleCat.Hom.hom ((restrictedHomologyZeroIso Λ φ).hom.naturality S.f)).symm).symm
    rw [h0, Stacks.CategoryHomology.HomologicalDeltaFunctor.natCard_ker_map_f_eq_of_map_g_eq_zero
      Hgh hS 0 c.map_π]
    change Nat.card ((T.functor 1).obj P) ≤
      Nat.card (CharacterModule ((E.functor 1).obj
        ((finiteTypeContinuousModuleDual Λ _).obj (Opposite.op P))))
    rw [CharacterModule.natCard_eq, Nat.card_congr eE.toLinearEquiv.toEquiv,
      Nat.card_congr (Equiv.ofBijective _ hbij)]
    exact hle
  have hT : (T.functor 1).map c.π = 0 :=
    Stacks.CategoryHomology.HomologicalDeltaFunctor.map_g_eq_zero_of_natCard_le T hS 0 hcard
  exact ⟨⟨c.P, c.π ≫ πM, by rw [Functor.map_comp, hT, zero_comp]⟩⟩

end AlgebraicGeometry

end
