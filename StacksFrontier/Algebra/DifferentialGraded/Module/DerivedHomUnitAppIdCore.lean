module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCohomologyBridge
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCohomologyCocycle
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoreLHSFactors
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoreLHSMid
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoreRHSSeam
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomForgetRecovery
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomUnitAppId

/-!
# The one equation [Stacks, Tag 09LK] still owed, proved

`DGCategory.derivedHomPhiQh_phiReflectorBeta_app_eq_iff` reduced the clause `unit_app_id` of
step 3 of the replacement proof of [Stacks, Tag 09LK], at the canonical comparison
`DGCategory.phiReflectorBeta`, to a single equation between two morphisms

`q K ⟶ (q (Φ' Y))⟦n⟧`

of `D(A)`, in which neither `β` nor the comparison `ν` nor the transported `(*)` occurs. This
file proves that equation, and with it `unit_app_id` at the canonical `β` unconditionally:
nothing is assumed beyond Tag 09LK's own data — the reflector of steps 1 and 2 and, for the three
conclusions at the end, Tag 09LK's own derivability hypothesis `h`. No smallness, no universe
inequality, no K-injective resolution and no derivability of the `D(E)`-valued `Hom(K, -)`
enters.

## The three steps

**(1) Identify the class.** `CochainComplex.coreLHS_eq` says that the left-hand side of step 3's
equation — the comparison `ν⁻¹` followed by the identification
`DGCategory.RightModule.endDerivedForgetGradedCohomologyIso` of the cohomology of the forgetful
image with the explicit cohomology — *is* the identification
`CochainComplex.homologyGradedCohomologyIso` that [Tag 09LC] is stated against, read across the
degreewise bridge `CochainComplex.homYonedaCohomologyEquiv`. Its content is
`CochainComplex.coreLHS_step2` together with
`CochainComplex.homologyMap_homEvaluationComparisonIso_gradedCohomologyIso`, the intertwining of
the two explicit cohomologies: `HomologicalComplex.homologyπ` is epi, the two
`homologyπ_gradedCohomologyIso_hom` reduce it to the cycles, the two
`HomologicalComplex.cyclesIsoSc'` are pinned by
`DGCategory.RightModule.gradedCyclesIso_hom_val` and
`DifferentialGradedModule.gradedCyclesIso_hom_subtype`, and the residue is the agreement of
`CochainComplex.homEvaluationComparisonIso_hom_app_f_apply` with
`CochainComplex.homYonedaCocyclesEquiv_coe` — both of them `CochainComplex.homGradingEquiv`.

**(2) Strip links 4 and 2.** `DGCategory.RightModule.chainEquivReflectorEvaluation_eq_of_link1`
already does this: the chain of steps 1 and 2 carries the class the *first* link assigns to
`h_f ≫ σ_n ≫ η⟦n⟧` to `q(f)`, unconditionally and with no inverse expanded. No compatibility of
`η` with the `CommShift` of the localization is used.

**(3) The elementwise step.** `CochainComplex.coreRHS_mk_homCocycles` computes the first link on
the differential graded Yoneda image of the morphism `K ⟶ Y⟦n⟧` that [Tag 09LC] attaches to a
cocycle: it is the class of that cocycle. A cohomology class is reduced to a cocycle
representative only here.

What is left is bookkeeping in `D(A)`, and `DGCategory.phi_map_comp_commShiftIso` is all of it:
the image under `q = Φ'⁻¹ ⋙ Q` of `Φ'(h) ≫ σ_{Φ'}` is `Q(h) ≫ σ_Q` conjugated by the unit of the
comparison equivalence. The only inputs are the naturality of that unit and its compatibility
with the translation, which `CochainComplex.homotopyCategoryEquivalence_commShift` supplies.

*The sign.* The `(-1)^n` of `DGCategory.ShiftAxiomBIso.symm_toShift_d` is matched, not cancelled:
`DGCategory.RightModule.shift_d` puts `(-1)^n` on the differential of `M⟦n⟧` too, so closedness
is literally "`(-1)^n` times a differential vanishes" and the sign stands on both sides of one
equation. It never reaches the value.

## Main results

* `CochainComplex.homologyMap_homEvaluationComparisonIso_gradedCohomologyIso`: the degreewise
  comparison of the two constructions of `Hom^•(K, Y)` intertwines the two explicit cohomologies.
* `CochainComplex.coreLHS_eq`: **the left-hand side is [Tag 09LC]'s identification.**
* `CochainComplex.coreRHS_mk_homCocycles`: **the right-hand side at a cocycle representative.**
* `DGCategory.phi_map_comp_commShiftIso`: the seam in `D(A)`.
* `DGCategory.chainEquivReflectorEvaluation_gradedCohomologyMapK_eq`: **the equation**, at the
  homotopy class of a complex.
* `DGCategory.derivedHomPhiQh_phiReflectorBeta_app_eq`: **`unit_app_id` at the canonical `β`,
  unconditionally.**
* `DGCategory.isIso_derivedHomForgetComparison_phiReflectorBeta`,
  `DGCategory.derivedHomForgetPhiReflectorBetaIso` and
  `DGCategory.isRightDerivedFunctor_phiReflectorForget_phiReflectorBeta`: **step 3 of
  [Stacks, Tag 09LK] at the canonical `β`** — the canonical comparison
  `θ : R Hom(K, -) ⟶ R̃ ⋙ U` is an isomorphism, with `unit_app_id` no longer a hypothesis.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose step 3 this
  completes; [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the identification of a
  degree-`n` cohomology class of a Hom complex with a morphism of the homotopy category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.ObjectProperty

universe w v

/-- `a ≫ r = a' ≫ r`. Every object is a variable, so `exact`ing this matches a composite whose
objects are large semireducible terms at default transparency and unfolds nothing. -/
private theorem CategoryTheory.coreLHSEq_comp_left {D : Type*} [Category D] {X Y Z : D}
    {a a' : X ⟶ Y} (r : Y ⟶ Z) (h : a = a') : a ≫ r = a' ≫ r := by rw [h]

/-- `a ≫ b = a ≫ b'`, with every object a variable. -/
private theorem CategoryTheory.coreLHSEq_comp_right {D : Type*} [Category D] {X Y Z : D}
    (a : X ⟶ Y) {b b' : Y ⟶ Z} (h : b = b') : a ≫ b = a ≫ b' := by rw [h]

/-- `a ≫ u ≫ r = a ≫ u' ≫ r`, with every object a variable. -/
private theorem CategoryTheory.coreLHSEq_comp_mid {D : Type*} [Category D] {X Y Z W : D}
    (a : X ⟶ Y) {u u' : Y ⟶ Z} (r : Z ⟶ W) (h : u = u') : a ≫ u ≫ r = a ≫ u' ≫ r := by rw [h]

/-- **The rearrangement of step 3's two sides.** Given a square `d ≫ p = p' ≫ hm` — the
naturality of the factorization of cohomology — and an intertwining `hm ≫ g = q ≫ e`, the two
composites agree. Every object and morphism is a variable, so this is pure category theory and
applies by `exact` without unfolding anything. -/
private theorem CategoryTheory.coreLHSEq_assemble {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ : D} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄)
    (p : X₄ ⟶ X₅) (g : X₅ ⟶ X₆) (p' : X₃ ⟶ X₇) (hm : X₇ ⟶ X₅) (q : X₇ ⟶ X₈) (e : X₈ ⟶ X₆)
    (hnat : d ≫ p = p' ≫ hm) (hbr : hm ≫ g = q ≫ e) :
    (a ≫ b ≫ c) ≫ d ≫ p ≫ g = (a ≫ (b ≫ c ≫ p') ≫ q) ≫ e := by
  simp only [Category.assoc]
  rw [← Category.assoc d p g, hnat, Category.assoc, hbr]

/-- **The assembly of the intertwining of the two cohomologies.** Given the naturality `π ≫ m =
cm ≫ π₁`, the two factorizations through the cycles, the square `ec ≫ q₁ = q₂ ≫ e` of quotient
maps and the cycle-level square `cm ≫ c₁ = c₂ ≫ ec`, one has `π ≫ m ≫ G = π ≫ G' ≫ e`. -/
private theorem CategoryTheory.coreLHSEq_cancel_square {D : Type*} [Category D]
    {P H H₁ C₁ T Z T' Z' : D} (π : P ⟶ H) (m : H ⟶ H₁) (cm : P ⟶ C₁) (π₁ : C₁ ⟶ H₁)
    (G : H₁ ⟶ T) (c₁ : C₁ ⟶ Z) (q₁ : Z ⟶ T) (G' : H ⟶ T') (c₂ : P ⟶ Z') (q₂ : Z' ⟶ T')
    (e : T' ⟶ T) (ec : Z' ⟶ Z) (hπ : π ≫ m = cm ≫ π₁) (h₁ : π₁ ≫ G = c₁ ≫ q₁)
    (h₂ : π ≫ G' = c₂ ≫ q₂) (hq : ec ≫ q₁ = q₂ ≫ e) (hc : cm ≫ c₁ = c₂ ≫ ec) :
    π ≫ m ≫ G = π ≫ G' ≫ e := by
  rw [← Category.assoc, hπ, Category.assoc, h₁, ← Category.assoc, hc, Category.assoc, hq,
    ← Category.assoc, ← Category.assoc, h₂]

namespace CochainComplex

variable (A : Type) [Category.{0} A] [Preadditive A] (K : CochainComplex A ℤ)
  [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **The comparison intertwines the two identifications of the cycles.** The degreewise
comparison of the two readings of `Hom^•(K, Y)` carries the identification of the cycles of
`Hom^•(K, Y)` with its explicit cocycles to the identification of the cycles of `ev_K(h_Y)` with
the explicit cocycles of the Yoneda right module, the two being matched by
`CochainComplex.homYonedaCocyclesEquiv`.

Both underlying cochains are `CochainComplex.homGradingEquiv` of the underlying element of the
cycle: on the left by `DGCategory.RightModule.gradedCyclesIso_hom_val` and
`HomologicalComplex.cyclesMap_i`, on the right by
`DifferentialGradedModule.gradedCyclesIso_hom_subtype` and
`CochainComplex.homYonedaCocyclesEquiv_coe`. -/
private theorem cyclesMap_homEvaluationComparisonIso_gradedCyclesIso (n : ℤ)
    (Y : CochainComplex A ℤ) :
    HomologicalComplex.cyclesMap ((homEvaluationComparisonIso A K).hom.app Y) n ≫
        (DGCategory.RightModule.gradedCyclesIso
          (DGCategory.yonedaRightModule (dgCategory A) Y) K n).hom =
      (DifferentialGradedModule.gradedCyclesIso
          (DGCategory.representableModule (dgCategory A) K Y) n).hom ≫
        ModuleCat.ofHom (homYonedaCocyclesEquiv A K Y n).toIntLinearEquiv.toLinearMap := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => Subtype.ext ?_)
  have h1 := DGCategory.RightModule.gradedCyclesIso_hom_val
    (DGCategory.yonedaRightModule (dgCategory A) Y) K n
    ((HomologicalComplex.cyclesMap ((homEvaluationComparisonIso A K).hom.app Y) n).hom z)
  have h2 := ConcreteCategory.congr_hom (C := ModuleCat.{0} ℤ)
    (HomologicalComplex.cyclesMap_i ((homEvaluationComparisonIso A K).hom.app Y) n) z
  have h3 := ConcreteCategory.congr_hom (C := ModuleCat.{0} ℤ)
    (DifferentialGradedModule.gradedCyclesIso_hom_subtype
      (DGCategory.representableModule (dgCategory A) K Y) n) z
  exact h1.trans (h2.trans (congrArg (fun x => homGradingEquiv A K Y n x) h3).symm)

/-- **The owed `gradedCohomologyIso` intertwining.** The degreewise comparison of the two
constructions of `Hom^•(K, Y)` carries the explicit degree-`n` cohomology of the representable
differential graded `End(K)`-module to the explicit degree-`n` cohomology of the differential
graded Yoneda module of `Y` at `K`, along the bridge
`CochainComplex.homYonedaCohomologyEquiv`.

`HomologicalComplex.homologyπ` is epi, so this follows from the cycles-level statement
`CochainComplex.cyclesMap_homEvaluationComparisonIso_gradedCyclesIso` together with
`DGCategory.RightModule.homologyπ_gradedCohomologyIso_hom'`,
`DifferentialGradedModule.homologyπ_gradedCohomologyIso_hom` and
`HomologicalComplex.homologyπ_naturality`; the two quotient maps are matched by
`CochainComplex.homYonedaCohomologyEquiv_mk`, which is a reflexivity. -/
theorem homologyMap_homEvaluationComparisonIso_gradedCohomologyIso (n : ℤ)
    (Y : CochainComplex A ℤ) :
    HomologicalComplex.homologyMap ((homEvaluationComparisonIso A K).hom.app Y) n ≫
        (DGCategory.RightModule.gradedCohomologyIso
          (DGCategory.yonedaRightModule (dgCategory A) Y) K n).hom =
      (DifferentialGradedModule.gradedCohomologyIso
          (DGCategory.representableModule (dgCategory A) K Y) n).hom ≫
        ModuleCat.ofHom (homYonedaCohomologyEquiv A K Y n).toIntLinearEquiv.toLinearMap := by
  refine (cancel_epi (((homModuleComplexFunctor A K).obj Y).homologyπ n)).1 ?_
  have hquot : ModuleCat.ofHom (homYonedaCocyclesEquiv A K Y n).toIntLinearEquiv.toLinearMap ≫
        ModuleCat.ofHom (DGCategory.RightModule.gradedBoundaries
          (DGCategory.yonedaRightModule (dgCategory A) Y) K n).mkQ =
      ModuleCat.ofHom
          ((DGCategory.representableModule (dgCategory A) K Y).gradedCoboundaries n).mkQ ≫
        ModuleCat.ofHom (homYonedaCohomologyEquiv A K Y n).toIntLinearEquiv.toLinearMap :=
    ModuleCat.hom_ext (LinearMap.ext fun z => rfl)
  refine coreLHSEq_cancel_square _ _ _ (((homEvaluationComplexFunctor A K).obj Y).homologyπ n)
    _ _ _ _ _ _ _ _ ?_ ?_ ?_ hquot
    (cyclesMap_homEvaluationComparisonIso_gradedCyclesIso A K n Y)
  · exact HomologicalComplex.homologyπ_naturality
      ((homEvaluationComparisonIso A K).hom.app Y) n
  · exact DGCategory.RightModule.homologyπ_gradedCohomologyIso_hom'
      (DGCategory.yonedaRightModule (dgCategory A) Y) K n
  · exact DifferentialGradedModule.homologyπ_gradedCohomologyIso_hom
      (DGCategory.representableModule (dgCategory A) K Y) n

/-- **The left-hand side of step 3's equation is [Tag 09LC]'s identification.** The comparison
`ν⁻¹` of step 3, followed by the identification of the cohomology of the forgetful image with the
explicit cohomology, *is* `CochainComplex.homologyGradedCohomologyIso` read across the degreewise
bridge `CochainComplex.homYonedaCohomologyEquiv`. -/
theorem coreLHS_eq (n : ℤ) (Y : CochainComplex A ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((homDerivedLiftForgetIso A K).inv.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) ≫
        (DGCategory.RightModule.endDerivedForgetGradedCohomologyIso (dgCategory A) K
          ((yonedaHomotopyFunctor A).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) PUnit.unit n).hom =
      (homologyGradedCohomologyIso A K n).hom.app Y ≫
        ModuleCat.ofHom (homYonedaCohomologyEquiv A K Y n).toIntLinearEquiv.toLinearMap := by
  -- The forgetful square of the Hom representation, as three factors, with its innermost one
  -- identified with the quotient comparison of the two routes to the homotopy category.
  have hFS0 : ((DGCategory.homRepresentation (dgCategory A) K).forgetSquareIso).hom.app Y =
      (DifferentialGradedModule.derivedForget (endAlgebra A K)).map
          ((DifferentialGradedModule.quasiIsomorphisms' (endAlgebra A K)).Q.map
            ((homHomotopyFunctorQuotientIso A K).hom.app Y)) ≫
        (DifferentialGradedModule.derivedForgetFactorization (endAlgebra A K)).hom.app
            ((DifferentialGradedModule.toHomotopyCategory (endAlgebra A K)).obj
              ((homComplexesFunctor A K).obj Y)) ≫
          (DifferentialGradedModule.forgetHomotopyToDerivedCategoryIso (endAlgebra A K)).hom.app
            ((homComplexesFunctor A K).obj Y) :=
    (forgetSquareIso_hom_app A K Y).trans
      (coreLHSEq_comp_left _ (congrArg (DifferentialGradedModule.derivedForget (endAlgebra A K)).map
        (congrArg (DifferentialGradedModule.quasiIsomorphisms' (endAlgebra A K)).Q.map
          (complexesQuotientSquareIso_inv_app_onComp A K Y))))
  -- `H^n` of it, with the first factor read as the composite functor the right-hand side uses.
  have hFS : (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        (((DGCategory.homRepresentation (dgCategory A) K).forgetSquareIso).hom.app Y) =
      ((DifferentialGradedModule.quasiIsomorphisms' (endAlgebra A K)).Q ⋙
            DifferentialGradedModule.derivedForget (endAlgebra A K) ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((homHomotopyFunctorQuotientIso A K).hom.app Y) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((DifferentialGradedModule.derivedForgetFactorization (endAlgebra A K)).hom.app
              ((DifferentialGradedModule.toHomotopyCategory (endAlgebra A K)).obj
                ((homComplexesFunctor A K).obj Y))) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((DifferentialGradedModule.forgetHomotopyToDerivedCategoryIso (endAlgebra A K)).hom.app
              ((homComplexesFunctor A K).obj Y)) :=
    (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map hFS0).trans
      (((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map_comp _ _).trans
        (coreLHSEq_comp_right _
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map_comp _ _)))
  -- Tag 09LC's identification, as the same three factors followed by two more.
  have hRHS : (homologyGradedCohomologyIso A K n).hom.app Y =
      ((DifferentialGradedModule.quasiIsomorphisms' (endAlgebra A K)).Q ⋙
            DifferentialGradedModule.derivedForget (endAlgebra A K) ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((homHomotopyFunctorQuotientIso A K).hom.app Y) ≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
              ((DifferentialGradedModule.derivedForgetFactorization (endAlgebra A K)).hom.app
                ((DifferentialGradedModule.toHomotopyCategory (endAlgebra A K)).obj
                  ((homComplexesFunctor A K).obj Y))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
                ((DifferentialGradedModule.forgetHomotopyToDerivedCategoryIso
                  (endAlgebra A K)).hom.app
                  ((homComplexesFunctor A K).obj Y)) ≫
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℤ) n).hom.app
                ((DifferentialGradedModule.forgetToCochainComplex (endAlgebra A K)).obj
                  ((homComplexesFunctor A K).obj Y))) ≫
          (DifferentialGradedModule.gradedCohomologyFunctorIso (endAlgebra A K) n).hom.app
            ((homComplexesFunctor A K).obj Y) :=
    (homologyGradedCohomologyIso_hom_app A K n Y).trans
      (coreLHSEq_comp_mid _ _
        (DifferentialGradedModule.derivedForgetHomologyIso_hom_app (endAlgebra A K) n
          ((homComplexesFunctor A K).obj Y)))
  -- The naturality of the factorization of cohomology, at the degreewise comparison.
  have hnat : (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          (DerivedCategory.Q.map ((homEvaluationComparisonIso A K).hom.app Y)) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℤ) n).hom.app
          ((homEvaluationComplexFunctor A K).obj Y) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℤ) n).hom.app
          ((DifferentialGradedModule.forgetToCochainComplex (endAlgebra A K)).obj
            ((homComplexesFunctor A K).obj Y)) ≫
        HomologicalComplex.homologyMap ((homEvaluationComparisonIso A K).hom.app Y) n :=
    DerivedCategory.homologyFunctorFactors_hom_naturality _ n
  -- The intertwining, in the two spellings the two sides use.
  have hbr : HomologicalComplex.homologyMap ((homEvaluationComparisonIso A K).hom.app Y) n ≫
        (DGCategory.RightModule.gradedCohomologyIso
          ((DGCategory.evaluationOnK (dgCategory A) K).obj
            ((yonedaHomotopyFunctor A).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y))) PUnit.unit n).hom =
      (DifferentialGradedModule.gradedCohomologyFunctorIso (endAlgebra A K) n).hom.app
          ((homComplexesFunctor A K).obj Y) ≫
        ModuleCat.ofHom (homYonedaCohomologyEquiv A K Y n).toIntLinearEquiv.toLinearMap :=
    homologyMap_homEvaluationComparisonIso_gradedCohomologyIso A K n Y
  refine (coreLHS_step2 A K n Y).trans ?_
  refine Eq.trans (coreLHSEq_comp_left _ hFS) ?_
  refine Eq.trans ?_ (congrArg (fun t => t ≫ ModuleCat.ofHom
    (homYonedaCohomologyEquiv A K Y n).toIntLinearEquiv.toLinearMap) hRHS).symm
  exact coreLHSEq_assemble _ _ _ _ _ _ _ _ _ _ hnat hbr

/-- The hypothesis `hc` of `CochainComplex.coreRHS_mk`, for a cocycle of the Yoneda right module
presented in degree `j` rather than in degree `0 + n`. The degree equation is an argument, so
that the reindexing of `DGCategory.RightModule.gradedCocyclesShiftEquiv'` can be substituted
away; after the substitution both sides are the same right shift of the same cochain. -/
private theorem hc_rightShift (n : ℤ) (Y : CochainComplex A ℤ) {j : ℤ} (h : 0 + n = j)
    (a : ↥(DGCategory.RightModule.gradedCocycles
      (DGCategory.yonedaRightModule (dgCategory A) Y) K j))
    (γ : (dgCategory A).Hom K (((dgShiftAxiomBIso A).shiftFunctor n).obj Y) 0)
    (hγ : γ = HomComplex.Cochain.rightShift
      (a.1 : HomComplex.Cochain K Y j) n 0 h) :
    (dgShiftAxiomBIso A).toShift n K Y 0
        ((DGCategory.RightModule.gradedCocyclesShiftEquiv'
          (DGCategory.yonedaRightModule (dgCategory A) Y) n K h).symm a).1 = γ := by
  subst h
  subst hγ
  rfl

/-- The right-hand side of step 3's equation at a cocycle representative. -/
theorem coreRHS_mk_homCocycles (n : ℤ) (Y : CochainComplex A ℤ)
    (e : (DGCategory.endDGCategory (dgCategory A) K).Obj)
    (z : ↥((DGCategory.representableModule (dgCategory A) K Y).gradedCocycles n)) :
    DGCategory.RightModule.homShiftEquivEvaluationGradedCohomology
        ((yonedaHomotopyFunctor A).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) K e n
        ((yonedaHomotopyFunctor A).map
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                (HomComplex.Cocycle.equivHomShift.symm (homCocyclesEquiv A K Y n z)) ≫
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso
                (A := ℤ) n).hom.app Y) ≫
          ((yonedaHomotopyFunctor A).commShiftIso n).hom.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) =
      Submodule.Quotient.mk (homYonedaCocyclesEquiv A K Y n z) := by
  refine Eq.trans (coreRHS_mk A K n _ e _ _
    ((DGCategory.RightModule.gradedCocyclesShiftEquiv'
      (DGCategory.yonedaRightModule (dgCategory A) Y) n K (zero_add n)).symm
        (homYonedaCocyclesEquiv A K Y n z))
    (map_comp_commShiftIso_mk A K n Y _) ?_)
    (congrArg Submodule.Quotient.mk (LinearEquiv.apply_symm_apply _ _))
  refine hc_rightShift A K n Y (zero_add n) (homYonedaCocyclesEquiv A K Y n z) _ ?_
  have hσ : ((cochainToComplexFunctor A).commShiftIso n).hom.app Y = 𝟙 _ := by
    simp only [Functor.commShiftIso_eq_ofInduced, Iso.symm_hom, eqToIso.inv, eqToHom_app]
    rfl
  rw [hσ]
  refine Eq.trans ((dgCategory A).id_comp _) ?_
  rw [HomComplex.Cocycle.equivHomShift_symm_apply]
  exact congrArg Subtype.val (HomComplex.Cocycle.ofHom_homOf_eq_self _)

end CochainComplex

namespace DGCategory

variable (A : Type) [Category.{0} A] [Abelian A] [HasDerivedCategory.{v} A]

theorem unitIso_hom_app_shift (n : ℤ) (Y : HomotopyCategory A (ComplexShape.up ℤ)) :
    (shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) n).map
        ((CochainComplex.homotopyCategoryEquivalence A).unitIso.hom.app Y) =
      (CochainComplex.homotopyCategoryEquivalence A).unitIso.hom.app
          ((shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) n).obj Y) ≫
        ((((CochainComplex.homotopyCategoryEquivalence A).functor ⋙
          (CochainComplex.homotopyCategoryEquivalence A).inverse).commShiftIso n)).hom.app Y := by
  simpa using NatTrans.shift_app_comm
    (CochainComplex.homotopyCategoryEquivalence A).unitIso.hom n Y

theorem functor_comp_inverse_map_comp_commShiftIso (n : ℤ)
    (X Y : HomotopyCategory A (ComplexShape.up ℤ)) (h : X ⟶ Y⟦n⟧) :
    ((CochainComplex.homotopyCategoryEquivalence A).functor ⋙
          (CochainComplex.homotopyCategoryEquivalence A).inverse).map h ≫
        ((((CochainComplex.homotopyCategoryEquivalence A).functor ⋙
          (CochainComplex.homotopyCategoryEquivalence A).inverse).commShiftIso n)).hom.app Y =
      (CochainComplex.homotopyCategoryEquivalence A).unitIso.inv.app X ≫ h ≫
        (shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) n).map
          ((CochainComplex.homotopyCategoryEquivalence A).unitIso.hom.app Y) := by
  have hnat : h ≫ (CochainComplex.homotopyCategoryEquivalence A).unitIso.hom.app
        ((shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) n).obj Y) =
      (CochainComplex.homotopyCategoryEquivalence A).unitIso.hom.app X ≫
        ((CochainComplex.homotopyCategoryEquivalence A).functor ⋙
          (CochainComplex.homotopyCategoryEquivalence A).inverse).map h :=
    (CochainComplex.homotopyCategoryEquivalence A).unitIso.hom.naturality h
  rw [unitIso_hom_app_shift, ← Category.assoc h, hnat, Category.assoc,
    Iso.inv_hom_id_app_assoc]

/-- PIECE A: the seam in `D(A)`. -/
theorem phi_map_comp_commShiftIso (n : ℤ) (X Y : HomotopyCategory A (ComplexShape.up ℤ))
    (h : X ⟶ Y⟦n⟧) :
    (phiComparisonLocalization A).map
          ((CochainComplex.homotopyCategoryEquivalence A).functor.map h ≫
            ((CochainComplex.homotopyCategoryEquivalence A).functor.commShiftIso n).hom.app Y) ≫
        ((phiComparisonLocalization A).commShiftIso n).hom.app
          ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y) =
      (phiUnitIso A X).inv ≫
        (DerivedCategory.Qh.map h ≫ (DerivedCategory.Qh.commShiftIso n).hom.app Y) ≫
          (shiftFunctor (DerivedCategory A) n).map (phiUnitIso A Y).hom := by
  have hin : (CochainComplex.homotopyCategoryEquivalence A).inverse.map
          ((CochainComplex.homotopyCategoryEquivalence A).functor.map h ≫
            ((CochainComplex.homotopyCategoryEquivalence A).functor.commShiftIso n).hom.app Y) ≫
        (((CochainComplex.homotopyCategoryEquivalence A).inverse.commShiftIso n)).hom.app
          ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y) =
      (CochainComplex.homotopyCategoryEquivalence A).unitIso.inv.app X ≫ h ≫
        (shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) n).map
          ((CochainComplex.homotopyCategoryEquivalence A).unitIso.hom.app Y) := by
    rw [Functor.map_comp, Category.assoc, ← Functor.commShiftIso_comp_hom_app]
    exact functor_comp_inverse_map_comp_commShiftIso A n X Y h
  have hq : DerivedCategory.Qh.map
          ((shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) n).map
            ((CochainComplex.homotopyCategoryEquivalence A).unitIso.hom.app Y)) ≫
        (DerivedCategory.Qh.commShiftIso n).hom.app
          ((CochainComplex.homotopyCategoryEquivalence A).inverse.obj
            ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y)) =
      (DerivedCategory.Qh.commShiftIso n).hom.app Y ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Qh.map
          ((CochainComplex.homotopyCategoryEquivalence A).unitIso.hom.app Y)) :=
    DerivedCategory.Qh.commShiftIso_hom_naturality _ n
  rw [Functor.commShiftIso_comp_hom_app]
  rw [show (phiComparisonLocalization A).map
        ((CochainComplex.homotopyCategoryEquivalence A).functor.map h ≫
          ((CochainComplex.homotopyCategoryEquivalence A).functor.commShiftIso n).hom.app Y) =
      DerivedCategory.Qh.map ((CochainComplex.homotopyCategoryEquivalence A).inverse.map
        ((CochainComplex.homotopyCategoryEquivalence A).functor.map h ≫
          ((CochainComplex.homotopyCategoryEquivalence A).functor.commShiftIso n).hom.app Y))
      from rfl]
  rw [← Functor.map_comp_assoc, hin, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, hq, phiUnitIso, phiUnitIso, Functor.mapIso_inv, Functor.mapIso_hom,
    Iso.app_inv, Iso.app_hom, Category.assoc]

section Main

variable (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  (L : (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K ⥤
    (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K)
  [L.CommShift ℤ] [L.IsTriangulated]
  (η : 𝟭 (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K ⟶ L)

attribute [local implicit_reducible] DGCategory.K

variable
  (hL : ∀ X, (RightModule.yonedaLocalizing (CochainComplex.dgCategory A) (phiGen A)).rightOrthogonal
    (L.obj X))
  (hη : ∀ (X Z : (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K) (f : Z ⟶ X)
      (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
    Triangle.mk f (η.app X) g ∈
        distTriang (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K →
      RightModule.yonedaLocalizing (CochainComplex.dgCategory A) (phiGen A) Z)
  (hΦ : ∀ X, RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A) X →
    IsZero (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK ⋙ L).obj X))




/-- **The equation, at the homotopy class of a complex.** -/
theorem chainEquivReflectorEvaluation_gradedCohomologyMapK_eq (Y : CochainComplex A ℤ) (n : ℤ)
    (x : ↥((CochainComplex.homToDerivedCategoryForget A K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y))) :
    RightModule.chainEquivReflectorEvaluation (CochainComplex.dgCategory A) (phiGen A) hL hη
        (phiComparisonLocalization A) (K : (CochainComplex.dgCategory A).K)
        ((CochainComplex.homotopyCategoryEquivalence A).functor.obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) PUnit.unit n
        (RightModule.gradedCohomologyMapK
          ((evaluationOnK (CochainComplex.dgCategory A) K).map
            (η.app (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).obj
              ((CochainComplex.homotopyCategoryEquivalence A).functor.obj
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)))))
          PUnit.unit n
          ((RightModule.endDerivedForgetGradedCohomologyIso (CochainComplex.dgCategory A) K
              (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).obj
                ((CochainComplex.homotopyCategoryEquivalence A).functor.obj
                  ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)))
              PUnit.unit n).hom
            ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
              ((CochainComplex.homDerivedLiftForgetIso A K).inv.app
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) x))) =
      (phiSourceIso A K).inv ≫
        (DerivedCategory.Qh.map (CochainComplex.homologyHomAddEquiv A K n
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y) x) ≫
            (DerivedCategory.Qh.commShiftIso n).hom.app
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) ≫
          (shiftFunctor (DerivedCategory A) n).map
            (phiUnitIso A ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)).hom := by
  obtain ⟨z, hz⟩ := CochainComplex.exists_gradedCocycles_repr A K n Y x
  have h09 : CochainComplex.homologyHomAddEquiv A K n
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y) x =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
            (CochainComplex.homCocyclesEquiv A K Y n z)) ≫
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso (A := ℤ) n).hom.app Y :=
    CochainComplex.homologyHomAddEquiv_quotient_obj_apply_mk A K n Y x z hz
  have hclass : (RightModule.endDerivedForgetGradedCohomologyIso (CochainComplex.dgCategory A) K
          (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).obj
            ((CochainComplex.homotopyCategoryEquivalence A).functor.obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)))
          PUnit.unit n).hom
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((CochainComplex.homDerivedLiftForgetIso A K).inv.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) x) =
      Submodule.Quotient.mk (CochainComplex.homYonedaCocyclesEquiv A K Y n z) := by
    refine Eq.trans (ConcreteCategory.congr_hom (C := ModuleCat.{0} ℤ)
      (CochainComplex.coreLHS_eq A K n Y) x) ?_
    exact congrArg (CochainComplex.homYonedaCohomologyEquiv A K Y n) hz
  have hsrc : (phiSourceIso A K).inv =
      (phiUnitIso A ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).inv := by
    have hid : DerivedCategory.Qh.map ((CochainComplex.homotopyCategoryEquivalence A).inverse.map
          (eqToHom (CochainComplex.homotopyCategoryEquivalence_obj A K).symm)) = 𝟙 _ :=
      (congrArg (fun t => DerivedCategory.Qh.map
            ((CochainComplex.homotopyCategoryEquivalence A).inverse.map t))
          (eqToHom_refl _ _)).trans
        ((congrArg DerivedCategory.Qh.map
            ((CochainComplex.homotopyCategoryEquivalence A).inverse.map_id _)).trans
          (DerivedCategory.Qh.map_id _))
    rw [phiSourceIso, Iso.trans_inv, Functor.mapIso_inv, Functor.mapIso_inv, eqToIso.inv, hid]
    exact Category.id_comp _
  refine (RightModule.chainEquivReflectorEvaluation_eq_of_link1
    (CochainComplex.dgCategory A) (phiGen A) hL hη (phiComparisonLocalization A)
    (K : (CochainComplex.dgCategory A).K)
    ((CochainComplex.homotopyCategoryEquivalence A).functor.obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) PUnit.unit n _
    ((CochainComplex.homotopyCategoryEquivalence A).functor.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
            (CochainComplex.homCocyclesEquiv A K Y n z)) ≫
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso (A := ℤ) n).hom.app Y) ≫
      ((CochainComplex.homotopyCategoryEquivalence A).functor.commShiftIso n).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) ?_).trans ?_
  · have hb : RightModule.homShiftEquivEvaluationGradedCohomology _
          ((CochainComplex.homotopyCategoryEquivalence A).functor.obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) :
              (CochainComplex.dgCategory A).Obj)
          PUnit.unit n
          (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).map
              ((CochainComplex.homotopyCategoryEquivalence A).functor.map
                  ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                    (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
                      (CochainComplex.homCocyclesEquiv A K Y n z)) ≫
                    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso
                      (A := ℤ) n).hom.app Y) ≫
                ((CochainComplex.homotopyCategoryEquivalence A).functor.commShiftIso n).hom.app
                  ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) ≫
            (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).commShiftIso n).hom.app
              ((CochainComplex.homotopyCategoryEquivalence A).functor.obj
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y))) =
        (RightModule.endDerivedForgetGradedCohomologyIso (CochainComplex.dgCategory A) K
            (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).obj
              ((CochainComplex.homotopyCategoryEquivalence A).functor.obj
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)))
            PUnit.unit n).hom
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((CochainComplex.homDerivedLiftForgetIso A K).inv.app
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) x) := by
      refine Eq.trans ?_ hclass.symm
      refine Eq.trans ?_ (CochainComplex.coreRHS_mk_homCocycles A K n Y PUnit.unit z)
      exact congrArg (RightModule.homShiftEquivEvaluationGradedCohomology _ _ PUnit.unit n)
        (CochainComplex.yonedaHomotopyFunctor_map_comp_commShiftIso A K n _ _).symm
    exact Eq.symm ((Equiv.symm_apply_eq _).1
      ((RightModule.homShiftEquivEvaluationGradedCohomology_symm_evaluationOnK_mapK
            (η.app (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).obj
              ((CochainComplex.homotopyCategoryEquivalence A).functor.obj
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)))) _ PUnit.unit n _).trans
        (congrArg (· ≫ _) ((Equiv.symm_apply_eq _).2 hb.symm))))
  · rw [h09]
    refine Eq.trans (phi_map_comp_commShiftIso A n _ _ _) ?_
    exact congrArg (· ≫ _) hsrc.symm

/-- **`unit_app_id` at the canonical `β`.** -/
theorem derivedHomPhiQh_phiReflectorBeta_app_eq (Y : HomotopyCategory A (ComplexShape.up ℤ))
    (n : ℤ) (x : ↥((CochainComplex.homToDerivedCategoryForget A K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj Y)) :
    derivedHomPhiQh A K L hL hη hΦ Y n
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((phiReflectorBeta A K L η hΦ).app Y) x) =
      DerivedCategory.Qh.map (CochainComplex.homologyHomAddEquiv A K n Y x) ≫
        (DerivedCategory.Qh.commShiftIso n).hom.app Y := by
  rw [derivedHomPhiQh_phiReflectorBeta_app_eq_iff]
  obtain ⟨Y₀⟩ := Y
  exact chainEquivReflectorEvaluation_gradedCohomologyMapK_eq A K L η hL hη Y₀ n x

variable (h : (CochainComplex.homToDerivedCategoryForget A K).IsRightDerivable
  (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))

include hL hη in
/-- **Step 3 of 09LK at the canonical `β`, with nothing owed.** -/
theorem isIso_derivedHomForgetComparison_phiReflectorBeta :
    IsIso (CochainComplex.derivedHomForgetComparison A K
      (endDerivedForget (CochainComplex.dgCategory A) K) (phiReflector A K L hΦ) h
      (phiReflectorBeta A K L η hΦ)) :=
  isIso_derivedHomForgetComparison_phiReflector A K L hL hη hΦ
    (phiReflectorBeta A K L η hΦ) h
    (derivedHomPhiQh_phiReflectorBeta_app_eq A K L η hL hη hΦ)

include hL hη in
/-- **`R Hom(K, -) ≅ R̃ ⋙ U`, with nothing owed.** -/
@[stacks 09LK "the reduction clause: the functor REDUCES TO THE USUAL R Hom(K, -) on taking \
associated complexes of abelian groups, under the source's own hypothesis h and the reflector \
data of steps 1 and 2"]
def derivedHomForgetPhiReflectorBetaIso :
    CochainComplex.derivedHomForgetFunctor A K h ≅ phiReflectorForget A K L hΦ :=
  derivedHomForgetPhiReflectorIso A K L hL hη hΦ
    (phiReflectorBeta A K L η hΦ) h
    (derivedHomPhiQh_phiReflectorBeta_app_eq A K L η hL hη hΦ)

include hL hη h in
/-- **`R̃ ⋙ U` with the canonical `β` is a right derived functor of `Hom(K, -)`.** -/
theorem isRightDerivedFunctor_phiReflectorForget_phiReflectorBeta :
    (phiReflectorForget A K L hΦ).IsRightDerivedFunctor (phiReflectorBeta A K L η hΦ)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_phiReflectorForget A K L hL hη hΦ
    (phiReflectorBeta A K L η hΦ) h
    (derivedHomPhiQh_phiReflectorBeta_app_eq A K L η hL hη hΦ)

end Main

end DGCategory

end
