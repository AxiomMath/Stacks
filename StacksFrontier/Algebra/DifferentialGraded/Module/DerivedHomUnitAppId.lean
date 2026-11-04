module

public import StacksFrontier.CategoryTheory.CancelRetraction
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomPhiTransport
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomForgetUnit

/-!
# The canonical comparison `β` at the reflector of Tag 09LK, and the clause `unit_app_id`

Step 3 of the replacement proof of [Stacks, Tag 09LK]
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomForgetRecovery.lean`) is parameterized
on a comparison

`β : Hom(K, -) ⟶ Q ⋙ (R̃ ⋙ U)`

and on one elementwise clause `unit_app_id` about it: that the transported identification `(*)`
of `DGCategory.derivedHomPhiQh` carries the `β`-image of a degree-`n` cohomology class `x` of
`Hom^•(K, Y)` to `Q` of the morphism `K ⟶ Y⟦n⟧` that [Stacks, Tag 09LC] assigns to `x`. This
file fixes `β` to the canonical one and reduces `unit_app_id` at it to a single equation between
two morphisms of `D(A)`, in which neither `β` nor the comparison `ν` nor the transported `(*)`
occurs.

## Which `β`

The `β` used here is **not** a free binder and not one invented to make the equation true. It is
the unit that steps 1 and 2 produce, `DGCategory.derivedHomReflectorUnit`, transported to the
indexing step 3 consumes and forgotten along `DGCategory.endDerivedForget`:

* `DGCategory.phiReflectorLiftUnit` is `DGCategory.derivedHomReflectorUnit` at
  `Φ = (yonedaDGFunctor (Comp^dg A)).onK`, `Z = yonedaInverseImage` at `DGCategory.phiGen` and
  `q = DGCategory.phiComparisonLocalization`, whiskered on the left by the comparison equivalence
  `CochainComplex.homotopyCategoryEquivalence` and composed with
  `DGCategory.phiReflectorTransportIso`, the `R̃`-image of the unit of that equivalence. Its
  component at `Y` is, by `DGCategory.phiReflectorLiftUnit_app`,

  `(derivedHomReflectorUnit …).app (Φ' Y) ≫ R̃.map (phiUnitIso A Y).inv`,

  which is the only transport available: `DGCategory.derivedHomReflectorUnit` runs along
  `q = Φ'⁻¹ ⋙ Q` and the consumer wants a transformation along `DerivedCategory.Qh`, and
  `DGCategory.phiUnitIso` is the same comparison the transport of `φ` in
  `StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/DerivedHomPhiTransport.lean` conjugates by.
* `DGCategory.phiReflectorBeta` feeds that unit to
  `DGCategory.RightModule.derivedHomForgetUnitAtReflector`, i.e. composes its
  `DGCategory.endDerivedForget`-image with the identification
  `CochainComplex.homDerivedLiftForgetIso` of the lift with the abelian-group-valued `Hom(K, -)`.
  `DGCategory.phiReflectorBeta_app` records the component.

Nothing beyond Tag 09LK's own data enters: no smallness, no universe inequality, no K-injective
resolution, no `(CochainComplex.homToDerivedCategory A K).IsRightDerivable`, and no derivability
of the `D(E)`-valued `Hom(K, -)`.

## What is proved

* `DGCategory.phiUnitIso_inv_naturality`: the comparison of the two homotopy categories is
  natural, in the form the transport needs.
* `DGCategory.phiReflectorLiftUnit_app_comp`: **the transport inside the canonical `β` cancels
  exactly the conjugation that the transported `(*)` performs on its source.** This is the one
  place where the choice of `β` is used, and it is why no other `β` can work: for an arbitrary
  comparison the two do not cancel.
* `DGCategory.map_phiReflectorBeta_app_comp`: the source of step 3's equation at the canonical
  `β`, normalised. Combining the cancellation above with
  `DGCategory.derivedHomReflectorUnit_gradedCohomologyMapK` — the normalisation of the reflector's
  unit on cohomology — the composite

  `H^n(β_Y) ≫ H^n(R̃U(phiUnitIso)) ≫ (junction)`

  is `H^n(ν⁻¹_Y)`, followed by the identification of the cohomology of the forgetful image with
  the explicit cohomology, followed by the map `η` induces at the representable after evaluation
  at `K`.
* `DGCategory.derivedHomPhiQh_phiReflectorBeta_app`: **the left-hand side of `unit_app_id` at the
  canonical `β`**, as the chain `DGCategory.RightModule.chainEquivReflectorEvaluation` of steps 1
  and 2 applied to that class, conjugated by `DGCategory.phiSourceIso` and
  `DGCategory.phiUnitIso`. No localization comparison and no `β` survives inside the chain's
  argument.
* `DGCategory.derivedHomPhiQh_phiReflectorBeta_app_eq_iff`: **the residual obligation, stated
  exactly.** `unit_app_id` at the canonical `β` holds if and only if

  `chain (H^n(ev_K η) (ι_Y (H^n(ν⁻¹_Y) x))) =
      (phiSourceIso A K).inv ≫ (Q(09LC x) ≫ (Q.commShiftIso n).hom.app Y) ≫ (phiUnitIso A Y)⟦n⟧`

  where `ι_Y` is `DGCategory.RightModule.endDerivedForgetGradedCohomologyIso`. Both sides are
  morphisms `q K ⟶ (q (Φ' Y))⟦n⟧` of `D(A)`; the conjugation on the right is pure bookkeeping.

## What is still owed, and the route

The residual equation of `DGCategory.derivedHomPhiQh_phiReflectorBeta_app_eq_iff` is all that
[Stacks, Tag 09LK] still owes. It splits into three steps, each with its ingredients already
available in the library.

**(1) Identify the class.** Say what
`ι_Y (H^n(ν⁻¹_Y) x)` is, for `x` the class of a cocycle. At `Y` the homotopy class of a complex
`Y₀` — which every object of `K(A)` is — `CochainComplex.coreLHS_step2` computes exactly
`H^n(ν⁻¹) ≫ ι` as three factors: the forgetful square of the Hom representation, `Q` of
`CochainComplex.homEvaluationComparisonIso`, and the factorization of cohomology over the
category of complexes followed by the explicit cohomology. What that reduction still owes is the
one lemma recorded in the header of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomCoreLHSMid.lean`:

```
HomologicalComplex.homologyMap ((homEvaluationComparisonIso A K).hom.app Y) n ≫
    (DGCategory.RightModule.gradedCohomologyIso
      (DGCategory.yonedaRightModule (dgCategory A) Y) K n).hom =
  (DifferentialGradedModule.gradedCohomologyIso
      (DGCategory.representableModule (dgCategory A) K Y) n).hom ≫
    ModuleCat.ofHom (homYonedaCohomologyEquiv A K Y n).toIntLinearEquiv.toLinearMap
```

`DGCategory.RightModule.gradedCohomology_evaluation` is `rfl`, so the two indexings need no
bridge; `HomologicalComplex.homologyπ` is epi and the two
`homologyπ_gradedCohomologyIso_hom` (`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/YonedaHomCohomology.lean:359` and
`HomCohomology.lean:221`) reduce it to the agreement of
`CochainComplex.homEvaluationComparisonIso_hom_app_f_apply`
(`HomEvaluationComplexIso.lean:228`) with `CochainComplex.homYonedaCocyclesEquiv_coe`, both being
`CochainComplex.homGradingEquiv`. The remaining bookkeeping is the two
`HomologicalComplex.cyclesIsoSc'` — both sides carry one, pinned by
`DGCategory.RightModule.gradedCyclesIso_hom_val` and
`DifferentialGradedModule.gradedCyclesIso_hom_subtype` respectively — and the class is then
`CochainComplex.homYonedaCohomologyEquiv_mk` of the cocycle, which
`CochainComplex.homologyHomAddEquiv_quotient_obj_apply_mk` identifies with 09LC's morphism.

**(2) Strip links 4 and 2 of the chain.** `DGCategory.RightModule.chainEquivReflectorEvaluation`
is `E_n⁻¹ ∘ B_n ∘ Y_n⁻¹`, so
`DGCategory.RightModule.homEquivDerivedYonedaOnK'_symm_eq_iff` turns the residual equation into
`E_n(RHS) = B_n (Y_n⁻¹ (…))`, and
`CategoryTheory.ObjectProperty.homEquivReflectorShift_apply_comp`
(`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/LinkApplyLemmas.lean:317`) states `B_n` with the denominator cleared, so that postcomposing by
the isomorphism `(Q η_y)⟦n⟧` and cancelling it leaves no `CategoryTheory.inv`. The reflector
cancellation is purely categorical:

`B_n(d_f ≫ η_y⟦n⟧) = Q(d_f ≫ η_y⟦n⟧) ≫ σ_Q ≫ ((Q η_y)⟦n⟧)⁻¹ = Q(d_f) ≫ σ_Q(Φ y, n)`,

by `CategoryTheory.Functor.map_comp` and naturality of `Q.commShiftIso` at `η_y`. **No
compatibility of `η` with `L`'s `CommShift` is needed** — `η_y⟦n⟧` is the ordinary shift of a
component — and inverses are never expanded.

**(3) The one elementwise step.** What is left is
`Y_n⁻¹ (H^n(ev_K η_{Φ y}) [f]) = d_f ≫ (η_{Φ y})⟦n⟧`, i.e. that link 1's inverse carries the
`η`-image of the class of the cocycle `f` to the differential graded Yoneda image of `f` composed
with the shifted unit. Prove it with
`DGCategory.RightModule.homShiftEquivEvaluationGradedCohomology_mk`
(`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/LinkApplyLemmas.lean:438`) through
`DGCategory.RightModule.homShiftEquivGradedCohomology_symm_eq_iff`, together with
`CochainComplex.homEvaluationComparisonIso_hom_app_f_apply` and
`CochainComplex.homEvaluationComparisonIso_inv_app_f_apply`
(`HomEvaluationComplexIso.lean:228,239`) — both directions; the inverse is the inverse
`CochainComplex.homGradingEquiv`, not an opaque preimage. A cohomology class is reduced to a
cocycle representative **only here**. The right-hand side at a cocycle is then
`CochainComplex.coreRHS_mk`, whose hypothesis `hf` is discharged by
`CochainComplex.map_comp_commShiftIso_mk`.

*The sign.* The `(-1)^n` of `symm_toShift_d` is **matched, not cancelled**:
`DGCategory.RightModule.shift_d` puts `(-1)^n` on the differential of `M⟦n⟧` too, so closedness
is literally "`(-1)^n` times a differential vanishes" and the sign stands on both sides of one
equation. It must not be divided out. At evaluation on the identity the input morphism has degree
zero, so signs involving that degree vanish; every reindexing isomorphism is nevertheless
retained.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose step 3 this
  belongs to; [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the identification of a
  degree-`n` cohomology class of a Hom complex with a morphism of the homotopy category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.ObjectProperty

/-- A two-sided conjugation by isomorphisms can be moved to the other side of an equation.
Every object is a variable, so this applies at composites whose objects are large semireducible
terms without unfolding any of them. -/
private theorem CategoryTheory.comp_conj_eq_iff {D : Type*} [Category D] {X X' Y Y' : D}
    (i : X ≅ X') (j : Y ≅ Y') (c : X' ⟶ Y') (t : X ⟶ Y) :
    i.hom ≫ c ≫ j.inv = t ↔ c = i.inv ≫ t ≫ j.hom := by
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

/-- `a ≫ b ≫ 𝟙 = a ≫ b`, with every object a variable. -/
private theorem CategoryTheory.comp_comp_id {D : Type*} [Category D] {X Y Z : D} (a : X ⟶ Y)
    (b : Y ⟶ Z) : a ≫ b ≫ 𝟙 Z = a ≫ b := by rw [Category.comp_id]

namespace DGCategory

universe w v

variable (A : Type) [Category.{0} A] [Abelian A] [HasDerivedCategory.{v} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).CommShift ℤ]
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).IsTriangulated]
  (L : (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K ⥤
    (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K)
  [L.CommShift ℤ] [L.IsTriangulated]
  (η : 𝟭 (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K ⟶ L)

attribute [local implicit_reducible] DGCategory.K

variable (hΦ : ∀ X, RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A) X →
  IsZero (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK ⋙ L).obj X))

/-- Naturality of the inverse of `DGCategory.phiUnitIso`: for a morphism `s : X ⟶ Y` of the
homotopy category, the image of `s` under the comparison localization followed by
`(phiUnitIso A Y).inv` equals `(phiUnitIso A X).inv` followed by `DerivedCategory.Qh.map s`. -/
theorem phiUnitIso_inv_naturality {X Y : HomotopyCategory A (ComplexShape.up ℤ)} (s : X ⟶ Y) :
    (phiComparisonLocalization A).map
        ((CochainComplex.homotopyCategoryEquivalence A).functor.map s) ≫
      (phiUnitIso A Y).inv = (phiUnitIso A X).inv ≫ DerivedCategory.Qh.map s := by
  have hu : (phiUnitIso A X).hom ≫ (phiComparisonLocalization A).map
        ((CochainComplex.homotopyCategoryEquivalence A).functor.map s) =
      DerivedCategory.Qh.map s ≫ (phiUnitIso A Y).hom := by
    rw [phiUnitIso, phiUnitIso, Functor.mapIso_hom, Functor.mapIso_hom, Functor.comp_map,
      ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Qh.map
      ((CochainComplex.homotopyCategoryEquivalence A).unitIso.hom.naturality s).symm
  rw [Iso.comp_inv_eq, Category.assoc, ← hu, Iso.inv_hom_id_assoc]

/-- The reindexing isomorphism `R̃ ∘ q ∘ Φ' ≅ R̃ ∘ Q`, the `R̃`-image of the unit of the
comparison equivalence. -/
def phiReflectorTransportIso :
    (CochainComplex.homotopyCategoryEquivalence A).functor ⋙ phiComparisonLocalization A ⋙
        phiReflector A K L hΦ ≅ DerivedCategory.Qh ⋙ phiReflector A K L hΦ :=
  NatIso.ofComponents (fun Y ↦ (phiReflector A K L hΦ).mapIso (phiUnitIso A Y).symm)
    (fun {_X _Y} f ↦
      (((phiReflector A K L hΦ).map_comp _ _).symm.trans
          (congrArg (phiReflector A K L hΦ).map (phiUnitIso_inv_naturality A f))).trans
        ((phiReflector A K L hΦ).map_comp _ _))

/-- The unit of steps 1 and 2, transported from `DGCategory.phiComparisonLocalization` to
`DerivedCategory.Qh`. -/
def phiReflectorLiftUnit :
    CochainComplex.homDerivedLift A K ⟶ DerivedCategory.Qh ⋙ phiReflector A K L hΦ :=
  Functor.whiskerLeft (CochainComplex.homotopyCategoryEquivalence A).functor
      (derivedHomReflectorUnit (CochainComplex.dgCategory A) K L
        ((yonedaDGFunctor (CochainComplex.dgCategory A)).onK)
        (RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A))
        (phiComparisonLocalization A) η hΦ) ≫
    (phiReflectorTransportIso A K L hΦ).hom

/-- The canonical `β`. -/
def phiReflectorBeta :
    CochainComplex.homToDerivedCategoryForget A K ⟶
      DerivedCategory.Qh ⋙ phiReflector A K L hΦ ⋙
        endDerivedForget (CochainComplex.dgCategory A) K :=
  RightModule.derivedHomForgetUnitAtReflector A K (phiReflector A K L hΦ)
    (phiReflectorLiftUnit A K L η hΦ)

/-- The component of `DGCategory.phiReflectorLiftUnit` at `Y` is the component of the reflector
unit at the image of `Y` in the homotopy category of complexes, followed by the image under the
reflector of `(phiUnitIso A Y).inv`. -/
theorem phiReflectorLiftUnit_app (Y : HomotopyCategory A (ComplexShape.up ℤ)) :
    (phiReflectorLiftUnit A K L η hΦ).app Y =
      (derivedHomReflectorUnit (CochainComplex.dgCategory A) K L
            ((yonedaDGFunctor (CochainComplex.dgCategory A)).onK)
            (RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A))
            (phiComparisonLocalization A) η hΦ).app
          ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y) ≫
        (phiReflector A K L hΦ).map (phiUnitIso A Y).inv := rfl

/-- **The transport cancels against the conjugation the transported `φ` performs.** -/
theorem phiReflectorLiftUnit_app_comp (Y : HomotopyCategory A (ComplexShape.up ℤ)) :
    (phiReflectorLiftUnit A K L η hΦ).app Y ≫
        (phiReflector A K L hΦ).map (phiUnitIso A Y).hom =
      (derivedHomReflectorUnit (CochainComplex.dgCategory A) K L
          ((yonedaDGFunctor (CochainComplex.dgCategory A)).onK)
          (RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A))
          (phiComparisonLocalization A) η hΦ).app
        ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y) := by
  rw [phiReflectorLiftUnit_app]
  exact CategoryTheory.comp_cancel_right _
    ((phiReflector A K L hΦ).mapIso (phiUnitIso A Y)).inv_hom_id

/-- The component of `DGCategory.phiReflectorBeta` at `Y` is the inverse of
`CochainComplex.homDerivedLiftForgetIso` at `Y` followed by the image under `endDerivedForget` of
the component of `DGCategory.phiReflectorLiftUnit` at `Y`. -/
theorem phiReflectorBeta_app (Y : HomotopyCategory A (ComplexShape.up ℤ)) :
    (phiReflectorBeta A K L η hΦ).app Y =
      (CochainComplex.homDerivedLiftForgetIso A K).inv.app Y ≫
        (endDerivedForget (CochainComplex.dgCategory A) K).map
          ((phiReflectorLiftUnit A K L η hΦ).app Y) := by
  show (CochainComplex.homDerivedLiftForgetIso A K).inv.app Y ≫
      (endDerivedForget (CochainComplex.dgCategory A) K).map
        ((phiReflectorLiftUnit A K L η hΦ).app Y) ≫ 𝟙 _ = _
  exact CategoryTheory.comp_comp_id _ _

/-- **The source of step 3's equation at the canonical `β`, normalised.** The conjugation that
the transported `(*)` performs on its source cancels the transport inside the canonical `β`, and
what is left of `β` is the reflector's own unit, which
`DGCategory.derivedHomReflectorUnit_gradedCohomologyMapK` reads on the explicit cohomology as the
map induced by `η` at the representable, evaluated at `K`. -/
theorem map_phiReflectorBeta_app_comp (Y : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((phiReflectorBeta A K L η hΦ).app Y) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((phiReflectorForget A K L hΦ).map (phiUnitIso A Y).hom) ≫
          (derivedHomReflectorGradedCohomologyIso (CochainComplex.dgCategory A) K L
            ((yonedaDGFunctor (CochainComplex.dgCategory A)).onK)
            (RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A))
            (phiComparisonLocalization A) hΦ
            ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y) PUnit.unit n).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((CochainComplex.homDerivedLiftForgetIso A K).inv.app Y) ≫
        (RightModule.endDerivedForgetGradedCohomologyIso (CochainComplex.dgCategory A) K
            (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).obj
              ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y))
            PUnit.unit n).hom ≫
          RightModule.gradedCohomologyMapK
            ((evaluationOnK (CochainComplex.dgCategory A) K).map
              (η.app (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).obj
                ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y))))
            PUnit.unit n := by
  have hcomb : (phiReflectorBeta A K L η hΦ).app Y ≫
        (phiReflectorForget A K L hΦ).map (phiUnitIso A Y).hom =
      (CochainComplex.homDerivedLiftForgetIso A K).inv.app Y ≫
        (endDerivedForget (CochainComplex.dgCategory A) K).map
          ((derivedHomReflectorUnit (CochainComplex.dgCategory A) K L
              ((yonedaDGFunctor (CochainComplex.dgCategory A)).onK)
              (RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A))
              (phiComparisonLocalization A) η hΦ).app
            ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y)) := by
    rw [phiReflectorBeta_app, Category.assoc]
    exact congrArg ((CochainComplex.homDerivedLiftForgetIso A K).inv.app Y ≫ ·)
      ((((endDerivedForget (CochainComplex.dgCategory A) K).map_comp _ _).symm).trans
        (congrArg (endDerivedForget (CochainComplex.dgCategory A) K).map
          (phiReflectorLiftUnit_app_comp A K L η hΦ Y)))
  have h2 := derivedHomReflectorUnit_gradedCohomologyMapK (CochainComplex.dgCategory A) K L
    ((yonedaDGFunctor (CochainComplex.dgCategory A)).onK)
    (RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A))
    (phiComparisonLocalization A) η hΦ
    ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y) PUnit.unit n
  rw [← Category.assoc, ← Functor.map_comp, hcomb, Functor.map_comp, Category.assoc]
  exact congrArg (_ ≫ ·) h2

section Transport

variable
  (hL : ∀ X, (RightModule.yonedaLocalizing (CochainComplex.dgCategory A) (phiGen A)).rightOrthogonal
    (L.obj X))
  (hη : ∀ (X Z : (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K) (f : Z ⟶ X)
      (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
    Triangle.mk f (η.app X) g ∈
        distTriang (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K →
      RightModule.yonedaLocalizing (CochainComplex.dgCategory A) (phiGen A) Z)

/-- **The left-hand side of step 3's elementwise equation at the canonical `β`.** No comparison
of localizations and no `β` is left: what the transported `(*)` does to the `β`-image of a
degree-`n` cohomology class `x` of `Hom^•(K, Y)` is the chain of steps 1 and 2, applied to the
`η`-image of the class that the comparison `ν` and the explicit cohomology carry `x` to, read
back into `D(A)` by the two comparisons of the homotopy categories. -/
theorem derivedHomPhiQh_phiReflectorBeta_app (Y : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
    (x : ↥((CochainComplex.homToDerivedCategoryForget A K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj Y)) :
    derivedHomPhiQh A K L hL hη hΦ Y n
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((phiReflectorBeta A K L η hΦ).app Y) x) =
      (phiSourceIso A K).hom ≫
        RightModule.chainEquivReflectorEvaluation (CochainComplex.dgCategory A) (phiGen A) hL hη
            (phiComparisonLocalization A) (K : (CochainComplex.dgCategory A).K)
            ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y) PUnit.unit n
            (RightModule.gradedCohomologyMapK
              ((evaluationOnK (CochainComplex.dgCategory A) K).map
                (η.app (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).obj
                  ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y))))
              PUnit.unit n
              ((RightModule.endDerivedForgetGradedCohomologyIso (CochainComplex.dgCategory A) K
                  (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).obj
                    ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y))
                  PUnit.unit n).hom
                ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
                  ((CochainComplex.homDerivedLiftForgetIso A K).inv.app Y) x))) ≫
        (shiftFunctor (DerivedCategory A) n).map (phiUnitIso A Y).inv := by
  have hA := ConcreteCategory.congr_hom (C := ModuleCat.{0} ℤ)
    (map_phiReflectorBeta_app_comp A K L η hΦ Y n) x
  refine Eq.trans (derivedHomPhiQh_apply A K L hL hη hΦ Y n _) ?_
  exact congrArg (fun w ↦ (phiSourceIso A K).hom ≫
      RightModule.chainEquivReflectorEvaluation (CochainComplex.dgCategory A) (phiGen A) hL hη
          (phiComparisonLocalization A) (K : (CochainComplex.dgCategory A).K)
          ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y) PUnit.unit n w ≫
        (shiftFunctor (DerivedCategory A) n).map (phiUnitIso A Y).inv) hA

/-- **The clause `unit_app_id` at the canonical `β`, with every comparison of localizations
removed: exactly what is left to prove.** The left-hand side of step 3's equation at the
canonical `β` is a two-sided conjugate of the chain of steps 1 and 2, so the equation holds if
and only if the chain, applied to the `η`-image of the class that `ν` and the explicit cohomology
carry `x` to, is the morphism that [Stacks, Tag 09LC] assigns to `x`, read into
`Hom_{D(A)}(q K, (q (Φ' Y))⟦n⟧)` by the two comparisons of the homotopy categories.

The right-hand side mentions neither `β` nor `ν` nor the transported `(*)`: it is an equation
between two morphisms of `D(A)`, and it is the one obligation of [Stacks, Tag 09LK] that the
replacement proof still owes. -/
theorem derivedHomPhiQh_phiReflectorBeta_app_eq_iff
    (Y : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
    (x : ↥((CochainComplex.homToDerivedCategoryForget A K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj Y)) :
    derivedHomPhiQh A K L hL hη hΦ Y n
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((phiReflectorBeta A K L η hΦ).app Y) x) =
        DerivedCategory.Qh.map (CochainComplex.homologyHomAddEquiv A K n Y x) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app Y ↔
      RightModule.chainEquivReflectorEvaluation (CochainComplex.dgCategory A) (phiGen A) hL hη
          (phiComparisonLocalization A) (K : (CochainComplex.dgCategory A).K)
          ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y) PUnit.unit n
          (RightModule.gradedCohomologyMapK
            ((evaluationOnK (CochainComplex.dgCategory A) K).map
              (η.app (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).obj
                ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y))))
            PUnit.unit n
            ((RightModule.endDerivedForgetGradedCohomologyIso (CochainComplex.dgCategory A) K
                (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).obj
                  ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y))
                PUnit.unit n).hom
              ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
                ((CochainComplex.homDerivedLiftForgetIso A K).inv.app Y) x))) =
        (phiSourceIso A K).inv ≫
          (DerivedCategory.Qh.map (CochainComplex.homologyHomAddEquiv A K n Y x) ≫
              (DerivedCategory.Qh.commShiftIso n).hom.app Y) ≫
            (shiftFunctor (DerivedCategory A) n).map (phiUnitIso A Y).hom := by
  rw [derivedHomPhiQh_phiReflectorBeta_app]
  exact CategoryTheory.comp_conj_eq_iff (phiSourceIso A K)
    ((shiftFunctor (DerivedCategory A) n).mapIso (phiUnitIso A Y)) _ _

end Transport

end DGCategory

end
