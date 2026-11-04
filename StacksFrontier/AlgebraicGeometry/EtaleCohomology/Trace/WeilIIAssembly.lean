module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionStepGoodOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBoundOfFibrePurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreDegeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsInjectionAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AffineCurveDirectImageCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPartStalkCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurvePointInertiaStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLinearTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLinearCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceCoreProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageRealizable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysinOfMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysinVanishingOfPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekLisseLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekLerayWeight
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteCompactSupportCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactificationIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LerayFrobeniusComparisonDischarge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional

/-!
# The assembly of the weight bound of Weil II from its remaining inputs

The weight bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne,
Weil II 3.3.1) is proved by induction on the dimension
(`Stacks.EtaleCohomology.LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_inputs`),
from the curve case on opens of the affine line and the inputs of the induction step. This file
discharges every input that is proved, and keeps as hypotheses only three propositions:

* `Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`: the degeneration of the Fourier family
  at the origin (Laumon's specialization);
* `Stacks.EtaleCohomology.LaumonFibrePurityInput`: the purity of the two-parameter Fourier family
  off a curve of the parameter plane;
* `Stacks.EtaleCohomology.RelativeCurvePurityInput` (at the twist
  `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneOp`): relative purity for étale divisors of smooth
  relative curves, which gives the Gysin morphism of `R² g_!`.

The chain is: Weil II 1.8.4 at a missing point of a curve
(`Stacks.EtaleCohomology.curveLocalInvariantsWeightInput`), from the proved injection of the local
invariants, the proved `E`-linear trace formula and the proved `E`-linear coinvariants; Laumon's
degeneration at the origin (`Stacks.EtaleCohomology.laumonFibreDegenerationInput_of_familyInput`);
the curve case on opens
of `𝔸¹` (`Stacks.EtaleCohomology.weilIICurveBoundOpenAffineLine_of_laumonInputs`); the induction
step (`Stacks.EtaleCohomology.LAdicSheaf.weightBoundInDimension_succ_of_relativeCurvePurityInput`),
where the Leray weight implication, the stalks and the lisse locus of the `Rʳ g_!`, the finiteness
of compactly supported cohomology, the independence of the compactification, the trace formula on
curves and the realizability of `R² g_!` are proved; and the bound of Tag 03VH for `ℱ_ρ`
(`LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_laumonInputs`).

## Main results

* `LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_laumonInputs`: the weight bound of
  Tag 03VH for `ℱ_ρ`, assuming the three inputs above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-! ### The curve case -/

/-- **Weil II 1.8.4 at a missing point of a curve** (`CurveLocalInvariantsWeightInput`): the
injection of the local invariants into `H¹_c` is proved
(`Stacks.EtaleCohomology.curveLocalInvariantsInjectionInput_of_inputs` with its three proved
inputs), and so are the `E`-linear trace formula on curves
(`Stacks.EtaleCohomology.curveLinearTraceFormulaInput`) and the `E`-linear identification of `H²_c`
with the twisted coinvariants (`Stacks.EtaleCohomology.curveLinearCoinvariantsInput`). -/
public theorem curveLocalInvariantsWeightInput : CurveLocalInvariantsWeightInput.{u} :=
  curveLocalInvariantsWeightInput_of_injection curveLinearTraceFormulaInput
    curveLinearCoinvariantsInput
    (curveLocalInvariantsInjectionInput_of_inputs affineCurveDirectImageCompactSupportZeroInput
      closedPartStalkCompactSupportInput curvePointInertiaStalkInput)

/-- **Laumon's degeneration at the origin (L8)** from the degeneration of the Fourier family,
Weil II 1.8.4 being `Stacks.EtaleCohomology.curveLocalInvariantsWeightInput`. -/
public theorem laumonFibreDegenerationInput_of_familyInput
    (hfam : LaumonDegenerationFamilyInput.{u}) : LaumonFibreDegenerationInput.{u} :=
  laumonFibreDegenerationInput_of_family curveLocalInvariantsWeightInput hfam

/-- **The curve case of Weil II on opens of the affine line** from the purity of the Fourier
family (L7) and the degeneration of the Fourier family at the origin. -/
public theorem weilIICurveBoundOpenAffineLine_of_laumonInputs (h7 : LaumonFibrePurityInput.{u})
    (hfam : LaumonDegenerationFamilyInput.{u}) : WeilIICurveBoundOpenAffineLine.{u} :=
  weilIICurveBoundOpenAffineLine_of_fibrePurity h7
    (laumonFibreDegenerationInput_of_familyInput hfam)

/-! ### The induction step -/

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The induction step `S(n) → S(n + 1)` of Weil II from relative purity alone**, for the
family of the ℓ-adic sheaves `Rʳ g_! G`: the Leray weight implication, the stalks and the lisse
locus of the `Rʳ g_! G`, the finiteness of compactly supported cohomology (Tag 03V3), the
independence of the compactification (Tag 0F7I) and the trace formula on smooth curves are
proved, and the realizability of the `Rʳ g_! G` follows from these and from the Gysin morphism of
`R² g_!` along étale divisors, which relative purity gives. -/
theorem LAdicSheaf.weightBoundInDimension_succ_of_relativeCurvePurityInput
    (hPur : RelativeCurvePurityInput B ℓ (LAdicSheaf.twistNegOneOp B ℓ)) (n : ℕ) (hn : 1 ≤ n)
    (hS : LAdicSheaf.WeightBoundInDimension B ℓ n) :
    LAdicSheaf.WeightBoundInDimension B ℓ (n + 1) :=
  have hstalk : LAdicSheaf.HigherDirectImageStalkInput
      (LAdicSheaf.higherDirectImageShriekFamily B ℓ) :=
    LAdicSheaf.higherDirectImageStalkInput_higherDirectImageShriek B ℓ
      (lowerShriekConstructibilityInput B)
      (by
        intro U W _ _ g _ _ _ jg k _ _ fW _ _ _ jW kbar _ _ p q _ _ hcard
        exact LAdicSheaf.lerayFrobeniusComparison B ℓ g jg fW jW kbar p q hcard)
  have hlisse : LAdicSheaf.HigherDirectImageLisseLocusInput
      (LAdicSheaf.higherDirectImageShriekFamily B ℓ) :=
    LAdicSheaf.higherDirectImageLisseLocusInput_higherDirectImageShriek B ℓ
      (lowerShriekConstructibilityInput B)
  LAdicSheaf.weightBoundInDimension_succ_of_inputs
    (lerayWeightInput_higherDirectImageShriekFamily_of_finiteCompactSupportCohomologyInput
      B ℓ (LAdicSheaf.finiteCompactSupportCohomologyInput B ℓ))
    hstalk hlisse
    (LAdicSheaf.higherDirectImageRealizableInput _ hstalk hlisse lisseCurveTraceFormulaInput
      (LAdicSheaf.higherDirectImageTopRealizableInput_higherDirectImageShriekFamily
        (lowerShriekConstructibilityInput B)
        (LAdicSheaf.higherDirectImageTopGysinMorphismInput_of_purity B ℓ hPur)))
    (LAdicSheaf.finiteCompactSupportCohomologyInput B ℓ)
    (LAdicSheaf.compactSupportCompactificationIndependenceInput B ℓ) n hn hS

/-- **The weight bound of Weil II for lisse sheaves on every scheme separated of finite type over
a finite field**, from the three remaining inputs: for every compactification, every lisse ℓ-adic
sheaf `F` pointwise `ι`-mixed of weights `≤ w` and `ι`-realizable, and every `i`, the complex
characteristic roots of the geometric Frobenius on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` have weights
`≤ w + i` along `ι`. -/
theorem LAdicSheaf.satisfiesWeightBound_of_laumonInputs (h7 : LaumonFibrePurityInput.{u})
    (hfam : LaumonDegenerationFamilyInput.{u})
    (hPur : RelativeCurvePurityInput B ℓ (LAdicSheaf.twistNegOneOp B ℓ))
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (hℓ : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ) (X : B.Scheme) [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f :=
  LAdicSheaf.satisfiesWeightBound_of_weightBoundInDimension_succ
    (weilIICurveBoundOpenAffineLine_of_laumonInputs h7 hfam)
    (LAdicSheaf.weightBoundInDimension_succ_of_relativeCurvePurityInput hPur) kbar p q hcard hℓ ι
    X f

/-- **The weight bound of Tag 03VH from the three remaining inputs.**  For `X` connected,
separated of finite type over `k` with `q = p ^ m` elements, `ℓ ≠ p`, and `ρ` a continuous
representation of `π₁(X, x̄)` satisfying the conclusions of Deligne's conjecture, the
eigenvalues of `π_X^*` on `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` are algebraic numbers of absolute value
`q ^ (w / 2)` with `w ≤ i` along every `ι`, given Laumon's two inputs on the Fourier family and
relative purity. -/
theorem LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_laumonInputs
    (h7 : LaumonFibrePurityInput.{u}) (hfam : LaumonDegenerationFamilyInput.{u})
    (hPur : RelativeCurvePurityInput B ℓ (LAdicSheaf.twistNegOneOp B ℓ))
    {k : Type u} [Field k] [Fintype k] {kbar : Type u} [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] {p q : ℕ} [Fact p.Prime] [CharP k p] {hcard : Fintype.card k = p ^ q}
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ)
    (hD : ∀ ι : ℚ_[ℓ] →+* ℂ, HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (LAdicSheaf.representationSheaf B X x ρ hρ) i)] (ι : ℚ_[ℓ] →+* ℂ) :
    IsCharpolyMixedOfWeightLE (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom :=
  LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_weightBoundInDimension_succ
    (weilIICurveBoundOpenAffineLine_of_laumonInputs h7 hfam)
    (LAdicSheaf.weightBoundInDimension_succ_of_relativeCurvePurityInput hPur) hℓ X f j x ρ hρ hD
    i ι

end Stacks.EtaleCohomology

end
