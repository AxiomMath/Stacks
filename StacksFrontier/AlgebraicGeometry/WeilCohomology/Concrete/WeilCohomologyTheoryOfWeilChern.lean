module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassPointWeilThree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassWeilThree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DivisorTracePushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassPushforwardGlobalSections
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.KunnethWeilThree

/-!
# Proposition 0FIU: the Weil cohomology theory of data satisfying (A1)–(A8)

Let (D0), (D1), (D2') satisfy axioms (A1)–(A7) (`Stacks.WeilCohomology.WeilChernData`), and let
`WeilChernData.toWeilData` be the data (D0)–(D3) of Section 0FHA they define: `F(1)`, `H^*`, the
cycle class map `γ` of Tag 0FIF and the trace map `∫_X = λ` of axiom (A6). Proposition 0FIU says
that under (A8) these data form a Weil cohomology theory (Definition 0FI2). Its proof collects:

* axiom (A): Lemma 0FIJ (`WeilChernData.poincareDuality`);
* axiom (B): Lemma 0FIL (`WeilChernData.kunneth_toWeilData`);
* axioms (C)(a) and (C)(c): the compatibility of `γ` with Gysin maps and intersection products
  (`cycleClassPullback_toWeilData`, `cycleClassMul_toWeilData`);
* axiom (C)(d): Lemma 0FIM (`cycleClassPoint_toWeilData`);
* axiom (C)(b): Lemma 0FIT (`WeilChernData.cycleClassPushforward_of_globalSections`), proved
  under (A1)–(A8);
* the condition of Lemma 0FI0 required by Definition 0FI2: axiom (A8)
  (`globalSectionsCondition_toWeilData`).

The only hypothesis beside the data is (A8): axiom (A9), which the source's proof of Lemma 0FIT
cites, follows from (A1)–(A8) (`WeilChernData.divisorTrace_of_globalSections`) and is not assumed.
Proposition 0FIU is registered on `exists_weilCohomologyTheory`.

## Main definitions

* `Stacks.WeilCohomology.WeilChernData.toWeilCohomologyTheory`: the Weil cohomology theory with
  data `𝔚.toWeilData`.

## Main results

* `Stacks.WeilCohomology.WeilChernData.exists_weilCohomologyTheory`: there is a Weil cohomology
  theory whose data (D0)–(D3) are `𝔚.toWeilData`.

## References

* [Stacks Project, Tag 0FIU](https://stacks.math.columbia.edu/tag/0FIU)
* [Stacks Project, Tag 0FI2](https://stacks.math.columbia.edu/tag/0FI2)
* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

universe u w

namespace Stacks.WeilCohomology.WeilChernData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **The Weil cohomology theory defined by data (D0), (D1), (D2') satisfying (A1)–(A8)**: its
data are `F(1)`, `H^*`, the cycle class map `γ` of Tag 0FIF and the trace map `∫_X = λ` of axiom
(A6), with axioms (A), (B), (C) and the condition of Lemma 0FI0 proved as in Proposition 0FIU. -/
def toWeilCohomologyTheory (hA8 : 𝔚.GlobalSections) :
    WeilCohomologyTheory k F where
  toWeilData := 𝔚.toWeilData
  poincareDuality := 𝔚.poincareDuality
  kunneth := 𝔚.kunneth_toWeilData
  cycleClassAxiom :=
    { pullback := 𝔚.isCohomologicalChernCharacter.cycleClassPullback_toWeilData _ _ _ _
      pushforward := 𝔚.cycleClassPushforward_of_globalSections hA8
      mul := 𝔚.isCohomologicalChernCharacter.cycleClassMul_toWeilData _ _ _ _
      point := 𝔚.isCohomologicalChernCharacter.cycleClassPoint_toWeilData _ _ _ _ }
  globalSections := 𝔚.isCohomologicalChernCharacter.globalSectionsCondition_toWeilData _ _ _ _ hA8

/-- The data (D0)–(D3) of `toWeilCohomologyTheory` are `𝔚.toWeilData`. -/
@[simp]
theorem toWeilCohomologyTheory_toWeilData (hA8 : 𝔚.GlobalSections) :
    (𝔚.toWeilCohomologyTheory hA8).toWeilData = 𝔚.toWeilData :=
  rfl

/-- **Proposition 0FIU: data (D0), (D1), (D2') satisfying (A1)–(A8) give a Weil cohomology
theory**: there is a Weil cohomology theory (Definition 0FI2) whose data (D0)–(D3) are
`𝔚.toWeilData`, i.e. the given `F(1)` and `H^*`, the cycle class map `γ` of Tag 0FIF and the trace
map `∫_X = λ` of axiom (A6). -/
@[stacks 0FIU "the whole proposition, under exactly (A1)-(A8): WeilChernData bundles (A1)-(A7) \
  and the only hypothesis is (A8) GlobalSections; conclusion: a Weil cohomology theory \
  (Definition 0FI2) whose data (D0)-(D3) are F(1), H^*, gamma of 0FIF and the trace of (A6); \
  nothing assumed, (A9) is not used"]
theorem exists_weilCohomologyTheory (hA8 : 𝔚.GlobalSections) :
    ∃ T : WeilCohomologyTheory k F, T.toWeilData = 𝔚.toWeilData :=
  ⟨𝔚.toWeilCohomologyTheory hA8, rfl⟩

end Stacks.WeilCohomology.WeilChernData

end
