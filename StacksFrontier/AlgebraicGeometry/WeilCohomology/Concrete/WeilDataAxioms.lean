module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilCohomologyTheory

/-!
# Data (D0)–(D3) satisfying (A), (B) and (C)

Section 45.9 of the Stacks Project (Tag 0FHA) states many results for "data (D0), (D1), (D2) and
(D3) satisfying (A), (B) and (C)", and Lemmas 0FHK, 0FHL and 0FHM compare such data with
realizations of Chow motives. This file bundles them: `Stacks.WeilCohomology.WeilDataAxioms k F`
is the data `Stacks.WeilCohomology.WeilData k F` together with axioms (A), (B) and (C), with the
same field names as `Stacks.WeilCohomology.WeilCohomologyTheory` (Definition 0FI2), which is this
bundle together with condition (2) of Lemma 0FI0. A Weil cohomology theory has underlying data
satisfying (A), (B), (C) (`Stacks.WeilCohomology.WeilCohomologyTheory.toWeilDataAxioms`), by
forgetting that condition.

## Main definitions

* `Stacks.WeilCohomology.WeilDataAxioms`: data (D0)–(D3) satisfying (A), (B) and (C).
* `Stacks.WeilCohomology.WeilCohomologyTheory.toWeilDataAxioms`: the underlying bundle of a Weil
  cohomology theory.

## References

* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
* [Stacks Project, Tag 0FI2](https://stacks.math.columbia.edu/tag/0FI2)
-/

@[expose] public section

universe u w

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k] (F : Type w) [Field F]

/-- **Data (D0), (D1), (D2) and (D3) satisfying (A), (B) and (C)** (Section 45.9, Tag 0FHA): the
data `WeilData k F` together with Poincaré duality, the Künneth formula and compatibility with
cycle classes. -/
structure WeilDataAxioms extends WeilData k F where
  /-- Axiom (A). -/
  poincareDuality : toWeilData.PoincareDuality
  /-- Axiom (B). -/
  kunneth : toWeilData.Kunneth
  /-- Axiom (C). -/
  cycleClassAxiom : toWeilData.CycleClassAxiom poincareDuality.perfectPairing

variable {k F}

/-- The data (D0)–(D3) of a Weil cohomology theory satisfy (A), (B) and (C): forget condition (2)
of Lemma 0FI0. -/
def WeilCohomologyTheory.toWeilDataAxioms (T : WeilCohomologyTheory k F) : WeilDataAxioms k F where
  toWeilData := T.toWeilData
  poincareDuality := T.poincareDuality
  kunneth := T.kunneth
  cycleClassAxiom := T.cycleClassAxiom

/-- The underlying data (D0)–(D3) of `T.toWeilDataAxioms` are those of `T`. -/
@[simp]
theorem WeilCohomologyTheory.toWeilDataAxioms_toWeilData (T : WeilCohomologyTheory k F) :
    T.toWeilDataAxioms.toWeilData = T.toWeilData :=
  rfl

/-- A Weil cohomology theory is the same as data satisfying (A), (B), (C) and condition (2) of
Lemma 0FI0. -/
def WeilCohomologyTheory.ofWeilDataAxioms (W : WeilDataAxioms k F)
    (h : W.toWeilData.GlobalSectionsCondition) : WeilCohomologyTheory k F where
  toWeilData := W.toWeilData
  poincareDuality := W.poincareDuality
  kunneth := W.kunneth
  cycleClassAxiom := W.cycleClassAxiom
  globalSections := h

/-- Forgetting condition (2) of Lemma 0FI0 from `WeilCohomologyTheory.ofWeilDataAxioms W h`
recovers `W`. -/
@[simp]
theorem WeilCohomologyTheory.toWeilDataAxioms_ofWeilDataAxioms (W : WeilDataAxioms k F)
    (h : W.toWeilData.GlobalSectionsCondition) :
    (WeilCohomologyTheory.ofWeilDataAxioms W h).toWeilDataAxioms = W :=
  rfl

end Stacks.WeilCohomology

end
