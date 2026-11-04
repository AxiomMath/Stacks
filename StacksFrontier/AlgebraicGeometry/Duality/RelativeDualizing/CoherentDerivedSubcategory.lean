module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A dualizing complex on a locally Noetherian scheme lies in `D_Coh(𝒪_X)`

For a scheme `X` the subcategory `D_Coh(𝒪_X) ⊆ D(𝒪_X)` consists of the objects whose cohomology
sheaf is coherent in every degree. On a locally Noetherian `X` a dualizing complex
([Stacks, Tag 0A87]) is such an object: this is the first assertion of [Stacks, Tag 0A89].

## Main definitions

* `Stacks.Duality.isCoherentSheaf` — coherence of a sheaf of modules, as an object property.
* `Stacks.Duality.CoherentDerivedCategory` — `D_Coh(𝒪_X)`, the full subcategory of `D(𝒪_X)` on
  the objects with coherent cohomology sheaves.

## Main results

* `Stacks.Duality.mem_coherentDerivedCategory_of_isDualizingComplex` — **[Stacks, Tag 0A89]**, the
  assertion that a dualizing complex is an object of `D_Coh(𝒪_X)`.
* `Stacks.Duality.dualizingCoherentObject` — the object of `D_Coh(𝒪_X)` this produces.

## Implementation notes

`D_Coh(𝒪_X)` is `DerivedCategoryB.derivedCategoryB` of `Stacks.Duality.isCoherentSheaf`, the
general `D_B(A)` construction of [Stacks, Tag 06UP]; taking `B` to be coherence is what makes it
the subcategory the duality statements of [Stacks, Tag 0A89] are phrased in. The coherence
predicate is written `_root_.SheafOfModules.IsCoherent`, which inside the `Stacks.` namespace is a
different constant from the unqualified name.

The derived category `D(𝒪_X)` is an instance argument `HasDerivedCategory`, so the membership
statement holds for any model of the derived category.

## References

* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

variable (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]

/-- Coherence of a sheaf of modules on a scheme, as an object property of `𝒪_X`-modules. -/
def isCoherentSheaf : ObjectProperty X.Modules :=
  fun F => _root_.SheafOfModules.IsCoherent F

/-- `D_Coh(𝒪_X)`: the full subcategory of the unbounded derived category of `𝒪_X`-modules on the
objects whose cohomology sheaf is coherent in every degree. -/
@[sga "5 III 6.1"]
abbrev CoherentDerivedCategory : Type (u + 1) :=
  (DerivedCategoryB.derivedCategoryB (A := X.Modules) (isCoherentSheaf X)).FullSubcategory

variable [IsLocallyNoetherian X]

/-- A dualizing complex on a locally Noetherian scheme is an object of `D_Coh(𝒪_X)`: every one of
its cohomology sheaves is coherent. -/
@[stacks 0A89 "K is an object of D_Coh(O_X)"]
theorem mem_coherentDerivedCategory_of_isDualizingComplex {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules) (isCoherentSheaf X) K :=
  fun i => isCoherent_homology_of_isDualizingComplex hK i

/-- The object of `D_Coh(𝒪_X)` named by a dualizing complex on a locally Noetherian scheme. -/
def dualizingCoherentObject {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    CoherentDerivedCategory X :=
  ⟨K, mem_coherentDerivedCategory_of_isDualizingComplex X hK⟩

/-- The object of `D(𝒪_X)` underlying `dualizingCoherentObject X hK` is the dualizing complex. -/
@[simp]
theorem dualizingCoherentObject_obj {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    (dualizingCoherentObject X hK).obj = K :=
  rfl

end Stacks.Duality

end
