module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekComparison
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.LowerShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel

/-!
# `H⁰(f_new^! 𝒪_Y)` is the relative dualizing module

In Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes
of finite type over `S`, and `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to
`ω_S^•`. The second assertion of [Stacks, Tag 0BUL] says `H⁰(f_new^! 𝒪_Y) = ω_{X/Y}`.

For `f` separated this is the first assertion of [Stacks, Tag 0BUL] transported along the closing
remark of [Stacks, Tag 0AUE], `f_new^! 𝒪_Y ≅ f^! 𝒪_Y`.

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.newShriekStructureSheafZeroth`: `H⁰(f_new^! 𝒪_Y)`.
* `Stacks.Duality.NormalizedOnOpens.newShriekRelativeDualizingModuleDataOfSeparated`: the chart
  data of `ω_{X/Y}` on it, for `f` separated.

## References

* [Stacks Project, Tag 0BUL](https://stacks.math.columbia.edu/tag/0BUL)
* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std comparison plusCoh plusCoh_le_qcoh plusCoh_iff)
open Stacks.Discriminant

/-- `𝒪_Y` in degree zero, read at the standard model. -/
abbrev structureStd (Y : Scheme.{u}) : Std Y :=
  (comparison Y).inverse.obj (DerivedPushforward.derivedStructureSheaf Y).obj

/-- On a locally Noetherian scheme `Y`, `𝒪_Y` in degree zero lies in `D^+_{Coh}`. -/
theorem plusCoh_structureStd (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    plusCoh Y (structureStd Y) :=
  (plusCoh_iff _).2 (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _
    (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre Y)
    (SheafOfModules.unit Y.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit (X := Y)))

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} (f : X ⟶ Y) {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- `H⁰(f_new^! 𝒪_Y)`, the degree-zero cohomology sheaf at the standard model. -/
abbrev newShriekStructureSheafZeroth
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS) : X.Modules :=
  (@DerivedCategory.homologyFunctor X.Modules _ _ (PerfectApproximation.standardModel X) 0).obj
    ((fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).obj (structureStd Y))

variable (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) {f}
  (hf : IsShriekable f)
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)

/-- For `f` separated, `H⁰(f_new^! 𝒪_Y) ≅ H⁰(f^! 𝒪_Y)`, from the closing remark of
[Stacks, Tag 0AUE] at `𝒪_Y`. -/
def newShriekStructureSheafZerothIso :
    haveI := hq.source_noetherian
    newShriekStructureSheafZeroth c f 𝒦X 𝒦Y ≅
      upperShriekStructureSheafZeroth (ftsHomSelf hf) (c f hf) :=
  haveI := hq.source_noetherian
  (@DerivedCategory.homologyFunctor X.Modules _ _ (PerfectApproximation.standardModel X) 0).mapIso
      ((upperShriekStdIsoFNewShriek c hpe hωS hf 𝒦X 𝒦Y).app
        ⟨structureStd Y, plusCoh_structureStd Y⟩).symm ≪≫
    (PerfectApproximation.homologyStandardIso _ 0).symm

/-- **[Stacks, Tag 0BUL], second assertion, for `f` separated.** Let `f : X ⟶ Y` be a separated
locally quasi-finite morphism of schemes of finite type over `S`, and `ω_X^•`, `ω_Y^•` normalized
relative to `ω_S^•`. Then `H⁰(f_new^! 𝒪_Y)` carries the chart data of the relative dualizing
module `ω_{X/Y}` of Tag 0BVG. -/
def newShriekRelativeDualizingModuleDataOfSeparated [LocallyQuasiFinite f] :
    haveI := hp.source_noetherian
    haveI := hq.source_noetherian
    RelativeDualizingModuleData f :=
  haveI := hp.source_noetherian
  haveI := hq.source_noetherian
  haveI : LocallyQuasiFinite (ftsHomSelf hf).left := ‹LocallyQuasiFinite f›
  let F := chosenOpenFiniteFactorization (ftsHomSelf hf)
  RelativeDualizingModuleData.ofFiniteTrace F.fac (finiteZeroTwisted F) (finiteTrace F)
    (bijective_traceDual_finiteTrace F)
    (newShriekStructureSheafZerothIso c hpe hωS hf 𝒦X 𝒦Y ≪≫
      upperShriekStructureSheafZerothIso F (c f hf))

/-- The sheaf of `newShriekRelativeDualizingModuleDataOfSeparated` is `H⁰(f_new^! 𝒪_Y)`. -/
@[simp]
theorem newShriekRelativeDualizingModuleDataOfSeparated_sheaf [LocallyQuasiFinite f] :
    haveI := hp.source_noetherian
    haveI := hq.source_noetherian
    (newShriekRelativeDualizingModuleDataOfSeparated c hpe hωS hf 𝒦X 𝒦Y).sheaf =
      newShriekStructureSheafZeroth c f 𝒦X 𝒦Y :=
  rfl

end NormalizedOnOpens

end Stacks.Duality
