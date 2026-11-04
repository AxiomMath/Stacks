module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualPerfectLocal
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualRingedSpaceJoin
import StacksCore.Tactic.StacksAttribute

/-!
# An object of `D(O_X)` with a left dual is perfect

Let `(X, O_X)` be a ringed space and let `M` be an object of `D(O_X)` admitting a left dual `N`
in the symmetric monoidal category `D(O_X)` of Stacks 0FPB (Categories, Definition 0FFP: an
exact pairing `M ⊣ N`). Then `M` is perfect (Stacks 0FPD).

The proof is local on `X` (Stacks 08CR). Near a point, the pairing restricts to the open
subspace (`Stacks.Cohomology.LeftDualPerfect.exactPairingRestrictOpen`) and the coevaluation is
a finite sum `Σ fᵢ ⊗ gᵢ` against K-flat representatives, so that `M` is a retract of every
subcomplex of a representative containing the `fᵢ`
(`Stacks.Cohomology.LeftDualPerfect.exists_local_retract`). Applied to a canonical truncation this
bounds `M` above near the point (`Stacks.Cohomology.LeftDualPerfect.exists_isLE_restrict`);
applied to a bounded above representative whose terms are sums of extensions by zero of
structure sheaves of opens (Stacks 05T7, Stacks 05NI), and to the finite subcomplex generated near
the point by the summands carrying the `fᵢ`, it exhibits `M` near the point as a retract of a
bounded complex of finite free modules
(`Stacks.Cohomology.LeftDualPerfect.exists_isPerfect_restrict_of_isLE`), hence as perfect.

## Main results

* `Stacks.Cohomology.LeftDualPerfect.isPerfect_of_exactPairing`: Stacks 0FPD, conclusion (a).
* `Stacks.Cohomology.LeftDualPerfect.isPerfect_and_isIso_derivedDualToLeftDual`: **Stacks 0FPD**,
  both conclusions for one and the same pairing.

## References

* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal Stacks.Cohomology.MonoidalDerived

universe u d

namespace Stacks.Cohomology.LeftDualPerfect

attribute [local instance] HasDerivedCategory.standard in
/-- **Stacks 0FPD, conclusion (a).** Let `(X, O_X)` be a ringed space and let `M` be an object of
`D(O_X)` with a left dual `N` for the derived tensor product of Stacks 0FPB, that is, an exact
pairing `M ⊣ N` (Categories, Definition 0FFP). Then `M` is perfect (Tag 08CM).

The derived category of `X` is arbitrary; those of the open subspaces of `X`, which occur only in
the proof, are the standard ones. -/
theorem isPerfect_of_exactPairing (X : RingedSpace.{u, u})
    [inst : HasDerivedCategory.{d} (Mod X.sheaf)] (M N : DerivedModules X.sheaf)
    (pair : letI := derivedCategoryMonoidalCategory X; ExactPairing M N) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} X inst M := by
  let : HasDerivedCategory.{d} (StrictlyPerfect.OXMod X) := inst
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect M fun x => ?_
  obtain ⟨V, hxV, b, hb⟩ := exists_isLE_restrict X M N pair x
  refine ⟨V, hxV, ?_⟩
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect
    (X := X.restrict V.isOpenEmbedding) _ fun y => ?_
  exact exists_isPerfect_restrict_of_isLE (X.restrict V.isOpenEmbedding) _ _
    (exactPairingRestrictOpen X V M N pair) b hb y

attribute [local instance] HasDerivedCategory.standard in
/-- The monoidal structure of Stacks 0FPB on `D(O_X)`, in its ringed-site spelling at the site of
opens of `X`. -/
@[instance_reducible]
def derivedMonoidalSpace (X : RingedSpace.{u, u}) : MonoidalCategory (DerivedModules X.sheaf) :=
  AlgebraicGeometry.RingedSite.derivedMonoidalStructure (Stacks.SheafOfModules.ringedSite X.sheaf)

attribute [local instance] HasDerivedCategory.standard in
/-- **Stacks 0FPD.** Let `(X, O_X)` be a ringed space and let `M` be an object of `D(O_X)` with a
left dual `N` in the symmetric monoidal category `D(O_X)` of Stacks 0FPB (an exact pairing,
Categories, Definition 0FFP). Then

* (a) `M` is perfect (Tag 08CM), and
* (b) the left dual is the one constructed in Example 0FPC: the morphism
  `M^∨ = RSheafHom(M, O_X) ⟶ N` which the pairing matches with the evaluation of Example 0FPC is
  an isomorphism.

The monoidal structure is written in its ringed-site spelling, which is the structure of
Stacks 0FPB on the nose (`derivedCategoryMonoidalCategory_eq_ringedSite`, by `rfl`). Conclusion
(a) is `isPerfect_of_exactPairing`; conclusion (b) is
`Stacks.SheafOfModules.isIso_derivedDualToLeftDualMonoidal`, whose morphism carries the evaluation
of the pairing to the evaluation of Example 0FPC
(`Stacks.SheafOfModules.whiskerRight_derivedDualToLeftDualMonoidal`). -/
@[stacks 0FPD "both conclusions, for one pairing: M is perfect, and the left dual is the \
derived dual of Example 0FPC"]
theorem isPerfect_and_isIso_derivedDualToLeftDual (X : RingedSpace.{u, u})
    (M N : DerivedModules X.sheaf)
    (pair : letI := derivedMonoidalSpace X; ExactPairing M N) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect M ∧
      (letI := derivedMonoidalSpace X
       let _ := pair
       IsIso (AlgebraicGeometry.RingedSite.derivedDualToLeftDual
        (X := Stacks.SheafOfModules.ringedSite X.sheaf) M N)) :=
  ⟨isPerfect_of_exactPairing X M N pair,
    Stacks.SheafOfModules.isIso_derivedDualToLeftDualMonoidal X.sheaf M N pair⟩

end Stacks.Cohomology.LeftDualPerfect
