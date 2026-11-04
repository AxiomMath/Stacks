module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassBivariant
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
import StacksCore.Tactic.StacksAttribute

/-!
# The first Chern class of the dual of an invertible module

For an invertible `𝒪_X`-module `ℒ` on a scheme `X` locally of finite type over the base of a
Chow situation, `c₁(ℒ^∨) = -c₁(ℒ)`.

This is the rank-one case of [Stacks Project, Tag 0FA5], deduced from the two clauses of
[Stacks Project, Tag 02SP], and carried up the three layers the Chern classes of this
development are built in:

* on cycles, `firstChernClassCapOfInvertible_dualSheaf`;
* on Chow groups, `firstChernClassCapChow_dualSheaf`, and on the Chern class cap products
  of [Stacks Project, Tag 02U6], `chernCap_one_dualSheaf`;
* **as bivariant classes of [Stacks Project, Tag 0B77]**, `firstChernClass_dualSheaf`:
  an equality `c₁(ℒ^∨) = -c₁(ℒ)` in `A^1(X)`.

The last of these is the one that was missing: nothing in this repository negated a
`Stacks.Chow.BivariantClass`, so the only form of `c₁` of an inverse available was the operation
on cycle groups.

## Main results

* `Stacks.Chow.GenuineChern.firstChernClassCapOfInvertible_dualSheaf`
* `Stacks.Chow.GenuineChern.firstChernClassCapChow_dualSheaf`
* `Stacks.Chow.GenuineChern.chernCap_one_dualSheaf`
* `Stacks.Chow.GenuineChern.firstChernClass_dualSheaf`

## Implementation notes

**Why the dual, and not a chosen tensor inverse.** The existing form of this identity,
`Stacks.Chow.firstChernCapStep_eq_neg_of_tensorObj_iso_unit`, takes the inverse as a *hypothesis*
`ℳ` together with an isomorphism `ℒ ⊗ ℳ ≅ 𝒪_X`, which is what Stacks 02SP is stated at. The
statements here are about `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf` itself, because
that is the module whose Chern classes [Stacks Project, Tag 0FAE] is about: an `E^∨` is not
accompanied by a chosen tensor inverse. The bridge is Tag 0B8K,
`Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf`: a tensor inverse of `ℒ` exists
because `ℒ` is invertible, and it is isomorphic to `ℒ^∨`, so tensoring that isomorphism with
`ℒ` turns the existential inverse into the isomorphism `ℒ ⊗ ℒ^∨ ≅ 𝒪_X` that Stacks 02SP
consumes. The two spellings of the dual in this repository,
`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf` (over `X.Modules`) and
`Stacks.SheafOfModules.dualSheaf` (over a ringed site), are definitionally the same object, and
`Stacks.InvertibleBridge` carries invertibility between the two spellings of `IsInvertible`.

**How the bivariant statement is proved.** Not by unfolding the construction of a bivariant
class. A bivariant class satisfying the characterization of Tag 0B7H is unique
(`Stacks.Chow.eq_of_isChernClassBivariant`), so it is enough to check that `-c₁(ℒ)` satisfies
that characterization for `ℒ^∨`, i.e. that on every test scheme `g : T ⟶ X` its cap operation is
`c₁(g^*(ℒ^∨)) ∩ -`. Negation of a bivariant class is pointwise on the cap operation, so the left
side is `-(c₁(g^*ℒ) ∩ -)`, and the identity needed on `T` is the Chern-cap form
`chernCap_one_dualSheaf` applied to `g^*ℒ`, after `g^*(ℒ^∨)` is identified with `(g^*ℒ)^∨` by the
dual base-change isomorphism `Stacks.Chow.pullbackDualMap_isIso` of Tag 0GMX. No flat pullback,
no projective bundle and no splitting principle enters.

**No `@[stacks]` attribute is placed in this file.** Tag 02SP has exactly two clauses, the
additivity `c₁(ℒ) ∩ α + c₁(𝒩) ∩ α = c₁(ℒ ⊗ 𝒩) ∩ α` and the vanishing `c₁(𝒪_X) ∩ α = 0`, and both
are already carried, by `Stacks.Chow.firstChernClassCapOfInvertible_tensorObj` and
`Stacks.Chow.firstChernClassCapOfInvertible_unit`. The sign rule proved here is a *consequence*
of those two clauses, not a clause of the tag — the same reading under which
`Stacks.Chow.firstChernCapStep_eq_neg_of_tensorObj_iso_unit` carries no attribute either. Nor is
this file Tag 0FA5: that tag is `c_i(E^∨) = (-1)^i c_i(E)` for every finite locally free `E` and
every `i`, and what is proved here is only its rank-one case. It is a prerequisite of Tag 0FAE,
and the tags it would be part of are registered where they are proved in full.

## References

* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 0B77](https://stacks.math.columbia.edu/tag/0B77)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}}

/-- **The dual of an invertible module is invertible**, in the spelling of invertibility that the
Chow machinery's first Chern class is stated at. This is Tag 01CT (2) and Tag 040A (2),
`Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf`, carried across
`Stacks.InvertibleBridge`. -/
@[ega "0 5.4.3" "special case"]
theorem isInvertible_dualSheaf (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (dualSheaf L) :=
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (dualSheaf L) :=
    Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.sheaf.obj X.ringCatSheaf.property L
  Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible

/-- **Tag 0B8K for the dual itself.** An invertible module tensored with its own dual is the
structure sheaf.

A tensor inverse `ℳ` of `ℒ` exists because `ℒ` is invertible, and `ℳ ≅ ℒ^∨` by Tag 0B8K; tensoring
that isomorphism with `ℒ` carries `ℒ ⊗ ℳ ≅ 𝒪_X` to `ℒ ⊗ ℒ^∨ ≅ 𝒪_X`. -/
@[ega "0 5.4.3" "partial", sga "6 VIII 3.5" "Sheaf-level clause"]
theorem nonempty_tensorObj_dualSheaf_iso_unit (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Nonempty (Scheme.Modules.tensorObj L (dualSheaf L) ≅
      SheafOfModules.unit X.ringCatSheaf) := by
  let hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit L).mp hL
  exact ⟨(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
    L).mapIso (Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.sheaf.obj
      X.ringCatSheaf.property L N e)).symm ≪≫ e⟩

variable (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- **The sign rule for the dual of an invertible module, on cycles.**
`c₁(ℒ^∨) ∩ α = -(c₁(ℒ) ∩ α)` for a cycle `α`, from the two clauses of Tag 02SP. -/
theorem firstChernClassCapOfInvertible_dualSheaf (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (α : CycleGroup C p (k + 1)) :
    haveI := isInvertible_dualSheaf L
    firstChernClassCapOfInvertible C p k (dualSheaf L) α =
      -firstChernClassCapOfInvertible C p k L α := by
  have := isInvertible_dualSheaf L
  obtain ⟨e⟩ := nonempty_tensorObj_dualSheaf_iso_unit L
  exact firstChernClassCapOfInvertible_eq_neg_of_tensorObj_iso_unit C p k L (dualSheaf L) e α

/-- **The sign rule for the dual of an invertible module, on Chow groups.**
`c₁(ℒ^∨) ∩ x = -(c₁(ℒ) ∩ x)` in `A_k(X)`. -/
theorem firstChernClassCapChow_dualSheaf (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (x : chowGroup C p (k + 1)) :
    haveI := isInvertible_dualSheaf L
    firstChernClassCapChow C k p (dualSheaf L) x = -firstChernClassCapChow C k p L x := by
  have := isInvertible_dualSheaf L
  induction x using QuotientAddGroup.induction_on with
  | H α => exact firstChernClassCapOfInvertible_dualSheaf C p k L α

/-- **The sign rule for the dual of an invertible module, on the Chern class cap products of
Tag 02U6.** `c_1(ℒ^∨) ∩ α = -(c_1(ℒ) ∩ α)` in `A_{k-1}(X)`. -/
theorem chernCap_one_dualSheaf (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (k : ℤ) (α : chowGroup C p k) :
    haveI := isInvertible_dualSheaf L
    haveI := isFiniteLocallyFreeOfRank_one_of_isInvertible L
    haveI := isFiniteLocallyFreeOfRank_one_of_isInvertible (dualSheaf L)
    chernCap C 1 p (dualSheaf L) k 1 α = -chernCap C 1 p L k 1 α := by
  have := isInvertible_dualSheaf L
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible (dualSheaf L)
  rw [chernCap_one_eq_invCap C p (dualSheaf L) k α, chernCap_one_eq_invCap C p L k α]
  exact firstChernClassCapChow_dualSheaf C p (k - 1) L (chowGroupCast C p (by omega) α)

/-- **The Chern class cap product in rank one depends only on the isomorphism class.** At rank
one the cap product is the first Chern class cap on Chow groups, where
`Stacks.Chow.firstChernClassCapChow_congr` is this statement. -/
theorem chernCap_one_congr (M N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1]
    (e : M ≅ N) (k : ℤ) (α : chowGroup C p k) :
    chernCap C 1 p M k 1 α = chernCap C 1 p N k 1 α := by
  have := isInvertible_of_rank_one M
  have := isInvertible_of_rank_one N
  rw [chernCap_one_eq_invCap C p M k α, chernCap_one_eq_invCap C p N k α]
  exact firstChernClassCapChow_congr C p (k - 1) e (chowGroupCast C p (by omega) α)

variable (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The first Chern class of a dual invertible module, as an identity of bivariant classes.**
For an invertible `𝒪_X`-module `ℒ`,

  `c₁(ℒ^∨) = -c₁(ℒ)`

in `A^1(X)`, the group of bivariant classes of degree `1` for `𝟙 X` of Tag 0B76.

Both sides satisfy the characterization of Tag 0B7H for `ℒ^∨`, which determines a bivariant
class: the cap operation of `-c₁(ℒ)` on a test scheme `g : T ⟶ X` is the negative of
`c₁(g^*ℒ) ∩ -`, and that is `c₁(g^*(ℒ^∨)) ∩ -` by `chernCap_one_dualSheaf` on `T`, once the dual
base-change isomorphism of Tag 0GMX identifies `g^*(ℒ^∨)` with `(g^*ℒ)^∨`. -/
theorem firstChernClass_dualSheaf (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    haveI := isInvertible_dualSheaf L
    firstChernClass C sX (dualSheaf L) = -firstChernClass C sX L := by
  have := isInvertible_dualSheaf L
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible (dualSheaf L)
  have hlf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    isFiniteLocallyFree_of_rank L 1
  refine eq_of_isChernClassBivariant C sX (dualSheaf L) 1 (gysinSystemOfInvertible C)
    (chernCap C 1) (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (dualSheaf L) 1) 1
    (isChernClassBivariant_chernClass C sX (dualSheaf L) 1 1) ?_
  intro T g _ k α
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank L 1 g
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (dualSheaf L) 1 g
  have := isInvertible_of_rank_one ((Scheme.Modules.pullback g).obj L)
  have := isInvertible_dualSheaf ((Scheme.Modules.pullback g).obj L)
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible
    (dualSheaf ((Scheme.Modules.pullback g).obj L))
  have hdual : chernCap C 1 (g ≫ sX) ((Scheme.Modules.pullback g).obj (dualSheaf L)) k 1 α =
      -chernCap C 1 (g ≫ sX) ((Scheme.Modules.pullback g).obj L) k 1 α := by
    -- the dual base-change isomorphism `g^*(ℒ^∨) ≅ (g^*ℒ)^∨` of Tag 0GMX
    rw [chernCap_one_congr C (g ≫ sX) ((Scheme.Modules.pullback g).obj (dualSheaf L))
      (dualSheaf ((Scheme.Modules.pullback g).obj L))
      (@asIso _ _ _ _ (pullbackDualMap g L) (pullbackDualMap_isIso g L hlf)) k α]
    exact chernCap_one_dualSheaf C (g ≫ sX) ((Scheme.Modules.pullback g).obj L) k α
  rw [BivariantClass.neg_cap, map_neg]
  exact (congrArg (fun z => -z) (isChernClassBivariant_chernClass C sX L 1 1 g k α)).trans
    hdual.symm

end Stacks.Chow.GenuineChern

end
