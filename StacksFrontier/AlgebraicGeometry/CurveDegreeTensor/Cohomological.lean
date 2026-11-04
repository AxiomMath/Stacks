module

public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Basic
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.IntegralDevissage
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneTensorMonoid
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantStalkRank
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CoherentFiniteness
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0AYX]: the degree of a tensor product on a proper curve

[Stacks, Tag 0AYX] computes the degree of a tensor product of locally free modules of constant
finite rank on a proper scheme of dimension at most one over a field:

`deg(ℰ ⊗ 𝒱) = rank(ℰ) · deg(𝒱) + rank(𝒱) · deg(ℰ)`.

`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_devissage` proves this on a proper curve
from five hypotheses, and all five are discharged here. The dévissage of [Stacks, Tag 01YH] and
clause (5) of [Stacks, Tag 0AYT] come from the library's form of [Stacks, Tag 0AYV], namely
`exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_h02O6`; the rank of
the tensor product is the rank computation below; and the two remaining hypotheses, both
instances of [Stacks, Tag 02O6] over a field, are
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`, the form of that
tag over a field base that
`StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/OverFieldProper.lean` derives from
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`. So the statement below
carries **no finiteness hypothesis at all**.

The rank of the tensor product is obtained through the fibre rank rather than by trivializing
the tensor product directly. A tensor product of finite locally free modules is finite locally
free (`AlgebraicGeometry.isFiniteLocallyFree_tensorObj`, [Stacks, Tag 0FDK]), its stalks are
therefore free, and the comparison `(ℰ ⊗ 𝒱)_x ≅ ℰ_x ⊗ 𝒱_x` of [Stacks, Tag 01CB] makes the
fibre rank multiplicative
(`AlgebraicGeometry.CoherentReflexive.finrank_stalk_tensorSheaf`). That constant fibre rank is
turned back into a rank by
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq`, the form of
[Stacks, Tag 01C9] that reads the rank off every point of the whole scheme.

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf`: **the rank of a tensor product**,
  `rank(ℰ ⊗ 𝒱) = rank(ℰ) · rank(𝒱)`.
* `curveDegree_tensorSheaf_eq_add`: **[Stacks, Tag 0AYX] on a proper curve**, with no
  hypothesis.

## Implementation notes

**What the tagged statement assumes that Tag 0AYX does not.** One thing, recorded in the
attribute's clause string: `[IsCurve k f]`, a proper *curve*, whereas Tag 0AYX is stated for a
proper scheme of dimension at most one. That hypothesis is removed in
`StacksFrontier/AlgebraicGeometry/CurveDegreeTensor/Devissage.lean`, where
`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one` is the whole tag
and carries the bare attribute; the statement below is the curve case it rests on, reached there
through the dévissage of [Stacks, Tag 01YG] rather than through the component formula of
[Stacks, Tag 0AYW]. The library's form of [Stacks, Tag 0AYV]
already carries the curve hypothesis, so nothing is lost by it here.

**[Stacks, Tag 02O6] is not assumed.** It is a theorem of this library over a field base, so
the finiteness hypothesis it would otherwise contribute is discharged.
The two uses are the two instances [Stacks, Tag 0AYV] needs, at a coherent module supported in a
proper closed subset and at the structure sheaf.

The dimension bound `hdim` is kept as an explicit argument because
`AlgebraicGeometry.curveDegree` takes one; on a curve it is implied by
`AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one`, and the two proofs of it are
interchangeable by proof irrelevance. That interchange is what lets the equation coming out of
[Stacks, Tag 0AYV] — which is stated with the derived proof — be rebound with a declared type at
the `hdim` spelling instead of rewritten.

**Spelling of the tensor product.** Everything here is stated with
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X.toRingedSpace`, the spelling of
[Stacks, Tag 0AYV] and of `AlgebraicGeometry.Scheme.Modules.tensorObjRingedSpace`, so no
transport of spelling is needed. `AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_devissage`
is stated with `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` instead; the two are the
same term, and the choice there is explained in that file's implementation notes.

## References

* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The rank of a tensor product is the product of the ranks.** For `ℰ` and `𝒱` finite locally
free of constant ranks `m` and `n`, the tensor product `ℰ ⊗ 𝒱` is finite locally free of
constant rank `m · n`.

A tensor product of finite locally free modules is finite locally free by
[Stacks, Tag 0FDK], so it has free stalks, and the stalk comparison
`(ℰ ⊗ 𝒱)_x ≅ ℰ_x ⊗ 𝒱_x` of [Stacks, Tag 01CB] together with
`Module.finrank_tensorProduct` makes the fibre rank multiplicative. The fibre ranks of the
factors are `m` and `n` at every point, so the fibre rank of the tensor product is constantly
`m · n`, and
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq`
converts that back into a rank. -/
public theorem SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf
    (X : Scheme.{u}) (E V : X.Modules) (m n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V n] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V)))
      (m * n) := by
  -- The two factors and their tensor product are finite locally free, in both of the two
  -- spellings of that condition carried by this repository.
  have hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E :=
    @Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree X E
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E m)
  have hV : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) V :=
    @Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree X V
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree V n)
  have hT : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) :=
    isFiniteLocallyFree_tensorObj E V
  have hTflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) :=
    Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree _
  -- The three sets of stalk data: finite type and free stalks for the factors and for the
  -- tensor product.
  obtain ⟨hEft, hEfree, -⟩ :=
    Scheme.Modules.isFiniteType_and_free_stalks_and_isLocallyConstant_fiberRank E
  obtain ⟨hVft, hVfree, -⟩ :=
    Scheme.Modules.isFiniteType_and_free_stalks_and_isLocallyConstant_fiberRank V
  obtain ⟨hTft, hTfree, -⟩ :=
    Scheme.Modules.isFiniteType_and_free_stalks_and_isLocallyConstant_fiberRank
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V)))
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V)))
    (m * n) fun x => ?_
  have key : Scheme.Modules.fiberRank
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) x =
      Scheme.Modules.fiberRank E x * Scheme.Modules.fiberRank V x := by
    rw [Scheme.Modules.fiberRank_eq_finrank_stalk _ x (hTfree x),
      Scheme.Modules.fiberRank_eq_finrank_stalk E x (hEfree x),
      Scheme.Modules.fiberRank_eq_finrank_stalk V x (hVfree x)]
    exact CoherentReflexive.finrank_stalk_tensorSheaf E V x _ _ _
      (Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace E.val x)
      (Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace V.val x)
      (Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace _ x)
      (hEfree x) (hVfree x)
  rw [key, Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank E m x,
    Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank V n x]

/-- **[Stacks, Tag 0AYX] on a proper curve.** For `ℰ` and `𝒱` finite locally free of constant
ranks `n` and `m` on a proper curve over a field,

`deg(ℰ ⊗ 𝒱) = m · deg(ℰ) + n · deg(𝒱)`.

**No hypothesis beyond the source's own**, apart from the curve hypothesis discussed in the
module docstring. The rank of the tensor product is
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf`, and the two instances
of [Stacks, Tag 02O6] over a field that [Stacks, Tag 0AYV] needs are supplied by
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`.

The proof is the arithmetic of [Stacks, Tag 0AYX]: the Euler characteristic of `ℰ ⊗ 𝒱` is
`m · deg(ℰ) + n · χ(𝒱)` by [Stacks, Tag 0AYV], whose rank input is the fibre rank of `𝒱` at the
generic point and hence `m`; every degree is then unfolded into Euler characteristics by
`AlgebraicGeometry.curveDegree_eq_eulerCharacteristic_sub`, where the identity is linear
arithmetic. -/
@[stacks 0AYX "on a proper curve; the whole tag, on a proper scheme of dimension at most one, \
is AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one"]
public theorem curveDegree_tensorSheaf_eq_add
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E V : X.Modules) (n m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V m] :
    @curveDegree k _ X f _ hdim
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) (n * m)
        (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m) =
      (m : ℤ) * curveDegree k f hdim E n + (n : ℤ) * curveDegree k f hdim V m := by
  have hcV : SheafOfModules.IsCoherent V :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f V m
  have hO : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f _ 1
  obtain ⟨hT, hchi⟩ :=
    @exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_h02O6
      k _ X f _ _ E n _
      (fun G _ _ _ _ hG p => forall_finiteDimensional_cohomologyOverField_of_isProper k f G hG p)
      (fun p => forall_finiteDimensional_cohomologyOverField_of_isProper k f _ hO p)
      V hcV
  rw [Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank V m
    (genericPoint X)] at hchi
  have hchi' : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) hT =
      (m : ℤ) * @curveDegree k _ X f _ hdim E n ‹_› +
        (n : ℤ) * eulerCharacteristic k f V := hchi
  rw [@curveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim _ (n * m)
      (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m) hT hO,
    @curveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim V m ‹_› hcV hO, hchi']
  push_cast
  ring

end AlgebraicGeometry

end
