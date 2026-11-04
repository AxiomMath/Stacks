module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageAffine.AffineMorphismVanishing
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Towards Stacks 0EX4: the quasi-coherence half, at the source's own indexing

Stacks Tag 0EX4 carries two distinct labels. The **quasi-coherence** one asserts that for a
proper `f : X ⟶ Y` and a quasi-coherent `F : X.Modules`, every `R ⁱ f_* F`, `i : ℕ`, is
quasi-coherent; the **finite type** one asserts that if moreover the fibres of `f` have dimension
at most `d` and `F` is of finite type, then `R ᵈ f_* F` is of finite type. Both are stated with
Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`.

This file supplies the indexing transfer that the quasi-coherence half needs, and the case of it
that is unconditional at this revision. No `stacks` attribute is attached: each of the two labels
is a single assertion quantified over **all** degrees, so a result in one degree range, or for one
class of morphism, is not a covering set for it.

## Main results

* `Stacks.AlgebraicGeometry.ProperHigherDirectImageQcoh.isQuasicoherent_rightDerived_iff`:
  quasi-coherence of the `ℕ`-indexed `R ⁱ f_* F` is quasi-coherence of the `ℤ`-indexed `R ⁱ f_* F`,
  for an arbitrary morphism of schemes and in every degree. This is the whole distance between the
  indexing this library's higher-direct-image theory is stated in and the indexing Tag 0EX4 is
  stated in.
* `ProperHigherDirectImageQcoh.isQuasicoherent_rightDerived_of_isAffineHom`: **the
  quasi-coherence assertion of Tag 0EX4 for an affine morphism, in every degree `i : ℕ`,
  unconditionally.** Affine is not proper, so this does not close the label; it is the statement
  the general case is assembled from.

## What the quasi-coherence label still needs

Exactly one input: **the quasi-compact quasi-separated case of [Stacks, Tag 01XJ] part (1) in
positive degrees**, that is, `R ᵖ f_* F` quasi-coherent for `p > 0` and `f` qcqs. A proper
morphism is quasi-compact and separated, hence qcqs, so that statement plus
`isQuasicoherent_rightDerived_iff` closes the label. A fixed-string search for a Tag 01XJ
attribute over the whole tree returns nothing, and
`StacksFrontier/AlgebraicGeometry/QcohShortExact/` holds only its inputs — the Mayer–Vietoris short
exact sequences (`StacksFrontier/AlgebraicGeometry/QcohShortExact/MayerVietorisInjective.lean`) and the quasi-coherence extension lemmas
(`StacksFrontier/AlgebraicGeometry/QcohShortExact/QcohExtension.lean`) — not the induction over a finite affine cover that assembles the affine
case into the general one.

Three inputs the general case rests on are **available**:

* [Stacks, Tag 01EW] in the form this chain consumes — the vanishing of the higher cohomology of
  a quasi-coherent module on an affine open — is
  `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`
  (`StacksFrontier/AlgebraicGeometry/AffineCohomologyGlue/AffineOpenVanishing.lean`, tagged for
  Tag 01XB), and its file carries no live open goal.
* [Stacks, Tag 01LC] **for a quasi-compact quasi-separated morphism** is
  `Stacks.AlgebraicGeometry.RelativeMayerVietoris.pushforward_isQuasicoherent`
  (`StacksFrontier/AlgebraicGeometry/RelativeMayerVietoris/Qcoh.lean`, tagged for Tag 01LC),
  with `[QuasiCompact f] [QuasiSeparated f]` and nothing else.
* The comparison of the two indexings is `Stacks.DerivedIndexing.rightDerivedIso`
  (`StacksFrontier/Homology/DerivedIndexing/Basic.lean`), a natural isomorphism
  `F.rightDerived n ≅ F.rightDerivedPlus (n : ℤ)` with no boundedness or acyclicity hypothesis.
  It is what this file runs on.

## Implementation notes

The degree-`0` theory for the `ℕ`-indexed functor, and the stability of finite type under
isomorphism, are in `StacksFrontier/AlgebraicGeometry/DerivedPushforward/Basic.lean` and are not
repeated here. Nothing below touches the finite-type label, whose own floor is separate: for an
affine morphism the degree-`0` direct image of a finite-type module is not of finite type (take
`𝔸¹ ⟶ Spec k`), so the finite-type assertion has no unconditional affine case to be assembled
from, and the properness hypothesis is load-bearing there in a way it is not here.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperHigherDirectImageQcoh

/-! The `ℤ`-indexed `rightDerivedPlus` is taken with respect to the standard derived category,
which is the instance the higher-direct-image theory is stated under; `Scheme.Modules` is
a `def`, so it is not found as an instance argument and is installed locally here exactly as in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageAffine/AffineMorphismVanishing.lean`. -/

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (i : ℕ)

/-! ### The indexing transfer -/

/-- **Quasi-coherence of the `ℕ`-indexed higher direct image is quasi-coherence of the
`ℤ`-indexed one.** No hypothesis on the morphism and none on the degree: the two functors are
naturally isomorphic by `Stacks.DerivedIndexing.rightDerivedIso`, and quasi-coherence is stable
under isomorphism. This is the transfer the `ℕ`-indexed statement of Tag 0EX4 needs in order to
consume this library's `ℤ`-indexed higher-direct-image theory. -/
theorem isQuasicoherent_rightDerived_iff :
    (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsQuasicoherent ↔
      (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsQuasicoherent :=
  ⟨fun h => (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) i).app F) h,
    fun h => (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) i).app F).symm h⟩

/-! ### The affine case of the quasi-coherence assertion -/

/-- **The quasi-coherence assertion of Stacks Tag 0EX4 for an affine morphism, in every degree.**
For `f : X ⟶ S` affine and `F` quasi-coherent, `R ⁱ f_* F` is quasi-coherent for every `i : ℕ`,
at Mathlib's `ℕ`-indexed `rightDerived`.

This is [Stacks, Tag 01XJ] part (1) for an affine morphism — formalized `ℤ`-indexed as
`Stacks.AlgebraicGeometry.HigherDirectImageAffine.isQuasicoherent_higherDirectImage_of_isAffineHom`
— carried across the indexing by
`Stacks.AlgebraicGeometry.ProperHigherDirectImageQcoh.isQuasicoherent_rightDerived_iff`. An affine
morphism is not proper, so this is not the label; it is the unconditional case the general one is
assembled from. -/
instance isQuasicoherent_rightDerived_of_isAffineHom [IsAffineHom f] [F.IsQuasicoherent] :
    (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsQuasicoherent :=
  (isQuasicoherent_rightDerived_iff f F i).mpr
    (HigherDirectImageAffine.isQuasicoherent_higherDirectImage_of_isAffineHom f F (i : ℤ))

end Stacks.AlgebraicGeometry.ProperHigherDirectImageQcoh

end
