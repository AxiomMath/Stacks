module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic

/-!
# Finite type of the higher direct images along a finite morphism

Let `f : X ⟶ S` be a finite morphism of schemes and let `F` be a quasi-coherent `𝒪_X`-module of
finite type. This file proves that `Rⁿ f_* F` is of finite type **in every degree `n`**, with no
hypothesis on `S` whatsoever, and draws the consequence for [Stacks, Tag 0EX4].

The two degree ranges are proved by completely different inputs, and each uses strictly less than
the statement as a whole:

* for `n > 0` the higher direct image **vanishes**, by [Stacks, Tag 01XC], and a zero sheaf of
  modules is of finite type. This needs only that `f` be **affine**, and needs nothing at all of
  `F` beyond quasi-coherence — neither finiteness of `f` nor finite type of `F` is used;
* for `n = 0` the higher direct image is the direct image `f_* F`, and the pushforward of a
  quasi-coherent module of finite type along a finite morphism is of finite type, which is the
  finite-type half of [Stacks, Tag 01Y6]. Here finiteness of `f` is genuinely needed: an affine
  morphism does not have finite-type pushforward in general.

Both hypothesis splits above were confirmed by failing to typecheck when the hypothesis is
dropped, so neither is decoration.

## Relation to [Stacks, Tag 0EX4]

Tag 0EX4 asserts that for `f` proper all of whose fibres have dimension at most `d`, and `F`
quasi-coherent of finite type, `R ᵈ f_* F` is quasi-coherent of finite type. A proper morphism
whose fibres all have dimension at most `0` is finite (Zariski's main theorem, [Stacks, Tag
02OH]), so the results here give the tag's finite-type conclusion **for every degree `d`** on
that class of morphisms, where
`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/Basic.lean` gives it for `d = 0` only.

That is a strengthening in the degree and **not** a proof of the tag: for `d ≥ 1` the hypothesis
used here (`dimension ≤ 0`) is strictly stronger than the tag's (`dimension ≤ d`), and in the
range where it is stronger the conclusion is about a sheaf that vanishes. The tag's content at a
tight fibre-dimension bound `d ≥ 1` is untouched over a base that is not locally Noetherian; it
rests on the finiteness theorem for the cohomology of a proper morphism over a Noetherian base,
[Stacks, Tag 02O6], which is
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology` and carries no hypothesis.
Over a locally Noetherian base the tag's finite-type clause follows from it in every degree:
`…TopDegreeFiniteType.isFiniteType_rightDerived_of_isProper_of_isLocallyNoetherian`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_rightDerived_succ_of_isAffineHom`:
  for `f` affine and `F` quasi-coherent, `R ⁿ ⁺ ¹ f_* F` is of finite type, because it is zero.
* `Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_rightDerived_of_isFinite`: for `f`
  finite and `F` quasi-coherent of finite type, `Rⁿ f_* F` is of finite type in every degree.
* `isFiniteType_rightDerived_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero`, in the
  same namespace: the finite-type conclusion of [Stacks, Tag 0EX4] in every degree, for a proper
  morphism all of whose fibres have dimension at most `0`.

## Implementation notes

**No `@[stacks 0EX4]` attribute is attached to anything here**, for the reason given above: the
fibre-dimension hypothesis is strengthened relative to the tag. The quasi-coherence clause of the
tag carries its own `@[stacks 0EX4 "quasi-coherence"]` in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageQcqs/Qcqs.lean`; the finite-type clause
carries one over a locally Noetherian base in
`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/NoetherianBaseUnconditional.lean`.

In this namespace `rightDerived` always means Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`, matching the existing declarations in `Basic.lean`. Note
that `StacksFrontier/AlgebraicGeometry/AffineCohomologyVanishing/Basic.lean` uses the opposite
convention: the name `isZero_rightDerived_pushforward_of_isAffineHom` there is a statement about
the `ℤ`-indexed `rightDerivedPlus`. The `ℕ`-indexed form of [Stacks, Tag 01XC] consumed here is
`Stacks.Cohomology.Affine.HigherDirectImage.isZero_rightDerivedNat_pushforward_of_isAffineHom`.

`Stacks.SheafOfModules.isFiniteType_of_isZero` is applied with its module argument `M` supplied
by name. Without it the three universe parameters of the conclusion default to `0` before they
are unified against the expected type, and the application fails with
`SheafOfModules.IsFiniteType.{0, 0, 0} ?m` against `…IsFiniteType.{u, u, u}`. What does not
help: wrapping the term in `exact`, and `_root_`-qualifying the name — so this is not namespace
capture, it is an argument that must be given for the universes to be determined.
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean:343` pins the universe directly
instead, which is the same obstacle seen from the declaring file.

`isFiniteType_rightDerived_of_isFinite` subsumes
`…TopDegreeFiniteType.rightDerived_pushforward_isFiniteType_of_isProper_of_fiber_dimension_le_zero`
of `Basic.lean`, which is its degree-`0` case composed with Zariski's main theorem; that
declaration is left in place because it is the statement of the tag's `d = 0` instance and is
cited as such.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

/-! ### The positive degrees, for an affine morphism -/

/-- **In a positive degree the higher direct image along an affine morphism is of finite type,
because it vanishes.** This is [Stacks, Tag 01XC] together with the fact that a zero sheaf of
modules is of finite type.

Neither finiteness of `f` nor finite type of `F` is used: affineness of `f` and quasi-coherence
of `F` are the whole input. -/
theorem isFiniteType_rightDerived_succ_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived (n + 1)).obj F).IsFiniteType :=
  Stacks.SheafOfModules.isFiniteType_of_isZero
    (M := ((Scheme.Modules.pushforward f).rightDerived (n + 1)).obj F)
    (Stacks.Cohomology.Affine.HigherDirectImage.isZero_rightDerivedNat_pushforward_of_isAffineHom
      f F (n + 1) (Nat.succ_pos n))

/-! ### Every degree, for a finite morphism -/

/-- **The higher direct images of a quasi-coherent module of finite type along a finite morphism
are of finite type in every degree.** In degree `0` this is the finite-type half of
[Stacks, Tag 01Y6]; in positive degrees the module vanishes by [Stacks, Tag 01XC], a finite
morphism being affine.

No hypothesis on `S` is needed — in particular no Noetherian hypothesis. The coherence analogue
`…FiniteDirectImageCoherent.isCoherent_rightDerived_of_isFinite` does need `IsLocallyNoetherian`
on the target, since coherence is finite type plus quasi-coherence only over such a scheme. -/
theorem isFiniteType_rightDerived_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFiniteType := by
  rcases n with _ | m
  · exact (DerivedPushforward.isFiniteType_rightDerived_zero_iff f F).2
      (isFiniteType_pushforward_of_isFinite f F)
  · exact isFiniteType_rightDerived_succ_of_isAffineHom f F m

/-! ### The finite-type conclusion of Tag 0EX4 in every degree, for zero-dimensional fibres -/

/-- **The finite-type conclusion of [Stacks, Tag 0EX4] in every degree, for a proper morphism all
of whose fibres have dimension at most `0`.** Such a morphism is finite by Zariski's main theorem
([Stacks, Tag 02OH]), as
`AlgebraicGeometry.isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero`, and then
every degree is covered by `isFiniteType_rightDerived_of_isFinite`.

**No `@[stacks 0EX4]` attribute is attached.** For `d ≥ 1` the hypothesis here is strictly
stronger than the tag's, which bounds the fibre dimension by `d` rather than by `0`. -/
theorem isFiniteType_rightDerived_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (d : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  have : IsFinite f :=
    AlgebraicGeometry.isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero f hdim
  isFiniteType_rightDerived_of_isFinite f F d

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
