module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentabilityShrinkHoms
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksCore.Tactic.StacksAttribute

/-!
# The twisted inverse image of a quasi-compact quasi-separated morphism

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `Y` quasi-compact.
[Stacks, Tag 0A9E] says that `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint, the twisted
inverse image `f^×`, and proves it by verifying the hypotheses of Brown representability
([Stacks, Tag 0A8G]):

* `D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)` ([Stacks, Tag 06VT]);
* `D_QCoh(𝒪_X)` has direct sums ([Stacks, Tag 08DT]);
* `D_QCoh(𝒪_X)` is compactly generated ([Stacks, Tag 09IS]);
* `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)` ([Stacks, Tag 08D5] part (1)) and commutes with
  direct sums ([Stacks, Tag 08DZ]).

This file runs that argument with the last two inputs — [Stacks, Tag 08DZ] and
[Stacks, Tag 09IS] — taken as hypotheses, which is what the import order allows here. Both are
proved downstream, and the tag itself, with no hypothesis, is
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs` of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCompactGeneration.lean`.

The tag's own hypotheses are that `X` and `Y` be quasi-compact and quasi-separated *schemes*; what
is assumed below is that `Y` be quasi-compact and the *morphism* be quasi-compact and
quasi-separated, which is weaker. The source derives the latter from the former by
[Stacks, Tag 01KV] and [Stacks, Tag 03GI], and in Lean those two steps are the instances
`AlgebraicGeometry.quasiCompact_of_compactSpace` and
`AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace`, so the statements below apply in the
tag's situation by instance search with no further argument.

## Main results

* `qcqsRestrictedDerivedPushforward` — the restriction `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` with
  no quasi-coherence hypothesis supplied, at the locally small model.
* `isLeftAdjoint_qcqsRestrictedDerivedPushforward` — **[Stacks, Tag 0A9E]**, carrying
  [Stacks, Tag 08DZ] and [Stacks, Tag 09IS].
* `exists_isTriangulated_rightAdjoint_qcqsRestrictedDerivedPushforward` — the same with the
  adjoint exhibited as an exact functor and the adjunction as a triangulated one, which is what
  Brown representability produces and which the source also records.

## The carried hypotheses

The two statements below take the commutation of `Rf_*` with direct sums as an instance
hypothesis. That instance is **supplied**, in the module
`StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSumsLocallySmall`,
which cannot be imported here without a cycle; the forms of [Stacks, Tag 0A9E] with it already
discharged, and with compact generation as their only hypothesis, are
`isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isCompactlyGenerated` and its
exactness-carrying companion, in that module. So the only hypothesis that remains open is compact
generation.

**Compact generation of `D_QCoh(𝒪_X)`**, `CategoryTheory.Pretriangulated.IsCompactlyGenerated`
([Stacks, Tag 09SQ]), is the conjunction of [Stacks, Tag 09IS], that `D_QCoh(𝒪_X)` has a single
perfect generator, with [Stacks, Tag 09M1], that a perfect object of `D_QCoh(𝒪_X)` is compact.
Neither is proved in this repository; the same hypothesis is carried in the same shape by
`Stacks.Duality.Coherator.isLeftAdjoint_derivedQuasiCoherentι` ([Stacks, Tag 0CR0]).

**Commutation of `Rf_*` with direct sums**, [Stacks, Tag 08DZ], is proved at the locally small
model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model Brown
representability has to be run at: [Stacks, Tag 0A8G] asks for direct sums indexed by the
morphism universe of the category, and only there is that universe the `u` indexing the direct
sums of `𝒪_X`-modules. At `standard` the morphisms live in `Type (u + 1)` and the hypothesis is
false rather than unavailable, so
`preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward`, which is 08DZ at
`standard`, is a statement about a different category and does not discharge the instance. The
locally small form, `preservesColimitsOfShape_discrete_qcqsRestrictedDerivedPushforward`, does; it
rests on the transport of part (2) of [Stacks, Tag 08D5] off `standard`, which is
`Stacks.Duality.exists_isLE_derivedPushforward_obj_anyModel`.

Part (1) of [Stacks, Tag 08D5] is *not* in the same position: it has been transported, as
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`, so the restricted functor
below is formed with no hypothesis and is canonical.

Neither carried hypothesis is the conclusion in disguise. For `f` the identity the conclusion is
automatic whatever the scheme, while both hypotheses are theorems about `X` and `f`.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09SQ](https://stacks.math.columbia.edu/tag/09SQ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated Opposite

universe u

namespace Stacks.Duality.DerivedPushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f] [CompactSpace Y]

/-- **The restriction of `Rf_*` to `D_QCoh`** for a quasi-compact quasi-separated morphism with
quasi-compact target, at the locally small model, with no quasi-coherence hypothesis supplied: it
is discharged by `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`, part (1) of
[Stacks, Tag 08D5]. This is the functor `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` whose right adjoint
[Stacks, Tag 0A9E] produces. -/
abbrev qcqsRestrictedDerivedPushforward :
    Stacks.Duality.quasiCoherentDerivedCategory X ⥤ Stacks.Duality.quasiCoherentDerivedCategory Y :=
  Stacks.Duality.quasiCoherentDerivedPushforward f
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)

/-- A compactly generated `D_QCoh(𝒪_X)` has a generating family whose corepresentable functors
preserve coproducts. -/
private theorem exists_generatorFamily_of_isCompactlyGenerated
    (hX : IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory X)) :
    ∃ (ι : Type u) (E : ι → Stacks.Duality.quasiCoherentDerivedCategory X),
      (∀ (i : ι) (α : Type u),
        PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))) ∧
      ∀ K, ((ofObj E).shiftClosure ℤ).rightOrthogonal K → IsZero K := by
  obtain ⟨ι, E, hcompact, hgen⟩ := hX
  let : ∀ i : ι, IsCompactObject.{u} (E i) := hcompact
  exact ⟨ι, E, fun i α => preservesCoproducts_preadditiveCoyoneda_of_isCompactObject (E i) α,
    hgen⟩

omit [QuasiCompact f] [QuasiSeparated f] [CompactSpace ↥Y] in
/-- The Stacks proof of [Stacks, Tag 0A9E] for the restriction of `Rf_*` attached to an arbitrary
proof `hpush` that `Rf_*` preserves quasi-coherence of cohomology, carrying [Stacks, Tag 08DZ] as
an instance and [Stacks, Tag 09IS] as the hypothesis `hX`.

The tagged form, in which `hpush` is discharged, is
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward`. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_of_isCompactlyGenerated
    (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward f hpush)]
    (hX : IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory X)) :
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint := by
  obtain ⟨ι, E, h, hgen⟩ := exists_generatorFamily_of_isCompactlyGenerated hX
  have := h
  exact isLeftAdjoint_quasiCoherentDerivedPushforward_of_generatorFamily f hpush E hgen

omit [QuasiCompact f] [QuasiSeparated f] [CompactSpace ↥Y] in
/-- The exactness-carrying form of
`isLeftAdjoint_quasiCoherentDerivedPushforward_of_isCompactlyGenerated`: Brown representability
returns the right adjoint as an exact functor and the adjunction as a triangulated one. -/
theorem exists_isTriangulated_rightAdjoint_quasiCoherentDerivedPushforward_of_isCompactlyGenerated
    (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward f hpush)]
    (hX : IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory X)) :
    ∃ (a : _) (adj : Stacks.Duality.quasiCoherentDerivedPushforward f hpush ⊣ a)
      (_ : a.CommShift ℤ), adj.IsTriangulated := by
  obtain ⟨ι, E, h, hgen⟩ := exists_generatorFamily_of_isCompactlyGenerated hX
  have := h
  have hsum := hasCoproducts_quasiCoherentDerivedCategory X
  exact exists_isTriangulated_rightAdjoint_of_compactlyGenerated
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush) E hgen

/-- **The Stacks proof of Tag 0A9E, with Tags 08DZ and 09IS as hypotheses.** Let `f : X ⟶ Y` be a
quasi-compact and quasi-separated morphism of schemes with `Y` quasi-compact. Suppose
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with
direct sums ([Stacks, Tag 08DZ]) and `D_QCoh(𝒪_X)` is compactly generated ([Stacks, Tag 09IS]).
Then `Rf_*` has a right adjoint — the twisted inverse image `f^×`.

The functor is the canonical `Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward`
and not one depending on a supplied proof: that `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`
at all is part (1) of [Stacks, Tag 08D5] and is discharged. So are the other two inputs of the
source's proof that are not hypotheses here: that `D_QCoh` is a triangulated subcategory on
either side and that the restriction of `Rf_*` to it is exact ([Stacks, Tag 06VT], the instances
of `StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/Exactness.lean`), and that
`D_QCoh(𝒪_X)` has direct sums ([Stacks, Tag 08DT]).

The two that remain are hypotheses here only because of the import order: both are proved in
files that import this one. [Stacks, Tag 0A9E] itself, with no hypothesis, is
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs` of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCompactGeneration.lean`. -/
theorem isLeftAdjoint_qcqsRestrictedDerivedPushforward
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α) (qcqsRestrictedDerivedPushforward f)]
    (hX : IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory X)) :
    (qcqsRestrictedDerivedPushforward f).IsLeftAdjoint :=
  isLeftAdjoint_quasiCoherentDerivedPushforward_of_isCompactlyGenerated f _ hX

/-- **The Stacks proof of Tag 0A9E with the adjoint exhibited as exact**, under the same two
hypotheses. For a quasi-compact and quasi-separated `f : X ⟶ Y` with `Y` quasi-compact, with
`Rf_*` commuting with direct sums and `D_QCoh(𝒪_X)` compactly generated, there is a functor
`a : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`, an adjunction `Rf_* ⊣ a`, and a shift structure on `a` for
which that adjunction is triangulated.

This is the extra information Brown representability returns and that the source records
alongside existence;
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward` is the tag's
own conclusion. -/
theorem exists_isTriangulated_rightAdjoint_qcqsRestrictedDerivedPushforward
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α) (qcqsRestrictedDerivedPushforward f)]
    (hX : IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory X)) :
    ∃ (a : _) (adj : qcqsRestrictedDerivedPushforward f ⊣ a) (_ : a.CommShift ℤ),
      adj.IsTriangulated :=
  exists_isTriangulated_rightAdjoint_quasiCoherentDerivedPushforward_of_isCompactlyGenerated
    f _ hX

end Stacks.Duality.DerivedPushforward

end
