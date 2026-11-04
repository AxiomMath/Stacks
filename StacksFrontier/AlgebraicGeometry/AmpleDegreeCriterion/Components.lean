module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Curve
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteSurjective.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.QuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
import StacksCore.Tactic.StacksAttribute

/-!
# Ampleness and the degrees on the one-dimensional components

[Stacks, Tag 0B5Y] says: let `k` be a field, let `X` be a proper scheme over `k` of dimension at
most one, let `𝓛` be an invertible `𝒪_X`-module and let `C₁, …, C_t ⊆ X` be the irreducible
components of dimension one. Then

1. `𝓛` is ample

if and only if

2. `deg(𝓛|_{C_i}) > 0` for every `i`.

This file proves the implication (1) ⟹ (2), on every closed subscheme of `X` that is a proper
curve over `k` — in particular on each one-dimensional irreducible component with its reduced
induced structure.

## Main definitions

* `AlgebraicGeometry.HasCurveDegreePositivityInputs`: the four inputs that the proved forward
  direction of [Stacks, Tag 0B5X] carries on a proper curve, bundled so that a statement about a
  closed subcurve of `X` can name them once.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isAmple_modulePullback_of_isClosedImmersion`: the restriction
  of an ample invertible module to a closed subscheme is ample. Unconditional.
* `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_isClosedImmersion`: **the
  implication (1) ⟹ (2) of [Stacks, Tag 0B5Y]**, for an arbitrary closed immersion `i : C ⟶ X`
  whose source is a proper curve over `k`.
* `AlgebraicGeometry.invertibleCurveDegree_subscheme_pos_of_isAmple`: the same at the irreducible
  components of `X` with their reduced induced structure, which is the tag's own indexing.

## The route, and why it is the source's

The source forms the finite surjective morphism
`g : C₁ ⨿ … ⨿ C_t ⨿ x₁ ⨿ … ⨿ x_r ⟶ X` from the one-dimensional components and the isolated
closed points, reads ampleness of `𝓛` as ampleness of `g^*𝓛` through [Stacks, Tag 0B5V], and
concludes by [Stacks, Tag 0B5X] on each `C_i`.

For the implication (1) ⟹ (2) the coproduct is unnecessary: only the implication `⟹` of
[Stacks, Tag 0B5V] is used, and that implication is proved unconditionally for any finite
morphism as `Stacks.AmpleFiniteSurjective.isAmple_modulePullback_of_isFinite`. A closed immersion
is finite (Mathlib's `AlgebraicGeometry.IsClosedImmersion.instIsFinite`), so the restriction of
`𝓛` to each component is ample directly, and [Stacks, Tag 0B5X]'s forward direction —
`AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_devissage` — finishes.

## What is not covered, and why

**The implication (2) ⟹ (1) is not covered.** It is the one that needs the coproduct and, with
it, the *converse* implication of [Stacks, Tag 0B5V], and that converse is not in this library:
`StacksFrontier/AlgebraicGeometry/AmpleFiniteSurjective/Basic.lean` carries the Tag 0B5V attribute
under the scoped clause "the implication `L` ample ⟹ `f^* L` ample" only, and records the
converse as owed. Its own route runs through [Stacks, Tag 0B5U], and that tag is no longer the
obstruction: every one of its implications is proved in
`StacksFrontier/AlgebraicGeometry/AmpleDegreeCriterion/CohomologicalCriterion.lean`, the implication
(1) ⟹ (2) being clause (4) of [Stacks, Tag 0B5T], proved in `../ProperAmpleCohomology/Basic.lean`.
What the converse of Tag 0B5V needs beyond Tag 0B5U is the transport of the vanishing along the
finite surjection, and that is what `../AmpleFiniteSurjective/Basic.lean` records as owed.

## Implementation notes

**The four carried inputs are bundled.** `AlgebraicGeometry.HasCurveDegreePositivityInputs`
is the conjunction of the hypothesis list of
`AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_devissage`: the dévissage of
[Stacks, Tag 01YH], [Stacks, Tag 02O6] at the coherent modules supported in a proper closed
subset and at the structure sheaf, and [Stacks, Tag 0B40] part 2. They are carried rather than
proved because the forward direction of [Stacks, Tag 0B5X] carries them; bundling them keeps the
statements below readable and makes discharging them a substitution.

**The component is a curve by hypothesis.** `AlgebraicGeometry.IsCurve` asks for a variety of
dimension one, so a one-dimensional irreducible component taken with its reduced induced
structure is a curve over `k` — it is integral by
`StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible`, separated by
`StacksTag09NX.isSeparated_of_isClosedImmersion` and of finite type over `k` because `X` is. The
instance is taken as a binder rather than assembled, which is also what selects the
*one-dimensional* components: `IsCurve.topologicalKrullDim_eq_one` is exactly the tag's
`dim C_i = 1`.

## References

* [Stacks Project, Tag 0B5Y](https://stacks.math.columbia.edu/tag/0B5Y)
* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0B5V](https://stacks.math.columbia.edu/tag/0B5V)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules (nonvanishingLocus)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)
-- (open removed: its only name was the merged moduleGlobalSections)
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **The four inputs that the forward direction of [Stacks, Tag 0B5X] carries on a proper
curve**, as a single proposition about `(k, g, hdim, M)`:

* the dévissage of [Stacks, Tag 01YH] for a two-out-of-three property of coherent modules;
* [Stacks, Tag 02O6] at the coherent modules supported in a proper closed subset;
* [Stacks, Tag 02O6] at the structure sheaf;
* [Stacks, Tag 0B40] part 2, in the form "an invertible module with a section vanishing
  somewhere but not everywhere has positive degree", for the positive tensor powers of `M`.

This is literally the hypothesis list of
`AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_devissage`, and
`AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_inputs` is that lemma consuming it. -/
public def HasCurveDegreePositivityInputs (k : Type u) [Field k] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsCurve k g] [IsProper g] (hdim : topologicalKrullDim C ≤ 1)
    (M : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M] : Prop :=
  (∀ P : C.Modules → Prop,
      (∀ T : ShortComplex C.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : C.Modules) (Z : Set C), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit C.ringCatSheaf) →
      ∀ G : C.Modules, SheafOfModules.IsCoherent G → P G) ∧
  (∀ (G : C.Modules) (Z : Set C), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ m, FiniteDimensional k (cohomologyOverField k g G m)) ∧
  (∀ m, FiniteDimensional k
      (cohomologyOverField k g (SheafOfModules.unit C.ringCatSheaf) m)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ s : (tensorPower C.toRingedSpace.presheaf
        (structureSheafRing C.toRingedSpace).property M (n : ℤ)).sections,
      (∃ x : C, x ∈ nonvanishingLocus (X := C.toLocallyRingedSpace.toRingedSpace)
        (tensorPower C.toRingedSpace.presheaf
          (structureSheafRing C.toRingedSpace).property M (n : ℤ)) s) →
      nonvanishingLocus (X := C.toLocallyRingedSpace.toRingedSpace)
        (tensorPower C.toRingedSpace.presheaf
          (structureSheafRing C.toRingedSpace).property M (n : ℤ)) s ≠ Set.univ →
      0 < @invertibleCurveDegree k _ C g _ hdim
        (tensorPower C.toRingedSpace.presheaf
          (structureSheafRing C.toRingedSpace).property M (n : ℤ))
        (tensorPower_isInvertible C.toRingedSpace.presheaf
          (structureSheafRing C.toRingedSpace).property M (n : ℤ)))

/-- **The forward direction of [Stacks, Tag 0B5X], consuming the bundled inputs.** An ample
invertible module on a proper curve over a field has positive degree.

This is `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_devissage` with its four
carried inputs packaged as `hin`. None of them mentions ampleness or the degree of `M` itself,
so this half of the tag is proved outright from four named tag-level debts; the full
biconditional, whose converse adds a fifth, is
`AlgebraicGeometry.isAmple_iff_degree_pos` of `./Curve.lean`. -/
-- No `@[stacks 0B5X]` registration here: this statement takes `hin`, the bundled inputs of the
-- forward direction, which the source proves rather than assumes. A tag counts only on a
-- declaration proved under the source's own hypotheses, so the registration sits on
-- `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_isCurve` of `CurveInputs.lean`.
public theorem invertibleCurveDegree_pos_of_isAmple_of_inputs (k : Type u) [Field k]
    {C : Scheme.{u}} (g : C ⟶ Spec (.of k)) [IsCurve k g] [IsProper g]
    (hdim : topologicalKrullDim C ≤ 1) (M : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M]
    (hin : HasCurveDegreePositivityInputs k g hdim M)
    (hM : Scheme.Modules.IsAmple C M) :
    0 < invertibleCurveDegree k g hdim M :=
  invertibleCurveDegree_pos_of_isAmple_of_devissage k g hin.1 hin.2.1 hin.2.2.1 hdim M
    hin.2.2.2 hM

namespace Scheme.Modules

/-- **The restriction of an ample invertible module to a closed subscheme is ample.**
Unconditional: a closed immersion is finite, and the pullback of an ample invertible module along
a finite — indeed any affine — morphism is ample, which is the implication `⟹` of
[Stacks, Tag 0B5V].

`Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple` carries ampleness between the two
spellings of [Stacks, Tag 01PS]: the one the degree theory is stated over, and the one
`Stacks.AmpleFiniteSurjective` is stated over. -/
@[ega "III 2.6.2.3" "special case"]
public theorem isAmple_modulePullback_of_isClosedImmersion {X C : Scheme.{u}} (i : C ⟶ X)
    [IsClosedImmersion i] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : IsAmple X L) :
    IsAmple C ((modulePullback i.toLRSHom.toShHom).obj L) :=
  (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple C
      ((modulePullback i.toLRSHom.toShHom).obj L)).mpr
    (Stacks.AmpleFiniteSurjective.isAmple_modulePullback_of_isFinite i L
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mp hL))

end Scheme.Modules

/-- **The implication (1) ⟹ (2) of [Stacks, Tag 0B5Y].** Let `X` be proper over a field `k`, let
`𝓛` be an ample invertible `𝒪_X`-module, and let `i : C ⟶ X` be a closed immersion whose source
is a proper curve over `k`. Then `deg(𝓛|_C) > 0`.

The restriction `𝓛|_C` is ample by
`AlgebraicGeometry.Scheme.Modules.isAmple_modulePullback_of_isClosedImmersion`, and the forward
direction of [Stacks, Tag 0B5X] on the curve `C` gives the positivity; the four inputs that
direction carries are `hin`.

Taking `C` to be a one-dimensional irreducible component of `X` with its reduced induced
structure gives the tag's own statement — see
`AlgebraicGeometry.invertibleCurveDegree_subscheme_pos_of_isAmple`. The implication (2) ⟹ (1) is
not covered; see the implementation notes of this file. -/
-- No `@[stacks 0B5Y]` registration here: this statement takes `hin`, the bundled inputs of the
-- forward direction of [Stacks, Tag 0B5X], which the source proves rather than assumes. A tag
-- counts only on a declaration proved under the source's own hypotheses, so the registration sits
-- on `AlgebraicGeometry.invertibleCurveDegree_reducedComponent_pos_of_isAmple` of
-- `ComponentPositivity.lean`.
public theorem invertibleCurveDegree_pos_of_isAmple_of_isClosedImmersion (k : Type u) [Field k]
    {X C : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : C ⟶ X) [IsClosedImmersion i]
    [IsCurve k (i ≫ f)] (hdim : topologicalKrullDim C ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hin : HasCurveDegreePositivityInputs k (i ≫ f) hdim
      ((modulePullback i.toLRSHom.toShHom).obj L))
    (hL : Scheme.Modules.IsAmple X L) :
    0 < invertibleCurveDegree k (i ≫ f) hdim ((modulePullback i.toLRSHom.toShHom).obj L) :=
  invertibleCurveDegree_pos_of_isAmple_of_inputs k (i ≫ f) hdim _ hin
    (Scheme.Modules.isAmple_modulePullback_of_isClosedImmersion i L hL)

/-- **The implication (1) ⟹ (2) of [Stacks, Tag 0B5Y] at the irreducible components.** Let `X` be
proper over a field `k` and `𝓛` an ample invertible `𝒪_X`-module. For an irreducible component
`Z` of `X` whose reduced induced closed subscheme is a curve over `k` — that is, for a component
of dimension one — the degree of the restriction of `𝓛` is positive.

The dimension bound on the component is automatic from the one on `X`
(`StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion`), so it is not a hypothesis here. -/
-- No `@[stacks 0B5Y]` registration here: this statement takes `hin`, the four inputs of the
-- forward direction of [Stacks, Tag 0B5X], which the source proves rather than assumes. The tag is
-- registered on the unconditional implication (1) ⟹ (2),
-- `AlgebraicGeometry.invertibleCurveDegree_reducedComponent_pos_of_isAmple` of
-- `ComponentPositivity.lean`, where `hin` is discharged.
public theorem invertibleCurveDegree_subscheme_pos_of_isAmple (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdimX : topologicalKrullDim (X : Type u) ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents (X : Type u))
    [IsCurve k ((Scheme.IdealSheafData.vanishingIdeal
      ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι ≫ f)]
    (hin : HasCurveDegreePositivityInputs k
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι ≫ f)
      ((StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion
        (Scheme.IdealSheafData.vanishingIdeal
          ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι).trans hdimX)
      ((modulePullback (Scheme.IdealSheafData.vanishingIdeal
        ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι.toLRSHom.toShHom).obj L))
    (hL : Scheme.Modules.IsAmple X L) :
    0 < invertibleCurveDegree k
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι ≫ f)
      ((StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion
        (Scheme.IdealSheafData.vanishingIdeal
          ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι).trans hdimX)
      ((modulePullback (Scheme.IdealSheafData.vanishingIdeal
        ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι.toLRSHom.toShHom).obj L) :=
  invertibleCurveDegree_pos_of_isAmple_of_isClosedImmersion k f _ _ L hin hL

/-! ### The converse: ampleness from positivity of the degrees -/

/-- **The gated vanishing input of the converse of [Stacks, Tag 0B5X] on a proper curve.** This
is the `hvan` of `AlgebraicGeometry.isAmple_iff_degree_pos`: positivity of the degree gives, for
every closed subscheme of the curve, a positive power of `M` killing `H¹` of its ideal sheaf
twisted by that power.

It is an implication out of positivity of the degree, and not a bare hypothesis, for the reason
spelled out in `./Vanishing.lean`: assumed unconditionally it would make `M` ample outright. As
an implication it forces nothing — at every `M` of non-positive degree it is inhabited vacuously
— so the hypothesis set is consistent with both sides of the biconditional below being false. -/
public def HasCurveAmpleFromDegreeInput (k : Type u) [Field k] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim C ≤ 1) (M : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M] : Prop :=
  0 < invertibleCurveDegree k g hdim M →
    ∀ {W : Scheme.{u}} (j : W ⟶ C), IsClosedImmersion j → ∃ n : ℕ, 1 ≤ n ∧
      IsZero (((moduleGlobalSections C).rightDerived 1).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((C.toRingedSpace)).presheaf, ((C.toRingedSpace)).IsSheaf⟩).obj
          ((Stacks.ClosedImmersion.idealSheaf j.toLRSHom.toShHom))).obj
          ((tensorPower C.toRingedSpace.presheaf
            (structureSheafRing C.toRingedSpace).property M (n : ℤ))))))

/-- **The converse direction of [Stacks, Tag 0B5X], consuming the bundled gated input.** An
invertible module of positive degree on a proper curve over a field is ample. -/
-- No `@[stacks 0B5X]` registration here: this statement takes `hvan`, the third paragraph of the
-- source's proof, which the source proves rather than assumes. A tag counts only on a declaration
-- proved under the source's own hypotheses, so the registration sits on
-- `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_isCurve` of `CurveInputs.lean`.
public theorem isAmple_of_invertibleCurveDegree_pos_of_input (k : Type u) [Field k]
    {C : Scheme.{u}} (g : C ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim C ≤ 1)
    (M : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M]
    (hvan : HasCurveAmpleFromDegreeInput k g hdim M)
    (hpos : 0 < invertibleCurveDegree k g hdim M) :
    Scheme.Modules.IsAmple C M :=
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace g
  Scheme.Modules.isAmple_of_forall_exists_isZero_h1_idealSheaf M (hvan hpos)

/-- **The gated control for `AlgebraicGeometry.HasCurveAmpleFromDegreeInput`.** At every
invertible module of non-positive degree the input is inhabited vacuously, so carrying it forces
neither side of the biconditional of [Stacks, Tag 0B5Y] below. This is the joint-satisfiability
guard that a biconditional with a positivity condition on one side needs. -/
public theorem hasCurveAmpleFromDegreeInput_of_not_pos (k : Type u) [Field k] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim C ≤ 1) (M : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M]
    (hneg : ¬ 0 < invertibleCurveDegree k g hdim M) :
    HasCurveAmpleFromDegreeInput k g hdim M :=
  fun h => absurd h hneg

/-- **The converse implication of [Stacks, Tag 0B5V], in the form [Stacks, Tag 0B5Y] consumes
it**: ampleness of `𝓛` descends from the ampleness of its restrictions to a finite family of
closed subschemes whose images cover `X`.

The source of [Stacks, Tag 0B5Y] forms `g : C₁ ⨿ … ⨿ C_t ⨿ x₁ ⨿ … ⨿ x_r ⟶ X`, which is finite
(each summand maps in by a closed immersion, hence finitely, and the index type is finite) and
surjective (the images cover), and then cites [Stacks, Tag 0B5V] to pass ampleness from `g^*𝓛` to
`𝓛`. Two things are needed for that and neither is in this library:

* the **converse** implication of [Stacks, Tag 0B5V]. Only the forward implication carries that
  tag, at `../AmpleFiniteSurjective/Basic.lean:208`, under the scoped clause "the implication
  `L` ample ⟹ `f^* L` ample"; that file's own "What is not done" section records the converse as
  owed, blocked on [Stacks, Tag 0B5U] and hence on clause (4) of [Stacks, Tag 0B5T];
* that ampleness on a finite coproduct of schemes is ampleness on each summand, which is not a
  Stacks tag but is also absent — no declaration in either Lean tree relates
  `AlgebraicGeometry.Scheme.Modules.IsAmple` to a coproduct, a sigma or a disjoint union of
  schemes.

So this is carried, and it is the whole of the converse's debt beyond [Stacks, Tag 0B5X]. -/
public def AmpleDescendsAlongFiniteClosedCover {X : Scheme.{u}} {ι : Type u} [Finite ι]
    {C : ι → Scheme.{u}} (i : ∀ j, C j ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : Prop :=
  (⋃ j, Set.range (i j).base) = Set.univ →
    (∀ j, Scheme.Modules.IsAmple (C j)
      ((modulePullback (i j).toLRSHom.toShHom).obj L)) →
        Scheme.Modules.IsAmple X L

/-- **[Stacks, Tag 0B5Y], both directions.** Let `X` be proper over a field `k`, let `𝓛` be an
invertible `𝒪_X`-module, and let `i j : C j ⟶ X`, `j ∈ ι` finite, be closed immersions whose
images cover `X` and each of which is either a proper curve over `k` or affine — the tag's family
of the one-dimensional irreducible components `C₁, …, C_t` together with the isolated closed
points `x₁, …, x_r`, each taken with its reduced induced structure. Then

`𝓛` is ample ⟺ `deg(𝓛|_{C j}) > 0` for every `j` whose `C j` is a curve.

The zero-dimensional members of the family cost nothing: an invertible module on an affine scheme
is ample (`AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible`,
[Stacks, Tag 0B5P] fired on its satisfiable affine hypothesis), which is why the tag's degree
condition ranges over the one-dimensional components only.

Three inputs the library does not have are carried, and none of them is an instance of this
statement: `hin j` and `hvan j` are the inputs of the two directions of [Stacks, Tag 0B5X] on
the curve `C j`, and `hdesc` is the converse of [Stacks, Tag 0B5V] together with the behaviour of
ampleness on a finite coproduct. -/
-- No `@[stacks 0B5Y]` registration here: this statement takes `hin`, `hvan` and `hdesc`, each
-- standing for a result the source proves, which the source proves rather than assumes. A tag
-- counts only on a declaration proved under the source's own hypotheses, so the registration sits
-- on `AlgebraicGeometry.invertibleCurveDegree_reducedComponent_pos_of_isAmple` of
-- `ComponentPositivity.lean`.
public theorem isAmple_iff_forall_invertibleCurveDegree_pos (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {ι : Type u} [Finite ι]
    {C : ι → Scheme.{u}} (i : ∀ j, C j ⟶ X) [∀ j, IsClosedImmersion (i j)]
    (hdim : ∀ j, topologicalKrullDim (C j) ≤ 1)
    (hmem : ∀ j, IsCurve k (i j ≫ f) ∨ IsAffine (C j))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hin : ∀ (j : ι) (_ : IsCurve k (i j ≫ f)),
      HasCurveDegreePositivityInputs k (i j ≫ f) (hdim j)
        ((modulePullback (i j).toLRSHom.toShHom).obj L))
    (hvan : ∀ j, HasCurveAmpleFromDegreeInput k (i j ≫ f) (hdim j)
      ((modulePullback (i j).toLRSHom.toShHom).obj L))
    (hdesc : AmpleDescendsAlongFiniteClosedCover i L)
    (hcover : (⋃ j, Set.range (i j).base) = Set.univ) :
    Scheme.Modules.IsAmple X L ↔
      ∀ (j : ι), IsCurve k (i j ≫ f) →
        0 < invertibleCurveDegree k (i j ≫ f) (hdim j)
          ((modulePullback (i j).toLRSHom.toShHom).obj L) := by
  have hXcpt : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  refine ⟨fun hL j hj => ?_, fun hdeg => hdesc hcover fun j => ?_⟩
  · exact @invertibleCurveDegree_pos_of_isAmple_of_isClosedImmersion k _ X (C j) f _ (i j) _ hj
      (hdim j) L _ (hin j hj) hL
  · rcases hmem j with hj | hj
    · exact isAmple_of_invertibleCurveDegree_pos_of_input k (i j ≫ f) (hdim j) _
        (hvan j) (hdeg j hj)
    · have : CompactSpace (C j) :=
        StacksTag09NX.compactSpace_of_isClosedImmersion (X := X) (i j)
      exact Scheme.Modules.isAmple_of_isAffine_of_isInvertible
        ((modulePullback (i j).toLRSHom.toShHom).obj L)

end AlgebraicGeometry

end
