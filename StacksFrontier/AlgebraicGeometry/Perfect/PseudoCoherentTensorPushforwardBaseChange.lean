module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.TensorFlat
import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the derived pushforward of a pseudo-coherent complex

Let `f : X ⟶ S` be a morphism of finite presentation, let `E` be a pseudo-coherent object of
`D(𝒪_X)` and let `𝒢^•` be a bounded-above complex of finitely presented `𝒪_X`-modules, flat
over `S`, with support proper over `S`. [Stacks, Tag 0CSC] asserts two things about
`K = Rf_*(E ⊗^𝐋_{𝒪_X} 𝒢^•)`: that `K` is a pseudo-coherent object of `D(𝒪_S)`, and that its
formation commutes with arbitrary base change. [Stacks, Tag 0CSD] is the special case
`𝒢^• = 𝒪_X` in degree `0`, for a flat proper `f` of finite presentation.

**This file proves the base-change half of each, and only that half.** The source's own proof
splits the two: "The statement on base change is Lemma 0A1D. Thus it suffices to show that `K`
is a pseudo-coherent object." The first sentence is what is carried out here; the second is not,
and the implementation notes below record exactly which inputs it needs that this library does
not have.

The precise form of the base-change statement is the one [Stacks, Tag 0A1D] is stated at in this
library: for every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

the canonical map

`Lg^*Rf_*(E ⊗^𝐋_{𝒪_X} 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^𝐋_{𝒪_{X'}} (g')^*𝒢^•)`

of `AlgebraicGeometry.tensorFlatBaseChangeMap` is an isomorphism, with the **ordinary** pullback
`(g')^*𝒢^•` on the right — the source sets that in bold.

## Main results

In the namespace `AlgebraicGeometry.PseudoCoherentTensorBaseChange`:

* `isIso_tensorFlatBaseChangeMap_of_isPseudoCoherent` is the base-change half of
  [Stacks, Tag 0CSC].
* `isIso_tensorFlatBaseChangeMap_structure_of_isPseudoCoherent` is the base-change half of
  [Stacks, Tag 0CSD], obtained from it by the source's own specialisation `𝒢^• = 𝒪_X` in
  degree `0`, at the tensor form that specialisation produces.
* `isIso_derivedBaseChangeMap_of_isIso_tensorFlatBaseChangeMap` is the passage from
  `Rf_*(E ⊗^𝐋_{𝒪_X} 𝒢^•)` to `Rf_*E`, for a K-flat `𝒢^•` carrying an isomorphism
  `E ⊗^𝐋_{𝒪_X} 𝒢^• ≅ E`: invertibility of `AlgebraicGeometry.tensorFlatBaseChangeMap` gives
  invertibility of the base-change map of [Stacks, Tag 08HY] at `E` itself.
* `isIso_derivedBaseChangeMap_of_isPseudoCoherent` is the base-change half of
  [Stacks, Tag 0CSD] **in the tag's own form**: `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` is an isomorphism.

## Implementation notes

**Why [Stacks, Tag 0A1D] and not [Stacks, Tag 0A1H].** [Stacks, Tag 0CSC] allows `𝒢^•` to be
bounded *above* only, while [Stacks, Tag 0A1H] asks for a bounded complex; the source accordingly
cites [Stacks, Tag 0A1D], whose hypothesis on `𝒢^•` is boundedness above
(`CochainComplex.minus`). So `AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_isPullback`
([Stacks, Tag 0A1D]) is quoted directly; going through [Stacks, Tag 0A1H] would add a
hypothesis that [Stacks, Tag 0CSC] does not make. The
proper-support hypothesis on `𝒢^•` is stated below because [Stacks, Tag 0CSC] states it, and is
not used by this half: the source's base-change argument does not appeal to it.

**What is discharged here.** The hypothesis `hE` of [Stacks, Tag 0A1D] — quasi-coherence of
the cohomology of `E` — is *proved* here from pseudo-coherence of `E`, by [Stacks, Tag 08E5]
(`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`), so that grant of
[Stacks, Tag 0A1D] disappears. Also discharged, as in [Stacks, Tag 0A1H]: quasi-compactness and
quasi-separatedness of `f`, from `AlgebraicGeometry.FinitePresentation` ([Stacks, Tag 01TP] part
(3)); and quasi-coherence of the terms of `𝒢^•`, from their finite presentation by
[Stacks, Tag 01BW].

**What is *not* restricted.** The base is an arbitrary scheme `S` — neither affine nor
Noetherian — `f` is only of finite presentation, `E` is an arbitrary pseudo-coherent object of
`D(𝒪_X)` and `𝒢^•` is only bounded above, so the base-change half below is at
[Stacks, Tag 0CSC]'s own hypotheses and at no narrower ones.

**The derived category is pinned to the standard model.** [Stacks, Tag 0CSC] and
[Stacks, Tag 0CSD] are model-independent; the statements below are not. `DerivedCategory`
is read at `CategoryTheory.HasDerivedCategory.standard`, seated as a local instance, because
`AlgebraicGeometry.tensorFlatBaseChangeMap` — the canonical map whose invertibility is the
conclusion — is built from the base-change map of [Stacks, Tag 08HY], which this library carries
only at that model, and the three conditions of [Stacks, Tag 0DJ8] that the proof of
[Stacks, Tag 0A1D] runs on are available in the pointwise form (1) only there; the module
documentation of
`StacksFrontier/AlgebraicGeometry/BaseChange/TensorFlatPushforwardBaseChange.lean` records that the
chart forms (2) and (3) are carried at the locally small model instead and that no transport
between the two exists in this tree. Every result below therefore inherits the pin, as
[Stacks, Tag 0A1D], [Stacks, Tag 0A1H] and [Stacks, Tag 0B91] clause (1) already do.

**Nothing is carried.** [Stacks, Tag 0A1D] is proved in this library without hypotheses beyond
the tag's own (`AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_isPullback`), so the
base-change half below takes only the hypotheses of [Stacks, Tag 0CSC] and [Stacks, Tag 0CSD].

**The unit-object transport, and why it needs no unit coherence.** [Stacks, Tag 0CSD] asserts
that the formation of `Rf_*E` commutes with base change, while the specialisation of
[Stacks, Tag 0CSC] to `𝒢^• = 𝒪_X` in degree zero asserts it of `Rf_*(E ⊗^𝐋_{𝒪_X} 𝒪_X)`. The
passage between the two is `isIso_derivedBaseChangeMap_of_isIso_tensorFlatBaseChangeMap`, and it
carries nothing. `AlgebraicGeometry.tensorFlatBaseChangeMap` is a composite of two factors: the
base-change map of [Stacks, Tag 08HY] at `E ⊗^𝐋_{𝒪_X} 𝒢^•`, and `Rf'_*` of
`Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison`. Naturality of the
first in its argument, `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_naturality`,
moves the conclusion along *any* isomorphism `E ⊗^𝐋_{𝒪_X} 𝒢^• ≅ E`. Of the second only
**invertibility** is needed, and for a K-flat `𝒢^•` that is unconditional: the comparison is the
monoidality isomorphism of [Stacks, Tag 079U] followed by the derived-to-ordinary comparison
`L(g')^*𝒢^• ⟶ (g')^*𝒢^•`, and the latter is invertible at a K-flat complex by
`Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackNatTrans_app`. For `𝒢^• = 𝒪_X` in
degree zero the K-flatness is `Stacks.SheafOfModules.isKFlat_single_unit` and the isomorphism is
`Stacks.Cohomology.PerfectPushforward.tensorStructureComplexIso`, the right unit constraint of
[Stacks, Tag 0FPT] read at that complex.

This passage might seem to need compatibility of `baseChangeTensorComparison` with the unit
constraint, that is a right-unitor coherence for
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`. The transport does not
need the coherence, only the invertibility just described; the coherence is nevertheless
available:
`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_of_kFlat` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/ProjectionFormulaUnitCoherence.lean`
states it for every object of `D(𝒪_Y)`, and
`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_app_q` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/ProjectionFormulaUnitCoherenceMonoidal.lean` discharges the K-flat hypothesis it is reduced
to. It is not used here, the invertibility route being shorter.

**Why the pseudo-coherence half is absent.** The source proves it by approximation by perfect
complexes, and the proof uses three inputs. All three are now in this library; their assembly
into the pseudo-coherence half is not done here.

* [Stacks, Tag 08D5] part (2), the uniform bound on the cohomological dimension of
  `Rf_* : D_QCoh(𝒪_X) → D_QCoh(𝒪_S)` over an affine base, **is** available, as
  `AlgebraicGeometry.exists_isZero_homology_derivedPushforward_of_isLE_zero`.
* [Stacks, Tag 08ES], that a quasi-compact and quasi-separated scheme satisfies approximation by
  perfect complexes, **is** available, as
  `AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_of_qcqs`: the
  compact-open induction principle [Stacks, Tag 08DR] run on the affine case
  [Stacks, Tag 08EQ] with the union step [Stacks, Tag 08ER],
  `AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_sup_affine`. Both are
  stated through `AlgebraicGeometry.PerfectApproximation.ApproximationByPerfectComplexes`, the
  predicate of [Stacks, Tag 08EN] at the standard derived category, which is the model this
  file is pinned to as well.
* The perfection half of [Stacks, Tag 0A1H] — that `Rf_*(P ⊗^𝐋_{𝒪_X} 𝒢^•)` is a perfect object
  of `D(𝒪_S)` for `P` perfect and `𝒢^•` bounded, finitely presented, flat over `S` and of proper
  support — is the last step of the source's proof. It is now in this library, as
  `AlgebraicGeometry.isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap`.

Two results in this library do conclude that a derived pushforward is pseudo-coherent, and
neither is [Stacks, Tag 0CSD]. In `Stacks.AlgebraicGeometry.PerfectProperDirectImage`,
`isPseudoCoherent_derivedPushforward_of_isPerfect` asks `IsNoetherian S`, `Perfect f` and
perfectness of `E`; in `Stacks.AlgebraicGeometry.ProperSupportCoherent`,
`isPseudoCoherent_derivedPushforward_of_isProperOver_supp` asks `IsNoetherian S` together with
coherence of the cohomology of `E` and two-sided bounds on it. [Stacks, Tag 0CSD] grants no
Noetherian hypothesis, does not ask `f` to be perfect, and assumes of `E` only
pseudo-coherence, so neither can be read as that tag.

Both missing inputs are the whole mathematical substance of the half, so stating the half with
them as hypotheses would move the work rather than do it; accordingly no statement of the
pseudo-coherence half is given, and the part strings below say that the half is neither
proved nor stated.

## References

* [Stacks Project, Tag 0CSC](https://stacks.math.columbia.edu/tag/0CSC)
* [Stacks Project, Tag 0CSD](https://stacks.math.columbia.edu/tag/0CSD)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08ES](https://stacks.math.columbia.edu/tag/08ES)
* [Stacks Project, Tag 08ER](https://stacks.math.columbia.edu/tag/08ER)
* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
* [Stacks Project, Tag 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap derivedBaseChangeMap_naturality)
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeTensorComparison)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans derivedPullbackTensorIso
  isIso_derivedPullbackNatTrans_app pullbackComplex)
open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct derivedTensorProductFunctor)
open Stacks.Cohomology.PerfectPushforward (isFlatOver_structureModule isProperOver_top_of_isProper
  tensorStructureComplexIso)

universe u

namespace AlgebraicGeometry.PseudoCoherentTensorBaseChange

-- Priority `10000`: the import of `AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_isPullback`
-- brings global locally small `HasDerivedCategory` instances into scope, which a plain local
-- attribute does not beat; the statements below are read at the standard model, as before.
attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Stacks 0CSC, the base-change half -/

/-- **[Stacks, Tag 0CSC], the base-change half of the conclusion.** Let `f : X ⟶ S` be a
morphism of schemes of finite presentation, let `E` be a pseudo-coherent object of `D(𝒪_X)` and
let `𝒢^•` be a bounded-above complex of finitely presented `𝒪_X`-modules, flat over `S`, with
support proper over `S`. For every cartesian base-change square the canonical map

`Lg^*Rf_*(E ⊗^𝐋_{𝒪_X} 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^𝐋_{𝒪_{X'}} (g')^*𝒢^•)`

of `AlgebraicGeometry.tensorFlatBaseChangeMap` is an isomorphism — note the ordinary pullback of
`𝒢^•` on the right, as the source's boldface demands.

This is the source's own first sentence, "The statement on base change is Lemma 0A1D", carried
out: finite presentation of `f` supplies the quasi-compactness and quasi-separatedness that
[Stacks, Tag 0A1D] asks for, pseudo-coherence of `E` supplies the quasi-coherence of its
cohomology by [Stacks, Tag 08E5], and finite presentation of the terms of `𝒢^•` supplies their
quasi-coherence and that of the cohomology of `Q 𝒢^•` and `Q((g')^*𝒢^•)`.

The pseudo-coherence half of [Stacks, Tag 0CSC] is not proved; the implementation notes of this
file say which inputs it needs that this library does not have.

Cf. Stacks Tag 0CSC; not registered because it is the base-change half only. -/
public theorem isIso_tensorFlatBaseChangeMap_of_isPseudoCoherent
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (hf : FinitePresentation f)
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ)
    (hGminus : CochainComplex.minus X.Modules G)
    (hGfp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hGflat : ∀ i : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X i))
    (hGsupp : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      ∃ Z : Closeds X, IsProperOver f Z ∧
        ∀ i : ℤ, SheafOfModules.supp (G.X i) ⊆ (Z : Set X)) :
    IsIso (tensorFlatBaseChangeMap f g f' g' sq E G) :=
  have hGqcoh : ∀ i : ℤ, (G.X i).IsQuasicoherent := fun i =>
    let := hGfp i
    isQuasicoherent_of_isFinitePresentation (G.X i)
  let : HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) :=
    HasDerivedCategory.standard _
  isIso_tensorFlatBaseChangeMap_of_isPullback f g f' g' hsq hf.quasiCompact
    hf.quasiSeparated sq E (isQuasicoherentDerived_of_isPseudoCoherent.{u, u + 1} X E hE) G
    hGminus hGqcoh hGflat

/-! ### Stacks 0CSD, the base-change half -/

/-- **[Stacks, Tag 0CSD], the base-change half of the conclusion.** Let `f : X ⟶ S` be a flat
proper morphism of finite presentation and let `E` be a pseudo-coherent object of `D(𝒪_X)`. For
every cartesian base-change square the canonical map

`Lg^*Rf_*(E ⊗^𝐋_{𝒪_X} 𝒪_X) ⟶ Rf'_*(L(g')^*E ⊗^𝐋_{𝒪_{X'}} (g')^*𝒪_X)`

of `AlgebraicGeometry.tensorFlatBaseChangeMap` is an isomorphism — note the ordinary pullback of
the complex on the right, as the source's boldface demands.

This is the source's one-line proof, "Special case of Lemma 0CSC applied with `𝒢^•` equal to
`𝒪_X` in degree 0": the complex with `𝒪_X` in degree zero is bounded above, of finite
presentation in each degree by [Stacks, Tag 03DL], flat over `S` in each degree because `f` is
flat ([Stacks, Tag 02N3]), and supported on the closed subset `⊤`, which is proper over `S`
because `f` is ([Stacks, Tag 0CYM]). The passage from `Rf_*(E ⊗^𝐋_{𝒪_X} 𝒪_X)` to `Rf_*E`, which
the source performs silently, is *not* done in this statement — it stands at the tensor form the
specialisation produces — but it is done, from this statement, by
`isIso_derivedBaseChangeMap_of_isPseudoCoherent` below, which is the base-change half in the
tag's own form.

The pseudo-coherence half of [Stacks, Tag 0CSD] is not proved; it is the pseudo-coherence half
of [Stacks, Tag 0CSC], which the implementation notes of this file discuss.

Cf. Stacks Tag 0CSD; not registered because it is the base-change half only. -/
public theorem isIso_tensorFlatBaseChangeMap_structure_of_isPseudoCoherent
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (hf : FinitePresentation f) (hproper : IsProper f) (hflat : Flat f)
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    IsIso (tensorFlatBaseChangeMap f g f' g' sq E
      (ProperFlatBaseChange.singleDegreeComplex
        (StrictlyPerfect.structureModule X.toRingedSpace : X.Modules))) :=
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  let : IsProper f := hproper
  let : Flat f := hflat
  isIso_tensorFlatBaseChangeMap_of_isPseudoCoherent f g f' g' hsq sq hf
    E hE _
    ⟨0, (CochainComplex.isStrictlyLE_iff _ 0).2 fun i hi =>
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i (by omega)⟩
    (ProperFlatBaseChange.isFinitePresentation_singleDegreeComplex _
      (ProperFlatBaseChange.isFinitePresentation_structureModule X))
    (ProperFlatBaseChange.isFlatOver_singleDegreeComplex f _ (isFlatOver_structureModule f))
    ⟨⊤, isProperOver_top_of_isProper f, fun _ => by simp⟩

/-! ### The unit-object transport -/

section UnitTransport

-- The import closure of this file also supplies the global locally small instances of
-- `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which the default-priority local
-- attribute at the head of this namespace does not beat: at an argument that is still a
-- metavariable, `derivedPullback` and `canonicalDerivedTensorProduct` are then read at the
-- locally small model and no longer match the statements above, which are at the standard one.
-- This is the same reseating, for the same reason, as in
-- `StacksFrontier/AlgebraicGeometry/PseudoCoherent/ThickeningQuasicoherent.lean`.
attribute [local instance 10000] HasDerivedCategory.standard

-- No reducibility is opted into here, and none is needed. The base-change comparison of
-- Stacks 0DJA is declared over `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules`, the
-- derived pullback of Stacks 079W over `SheafOfModules (structureSheafRing _)`, and the
-- statements of this file over `AlgebraicGeometry.Scheme.Modules`; the three are one type by
-- `rfl`, and the declarations below mix them. Each crossing is made structurally instead: the
-- formal core is `isIso_of_square_of_isIso_comp` over an abstract category, which names no
-- sheaf, so every invertibility is passed to it as an explicit argument and none is searched
-- for; and the one instance that search did fail to find, `HasDerivedCategory` at the
-- `KFlatDerivedPullback.Modules` spelling, is seated by the two ascriptions at the head of the
-- proof of `isIso_derivedBaseChangeMap_of_isIso_tensorFlatBaseChangeMap` rather than by making
-- the spellings unfold into one another.

/-- The formal core of the unit-object transport: in any category, if `a ≫ b` is invertible and
`b` is invertible, and a commuting square `m ≫ c = a ≫ n` has `m` and `n` invertible, then `c`
is invertible.

It is stated over an abstract category on purpose, and that is what keeps this file free of any
reducibility opt-in. The derived categories below carry `IsIso` at three definitionally equal
spellings of the category of `𝒪_X`-modules — `AlgebraicGeometry.Scheme.Modules`,
`SheafOfModules (structureSheafRing X.toRingedSpace)` and
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace` — and instance
search does not cross between them. Over an abstract `C` nothing in the statement mentions a
sheaf of rings at all, so each invertibility the transport uses is passed as an explicit
argument and the spellings only ever have to agree up to `whnf` at the application, which they
do. -/
private theorem isIso_of_square_of_isIso_comp {C : Type*} [Category C] {W Y Z T V : C}
    (a : W ⟶ Y) (b : Y ⟶ Z) (m : W ⟶ T) (c : T ⟶ V) (n : Y ⟶ V)
    (hb : IsIso b) (hab : IsIso (a ≫ b)) (hm : IsIso m) (hn : IsIso n)
    (hsq : m ≫ c = a ≫ n) : IsIso c := by
  have := hb
  have := hab
  have := hm
  have := hn
  have : IsIso a := IsIso.of_isIso_comp_right a b
  have : IsIso (m ≫ c) := by rw [hsq]; infer_instance
  exact IsIso.of_isIso_comp_left m c

/-- **The passage from `Rf_*(E ⊗^𝐋_{𝒪_X} 𝒢^•)` to `Rf_*E`.** Let `𝒢^•` be a K-flat complex of
`𝒪_X`-modules carrying an isomorphism `ρ : E ⊗^𝐋_{𝒪_X} 𝒢^• ≅ E`. If the canonical map

`Lg^*Rf_*(E ⊗^𝐋_{𝒪_X} 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^𝐋_{𝒪_{X'}} (g')^*𝒢^•)`

of `AlgebraicGeometry.tensorFlatBaseChangeMap` is an isomorphism, then so is the base-change map

`Lg^*Rf_*E ⟶ Rf'_*L(g')^*E`

of [Stacks, Tag 08HY]. This is the transport the source performs silently whenever it
specialises a tensor statement to the unit object, and it carries nothing: `ρ` is data the
caller supplies and the conclusion does not mention it.

The proof uses only the two factors of `AlgebraicGeometry.tensorFlatBaseChangeMap`. The second
factor, `Rf'_*` of
`Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison`, is **invertible**:
that comparison is the monoidality isomorphism of [Stacks, Tag 079U] followed by the
derived-to-ordinary comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•`, which is invertible at a K-flat `𝒢^•`
by `Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackNatTrans_app`. So the first
factor, the base-change map at `E ⊗^𝐋_{𝒪_X} 𝒢^•`, is invertible, and naturality of the map of
[Stacks, Tag 08HY] in its argument
(`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_naturality`) moves that along `ρ`. No
unit coherence for `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` is
needed — only invertibility of the comparison, not its compatibility with the unit. -/
public theorem isIso_derivedBaseChangeMap_of_isIso_tensorFlatBaseChangeMap
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (E : DerivedCategory X.Modules) (G : CochainComplex X.Modules ℤ)
    (hG : RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace G)
    (ρ : ((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G) ≅ E)
    (h : IsIso (tensorFlatBaseChangeMap f g f' g' sq E G)) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom sq E) := by
  -- The base-change comparison of Stacks 0DJA is stated at the
  -- `KFlatDerivedPullback.Modules` spelling of the category of modules, at which instance search
  -- does not find the derived-category model that the statement above is at. The two spellings
  -- are one type by `rfl`, and the model is seated here, at that spelling, rather than by making
  -- one spelling unfold into the other.
  let : HasDerivedCategory.{u + 1}
      (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1}
      (RingedSpace.KFlatDerivedPullback.Modules X'.toRingedSpace) :=
    HasDerivedCategory.standard _
  refine isIso_of_square_of_isIso_comp
    (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom sq
      (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G)))
    ((derivedPushforward f'.toLRSHom.toShHom).map
      (baseChangeTensorComparison g'.toLRSHom.toShHom E (DerivedCategory.Q.obj G)
        (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app G)))
    ((derivedPullback g.toLRSHom.toShHom).map
      ((derivedPushforward f.toLRSHom.toShHom).map ρ.hom))
    _
    ((derivedPushforward f'.toLRSHom.toShHom).map
      ((derivedPullback g'.toLRSHom.toShHom).map ρ.hom))
    ?_ h ?_ ?_
    (derivedBaseChangeMap_naturality g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom sq ρ.hom)
  · exact ((derivedPushforward f'.toLRSHom.toShHom).mapIso
      ((derivedPullbackTensorIso g'.toLRSHom.toShHom).app (E, DerivedCategory.Q.obj G) ≪≫
        ((derivedTensorProductFunctor X'.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E)).mapIso
            (@asIso _ _ _ _ _
              (isIso_derivedPullbackNatTrans_app g'.toLRSHom.toShHom G hG)))).isIso_hom
  · exact ((derivedPullback g.toLRSHom.toShHom).mapIso
      ((derivedPushforward f.toLRSHom.toShHom).mapIso ρ)).isIso_hom
  · exact ((derivedPushforward f'.toLRSHom.toShHom).mapIso
      ((derivedPullback g'.toLRSHom.toShHom).mapIso ρ)).isIso_hom

/-- **[Stacks, Tag 0CSD], the base-change half of the conclusion, in the tag's own form.** Let
`f : X ⟶ S` be a flat proper morphism of finite presentation and let `E` be a pseudo-coherent
object of `D(𝒪_X)`. For every cartesian base-change square the canonical map

`Lg^*Rf_*E ⟶ Rf'_*L(g')^*E`

of [Stacks, Tag 08HY] is an isomorphism: the formation of `Rf_*E` commutes with arbitrary base
change.

This is `isIso_tensorFlatBaseChangeMap_structure_of_isPseudoCoherent` with the source's silent
passage from `Rf_*(E ⊗^𝐋_{𝒪_X} 𝒪_X)` to `Rf_*E` carried out, by
`isIso_derivedBaseChangeMap_of_isIso_tensorFlatBaseChangeMap`: the structure sheaf in degree zero
is K-flat (`Stacks.SheafOfModules.isKFlat_single_unit`) and the unit constraint of
[Stacks, Tag 0FPT] at it is
`Stacks.Cohomology.PerfectPushforward.tensorStructureComplexIso`. Nothing extra is carried, and
nothing of the pseudo-coherence half of [Stacks, Tag 0CSD] is claimed: that half is the
pseudo-coherence half of [Stacks, Tag 0CSC], which the implementation notes of this file
discuss.

Cf. Stacks Tag 0CSD; not registered because it is the base-change half only. -/
public theorem isIso_derivedBaseChangeMap_of_isPseudoCoherent
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (hf : FinitePresentation f) (hproper : IsProper f) (hflat : Flat f)
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom sq E) :=
  isIso_derivedBaseChangeMap_of_isIso_tensorFlatBaseChangeMap f g f' g' sq E
    (ProperFlatBaseChange.singleDegreeComplex
      (StrictlyPerfect.structureModule X.toRingedSpace : X.Modules))
    (Stacks.SheafOfModules.isKFlat_single_unit X.sheaf)
    (tensorStructureComplexIso (X := X) (canonicalDerivedTensorProduct X.sheaf) E)
    (isIso_tensorFlatBaseChangeMap_structure_of_isPseudoCoherent f g f' g' hsq sq hf hproper
      hflat E hE)

end UnitTransport

end AlgebraicGeometry.PseudoCoherentTensorBaseChange

end
