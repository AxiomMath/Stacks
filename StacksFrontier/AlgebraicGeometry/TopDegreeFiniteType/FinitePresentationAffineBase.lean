module

public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationFromAffine
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.AffineModuleFinite
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.NoetherianBase
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.NoetherianBaseUnconditional

/-!
# Finite presentation of the top higher direct image

[Stacks, Tag 0EX5] asserts, for `f : X ⟶ Y` proper and of finite presentation all of whose
fibres have dimension at most `d` and `F` an `𝒪_X`-module of finite presentation, that
`R ᵈ f_* F` is of finite presentation. The source prints the conclusion as a statement about an
`𝒪_X`-module; `R ᵈ f_* F` is a sheaf on `Y`, and the conclusion is read here as the statement
about the `𝒪_Y`-module that the source's own proof supports — that proof is the proof of
[Stacks, Tag 0EX4], which calls `R ᵈ f_* F` quasi-coherent by [Stacks, Tag 01XJ] (a statement
about `𝒪_Y`-modules), localises the question on `Y`, and over `Y = Spec R` asks that
`H ᵈ (X, F)` be finite as an `R`-module. Formally the reading is forced: the higher direct image
is an object of `Y.Modules`.

Three things are proved. The first two are the source's opening moves, isolated: the conclusion
is local on `Y`, and over an affine base it is the finite presentation of the single module
`H ᵈ (X, F)`. The third is the whole of the tag over a **locally Noetherian** base, with no
hypothesis at all — and in particular none on the fibres, which over such a base are provably
irrelevant. The finiteness theorem [Stacks, Tag 02O6] that the last one rests on is
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, reached through
`…TopDegreeFiniteType.isFiniteType_rightDerived_of_isProper_of_isLocallyNoetherian`.

Over a base that is not locally Noetherian the tag is **not** proved here; see the
implementation notes for the step that is missing.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeFiniteType`'s
  `isFinitePresentation_rightDerived_of_forall_isAffineOpen`: finite presentation of
  `R ᵈ f_* F` is local on the base. No hypothesis on the fibres of `f`, none on `Y`, and only
  quasi-compactness and quasi-separatedness of `f`.
* `…finitePresentation_cohomology_iff_isFinitePresentation_rightDerived`: over an **arbitrary**
  affine base, finite presentation of `R ⁿ f_* F` and finite presentation of the
  `Γ(S, ⊤)`-module `H ⁿ (X, F)` are the same condition. No Noetherian hypothesis.
* `…isFinitePresentation_rightDerived_of_moduleFinite_cohomology`: **[Stacks, Tag 0EX5] over a
  locally Noetherian base, unconditionally**, in every degree and with no hypothesis on the
  fibres.
* `…isFinitePresentation_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase` and
  `…forall_isFinitePresentation_rightDerived_iff_forall_isAffineBase`: the localisation of the
  tag on its base, and the statement that it loses nothing.

## Implementation notes

**Where the general base defeats this file, precisely.** The source's route over `Y = Spec R`
with `R` arbitrary is: write `R = colim R_i` with each `R_i` Noetherian, descend `f`, the bound
on its fibres and `F` to a finite stage, and read off `R ᵈ f_* F` as the pullback of
`R ᵈ (f₀)_* F₀` from top-degree base change; the finiteness theorem over the Noetherian stage
then finishes, since a finite module over a Noetherian ring is finitely presented
(`Module.finitePresentation_of_finite`) and finite presentation is stable under pullback.

Every descent input of that route is available: the limit presentation is
[Stacks, Tag 01ZA], `AlgebraicGeometry.exists_isLimit_finiteType`, which produces an `IsLimit`
cone over a directed diagram with affine transition morphisms whose stages are Noetherian by
`AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminalFrom`; the model of `f` is
[Stacks, Tag 01ZM] part (1); its properness at a later stage is [Stacks, Tag 081F]; the
fibre-dimension bound at a later stage is [Stacks, Tag 05M5]; and the model of `F` is
[Stacks, Tag 01ZR] (`descend_modules`).

What is missing is the base-change identification itself — clause (c) of [Stacks, Tag 0EX3],
that formation of `R ᵈ f_* F` commutes with base change. In this development only clause (a) is
proved; for clause (c) `…TopDegreeBaseChange.topDirectImageBaseChangeMap` constructs the
canonical comparison map and `…isIso_topDirectImageBaseChangeMap_iff` reduces its invertibility
to a derived-category statement, which is not discharged here. That identification, together
with the reconciliation of the two stages at which the models of `f` and of `F` are produced, is
a formalisation in its own right rather than a few lemmas; the tag over an arbitrary base is
`…TopDegreeFiniteType.isFinitePresentation_rightDerived_of_finitePresentation`, downstream in
`FinitePresentationModelDischarge.lean`.

**Over a locally Noetherian base the fibre-dimension bound is provably inert.** The statement
below holds in every degree with no hypothesis on the fibres of `f`, exactly as for the
finite-type clause of [Stacks, Tag 0EX4]; the bound is what the source needs in order to run the
limit argument over a general base, not in order to conclude over a Noetherian one.

**The `ℕ`- and `ℤ`-indexings are bridged twice in the locality statement.** The restriction
comparison `…SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` is stated for
`CategoryTheory.Functor.rightDerivedPlus` at `(d : ℤ)` while the tag uses Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`; the comparison of the two indexings is
`Stacks.DerivedIndexing.rightDerivedIso`, applied once at each end.

## References

* [Stacks Project, Tag 0EX5](https://stacks.math.columbia.edu/tag/0EX5)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherenceCriteria
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.FinitePresentationLocal
open Stacks.AlgebraicGeometry.ProperCohomologyFinite
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Finite presentation of a higher direct image is local on the base -/

/-- **Finite presentation of `R ᵈ f_* F` is local on the base.** If `R ᵈ (f ∣_ V)_*` of the
restriction of `F` is of finite presentation for every affine open `V` of `Y`, then `R ᵈ f_* F`
is of finite presentation.

The affine opens cover `Y`; restriction to an open of the base commutes with the higher direct
image ([Stacks, Tag 01E5]), here as
`…SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` read through
`Stacks.DerivedIndexing.rightDerivedIso` at both ends; and a quasi-coherent module whose
restriction to each member of an affine open covering is of finite presentation is of finite
presentation. Quasi-coherence of `R ᵈ f_* F` is [Stacks, Tag 01XJ], found by instance search
from the quasi-compactness and quasi-separatedness of `f`. No hypothesis on the fibres of `f`
and none on `Y`. -/
theorem isFinitePresentation_rightDerived_of_forall_isAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (d : ℕ)
    (h : ∀ V : Y.affineOpens,
      (((Scheme.Modules.pushforward (f ∣_ (V : Y.Opens))).rightDerived d).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : Y.Opens)).ι).obj F)).IsFinitePresentation) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFinitePresentation := by
  refine isFinitePresentation_of_affineCover_restrict _
    (fun V : Y.affineOpens => (V : Y.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top Y))
    (fun V => V.2) fun V => ?_
  refine (_root_.SheafOfModules.isFinitePresentation.{u, u, u}
    (V : Y.Opens).toScheme.ringCatSheaf).prop_of_iso ?_ (h V)
  exact (Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward (f ∣_ (V : Y.Opens))) d).app
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : Y.Opens)).ι).obj F) ≪≫
      rightDerivedPlusRestrictObjIso f (V : Y.Opens) d F ≪≫
    (Scheme.Modules.restrictFunctor (V : Y.Opens).ι).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) d).app F).symm

/-! ### Over an affine base, finite presentation is finite presentation of the cohomology -/

section AffineBase

variable {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f] [AlgebraicGeometry.IsAffine S]

/-- **Over an arbitrary affine base, finite presentation of `R ⁿ f_* F` makes `H ⁿ (X, F)` a
finitely presented `Γ(S, ⊤)`-module.** No Noetherian hypothesis on `S`.

The sections of a module of finite presentation over an affine open are a finitely presented
module (`…FinitePresentationLocal.finitePresentation_sections_of_restrict`, applied at `⊤`), and
[Stacks, Tag 01XK] identifies those sections with `H ⁿ (X, F)`. -/
theorem finitePresentation_cohomology_of_isFinitePresentation_rightDerived (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ)
    (h : (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFinitePresentation) :
    Module.FinitePresentation Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj F)) := by
  have hsec : Module.FinitePresentation Γ(S, ⊤)
      ((moduleGlobalSections S).obj (((Scheme.Modules.pushforward f).rightDerived n).obj F)) :=
    finitePresentation_sections_of_restrict _ (isAffineOpen_top S)
      (isFinitePresentation_restrict (⊤ : S.Opens).ι _ h)
  exact Module.FinitePresentation.of_equiv
    (cohomologyIsoSectionsRightDerived f F n).toLinearEquiv.symm

/-- **The converse, over an arbitrary affine base**: finite presentation of `H ⁿ (X, F)` as a
`Γ(S, ⊤)`-module makes `R ⁿ f_* F` of finite presentation. No Noetherian hypothesis on `S`.

[Stacks, Tag 01XK] turns the hypothesis into finite presentation of the sections of `R ⁿ f_* F`
over `⊤`, which covers `S` by itself, and
`…FinitePresentationLocal.isFinitePresentation_of_affineCover` concludes. -/
theorem isFinitePresentation_rightDerived_of_finitePresentation_cohomology (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ)
    (h : Module.FinitePresentation Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj F))) :
    (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFinitePresentation := by
  have hsec : Module.FinitePresentation Γ(S, ⊤)
      ((moduleGlobalSections S).obj (((Scheme.Modules.pushforward f).rightDerived n).obj F)) :=
    Module.FinitePresentation.of_equiv (cohomologyIsoSectionsRightDerived f F n).toLinearEquiv
  exact isFinitePresentation_of_affineCover _ (fun _ : PUnit.{u + 1} => (⊤ : S.Opens))
    (IsOpenCover.mk iSup_const) (fun _ => isAffineOpen_top S) fun _ => hsec

/-- **Over an arbitrary affine base, finite presentation of `R ⁿ f_* F` and finite presentation
of the `Γ(S, ⊤)`-module `H ⁿ (X, F)` are the same condition.** This is the source's own reading
of the conclusion over an affine base. -/
theorem finitePresentation_cohomology_iff_isFinitePresentation_rightDerived (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) :
    Module.FinitePresentation Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F)) ↔
      (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFinitePresentation :=
  ⟨isFinitePresentation_rightDerived_of_finitePresentation_cohomology f F n,
    finitePresentation_cohomology_of_isFinitePresentation_rightDerived f F n⟩

end AffineBase

/-! ### Tag 0EX5 over a locally Noetherian base -/

/-- **[Stacks, Tag 0EX5] over a locally Noetherian base, with no hypothesis on the fibres.** For
`f : X ⟶ Y` proper with `Y` locally Noetherian and `F` an `𝒪_X`-module of finite presentation,
the `𝒪_Y`-module `R ᵈ f_* F` is of finite presentation in **every** degree `d`.

A module of finite presentation is quasi-coherent and of finite type, so
`isFiniteType_rightDerived_of_isProper_of_isLocallyNoetherian` makes `R ᵈ f_* F` of finite type;
it is quasi-coherent by [Stacks, Tag 01XJ]; over a locally Noetherian scheme those two together
are coherence ([Stacks, Tag 01XZ]); and a coherent module is of finite presentation
(`…CoherentTFAE.isFinitePresentation_of_isCoherent'`).

No `@[stacks 0EX5]` attribute: `IsLocallyNoetherian Y` is a hypothesis the tag does not carry,
and neither is local finite presentation of `f`, which is unused here. -/
theorem isFinitePresentation_rightDerived_of_moduleFinite_cohomology {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules) [F.IsFinitePresentation]
    (d : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFinitePresentation := by
  obtain ⟨hqc, hft⟩ := isQuasicoherent_isFiniteType_of_isFinitePresentation F inferInstance
  have := hqc
  have := hft
  have hFTtarget := isFiniteType_rightDerived_of_isProper_of_isLocallyNoetherian f F d
  have := hFTtarget
  have : _root_.SheafOfModules.IsCoherent
      (((Scheme.Modules.pushforward f).rightDerived d).obj F) :=
    isCoherent_of_isQuasicoherent_of_isFiniteType _
  exact isFinitePresentation_of_isCoherent' _

/-! ### Tag 0EX5 over an arbitrary base -/

/-! ### Localising the tag on its base -/

/-- **[Stacks, Tag 0EX5] over an arbitrary base, from its own affine case.** For `f : X ⟶ Y`
proper and of finite presentation whose fibres all have dimension at most `d`, and `F` an
`𝒪_X`-module of finite presentation, the `𝒪_Y`-module `R ᵈ f_* F` is of finite presentation as
soon as the same conclusion is granted for every proper morphism of finite presentation onto an
**affine** base all of whose fibres have dimension at most `d`.

This is the source's opening reduction. Every hypothesis of the assumed case has to be produced
for `f ∣_ V`: properness and local finite presentation are instance search, the fibre-dimension
bound is `AlgebraicGeometry.topologicalKrullDim_fiber_morphismRestrict_le`, the fibres of
`f ∣_ V` over points of `V` being the fibres of `f` ([Stacks, Tag 02FY] part (1)), and the
restricted module is of finite presentation by
`…FinitePresentationLocal.isFinitePresentation_restrict`.

No `@[stacks 0EX5]` attribute: `haff` is the tag's own conclusion over affine bases, which
`forall_isFinitePresentation_rightDerived_iff_forall_isAffineBase` shows to be equi-strong with
the conclusion, so this statement asserts nothing about the tag by itself. -/
theorem isFinitePresentation_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (hfp : AlgebraicGeometry.FinitePresentation f)
    (d : ℕ) (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsFinitePresentation]
    (haff : ∀ (X₀ Y₀ : Scheme.{u}) (g : X₀ ⟶ Y₀), IsProper g →
      AlgebraicGeometry.FinitePresentation g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
        ∀ G : X₀.Modules, G.IsFinitePresentation →
          (((Scheme.Modules.pushforward g).rightDerived d).obj G).IsFinitePresentation) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFinitePresentation := by
  have := hfp.locallyOfFinitePresentation
  have : F.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation F
  refine isFinitePresentation_rightDerived_of_forall_isAffineOpen f F d fun V => ?_
  have hVaff : IsAffine (V : Y.Opens).toScheme := V.2
  exact haff _ _ (f ∣_ (V : Y.Opens)) inferInstance
    (AlgebraicGeometry.FinitePresentation.mk inferInstance inferInstance inferInstance) hVaff
    (topologicalKrullDim_fiber_morphismRestrict_le f (V : Y.Opens) d (fun y _ => hdim y))
    _ (isFinitePresentation_restrict (f ⁻¹ᵁ (V : Y.Opens)).ι F inferInstance)

/-- **[Stacks, Tag 0EX5] is equivalent to its own affine-base case.** Each side is quantified
over all of its own data; the right-hand side adds `IsAffine Y` and nothing else.

The forward direction is instantiation, so the reduction proved above is not a weakening: an
arbitrary base contributes nothing to the tag beyond an affine one, and the whole of what the
tag asks is located at a proper morphism of finite presentation onto `Spec R` for a ring `R`
with no Noetherian hypothesis. It is also why the affine case cannot be *assumed* in a statement
asserting the tag. -/
theorem forall_isFinitePresentation_rightDerived_iff_forall_isAffineBase :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsProper f → AlgebraicGeometry.FinitePresentation f →
        ∀ d : ℕ, (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) →
          ∀ F : X.Modules, F.IsFinitePresentation →
            (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFinitePresentation) ↔
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsProper f → AlgebraicGeometry.FinitePresentation f →
        IsAffine Y → ∀ d : ℕ,
          (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) →
            ∀ F : X.Modules, F.IsFinitePresentation →
              (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFinitePresentation) := by
  constructor
  · intro h X Y f hf hfp _ d hdim F hF
    exact h X Y f hf hfp d hdim F hF
  · intro h X Y f hf hfp d hdim F hF
    have := hf
    have := hF
    exact isFinitePresentation_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase
      f hfp d hdim F
      (fun X₀ Y₀ g hg hgfp hY₀ hgdim G hG => h X₀ Y₀ g hg hgfp hY₀ d hgdim G hG)

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
