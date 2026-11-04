module

public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Locality
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.FiniteMorphism

/-!
# Over a locally Noetherian base the finite-type clause of Tag 0EX4 is exactly Tag 02O6

[Stacks, Tag 0EX4] asserts, for `f : X ⟶ Y` proper all of whose fibres have dimension at most
`d` and `F` quasi-coherent of finite type, that `R ᵈ f_* F` is quasi-coherent of finite type.
The base `Y` carries **no** Noetherian hypothesis, and the source's proof spends three paragraphs
writing `Y` and `X` as cofiltered limits of Noetherian data before it can quote
[Stacks, Tag 02O6] at the end.

This file measures what is left of the tag once the base *is* locally Noetherian, and the answer
is: nothing but [Stacks, Tag 02O6], and the fibre-dimension hypothesis is not merely unnecessary
but provably unused.

**The reduction.** Over a locally Noetherian `Y` a proper `f` makes `X` locally Noetherian
([Stacks, Tag 01T6]), so a quasi-coherent `F` of finite type is coherent; [Stacks, Tag 02O5] then
says `R ᵈ f_* F` is coherent, hence of finite type. And [Stacks, Tag 02O5] is
[Stacks, Tag 02O6] by
`…ProperCohomologyFinite.isCoherent_rightDerivedPlus_of_moduleFinite_cohomology`.
No fibre dimension enters anywhere, in any degree.

**The converse, which is why this is a measurement and not a weakening.** The hypothesis-free
family — `R ᵈ f_* F` of finite type for every proper morphism to a locally Noetherian base, every
quasi-coherent `F` of finite type and every degree — *implies* [Stacks, Tag 02O6]: over an affine
locally Noetherian base, finite type plus quasi-coherence is coherence
(`…ProperCohomologyFinite.isCoherent_rightDerived_of_isFiniteType`) and coherence of `R ⁿ f_* F`
is finiteness of `Hⁿ(X, F)` (`…ProperCohomologyFinite.moduleFinite_cohomology_of_isCoherent`).
So the two are equivalent, and the statement proved here is exactly as strong as the core it is
conditional on rather than a convenient shadow of it.

**What this does not do.** It says nothing about the tag over a base that is not locally
Noetherian, which is the tag's actual generality and the part the source proves by limits
([Stacks, Tags 09ZR, 05M5, 01ZM, 081F, 01ZR, 0EX3, 086M]). Over a locally Noetherian base the
statements here are conditional on [Stacks, Tag 02O6], which is proved — it is
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, with no hypothesis — but in
a module whose import cone contains this one, so the hypothesis is discharged one level up, in
`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/NoetherianBaseUnconditional.lean`, and not
here. It also does not subsume
`isFiniteType_rightDerived_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero` of
`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/FiniteMorphism.lean`,
which is unconditional and needs no hypothesis on the base at all, but only covers fibres of
dimension at most `0`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeFiniteType`'s
  `isFiniteType_rightDerived_of_moduleFinite_cohomology`:
  **the finite-type clause of [Stacks, Tag 0EX4] over a locally Noetherian base, with no
  fibre-dimension hypothesis**, from [Stacks, Tag 02O6] and nothing else.
* `…isFiniteType_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_moduleFinite_cohomology`:
  the same in the shape of the tag's statement, with the fibre-dimension bound carried as a binder — named
  `_hdim`, because it is unused.
* `…moduleFinite_cohomology_of_forall_isFiniteType_rightDerived`: the converse, [Stacks,
  Tag 02O6] from the family of finite-type conclusions.
* `…forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology`: **the two are
  equivalent.**

## Implementation notes

**No `@[stacks 0EX4]` attribute is attached to anything here.** Every statement carries
[Stacks, Tag 02O6] as a hypothesis and `IsLocallyNoetherian Y` as a binder, and the tag carries
neither. The quasi-coherence clause of the tag is tagged in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageQcqs/Qcqs.lean`; the finite-type clause
carries one over a locally Noetherian base in
`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/NoetherianBaseUnconditional.lean`.

**The `_hdim` binder is significant.** Lean's unused-variable linter is what certifies that the
fibre-dimension bound is dead in the reduction: the declaration below is the tag's clause (2)
with the base restricted and the core assumed, and the bound is discarded. Over a
Noetherian base, [Stacks, Tag 0EX4] amounts to [Stacks, Tag 02O6] exactly, in every
degree, with or without a bound on the fibres.

**The `ℕ`- and `ℤ`-indexings are bridged once.**
`…ProperCohomologyFinite.isCoherent_rightDerivedPlus_of_moduleFinite_cohomology` concludes about
`CategoryTheory.Functor.rightDerivedPlus` at `(d : ℤ)` while [Stacks, Tag 0EX4] and the rest of
this directory use Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`; the comparison is
`Stacks.DerivedIndexing.rightDerivedIso`, and coherence is transported across it by
`Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso`, whose iso argument runs from
the *conclusion* to the hypothesis, so no `symm` appears.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherenceCriteria
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.ProperCohomologyFinite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

attribute [local instance] HasDerivedCategory.standard

/-! ### The finite-type clause of Tag 0EX4 over a locally Noetherian base -/

/-- **The finite-type clause of [Stacks, Tag 0EX4] over a locally Noetherian base, from
[Stacks, Tag 02O6] and nothing else — and with no hypothesis on the fibres.** For `f : X ⟶ Y`
proper with `Y` locally Noetherian and `F` quasi-coherent of finite type, `R ᵈ f_* F` is of
finite type in **every** degree `d`.

`X` is locally Noetherian because a proper morphism is locally of finite type
([Stacks, Tag 01T6]), so `F` is coherent ([Stacks, Tag 01XZ]); the hypothesis globalises to
coherence of `R ᵈ f_* F` by
`…ProperCohomologyFinite.isCoherent_rightDerivedPlus_of_moduleFinite_cohomology`,
which is [Stacks, Tag 02O5] from [Stacks, Tag 02O6]; and a coherent module is of finite type.

No `@[stacks 0EX4]` attribute: `h02O6` and `IsLocallyNoetherian Y` are hypotheses the tag does
not carry. -/
theorem isFiniteType_rightDerived_of_moduleFinite_cohomology {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (d : ℕ)
    (h02O6 : ∀ (X₀ S₀ : Scheme.{u}) (g : X₀ ⟶ S₀), IsProper g → IsAffine S₀ →
      IsLocallyNoetherian S₀ → ∀ G : X₀.Modules, _root_.SheafOfModules.IsCoherent G → ∀ n : ℕ,
        Module.Finite Γ(S₀, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
          (((moduleGlobalSections X₀).rightDerived n).obj G))) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType := by
  have hXN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hFcoh : _root_.SheafOfModules.IsCoherent F := isCoherent_of_isQuasicoherent_of_isFiniteType F
  have := hFcoh
  have hplus := isCoherent_rightDerivedPlus_of_moduleFinite_cohomology f F d h02O6
  have hnat : _root_.SheafOfModules.IsCoherent
      (((Scheme.Modules.pushforward f).rightDerived d).obj F) :=
    have := hplus
    CoherentDevissage.isCoherent_of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) d).app F)
  exact (isQuasicoherent_isFiniteType_of_isCoherent _).2

/-- **Clause (2) of [Stacks, Tag 0EX4], over a locally Noetherian base, conditional on
[Stacks, Tag 02O6].** The fibre-dimension bound is carried as a binder and never used — the name
is `_hdim` for that reason. This is the statement of the tag's finite-type clause with the base
restricted to be locally Noetherian and the finiteness theorem assumed; it is
`isFiniteType_rightDerived_of_moduleFinite_cohomology` with the bound discarded.

The point of stating it is that the bound is *measurably* inert: over a locally Noetherian base
the tag's content in degree `d` does not depend on the fibres of `f` at all. -/
theorem isFiniteType_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_moduleFinite_cohomology
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (d : ℕ)
    (_hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h02O6 : ∀ (X₀ S₀ : Scheme.{u}) (g : X₀ ⟶ S₀), IsProper g → IsAffine S₀ →
      IsLocallyNoetherian S₀ → ∀ G : X₀.Modules, _root_.SheafOfModules.IsCoherent G → ∀ n : ℕ,
        Module.Finite Γ(S₀, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
          (((moduleGlobalSections X₀).rightDerived n).obj G))) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  isFiniteType_rightDerived_of_moduleFinite_cohomology f F d h02O6

/-! ### The converse, and the equivalence -/

/-- **[Stacks, Tag 02O6] from the finite-type clause of [Stacks, Tag 0EX4] over locally
Noetherian bases.** If `R ᵈ f_* F` is of finite type for every proper morphism to a locally
Noetherian base, every quasi-coherent `F` of finite type and every degree, then `Hⁿ(X, G)` is a
finite `Γ(S, ⊤)`-module for every proper morphism to an affine locally Noetherian `S` and every
coherent `G`.

A coherent module is quasi-coherent of finite type, so the hypothesis applies; over a locally
Noetherian base quasi-coherent of finite type is coherent
(`…ProperCohomologyFinite.isCoherent_rightDerived_of_isFiniteType`); and over an affine base
coherence of `R ⁿ f_* G` is finiteness of `Hⁿ(X, G)`
(`…ProperCohomologyFinite.moduleFinite_cohomology_of_isCoherent`). -/
theorem moduleFinite_cohomology_of_forall_isFiniteType_rightDerived
    (h : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsProper f → IsLocallyNoetherian Y →
      ∀ F : X.Modules, F.IsQuasicoherent → F.IsFiniteType →
        ∀ d : ℕ, (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType)
    (X S : Scheme.{u}) (g : X ⟶ S) (hg : IsProper g) (hS : IsAffine S)
    (hSN : IsLocallyNoetherian S) (G : X.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (n : ℕ) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj G)) := by
  have := hg
  have := hS
  have := hSN
  have := hG
  obtain ⟨hqc, hft⟩ := isQuasicoherent_isFiniteType_of_isCoherent G
  have := hqc
  exact moduleFinite_cohomology_of_isCoherent g G n
    (isCoherent_rightDerived_of_isFiniteType g G n (h X S g hg hSN G hqc hft n))

/-- **The finite-type clause of [Stacks, Tag 0EX4] over locally Noetherian bases is equivalent to
[Stacks, Tag 02O6].** Each side quantified over all of its own data; the left-hand side carries
no hypothesis on the fibres of `f`.

So over a locally Noetherian base the tag's finite-type clause is neither weaker nor stronger
than the finiteness theorem it is proved from: it *is* that theorem. In particular no
reformulation of the fibre-dimension bound can reduce the obligation, and the tag's own
generality — an arbitrary base — is the only part of it that asks for anything beyond
[Stacks, Tag 02O6]. -/
theorem forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsProper f → IsLocallyNoetherian Y →
        ∀ F : X.Modules, F.IsQuasicoherent → F.IsFiniteType →
          ∀ d : ℕ, (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType) ↔
      (∀ (X S : Scheme.{u}) (g : X ⟶ S), IsProper g → IsAffine S → IsLocallyNoetherian S →
        ∀ G : X.Modules, _root_.SheafOfModules.IsCoherent G → ∀ n : ℕ,
          Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
            (((moduleGlobalSections X).rightDerived n).obj G))) :=
  ⟨moduleFinite_cohomology_of_forall_isFiniteType_rightDerived,
    fun h X Y f hf hY F hqc hft d => by
      have := hf
      have := hY
      have := hqc
      have := hft
      exact isFiniteType_rightDerived_of_moduleFinite_cohomology f F d h⟩

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
