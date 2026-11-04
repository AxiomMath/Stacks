module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.ProperAlgebraBaseChange.Basic

/-!
# Cohomology across the base change `X ×_{Spec A} Spec B`

The projection `π : X' = X ×_{Spec A} Spec B ⟶ X` is affine
(`Stacks.ProperAlgebraBaseChange.isAffineHom_proj`), so [Stacks, Tag 089W] applies to it: the
cohomology of a quasi-coherent module `F'` on `X'` is the cohomology on `X` of its direct image.
This file records that comparison in the spelling the graded-cohomology chapter uses, and uses it
together with the properness of `f' : X' ⟶ Spec B` to state
[Stacks, Tag 0897] part (1) with the base change *constructed* rather than assumed.

## Main results

* `Stacks.ProperAlgebraBaseChange.cohomologyProjIso`: `H^p(X', F') = H^p(X, π_* F')`, as
  `Γ(X, ⊤)`-modules — [Stacks, Tag 089W] at the affine projection `π`.
* `Stacks.ProperAlgebraBaseChange.moduleFinite_gradedCohomologySum_baseChange`: the conclusion of
  [Stacks, Tag 0897] part (1) with `X'` and `f'` taken to be the base change built in
  `Stacks.ProperAlgebraBaseChange.Basic`.

## Implementation notes

**No `@[stacks]` attribute is placed in this file.** `cohomologyProjIso` is the instance at `π` of
[Stacks, Tag 089W], which is carried in its own generality by
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`, and
`moduleFinite_gradedCohomologySum_baseChange` is a *weaker* statement than
[Stacks, Tag 0897] part (1): it still carries `F'` and the `B`-linear comparison `cmp` as
hypotheses. What it removes from
`Stacks.AlgebraicGeometry.GradedProperCohomology.moduleFinite_gradedCohomologySum` is the scheme
`X'`, the morphism `f'` and its properness — those three are now the constructed
`Stacks.ProperAlgebraBaseChange.scheme`, `Stacks.ProperAlgebraBaseChange.toSpec` and the instance
`Stacks.ProperAlgebraBaseChange.isProper_toSpec`.

What is *not* discharged, and what still blocks [Stacks, Tag 0897] part (1) outright, is the
*coherence* of the module `F'` on `X'` and the graded `B`-action on `⨁ₙ H^p(X, Fₙ)`. `F'` itself
now exists: `Stacks.ProperAlgebraBaseChange.descendedModule`. Using it needs the graded algebra
`𝓑` to be identified with `f^* B̃`, and the statement of [Stacks, Tag 0897] in
`StacksFrontier/AlgebraicGeometry/GradedProperCohomology/ProperCohomologyFiniteness.lean` leaves
`𝓑` an unconstrained graded algebra on `X`, so no such identification is available to quantify
over there.

**Tying `𝓑` to `B` is not by itself an improvement, and must not be done on its own.** The
source sets `𝓑 = f^* B̃`, so constraining `𝓑` is faithful rather than a narrowing — but adding
that constraint while `F'` and `cmp` stay as hypotheses only removes instances of a statement
without removing an assumption, which is a strictly narrower [Stacks, Tag 0897]. The constraint
earns its place only together with a *coherent* `F'`.

**`F'` is constructed.** [Stacks, Tag 01SB] is an equivalence from the quasi-coherent
`𝒪_{X'}`-modules to the quasi-coherent modules over the *sheaf of rings* `π_* 𝒪_{X'}`, and
`isEquivalence_pushforward_proj` has it at `π` already, so `F'` is the image of `⨁ₙ Fₙ` under its
quasi-inverse. Every input of that is now in place:

* the graded action of `𝓑` gives only the degreewise bilinear maps of
  `SheafOfModules.GradedModule`, and assembling them into a single action is
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/UngradedModules.lean` —
  `Stacks.RightGradedModule.moduleTotal` makes the direct sum of the homogeneous pieces a module
  over `Stacks.GradedAlgebra.totalPresheaf` over each open, and
  `SheafOfModules.GradedModule.ungradedSheafModule` sheafifies that into a sheaf of modules over
  `SheafOfModules.GradedAlgebra.ungradedSheaf`;
* `Stacks.ProperAlgebraBaseChange.ungradedSheafIsoPushforwardProj` identifies that sheaf of rings
  with `π_* 𝒪_{X'}` given the source's own `𝓑 ≅ f^* B̃` as algebra sheaves, and
  `Stacks.ProperAlgebraBaseChange.ungradedModuleOverPushforwardProj` is `⨁ₙ Fₙ` with its scalars
  restricted along it — and it is a module over the right object rather than an isomorphic copy,
  because `Stacks.ProperAlgebraBaseChange.ringSheaf_pushforwardAlgebra_eq` says the two spellings
  of `π_* 𝒪_{X'}` as a sheaf of rings are *equal*;
* `Stacks.ProperAlgebraBaseChange.isQuasicoherent_ungradedModuleOverPushforwardProj_of_pieces`
  supplies the quasi-coherence the equivalence is between, out of quasi-coherence of the pieces
  `Fₙ` alone. Its content is that the underlying `𝒪_X`-module of the realisation is the sheaf
  coproduct `∐ₙ Fₙ` (`SheafOfModules.GradedModule.coprodIsoUngradedSheafModule`, the route the
  *algebra* case takes in
  `StacksFrontier/AlgebraicGeometry/DeRham/LineBundle/Quasicoherent.lean`, with
  `Stacks.RightGradedModule.act_structureMap` as its input), together with closure of
  quasi-coherence on a scheme under colimits
  (`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit`).

`Stacks.ProperAlgebraBaseChange.descendedModule` is the resulting `F'`,
`isQuasicoherent_descendedModule` its quasi-coherence and `pushforwardDescendedModuleIso` the
identification `π_* F' ≅ ⨁ₙ Fₙ`.

**What remains.** Two things, and [Stacks, Tag 0897] part (1) needs both.

* *Coherence of `F'`.* `F'` is quasi-coherent, so by [Stacks, Tag 01XZ]
  (`Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae`) what is left is that `X'` is
  locally Noetherian and that `F'` is of finite type. **The first is now proved** in the setting
  of the tag — `A` Noetherian, `B` of finite type over `A`, `f` proper —
  as `Stacks.ProperAlgebraBaseChange.isLocallyNoetherian_scheme`, so
  `Stacks.ProperAlgebraBaseChange.isCoherent_descendedModule` reduces coherence of `F'` to its
  finite type outright. The finite type has to come from the graded module's own finiteness
  hypothesis `Stacks.Coherent.IsFiniteTypeOnAffine`, which is a statement about finitely many
  homogeneous generators of the sections over each affine open of `X`;
  `Stacks.ProperAlgebraBaseChange.isCoherent_descendedModule_of_finite_sections_realisation`
  reduces it to the statement that those sections are a finite module over the sections of the
  ungraded realisation of `𝓑`, which is a statement about the graded data alone. The one step
  still missing there is that the sheafification unit
  `⨁ₙ Γ(V, Fₙ) ⟶ Γ(V, ⨁ₙ Fₙ)` is *surjective* over a quasi-compact `V`.
* *`B`-linearity of the comparison.* The `B`-action on `⨁ₙ H^p(X, Fₙ)` is transported from
  `H^p(X', F')` along `cohomologyProjIso` and `pushforwardDescendedModuleIso`, which needs
  cohomology on `X` to commute with the coproduct `⨁ₙ`; that input is carried, as
  [Stacks, Tag 01FF] (`Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact`),
  for filtered colimits over a quasi-compact open.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.GradedProperCohomology

universe u

namespace Stacks.ProperAlgebraBaseChange

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **[Stacks, Tag 089W] at the affine projection `π : X ×_{Spec A} Spec B ⟶ X`.** For a
quasi-coherent module `F'` on the base change, the cohomology of `F'` upstairs is the cohomology
of `π_* F'` on `X`, in every degree, as `Γ(X, ⊤)`-modules after restriction of scalars along
`π^♯`. -/
def cohomologyProjIso (F' : (scheme A B f).Modules) [F'.IsQuasicoherent] (p : ℕ) :
    (ModuleCat.restrictScalars (proj A B f).appTop.hom).obj
        (cohomologyOf (scheme A B f) p F') ≅
      cohomologyOf X p ((Scheme.Modules.pushforward (proj A B f)).obj F') :=
  Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward (proj A B f) F' p

/-- **[Stacks, Tag 0897] part (1), with the base change constructed.** Let `A` be a Noetherian
ring, `B` a finitely generated graded `A`-algebra, `f : X ⟶ Spec A` proper and `F` a
quasi-coherent graded `𝓑`-module of finite type. If the graded cohomology `⨁ₙ H^p(X, Fₙ)` carries
a `B`-action that a `B`-linear isomorphism identifies with the cohomology of a coherent module
`F'` on `X ×_{Spec A} Spec B`, then it is a finite `B`-module.

This is `Stacks.AlgebraicGeometry.GradedProperCohomology.moduleFinite_gradedCohomologySum` with
its binders `X'`, `f'` and `[IsProper f']` replaced by the actual base change: `X'` is
`Stacks.ProperAlgebraBaseChange.scheme`, `f'` is `Stacks.ProperAlgebraBaseChange.toSpec`, and
properness is the instance `Stacks.ProperAlgebraBaseChange.isProper_toSpec`, which is
[Stacks, Tag 01W4]. The coherent `F'` and the `B`-linear comparison remain hypotheses; see the
module docstring for why. -/
theorem moduleFinite_gradedCohomologySum_baseChange [IsNoetherianRing A]
    {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B] [IsProper f]
    (F : _root_.SheafOfModules.GradedModule 𝓑)
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : F.IsFiniteType) (p : ℕ)
    (F' : (scheme A B f).Modules) [F'.IsCoherent]
    [Module B (gradedCohomologySum F p)]
    (cmp : gradedCohomologySum F p ≃ₗ[B]
      ↥((ModuleCat.restrictScalars (specAlgebraRingHom B (toSpec A B f))).obj
        (cohomologyOf (scheme A B f) p F'))) :
    Module.Finite B (gradedCohomologySum F p) :=
  moduleFinite_gradedCohomologySum A 𝒜 f F hqc hft p (toSpec A B f) F' cmp

end Stacks.ProperAlgebraBaseChange

end
