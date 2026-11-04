module

public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.StalkFibreProper
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.TwistPullbackInteger
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DegreeZeroSections
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Stalk
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.TwistFibreSectionsSurjective
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic

/-!
# Sections of a large twist restrict onto the fibre, over the local ring of the base

Let `f : X ⟶ S` be proper with `S` locally Noetherian, let `ℒ` be an invertible `𝒪_X`-module and
let `y` be a point of `S` at which `ℒ_y` is ample on the fibre `X_y`.  Write
`X' = X ×_S Spec 𝒪_{S, y}` and let `V ⊂ X'` be the closed subscheme cut out by `𝔪 𝒪_{X'}` —
the fibre, by `Stacks.AmpleFibreNeighbourhood.stalkFibreIso`.  This file proves that for every
large `d`

`Γ(X', (ℒ ^⊗ d)|_{X'}) ⟶ Γ(V, (ℒ ^⊗ d)|_V)`

is **surjective**.  That is assertion (B) of [Stacks, Tag 0D2M] over the local base `𝒪_{S, y}`,
at the source's own hypotheses and in the spelling the proof of [Stacks, Tag 0D2N] consumes:
restriction of sections along the closed immersion of the fibre, rather than a map between
right-derived functors.

## Main results

* `Stacks.AmpleFibreNeighbourhood.exists_surjective_pullbackGlobalSections_baseFibre`:
  the statement for an arbitrary Noetherian local ring `A` mapping to `S`.
* `Stacks.AmpleFibreNeighbourhood.exists_surjective_pullbackGlobalSections_stalkFibre`:
  the same at `A = 𝒪_{S, y}`, with the hypothesis in the form [Stacks, Tag 0D2N] grants it —
  `ℒ_y` ample on `X_y`.
* `Stacks.AmpleFibreNeighbourhood.surjective_pullbackGlobalSections_congr`: surjectivity of
  restriction of sections only depends on the module up to isomorphism.

## The route

Everything is a composition of facts already in the library.

* `Stacks.Cohomology.FormalFunctions.exists_surjective_fibreCohomology_twistModule` is assertion
  (B) over a local base, and it now carries no hypothesis beyond the source's: the vanishing of
  `H ¹` on the graded layers is proved from ampleness on the fibre by
  `Stacks.GradedProperCohomology.exists_isZero_rightDerived_kernelIdealPowerQuotientDropTwist`.
  Its data are the closed immersion `V ⟶ X'` with ideal sheaf `𝔪 𝒪` — the canonical
  `Scheme.IdealSheafData.subschemeι`, whose kernel is the ideal sheaf by
  `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι` — together with the structure morphism
  to `Spec κ(y)`, its properness and the square it sits in, all three from
  `StacksFrontier/AlgebraicGeometry/AmpleFibreNeighbourhood/StalkFibreProper.lean`, and ampleness on
  `V`, which the same file derives from ampleness on `X_y`.
* Its conclusion is about right-derived functors in degree zero;
  `Stacks.Cohomology.ClosedImmersion.surjective_pullbackGlobalSections_iff_rightDerivedZero`
  says that this is literally the surjectivity of `AlgebraicGeometry.pullbackGlobalSections`.
* The module it twists is `𝒪_{X'} ⊗ ((X' ⟶ X)^* ℒ) ^⊗ d`;
  `Stacks.AmpleFibreNeighbourhood.twistUnitPullbackIso` identifies it with
  `(X' ⟶ X)^* (ℒ ^⊗ d)`, and `surjective_pullbackGlobalSections_congr` carries the surjectivity
  across.
* The structure sheaf of `X'` is coherent because `X'` is locally Noetherian, being locally of
  finite type over `Spec 𝒪_{S, y}` (`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit`).

## Why the general form is stated in `A`, and the one place `show` is needed

The specialisation `A = 𝒪_{S, y}` is given as `↥(S.presheaf.stalk y)`, and
`CommRingCat.of ↥(S.presheaf.stalk y)` is `S.presheaf.stalk y` by `rfl`.  Passing
`AlgebraicGeometry.Scheme.fromSpecStalk` for `c` without a type ascription makes unification
solve the `CommRing` instance of `A` *structurally*, as the `str` field of the stalk rather than
as the instance `inferInstance` finds, and then `IsLocalRing A` is not synthesised — not even
from a local `haveI`, whose statement uses the other instance.  The one-line `show` on `c` fixes
the instance to the canonical one, after which the defeq `CommRingCat.of ↥R = R` is checked
directly and everything resolves.  This is why the mathematics is stated for a variable `A` and
instantiated exactly once.

## No attribute

No `@[stacks]` attribute is attached.  Assertion (B) over a local base carries none either, for
the reason recorded in `../FormalFunctions/TwistFibreSectionsSurjective.lean`: the tag's
statement is the conjunction of its two assertions over a general Noetherian base, and the
reduction of such a base to `Spec 𝒪_{S, y}` is not performed in either file.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence

universe u

namespace Stacks.AmpleFibreNeighbourhood


/-- **Surjectivity of restriction of sections depends on the module only up to isomorphism.**
Naturality of `AlgebraicGeometry.pullbackGlobalSections` in the module
(`AlgebraicGeometry.pullbackGlobalSections_natural`) conjugates the two maps by the isomorphism
on sections upstairs and its pullback downstairs. -/
theorem surjective_pullbackGlobalSections_congr {P Q : Scheme.{u}} (i : P ⟶ Q) {N N' : Q.Modules}
    (e : N ≅ N') (h : Function.Surjective (pullbackGlobalSections i N)) :
    Function.Surjective (pullbackGlobalSections i N') := by
  intro z
  obtain ⟨w, hw⟩ := h (((Scheme.Modules.pullback i).map e.inv).app ⊤ z)
  refine ⟨e.hom.app ⊤ w, ?_⟩
  rw [pullbackGlobalSections_natural i e.hom w, hw]
  have hcomp : ((Scheme.Modules.pullback i).map e.inv ≫
      (Scheme.Modules.pullback i).map e.hom) = 𝟙 _ := by
    rw [← Functor.map_comp, e.inv_hom_id]
    exact CategoryTheory.Functor.map_id _ _
  exact (ConcreteCategory.congr_hom
    (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) hcomp) z).trans (CategoryTheory.id_apply z)

/-- **Assertion (B) of [Stacks, Tag 0D2M] over a Noetherian local base, in the sections
spelling.**  For `f : X ⟶ S` proper, `A` a Noetherian local ring mapping to `S` by `c`, and `ℒ`
an invertible `𝒪_X`-module whose restriction to the subscheme of `X ×_S Spec A` cut out by
`𝔪 𝒪` is ample, there is a `d₀` such that for every `d ≥ d₀` restriction of sections

`Γ(X ×_S Spec A, (ℒ ^⊗ d)|) ⟶ Γ(V, (ℒ ^⊗ d)|_V)`

is surjective.  The route is in the module docstring. -/
theorem exists_surjective_pullbackGlobalSections_baseFibre
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (c : Spec (CommRingCat.of A) ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple (baseIdealSheaf A (IsLocalRing.maximalIdeal A) (pullback.snd f c)).subscheme
      (pullbackModule
        (baseIdealSheaf A (IsLocalRing.maximalIdeal A) (pullback.snd f c)).subschemeι
        (pullbackModule (pullback.fst f c) L))) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Function.Surjective (pullbackGlobalSections
        (baseIdealSheaf A (IsLocalRing.maximalIdeal A) (pullback.snd f c)).subschemeι
        (pullbackModule (pullback.fst f c) (tensorPowModule X L d))) := by
  have : IsLocallyNoetherian (Limits.pullback f c) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f c)
  have : IsInvertibleModule (Limits.pullback f c) (pullbackModule (pullback.fst f c) L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ L
  have : (unitModule (Limits.pullback f c)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit _
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.Cohomology.FormalFunctions.exists_surjective_fibreCohomology_twistModule
      A (pullback.snd f c) inferInstance
      (unitModule (Limits.pullback f c)) (pullbackModule (pullback.fst f c) L)
      (baseIdealSheaf A (IsLocalRing.maximalIdeal A) (pullback.snd f c)).subschemeι
      (Scheme.IdealSheafData.ker_subschemeι _)
      (baseFibreToQuot f A (IsLocalRing.maximalIdeal A) c)
      (isProper_baseFibreToQuot f A (IsLocalRing.maximalIdeal A) c)
      (baseFibreToQuot_comp f A (IsLocalRing.maximalIdeal A) c) hL
  refine ⟨d₀, fun d hd => ?_⟩
  refine surjective_pullbackGlobalSections_congr _
    (twistUnitPullbackIso (pullback.fst f c) L d) ?_
  exact Stacks.Cohomology.ClosedImmersion.surjective_pullbackGlobalSections_iff_rightDerivedZero
    _ _ |>.1 (hd₀ d hd)

/-- **The same at `A = 𝒪_{S, y}`, with [Stacks, Tag 0D2N]'s own hypothesis.**  If `ℒ_y` is ample
on the fibre `X_y` then, for every large `d`, sections of `ℒ ^⊗ d` on `X ×_S Spec 𝒪_{S, y}`
restrict onto all sections on the subscheme cut out by `𝔪 𝒪` — which is the fibre, by
`Stacks.AmpleFibreNeighbourhood.stalkFibreIso`.

Ampleness is carried onto that subscheme by
`Stacks.AmpleFibreNeighbourhood.isAmple_pullbackModule_stalkFibre`. -/
theorem exists_surjective_pullbackGlobalSections_stalkFibre
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsLocallyNoetherian S]
    (L : X.Modules) [IsInvertibleModule X L] (y : S)
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Function.Surjective (pullbackGlobalSections
        (stalkBaseChangeFibreIdeal f y).subschemeι
        (pullbackModule (pullback.fst f (S.fromSpecStalk y)) (tensorPowModule X L d))) :=
  exists_surjective_pullbackGlobalSections_baseFibre f ↥(S.presheaf.stalk y)
    (show Spec (CommRingCat.of ↥(S.presheaf.stalk y)) ⟶ S from S.fromSpecStalk y) L
    (isAmple_pullbackModule_stalkFibre f y L hL)

end Stacks.AmpleFibreNeighbourhood

end
