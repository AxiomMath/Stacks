module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosedImmersionCoherence
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent

/-!
# Finite type is tested on the direct image along a finite morphism

Let `f : X ⟶ Y` be a finite morphism of schemes and let `F` be a quasi-coherent
`𝒪_X`-module. Then `F` is of finite type if and only if `f_* F` is of finite type. This is
[Stacks, Tag 05B3].

## Main results

* `AlgebraicGeometry.isFiniteType_iff_pushforward_isFiniteType`: the equivalence.

## Implementation notes

Both implications are read off a single affine computation. On an affine open `V` of `Y` the
preimage `f ⁻¹ᵁ V` is affine and the sections of `f_* F` over `V` are the sections of `F` over
`f ⁻¹ᵁ V` with scalars restricted along `f.app V`, which is
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.specModulePushforwardIso`. Finiteness of
those sections detects finiteness of type in both directions, by
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.finite_specModule` one way and by
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn` the other, so
what is left is the algebra: along the *finite* ring map `f.app V` module-finiteness is
preserved by restriction of scalars, which is [Stacks, Tag 00GJ] and is supplied by
`AlgebraicGeometry.finite_restrictScalars_of_finite_hom`, and it is reflected by
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.finite_of_finite_restrictScalars`, which
needs nothing of the ring map at all.

The two implications are already available separately as
`AlgebraicGeometry.isFiniteType_pushforward_of_isFinite` and
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isFiniteType_of_isFiniteType_pushforward`,
but both of those carry a locally Noetherian hypothesis on the target which neither proof uses;
[Stacks, Tag 05B3] assumes no such thing, so the arguments are replayed here without it. The
covering used for the reverse implication is by the preimages of the affine opens of `Y`, which
cover `X` because the affine opens of `Y` cover `Y`.

## References

* [Stacks Project, Tag 05B3](https://stacks.math.columbia.edu/tag/05B3)
* [Stacks Project, Tag 00GJ](https://stacks.math.columbia.edu/tag/00GJ)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.ClosedImmersionCoherence

universe u

namespace AlgebraicGeometry

/-- The preimages of the affine opens of the target cover the source. -/
private theorem isOpenCover_preimage_affineOpens' {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsOpenCover (fun V : Y.affineOpens => f ⁻¹ᵁ (V : Y.Opens)) := by
  refine IsOpenCover.mk ?_
  rw [← Scheme.Hom.preimage_iSup]
  simp [iSup_affineOpens_eq_top Y]

/-- **Finite type ascends along a finite morphism.** This is
`AlgebraicGeometry.isFiniteType_pushforward_of_isFinite` without the locally Noetherian
hypothesis on the target, which that proof does not use. -/
alias isFiniteType_pushforward_of_isFinite' :=
  Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isFinite

/-- **Finite type descends along an affine morphism.** This is
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isFiniteType_of_isFiniteType_pushforward`
without the locally Noetherian hypothesis on the target, which that proof does not use. -/
theorem isFiniteType_of_isFiniteType_pushforward' {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent]
    (h : ((Scheme.Modules.pushforward f).obj F).IsFiniteType) : F.IsFiniteType := by
  have := h
  refine isFiniteType_of_cover_isFiniteTildeOn F (fun V : Y.affineOpens => f ⁻¹ᵁ (V : Y.Opens))
    (isOpenCover_preimage_affineOpens' f) (fun V => V.2.preimage f) fun V => ?_
  refine isFiniteTildeOn_of_finite_specModule F _ (V.2.preimage f) ?_
  have h2 : Module.Finite Γ(Y, (V : Y.Opens))
      ((ModuleCat.restrictScalars (f.app (V : Y.Opens)).hom).obj
        (specModule F (V.2.preimage f))) :=
    have : Module.Finite Γ(Y, (V : Y.Opens))
        (specModule ((Scheme.Modules.pushforward f).obj F) V.2) := finite_specModule _ V.2
    Module.Finite.equiv (specModulePushforwardIso f F V.2 (V.2.preimage f)).toLinearEquiv
  exact finite_of_finite_restrictScalars _ _ h2

end AlgebraicGeometry

end
