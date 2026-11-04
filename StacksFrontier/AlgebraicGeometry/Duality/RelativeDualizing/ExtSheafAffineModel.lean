module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# The affine model of a coherent sheaf of modules, in the dualizing-model spelling

On a locally Noetherian scheme a coherent sheaf of modules is, over every affine open `U`, the
sheaf associated with a finite `Γ(X, U)`-module. That is condition (4) of [Stacks, Tag 01XZ] and
it is already available in this repository as
`Stacks.AlgebraicGeometry.CoherentTFAE.IsFiniteTildeOn`, the fourth clause of
`Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae`.

What this file adds is only a change of spelling. The duality development writes an affine model
through the *restriction* functor along `IsAffineOpen.isoSpec`, as the composite
`tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom`; this is the shape of the
second conjunct of `Stacks.Duality.IsDualizingModelOn` and the shape consumed by
`Stacks.Duality.affineStalkNatIso` and by
`Stacks.Duality.nonempty_stalk_iso_extendScalars_of_affineModel`. Condition (4) is stated through
the *pullback* functor instead. The two differ by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and composing with that
isomorphism is the whole content below.

## Main results

* `Stacks.Duality.exists_affineModel_of_isCoherent` — a coherent sheaf of modules on a locally
  Noetherian scheme has, on every affine open `U`, a finite `Γ(X, U)`-module as its affine model,
  in the `Scheme.Modules.restrictFunctor` spelling used by the duality development.

## Implementation notes

No transport across `AlgebraicGeometry.Scheme.Opens.topIso` is needed, and no comparison between
`IsAffineOpen.isoSpec` and `AlgebraicGeometry.Scheme.isoSpec`. Routing through
`Stacks.AlgebraicGeometry.CoherentTFAE.IsFiniteTildeOn` rather than through essential
surjectivity of the tilde on the affine scheme `U.toScheme`
(`AlgebraicGeometry.Scheme.Modules.exists_iso_tildeOf`) avoids both: condition (4) is already
phrased over the ring `Γ(X, U)` and already uses `hU.isoSpec`, so the only gap left is
pullback-versus-restriction along a single morphism.

The module is `Module.Finite`, not merely `Module.FinitePresentation`, directly from condition
(4); over the Noetherian ring `Γ(X, U)` the two notions agree anyway, so no further argument is
required.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0ECM](https://stacks.math.columbia.edu/tag/0ECM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

/-- **A coherent sheaf of modules has a finite affine model on every affine open.** For `F`
coherent on a locally Noetherian scheme `X` and `U` an affine open, there is a finite
`Γ(X, U)`-module `M` with `F|_U ≅ M^~` read through `hU.isoSpec`.

This is clause (4) of [Stacks, Tag 01XZ] — available here as
`Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae` — restated with
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` in place of
`AlgebraicGeometry.Scheme.Modules.pullback`, which is the form the dualizing-model predicate
`Stacks.Duality.IsDualizingModelOn` and the stalk comparison
`Stacks.Duality.nonempty_stalk_iso_extendScalars_of_affineModel` are stated in. -/
theorem exists_affineModel_of_isCoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ M : ModuleCat.{u} Γ(X, U), Module.Finite Γ(X, U) M ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj F ≅
        (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj M) := by
  have h4 : ∀ (V : X.Opens) (hV : IsAffineOpen V),
      Stacks.AlgebraicGeometry.CoherentTFAE.IsFiniteTildeOn F V hV :=
    ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X F).out 1 4).mp
      (inferInstance : _root_.SheafOfModules.IsCoherent F)
  obtain ⟨M, hM, ⟨e⟩⟩ := h4 U hU
  exact ⟨M, hM, ⟨e ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app
    ((tilde.functor Γ(X, U)).obj M)).symm⟩⟩

end Stacks.Duality

end
