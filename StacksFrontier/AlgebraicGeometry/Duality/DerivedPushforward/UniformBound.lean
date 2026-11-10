module

public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.UniformBound
import StacksCore.Tactic.StacksAttribute

/-!
# The uniform cohomological bound for `Rf_*`, in the duality spelling

[Stacks, Tag 08D5] part (2) is available as
`AlgebraicGeometry.exists_isZero_homology_derivedPushforward`: for a quasi-compact and
quasi-separated `f : X ⟶ Y` with `Y` quasi-compact there is an integer `N`, depending on `f`
alone, with `H^m(Rf_*E) = 0` for `m ≥ b + N` whenever `E` has quasi-coherent cohomology living
in degrees `≤ b`. It is stated for `AlgebraicGeometry.RingedSpace.derivedPushforward` of the
underlying morphism of ringed spaces, and at the model `HasDerivedCategory.standard`.

The duality development spells derived direct image `Stacks.Duality.derivedPushforward` and its
source and target `Stacks.Duality.quasiCoherentDerivedCategory`. This module restates the bound
in that spelling, as `Stacks.Duality.exists_isLE_derivedPushforward_obj`, in the `IsLE` form its
consumers want: `Rf_*E` lives in degrees `≤ b + N`.

## Main results

* `Stacks.Duality.quasiCoherentDerivedCategory_eq` — the two spellings of `D_QCoh(𝒪_Z)` are the
  same type.
* `Stacks.Duality.derivedPushforward_eq_ringedSpace` — the two spellings of `Rf_*` are the same
  functor.
* `Stacks.Duality.exists_isLE_derivedPushforward_obj` — the uniform bound in the duality
  spelling.

## Implementation notes

*There is nothing to bridge beyond pinning the instance.* `HasDerivedCategory` is data-carrying,
so one expects two differently packaged derived categories to need a comparison equivalence, and
`Stacks.Duality.quasiCoherentDerivedCategory` takes `[HasDerivedCategory.{w} Z.Modules]` as a
binder where `AlgebraicGeometry.QuasicoherentDerivedCategory` resolves the instance at definition
time. But both are literally the `FullSubcategory` of
`DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Z.ringCatSheaf)`,
and `Stacks.Duality.derivedPushforward` and `AlgebraicGeometry.RingedSpace.derivedPushforward`
are literally the same total right derived functor of degreewise pushforward. So once the *same*
`HasDerivedCategory` instance is in force on both sides, each pair of spellings is definitionally
equal and the two lemmas below are `rfl`.

What makes the pairs come apart is instance resolution, not packaging. Two instances of
`HasDerivedCategory X.Modules` are in scope here: the global locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` at morphism universe `u`, and
`HasDerivedCategory.standard` at `u + 1`. A bare `quasiCoherentDerivedCategory X` picks up the
former and comes out at `u`, while everything imported from
`StacksFrontier/AlgebraicGeometry/UnboundedDerivedDirectImage/UniformBound.lean` is at `u + 1`;
the resulting `homologyFunctor`s differ in a universe argument and no statement about one applies
to the other. The fix is the `attribute [local instance 2000] HasDerivedCategory.standard` below
— the same idiom as in
`StacksFrontier/AlgebraicGeometry/Perfect/Coherator/QcqsQuasiCoherentDerivedPushforward.lean` —
which
makes the binder form resolve to `standard` too. No global priority is touched.

*The model of this statement is `standard`; the bound itself is no longer confined to it.* The
quasi-coherent inputs to [Stacks, Tag 0A9E] — direct sums in `D_QCoh(𝒪_X)`, Brown
representability, hence the right adjoint `a` itself — are only available at the locally small
model, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean`: with
`HasDerivedCategory.standard` the direct-sum hypothesis is false, not merely unavailable. Tag
08D5 is *proved* only at `standard`, its whole chain of Čech and basis inputs being stated there,
but it is *transported* off it in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/UniformBoundAnyModel.lean`, as
`Stacks.Duality.exists_isLE_derivedPushforward_obj_anyModel`. No comparison of the two
localizations is needed: the bound is restated with no derived category in it — a statement about
a complex and a K-injective resolution of it — and read back at an arbitrary
`[HasDerivedCategory.{w}]`, which is the route
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/QcqsPushforwardAnyModel.lean` takes for
part (1) of the same tag. Consumers that need the bound at a free model should use the
arbitrary-model form; `exists_isLE_derivedPushforward_obj` below is its instance at `standard`.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

attribute [local instance 2000] HasDerivedCategory.standard

/-- The two spellings of `D_QCoh(𝒪_Z)` — the binder form `quasiCoherentDerivedCategory` of
`StacksFrontier/AlgebraicGeometry/Duality/QuasiCoherentPushforwardAdjoint.lean` and the form
`AlgebraicGeometry.QuasicoherentDerivedCategory` of
`StacksFrontier/AlgebraicGeometry/Perfect/QuasiCoherentDerived/DirectSums.lean`, which fixes the
instance at definition time — are the same type once both resolve `HasDerivedCategory` to
`HasDerivedCategory.standard`. -/
theorem quasiCoherentDerivedCategory_eq (Z : Scheme.{u}) :
    quasiCoherentDerivedCategory Z = AlgebraicGeometry.QuasicoherentDerivedCategory Z :=
  rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The two spellings of `Rf_*` on the unbounded derived categories of sheaves of modules — the
scheme form `Stacks.Duality.derivedPushforward` and the ringed-space form
`AlgebraicGeometry.RingedSpace.derivedPushforward` — are the same functor. -/
theorem derivedPushforward_eq_ringedSpace :
    derivedPushforward f = RingedSpace.derivedPushforward f.toLRSHom.toShHom :=
  rfl

/-- **[Stacks, Tag 08D5] part (2), in the duality spelling.** Let `f : X ⟶ Y` be a quasi-compact
and quasi-separated morphism of schemes with `Y` quasi-compact. There is an integer `N`,
depending on `f` alone, such that `Rf_*E` lives in degrees `≤ b + N` for every object `E` of
`D_QCoh(𝒪_X)` living in degrees `≤ b`.

This is `AlgebraicGeometry.exists_isZero_homology_derivedPushforward` with `Rf_*` spelled
`Stacks.Duality.derivedPushforward` and the conclusion packaged as `DerivedCategory.IsLE`; the
degree drops by one in the repackaging because the source asserts vanishing *at* `b + N`. -/
@[stacks 08D5 "part (2), in the duality spelling"]
theorem exists_isLE_derivedPushforward_obj [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace Y] :
    ∃ N : ℤ, ∀ E : DerivedCategory X.Modules,
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent) →
      ∀ b : ℤ, E.IsLE b → ((derivedPushforward f).obj E).IsLE (b + N) := by
  obtain ⟨N, hN⟩ := AlgebraicGeometry.exists_isZero_homology_derivedPushforward f
  refine ⟨N - 1, fun E hE b hb ↦ ?_⟩
  rw [DerivedCategory.isLE_iff]
  exact fun i hi ↦ hN E hE b hb i (by omega)

end Stacks.Duality

end
