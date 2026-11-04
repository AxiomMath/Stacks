module

public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosedImmersionCoherence
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.PushforwardColimits.Affine
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Coherence of a higher direct image is invariant under an isomorphism of the base

Let `h : Y ⟶ T` be quasi-compact and quasi-separated, let `e : T ≅ T'` be an isomorphism of
locally Noetherian schemes and let `ℳ` be quasi-coherent on `Y`. Then `R^q (h ≫ e)_* ℳ` is
coherent exactly when `R^q h_* ℳ` is.

This is the statement that lets a result proved over the base `Spec R` be applied over an
arbitrary affine base: an affine scheme is the spectrum of its ring of global sections only up to
`AlgebraicGeometry.Scheme.isoSpec`, so a conclusion about `R^q g_*` for `g` a morphism to
`Spec Γ(T, 𝒪)` has to be moved back along that isomorphism.

The two inputs are both present and neither is about coherence.

* **The comparison.** `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` says an exact
  functor commutes with right derived functors; applied to
  `AlgebraicGeometry.Scheme.Modules.pushforwardComp` it gives
  `R^q h_* ℳ` pushed forward along `e` is `R^q (h ≫ e)_* ℳ`. The exactness it needs is
  `Stacks.AlgebraicGeometry.PushforwardColimits.isEquivalence_pushforward_of_isIso`: direct image
  along an isomorphism is an equivalence of module categories.
* **The test.** `Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isCoherent_pushforward_iff`
  tests coherence on the direct image along a closed immersion, and an isomorphism is one.

## Main definitions

* `Stacks.AlgebraicGeometry.CoherentImageBaseIso.rightDerivedPushforwardCompIsoHom`: the
  comparison `R^q h_* (-)` pushed forward along `e` with `R^q (h ≫ e)_* (-)`, as a natural
  isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.CoherentImageBaseIso.isCoherent_rightDerived_comp_isIso_iff`:
  **coherence of a higher direct image is invariant under an isomorphism of the base.**

## Implementation notes

**No tag attribute is attached.** This is a transport statement about two instances of coherence
and asserts neither; it is a step in the proof of [Stacks, Tag 02O4] and not a clause of it.

**Why the existing closed-immersion transport does not serve.**
`Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.isCoherent_rightDerived_pushforward_iff`
relates `R^n f_* (i_* 𝒢)` and `R^n (i ≫ f)_* 𝒢` for `i` a closed immersion, with `i` the *first*
factor of the composite. Here the isomorphism is the *second* factor, so that statement does not
apply however the maps are named, and the comparison has to be built from the composition
isomorphism instead.

**One hypothesis is restated by hand rather than inferred.** In the backward direction the
hypothesis is coherence of `(Scheme.Modules.pushforward e.hom).obj (R^q h_* ℳ)` while the
instance the transport needs is for the same object written as a value of the composite functor
`R^q h_* ⋙ e_*`. The two are definitionally equal but instance search does not see through the
composite, so the hypothesis is re-ascribed at the composite spelling before being used; this is
the same hazard the `⋙` spellings cause elsewhere in this development.

**Quasi-coherence of the higher direct image is found by instance search**, being
[Stacks, Tag 01XJ] for a quasi-compact quasi-separated morphism; it is what
`isCoherent_pushforward_iff` requires of the module it tests.

## References

* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.ModuleComparison

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.CoherentImageBaseIso

variable {Y T T' : Scheme.{u}}

/-- **The higher direct image along `h ≫ e` is the higher direct image along `h` pushed forward
along `e`**, for `e` an isomorphism of schemes, as a natural isomorphism of functors.

Direct image along an isomorphism is an equivalence of module categories, hence exact, so
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` applies to the composition isomorphism
`AlgebraicGeometry.Scheme.Modules.pushforwardComp`. -/
def rightDerivedPushforwardCompIsoHom (h : Y ⟶ T) (e : T ≅ T') (q : ℕ) :
    (Scheme.Modules.pushforward h).rightDerived q ⋙ Scheme.Modules.pushforward e.hom ≅
      (Scheme.Modules.pushforward (h ≫ e.hom)).rightDerived q :=
  rightDerivedCompIso (Scheme.Modules.pushforward h) (Scheme.Modules.pushforward e.hom)
    (Scheme.Modules.pushforward (h ≫ e.hom)) (Scheme.Modules.pushforwardComp h e.hom) q

/-- **Coherence of a higher direct image is invariant under an isomorphism of the base.** For
`h : Y ⟶ T` quasi-compact and quasi-separated, `e : T ≅ T'` an isomorphism of locally Noetherian
schemes and `ℳ` quasi-coherent, `R^q (h ≫ e)_* ℳ` is coherent exactly when `R^q h_* ℳ` is.

This is what moves a conclusion proved over `Spec Γ(T, 𝒪)` back to `T` itself, an affine scheme
being its own spectrum only up to `AlgebraicGeometry.Scheme.isoSpec`. -/
theorem isCoherent_rightDerived_comp_isIso_iff [IsLocallyNoetherian T] [IsLocallyNoetherian T']
    (h : Y ⟶ T) (e : T ≅ T') [AlgebraicGeometry.QuasiCompact h]
    [AlgebraicGeometry.QuasiSeparated h] (M : Y.Modules) [M.IsQuasicoherent] (q : ℕ) :
    (((Scheme.Modules.pushforward (h ≫ e.hom)).rightDerived q).obj M).IsCoherent ↔
      (((Scheme.Modules.pushforward h).rightDerived q).obj M).IsCoherent := by
  refine Iff.trans ?_ (Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isCoherent_pushforward_iff
    e.hom (((Scheme.Modules.pushforward h).rightDerived q).obj M))
  constructor
  · intro _
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      ((rightDerivedPushforwardCompIsoHom h e q).app M)
  · intro (_ : (((Scheme.Modules.pushforward h).rightDerived q ⋙
        Scheme.Modules.pushforward e.hom).obj M).IsCoherent)
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      ((rightDerivedPushforwardCompIsoHom h e q).app M).symm

end Stacks.AlgebraicGeometry.CoherentImageBaseIso

end
