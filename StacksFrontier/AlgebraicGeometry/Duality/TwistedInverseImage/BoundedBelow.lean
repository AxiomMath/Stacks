module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel

/-!
# The twisted inverse image of a qcqs morphism preserves bounded-below complexes

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes and let
`a = f^× : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` be the right adjoint of `Rf_*` of [Stacks, Tag 0A9E].
[Stacks, Tag 0A9I] says that `a` maps `D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)`, and more precisely
that there is an integer `N` such that `H^i(K) = 0` for `i ≤ c` implies `H^i(a(K)) = 0` for
`i ≤ c - N`.

Here `a` is `Stacks.Duality.twistedInverseImage f hpush` at the locally small model of the derived
categories (`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`), the model at which
[Stacks, Tag 0A9E] is proved: its adjointness is the instance
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs`, and the
quasi-coherence input `hpush` ([Stacks, Tag 08D5] part (1)) is
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`.

The proof is the source's, carried out in `Stacks.Duality.isGE_rightAdjoint_obj` for an arbitrary
right adjoint of `Rf_*`; the uniform bound it needs ([Stacks, Tag 08D5] part (2)) is supplied at
the locally small model by `Stacks.Duality.exists_isLE_derivedPushforward_obj_anyModel`.

## Main results

* `Stacks.Duality.exists_isGE_twistedInverseImage_obj` — the bound in `IsGE` form: there is `N`
  with `a(K)` in degrees `≥ c - N` whenever `K` is in degrees `≥ c`.
* `Stacks.Duality.isBoundedBelow_twistedInverseImage_obj` — `a` carries bounded-below objects to
  bounded-below objects.
* `Stacks.Duality.isBoundedBelow_twistedInverseImage_obj_and_exists_bound` —
  **[Stacks, Tag 0A9I]**, both sentences of the lemma, in the source's indexing.

## References

* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **The bound of [Stacks, Tag 0A9I] in `IsGE` form.** For a morphism `f : X ⟶ Y` of
quasi-compact quasi-separated schemes there is an integer `N` such that the twisted inverse image
`f^×` carries an object of `D_QCoh(𝒪_Y)` living in degrees `≥ c` to one living in degrees
`≥ c - N`. -/
theorem exists_isGE_twistedInverseImage_obj :
    ∃ N : ℤ, ∀ (K : quasiCoherentDerivedCategory Y) (c : ℤ), K.obj.IsGE c →
      ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        K).obj.IsGE (c - N) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj_anyModel.{u} f
  exact ⟨N, fun K c hK ↦ isGE_rightAdjoint_obj f _
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    N hN K c hK⟩

/-- **The twisted inverse image of a qcqs morphism preserves `D^+`.** For a morphism
`f : X ⟶ Y` of quasi-compact quasi-separated schemes, `f^× : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` carries
an object with bounded-below cohomology to an object with bounded-below cohomology; that is, it
maps `D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)`. This is the first sentence of [Stacks, Tag 0A9I]. -/
theorem isBoundedBelow_twistedInverseImage_obj (K : quasiCoherentDerivedCategory Y)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    DerivedCategoryB.IsBoundedBelow
      ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        K).obj := by
  obtain ⟨N, hN⟩ := exists_isGE_twistedInverseImage_obj f
  obtain ⟨n₀, hn₀⟩ := hK
  have := hN K n₀ ((DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hn₀ i hi)
  exact ⟨n₀ - N, fun n hn ↦ DerivedCategory.isZero_of_isGE _ (n₀ - N) n hn⟩

/-- **[Stacks, Tag 0A9I].** Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated
schemes and let `a = f^× : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` be the right adjoint of `Rf_*` of
[Stacks, Tag 0A9E]. Then `a` maps `D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)`. In fact, there exists an
integer `N` such that `H^i(K) = 0` for `i ≤ c` implies `H^i(a(K)) = 0` for `i ≤ c - N`. -/
@[stacks 0A9I]
theorem isBoundedBelow_twistedInverseImage_obj_and_exists_bound :
    (∀ K : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow K.obj →
      DerivedCategoryB.IsBoundedBelow
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          K).obj) ∧
    ∃ N : ℤ, ∀ (K : quasiCoherentDerivedCategory Y) (c : ℤ),
      (∀ i ≤ c, IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj K.obj)) →
      ∀ i ≤ c - N, IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          K).obj) := by
  refine ⟨isBoundedBelow_twistedInverseImage_obj f, ?_⟩
  obtain ⟨N, hN⟩ := exists_isGE_twistedInverseImage_obj f
  refine ⟨N, fun K c hK i hi ↦ ?_⟩
  have := hN K (c + 1) ((DerivedCategory.isGE_iff _ _).2 fun j hj ↦ hK j (by omega))
  exact DerivedCategory.isZero_of_isGE _ (c + 1 - N) i (by omega)

end Stacks.Duality

end
