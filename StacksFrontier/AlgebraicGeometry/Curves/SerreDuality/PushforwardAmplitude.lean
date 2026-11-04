module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject

/-!
# The cohomological amplitude of `Rf_*` on a curve over a field

Let `k` be a field and let `f : X ⟶ Spec(k)` be proper with `X` of topological Krull dimension at
most one. For a quasi-coherent `𝒪_X`-module `F` placed in degree `a` of the unbounded derived
category, the derived direct image `Rf_*(F[a])` lives in degrees `≤ a + 1`.

The two inputs are Grothendieck vanishing above the dimension, [Stacks, Tag 02UZ], and the
comparison of [Stacks, Tag 01XK] between the cohomology of `F` and the global sections of the
higher direct images over the affine base `Spec(k)`: on `Spec(k)` a quasi-coherent module with no
global sections vanishes, so the vanishing `H^n(X, F) = 0` for `n ≥ 2` of [Stacks, Tag 02UZ]
gives `R^n f_* F = 0` for `n ≥ 2`, and the cohomology sheaves of `Rf_*(F[a])` in degrees above
`a + 1` are exactly those higher direct images.

## Main results

* `AlgebraicGeometry.isZero_rightDerived_pushforward_of_topologicalKrullDim_le` — the higher
  direct images `R^n f_* F` vanish for `n ≥ 2`.
* `Stacks.Duality.isLE_derivedPushforward_singleFunctor_obj` — `Rf_*(F[a])` lies in degrees
  `≤ a + 1`.
* `Stacks.Duality.isLE_one_derivedPushforward_singleFunctor_zero_obj` — the case `a = 0`:
  `Rf_*F` lies in degrees `≤ 1`.

## Implementation notes

The model of the two unbounded derived categories is an arbitrary `[HasDerivedCategory.{w}]`
rather than `CategoryTheory.HasDerivedCategory.standard`. That is what makes the statement
available at the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which
is the model at which the twisted inverse image of [Stacks, Tag 0A9E] exists, and it costs
nothing: the identification of the cohomology sheaves of `Rf_*(F[a])` with the classical higher
direct images is `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`, whose model
binders are free and which takes the right derived functor as data, with
`Stacks.Duality.derivedPushforwardUnit` as the comparison and
`AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective` as the resolutions.

The vanishing of `R^n f_* F` is read off global sections rather than proved locally. Over the
affine base the comparison `Stacks.Cohomology.AffineBase.affineBaseHigherDirectImageIso` of
[Stacks, Tag 01XK] identifies `Γ(Spec(k), R^n f_* F)` with `H^n(X, F)` restricted along `f^♯`,
and restriction of scalars does not change the carrier of a module, so the vanishing of
`AlgebraicGeometry.cohomologyOverField` transfers through `ModuleCat.isZero_iff_subsingleton`.
`AlgebraicGeometry.isQuasicoherent_rightDerived` ([Stacks, Tag 01XJ]) supplies the quasi-coherence
that `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine` asks for.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

/-- **The higher direct images of a quasi-coherent module on a curve over a field vanish above
degree one.** For `f : X ⟶ Spec(k)` proper with `X` of topological Krull dimension at most one
and `F` quasi-coherent, `R^n f_* F = 0` for every `n ≥ 2`.

Over the affine base `Spec(k)` the module `R^n f_* F` is quasi-coherent ([Stacks, Tag 01XJ]) and
so vanishes as soon as its global sections do; those are `H^n(X, F)` by [Stacks, Tag 01XK], and
`H^n(X, F) = 0` for `n` above the dimension by [Stacks, Tag 02UZ]. -/
theorem isZero_rightDerived_pushforward_of_topologicalKrullDim_le (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules) [hF : F.IsQuasicoherent]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) {n : ℕ} (hn : 1 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj F) := by
  apply Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine
  refine IsZero.of_iso ?_
    ((Stacks.Cohomology.AffineBase.affineBaseHigherDirectImageIso f n).app ⟨F, hF⟩).symm
  have h0 : IsZero (cohomologyOverField k f F n) :=
    isZero_cohomologyOverField_of_topologicalKrullDim_le k f F (d := 1) hdim hn
  have hsub : Subsingleton (cohomologyOverField k f F n) :=
    ModuleCat.isZero_iff_subsingleton.mp h0
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub

end AlgebraicGeometry

namespace Stacks.Duality

/-- **`Rf_*` of a quasi-coherent module in degree `a` lies in degrees `≤ a + 1`, for a curve over
a field.** Let `k` be a field, let `f : X ⟶ Spec(k)` be proper with `X` of topological Krull
dimension at most one, and let `F` be a quasi-coherent `𝒪_X`-module. Then the derived direct
image of `F` placed in degree `a` has no cohomology above degree `a + 1`.

The cohomology sheaf of `Rf_*(F[a])` in degree `m` is the classical higher direct image
`R^{m - a} f_* F` by `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`, and those
vanish for `m - a ≥ 2` by
`AlgebraicGeometry.isZero_rightDerived_pushforward_of_topologicalKrullDim_le`. -/
theorem isLE_derivedPushforward_singleFunctor_obj (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{w} (Spec (CommRingCat.of k)).Modules]
    (F : X.Modules) [F.IsQuasicoherent] (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (a : ℤ) :
    ((derivedPushforward f).obj
      ((DerivedCategory.singleFunctor X.Modules a).obj F)).IsLE (a + 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine IsZero.of_iso ?_ (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso
    (Scheme.Modules.pushforward f) (derivedPushforward f) (derivedPushforwardUnit f)
    (AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X) F a i (i - a).toNat
      (by omega))
  exact AlgebraicGeometry.isZero_rightDerived_pushforward_of_topologicalKrullDim_le k f F hdim
    (by omega)

/-- **`Rf_*` of a quasi-coherent module lies in degrees `≤ 1`, for a curve over a field.** The
case `a = 0` of `Stacks.Duality.isLE_derivedPushforward_singleFunctor_obj`. -/
theorem isLE_one_derivedPushforward_singleFunctor_zero_obj (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{w} (Spec (CommRingCat.of k)).Modules]
    (F : X.Modules) [F.IsQuasicoherent] (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    ((derivedPushforward f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)).IsLE 1 := by
  have := isLE_derivedPushforward_singleFunctor_obj.{w} k f F hdim 0
  rwa [zero_add] at this

end Stacks.Duality

end
