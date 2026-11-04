module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreStableTransitions
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.PerfectFibreBands
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SmoothBandSplitting

/-!
# The splitting of [Stacks, Tag 0FZ9] read off the fibrewise hypotheses

Let `X` and `Y` be quasi-compact schemes, smooth and locally of finite type over a field `k`, and
let `K₀ ⟶ K₁ ⟶ ⋯` be a system of perfect objects of `D(𝒪_{X ×_k Y})` whose cohomology vanishes
above a degree `m`. Assume, for every coherent `𝒪_X`-module `𝓕` with zero-dimensional support,
that the cohomology of the integral transform `R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 Kₙ)` is concentrated in
`[-m, m] ∪ [-m-n, m-n]` and that the transition maps are isomorphisms on the cohomology of these
transforms throughout `[-m, m]` once `n > 2m`. Then for all large `n` the object `Kₙ` is the
direct sum of a perfect object `A` concentrated in `[-m, m]` and independent of `n` and a perfect
object `Cₙ` concentrated in `[-m-n, m-n]`, compatibly with the transition maps.

This is assertion (3) of [Stacks, Tag 0FZ9] with its two band hypotheses on the kernels replaced
by the fibrewise hypotheses of the tag.

## Main results

* `AlgebraicGeometry.isZero_homology_system_of_notInBands`: assertion (1) of [Stacks, Tag 0FZ9]
  for a system of kernels, at every index at once.
* `AlgebraicGeometry.isIso_homologyMap_system_of_fibreStable`: assertion (2) of
  [Stacks, Tag 0FZ9] for a system of kernels, at every index at once.
* `AlgebraicGeometry.exists_stable_biprod_of_smooth_of_fibreTransforms`: assertion (3) of
  [Stacks, Tag 0FZ9] with assertions (1) and (2) discharged, so that only the fibrewise
  hypotheses of the tag remain.

## Implementation notes

*The model of the derived categories.* Everything is read at
`CategoryTheory.HasDerivedCategory.standard`, the model at which `AlgebraicGeometry.fourierMukai`
is defined.

*The index alignment.* Assertion (1) is applied to the kernel `Kₙ` with the band index `n`, and
assertion (2) to the transition map `tₙ : Kₙ ⟶ Kₙ₊₁` with the band index `n` for its source and
`n + 1` for its target, which is why the fibrewise band hypothesis is quantified over the index
of the system and is used twice, at `n` and at `n + 1`.

*The shape of the fibrewise hypotheses.* They are stated through
`AlgebraicGeometry.fibreTransform` and `AlgebraicGeometry.fibreTransformFunctor`, the spellings
in which assertions (1) and (2) consume them.

*The two hypotheses carried from assertion (3).* `hvan` is the `Hom`-vanishing of
[Stacks, Tag 0FZ3] part (2), already a hypothesis of the form of [Stacks, Tag 0FZ4] used in the
splitting, and `hne` is the non-emptiness of the product, without which its dimension is `⊥` and
no natural number `d` with `topologicalKrullDim (X ×_k Y) = d` exists.

## References

* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
* [Stacks Project, Tag 0FZ4](https://stacks.math.columbia.edu/tag/0FZ4)
* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The two cohomological assertions for a whole system of kernels -/

section System

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsAffine S] [JacobsonSpace ↥S]
  [LocallyOfFiniteType f] [LocallyOfFiniteType g] [IsLocallyNoetherian X]
  [IsLocallyNoetherian (Limits.pullback f g)]

/-- **[Stacks, Tag 0FZ9] part (1) for a system of kernels.** If each member of a system of
perfect objects of `D(𝒪_{X ×_S Y})` has cohomology vanishing above `m` and, for every coherent
`𝒪_X`-module with zero-dimensional support, the cohomology of the integral transform by `Kₙ` is
concentrated in `[-m, m] ∪ [-m-n, m-n]`, then the cohomology of `Kₙ` itself is concentrated
there. -/
public theorem isZero_homology_system_of_notInBands (cmp : FibreTensorComparisons f g)
    (K : ℕ → DerivedCategory (Limits.pullback f g).Modules) (m : ℕ)
    (hperf : ∀ n, RingedSpace.IsPerfect.{u, u + 1}
      (X := (Limits.pullback f g).toRingedSpace) (K n))
    (hupper : ∀ (n : ℕ) (j : ℤ), (m : ℤ) < j →
      IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj (K n)))
    (hfibreBand : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ (n : ℕ) (j : ℤ), ¬ InBands m n j →
      IsZero ((DerivedCategory.homologyFunctor Y.Modules j).obj (fibreTransform f g (K n) F)))
    (n : ℕ) (i : ℤ) (hi : ¬ InBands m n i) :
    IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj (K n)) :=
  isZero_homology_of_notInBands f g cmp (K n) (hperf n) m n (hupper n)
    (fun F hF hdim j hj => hfibreBand F hF hdim n j hj) i hi

/-- **[Stacks, Tag 0FZ9] part (2) for a system of kernels.** In the situation of
`AlgebraicGeometry.isZero_homology_system_of_notInBands`, if the transition maps are
isomorphisms on the cohomology of the integral transforms of the coherent modules with
zero-dimensional support throughout `[-m, m]`, then for `n > 2m` the map `tₙ` is an isomorphism
on the cohomology sheaves of the kernels throughout `[-m, m]`. -/
public theorem isIso_homologyMap_system_of_fibreStable (cmp : FibreTensorComparisons f g)
    (K : ℕ → DerivedCategory (Limits.pullback f g).Modules) (t : ∀ n, K n ⟶ K (n + 1)) (m : ℕ)
    (hperf : ∀ n, RingedSpace.IsPerfect.{u, u + 1}
      (X := (Limits.pullback f g).toRingedSpace) (K n))
    (hupper : ∀ (n : ℕ) (j : ℤ), (m : ℤ) < j →
      IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj (K n)))
    (hfibreBand : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ (n : ℕ) (j : ℤ), ¬ InBands m n j →
      IsZero ((DerivedCategory.homologyFunctor Y.Modules j).obj (fibreTransform f g (K n) F)))
    (hfibreStable : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ (n : ℕ) (j : ℤ), 2 * m < n →
      -(m : ℤ) ≤ j → j ≤ (m : ℤ) →
      IsIso ((DerivedCategory.homologyFunctor Y.Modules j).map
        ((fibreTransformFunctor f g F).map (t n))))
    (n : ℕ) (i : ℤ) (hn : 2 * m < n) (hi₁ : -(m : ℤ) ≤ i) (hi₂ : i ≤ (m : ℤ)) :
    IsIso ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).map (t n)) :=
  isIso_homologyMap_of_fibreStable f g cmp (K n) (K (n + 1)) (t n) (hperf n) (hperf (n + 1)) m n
    (hupper n) (hupper (n + 1))
    (fun F hF hdim j hj => hfibreBand F hF hdim n j hj)
    (fun F hF hdim j hj => hfibreBand F hF hdim (n + 1) j hj)
    (fun F hF hdim j hj₁ hj₂ => hfibreStable F hF hdim n j hn hj₁ hj₂)
    hn i hi₁ hi₂

end System

/-! ### The splitting on a product of smooth schemes -/

/-- Let `X` and `Y` be quasi-compact schemes, smooth and locally of finite type over a field `k`,
with `X ×_k Y` nonempty, and let `K₀ ⟶ K₁ ⟶ ⋯` be a system of perfect objects of
`D(𝒪_{X ×_k Y})` with cohomology vanishing above `m`. Assume that for every coherent `𝒪_X`-module
with zero-dimensional support the cohomology of the integral transform by `Kₙ` is concentrated in
`[-m, m] ∪ [-m-n, m-n]` and that, for `n > 2m`, the transition maps are isomorphisms on the
cohomology of those transforms throughout `[-m, m]`. Then for all large `n` the object `Kₙ` is the
direct sum of a perfect object `A` concentrated in `[-m, m]` and independent of `n` and a perfect
object `Cₙ` concentrated in `[-m-n, m-n]`, compatibly with the transition maps. -/
@[stacks 0FZ9 "part (3) with parts (1) and (2) DISCHARGED from the tag's fibrewise hypotheses, \
carrying only the general derived-tensor comparisons as FibreTensorComparisons together with \
the two hypotheses the source does not have, 0FZ3(2) as hvan (which the library's 0FZ4 itself \
carries) and non-emptiness of the product as hne"]
public theorem exists_stable_biprod_of_smooth_of_fibreTransforms (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    [Smooth f] [Smooth g] [IsNoetherian (pullback f g)] (hne : Nonempty ↥(pullback f g))
    (hvan : ∀ d : ℕ, SeparatedCohomologyHomVanishing (pullback f g) d)
    (cmp : FibreTensorComparisons f g)
    (K : ℕ → DerivedCategory (pullback f g).Modules) (t : ∀ n, K n ⟶ K (n + 1)) (m : ℕ)
    (hperf : ∀ n, RingedSpace.IsPerfect.{u, u + 1}
      (X := (pullback f g).toRingedSpace) (K n))
    (hupper : ∀ (n : ℕ) (j : ℤ), (m : ℤ) < j →
      Limits.IsZero
        ((DerivedCategory.homologyFunctor (pullback f g).Modules j).obj (K n)))
    (hfibreBand : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ (n : ℕ) (j : ℤ), ¬ InBands m n j →
      Limits.IsZero ((DerivedCategory.homologyFunctor Y.Modules j).obj
        (fibreTransform f g (K n) F)))
    (hfibreStable : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ (n : ℕ) (j : ℤ), 2 * m < n →
      -(m : ℤ) ≤ j → j ≤ (m : ℤ) →
      IsIso ((DerivedCategory.homologyFunctor Y.Modules j).map
        ((fibreTransformFunctor f g F).map (t n)))) :
    ∃ (N : ℕ) (A : DerivedCategory (pullback f g).Modules)
      (C : ℕ → DerivedCategory (pullback f g).Modules),
      RingedSpace.IsPerfect.{u, u + 1} (X := (pullback f g).toRingedSpace) A ∧
      (∀ n, N ≤ n →
        RingedSpace.IsPerfect.{u, u + 1} (X := (pullback f g).toRingedSpace) (C n)) ∧
      (∀ i : ℤ, (i < -(m : ℤ) ∨ (m : ℤ) < i) →
        Limits.IsZero ((DerivedCategory.homologyFunctor (pullback f g).Modules i).obj A)) ∧
      (∀ n, N ≤ n → ∀ i : ℤ, (i < -(m : ℤ) - (n : ℤ) ∨ (m : ℤ) - (n : ℤ) < i) →
        Limits.IsZero ((DerivedCategory.homologyFunctor (pullback f g).Modules i).obj (C n))) ∧
      ∃ e : (∀ n : ℕ, N ≤ n → (K n ≅ A ⊞ C n)),
        ∀ (n : ℕ) (hn : N ≤ n),
          ∃ (a : A ≅ A) (c : C n ⟶ C (n + 1)),
            t n ≫ (e (n + 1) (by omega)).hom = (e n hn).hom ≫ biprod.map a.hom c :=
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular
    (isRegular_of_smooth_over_field f)
  exists_stable_biprod_of_smooth k f g hne hvan K t m hperf
    (isZero_homology_system_of_notInBands f g cmp K m hperf hupper hfibreBand)
    (fun n i hn hi₁ hi₂ =>
      isIso_homologyMap_system_of_fibreStable f g cmp K t m hperf hupper hfibreBand
        hfibreStable n i hn hi₁ hi₂)

end AlgebraicGeometry

end
