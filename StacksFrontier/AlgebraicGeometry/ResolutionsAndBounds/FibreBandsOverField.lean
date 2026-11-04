module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreTensorStalkInstance
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.RegularExtVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SmoothBandSplittingUnconditional
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0FZ9] over a field

Let `k` be a field, let `X` and `Y` be schemes of finite type over `k` and let
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` be a system of perfect objects of `D(𝒪_{X ×_k Y})` and `m ≥ 0` an integer
such that `H^q(Kₙ)` vanishes for `q > m` and, for every coherent `𝒪_X`-module `𝓕` with
zero-dimensional support, the integral transform `R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 Kₙ)` has its cohomology
concentrated in `[-m, m] ∪ [-m-n, m-n]`, the transition maps being isomorphisms on it throughout
`[-m, m]` once `n > 2m`. [Stacks, Tag 0FZ9] asserts:

1. the cohomology of `Kₙ` is concentrated in `[-m, m] ∪ [-m-n, m-n]`;
2. for `n > 2m` the transition maps are isomorphisms on the cohomology of the kernels throughout
   `[-m, m]`;
3. if `X` and `Y` are smooth over `k`, then for all large `n` the kernel `Kₙ` is `K ⊕ Cₙ` with
   `K` concentrated in `[-m, m]` and `Cₙ` in `[-m-n, m-n]`, compatibly with the transition maps.

The general forms of these assertions in
`StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/PerfectFibreBands.lean`,
`StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/FibreStableTransitions.lean` and
`StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/SmoothBandSplittingUnconditional.lean` take
the bundle `AlgebraicGeometry.FibreTensorComparisons f g` of derived-tensor comparisons as an
argument. This file supplies it as `AlgebraicGeometry.fibreTensorComparisonsOfPullback`, whose
only non-formal field is the derived form of [Stacks, Tag 01CB], so that the statements here are
at the hypotheses of the source.

## Main results

* `AlgebraicGeometry.isZero_homology_of_notInBands_of_finiteTypeOverField`: part (1).
* `AlgebraicGeometry.isIso_homologyMap_of_fibreStable_of_finiteTypeOverField`: part (2).
* `AlgebraicGeometry.exists_stable_biprod_of_smooth_of_homVanishing`: part (3) from the
  `Hom`-vanishing of [Stacks, Tag 0FZ3] part (2), with no non-emptiness hypothesis.
* `AlgebraicGeometry.exists_stable_biprod_of_smooth_of_finiteTypeOverField`: part (3), with
  [Stacks, Tag 0FZ3] part (2) supplied by `AlgebraicGeometry.separatedCohomologyHomVanishing`.

## Implementation notes

*The standing hypotheses.* Over a field the base `Spec k` is affine and Jacobson, and a scheme
locally of finite type over it is locally Noetherian ([Stacks, Tag 01T6]), which is what the
general forms need of `X` and of `X ×_k Y`. Parts (1) and (2) need only local finiteness of type,
not quasi-compactness, and part (1) does not use the stability of the transition maps, so those
hypotheses are not taken.

*The empty product.* The general splitting needs a natural number `d` with
`topologicalKrullDim (X ×_k Y) = d`, which fails on the empty product, whose dimension is `⊥`.
There every object of `D(𝒪_{X ×_k Y})` is zero, every cohomology sheaf being a module on a
scheme with no points, and the splitting holds trivially.

## References

* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3)
* [Stacks Project, Tag 0FZ4](https://stacks.math.columbia.edu/tag/0FZ4)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

/-- Let `X` and `Y` be locally of finite type over a field `k` and let `K₀, K₁, …` be perfect
objects of `D(𝒪_{X ×_k Y})` with cohomology vanishing above `m`. If for every coherent
`𝒪_X`-module `𝓕` with zero-dimensional support the cohomology of `R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 Kₙ)` is
concentrated in `[-m, m] ∪ [-m-n, m-n]`, then so is the cohomology of `Kₙ`. -/
@[stacks 0FZ9 "part (1)"]
public theorem isZero_homology_of_notInBands_of_finiteTypeOverField
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
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
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  isZero_homology_system_of_notInBands f g (fibreTensorComparisonsOfPullback f g) K m hperf
    hupper hfibreBand n i hi

/-- In the situation of `isZero_homology_of_notInBands_of_finiteTypeOverField`, if moreover
the transition maps `tₙ : Kₙ ⟶ Kₙ₊₁` are isomorphisms on the cohomology of the integral
transforms of the coherent modules with zero-dimensional support throughout `[-m, m]` once
`n > 2m`, then for `n > 2m` the map `tₙ` is an isomorphism on the cohomology sheaves of the
kernels throughout `[-m, m]`. -/
@[stacks 0FZ9 "part (2)"]
public theorem isIso_homologyMap_of_fibreStable_of_finiteTypeOverField
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
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
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  isIso_homologyMap_system_of_fibreStable f g (fibreTensorComparisonsOfPullback f g) K t m hperf
    hupper hfibreBand hfibreStable n i hn hi₁ hi₂

/-- **Tag 0FZ9 part (3) from the `Hom`-vanishing of Tag 0FZ3 part (2).** Let `X` and `Y` be smooth
and of finite type over a field `k`, and let `K₀ ⟶ K₁ ⟶ ⋯` satisfy the hypotheses of
[Stacks, Tag 0FZ9]. Then for all large `n` the kernel `Kₙ` is the direct sum of a perfect object
`A` concentrated in `[-m, m]` and independent of `n` and a perfect object `Cₙ` concentrated in
`[-m-n, m-n]`, compatibly with the transition maps.

The input `hvan` is the statement of [Stacks, Tag 0FZ3] part (2) for every Noetherian scheme.
On a nonempty product this is `AlgebraicGeometry.exists_stable_biprod_of_smooth_of_fibreTransforms`
with the comparisons `AlgebraicGeometry.fibreTensorComparisonsOfPullback`; on the empty product
every object of `D(𝒪_{X ×_k Y})` is zero. -/
public theorem exists_stable_biprod_of_smooth_of_homVanishing
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    [Smooth f] [Smooth g]
    (hvan : ∀ (W : Scheme.{u}) [IsNoetherian W] (d : ℕ), SeparatedCohomologyHomVanishing W d)
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
            t n ≫ (e (n + 1) (by omega)).hom = (e n hn).hom ≫ biprod.map a.hom c := by
  have : IsNoetherian (pullback f g) := isNoetherian_pullback_of_smooth k f g
  by_cases hne : Nonempty ↥(pullback f g)
  · exact exists_stable_biprod_of_smooth_of_fibreTransforms k f g hne (hvan _)
      (fibreTensorComparisonsOfPullback f g) K t m hperf hupper hfibreBand hfibreStable
  -- On the empty product every object of the derived category is zero.
  have hz : ∀ E : DerivedCategory (pullback f g).Modules, IsZero E := by
    intro E
    have h : ∀ i : ℤ,
        IsZero ((DerivedCategory.homologyFunctor (pullback f g).Modules i).obj E) :=
      fun i => isZero_of_forall_isZero_stalk _ fun x => (hne ⟨x⟩).elim
    have : E.IsLE 0 := (DerivedCategory.isLE_iff E 0).2 fun i _ => h i
    have : E.IsGE 1 := (DerivedCategory.isGE_iff E 1).2 fun i _ => h i
    exact DerivedCategory.TStructure.t.isZero E 0 1
  refine ⟨0, K 0, K, hperf 0, fun n _ => hperf n,
    fun i _ => Functor.map_isZero _ (hz _), fun n _ i _ => Functor.map_isZero _ (hz _),
    fun n _ => (hz _).iso (hz _), fun n _ => ⟨Iso.refl _, t n, (hz _).eq_of_src _ _⟩⟩

/-- Let `X` and `Y` be smooth and of finite type over a field `k`, and let `K₀ ⟶ K₁ ⟶ ⋯` be a
system of perfect objects of `D(𝒪_{X ×_k Y})` with cohomology vanishing above `m` such that, for
every coherent `𝒪_X`-module `𝓕` with zero-dimensional support, the cohomology of
`R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 Kₙ)` is concentrated in `[-m, m] ∪ [-m-n, m-n]` and the transition maps
are isomorphisms on it throughout `[-m, m]` once `n > 2m`. Then for all large `n` the kernel `Kₙ`
is the direct sum of a perfect object `A` concentrated in `[-m, m]` and independent of `n` and a
perfect object `Cₙ` concentrated in `[-m-n, m-n]`, and each transition map is the direct sum of an
automorphism of `A` and a map `Cₙ ⟶ Cₙ₊₁`.

This is `AlgebraicGeometry.exists_stable_biprod_of_smooth_of_homVanishing` with
[Stacks, Tag 0FZ3] part (2) supplied by `AlgebraicGeometry.separatedCohomologyHomVanishing`. -/
@[stacks 0FZ9 "part (3)"]
public theorem exists_stable_biprod_of_smooth_of_finiteTypeOverField
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    [Smooth f] [Smooth g]
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
  exists_stable_biprod_of_smooth_of_homVanishing k f g
    (fun W _ d => separatedCohomologyHomVanishing W d) K t m hperf hupper hfibreBand hfibreStable

end AlgebraicGeometry

end
