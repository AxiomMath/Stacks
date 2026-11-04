module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.SingleKernel
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.BoxTransform
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExtVanishingRegular
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreTensorStalkInstance
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SmoothBandSplittingUnconditional

/-!
# The splitting of [Stacks, Tag 0FZ9] with no carried hypothesis

Let `X` and `Y` be quasi-compact schemes, smooth and locally of finite type over a field `k`, and
let `K₀ ⟶ K₁ ⟶ ⋯` be a system of perfect objects of `D(𝒪_{X ×_k Y})` with cohomology vanishing
above `m`, such that for every coherent `𝒪_X`-module `𝓕` with zero-dimensional support the
cohomology of `R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 Kₙ)` is concentrated in `[-m, m] ∪ [-m-n, m-n]` and, for
`n > 2m`, the transition maps are isomorphisms on it throughout `[-m, m]`. Then for all large `n`
the object `Kₙ` is the direct sum of a perfect `A` concentrated in `[-m, m]`, independent of `n`,
and a perfect `Cₙ` concentrated in `[-m-n, m-n]`, compatibly with the transition maps.

This is assertion (3) of [Stacks, Tag 0FZ9] with every hypothesis that
`AlgebraicGeometry.exists_stable_biprod_of_smooth_of_fibreTransforms` carries beyond the source
discharged: the derived-tensor comparisons are
`AlgebraicGeometry.fibreTensorComparisonsOfPullback`, the `Hom`-vanishing of [Stacks, Tag 0FZ3]
part (2) is `AlgebraicGeometry.forall_separatedCohomologyHomVanishing`, and the non-emptiness of
the product is removed by treating the empty product directly, every object of `D(𝒪_∅)` being zero.

The second result is the form in which the stability hypothesis of the tag is checked in
[Stacks, Section 0G07]: if each transition map `tₙ` sits in a distinguished triangle
`Kₙ ⟶ Kₙ₊₁ ⟶ Cₙ ⟶ Kₙ[1]` whose third vertex has transforms vanishing throughout `[-m-1, m]` once
`n > 2m`, then `tₙ` is an isomorphism on the cohomology of the transforms throughout `[-m, m]`.

## Main results

* `AlgebraicGeometry.exists_stable_biprod_of_smooth_of_fibreBands`: [Stacks, Tag 0FZ9] part (3)
  on the source's hypotheses.
* `AlgebraicGeometry.isIso_homologyMap_fibreTransformFunctor_map_of_distTriang`: the stability of
  the transition maps on the transforms from the vanishing of the transforms of their cones.
* `AlgebraicGeometry.fibreTransformFunctorIso`: for a flat first projection, the transform
  `R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 -)` of the tag is the integral transform
  `R pr_{2,*}(L pr_1^*(𝓕[0]) ⊗^𝐋 -)` (`AlgebraicGeometry.kernelIntegralTransform`), i.e. the
  Fourier-Mukai functor of the kernel evaluated at `𝓕[0]`.

## References

* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3)
* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Objects over the empty scheme -/

/-- **Every object of the derived category of modules on the empty scheme is zero**: its
cohomology sheaves are modules on the empty space, and these are zero. -/
theorem isZero_of_isEmpty {W : Scheme.{u}} [IsEmpty W] (K : DerivedCategory W.Modules) :
    IsZero K := by
  have hM (M : W.Modules) : IsZero M := by
    refine (IsZero.iff_id_eq_zero _).2 (Scheme.Modules.hom_ext _ _ fun U => ?_)
    obtain rfl : U = ⊥ := by
      ext x
      exact isEmptyElim x
    have : Subsingleton Γ(M, ⊥) := Module.subsingleton Γ(W, ⊥) _
    ext x
    exact Subsingleton.elim _ _
  have : K.IsLE 0 := (DerivedCategory.isLE_iff K 0).2 fun i _ => hM _
  have : K.IsGE 1 := (DerivedCategory.isGE_iff K 1).2 fun i _ => hM _
  exact DerivedCategory.TStructure.t.isZero K 0 1

/-! ### Stability of the transition maps from their cones -/

section Cones

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

attribute [local instance] AlgebraicGeometry.commShift_pushforward
  AlgebraicGeometry.isTriangulated_pushforward AlgebraicGeometry.commShift_fibreTensor
  AlgebraicGeometry.isTriangulated_fibreTensor

/-- **The stability hypothesis of [Stacks, Tag 0FZ9] from the cones of the transition maps.**
If each `tₙ : Kₙ ⟶ Kₙ₊₁` is the first morphism of a distinguished triangle
`Kₙ ⟶ Kₙ₊₁ ⟶ Cₙ ⟶ Kₙ[1]` and, for every coherent `𝒪_X`-module with zero-dimensional support
and every `n > 2m`, the transform of `Cₙ` vanishes in the degrees `[-m-1, m]`, then for such `𝓕`
and `n` the map `tₙ` is an isomorphism on the cohomology of the transforms throughout `[-m, m]`;
this is the hypothesis `hfibreStable` of
`AlgebraicGeometry.exists_stable_biprod_of_smooth_of_fibreBands`. -/
theorem isIso_homologyMap_fibreTransformFunctor_map_of_distTriang
    (K C : ℕ → DerivedCategory (Limits.pullback f g).Modules) (t : ∀ n, K n ⟶ K (n + 1))
    (u : ∀ n, K (n + 1) ⟶ C n) (w : ∀ n, C n ⟶ (K n)⟦(1 : ℤ)⟧)
    (hT : ∀ n, Triangle.mk (t n) (u n) (w n) ∈ distTriang _) (m : ℕ)
    (hC : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ (n : ℕ) (j : ℤ), 2 * m < n →
      -(m : ℤ) - 1 ≤ j → j ≤ (m : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor Y.Modules j).obj (fibreTransform f g (C n) F))) :
    ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ (n : ℕ) (j : ℤ), 2 * m < n →
      -(m : ℤ) ≤ j → j ≤ (m : ℤ) →
      IsIso ((DerivedCategory.homologyFunctor Y.Modules j).map
        ((fibreTransformFunctor f g F).map (t n))) := by
  intro F hF hdim n j hn hj₁ hj₂
  exact isIso_homologyMap_mor₁_of_isZero _
    ((fibreTensorFunctor f g F ⋙ fourierMukaiPushforward f g).map_distinguished _ (hT n))
    (j - 1) j (by omega)
    (hC F hF hdim n (j - 1) hn (by omega) (by omega)) (hC F hF hdim n j hn (by omega) hj₂)

end Cones

/-! ### The transform of the tag as an integral transform -/

section IntegralTransform

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **For a flat first projection, `R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 -)` is the integral transform of
`𝓕[0]`**: `L pr_1^*(𝓕[0]) = (pr_1^*𝓕)[0]`, naturally in the kernel. So the transforms
constrained by [Stacks, Tag 0FZ9] are the values `Φ_K(𝓕[0])` of the Fourier-Mukai functors. -/
def fibreTransformFunctorIso (hflat : AlgebraicGeometry.IsFlat (fourierMukaiFst f g))
    (F : X.Modules) :
    fibreTransformFunctor f g F ≅
      kernelIntegralTransform f g ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
  Functor.isoWhiskerRight
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (Limits.pullback f g).toRingedSpace.sheaf).mapIso
        ((fourierMukaiPullbackSingleIso f g hflat).app F).symm) (fourierMukaiPushforward f g)

end IntegralTransform

/-! ### The splitting on a product of smooth schemes -/

/-- **Stacks Project, Tag 0FZ9, part (3), on the source's hypotheses.** Let `X` and `Y` be
quasi-compact schemes, smooth and locally of finite type over a field `k`, and let
`K₀ ⟶ K₁ ⟶ ⋯` be a system of perfect objects of `D(𝒪_{X ×_k Y})` with cohomology vanishing above
`m`. Assume that for every coherent `𝒪_X`-module with zero-dimensional support the cohomology of
the integral transform by `Kₙ` is concentrated in `[-m, m] ∪ [-m-n, m-n]` and that, for `n > 2m`,
the transition maps are isomorphisms on the cohomology of those transforms throughout `[-m, m]`.
Then for all large `n` the object `Kₙ` is the direct sum of a perfect object `A` concentrated in
`[-m, m]` and independent of `n` and a perfect object `Cₙ` concentrated in `[-m-n, m-n]`,
compatibly with the transition maps.

This is `AlgebraicGeometry.exists_stable_biprod_of_smooth_of_fibreTransforms` with its three extra
hypotheses discharged: the comparisons by `AlgebraicGeometry.fibreTensorComparisonsOfPullback`,
[Stacks, Tag 0FZ3] part (2) by `AlgebraicGeometry.forall_separatedCohomologyHomVanishing`, and the
non-emptiness of `X ×_k Y` by treating the empty product apart, where every object is zero, so that
`A = K₀` and `Cₙ = Kₙ` do. -/
@[stacks 0FZ9 "part (3), on the source's hypotheses: parts (1) and (2), the derived-tensor \
comparisons, Stacks 0FZ3(2) and the non-emptiness of the product are all discharged"]
theorem exists_stable_biprod_of_smooth_of_fibreBands (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    [Smooth f] [Smooth g]
    (K : ℕ → DerivedCategory (pullback f g).Modules) (t : ∀ n, K n ⟶ K (n + 1)) (m : ℕ)
    (hperf : ∀ n, RingedSpace.IsPerfect.{u, u + 1}
      (X := (pullback f g).toRingedSpace) (K n))
    (hupper : ∀ (n : ℕ) (j : ℤ), (m : ℤ) < j →
      IsZero ((DerivedCategory.homologyFunctor (pullback f g).Modules j).obj (K n)))
    (hfibreBand : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ (n : ℕ) (j : ℤ), ¬ InBands m n j →
      IsZero ((DerivedCategory.homologyFunctor Y.Modules j).obj (fibreTransform f g (K n) F)))
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
        IsZero ((DerivedCategory.homologyFunctor (pullback f g).Modules i).obj A)) ∧
      (∀ n, N ≤ n → ∀ i : ℤ, (i < -(m : ℤ) - (n : ℤ) ∨ (m : ℤ) - (n : ℤ) < i) →
        IsZero ((DerivedCategory.homologyFunctor (pullback f g).Modules i).obj (C n))) ∧
      ∃ e : (∀ n : ℕ, N ≤ n → (K n ≅ A ⊞ C n)),
        ∀ (n : ℕ) (hn : N ≤ n),
          ∃ (a : A ≅ A) (c : C n ⟶ C (n + 1)),
            t n ≫ (e (n + 1) (by omega)).hom = (e n hn).hom ≫ biprod.map a.hom c := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : CompactSpace ↥(pullback f g) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f g)
  have : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ f)
  have : IsNoetherian (pullback f g) := ⟨⟩
  rcases isEmpty_or_nonempty ↥(pullback f g) with hW | hW
  · have hz : ∀ n, IsZero (K n) := fun n => isZero_of_isEmpty (K n)
    refine ⟨0, K 0, K, hperf 0, fun n _ => hperf n,
      fun i _ => Functor.map_isZero _ (hz 0), fun n _ i _ => Functor.map_isZero _ (hz n),
      fun n _ => isoZeroBiprod (hz 0),
      fun n _ => ⟨Iso.refl _, t n, biprod.hom_ext _ _ ((hz 0).eq_of_tgt _ _) (by simp)⟩⟩
  · exact exists_stable_biprod_of_smooth_of_fibreTransforms k f g hW
      (fun d => forall_separatedCohomologyHomVanishing _ d) (fibreTensorComparisonsOfPullback f g)
      K t m hperf hupper hfibreBand hfibreStable

end AlgebraicGeometry

end
