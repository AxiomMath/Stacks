module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.WideLayerClopenDecomposition

/-!
# The class of a cycle in the K-group of a dimension layer

Let `(S, δ)` be a base situation with a dimension function and let `X` be a scheme locally of
finite type over `S`. Writing `Coh_{≤k}(X)` for the coherent `𝒪_X`-modules whose support has
delta-dimension at most `k`, the cycle class homomorphism

`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ Z_k(X)`, `F ↦ [F]_k`

of `Stacks.Chow.dimensionLayerCycleHom` is an isomorphism, with inverse
`∑ n_Z[Z] ↦ [⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]`.

This module gives the inverse map on a quasi-compact `X`, `∑ n_Z[Z] ↦ ∑ n_Z[𝒪_Z]`, where `𝒪_Z`
is the structure sheaf of the integral closed subscheme `Z` attached to a point of relative
dimension `k`, and shows that it is a section of the cycle class homomorphism.

## Main definitions

* `Stacks.Chow.integralComponentModule`: the structure sheaf `𝒪_Z` of the integral closed
  subscheme `Z` attached to a point, as an `𝒪_X`-module.
* `Stacks.Chow.integralComponentDimLE`: the same module read as an object of `Coh_{≤k}(X)`.
* `Stacks.Chow.integralComponentLayerClass`: its class in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`.
* `Stacks.Chow.dimensionLayerClassHom`: the homomorphism `Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`
  for `X` quasi-compact.

## Main results

* `Stacks.Chow.dimensionLayerCycleHom_integralComponentLayerClass`: the cycle class homomorphism
  sends the class of `𝒪_Z` to the prime cycle `[Z]`.
* `Stacks.Chow.dimensionLayerCycleHom_finsum_integralComponentLayerClass`: the cycle of
  `∑ n_Z[𝒪_Z]` is `∑ n_Z[Z]`, for a `k`-cycle of finite support.
* `Stacks.Chow.mem_range_dimensionLayerCycleHom_of_finite_support`: every `k`-cycle with finite
  support is a cycle class.
* `Stacks.Chow.dimensionLayerCycleHom_comp_dimensionLayerClassHom`: for `X` quasi-compact the two
  homomorphisms compose to the identity of `Z_k(X)`.
* `Stacks.Chow.surjective_dimensionLayerCycleHom`: for `X` quasi-compact the cycle class
  homomorphism is surjective.

## References

* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### The structure sheaf of the integral closed subscheme attached to a point -/

/-- The structure sheaf `𝒪_Z` of the integral closed subscheme `Z` attached to a point `x` of `X`
— the reduced induced structure on the closure of `x` — as an `𝒪_X`-module, that is, the direct
image along the closed immersion `Z ⟶ X` of the structure sheaf of `Z`. -/
def integralComponentModule (x : X) : X.Modules :=
  (Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
    (Ample.unitModule (integralComponentAt x).subscheme)

/-- On a locally Noetherian scheme, `𝒪_Z` is coherent. -/
instance isCoherent_integralComponentModule [IsLocallyNoetherian X] (x : X) :
    (integralComponentModule x).IsCoherent :=
  isCoherent_pushforwardStructureSheaf _

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-- For a point of relative dimension `k` the module `𝒪_Z` has support of delta-dimension `k`, so
it is an object of `Coh_{≤k}(X)`. -/
def integralComponentDimLE (x : X) (hx : relativeDimension C.dimensionFunction f x = k) :
    CoherentModulesDimLE C f k :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  ⟨⟨integralComponentModule x,
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
        (isCoherent_integralComponentModule x)⟩,
    schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C f _
      (le_of_eq (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f x hx))⟩

/-- For the integral closed subscheme `Z` attached to a point of relative dimension `k`, the cycle
of `𝒪_Z` is the cycle of `Z`. -/
theorem dimensionLayerCycle_integralComponentDimLE (x : X)
    (hx : relativeDimension C.dimensionFunction f x = k) :
    dimensionLayerCycle C f k (integralComponentDimLE C f k x hx) =
      cycleAssociatedToClosedSubscheme C f (integralComponentAt x).subschemeι k :=
  (cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C f
    (integralComponentAt x).subschemeι k
    (le_of_eq (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f x hx))).symm

/-! ### The class of a prime cycle -/

open Classical in
/-- The class of `𝒪_Z` in the Grothendieck group of the dimension layer
`Coh_{≤k}(X)/Coh_{≤k-1}(X)`, for `Z` the integral closed subscheme attached to a point of relative
dimension `k`, and zero at a point of any other relative dimension. -/
def integralComponentLayerClass (x : X) :
    GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) :=
  if hx : relativeDimension C.dimensionFunction f x = k then
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
      (integralComponentDimLE C f k x hx))
  else 0

/-- At a point whose relative dimension is not `k` the class of the attached integral closed
subscheme is zero. -/
theorem integralComponentLayerClass_eq_zero {x : X}
    (hx : relativeDimension C.dimensionFunction f x ≠ k) :
    integralComponentLayerClass C f k x = 0 := by
  classical
  rw [integralComponentLayerClass, dite_eq_right hx]

/-- The cycle class homomorphism sends the class of `𝒪_Z` to the cycle `[Z]` of the integral closed
subscheme `Z` attached to a point of relative dimension `k`. -/
@[stacks 02S9 "the map `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})` on a prime cycle: the class \
  of `𝒪_Z` has cycle `[Z]`"]
theorem dimensionLayerCycleHom_integralComponentLayerClass (x : X)
    (hx : relativeDimension C.dimensionFunction f x = k) :
    dimensionLayerCycleHom C f k (integralComponentLayerClass C f k x) =
      cycleAssociatedToClosedSubscheme C f (integralComponentAt x).subschemeι k := by
  classical
  rw [integralComponentLayerClass, dite_eq_left hx, dimensionLayerCycleHom_of,
    dimensionLayerCycle_integralComponentDimLE]

/-- The cycle of `𝒪_Z` has coefficient one at the generic point of `Z`. -/
theorem dimensionLayerCycleHom_integralComponentLayerClass_apply_self (x : X)
    (hx : relativeDimension C.dimensionFunction f x = k) :
    (dimensionLayerCycleHom C f k (integralComponentLayerClass C f k x)).1 x = 1 := by
  rw [dimensionLayerCycleHom_integralComponentLayerClass C f k x hx]
  exact cycleAssociatedToClosedSubscheme_integralComponentAt_self C f x
    (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f x hx)

/-- The cycle of `𝒪_Z` vanishes at every point other than the generic point of `Z`. -/
theorem dimensionLayerCycleHom_integralComponentLayerClass_apply_of_ne (x : X) {y : X}
    (hy : y ≠ x) :
    (dimensionLayerCycleHom C f k (integralComponentLayerClass C f k x)).1 y = 0 := by
  by_cases hx : relativeDimension C.dimensionFunction f x = k
  · rw [dimensionLayerCycleHom_integralComponentLayerClass C f k x hx]
    exact cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C f k x hy
  · rw [integralComponentLayerClass_eq_zero C f k hx, map_zero]
    rfl

/-! ### The class of a cycle -/

/-- Only the points carrying a nonzero coefficient of a cycle contribute to the weighted family of
classes of integral closed subschemes. -/
private theorem support_zsmul_integralComponentLayerClass_subset (α : CycleGroup C f k) :
    (Function.support fun x : X => α.1 x • integralComponentLayerClass C f k x) ⊆
      Function.support (α.1 : X → ℤ) :=
  Function.support_smul_subset_left _ _

/-- The cycle of the class `∑ n_Z[𝒪_Z]` attached to a `k`-cycle `∑ n_Z[Z]` of finite support is
`∑ n_Z[Z]` again. -/
@[stacks 02S9 "the inverse identity `[∑ n_Z 𝒪_Z]_k = ∑ n_Z[Z]`, for a `k`-cycle of finite support"]
theorem dimensionLayerCycleHom_finsum_integralComponentLayerClass (α : CycleGroup C f k)
    (hα : (Function.support (α.1 : X → ℤ)).Finite) :
    dimensionLayerCycleHom C f k
        (∑ᶠ x : X, α.1 x • integralComponentLayerClass C f k x) = α := by
  classical
  have hsub : (Function.support fun x : X => α.1 x • integralComponentLayerClass C f k x) ⊆
      (hα.toFinset : Set X) := by
    rw [Set.Finite.coe_toFinset]
    exact support_zsmul_integralComponentLayerClass_subset C f k α
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  show (cycleCoeffHom C f k y).comp (dimensionLayerCycleHom C f k)
      (∑ᶠ x : X, α.1 x • integralComponentLayerClass C f k x) = α.1 y
  have hzero : ∀ x : X, x ≠ y → (cycleCoeffHom C f k y).comp (dimensionLayerCycleHom C f k)
      (α.1 x • integralComponentLayerClass C f k x) = 0 := fun x hx ↦ by
    rw [map_zsmul]
    exact (congrArg (α.1 x • ·)
      (dimensionLayerCycleHom_integralComponentLayerClass_apply_of_ne C f k x hx.symm)).trans
      (smul_zero _)
  rw [finsum_eq_sum_of_support_subset _ hsub, map_sum]
  by_cases hy : α.1 y = 0
  · rw [hy]
    exact Finset.sum_eq_zero fun x hx ↦ hzero x fun h ↦ (hα.mem_toFinset.1 hx) (h ▸ hy)
  · rw [Finset.sum_eq_single_of_mem y (hα.mem_toFinset.2 hy) fun x _ hxy ↦ hzero x hxy, map_zsmul]
    exact (congrArg (α.1 y • ·)
      (dimensionLayerCycleHom_integralComponentLayerClass_apply_self C f k y
        ((mem_cyclesOfDimension_iff_forall_point C f k α.1).1 α.2 y hy))).trans (mul_one _)

/-- Every `k`-cycle with finite support is the cycle of a class in the Grothendieck group of the
dimension layer, namely of the weighted sum of the classes of the structure sheaves of the integral
closed subschemes it is supported on. -/
@[stacks 02S9 "every `k`-cycle of finite support is in the image of \
  `K₀(Coh_{≤k}/Coh_{≤k-1}) → Z_k(X)`"]
theorem mem_range_dimensionLayerCycleHom_of_finite_support (α : CycleGroup C f k)
    (hα : (Function.support (α.1 : X → ℤ)).Finite) :
    α ∈ (dimensionLayerCycleHom C f k).range :=
  ⟨_, dimensionLayerCycleHom_finsum_integralComponentLayerClass C f k α hα⟩

/-! ### The quasi-compact case -/

section CompactSpace

variable [CompactSpace X]

/-- On a quasi-compact scheme a cycle has finite support. -/
theorem finite_support_cycleGroup (α : CycleGroup C f k) :
    (Function.support (α.1 : X → ℤ)).Finite := by
  simpa using (Function.locallyFinsupp.locallyFiniteSupport α.1).finite_inter_support_of_isCompact
    (isCompact_univ (X := (X : Type u)))

/-- On a quasi-compact scheme the weighted family of classes of integral closed subschemes attached
to a cycle has finite support. -/
private theorem finite_support_zsmul_integralComponentLayerClass (α : CycleGroup C f k) :
    (Function.support fun x : X => α.1 x • integralComponentLayerClass C f k x).Finite :=
  (finite_support_cycleGroup C f k α).subset
    (support_zsmul_integralComponentLayerClass_subset C f k α)

/-- The map `Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` for `X` quasi-compact: a `k`-cycle `∑ n_Z[Z]`
is sent to `∑ n_Z[𝒪_Z]`, the coefficients weighting the classes of the structure sheaves of the
integral closed subschemes occurring in the cycle. -/
@[stacks 02S9 "the map `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})`, `∑ n_Z[Z] ↦ ∑ n_Z[𝒪_Z]`, \
  for `X` quasi-compact"]
def dimensionLayerClassHom :
    CycleGroup C f k →+ GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) :=
  AddMonoidHom.mk' (fun α ↦ ∑ᶠ x : X, α.1 x • integralComponentLayerClass C f k x) fun α β ↦ by
    have h : ∀ x : X, (α + β).1 x • integralComponentLayerClass C f k x =
        α.1 x • integralComponentLayerClass C f k x +
          β.1 x • integralComponentLayerClass C f k x := fun x ↦ add_smul (α.1 x) (β.1 x) _
    rw [finsum_congr h, finsum_add_distrib
      (finite_support_zsmul_integralComponentLayerClass C f k α)
      (finite_support_zsmul_integralComponentLayerClass C f k β)]

/-- The class of a cycle is the weighted locally finite sum of the classes of the structure sheaves
of the integral closed subschemes occurring in it. -/
theorem dimensionLayerClassHom_apply (α : CycleGroup C f k) :
    dimensionLayerClassHom C f k α =
      ∑ᶠ x : X, α.1 x • integralComponentLayerClass C f k x :=
  rfl

/-- For `X` quasi-compact, the composite
`Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → Z_k(X)` is the identity. -/
@[stacks 02S9 "the inverse identity `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1}) → Z_k(X) = id`, \
  for `X` quasi-compact"]
theorem dimensionLayerCycleHom_comp_dimensionLayerClassHom :
    (dimensionLayerCycleHom C f k).comp (dimensionLayerClassHom C f k) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun α ↦
    dimensionLayerCycleHom_finsum_integralComponentLayerClass C f k α
      (finite_support_cycleGroup C f k α)

/-- For `X` quasi-compact, every `k`-cycle is the cycle of a class in the Grothendieck group of the
dimension layer. -/
@[stacks 02S9 "surjectivity of `K₀(Coh_{≤k}/Coh_{≤k-1}) → Z_k(X)`, for `X` quasi-compact"]
theorem surjective_dimensionLayerCycleHom :
    Function.Surjective (dimensionLayerCycleHom C f k) := fun α ↦
  ⟨dimensionLayerClassHom C f k α,
    dimensionLayerCycleHom_finsum_integralComponentLayerClass C f k α
      (finite_support_cycleGroup C f k α)⟩

end CompactSpace

end Stacks.Chow

end
