module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.CokernelAffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.MeromorphicDenominatorFreeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.MeromorphicDenominatorIdealCoherent

/-!
# The two quotients attached to the ideal of denominators

Let `t` be a regular meromorphic section of an invertible module `ℒ` with ideal of denominators
`𝓘`. The two quotients are `𝒬₁ = 𝒪_X / 𝓘` and `𝒬₂ = ℒ / t 𝓘`, the cokernels of the inclusion
`𝓘 ⟶ 𝒪_X` and of multiplication by `t`. Over an affine chart `V` trivializing `ℒ` with chart
ratio `c`, their sections are `𝒪(V) / 𝓘(V)` and `𝒪(V) / c 𝓘(V)`.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicDenominatorQuotient`: `𝒪_X / 𝓘`.
* `AlgebraicGeometry.Space.meromorphicNumeratorQuotient`: `ℒ / t 𝓘`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS X.1 X.2)
  (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
  (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property L)

/-- The first quotient `𝒪_X / 𝓘` of the ideal of denominators. -/
noncomputable abbrev meromorphicDenominatorQuotient : Modules.{u, u} B S hS X.1 X.2 :=
  cokernel (meromorphicDenominatorIdeal B S hS X L t hL).ι

/-- The second quotient `ℒ / t 𝓘` of the ideal of denominators. -/
noncomputable abbrev meromorphicNumeratorQuotient : Modules.{u, u} B S hS X.1 X.2 :=
  cokernel (meromorphicDenominatorMul B S hS X L t hL)

variable (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
  (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)

include hwa hfin in
/-- **The sections of `𝒪_X / 𝓘` over an affine chart** are `𝒪(V) / 𝓘(V)`. -/
noncomputable def meromorphicDenominatorQuotientSectionsEquiv (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    (meromorphicDenominatorQuotient B S hS X L t hL).val.obj (op V) ≃ₗ[chartRing B S hS X.1 X.2 V]
      chartRing B S hS X.1 X.2 V ⧸ meromorphicDenominatorIdealAt B S hS X L t V := by
  let π := ((cokernel.π (meromorphicDenominatorIdeal B S hS X L t hL).ι).val.app (op V)).hom
  have hsurj : Function.Surjective π :=
    surjective_cokernel_π_app_of_mono _
      (isCartesianOnAffineCharts_meromorphicDenominatorIdeal B S hS X L t hL hwa hfin) V hV
  have hex := exact_cokernel_π_app_of_mono (meromorphicDenominatorIdeal B S hS X L t hL).ι V
  have hker : LinearMap.ker π = meromorphicDenominatorIdealAt B S hS X L t V := by
    ext a
    refine (LinearMap.mem_ker (f := π)).trans ((hex a).trans ⟨?_, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩)
    rintro ⟨b, rfl⟩
    exact b.2
  exact (LinearMap.quotKerEquivOfSurjective π hsurj).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)

section FreeChart

variable (V : SmallEtale B S hS X.1)
  (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
  (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
    (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
  (hfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
    Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)

/-- Over a chart trivializing `ℒ` with chart ratio `c`, the ideal `c 𝓘(V)` of the `y = a c` for
the denominators `a` of `t`. -/
noncomputable def meromorphicNumeratorIdealAt : Ideal (chartRing B S hS X.1 X.2 V) where
  carrier := {y | ∃ a, IsMeromorphicDenominator B S hS X L t V a ∧
    chartMeromorphicScalar B S hS X V y =
      chartMeromorphicScalar B S hS X V a * chartRatio B S hS X.1 X.2 L V e hcompat hfree t}
  zero_mem' := ⟨0, isMeromorphicDenominator_zero B S hS X L t V, by simp⟩
  add_mem' := by
    rintro y y' ⟨a, ha, hy⟩ ⟨a', ha', hy'⟩
    exact ⟨a + a', isMeromorphicDenominator_add B S hS X L t ha ha', by
      rw [map_add, map_add, hy, hy', add_mul]⟩
  smul_mem' := by
    rintro r y ⟨a, ha, hy⟩
    exact ⟨r * a, isMeromorphicDenominator_mul B S hS X L t r ha, by
      rw [smul_eq_mul, map_mul, map_mul, hy, mul_assoc]⟩

include hwa hfin in
/-- **The sections of `ℒ / t 𝓘` over an affine chart trivializing `ℒ`** are `𝒪(V) / c 𝓘(V)`. -/
noncomputable def meromorphicNumeratorQuotientSectionsEquiv
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t)
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    (meromorphicNumeratorQuotient B S hS X L t hL).val.obj (op V) ≃ₗ[chartRing B S hS X.1 X.2 V]
      chartRing B S hS X.1 X.2 V ⧸ meromorphicNumeratorIdealAt B S hS X L t V e hcompat hfree := by
  haveI := mono_meromorphicDenominatorMul B S hS X L t hL ht
  let π := ((cokernel.π (meromorphicDenominatorMul B S hS X L t hL)).val.app (op V)).hom
  have hsurj : Function.Surjective π :=
    surjective_cokernel_π_app_of_mono _
      (isCartesianOnAffineCharts_meromorphicDenominatorIdeal B S hS X L t hL hwa hfin) V hV
  have hex := exact_cokernel_π_app_of_mono (meromorphicDenominatorMul B S hS X L t hL) V
  let eL : chartRing B S hS X.1 X.2 V ≃ₗ[chartRing B S hS X.1 X.2 V] L.val.obj (op V) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (e V (𝟙 V))) (hfree V (𝟙 V))
  have hker : Submodule.map eL.toLinearMap
      (meromorphicNumeratorIdealAt B S hS X L t V e hcompat hfree) = LinearMap.ker π := by
    ext m
    refine Iff.trans ?_ ((LinearMap.mem_ker (f := π)).trans (hex m)).symm
    constructor
    · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
      exact ⟨⟨a, ha⟩, (meromorphicDenominatorNumerator_eq_smul_of_free B S hS X L t V e hcompat
        hfree hL ha hy).trans rfl⟩
    · rintro ⟨⟨a, ha⟩, rfl⟩
      obtain ⟨y, hy⟩ := (isMeromorphicDenominator_iff_of_free B S hS X L t V e hcompat hfree a).1 ha
      exact ⟨y, ⟨a, ha, hy⟩, ((meromorphicDenominatorNumerator_eq_smul_of_free B S hS X L t V e
        hcompat hfree hL ha hy).trans rfl).symm⟩
  exact (LinearMap.quotKerEquivOfSurjective π hsurj).symm.trans
    (Submodule.Quotient.equiv _ _ eL hker).symm

end FreeChart

end AlgebraicGeometry.Space

end
