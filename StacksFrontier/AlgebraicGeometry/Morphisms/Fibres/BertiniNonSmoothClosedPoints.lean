module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ClosedPointBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniNonSmoothProjection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre bound for the non-smooth locus needs checking only over closed points

Let `Σ` be the non-smooth locus of the universal family `q : H_univ → 𝔸^r_k` of a family of
divisors on a scheme `X` over a field `k`, and let `p : Σ → X` be the projection. When `X` is
smooth and locally of finite type over `k`, both `Σ` and `X` are Jacobson spaces and the local
dimension of the fibres of `p` is upper semicontinuous on `Σ`, so a bound on the dimension of the
fibres `Σ_x` over the closed points `x` of `X` implies the same bound on the local dimension of the
fibre at every point of `Σ`. The results below take the closed-point bound as a hypothesis.

## Main results

* `Stacks.Bertini.FamilyDivisors.locallyOfFiniteType_nonSmoothToX` and
  `Stacks.Bertini.FamilyDivisors.jacobsonSpace_nonSmoothSubscheme`: the projection `Σ → X` is
  locally of finite type and `Σ` is a Jacobson space.
* `Stacks.Bertini.FamilyDivisors.fiber_nonSmoothToX_le_of_isClosed_singleton`: the fibre bound at
  every point of `Σ` from the bound on the dimension of `Σ_x` for closed `x`.
* `Stacks.Bertini.FamilyDivisors.topologicalKrullDim_fiber_nonSmoothToX_le_of_subset`: the
  dimension of `Σ_x` is bounded by that of any subset of `H_univ` containing the points over `x`
  at which `q` is not smooth.
* `Stacks.Bertini.FamilyDivisors.topologicalKrullDim_fiber_nonSmoothToX_le_of_closedPoints`: the
  same with the containment required only at the closed points of `H_univ`, the target set being
  closed.
* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_closed_fiber_le` and
  `Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral_of_closed_fiber_le`:
  `exists_nonempty_opens_subset_smoothLocus_of_fiber_le` and
  `smooth_specializedDivisor_forGeneral_of_fiber_le` with their fibre hypothesis at all points
  replaced by the one at closed points.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, v})

/-- For `X` smooth over `k`, the projection `Σ → X` is locally of finite type. -/
instance locallyOfFiniteType_nonSmoothToX [Smooth D.toBase] :
    LocallyOfFiniteType D.nonSmoothToX := by
  rw [nonSmoothToX]
  have h₁ : LocallyOfFiniteType D.parameterProjection :=
    inferInstanceAs (LocallyOfFiniteType (𝔸(D.basisIndex; D.X) ↘ D.X))
  exact MorphismProperty.comp_mem _ _ _ inferInstance
    (MorphismProperty.comp_mem _ _ _ inferInstance h₁)

/-- `X` is a Jacobson space when it is locally of finite type over the field `k`. -/
@[ega "IV 10.4.7" "special case"]
theorem jacobsonSpace_X [LocallyOfFiniteType D.toBase] : JacobsonSpace D.X :=
  LocallyOfFiniteType.jacobsonSpace D.toBase

/-- For `X` smooth and locally of finite type over the field `k`, the non-smooth locus `Σ` is a
Jacobson space. -/
theorem jacobsonSpace_nonSmoothSubscheme [Smooth D.toBase] [LocallyOfFiniteType D.toBase] :
    JacobsonSpace D.universalFamilyMap.nonSmoothSubscheme :=
  let := D.jacobsonSpace_X
  LocallyOfFiniteType.jacobsonSpace D.nonSmoothToX

/-- Let `X` be smooth and locally of finite type over `k`. Suppose that for every closed point
`x` of `X` the fibre `Σ_x` of the projection of the non-smooth locus has dimension at most `m`.
Then at every point `z` of `Σ` the fibre through `z` has local dimension at most `m`. -/
theorem fiber_nonSmoothToX_le_of_isClosed_singleton [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] {m : ℕ}
    (hclosed : ∀ x : D.X, IsClosed {x} →
      topologicalKrullDim (D.nonSmoothToX.fiber x) ≤ (m : WithBot ℕ∞))
    (z : D.universalFamilyMap.nonSmoothSubscheme) :
    topologicalKrullDimAt (D.nonSmoothToX.fiber (D.nonSmoothToX z)) (D.nonSmoothToX.asFiber z) ≤
      (m : WithBot ℕ∞) :=
  let := D.jacobsonSpace_X
  let := D.jacobsonSpace_nonSmoothSubscheme
  AlgebraicGeometry.fiberDimensionAt_le_of_isClosed_singleton_target D.nonSmoothToX hclosed z

/-- Let `X` be smooth over `k`. If a subset `Z` of `H_univ` of dimension at most `d` contains
every point of `H_univ` lying over `x` at which `q` is not smooth, then the fibre of `Σ → X` over
`x` has dimension at most `d`. -/
theorem topologicalKrullDim_fiber_nonSmoothToX_le_of_subset [Smooth D.toBase] (x : D.X)
    {d : WithBot ℕ∞} (Z : Set D.universalDivisorScheme)
    (hZ : {w : D.universalDivisorScheme | w ∉ D.universalFamilyMap.smoothLocus ∧
        D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x} ⊆ Z)
    (hdim : topologicalKrullDim Z ≤ d) :
    topologicalKrullDim (D.nonSmoothToX.fiber x) ≤ d := by
  set ι := D.universalFamilyMap.nonSmoothSubschemeι with hιdef
  have hemb : Topology.IsEmbedding ι.base := ι.isClosedEmbedding.isEmbedding
  set A : Set D.universalFamilyMap.nonSmoothSubscheme := D.nonSmoothToX.base ⁻¹' {x} with hAdef
  have himg : ι.base '' A ⊆ Z := by
    rintro _ ⟨z, hz, rfl⟩
    refine hZ ⟨Scheme.Hom.notMem_smoothLocus_nonSmoothSubschemeι _ z, hz⟩
  refine AlgebraicGeometry.topologicalKrullDim_fiber_le_of_preimage_subset D.nonSmoothToX x
    A (le_refl _) ?_
  exact le_trans (le_of_eq (IsHomeomorph.topologicalKrullDim_eq _
    (hemb.homeomorphImage A).isHomeomorph)) (le_trans (topologicalKrullDim_le_of_subset himg)
      hdim)

/-- `H_univ` is a Jacobson space when `X` is locally of finite type over the field `k`. -/
theorem jacobsonSpace_universalDivisorScheme [LocallyOfFiniteType D.toBase] :
    JacobsonSpace D.universalDivisorScheme :=
  let : JacobsonSpace (Spec (CommRingCat.of D.k)) := inferInstance
  LocallyOfFiniteType.jacobsonSpace D.universalDivisorToBase

/-- For `X` smooth over `k` and `x` a closed point of `X`, the points of `H_univ` over `x` at
which `q` is not smooth form a closed set. -/
theorem isClosed_nonSmooth_over [Smooth D.toBase] {x : D.X} (hx : IsClosed {x}) :
    IsClosed {w : D.universalDivisorScheme | w ∉ D.universalFamilyMap.smoothLocus ∧
      D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x} := by
  have h₁ : IsClosed ((D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme)ᶜ) :=
    Scheme.Hom.isClosed_compl_smoothLocus D.universalFamilyMap
  have h₂ : IsClosed ((D.universalDivisor.subschemeι ≫ D.parameterProjection).base ⁻¹' {x}) :=
    hx.preimage (D.universalDivisor.subschemeι ≫ D.parameterProjection).base.hom.continuous
  exact h₁.inter h₂

/-- Let `X` be smooth and locally of finite type over `k`, let `x` be a closed point of `X` and
let `L` be a closed subset of `H_univ` of dimension at most `d`. If every point of `H_univ` which
is closed, lies over `x`, and is a point of non-smoothness of `q` belongs to `L`, then the fibre
of `Σ → X` over `x` has dimension at most `d`. -/
theorem topologicalKrullDim_fiber_nonSmoothToX_le_of_closedPoints [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] {x : D.X} (hx : IsClosed {x}) {d : WithBot ℕ∞}
    (L : Set D.universalDivisorScheme) (hL : IsClosed L)
    (hmem : ∀ w : D.universalDivisorScheme, IsClosed {w} →
      w ∉ D.universalFamilyMap.smoothLocus →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x → w ∈ L)
    (hdim : topologicalKrullDim L ≤ d) :
    topologicalKrullDim (D.nonSmoothToX.fiber x) ≤ d :=
  let := D.jacobsonSpace_universalDivisorScheme
  D.topologicalKrullDim_fiber_nonSmoothToX_le_of_subset x L
    (Set.subset_of_isClosed_of_closedPoints_subset (D.isClosed_nonSmooth_over hx) hL
      (fun w hw hwc ↦ hmem w hwc hw.1 hw.2)) hdim

/-- Let `X` be smooth and locally of finite type over `k` with `H_univ` Noetherian, and let `r`
be the dimension of the linear system. Suppose `dim X ≤ n`, suppose `n + 1 ≤ r`, and suppose that
for every closed point `x` of `X` the fibre `Σ_x` of the projection of the non-smooth locus of
`q : H_univ → 𝔸^r_k` has dimension at most `r - (n + 1)`. Then there is a nonempty open
`U ⊂ 𝔸^r_k` whose preimage under `q` lies in the smooth locus of `q`. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_closed_fiber_le [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] [NoetherianSpace D.universalDivisorScheme] {n : ℕ}
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hclosed : ∀ x : D.X, IsClosed {x} →
      topologicalKrullDim (D.nonSmoothToX.fiber x) ≤
        ((Nat.card D.basisIndex - (n + 1) : ℕ) : WithBot ℕ∞)) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) :=
  D.exists_nonempty_opens_subset_smoothLocus_of_fiber_le hnr hX
    (D.fiber_nonSmoothToX_le_of_isClosed_singleton hclosed)

/-- Let `X` be smooth and locally of finite type over `k` with `H_univ` Noetherian. If
`dim X ≤ n`, if `n + 1 ≤ r`, and if the fibre of the projection `Σ → X` over every closed point
of `X` has dimension at most `r - (n + 1)`, then `H_v` is smooth over `k'` for general
`v ∈ V ⊗_k k'`. -/
theorem smooth_specializedDivisor_forGeneral_of_closed_fiber_le [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] [NoetherianSpace D.universalDivisorScheme] {n : ℕ}
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hclosed : ∀ x : D.X, IsClosed {x} →
      topologicalKrullDim (D.nonSmoothToX.fiber x) ≤
        ((Nat.card D.basisIndex - (n + 1) : ℕ) : WithBot ℕ∞)) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.smooth_specializedDivisor_forGeneral_of_fiber_le hnr hX
    (D.fiber_nonSmoothToX_le_of_isClosed_singleton hclosed)

end Stacks.Bertini.FamilyDivisors

end
