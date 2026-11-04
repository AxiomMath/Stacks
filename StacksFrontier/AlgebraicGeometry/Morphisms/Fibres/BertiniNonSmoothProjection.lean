module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.NonSmoothLocusFibreDimension

/-!
# The projection of the non-smooth locus of the universal family to `X`

Let `Σ ⊂ H_univ` be the locus where the universal family `q : H_univ → 𝔸^r_k` is not smooth.
This file builds the projection

`Σ ⊂ H_univ ⊂ 𝔸^r_X = 𝔸^r_k ×_k X → X`

and shows that a bound on the dimension of its fibres gives a nonempty open `U ⊂ 𝔸^r_k` whose
preimage lies in the smooth locus of `q`.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.universalDivisorToBase`: the structure morphism
  `H_univ → Spec k`.
* `Stacks.Bertini.FamilyDivisors.nonSmoothToX`: the projection `Σ → X` of the non-smooth locus
  of `q` to the ambient scheme.

## Main results

* `Stacks.Bertini.FamilyDivisors.universalFamilyMap_comp_over`: `q` lies over `Spec k`.
* `Stacks.Bertini.FamilyDivisors.nonSmoothToX_comp_toBase`: the projection `Σ → X` lies over
  `Spec k` as well.
* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_fiber_le`: if
  `dim X ≤ n`, if `n + 1 ≤ r`, and if every fibre of `Σ → X` has local dimension at most
  `r - (n + 1)`, then there is a nonempty open `U ⊂ 𝔸^r_k` with `q ⁻¹ᵁ U` inside the smooth locus
  of `q`.
* `Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral_of_fiber_le`: under the
  same hypotheses, with `X` smooth over `k`, the divisor `H_v` is smooth over `k'` for general
  `v ∈ V ⊗_k k'`.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L), part (3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, v})

/-- The structure morphism `H_univ → Spec k`: the closed immersion of the universal divisor into
`𝔸^r_X`, the projection `𝔸^r_X → X`, and the structure morphism of `X`. -/
def universalDivisorToBase : D.universalDivisorScheme ⟶ Spec (.of D.k) :=
  D.universalDivisor.subschemeι ≫ D.parameterProjection ≫ D.toBase

/-- The structure morphism `H_univ → Spec k` is locally of finite type when `X` is. -/
instance locallyOfFiniteType_universalDivisorToBase [LocallyOfFiniteType D.toBase] :
    LocallyOfFiniteType D.universalDivisorToBase := by
  have h₁ : LocallyOfFiniteType D.parameterProjection :=
    inferInstanceAs (LocallyOfFiniteType (𝔸(D.basisIndex; D.X) ↘ D.X))
  exact MorphismProperty.comp_mem _ _ _ inferInstance (MorphismProperty.comp_mem _ _ _ h₁
    inferInstance)

/-- The morphism `q : H_univ → 𝔸^r_k` lies over `Spec k`: its composite with the structure
morphism of `𝔸^r_k` is the structure morphism `H_univ → Spec k`. -/
theorem universalFamilyMap_comp_over :
    D.universalFamilyMap ≫ (𝔸(D.basisIndex; Spec (.of D.k)) ↘ Spec (.of D.k)) =
      D.universalDivisorToBase := by
  rw [universalFamilyMap, universalDivisorToBase, Category.assoc,
    AffineSpace.map_over D.toBase]

/-- The projection `Σ → X` of the non-smooth locus of the universal family to the ambient
scheme: the closed immersion of `Σ` into `H_univ`, the closed immersion of `H_univ` into
`𝔸^r_X`, and the projection `𝔸^r_X = 𝔸^r_k ×_k X → X`. -/
def nonSmoothToX [Smooth D.toBase] : D.universalFamilyMap.nonSmoothSubscheme ⟶ D.X :=
  D.universalFamilyMap.nonSmoothSubschemeι ≫ D.universalDivisor.subschemeι ≫
    D.parameterProjection

/-- The projection `Σ → X` lies over `Spec k`: its composite with the structure morphism of `X`
is the inclusion of `Σ` followed by the structure morphism `H_univ → Spec k`. -/
theorem nonSmoothToX_comp_toBase [Smooth D.toBase] :
    D.nonSmoothToX ≫ D.toBase =
      D.universalFamilyMap.nonSmoothSubschemeι ≫ D.universalDivisorToBase := by
  rw [nonSmoothToX, universalDivisorToBase, Category.assoc, Category.assoc]

/-- With `r` the dimension of the linear system, suppose `dim X ≤ n`, suppose `n + 1 ≤ r`, and
suppose every fibre of the projection `Σ → X` of the non-smooth locus of `q : H_univ → 𝔸^r_k` has
local dimension at most `r - (n + 1)`. Then there is a nonempty open `U ⊂ 𝔸^r_k` whose preimage
under `q` lies in the smooth locus of `q`. It assumes that `X` is smooth and locally of finite type
over `k` and that `H_univ` is a Noetherian space. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_fiber_le [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] [NoetherianSpace D.universalDivisorScheme] {n : ℕ}
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hfib : ∀ z : D.universalFamilyMap.nonSmoothSubscheme,
      topologicalKrullDimAt (D.nonSmoothToX.fiber (D.nonSmoothToX z)) (D.nonSmoothToX.asFiber z) ≤
        ((Nat.card D.basisIndex - (n + 1) : ℕ) : WithBot ℕ∞)) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) :=
  AlgebraicGeometry.exists_nonempty_opens_preimage_subset_smoothLocus_of_fiber_le D.k
    D.basisIndex D.universalFamilyMap D.universalDivisorToBase D.universalFamilyMap_comp_over
    D.toBase D.nonSmoothToX D.nonSmoothToX_comp_toBase hnr hX hfib

/-- In the standing situation of `Stacks.Bertini.FamilyDivisors` with `X` smooth over `k`, if
`dim X ≤ n`, if `n + 1 ≤ r`, and if every fibre of the projection `Σ → X` of the non-smooth locus
of `q` has local dimension at most `r - (n + 1)`, then `H_v` is smooth over `k'` for general
`v ∈ V ⊗_k k'`. It assumes that `X` is locally of finite type over `k` and that `H_univ` is a
Noetherian space, and takes the fibre bound as the hypothesis `hfib`. -/
theorem smooth_specializedDivisor_forGeneral_of_fiber_le [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] [NoetherianSpace D.universalDivisorScheme] {n : ℕ}
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hfib : ∀ z : D.universalFamilyMap.nonSmoothSubscheme,
      topologicalKrullDimAt (D.nonSmoothToX.fiber (D.nonSmoothToX z)) (D.nonSmoothToX.asFiber z) ≤
        ((Nat.card D.basisIndex - (n + 1) : ℕ) : WithBot ℕ∞)) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) := by
  obtain ⟨U, hU, hsing⟩ :=
    D.exists_nonempty_opens_subset_smoothLocus_of_fiber_le hnr hX hfib
  exact D.smooth_specializedDivisor_forGeneral U hU hsing

end Stacks.Bertini.FamilyDivisors

end
