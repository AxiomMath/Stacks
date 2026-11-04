module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.AffineSpaceFibreChartConstants
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniNonSmoothClosedPoints
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank

/-!
# The linear subspace of the fibre cut out by the evaluation of a linear system

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]) and let `x` be a
closed point of `X`. The dimension count in the proof of [Stacks, Tag 0FD6] bounds the fibre of
the projection `Σ → X` over `x` by the linear subspace of `𝔸^r_{κ(x)}` cut out by the kernel of
the evaluation `ev_x : V → ℒ_x/𝔪_x²ℒ_x`.

This module builds that subspace as a closed subset `L` of `H_univ` and proves the bound. The
data it takes is the **matrix of the evaluation**: a family of coefficient vectors
`M : {1, …, r} → τ → k` whose associated map `k^r → k^τ` is surjective — in the situation of
Tag 0FD6 this is `Stacks.ImmersionEvaluationSurjective.evalCoord` read in a basis of its target,
so `#τ = n + 1` and the kernel has dimension `r - (n + 1)`.

Given `M`, the `j`-th coefficient vector gives the global function `∑ᵢ Mᵢⱼ xᵢ` on `𝔸^r_X`, and
`L` is the set of points of `H_univ` which lie over `x` and at which all of those functions
vanish. It is closed, and its dimension is at most `r - #τ`, because over `x` the chart of the
fibre identifies it with a subset of the linear subspace of `𝔸^r_{κ(x)}` cut out by the same
forms with coefficients read in `κ(x)` — the point at which the identification
`k ≅ κ(x)` at a closed point over an algebraically closed field is used.

## Main definitions

* `Stacks.LinearSubspace.coeffMap`: the linear map `κ^ι → κ^τ` of a family of coefficient
  vectors.
* `Stacks.Bertini.FamilyDivisors.constSection`: a scalar read as a global function on `X`.
* `Stacks.Bertini.FamilyDivisors.residueStructureMap`: the structure map `k → κ(x)`.
* `Stacks.Bertini.FamilyDivisors.evalCoordForm`: the function `∑ᵢ Mᵢⱼ xᵢ` on `𝔸^r_X`.
* `Stacks.Bertini.FamilyDivisors.evalSubspace`: **the closed subset `L` of `H_univ`**.

## Main results

* `Stacks.LinearSubspace.surjective_coeffMap_map`: surjectivity of a coefficient map is
  preserved by a surjective change of coefficient field.
* `Stacks.Bertini.FamilyDivisors.surjective_residueStructureMap`: at a closed point over an
  algebraically closed field the structure map `k → κ(x)` is surjective.
* `Stacks.Bertini.FamilyDivisors.isClosed_evalSubspace`: `L` is closed in `H_univ`.
* `Stacks.Bertini.FamilyDivisors.topologicalKrullDim_evalSubspace_le`: **`dim L ≤ r - #τ`**.

## Implementation notes

`L` is defined as the inverse image under the closed immersion `H_univ → 𝔸^r_X` of a closed
subset of `𝔸^r_X`, so closedness is immediate and the dimension bound is the bound for that
subset, the closed immersion being a topological embedding.

The coefficients of the forms are scalars of `k`, pushed into `Γ(X, ⊤)` by the structure
morphism and then into `Γ(𝔸^r_X, ⊤)`; `AlgebraicGeometry.AffineSpace.coordForm` is exactly that
shape, and `AlgebraicGeometry.AffineSpace.residueFibreChart_appTop_coordForm` reads such a form
in the chart of the fibre as the linear form whose coefficients are the values at `x`, that is,
the images of the `Mᵢⱼ` under the structure map `k → κ(x)`.

The dimension of the kernel is computed over `κ(x)` by rank-nullity rather than transported from
`k`: surjectivity is all that has to travel along `k ≅ κ(x)`, and
`LinearMap.finrank_ker_eq_sub_of_surjective` then gives `r - #τ` on the `κ(x)` side directly.

No `@[stacks]` attribute is attached: this is a step inside the proof of Tag 0FD6.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v w

namespace Stacks.LinearSubspace

/-- **The linear map of a family of coefficient vectors**: `c ↦ (∑ᵢ Bᵢⱼ cᵢ)ⱼ`. -/
def coeffMap {κ : Type*} [Field κ] {ι τ : Type*} [Fintype ι] (B : ι → τ → κ) :
    (ι → κ) →ₗ[κ] (τ → κ) where
  toFun c j := ∑ i, B i j * c i
  map_add' c d := by
    funext j
    simp only [Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' a c := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The `j`-th coordinate of `coeffMap B c` is `∑ᵢ Bᵢⱼ cᵢ`. -/
@[simp]
theorem coeffMap_apply {κ : Type*} [Field κ] {ι τ : Type*} [Fintype ι] (B : ι → τ → κ)
    (c : ι → κ) (j : τ) : coeffMap B c j = ∑ i, B i j * c i := rfl

/-- `coeffMap B` sends the `i`-th standard basis vector to the `i`-th coefficient vector `B i`. -/
theorem coeffMap_single {κ : Type*} [Field κ] {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → τ → κ) (i : ι) (j : τ) : coeffMap B (Pi.single i 1) j = B i j := by
  rw [coeffMap_apply, Finset.sum_eq_single i
    (fun i' _ hi' => by rw [Pi.single_eq_of_ne hi', mul_zero]) (fun h => absurd
      (Finset.mem_univ i) h), Pi.single_eq_same, mul_one]

/-- **Surjectivity of a coefficient map survives a surjective change of coefficient field.**
A preimage of the target vector is found over the small field and pushed forward. -/
theorem surjective_coeffMap_map {k κ : Type*} [Field k] [Field κ] (γ : k →+* κ)
    (hγ : Function.Surjective γ) {ι τ : Type*} [Fintype ι] (M : ι → τ → k)
    (hM : Function.Surjective (coeffMap M)) :
    Function.Surjective (coeffMap (fun i j => γ (M i j))) := by
  intro t
  choose t' ht' using fun j => hγ (t j)
  obtain ⟨c, hc⟩ := hM t'
  refine ⟨fun i => γ (c i), funext fun j => ?_⟩
  have h : (coeffMap (fun i j => γ (M i j)) (fun i => γ (c i))) j = γ (coeffMap M c j) := by
    rw [coeffMap_apply, coeffMap_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_mul γ _ _).symm
  rw [h, hc, ht']

end Stacks.LinearSubspace

namespace Stacks.Bertini.FamilyDivisors

open Stacks.LinearSubspace

variable (D : FamilyDivisors.{u, v})

/-- **A scalar of the base field read as a global function on `X`**, along the structure
morphism. -/
def constSection (c : D.k) : Γ(D.X, ⊤) :=
  D.toBase.appTop ((Scheme.ΓSpecIso (.of D.k)).inv c)

/-- **The structure map `k → κ(x)`** of the residue field at a point of `X`. -/
def residueStructureMap (x : D.X) : D.k →+* ↥(D.X.residueField x) :=
  ((Scheme.ΓSpecIso (.of D.k)).inv ≫ D.toBase.appTop ≫ D.X.Γevaluation x).hom

/-- The value at `x` of the constant function with value `c` is the image of `c` under the
structure map of the residue field. -/
theorem Γevaluation_constSection (x : D.X) (c : D.k) :
    D.X.Γevaluation x (D.constSection c) = D.residueStructureMap x c := rfl

/-- **At a closed point over an algebraically closed field the structure map `k → κ(x)` is
surjective**, being the inverse of the identification `κ(x) ≅ k`. -/
theorem surjective_residueStructureMap [IsAlgClosed D.k] [LocallyOfFiniteType D.toBase]
    {x : D.X} (hx : IsClosed ({x} : Set D.X)) :
    Function.Surjective (D.residueStructureMap x) := by
  let : Algebra D.k ↥(D.X.residueField x) :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫ D.toBase.appTop ≫ D.X.Γevaluation x).hom.toAlgebra
  have h := AlgebraicGeometry.bijective_algebraMap_residueField_of_isClosed D.toBase x hx
  rw [RingHom.algebraMap_toAlgebra] at h
  exact h.2

variable {τ : Type w} [Fintype τ]

/-- **The linear form `∑ᵢ Mᵢⱼ xᵢ` in the coordinates of `𝔸^r_X`**, with the coefficients of the
`j`-th row of `M` read as constant functions along the structure morphism. -/
def evalCoordForm (M : D.basisIndex → τ → D.k) (j : τ) : Γ(D.parameterSpace, ⊤) :=
  AffineSpace.coordForm D.basisIndex (fun i => D.constSection (M i j))

/-- **The locus in `𝔸^r_X` over `x` where all the forms of `M` vanish.** -/
def evalZeroSet (x : D.X) (M : D.basisIndex → τ → D.k) : Set D.parameterSpace :=
  (D.parameterProjection.base ⁻¹' {x}) ∩
    ⋂ j, ((D.parameterSpace.basicOpen (D.evalCoordForm M j) : Set D.parameterSpace))ᶜ

omit [Fintype τ] in
/-- A point `y` of `𝔸^r_X` lies in `evalZeroSet x M` if and only if it lies over `x` and lies
outside the basic open of every form `evalCoordForm M j`. -/
theorem mem_evalZeroSet {x : D.X} {M : D.basisIndex → τ → D.k} {y : D.parameterSpace} :
    y ∈ D.evalZeroSet x M ↔ D.parameterProjection.base y = x ∧
      ∀ j, y ∉ (D.parameterSpace.basicOpen (D.evalCoordForm M j) : Set D.parameterSpace) := by
  simp only [evalZeroSet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_iInter, Set.mem_compl_iff]

omit [Fintype τ] in
/-- The locus over a closed point where a family of coordinate forms vanishes is closed: it is
the intersection of the inverse image of a closed point with the complements of the basic
opens. -/
theorem isClosed_evalZeroSet {x : D.X} (hx : IsClosed ({x} : Set D.X))
    (M : D.basisIndex → τ → D.k) : IsClosed (D.evalZeroSet x M) :=
  (hx.preimage D.parameterProjection.base.hom.continuous).inter
    (isClosed_iInter fun j => ((D.parameterSpace.basicOpen
      (D.evalCoordForm M j)).2).isClosed_compl)

/-- **The linear subspace `L` of `H_univ` cut out by the forms of `M` over `x`**: the points of
the universal divisor which lie over `x` and at which all the forms vanish. -/
def evalSubspace (x : D.X) (M : D.basisIndex → τ → D.k) : Set D.universalDivisorScheme :=
  D.universalDivisor.subschemeι.base ⁻¹' D.evalZeroSet x M

omit [Fintype τ] in
/-- **`L` is closed in `H_univ`.** -/
theorem isClosed_evalSubspace {x : D.X} (hx : IsClosed ({x} : Set D.X))
    (M : D.basisIndex → τ → D.k) : IsClosed (D.evalSubspace x M) :=
  (D.isClosed_evalZeroSet hx M).preimage D.universalDivisor.subschemeι.base.hom.continuous

/-- **`dim L ≤ r - #τ`.** Read in the chart of the fibre of `𝔸^r_X → X` over `x`, the forms of
`M` become the linear forms with coefficients the images of the `Mᵢⱼ` in `κ(x)`, whose common
zero locus is a linear subspace of `𝔸^r_{κ(x)}` of dimension the dimension of the kernel of the
corresponding map `κ(x)^r → κ(x)^τ`. That map is surjective because the one over `k` is and
`k → κ(x)` is onto at a closed point over an algebraically closed field, so rank-nullity gives
`r - #τ`.

With `M` the matrix of the evaluation `ev_x` of the linear system and `#τ = n + 1` this is the
fibre bound `r - (n + 1)` of the dimension count in the proof of [Stacks, Tag 0FD6]. -/
theorem topologicalKrullDim_evalSubspace_le [IsAlgClosed D.k] [LocallyOfFiniteType D.toBase]
    {x : D.X} (hx : IsClosed ({x} : Set D.X)) (M : D.basisIndex → τ → D.k)
    (hM : Function.Surjective (coeffMap M)) :
    topologicalKrullDim (D.evalSubspace x M) ≤
      ((Nat.card D.basisIndex - Fintype.card τ : ℕ) : WithBot ℕ∞) := by
  classical
  have hφ : Function.Surjective
      (coeffMap (fun i j => D.residueStructureMap x (M i j))) :=
    surjective_coeffMap_map _ (D.surjective_residueStructureMap hx) M hM
  have hker : Module.finrank ↥(D.X.residueField x)
      (LinearMap.ker (coeffMap (fun i j => D.residueStructureMap x (M i j)))) =
      Nat.card D.basisIndex - Fintype.card τ := by
    rw [LinearMap.finrank_ker_eq_sub_of_surjective hφ, Module.finrank_pi, Module.finrank_pi,
      Nat.card_eq_fintype_card]
  have hemb : Topology.IsEmbedding D.universalDivisor.subschemeι.base :=
    D.universalDivisor.subschemeι.isClosedEmbedding.isEmbedding
  refine le_trans (le_of_eq (IsHomeomorph.topologicalKrullDim_eq _
    (hemb.homeomorphImage (D.evalSubspace x M)).isHomeomorph)) ?_
  refine le_trans (topologicalKrullDim_le_of_subset
    (Set.image_preimage_subset D.universalDivisor.subschemeι.base (D.evalZeroSet x M))) ?_
  rw [← hker]
  refine AffineSpace.topologicalKrullDim_le_finrank_ker_of_coordForm_vanishing D.basisIndex x
    hφ (fun j i => D.constSection (M i j)) (fun j i => ?_) (D.evalZeroSet x M)
    (fun y hy => ?_)
  · rw [D.Γevaluation_constSection x (M i j), coeffMap_single]
  · exact ⟨(D.mem_evalZeroSet.mp hy).1, (D.mem_evalZeroSet.mp hy).2⟩

end Stacks.Bertini.FamilyDivisors

end
