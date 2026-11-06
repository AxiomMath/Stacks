module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.GradedAlgebra.SymmetricAway.DegreeOneChart
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# The dimension of projective space

Projective space `ℙ^{r-1}` over a field `K` is `Proj` of the polynomial algebra on `r` variables,
graded by total degree. It is covered by the `r` standard affine charts `D₊(Xᵢ)`, and each chart
is the spectrum of a polynomial algebra on `r - 1` variables over `K`
(`Stacks.SymmetricAway.chartAlgEquiv`), hence has dimension `r - 1`. Two facts follow.

The topological Krull dimension of `ℙ^{r-1}` is `r - 1`. The lower bound is that a chart is a
subspace. The upper bound is local: the dimension of a space is the supremum of its local
dimensions (`TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim`), and the local dimension
at a point is bounded by the dimension of any open neighbourhood of it, so by the dimension of
whichever chart contains the point.

`ℙ^{r-1}` is equidimensional. Each chart is irreducible, being the spectrum of a polynomial
algebra over a field; an irreducible component of the whole space which meets a chart therefore
restricts to the chart's unique irreducible component, namely the whole chart, and so contains
that chart. A component thus has dimension at least `r - 1`, and at most the dimension of the
whole space, which is `r - 1`.

Together these are what `AlgebraicGeometry.RelativeDimension` asks of a nonempty fibre, and so
they are the input to the relative dimension of a projective bundle: the fibres of a projective
bundle of rank `r` are the projective spaces `ℙ^{r-1}` over the residue fields of the base.

## Main results

* `Stacks.ProjectiveSpace.topologicalKrullDim_basicOpen`: a standard chart of projective space
  has dimension one less than the number of variables.
* `Stacks.ProjectiveSpace.topologicalKrullDim_proj`: so does projective space itself.
* `Stacks.ProjectiveSpace.irreducibleSpace_basicOpen`: each standard chart is irreducible.
* `Stacks.ProjectiveSpace.basicOpen_subset_of_mem_irreducibleComponents`: an irreducible
  component contains every standard chart it meets.
* `Stacks.ProjectiveSpace.equidimensional_proj`: projective space over a field is
  equidimensional.
* `Stacks.ProjectiveSpace.equidimensional_and_topologicalKrullDim_proj_fin`: the two statements
  together, for the variables indexed by `Fin r`.

## Implementation notes

The index type of the variables is an arbitrary finite type `σ`, and the dimension is
`Nat.card σ - 1`; `Fin r` versions of the two main results are derived at the end, because that
is the form in which a projective bundle of rank `r` presents its fibres. Nonemptiness of `σ` is
needed for the dimension — for `σ` empty `Proj K` is the empty scheme, whose dimension is `⊥` and
not `0` — but not for equidimensionality, which is vacuous there.

The charts are handled as *subspaces* of `Proj`, i.e. through the coercion of
`AlgebraicGeometry.Proj.basicOpen` to a `Set`, rather than as the open subschemes
`Scheme.Opens.toScheme`: the two carriers agree, and the subspace form is the one that
`topologicalKrullDim_subspace_le` and `preimage_mem_irreducibleComponents` expect.

Only `iSup_basicOpen_X_eq_top` carries a `@[stacks]` attribute, for the covering half of tag
01NG, which it proves for an arbitrary coefficient ring and index type; the affine-space half of
that tag is `AlgebraicGeometry.ProjectiveSpace.basicOpenXIsoAffineSpace`. Nothing else here is one
of the assertions of a Stacks tag. The relative dimension of a projective bundle is part of tag
02TX, whose statement is about the relative `Proj` of a symmetric algebra; this is one input to it.

## References

* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 0058](https://stacks.math.columbia.edu/tag/0058)
-/

@[expose] public noncomputable section

open AlgebraicGeometry MvPolynomial TopologicalSpace Stacks.SymmetricAway

namespace Stacks.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

/-! ### The standard covering -/

section Covering

variable {R : Type u} [CommRing R] {σ : Type v}

/-- **The standard opens `D₊(Xᵢ)` cover `Proj` of the polynomial algebra graded by total
degree.** For `R = ℤ` and `σ = Fin (n + 1)` this is the standard covering of projective
`n`-space over the integers. -/
@[stacks 01NG "standard-open covering"]
theorem iSup_basicOpen_X_eq_top (R : Type u) [CommRing R] (σ : Type v) :
    (⨆ i : σ, Proj.basicOpen (homogeneousSubmodule σ R) (X i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' _ X (fun i => ⟨1, X_mem_homogeneousSubmodule_one i⟩)
    (adjoin_range_X_gradeZero R σ)

/-- Every point of `Proj` of the polynomial algebra lies in one of the standard charts. -/
theorem exists_mem_basicOpen_X (x : Proj (homogeneousSubmodule σ R)) :
    ∃ i : σ, x ∈ Proj.basicOpen (homogeneousSubmodule σ R) (X i) := by
  have hx : x ∈ (⨆ i : σ, Proj.basicOpen (homogeneousSubmodule σ R) (X i)) := by
    rw [iSup_basicOpen_X_eq_top]; trivial
  exact Opens.mem_iSup.mp hx

end Covering

variable {K : Type u} [Field K] {σ : Type v} [Finite σ]

/-! ### The standard charts -/

/-- Removing one index from a finite type drops its cardinality by one. -/
theorem card_subtype_ne (i : σ) : Nat.card {j : σ // j ≠ i} = Nat.card σ - 1 := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

/-- A standard chart of projective space over a field is a domain: it is a polynomial algebra. -/
instance isDomainChartRing (i : σ) : IsDomain (chartRing K i) :=
  MulEquiv.isDomain (MvPolynomial {j : σ // j ≠ i} K)
    (chartAlgEquiv (R := K) i).symm.toRingEquiv.toMulEquiv

/-- A standard chart of projective space over a field has Krull dimension one less than the
number of variables. -/
theorem ringKrullDim_chartRing (i : σ) :
    ringKrullDim (chartRing K i) = ((Nat.card σ - 1 : ℕ) : WithBot ℕ∞) := by
  rw [← ringKrullDim_eq_of_ringEquiv (chartAlgEquiv (R := K) i).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    ENat.card_eq_coe_natCard, card_subtype_ne]
  norm_cast

/-- The standard chart `D₊(Xᵢ)` of projective space is the spectrum of the chart ring. -/
def chartHomeo (i : σ) :
    ((Proj.basicOpen (homogeneousSubmodule σ K) (X i) :
        Set (Proj (homogeneousSubmodule σ K)))) ≃ₜ PrimeSpectrum (chartRing K i) :=
  (Proj.basicOpenIsoSpec (homogeneousSubmodule σ K) (X i)
    (X_mem_homogeneousSubmodule_one i) Nat.one_pos).hom.homeomorph

/-- **A standard chart of projective space has dimension one less than the number of
variables.** -/
theorem topologicalKrullDim_basicOpen (i : σ) :
    topologicalKrullDim ((Proj.basicOpen (homogeneousSubmodule σ K) (X i) :
        Set (Proj (homogeneousSubmodule σ K)))) = ((Nat.card σ - 1 : ℕ) : WithBot ℕ∞) := by
  rw [IsHomeomorph.topologicalKrullDim_eq _ (chartHomeo (K := K) i).isHomeomorph,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_chartRing]

/-! ### The dimension -/

/-- Projective space has dimension at most one less than the number of variables: the dimension
is the supremum of the local dimensions, and every point has a chart for a neighbourhood. -/
theorem topologicalKrullDim_le (K : Type u) [Field K] (σ : Type v) [Finite σ] :
    topologicalKrullDim (Proj (homogeneousSubmodule σ K))
      ≤ ((Nat.card σ - 1 : ℕ) : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x => ?_
  obtain ⟨i, hi⟩ := exists_mem_basicOpen_X (R := K) x
  refine le_trans ?_ (topologicalKrullDim_basicOpen (K := K) i).le
  exact iInf_le_of_le ((Proj.basicOpen (homogeneousSubmodule σ K) (X i) : Set _))
    (iInf_le_of_le (Proj.basicOpen (homogeneousSubmodule σ K) (X i)).2 (iInf_le _ hi))

/-- Projective space has dimension at least one less than the number of variables: a chart is a
subspace of it. -/
theorem le_topologicalKrullDim (K : Type u) [Field K] {σ : Type v} [Finite σ] (i : σ) :
    ((Nat.card σ - 1 : ℕ) : WithBot ℕ∞)
      ≤ topologicalKrullDim (Proj (homogeneousSubmodule σ K)) := by
  rw [← topologicalKrullDim_basicOpen (K := K) i]
  exact topologicalKrullDim_subspace_le (Proj (homogeneousSubmodule σ K))
    ((Proj.basicOpen (homogeneousSubmodule σ K) (X i) : Set (Proj (homogeneousSubmodule σ K))))

/-- **The dimension of projective space over a field is one less than the number of
variables.** -/
theorem topologicalKrullDim_proj (K : Type u) [Field K] (σ : Type v) [Finite σ] [Nonempty σ] :
    topologicalKrullDim (Proj (homogeneousSubmodule σ K))
      = ((Nat.card σ - 1 : ℕ) : WithBot ℕ∞) :=
  le_antisymm (topologicalKrullDim_le K σ) (le_topologicalKrullDim K (Classical.arbitrary σ))

/-! ### Equidimensionality -/

/-- Each standard chart of projective space over a field is irreducible: it is the spectrum of a
polynomial algebra over the field. -/
instance irreducibleSpace_basicOpen (i : σ) :
    IrreducibleSpace ((Proj.basicOpen (homogeneousSubmodule σ K) (X i) :
      Set (Proj (homogeneousSubmodule σ K)))) :=
  have : Nonempty ((Proj.basicOpen (homogeneousSubmodule σ K) (X i) :
      Set (Proj (homogeneousSubmodule σ K)))) :=
    Nonempty.map (chartHomeo (K := K) i).symm inferInstance
  (chartHomeo (K := K) i).isOpenEmbedding.irreducibleSpace

omit [Finite σ] in
/-- **An irreducible component of projective space contains every standard chart it meets.** The
chart is irreducible, so it is its own unique irreducible component, and restriction to an open
set carries irreducible components to irreducible components. -/
theorem basicOpen_subset_of_mem_irreducibleComponents
    {Z : Set (Proj (homogeneousSubmodule σ K))}
    (hZ : Z ∈ irreducibleComponents (Proj (homogeneousSubmodule σ K))) (i : σ)
    (hi : (Z ∩ (Proj.basicOpen (homogeneousSubmodule σ K) (X i) :
      Set (Proj (homogeneousSubmodule σ K)))).Nonempty) :
    (Proj.basicOpen (homogeneousSubmodule σ K) (X i) :
      Set (Proj (homogeneousSubmodule σ K))) ⊆ Z := by
  have hemb : Topology.IsOpenEmbedding
      (Subtype.val : ((Proj.basicOpen (homogeneousSubmodule σ K) (X i) :
        Set (Proj (homogeneousSubmodule σ K)))) → Proj (homogeneousSubmodule σ K)) :=
    (Proj.basicOpen (homogeneousSubmodule σ K) (X i)).2.isOpenEmbedding_subtypeVal
  have hpre := preimage_mem_irreducibleComponents hZ hemb (by rwa [Subtype.range_val])
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hpre
  intro y hy
  have hmem : (⟨y, hy⟩ : ((Proj.basicOpen (homogeneousSubmodule σ K) (X i) :
      Set (Proj (homogeneousSubmodule σ K))))) ∈ Subtype.val ⁻¹' Z := by
    rw [hpre]; trivial
  exact hmem

/-- **Projective space over a field is equidimensional.** Every irreducible component contains a
standard chart, so its dimension is at least that of a chart; and it is a subspace of the whole
space, so its dimension is at most that of the whole space. The two bounds coincide. -/
theorem equidimensional_proj (K : Type u) [Field K] (σ : Type v) [Finite σ] :
    TopologicalSpace.Equidimensional (Proj (homogeneousSubmodule σ K)) := by
  have key : ∀ Z ∈ irreducibleComponents (Proj (homogeneousSubmodule σ K)),
      topologicalKrullDim Z = ((Nat.card σ - 1 : ℕ) : WithBot ℕ∞) := by
    intro Z hZ
    obtain ⟨x, hx⟩ := hZ.1.nonempty
    obtain ⟨i, hi⟩ := exists_mem_basicOpen_X (R := K) x
    have hsub := basicOpen_subset_of_mem_irreducibleComponents hZ i ⟨x, hx, hi⟩
    refine le_antisymm
      (le_trans (topologicalKrullDim_subspace_le _ Z) (topologicalKrullDim_le K σ)) ?_
    rw [← topologicalKrullDim_basicOpen (K := K) i]
    exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
  intro Z hZ W hW
  rw [key Z hZ, key W hW]

/-! ### Projective space on `Fin r` variables -/

/-- **The dimension of `ℙ^{r-1}` over a field is `r - 1`.** -/
theorem topologicalKrullDim_proj_fin (K : Type u) [Field K] {r : ℕ} (hr : 0 < r) :
    topologicalKrullDim (Proj (homogeneousSubmodule (Fin r) K))
      = ((r - 1 : ℕ) : WithBot ℕ∞) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  rw [topologicalKrullDim_proj, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **`ℙ^{r-1}` over a field is equidimensional.** -/
theorem equidimensional_proj_fin (K : Type u) [Field K] (r : ℕ) :
    TopologicalSpace.Equidimensional (Proj (homogeneousSubmodule (Fin r) K)) :=
  equidimensional_proj K (Fin r)

/-- **`ℙ^{r-1}` over a field is equidimensional of dimension `r - 1`**: the two conditions that
`AlgebraicGeometry.RelativeDimension` asks of a nonempty fibre. -/
theorem equidimensional_and_topologicalKrullDim_proj_fin (K : Type u) [Field K] {r : ℕ}
    (hr : 0 < r) :
    TopologicalSpace.Equidimensional (Proj (homogeneousSubmodule (Fin r) K)) ∧
      topologicalKrullDim (Proj (homogeneousSubmodule (Fin r) K))
        = ((r - 1 : ℕ) : WithBot ℕ∞) :=
  ⟨equidimensional_proj_fin K r, topologicalKrullDim_proj_fin K hr⟩

end Stacks.ProjectiveSpace

end
