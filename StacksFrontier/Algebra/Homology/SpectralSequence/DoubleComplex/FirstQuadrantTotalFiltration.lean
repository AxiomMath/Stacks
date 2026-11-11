module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.Filtration

/-!
# The filtration of a first-quadrant double complex by the first coordinate

Let `K^{•,•}` be a double complex with `K^{i,j} = 0` whenever `i < 0` or `j < 0`. The filtration
`F_I^p Tot^n = ⨁_{i + j = n, i ≥ p} K^{i,j}` of its total complex by the first coordinate is then
*first quadrant*: its zeroth step is the whole of `Tot^n`, and its `p`-th step vanishes in every
total degree `n < p`. These are the two hypotheses `htop` and `hbot` under which
`CochainComplex.Filtered.firstQuadrantAbutmentOfFiltered` makes the spectral sequence of a
filtered complex abut to its cohomology. The counterparts for the filtration by the second
coordinate are `HomologicalComplex₂.isIso_totalFiltration₂_ι_f` and
`HomologicalComplex₂.isZero_totalFiltration₂_obj_X`.

## Main results

* `HomologicalComplex₂.isIso_totalFiltration₁_ι_f`: the zeroth step of `totalFiltration₁` is
  everything when `K^{i,j} = 0` for `i < 0`.
* `HomologicalComplex₂.isZero_totalFiltration₁_obj_X`: the `p`-th step of `totalFiltration₁`
  vanishes in total degrees `n < p` when `K^{i,j} = 0` for `j < 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace HomologicalComplex₂

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

/-- The projector onto the summands `K^{i,j}` with `p ≤ i` is the identity as soon as the
summands it omits are zero. -/
lemma totalProjector_fst_eq_id_of_isZero (p : ℤ)
    (hz : ∀ i j : ℤ, i < p → IsZero ((K.X i).X j)) (n : ℤ) :
    K.totalProjector (fun i (_ : ℤ) => p ≤ i) n = 𝟙 _ := by
  refine total.hom_ext _ fun i j hij => ?_
  rw [ι_totalProjector, Category.comp_id]
  split_ifs with h
  · rfl
  · exact ((hz i j (by omega)).eq_of_src _ _).symm

/-- The projector onto the summands `K^{i,j}` with `p ≤ i`, in a total degree `n < p`, is zero as
soon as the double complex vanishes in negative second degree: a surviving summand has
`j = n - i ≤ n - p < 0`. -/
lemma totalProjector_fst_eq_zero_of_isZero (hz : ∀ i j : ℤ, j < 0 → IsZero ((K.X i).X j))
    (p n : ℤ) (hnp : n < p) :
    K.totalProjector (fun i (_ : ℤ) => p ≤ i) n = 0 := by
  refine total.hom_ext _ fun i j hij => ?_
  have hij' : i + j = n := hij
  rw [ι_totalProjector, comp_zero]
  split_ifs with h
  · exact (hz i j (by omega)).eq_of_src _ _
  · rfl

/-- **`htop` for the first total filtration.** If the double complex vanishes in negative first
degree then the zeroth step `F_I^0 Tot^n = ⨁_{i + j = n, i ≥ 0} K^{i,j}` is the whole of
`Tot^n`. -/
lemma isIso_totalFiltration₁_ι_f (hz : ∀ i j : ℤ, i < 0 → IsZero ((K.X i).X j)) (n : ℤ) :
    IsIso ((K.totalFiltration₁.filtration.ι.app (op (0 : ℤ))).f n) := by
  change IsIso (imageSubobject (K.totalProjector (fun i (_ : ℤ) => (0 : ℤ) ≤ i) n)).arrow
  have : Epi (K.totalProjector (fun i (_ : ℤ) => (0 : ℤ) ≤ i) n) := by
    rw [totalProjector_fst_eq_id_of_isZero K 0 hz n]; infer_instance
  have := epi_of_epi_fac (imageSubobject_arrow_comp
    (K.totalProjector (fun i (_ : ℤ) => (0 : ℤ) ≤ i) n))
  exact isIso_of_mono_of_epi _

/-- **`hbot` for the first total filtration.** If the double complex vanishes in negative second
degree then the step `F_I^p Tot^n` is zero in every total degree `n < p`. -/
lemma isZero_totalFiltration₁_obj_X (hz : ∀ i j : ℤ, j < 0 → IsZero ((K.X i).X j)) (p n : ℤ)
    (hnp : n < p) :
    IsZero ((K.totalFiltration₁.filtration.obj (op p)).X n) := by
  change IsZero ((imageSubobject (K.totalProjector (fun i (_ : ℤ) => p ≤ i) n) : C))
  rw [totalProjector_fst_eq_zero_of_isZero K hz p n hnp, imageSubobject_zero]
  exact IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero

end HomologicalComplex₂

end
