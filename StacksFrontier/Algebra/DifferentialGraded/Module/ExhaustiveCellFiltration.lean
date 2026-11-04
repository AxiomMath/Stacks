module

public import StacksFrontier.Algebra.DifferentialGraded.Module.GradedCellFiltration
public import StacksFrontier.Algebra.DifferentialGraded.Module.HasShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyExtension

/-!
# Differential graded modules with an unbounded triangular cell decomposition

Let `(A, d)` be a differential graded algebra and let `M` be a right differential graded
`A`-module whose underlying *graded* right `A`-module is a direct sum `⨁_{m ∈ ℕ} L_m` of
differential graded `A`-modules `L_m`, in such a way that the differential of `M` is *lower
triangular* for that decomposition. If each `L_m` is orthogonal on the left to the acyclic
modules, then so is `M`.

This is `DifferentialGradedModule.GradedCellData` with the finiteness hypothesis removed: there
no longer has to be an index beyond which every coordinate vanishes. Nothing is lost, because a
coordinate family is an element of a direct sum and therefore has finite support: the stages
`F_k = {x : the coordinates of x in degrees ≥ k vanish}` still exhaust `M`, only not by a single
one of them. The conclusion is therefore the same, drawn from
`DifferentialGradedModule.leftOrthogonal_acyclic_of_admissibleFiltration` — the telescope
argument of Tag 09KL in its homotopy-theoretic form — instead of from orthogonality of one
stage.

Removing the bound is what a divided-power variable forces. A cell decomposition of a
differential graded algebra such as `R⟨x, z, u⟩` over a Koszul subalgebra has one cell for each
divided-power monomial `u⁽ᵐ⁾`, and the differential `d u⁽ᵐ⁾ = (z - f^{N-t} x) u⁽ᵐ⁻¹⁾` takes the
`m`-th cell strictly into the `(m-1)`-st, so the cells form an infinite strictly descending
chain and no finite decomposition into cells with diagonal differential exists.

## Main definitions

* `DifferentialGradedModule.ExhaustiveCellData`: the data of such a cell decomposition — the
  pieces `L_m`, their orthogonality, the coordinate isomorphism, its compatibility with the
  action and the grading, and the two triangularity properties of the differential.
* `DifferentialGradedModule.ExhaustiveCellData.stage`: the differential graded submodule `F_k`.
* `DifferentialGradedModule.ExhaustiveCellData.layerHom`: the `k`-th coordinate, as a
  homomorphism `F_{k+1} ⟶ L_k`.
* `DifferentialGradedModule.exhaustiveCellDataOfCellCoords`: the same data from coordinates
  valued in direct sums of shifts of the algebra.

## Main results

* `DifferentialGradedModule.exists_forall_apply_eq_zero`: an element of a direct sum indexed by
  `ℕ` has a bound beyond which its coordinates vanish. This is what replaces the bound of
  `DifferentialGradedModule.GradedCellData`.
* `DifferentialGradedModule.leftOrthogonal_acyclic_shift`: a shift of a module orthogonal on the
  left to the acyclic modules is again one, which is what supplies the orthogonality of the
  graded pieces when they are shifts of one coefficient module.
* `DifferentialGradedModule.ExhaustiveCellData.isAdmissibleShortExact_stageIncl_layerHom`: each
  step of the filtration is an admissible short exact sequence `F_k ⟶ F_{k+1} ⟶ L_k`.
* `DifferentialGradedModule.ExhaustiveCellData.exists_mem_carrier`: the filtration exhausts `M`.
* `DifferentialGradedModule.leftOrthogonal_acyclic_of_exhaustiveCellData`: a module with such a
  cell decomposition is orthogonal on the left to the acyclic modules.
* `DifferentialGradedModule.leftOrthogonal_acyclic_of_exhaustiveCellCoords`: the same conclusion
  from coordinates valued in direct sums of shifts of the algebra, which is the form in which a
  module with a graded basis presents them.

## Implementation notes

The stages, their inclusions, the coordinate truncations and the graded pieces are built exactly
as for `DifferentialGradedModule.GradedCellData`; only the final assembly differs. They are
rebuilt here rather than shared, because the bound is a field of that structure and no module
with infinitely many nonzero coordinates satisfies it, so its stage machinery cannot be
instantiated at the data below.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules all live in a single universe `u`.

## References

* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT), admissible short exact
  sequences.
* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), property (P), the
  filtration whose shape this reproduces.
* [Stacks Project, Tag 09KL](https://stacks.math.columbia.edu/tag/09KL), the telescope.
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), orthogonality of the
  modules with property (P) to the acyclic ones.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- **An element of a direct sum indexed by `ℕ` has a bound beyond which its coordinates
vanish.** This is the finiteness that replaces the bound of
`DifferentialGradedModule.GradedCellData`: it is a property of every element rather than of the
decomposition, so it is available for free. -/
theorem exists_forall_apply_eq_zero {β : ℕ → Type u} [∀ m, AddCommGroup (β m)]
    (y : ⨁ (m : ℕ), β m) : ∃ k : ℕ, ∀ m : ℕ, k ≤ m → y m = 0 := by
  classical
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, fun m _ => DirectSum.zero_apply m⟩
  | of j b => exact ⟨j + 1, fun m hm => DirectSum.of_eq_of_ne _ _ _ (by omega)⟩
  | add y z hy hz =>
      obtain ⟨k, hk⟩ := hy
      obtain ⟨l, hl⟩ := hz
      refine ⟨max k l, fun m hm => ?_⟩
      rw [DirectSum.add_apply, hk m ((le_max_left k l).trans hm),
        hl m ((le_max_right k l).trans hm), add_zero]

/-- **A shift of a module orthogonal on the left to the acyclic modules is again one.** The
graded pieces of an unbounded cell decomposition coming from a divided-power variable are shifts
of one module — the `m`-th piece is the coefficient module placed in the degree of `u⁽ᵐ⁾` — so
this is what supplies their orthogonality. The left orthogonal of the acyclic objects is stable
under the shift of the homotopy category, and the shift of a differential graded module
represents the shift of its image there. -/
theorem leftOrthogonal_acyclic_shift {M : DifferentialGradedModule.{u, u, u} A} (k : ℤ)
    (h : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M)) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (shift M k)) := by
  have hshift : (((toHomotopyCategory A).obj M)⟦k⟧) =
      (toHomotopyCategory A).obj (shift M k) :=
    CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ M k
  rw [← hshift]
  exact ObjectProperty.le_shift (acyclic' A).leftOrthogonal k _ h

namespace ExhaustiveCellData

variable {M : DifferentialGradedModule.{u, u, u} A} (D : ExhaustiveCellData M)

/-- **The filtration exhausts `M`**: the coordinates of any one element vanish from some index
on, so that element lies in the corresponding stage. -/
theorem exists_mem_carrier (x : M.M) : ∃ k : ℕ, x ∈ D.carrier (k + 1) := by
  obtain ⟨k, hk⟩ := exists_forall_apply_eq_zero (D.coords x)
  exact ⟨k, fun m hm => hk m (by omega)⟩

end ExhaustiveCellData

/-- **A differential graded module with an unbounded triangular cell decomposition is orthogonal
on the left to the acyclic modules.** The stages of the filtration cut out by the vanishing of
the coordinates in high degrees are differential graded submodules, their inclusions are
admissible monomorphisms with the coordinate truncations as graded retractions, and the
successive quotients are the graded pieces; the filtration exhausts `M` because a coordinate
family has finite support, so the telescope argument of
`DifferentialGradedModule.leftOrthogonal_acyclic_of_admissibleFiltration` applies. -/
theorem leftOrthogonal_acyclic_of_exhaustiveCellData {M : DifferentialGradedModule.{u, u, u} A}
    (D : ExhaustiveCellData M) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M) := by
  refine leftOrthogonal_acyclic_of_admissibleFiltration
    (fun i => (D.stage (i + 1)).obj) (fun i => D.layer (i + 1))
    (fun i => (D.stage (i + 1)).ι) (fun i => D.stageIncl (i + 1))
    (fun i => D.layerHom (i + 1))
    (fun i => GradedSub.ι_injective (D.stage (i + 1)))
    (fun i x => D.val_stageIncl (i + 1) x)
    (fun i => D.isAdmissibleMono_stageIncl (i + 1))
    (fun i => D.layerHom_surjective (i + 1))
    (fun i => D.layerHom_ker (i + 1))
    (fun x => ?_)
    (leftOrthogonal_acyclic_of_iso A D.stageOneIso.symm (D.layer_leftOrthogonal 0))
    (fun i => D.layer_leftOrthogonal (i + 1))
  obtain ⟨k, hk⟩ := D.exists_mem_carrier x
  exact ⟨k, D.ofMem (k + 1) x hk, rfl⟩

/-! ### Cells given by direct sums of shifts of the algebra -/

/-- **An unbounded triangular cell decomposition with coordinates in direct sums of shifts of the
algebra.** This is `DifferentialGradedModule.gradedCellDataOfCellCoords` with the finiteness
hypothesis removed: the `m`-th coordinate is a direct sum of copies of the algebra, one for each
cell of index `m`, shifted by `sh m i`, and the hypotheses mention only the grading and the
differential of the algebra itself. -/
def exhaustiveCellDataOfCellCoords {M : DifferentialGradedModule.{u, u, u} A} {I : ℕ → Type u}
    [∀ m, DecidableEq (I m)] (sh : ∀ m, I m → ℤ)
    (coords : M.M ≃ₗ[R] ⨁ (m : ℕ), (⨁ (_ : I m), A.A))
    (coords_smul : ∀ (a : A.A) (x : M.M) (m : ℕ),
      (coords (MulOpposite.op a • x)) m = MulOpposite.op a • (coords x) m)
    (mem_grading_iff : ∀ (n : ℤ) (x : M.M),
      x ∈ M.grading n ↔ ∀ (m : ℕ) (i : I m), ((coords x) m) i ∈ A.grading (n + sh m i))
    (d_coords_eq_zero : ∀ (k : ℕ) (x : M.M), (∀ m : ℕ, k ≤ m → (coords x) m = 0) →
      ∀ m : ℕ, k ≤ m → (coords (M.d x)) m = 0)
    (d_coords : ∀ (k : ℕ) (x : M.M), (∀ m : ℕ, k + 1 ≤ m → (coords x) m = 0) →
      ∀ i : I k, ((coords (M.d x)) k) i =
        ((-1 : ℤ) ^ (sh k i).natAbs) • A.d (((coords x) k) i)) :
    ExhaustiveCellData M where
  layer m := directSumShifts A (sh m)
  layer_leftOrthogonal m := leftOrthogonal_acyclic_directSumShifts A (sh m)
  coords := coords
  coords_smul := coords_smul
  mem_grading_iff n x := (mem_grading_iff n x).trans
    (forall_congr' fun m => (mem_directSumShifts_grading (sh m) n ((coords x) m)).symm)
  d_coords_eq_zero := d_coords_eq_zero
  d_coords k x hx :=
    DirectSum.ext fun i => ((d_coords k x hx) i).trans
      (directSumShifts_d_apply (sh k) ((coords x) k) i).symm

/-- **A differential graded module with an unbounded triangular cell decomposition whose graded
pieces are direct sums of shifts of the algebra is orthogonal on the left to the acyclic
modules.** This is `DifferentialGradedModule.leftOrthogonal_acyclic_of_exhaustiveCellData` with
the graded pieces taken in the form a graded basis provides them, and it is the unbounded
companion of `DifferentialGradedModule.leftOrthogonal_acyclic_of_cellCoords`. -/
theorem leftOrthogonal_acyclic_of_exhaustiveCellCoords
    {M : DifferentialGradedModule.{u, u, u} A} {I : ℕ → Type u} (sh : ∀ m, I m → ℤ)
    (coords : M.M ≃ₗ[R] ⨁ (m : ℕ), (⨁ (_ : I m), A.A))
    (coords_smul : ∀ (a : A.A) (x : M.M) (m : ℕ),
      (coords (MulOpposite.op a • x)) m = MulOpposite.op a • (coords x) m)
    (mem_grading_iff : ∀ (n : ℤ) (x : M.M),
      x ∈ M.grading n ↔ ∀ (m : ℕ) (i : I m), ((coords x) m) i ∈ A.grading (n + sh m i))
    (d_coords_eq_zero : ∀ (k : ℕ) (x : M.M), (∀ m : ℕ, k ≤ m → (coords x) m = 0) →
      ∀ m : ℕ, k ≤ m → (coords (M.d x)) m = 0)
    (d_coords : ∀ (k : ℕ) (x : M.M), (∀ m : ℕ, k + 1 ≤ m → (coords x) m = 0) →
      ∀ i : I k, ((coords (M.d x)) k) i =
        ((-1 : ℤ) ^ (sh k i).natAbs) • A.d (((coords x) k) i)) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M) := by
  classical
  exact leftOrthogonal_acyclic_of_exhaustiveCellData
    (exhaustiveCellDataOfCellCoords sh coords coords_smul mem_grading_iff
      d_coords_eq_zero d_coords)

end DifferentialGradedModule

end
