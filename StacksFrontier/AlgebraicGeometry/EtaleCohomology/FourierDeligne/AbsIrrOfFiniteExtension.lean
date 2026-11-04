module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.SpanLatticeBound
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Absolute irreducibility from irreducibility over the finite extensions

Let `M : A → M_ι(E)` be a family of matrices over a field `E`, closed under products and
containing `1` (e.g. the image of a representation). If over every finite extension `E'` of `E`
inside an algebraic closure `Ē` the only `M`-stable subspaces of `E'^ι` are `0` and `E'^ι`, then
over every extension field `K` of `E` the only `M`-stable subspaces of `K^ι` are `0` and `K^ι`
(`Stacks.EtaleCohomology.eq_bot_or_eq_top_of_forall_finiteDimensional`).

Indeed an `M`-stable subspace `W₀ ⊆ Ē^ι` is spanned by finitely many vectors, whose coordinates
generate a finite extension `E'` of `E`; the vectors of `E'^ι` lying in `W₀` form an `M`-stable
subspace containing these generators and is `0` or `E'^ι`, so `W₀` is `0` or `Ē^ι`. By Burnside's
theorem the `E`-span of the family is then `M_ι(E)`
(`Stacks.EtaleCohomology.span_range_eq_top_of_forall_mulVec_map_mem`), and a family spanning
`M_ι(E)` is irreducible over every extension
(`Stacks.EtaleCohomology.eq_bot_or_eq_top_of_span_range_eq_top`).

This is the reduction, in piece L6 of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), of
the absolute irreducibility of the representation `τ` to its irreducibility over the finite
extensions of its field of coefficients, which are the ones with a ring of integers and finite
residue rings, on which the level dichotomy of the Fourier transform acts.

## Main results

* `Stacks.EtaleCohomology.eq_bot_or_eq_top_of_forall_finiteDimensional`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {E ι A : Type*} [Field E] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The vectors of `E'^ι` lying in a subspace of `L^ι`**, for a tower `E ⊆ E' ⊆ L`: an
`E'`-subspace of `E'^ι`, stable under every matrix over `E` stabilizing the subspace. -/
theorem mulVec_map_mem_comap {L : Type*} [Field L] [Algebra E L] (E' : IntermediateField E L)
    (X : Matrix ι ι E) (W₀ : Submodule L (ι → L))
    (hX : ∀ v ∈ W₀, X.map (algebraMap E L) *ᵥ v ∈ W₀) (v : ι → E')
    (hv : (fun i => (v i : L)) ∈ W₀) :
    (fun i => ((X.map (algebraMap E E') *ᵥ v) i : L)) ∈ W₀ := by
  have h : (fun i => ((X.map (algebraMap E E') *ᵥ v) i : L)) =
      X.map (algebraMap E L) *ᵥ fun i => (v i : L) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, IntermediateField.coe_sum,
      IntermediateField.coe_mul]
    rfl
  rw [h]
  exact hX _ hv

omit [Fintype ι] [DecidableEq ι] in
/-- The `E'`-subspace of `E'^ι` of the vectors whose image in `L^ι` lies in `W₀`, for a tower
`E ⊆ E' ⊆ L`. -/
def intermediateFieldComap {L : Type*} [Field L] [Algebra E L] (E' : IntermediateField E L)
    (W₀ : Submodule L (ι → L)) : Submodule E' (ι → E') where
  carrier := {v | (fun i => (v i : L)) ∈ W₀}
  add_mem' {v w} hv hw := by
    change (fun i => ((v i : L) + (w i : L))) ∈ W₀
    exact W₀.add_mem hv hw
  zero_mem' := by
    change (fun _ => ((0 : E') : L)) ∈ W₀
    simp only [IntermediateField.coe_zero]
    exact W₀.zero_mem
  smul_mem' c v hv := by
    change (fun i => ((c : L) * (v i : L))) ∈ W₀
    exact W₀.smul_mem (c : L) hv

omit [Fintype ι] [DecidableEq ι] in
/-- A vector `v` of `E'^ι` lies in `intermediateFieldComap E' W₀` if and only if its image in
`L^ι` lies in `W₀`. -/
@[simp]
theorem mem_intermediateFieldComap {L : Type*} [Field L] [Algebra E L]
    (E' : IntermediateField E L) (W₀ : Submodule L (ι → L)) (v : ι → E') :
    v ∈ intermediateFieldComap E' W₀ ↔ (fun i => (v i : L)) ∈ W₀ :=
  Iff.rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A subspace of `L^ι` whose vectors with coordinates in an intermediate field `E'` are all of
`E'^ι` is all of `L^ι`. -/
theorem eq_top_of_intermediateFieldComap_eq_top [Finite ι] {L : Type*} [Field L] [Algebra E L]
    {E' : IntermediateField E L} {W₀ : Submodule L (ι → L)}
    (htop : intermediateFieldComap E' W₀ = ⊤) : W₀ = ⊤ := by
  classical
  cases nonempty_fintype ι
  rw [eq_top_iff]
  intro w _
  rw [pi_eq_sum_univ w]
  refine W₀.sum_mem fun i _ => W₀.smul_mem _ ?_
  have hi : (Pi.single i 1 : ι → E') ∈ intermediateFieldComap E' W₀ := by
    rw [htop]
    exact Submodule.mem_top
  have heq : (fun j => if i = j then (1 : L) else 0) =
      fun j => ((Pi.single i 1 : ι → E') j : L) := by
    funext j
    by_cases hj : i = j
    · subst hj
      simp
    · simp [Ne.symm hj, hj]
  rw [heq]
  exact hi

/-- **Absolute irreducibility from irreducibility over the finite extensions.** Let
`M : A → M_ι(E)` be closed under products and contain `1`. If for every intermediate field
`E ⊆ E' ⊆ Ē` of finite degree over `E` the only `M`-stable subspaces of `E'^ι` are `0` and `E'^ι`,
then for every field `K ⊇ E` the only `M`-stable subspaces of `K^ι` are `0` and `K^ι`. -/
theorem eq_bot_or_eq_top_of_forall_finiteDimensional (M : A → Matrix ι ι E)
    (hmul : ∀ a b, ∃ c, M a * M b = M c) (hone : ∃ a, M a = 1)
    (h : ∀ E' : IntermediateField E (AlgebraicClosure E), FiniteDimensional E E' →
      ∀ W : Submodule E' (ι → E'), (∀ a, ∀ v ∈ W, (M a).map (algebraMap E E') *ᵥ v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (K : Type*) [Field K] [Algebra E K] (W : Submodule K (ι → K))
    (hW : ∀ a, ∀ v ∈ W, (M a).map (algebraMap E K) *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  refine eq_bot_or_eq_top_of_span_range_eq_top M ?_ W hW
  refine span_range_eq_top_of_forall_mulVec_map_mem (K := AlgebraicClosure E) M hmul hone ?_
  intro W₀ hW₀
  obtain ⟨T, hT⟩ := IsNoetherian.noetherian W₀
  let S : Set (AlgebraicClosure E) :=
    Set.range fun p : {x // x ∈ T} × ι => (p.1 : ι → AlgebraicClosure E) p.2
  have : Finite S := Set.finite_range _ |>.to_subtype
  let E' : IntermediateField E (AlgebraicClosure E) := IntermediateField.adjoin E S
  have hfd : FiniteDimensional E E' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hlift : ∀ t ∈ T, ∃ v : ι → E', (fun i => (v i : AlgebraicClosure E)) = t := fun t ht =>
    ⟨fun i => ⟨t i, IntermediateField.subset_adjoin E S ⟨(⟨t, ht⟩, i), rfl⟩⟩, rfl⟩
  rcases h E' hfd (intermediateFieldComap E' W₀)
    (fun a v hv => mulVec_map_mem_comap E' (M a) W₀ (hW₀ a) v hv) with hbot | htop
  · left
    rw [← hT, Submodule.span_eq_bot]
    intro t ht
    obtain ⟨v, rfl⟩ := hlift t ht
    have hv : v ∈ intermediateFieldComap E' W₀ := by
      rw [mem_intermediateFieldComap, ← hT]
      exact Submodule.subset_span ht
    rw [hbot, Submodule.mem_bot] at hv
    subst hv
    funext i
    simp
  · exact Or.inr (eq_top_of_intermediateFieldComap_eq_top htop)

end Stacks.EtaleCohomology

end
