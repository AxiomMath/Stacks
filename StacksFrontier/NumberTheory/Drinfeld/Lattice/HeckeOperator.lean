module

public import StacksFrontier.NumberTheory.Drinfeld.Lattice.Adelic
public import StacksFrontier.NumberTheory.Drinfeld.Lattice.Hecke

/-!
# The Hecke operator `T_v` as a sum over sublattices

Let `K` be a function field over a finite field, `v` a place of `K`, and identify functions on
`GL₂(O) \ GL₂(A)` with functions on adelic lattices through `x ↦ x⁻¹ (O_v^2)_v`. We show that the
`q_v + 1` matrices `g_j` of the base's explicit formula `T_v f (x) = ∑_j f (g_j x)` for the Hecke
operator (`Stacks.Adeles.IsHeckeDataAt`) send the lattice `Λ = x⁻¹ (O_w^2)_w` to exactly its
*Hecke neighbours at `v`*: the adelic lattices `Λ'` with `Λ'_w = Λ_w` for `w ≠ v` and
`π Λ_v ⊆ Λ'_v ⊆ Λ_v` of index `q_v`, each once. Hence
`T_v f (x) = ∑_{Λ'} F (Λ')`, the sum over the Hecke neighbours `Λ'` of `Λ` at `v`, where
`f (x) = F (x⁻¹ (O_w^2)_w)`. This is the geometric meaning of `T_v`: modifications at `v` of
index `q_v`.

## Main definitions

* `Stacks.Drinfeld.Lattice.AdelicLattice.IsHeckeNeighbour` — `Λ'` agrees with `Λ` away from `v`
  and is a Hecke sublattice of `Λ` at `v`.

## Main results

* `Stacks.Drinfeld.Lattice.AdelicLattice.bijective_heckeFamily_inv_smul` — `j ↦ (g_j x)⁻¹ O^2`
  is a bijection onto the Hecke neighbours of `x⁻¹ O^2` at `v`.
* `Stacks.Drinfeld.Lattice.AdelicLattice.heckeOperator_eq_finsum` — `T_v f (x)` is the sum of
  `F` over the Hecke neighbours of `x⁻¹ O^2` at `v`.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Drinfeld.Lattice

open Stacks.Adeles Stacks.Adeles.GlobalFunctionField

namespace AdelicLattice

variable {K : Type u} [Field K]

/-- `Λ'` is a Hecke neighbour of `Λ` at `v`: `Λ'_w = Λ_w` for `w ≠ v`, and `Λ'_v` is a Hecke
sublattice of `Λ_v` (`π Λ_v ⊆ Λ'_v ⊆ Λ_v` of index `q_v`). -/
public def IsHeckeNeighbour (v : Place K) (Λ Λ' : AdelicLattice K 2) : Prop :=
  (∀ w, w ≠ v → Λ'.lattice w = Λ.lattice w) ∧ IsHeckeSublattice (Λ.lattice v) (Λ'.lattice v)

variable (k : Type u) [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K]

variable {v : Place K} {q : ℕ} {π : v.integers} {lam : Fin q → v.integers}
  {g₀ : GL (Fin 2) (AdeleRing K)} {g : Fin q → GL (Fin 2) (AdeleRing K)}

include k in
/-- The component at `v` of `g_j⁻¹` is `M_j`, and its other components are `1`. -/
public theorem glAt_heckeFamily_inv (hd : IsHeckeDataAt v π lam g₀ g) (j : Option (Fin q)) :
    glAt K 2 v (heckeFamily g₀ g j)⁻¹ =
        heckeLocalGL (coe_ne_zero_of_isUniformizer k hd.isUniformizer)
          (fun i => (lam i : v.completion)) j ∧
      ∀ w, w ≠ v → glAt K 2 w (heckeFamily g₀ g j)⁻¹ = 1 := by
  obtain ⟨h₁, h₂⟩ := localMat_heckeFamily hd j
  refine ⟨?_, fun w hw => ?_⟩
  · rw [map_inv, inv_eq_iff_eq_inv]
    exact Units.ext h₁
  · rw [map_inv, inv_eq_one]
    exact Units.ext (h₂ w hw)

include k in
/-- **The Hecke neighbours of `x⁻¹ O^2` at `v` are the `(g_j x)⁻¹ O^2`**: for the data `g_j` of
the Hecke operator `T_v`, the map `j ↦ (g_j x)⁻¹ (O_w^2)_w` is a bijection from the `q_v + 1`
indices onto the Hecke neighbours of `x⁻¹ (O_w^2)_w` at `v`. -/
public theorem bijective_heckeFamily_inv_smul (hd : IsHeckeDataAt v π lam g₀ g)
    (x : GL (Fin 2) (AdeleRing K)) :
    Function.Bijective fun j : Option (Fin q) =>
      (⟨(heckeFamily g₀ g j * x)⁻¹ • standard K 2, by
        obtain ⟨h₁, h₂⟩ := glAt_heckeFamily_inv k hd j
        refine ⟨fun w hw => ?_, ?_⟩
        · rw [_root_.mul_inv_rev, mul_smul, smul_lattice, smul_lattice, smul_lattice,
            standard_lattice, h₂ w hw, translate_one]
        · rw [_root_.mul_inv_rev, mul_smul, smul_lattice, smul_lattice, smul_lattice,
            standard_lattice, h₁]
          exact (isHeckeSublattice_translate_iff _).2
            (isHeckeSublattice_heckeSublattice k hd.isUniformizer hd.isResidueSystem j)⟩ :
        {Λ' : AdelicLattice K 2 // IsHeckeNeighbour v (x⁻¹ • standard K 2) Λ'}) := by
  have hloc := bijective_heckeSublattice_translate k hd.isUniformizer hd.isResidueSystem
    (glAt K 2 v x⁻¹)
  have hv : ∀ j, ((heckeFamily g₀ g j * x)⁻¹ • standard K 2).lattice v =
      translate (glAt K 2 v x⁻¹ * heckeLocalGL (coe_ne_zero_of_isUniformizer k hd.isUniformizer)
        (fun i => (lam i : v.completion)) j) (stdLattice v 2) := fun j => by
    rw [_root_.mul_inv_rev, mul_smul, smul_lattice, smul_lattice, standard_lattice,
      (glAt_heckeFamily_inv k hd j).1, ← translate_mul]
  refine ⟨fun j j' hjj' => hloc.1 (Subtype.ext ?_), fun Λ' => ?_⟩
  · have := congrArg (fun Λ : {Λ' : AdelicLattice K 2 //
      IsHeckeNeighbour v (x⁻¹ • standard K 2) Λ'} => Λ.1.lattice v) hjj'
    simpa only [hv] using this
  · obtain ⟨j, hj⟩ := hloc.2 ⟨Λ'.1.lattice v, by
      have := Λ'.2.2
      rwa [smul_lattice, standard_lattice] at this⟩
    refine ⟨j, Subtype.ext (AdelicLattice.ext (funext fun w => ?_))⟩
    by_cases hw : w = v
    · subst hw
      rw [hv]
      exact congrArg Subtype.val hj
    · show ((heckeFamily g₀ g j * x)⁻¹ • standard K 2).lattice w = Λ'.1.lattice w
      rw [Λ'.2.1 w hw, _root_.mul_inv_rev, mul_smul, smul_lattice, smul_lattice, smul_lattice,
        standard_lattice, (glAt_heckeFamily_inv k hd j).2 w hw, translate_one]

include k in
/-- **`T_v` sums over the Hecke neighbours**: writing a function on `GL₂(O) \ GL₂(A)` as
`f (x) = F (x⁻¹ (O_w^2)_w)`, the Hecke operator of the base's explicit formula is
`T_v f (x) = ∑_{Λ'} F (Λ')`, the sum over the Hecke neighbours `Λ'` of `x⁻¹ (O_w^2)_w` at `v`. -/
public theorem heckeOperator_eq_finsum {Λ : Type w} [AddCommMonoid Λ]
    (hd : IsHeckeDataAt v π lam g₀ g) (F : AdelicLattice K 2 → Λ) (x : GL (Fin 2) (AdeleRing K)) :
    heckeOperator g₀ g (fun y => F (y⁻¹ • standard K 2)) x =
      ∑ᶠ Λ' : {Λ' : AdelicLattice K 2 // IsHeckeNeighbour v (x⁻¹ • standard K 2) Λ'}, F Λ'.1 := by
  rw [heckeOperator_eq_sum, ← finsum_eq_sum_of_fintype]
  exact finsum_comp_equiv (Equiv.ofBijective _ (bijective_heckeFamily_inv_smul k hd x))
    (f := fun Λ' => F Λ'.1)

end AdelicLattice

end Stacks.Drinfeld.Lattice

end
