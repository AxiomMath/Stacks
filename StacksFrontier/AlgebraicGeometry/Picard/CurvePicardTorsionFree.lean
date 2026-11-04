module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeZeroDivisibility
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PicardDegreeZeroDivisible

/-!
# The `n`-torsion of the Picard group of a smooth proper curve is free over `ℤ/n`

For a smooth proper curve `X` over an algebraically closed field `k` and `n` invertible in `k`,
`Pic(X)[n] = Pic⁰(X)[n]` is the `n`-torsion of the group of rational points of the Jacobian, an
abelian variety, hence `Pic(X)[n] ≅ (ℤ/n)^{2g}` ([Stacks, Tag 03RP] (7)). Only the existence of
some such isomorphism is recorded here.

## Main results

* `Stacks.Picard.exists_torsionBy_addEquiv_pi_zmod`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Picard

/-- **`Pic(X)[n]` is a free `ℤ/n`-module of finite rank** for a smooth proper curve over an
algebraically closed field and `n` invertible in the field. -/
theorem exists_torsionBy_addEquiv_pi_zmod {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g] [IsProper g] (n : ℕ) (hn : IsUnit (n : k)) :
    ∃ r : ℕ, Nonempty (Submodule.torsionBy ℤ (ofScheme X) (n : ℤ) ≃+ (Fin r → ZMod n)) := by
  have hdim : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨J, _, _, E, -⟩ := exists_jacobian_data g k hdim
  obtain ⟨eJ⟩ := Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isUnit k J n hn
  let M := Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
  have hdeg : ∀ x : Submodule.torsionBy ℤ (ofScheme X) (n : ℤ),
      M x.1 ∈ picardDegreeZero k g hdim := fun x =>
    mem_picardDegreeZero_of_nsmul_eq_zero k g hdim hn0 _ (by
      rw [← map_nsmul, ← natCast_zsmul, (Submodule.mem_torsionBy_iff _ _).1 x.2, map_zero])
  let F : Submodule.torsionBy ℤ (ofScheme X) (n : ℤ) ≃+
      AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) n :=
    { toFun := fun x => ⟨E.symm ⟨M x.1, hdeg x⟩, by
        show _ ∈ Submodule.torsionBy ℤ _ _
        rw [Submodule.mem_torsionBy_iff, ← map_zsmul, AddEquiv.map_eq_zero_iff]
        apply Subtype.ext
        show (n : ℤ) • M x.1 = 0
        rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).1 x.2, map_zero]⟩
      invFun := fun y => ⟨M.symm (E y.1).1, by
        rw [Submodule.mem_torsionBy_iff, ← map_zsmul, AddEquiv.map_eq_zero_iff]
        show ((n : ℤ) • E y.1).1 = 0
        rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).1 y.2, map_zero]
        rfl⟩
      left_inv := fun x => by
        apply Subtype.ext
        show M.symm (E (E.symm _)).1 = x.1
        rw [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
      right_inv := fun y => by
        apply Subtype.ext
        show E.symm ⟨M (M.symm (E y.1).1), _⟩ = y.1
        simp only [AddEquiv.apply_symm_apply, Subtype.coe_eta, AddEquiv.symm_apply_apply]
      map_add' := fun x y => by
        apply Subtype.ext
        show E.symm ⟨M (x.1 + y.1), _⟩ = E.symm ⟨M x.1, _⟩ + E.symm ⟨M y.1, _⟩
        rw [← map_add]
        congr 1
        exact Subtype.ext (map_add M x.1 y.1) }
  exact ⟨_, ⟨F.trans eJ⟩⟩

end Stacks.Picard

end
