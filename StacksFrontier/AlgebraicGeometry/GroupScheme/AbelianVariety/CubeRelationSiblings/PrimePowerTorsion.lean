module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelationSiblings.ZPowFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.AssemblyCubeRelation

/-!
# The `p`-power torsion of an abelian variety in characteristic `p`

Part (8) of [Stacks, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP) in the spelling used by
the torsion of the Jacobian: the `p ^ m`-torsion is the `ℤ`-submodule
`Submodule.torsionBy ℤ (Additive (𝟙_ _ ⟶ A)) ((p : ℤ) ^ m)` of the group of rational points. It is
read off `Stacks.Groupoids.exists_torsionBy_char_pow_addEquiv`, which states part (8) for the
additive subgroup `AddSubgroup.torsionBy`, the same subset.

## Main results

* `AlgebraicGeometry.IsAbelianVariety.exists_rank_nonempty_torsionBy_prime_pow_addEquiv_pi_zmod`:
  there is an `f ≤ dim A` with `A(k)[p^m] ≅ (ℤ/p^m)^f` for every `m ≥ 1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.IsAbelianVariety

universe u

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]

/-- **The `p`-power torsion of an abelian variety in characteristic `p`.** Let `k` be an
algebraically closed field of characteristic `p > 0` and `A` an abelian variety over `k`. Then
there is an integer `0 ≤ f ≤ dim A` with `A(k)[p^m] ≅ (ℤ/p^mℤ)^f` for all `m ≥ 1`; this is part
(8) of [Stacks, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP). -/
theorem exists_rank_nonempty_torsionBy_prime_pow_addEquiv_pi_zmod
    [IsAlgClosed k] (p : ℕ) [CharP k p] (hp : 0 < p) :
    letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
    ∃ r : ℕ, r ≤ Stacks.Groupoids.abelianVarietyDimension A ∧ ∀ m : ℕ, 1 ≤ m →
      Nonempty (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A))
        ((p : ℤ) ^ m) ≃+ (Fin r → ZMod (p ^ m))) := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  obtain ⟨r, hr, h⟩ := Stacks.Groupoids.exists_torsionBy_char_pow_addEquiv k A p hp
  refine ⟨r, hr, fun m _ => ?_⟩
  obtain ⟨e⟩ := h m
  have hcast : ((p ^ m : ℕ) : ℤ) = (p : ℤ) ^ m := by push_cast; rfl
  rw [hcast] at e
  let e₀ : Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((p : ℤ) ^ m) ≃+
      AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((p : ℤ) ^ m) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact ⟨e₀.trans e⟩

end AlgebraicGeometry.IsAbelianVariety

end
