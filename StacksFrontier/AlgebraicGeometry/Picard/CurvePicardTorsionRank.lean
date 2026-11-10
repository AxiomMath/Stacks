module

public import StacksFrontier.AlgebraicGeometry.Picard.CurvePicardTorsionFree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Jacobian
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianDimension
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianPointGroup
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeComponentProper
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# The `n`-torsion of the Picard group of a smooth proper curve has rank `2g`

For a smooth proper curve `X` over an algebraically closed field `k`, of genus `g`, and `n`
invertible in `k`, `Pic⁰(X) = J(k)` for the Jacobian `J`, an abelian variety of dimension `g`
(the degree-zero component of the Picard scheme is smooth of relative dimension `g`), so
`Pic(X)[n] = Pic⁰(X)[n] ≅ (ℤ/n)^{2g}` by [Stacks, Tag 03RP] (7).
`Stacks.Picard.exists_torsionBy_addEquiv_pi_zmod` records only the existence of some rank; this
file pins the rank to `2g`.

## Main results

* `Stacks.Picard.exists_jacobian_data_of_genus`: a Jacobian of dimension `g`.
* `Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_genus`: `Pic(X)[n] ≅ (ℤ/n)^{2g}`.
* `Stacks.Picard.natCard_torsionBy_eq_pow_genus`: `#Pic(X)[n] = n^{2g}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Picard

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] [IsProper g]

/-- Alias of `Stacks.Zeta.exists_jacobian_data_abelianVarietyDimension_eq_genus`. -/
alias exists_jacobian_data_of_genus :=
  Stacks.Zeta.exists_jacobian_data_abelianVarietyDimension_eq_genus

/-- An additive equivalence preserves being killed by an integer. -/
private theorem zsmul_equiv_eq_zero_iff {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) {n : ℤ} {x : A} : n • e x = 0 ↔ n • x = 0 := by
  rw [← map_zsmul, AddEquiv.map_eq_zero_iff]

/-- **`Pic(X)[n] ≅ (ℤ/n)^{2g}`** for a smooth proper curve of genus `g` over an algebraically
closed field and `n` invertible in the field ([Stacks, Tag 03RP] (7) for the Jacobian). -/
theorem nonempty_torsionBy_addEquiv_pi_zmod_genus (n : ℕ) (hn : IsUnit (n : k)) :
    Nonempty (Submodule.torsionBy ℤ (ofScheme X) (n : ℤ) ≃+ (Fin (2 * genus g) → ZMod n)) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := g)).le
  obtain ⟨J, _, _, E, hdimJ⟩ := exists_jacobian_data_of_genus g hdim
  obtain ⟨eJ⟩ := Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isUnit k J n hn
  rw [hdimJ] at eJ
  let M := Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
  have hM : ∀ x : Submodule.torsionBy ℤ (ofScheme X) (n : ℤ), (n : ℤ) • M x.1 = 0 := fun x =>
    (zsmul_equiv_eq_zero_iff M).2 x.2
  have hdeg : ∀ x : Submodule.torsionBy ℤ (ofScheme X) (n : ℤ),
      M x.1 ∈ picardDegreeZero k g hdim := fun x =>
    mem_picardDegreeZero_of_nsmul_eq_zero k g hdim hn0 _ (by simpa using hM x)
  let F : Submodule.torsionBy ℤ (ofScheme X) (n : ℤ) ≃+
      AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) n :=
    { toFun := fun x => ⟨E.symm ⟨M x.1, hdeg x⟩, by
        change _ ∈ Submodule.torsionBy ℤ _ _
        rw [Submodule.mem_torsionBy_iff, zsmul_equiv_eq_zero_iff]
        exact Subtype.ext (hM x)⟩
      invFun := fun y => ⟨M.symm (E y.1).1, by
        rw [Submodule.mem_torsionBy_iff, zsmul_equiv_eq_zero_iff]
        exact congrArg Subtype.val ((zsmul_equiv_eq_zero_iff E).2 y.2)⟩
      left_inv := fun x => by
        apply Subtype.ext
        change M.symm (E (E.symm _)).1 = x.1
        rw [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
      right_inv := fun y => by
        apply Subtype.ext
        change E.symm ⟨M (M.symm (E y.1).1), _⟩ = y.1
        simp only [AddEquiv.apply_symm_apply, Subtype.coe_eta, AddEquiv.symm_apply_apply]
      map_add' := fun x y => by
        apply Subtype.ext
        change E.symm ⟨M (x.1 + y.1), _⟩ = E.symm ⟨M x.1, _⟩ + E.symm ⟨M y.1, _⟩
        rw [← map_add]
        congr 1
        exact Subtype.ext (map_add M x.1 y.1) }
  exact ⟨F.trans eJ⟩

/-- **`#Pic(X)[n] = n^{2g}`** for a smooth proper curve of genus `g` over an algebraically closed
field and `n` invertible in the field. -/
theorem natCard_torsionBy_eq_pow_genus (n : ℕ) (hn : IsUnit (n : k)) :
    Nat.card (AddSubgroup.torsionBy (ofScheme X) (n : ℤ)) = n ^ (2 * genus g) := by
  obtain ⟨e⟩ := nonempty_torsionBy_addEquiv_pi_zmod_genus g n hn
  have : NeZero n := ⟨fun h => by simp [h] at hn⟩
  have h : Nat.card (AddSubgroup.torsionBy (ofScheme X) (n : ℤ)) =
      Nat.card (Submodule.torsionBy ℤ (ofScheme X) (n : ℤ)) := rfl
  rw [h, Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end Stacks.Picard

end
