module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantCoefficientTrace
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianDimension

/-!
# A class of maximal order in `H¹(C, ℤ/ℓ^j)` for a curve of positive genus

Let `C` be a smooth proper curve of genus `g ≥ 1` over an algebraically closed field `k` and
`ℓ` invertible in `k`. Then `H¹(C, ℤ/ℓ^j) ≅ H¹(C, μ_{ℓ^j}) ≅ Pic(C)[ℓ^j] = Pic⁰(C)[ℓ^j] ≅
J[ℓ^j] ≅ (ℤ/ℓ^j)^{2g}` (Kummer theory and the jacobian `J`, of dimension `g`), so it contains a
class whose order is exactly `ℓ^j`.

## Main results

* `Stacks.EtaleCohomology.exists_sheafH_one_etaleConstantSheaf_dvd_of_nsmul_eq_zero` — the class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Kummer
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]

/-- **`H¹(C, ℤ/ℓ^j)` has a class of order `ℓ^j`** for a smooth proper curve of positive genus over
an algebraically closed field in which `ℓ` is invertible. -/
theorem exists_sheafH_one_etaleConstantSheaf_dvd_of_nsmul_eq_zero (hg : 1 ≤ genus f) (ℓ j : ℕ)
    [NeZero ℓ] (hℓ : IsUnit (ℓ : k)) :
    ∃ z : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod (ℓ ^ j))) 1,
      ∀ m : ℕ, m • z = 0 → ℓ ^ j ∣ m := by
  have hn : IsUnit ((ℓ ^ j : ℕ) : k) := by exact_mod_cast hℓ.pow j
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
  have hn0 := ne_zero_of_isUnit_natCast hn
  have hdim : topologicalKrullDim C ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  have hX := isUnit_natCast_globalSections C (ℓ ^ j) f hn
  have hsurj := surjective_sheafH_map_powMap_zero.{u + 1, u, 0} C (n := ℓ ^ j)
    (exists_pow_eq_globalUnit C (ℓ ^ j) f (Nat.pos_of_ne_zero hn0))
  obtain ⟨J, _, _, E, hJ⟩ :=
    Stacks.Zeta.exists_jacobian_data_abelianVarietyDimension_eq_genus f hdim
  let e := (Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isUnit k J (ℓ ^ j) hn).some
  let Φ := (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 1).trans
    ((h1RootsOfUnityAddEquivPicardTorsion.{u + 1, 0, u} C (ℓ ^ j) hn0 hX hsurj).trans
      ((Stacks.AbelianGroup.torsionByNatCastPowEquiv _ ℓ j).trans
        ((AlgebraicGeometry.CurveGraph.picardDegreeZeroTorsionEquiv f hdim ℓ j).symm.trans
          ((Stacks.AbelianGroup.torsionAddEquiv E _).symm.trans e))))
  let i₀ : Fin (2 * Stacks.Groupoids.abelianVarietyDimension J) := ⟨0, by lia⟩
  refine ⟨Φ.symm (Pi.single i₀ 1), fun m hm => ?_⟩
  have h1 := congrArg (fun y => Φ y i₀) hm
  simp only [map_nsmul, AddEquiv.apply_symm_apply, map_zero, Pi.smul_apply, Pi.single_eq_same,
    Pi.zero_apply, nsmul_eq_mul, mul_one] at h1
  exact (ZMod.natCast_eq_zero_iff _ _).1 h1

end Stacks.EtaleCohomology

end
