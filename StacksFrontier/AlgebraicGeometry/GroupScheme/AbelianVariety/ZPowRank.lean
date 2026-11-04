module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowPullbackSymmetric
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowTorsionCard
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.GenericRank
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.EndomorphismDegree
public import StacksFrontier.AlgebraicGeometry.TensorPowerProduct.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.FiniteOfAmplePullback
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FiniteSelfMap
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.Main
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.SeparablyClosedDivisiblePoints
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank of multiplication by `n` on an abelian variety

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `k` and let
`n` be invertible in `k`. Then `[n] : A ⟶ A` is finite locally free of degree `n ^ {2g}`
([Stacks, Tag 0BFG]) and `A(k)[n] ≅ (𝐙/n𝐙)^{2g}` (clause (7) of [Stacks, Tag 03RP]). More
generally, over any field, multiplication by a nonzero integer `d` is finite locally free of degree
`|d| ^ {2g}` once `A` carries an ample invertible module and satisfies the theorem of the cube.

## Main results

* `Stacks.Groupoids.isAmple_symmetrize`: `L ⊗ [-1]^*L` is ample when `L` is.
* `Stacks.Groupoids.isFinite_zpow_id_left_of_isAmple`: `[d]` is finite for every `d ≠ 0`, over any
  field.
* `Stacks.Groupoids.flat_zpow_id_left_of_isAmple`: `[d]` is flat for every `d ≠ 0`.
* `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_left_of_isAmple_of_ne_zero`: [Stacks, Tag
  0BFG] for `d ≠ 0` over any field: `[d]` is finite locally free of rank `|d| ^ {2 dim A}`.
* `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_left_of_isAmple`: `[n]` is finite locally
  free of rank `n ^ {2 dim A}`.
* `Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isAmple`: `A(k)[n] ≅ (𝐙/n𝐙)^{2 dim A}`.
* `Stacks.Groupoids.exists_isAmple_modules_of_isAbelianVariety`: an abelian variety carries an
  ample invertible module.
* `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_left_of_ne_zero`,
  `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_left_of_isUnit` and
  `Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isUnit_of_isCommMonObj`: the same statements
  over an algebraically closed field, with no ample module or theorem of the cube assumed.

## References

* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BFF](https://stacks.math.columbia.edu/tag/0BFF)
* [Stacks Project, Tag 0890](https://stacks.math.columbia.edu/tag/0890)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

open _root_.AlgebraicGeometry

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- The symmetrization `L ⊗ [-1]^*L` of an invertible module is invertible, in the sense of
`AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
theorem isInvertible_symmetrize_ag (L : A.left.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible A.left.toRingedSpace.presheaf
      (structureSheafRing A.left.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible A.left.toRingedSpace.presheaf
      (structureSheafRing A.left.toRingedSpace).property (symmetrize A L) :=
  (isInvertible_symmetrize A L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL)).toAlgebraicGeometry

/-- **The symmetrization `L ⊗ [-1]^*L` of an ample invertible module `L` is ample.** -/
theorem isAmple_symmetrize (L : A.left.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible A.left.toRingedSpace.presheaf
      (structureSheafRing A.left.toRingedSpace).property L]
    (hamp : Scheme.Modules.IsAmple A.left L) :
    letI := isInvertible_symmetrize_ag A L
    Scheme.Modules.IsAmple A.left (symmetrize A L) := by
  have hLs := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hM : AlgebraicGeometry.SheafOfModules.IsInvertible A.left.toRingedSpace.presheaf
      (structureSheafRing A.left.toRingedSpace).property
      ((Scheme.Modules.pullback (ι : A ⟶ A).left).obj L) :=
    (isInvertible_pullbackOver (ι : A ⟶ A) L hLs).toAlgebraicGeometry
  have : IsIso (ι : A ⟶ A).left :=
    ⟨⟨(ι : A ⟶ A).left, inv_left_comp_inv_left A, inv_left_comp_inv_left A⟩⟩
  have hMamp : Scheme.Modules.IsAmple A.left ((Scheme.Modules.pullback (ι : A ⟶ A).left).obj L) :=
    Scheme.Modules.isAmple_pullback_of_isIso _ L hamp
  exact Scheme.Modules.isAmple_tensor_of_power_sections_cover A.left L _ hamp fun x => by
    obtain ⟨m, hm, t, hx, -⟩ := hMamp.exists_affine_nonvanishingLocus x
    exact ⟨m, hm, t, hx⟩

/-- **`[d]` is finite for every nonzero integer `d`**, given an ample invertible module on `A` and
the theorem of the cube for `A`. -/
theorem isFinite_zpow_id_left_of_isAmple [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (d : ℤ) (hd : d ≠ 0) (L : A.left.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible A.left.toRingedSpace.presheaf
      (structureSheafRing A.left.toRingedSpace).property L]
    (hamp : Scheme.Modules.IsAmple A.left L) : IsFinite ((𝟙 A : A ⟶ A) ^ d).left := by
  have hLs := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hN := isInvertible_symmetrize_ag A L
  have := isProper_zpow_id_left A d
  have : A.left.IsSeparated := ⟨by rw [← Limits.terminal.comp_from A.hom]; infer_instance⟩
  obtain ⟨e⟩ := nonempty_zpowId_pullback_symmetrize_iso A L hLs hcube d
  have hm : ((d.natAbs * d.natAbs : ℕ) : ℤ) = d * d := by
    push_cast; rw [← abs_mul, abs_of_nonneg (mul_self_nonneg d)]
  have hm1 : 1 ≤ d.natAbs * d.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (Int.natAbs_ne_zero.mpr hd) (Int.natAbs_ne_zero.mpr hd))
  exact isFinite_of_isAmple_tensorPowModule ((𝟙 A : A ⟶ A) ^ d).left (symmetrize A L)
    ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr (isAmple_symmetrize A L hamp))
    (symmetrize A L)
    (d.natAbs * d.natAbs) hm1
    (e ≪≫ eqToIso (by rw [hm]; rfl) ≪≫
      Stacks.PowerFamilyBridge.tensorPowerModuleIso A.left (symmetrize A L) _)

/-- **`[d]` is flat for every nonzero integer `d`**, given an ample invertible module on `A` and
the theorem of the cube for `A`. -/
theorem flat_zpow_id_left_of_isAmple [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (d : ℤ) (hd : d ≠ 0) (L : A.left.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.left.toRingedSpace.presheaf
      (structureSheafRing A.left.toRingedSpace).property L]
    (hamp : Scheme.Modules.IsAmple A.left L) : Flat ((𝟙 A : A ⟶ A) ^ d).left := by
  have := isFinite_zpow_id_left_of_isAmple A hcube d hd L hamp
  have : Smooth A.hom := smooth_hom A
  exact flat_of_isFinite_of_isRegularLocalRing k A.hom
    (fun x => isRegularLocalRing_stalk_of_smooth_over_field A.hom x) _

/-- For every nonzero integer `d`, multiplication by `d` on an abelian variety `A` over a field
`k` is finite locally free of degree `|d| ^ {2 dim A}`, given an ample invertible module `L` on `A`
and the theorem of the cube for `A`. -/
theorem isFiniteLocallyFreeOfRank_zpow_id_left_of_isAmple_of_ne_zero
    [AlgebraicGeometry.IsAbelianVariety k A] (hcube : HasTheoremOfTheCube A) (d : ℤ) (hd : d ≠ 0)
    (L : A.left.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible A.left.toRingedSpace.presheaf
      (structureSheafRing A.left.toRingedSpace).property L]
    (hamp : Scheme.Modules.IsAmple A.left L) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ d).left
      (d.natAbs ^ (2 * abelianVarietyDimension A)) := by
  have := isFinite_zpow_id_left_of_isAmple A hcube d hd L hamp
  have hfl := flat_zpow_id_left_of_isAmple A hcube d hd L hamp
  have := isFiniteLocallyFree_of_isFinite_of_flat A ((𝟙 A : A ⟶ A) ^ d).left
  have := surjective_zpow_id_left_of_flat A d hfl
  have hLs := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hN := isInvertible_symmetrize_ag A L
  obtain ⟨e⟩ := nonempty_zpowId_pullback_symmetrize_iso A L hLs hcube d
  have hm : ((d.natAbs * d.natAbs : ℕ) : ℤ) = d * d := by
    push_cast; rw [← abs_mul, abs_of_nonneg (mul_self_nonneg d)]
  have hdeg : degreeOver ((𝟙 A : A ⟶ A) ^ d).left =
      (d.natAbs * d.natAbs) ^ abelianVarietyDimension A :=
    degreeOver_eq_pow_of_pullback_iso_tensorPower k A.hom ((𝟙 A : A ⟶ A) ^ d).left
      (Over.w _) (abelianVarietyDimension A) (topologicalKrullDim_eq_abelianVarietyDimension A)
      (symmetrize A L) (isAmple_symmetrize A L hamp) (d.natAbs * d.natAbs)
      (e ≪≫ eqToIso (by rw [hm]; rfl))
  have h := Stacks.Morphisms.isFiniteLocallyFreeOfRank_degreeOver ((𝟙 A : A ⟶ A) ^ d).left
  rwa [hdeg, ← sq, ← pow_mul] at h

/-- **An abelian variety carries an ample invertible module.** -/
theorem exists_isAmple_modules_of_isAbelianVariety [AlgebraicGeometry.IsAbelianVariety k A] :
    ∃ L : A.left.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        A.left.toRingedSpace.presheaf (structureSheafRing A.left.toRingedSpace).property L,
      Scheme.Modules.IsAmple A.left L := by
  have : LocallyOfFiniteType (Grp.mk A).X.hom := inferInstanceAs (LocallyOfFiniteType A.hom)
  have : QuasiCompact (Grp.mk A).X.hom := inferInstanceAs (QuasiCompact A.hom)
  exact (isQuasiProjective_groupScheme_iff_exists_isAmple (Grp.mk A)).mp
    (isQuasiProjective_of_groupScheme_over_field (Grp.mk A))

variable [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]

/-- Multiplication by an integer invertible in `k` on an abelian variety is dominant, being
surjective. -/
theorem isDominant_zpow_id_left_of_isUnit (n : ℕ) (hn : IsUnit (n : k)) :
    IsDominant ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left := by
  have := surjective_zpow_id_left_of_etale A n (etale_natCast_zpow_id_left_of_isUnit A n hn)
  infer_instance

omit [IsAlgClosed k] in
/-- **`[n]` is finite locally free of rank `n ^ {2 dim A}`** for `n` invertible in `k`, given an
ample invertible module on `A` and the theorem of the cube for `A`. -/
theorem isFiniteLocallyFreeOfRank_zpow_id_left_of_isAmple (hcube : HasTheoremOfTheCube A)
    (n : ℕ) (hn : IsUnit (n : k)) (L : A.left.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible A.left.toRingedSpace.presheaf
      (structureSheafRing A.left.toRingedSpace).property L]
    (hamp : Scheme.Modules.IsAmple A.left L) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left
      (n ^ (2 * abelianVarietyDimension A)) := by
  have hn0 : (n : ℤ) ≠ 0 := by rintro h; simp_all
  simpa using isFiniteLocallyFreeOfRank_zpow_id_left_of_isAmple_of_ne_zero A hcube n hn0 L hamp

/-- **`A(k)[n] ≅ (𝐙/n𝐙)^{2 dim A}`** for `n` invertible in `k`, given an ample invertible module
on `A` and the theorem of the cube for `A`. -/
theorem nonempty_torsionBy_addEquiv_of_isAmple (hcube : HasTheoremOfTheCube A)
    (n : ℕ) (hn : IsUnit (n : k)) (L : A.left.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.left.toRingedSpace.presheaf
      (structureSheafRing A.left.toRingedSpace).property L]
    (hamp : Scheme.Modules.IsAmple A.left L) :
    letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
    Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) ≃+
      (Fin (2 * abelianVarietyDimension A) → ZMod n)) :=
  nonempty_torsionBy_addEquiv_of_isFiniteLocallyFreeOfRank A n _ hn fun p _ hpn =>
    isFiniteLocallyFreeOfRank_zpow_id_left_of_isAmple A hcube p
      (isUnit_of_dvd_unit (Nat.cast_dvd_cast hpn) hn) L hamp

/-- Over an algebraically closed field, multiplication by a nonzero integer `d` on an abelian
variety is finite locally free of rank `|d| ^ {2 dim A}`. -/
theorem isFiniteLocallyFreeOfRank_zpow_id_left_of_ne_zero (d : ℤ) (hd : d ≠ 0) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ d).left
      (d.natAbs ^ (2 * abelianVarietyDimension A)) := by
  obtain ⟨L, hL, hamp⟩ := exists_isAmple_modules_of_isAbelianVariety A
  exact isFiniteLocallyFreeOfRank_zpow_id_left_of_isAmple_of_ne_zero A
    Stacks.Cube.hasTheoremOfTheCube d hd L hamp

/-- **`[n]` has rank `n ^ {2 dim A}`** on an abelian variety over an algebraically closed field,
for `n` invertible in `k`. -/
theorem isFiniteLocallyFreeOfRank_zpow_id_left_of_isUnit (n : ℕ) (hn : IsUnit (n : k)) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left
      (n ^ (2 * abelianVarietyDimension A)) := by
  obtain ⟨L, hL, hamp⟩ := exists_isAmple_modules_of_isAbelianVariety A
  exact isFiniteLocallyFreeOfRank_zpow_id_left_of_isAmple A Stacks.Cube.hasTheoremOfTheCube n hn L
    hamp

/-- **`A(k)[n] ≅ (𝐙/n𝐙)^{2 dim A}`** for an abelian variety over an algebraically closed field `k`
and `n` invertible in `k`. -/
@[sga "3 XVII 4.5"]
theorem nonempty_torsionBy_addEquiv_of_isUnit_of_isCommMonObj (n : ℕ) (hn : IsUnit (n : k)) :
    letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
    Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) ≃+
      (Fin (2 * abelianVarietyDimension A) → ZMod n)) := by
  obtain ⟨L, hL, hamp⟩ := exists_isAmple_modules_of_isAbelianVariety A
  exact nonempty_torsionBy_addEquiv_of_isAmple A Stacks.Cube.hasTheoremOfTheCube n hn L hamp

end Stacks.Groupoids
