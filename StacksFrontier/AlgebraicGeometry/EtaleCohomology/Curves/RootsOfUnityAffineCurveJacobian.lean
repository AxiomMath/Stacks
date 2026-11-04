module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurveRank
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityJacobianTorsion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowRank
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 03RR from the Jacobian of the compactification

`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_picardDegreeZero` proves all
three clauses of [Stacks, Tag 03RR] for an affine smooth curve `X ⊆ X̄` over two inputs about the
smooth projective compactification `X̄`: `Pic⁰(X̄)` is `n`-divisible, and
`Pic⁰(X̄)[n] ≅ (𝐙/n𝐙)^{2g}`. This file derives both from an abelian variety `H` of dimension `g`
whose rational points are `Pic⁰(X̄)` (the Jacobian, [Stacks, Tag 0BA0]), carrying an ample
invertible module and satisfying the theorem of the cube:

* divisibility is clause (4) of [Stacks, Tag 03RP] for `H`, with `[n]` flat because étale
  (`AlgebraicGeometry.exists_nsmul_eq_curvePicardDegreeZero_of_jacobian`,
  `Stacks.Groupoids.flat_zpow_id_left_of_isUnit`);
* the torsion is clause (7) of [Stacks, Tag 03RP] for `H`
  (`AlgebraicGeometry.nonempty_curvePicardDegreeZeroTorsion_addEquiv_of_jacobian`), with the rank
  of `[p]` from `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_left_of_isAmple`.

## Main results

* `etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian_of_isAmple`: the three clauses of
  [Stacks, Tag 03RR] from the Jacobian, an ample module on it and the theorem of the cube for it.
* `etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian_of_isQuasiProjective`: the same
  with the ample module replaced by quasi-projectivity of the Jacobian.

## References

* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe t u

namespace AlgebraicGeometry

section AffineCurve

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)
  [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

include f in
/-- **The three clauses of [Stacks, Tag 03RR] from the Jacobian of the compactification.** Let
`X` be an affine smooth curve over an algebraically closed field `k`, `n` invertible in `k`, and
`j : X ⟶ X̄` an open immersion into a smooth projective curve of genus `g` with `r` points
outside `X`. Let `H` be a proper smooth connected open subgroup scheme of a group scheme over
`k`, of dimension `g`, whose rational points are identified with `Pic⁰(X̄)` by `φ`, carrying an
ample invertible module `L` and satisfying the theorem of the cube. Then
`H⁰_ét(X, μ_n) = μ_n(k)`, `H¹_ét(X, μ_n) ≅ (𝐙/n𝐙)^{2g+r-1}`, and `H^q_ét(X, μ_n) = 0` for
`q ≥ 2`. -/
@[sga "4 IX 4.6" "special case"]
theorem etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian_of_isAmple
    (hn : IsUnit (n : k))
    [IsAffine X] {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k fbar] [Smooth fbar]
    [IsProjectiveVariety k fbar] (j : X ⟶ Xbar) [IsOpenImmersion j] (hj : j ≫ fbar = f)
    (r : ℕ) (hr : Nat.card ↥(Set.range j.base)ᶜ = r)
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left)
    (hdim : Stacks.Groupoids.abelianVarietyDimension H.carrier.X = genus fbar)
    (φ : (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) → ↥(curvePicardDegreeZero k Xbar fbar))
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) (hbij : Function.Bijective φ)
    (hcube : Stacks.Groupoids.HasTheoremOfTheCube H.carrier.X)
    (L : H.carrier.X.left.Modules)
    [SheafOfModules.IsInvertible H.carrier.X.left.toRingedSpace.presheaf
      (structureSheafRing H.carrier.X.left.toRingedSpace).property L]
    (hamp : Scheme.Modules.IsAmple H.carrier.X.left L) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      Nonempty (Sheaf.H (kummerSmallEtale B X hX n).X₁ 1 ≃+
        (Fin (2 * genus fbar + r - 1) → ZMod n)) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) := by
  have : IsAbelianVariety k H.carrier.X := H.isAbelianVariety_carrier hproper hsmooth hconn
  refine etaleCohomology_rootsOfUnity_affineSmoothCurve_of_picardDegreeZero k X f B hX n hn fbar
    j hj r hr ?_ ?_
  · exact fun x hx => exists_nsmul_eq_curvePicardDegreeZero_of_jacobian k Xbar fbar n H hproper
      hsmooth hconn (Stacks.Groupoids.flat_zpow_id_left_of_isUnit H.carrier.X n hn) φ hmul hbij.2
      x hx
  · exact nonempty_curvePicardDegreeZeroTorsion_addEquiv_of_jacobian k Xbar fbar n hn H hproper
      hsmooth hconn hdim (fun p _ hpn =>
        Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_left_of_isAmple H.carrier.X hcube p
          (isUnit_of_dvd_unit (Nat.cast_dvd_cast hpn) hn) L hamp) φ hmul hbij

include f in
/-- The three clauses of [Stacks, Tag 03RR] from the Jacobian of the compactification, assumed
quasi-projective over `k` and satisfying the theorem of the cube. -/
theorem etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian_of_isQuasiProjective
    (hn : IsUnit (n : k))
    [IsAffine X] {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k fbar] [Smooth fbar]
    [IsProjectiveVariety k fbar] (j : X ⟶ Xbar) [IsOpenImmersion j] (hj : j ≫ fbar = f)
    (r : ℕ) (hr : Nat.card ↥(Set.range j.base)ᶜ = r)
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left)
    (hdim : Stacks.Groupoids.abelianVarietyDimension H.carrier.X = genus fbar)
    (φ : (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) → ↥(curvePicardDegreeZero k Xbar fbar))
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) (hbij : Function.Bijective φ)
    (hcube : Stacks.Groupoids.HasTheoremOfTheCube H.carrier.X)
    (hq : IsQuasiProjective H.carrier.X.hom) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      Nonempty (Sheaf.H (kummerSmallEtale B X hX n).X₁ 1 ≃+
        (Fin (2 * genus fbar + r - 1) → ZMod n)) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) := by
  have : IsAbelianVariety k H.carrier.X := H.isAbelianVariety_carrier hproper hsmooth hconn
  obtain ⟨L, hL, hamp⟩ := (isQuasiProjective_groupScheme_iff_exists_isAmple H.carrier).mp hq
  exact etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian_of_isAmple k X f B hX n hn fbar
    j hj r hr H hproper hsmooth hconn hdim φ hmul hbij hcube L hamp

end AffineCurve

end AlgebraicGeometry

end
