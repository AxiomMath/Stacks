module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Artinian.Module
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusGoesDownUnconditional
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusReduction
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionZModRank
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardTorsionGeneral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Passing to the reduction does not decrease the `ℓ`-torsion bound

Let `k` be an algebraically closed field, let `X` be a proper scheme of dimension at most one
over `k` and let `ℓ` be a prime invertible in `k`. Then `X` may be replaced by its reduction
`X_red` in the bound

`dim_{F_ℓ} Pic(X)[ℓ] ≤ dim_k H¹(X, 𝒪_X) + g_geom(X/k)`

of [Stacks, Tag 0CE6](https://stacks.math.columbia.edu/tag/0CE6):

* the genus goes down, `dim_k H¹(X_red, 𝒪_{X_red}) ≤ dim_k H¹(X, 𝒪_X)`;
* the geometric genus is unchanged ([Stacks, Tag 0CE2], clause (1));
* the `ℓ`-torsion of the Picard group is unchanged, so its `F_ℓ`-dimension is the same.

## Main results

* `AlgebraicGeometry.genus_reduction_le`: `dim_k H¹(X_red, 𝒪) ≤ dim_k H¹(X, 𝒪)` for a proper
  scheme of dimension at most one over a field.
* `AlgebraicGeometry.exists_pow_eq_of_isIntegral_of_isAlgClosed`: in a reduced Artinian ring
  integral over an algebraically closed field, every element is an `n`-th power for `n > 0`.
* `AlgebraicGeometry.exists_pow_eq_globalSections`: every global function on a reduced proper
  scheme over an algebraically closed field is an `n`-th power.
* `AlgebraicGeometry.bijOn_schemePullbackClass_reductionι_zsmulTorsion`: restriction is a
  bijection `Pic(X)[ℓ] → Pic(X_red)[ℓ]`.
* `AlgebraicGeometry.finrank_picardTorsion_reductionι_eq`:
  `dim_{F_ℓ} Pic(X)[ℓ] = dim_{F_ℓ} Pic(X_red)[ℓ]`.
* `AlgebraicGeometry.picardTorsion_bound_of_reduction`: **the reduction step of
  [Stacks, Tag 0CE6]**: the bound for `X_red` gives the bound for `X`.

## References

* [Stacks Project, Tag 0CE6](https://stacks.math.columbia.edu/tag/0CE6)
* [Stacks Project, Tag 0CE2](https://stacks.math.columbia.edu/tag/0CE2)
* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
* [Stacks Project, Tag 0C6S](https://stacks.math.columbia.edu/tag/0C6S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Picard (ofScheme schemePullbackClass schemePullbackClassHom zsmulTorsion)

universe u

namespace AlgebraicGeometry

attribute [local instance] AddSubgroup.torsionBy.zmodModule Ideal.Quotient.field

/-! ### The genus goes down on the reduction -/

/-- **The genus of the reduction is at most the genus.** For a proper scheme `X` of dimension at
most one over a field `k`, `dim_k H¹(X_red, 𝒪_{X_red}) ≤ dim_k H¹(X, 𝒪_X)`. -/
theorem genus_reduction_le (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsProper g] (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    genus (X.reductionι ≫ g) ≤ genus g :=
  genus_le_of_isFinite_of_isClosedImmersion_over_dense_open k g X.reductionι hdim ⊤ (by simp)
    inferInstance

/-! ### `n`-th powers over an algebraically closed field -/

/-- **In a reduced Artinian ring integral over an algebraically closed field every element is an
`n`-th power**, for every `n > 0`. -/
theorem exists_pow_eq_of_isIntegral_of_isAlgClosed {k R : Type*} [Field k] [IsAlgClosed k]
    [CommRing R] [_root_.IsReduced R] [IsArtinianRing R] (φ : k →+* R) (hφ : φ.IsIntegral)
    {n : ℕ} (hn : 0 < n) (u : R) : ∃ v : R, v ^ n = u := by
  classical
  have hroot : ∀ I : MaximalSpectrum R,
      ∃ w : R ⧸ I.asIdeal, w ^ n = Ideal.Quotient.mk I.asIdeal u := by
    intro I
    have hI : (Ideal.Quotient.mk I.asIdeal).IsIntegral :=
      (Ideal.Quotient.mk I.asIdeal).isIntegral_of_surjective Ideal.Quotient.mk_surjective
    have hbij : Function.Bijective ((Ideal.Quotient.mk I.asIdeal).comp φ) :=
      IsAlgClosed.ringHom_bijective_of_isIntegral _
        (RingHom.IsIntegral.trans φ (Ideal.Quotient.mk I.asIdeal) hφ hI)
    obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk I.asIdeal u)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (k := k) a hn
    exact ⟨(Ideal.Quotient.mk I.asIdeal).comp φ b, by rw [← map_pow, hb, ha]⟩
  choose w hw using hroot
  refine ⟨(IsArtinianRing.equivPi R).symm w, (IsArtinianRing.equivPi R).injective ?_⟩
  rw [map_pow, AlgEquiv.apply_symm_apply]
  funext I
  simpa only [Pi.pow_apply, IsArtinianRing.equivPi_apply] using hw I

/-- **Every global function on a reduced proper scheme over an algebraically closed field is an
`n`-th power**, for every `n > 0`. -/
@[sga "1 XI 6.6" "Example in Cor. 6.6"]
theorem exists_pow_eq_globalSections (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsProper g] [IsReduced X] {n : ℕ} (hn : 0 < n) (u : Γ(X, ⊤)) :
    ∃ v : Γ(X, ⊤), v ^ n = u := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have : Module.Finite k Γ(X, ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k g
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower k inferInstance
  have : _root_.IsReduced Γ(X, ⊤) := AlgebraicGeometry.IsReduced.component_reduced ⊤
  exact exists_pow_eq_of_isIntegral_of_isAlgClosed _
    (Stacks.AlgebraicGeometry.ProperGeomConnected.isIntegral_toSpecΓ_algebraMap g) hn u

/-- An integer invertible in the base field is invertible in the global functions of a scheme
over it. -/
theorem isUnit_intCast_globalSections (k : Type u) [Field k] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of k)) {ℓ : ℕ} (hℓ : IsUnit (ℓ : k)) : IsUnit ((ℓ : ℤ) : Γ(Y, ⊤)) := by
  simpa using hℓ.map ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom

/-! ### The `ℓ`-torsion of the Picard group is unchanged by the reduction -/

/-- **Restriction is a bijection `Pic(X)[ℓ] → Pic(X_red)[ℓ]`** for a proper scheme `X` over an
algebraically closed field `k` and a positive integer `ℓ` invertible in `k`. -/
theorem bijOn_schemePullbackClass_reductionι_zsmulTorsion (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g] (ℓ : ℕ) (hℓpos : 0 < ℓ)
    (hℓ : IsUnit (ℓ : k)) :
    Set.BijOn (schemePullbackClass X.reductionι) (zsmulTorsion (ofScheme X) (ℓ : ℤ))
      (zsmulTorsion (ofScheme X.reduction) (ℓ : ℤ)) := by
  have key : ∀ u : Γ(X.reduction, (⊤ : X.reduction.Opens))ˣ, ∃ v, u = v ^ (ℓ : ℤ) := by
    intro u
    obtain ⟨v, hv⟩ :=
      exists_pow_eq_globalSections k (X.reductionι ≫ g) hℓpos (u : Γ(X.reduction, ⊤))
    have hvu : IsUnit v := (isUnit_pow_iff hℓpos.ne').mp (hv ▸ u.isUnit)
    refine ⟨hvu.unit, Units.ext ?_⟩
    rw [zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    exact hv.symm
  have hpow : ∀ u : Γ(X.reduction, X.reductionι ⁻¹ᵁ (⊤ : X.Opens))ˣ, ∃ v, u = v ^ (ℓ : ℤ) := key
  exact Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_of_globalUnitsPowerLift
    X.reductionι (Scheme.isThickening_reductionι X)
    (isUnit_intCast_globalSections k (X.reductionι ≫ g) hℓ)
    (Stacks.Thickenings.globalUnitsPowerLift_of_isPow X.reductionι (ℓ : ℤ) hpow)

/-- **`dim_{F_ℓ} Pic(X)[ℓ] = dim_{F_ℓ} Pic(X_red)[ℓ]`** for a proper scheme over an algebraically
closed field and a prime `ℓ` invertible in it. No finiteness hypothesis is needed. -/
theorem finrank_picardTorsion_reductionι_eq (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) :
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) =
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X.reduction) (ℓ : ℤ)) :=
  Stacks.Picard.finrank_zmodTorsion_eq_of_bijOn ℓ (schemePullbackClassHom X.reductionι)
    (bijOn_schemePullbackClass_reductionι_zsmulTorsion k g ℓ (Fact.out : ℓ.Prime).pos hℓ)

/-- **Finite-dimensionality of the `ℓ`-torsion transfers from the reduction.** -/
theorem finiteDimensional_picardTorsion_of_reduction (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k))
    (hfin : FiniteDimensional (ZMod ℓ)
      (AddSubgroup.torsionBy (ofScheme X.reduction) (ℓ : ℤ))) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) :=
  Stacks.Picard.finiteDimensional_zmodTorsion_of_bijOn ℓ (schemePullbackClassHom X.reductionι)
    (bijOn_schemePullbackClass_reductionι_zsmulTorsion k g ℓ (Fact.out : ℓ.Prime).pos hℓ) hfin

/-! ### The reduction step of Tag 0CE6 -/

/-- **The reduction step of [Stacks, Tag 0CE6]: the bound passes from `X_red` to `X`.**
Let `k` be an algebraically closed field, let `X` be a proper scheme of dimension at most one
over `k` and let `ℓ` be a prime invertible in `k`. If the `ℓ`-torsion of `Pic(X_red)` is
finite-dimensional over `F_ℓ` and bounded by the genus of `X_red` plus its geometric genus, then
the `ℓ`-torsion of `Pic(X)` is finite-dimensional over `F_ℓ` and bounded by the genus of `X` plus
its geometric genus. -/
theorem picardTorsion_bound_of_reduction (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k))
    (hfin : FiniteDimensional (ZMod ℓ)
      (AddSubgroup.torsionBy (ofScheme X.reduction) (ℓ : ℤ)))
    (hbound : Module.finrank (ZMod ℓ)
        (AddSubgroup.torsionBy (ofScheme X.reduction) (ℓ : ℤ)) ≤
      genus (X.reductionι ≫ g) + geometricGenus k (X.reductionι ≫ g)) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ∧
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ≤
        genus g + geometricGenus k g := by
  refine ⟨finiteDimensional_picardTorsion_of_reduction k g ℓ hℓ hfin, ?_⟩
  rw [finrank_picardTorsion_reductionι_eq k g ℓ hℓ, geometricGenus_reduction g]
  exact hbound.trans (Nat.add_le_add_right (genus_reduction_le k g hdim) _)

end AlgebraicGeometry

end
