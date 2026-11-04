module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.RingTheory.MvPowerSeries.AdicTopology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A power series criterion for a split extension

A morphism of the completed base category whose deep enough infinitesimal truncations admit
retractions is a split extension. The criterion is phrased with power series.

## Main definitions

* `Deformation.mvPowerSeriesResidueEquiv`: the residue field of a power series algebra over an
  object of the completed base category is identified with `k`.
* `Deformation.mvPowerSeriesObject`: the power series algebra in finitely many variables over
  such an object, as an object of the completed base category.
* `Deformation.mvPowerSeriesCoeffMap`: the inclusion of coefficients into it.

## Main results

* `Deformation.ideal_le_maximalIdeal_of_prodDecomposition`: the complement ideal of an
  additive direct sum decomposition lies in the maximal ideal.
* `Deformation.mem_maximalIdeal_mvPowerSeries_iff`: membership in the maximal ideal of a
  power series algebra is membership of the constant coefficient.
* `Deformation.surjective_of_mvPowerSeriesEval`: a power-series map which is spanning modulo
  `𝔪_R I` is surjective.
* `Deformation.mvPowerSeries_bijective_of_eventually_quotient_retract`: the power series
  criterion.
-/

@[expose] public section

namespace Deformation

/-! ### A power series criterion for a split extension -/

section
open CategoryTheory IsLocalRing
open scoped BigOperators
universe u v w

open CompleteLocalAlgCat
open PowerSeries

/-- If `R` is the additive direct sum of the image of `R'` and an ideal `I`, then `I` is
contained in the maximal ideal of `R`. -/
public theorem ideal_le_maximalIdeal_of_prodDecomposition
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R' R : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R' ⟶ R) (I : Ideal R)
    (hdecomp : ∀ z : R, ∃! p : R' × I, z = f.hom p.1 + p.2.1) :
    I ≤ maximalIdeal R := by
  refine IsLocalRing.le_maximalIdeal fun htop => ?_
  obtain ⟨p, -, hu⟩ := hdecomp 0
  have hneg : (-1 : R) ∈ I := by simp [htop]
  exact zero_ne_one (congrArg Prod.fst
    ((hu ((0 : R'), (0 : I)) (by simp)).trans (hu ((1 : R'), ⟨-1, hneg⟩) (by simp)).symm))

/-- The residue field of a power series algebra `R'[[x_1, …, x_r]]` over a Noetherian
complete local `Λ`-algebra is identified with `k` through the constant coefficient. -/
noncomputable def mvPowerSeriesResidueEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R' : CompleteLocalAlgCat.{u, v, w} Λ k) (r : ℕ) :
    ResidueField (MvPowerSeries (Fin r) R') ≃ₐ[Λ] k := by
  let cc : MvPowerSeries (Fin r) R' →ₐ[Λ] R' :=
    { toRingHom := MvPowerSeries.constantCoeff
      commutes' _ := rfl }
  letI : IsLocalHom cc.toRingHom := IsLocalHom.of_surjective cc.toRingHom
    fun a => ⟨MvPowerSeries.C a, MvPowerSeries.constantCoeff_C a⟩
  letI : IsLocalHom cc := ⟨fun a h => IsLocalHom.map_nonunit (f := cc.toRingHom) a h⟩
  have hbij : Function.Bijective (ResidueField.mapAlgHom cc) := by
    refine ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨a, rfl⟩ := residue_surjective y
    refine ⟨residue _ (MvPowerSeries.C a), ?_⟩
    rw [ResidueField.mapAlgHom_residue]
    change residue R' (MvPowerSeries.constantCoeff (MvPowerSeries.C a)) = _
    simp
  exact (AlgEquiv.ofBijective (ResidueField.mapAlgHom cc) hbij).trans R'.residueEquiv

/-- The power series algebra `R'[[x_1, …, x_r]]` over a Noetherian complete local
`Λ`-algebra, as an object of the completed base category. -/
@[sga "7 VI 4.14" "base R = Λ[[t_1"]
noncomputable def mvPowerSeriesObject
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R' : CompleteLocalAlgCat.{u, v, w} Λ k) (r : ℕ) :
    CompleteLocalAlgCat.{u, v, w} Λ k where
  carrier := MvPowerSeries (Fin r) R'
  completeLocal := {
    isNoetherian := inferInstance
    isLocal := inferInstance
    isComplete := MvPowerSeries.isAdicComplete_maximalIdeal r R' inferInstance }
  residueEquiv := mvPowerSeriesResidueEquiv R' r

/-- The identification of the residue field of a power series algebra carries the residue of a
constant to the residue of its coefficient. -/
public theorem mvPowerSeriesResidueEquiv_residue_C
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R' : CompleteLocalAlgCat.{u, v, w} Λ k) (r : ℕ) (a : R') :
    mvPowerSeriesResidueEquiv R' r
        (residue (MvPowerSeries (Fin r) R') (MvPowerSeries.C a)) =
      R'.residueEquiv (residue R' a) := by
  simp only [mvPowerSeriesResidueEquiv, AlgEquiv.trans_apply]
  congr 1

/-- The inclusion of coefficients `R' → R'[[x_1, …, x_r]]`, as a morphism of the completed
base category. -/
public noncomputable def mvPowerSeriesCoeffMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R' : CompleteLocalAlgCat.{u, v, w} Λ k) (r : ℕ) :
    R' ⟶ mvPowerSeriesObject R' r := by
  let c : R' →ₐ[Λ] MvPowerSeries (Fin r) R' :=
    { toRingHom := MvPowerSeries.C
      commutes' a := by simp [MvPowerSeries.algebraMap_apply] }
  exact
    { hom := c
      isLocal := ⟨fun a hu => by
        simpa using (MvPowerSeries.isUnit_iff_constantCoeff.1 hu :
          IsUnit (MvPowerSeries.constantCoeff (MvPowerSeries.C a)))⟩
      residue_comm a := mvPowerSeriesResidueEquiv_residue_C R' r a }

/-- A power series over a local ring lies in the maximal ideal exactly when its constant
coefficient does. -/
public theorem mem_maximalIdeal_mvPowerSeries_iff
    {R : Type*} [CommRing R] [IsLocalRing R] {r : ℕ}
    (s : MvPowerSeries (Fin r) R) :
    s ∈ maximalIdeal (MvPowerSeries (Fin r) R) ↔
      MvPowerSeries.constantCoeff s ∈ maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Suppose `R` is the additive direct sum of the image of `R'` and an ideal `I`, and that the
elements `x i` of `I` span `I / 𝔪_R I`. Then a power-series map over `R'` carrying `X i` to
`x i` and the maximal ideal into the maximal ideal is surjective. -/
public theorem surjective_of_mvPowerSeriesEval
    {R' R : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R' ⟶ R) (I : Ideal R)
    (hdecomp : ∀ z : R, ∃! p : R' × I, z = f.hom p.1 + p.2.1)
    {r : ℕ} (x : Fin r → I)
    (hspan : ∀ y : I, ∃ a : Fin r → R,
      y.1 - ∑ i, a i * (x i).1 ∈ maximalIdeal R * I)
    (F : MvPowerSeries (Fin r) R' →+* R)
    (hFmax : ∀ s ∈ maximalIdeal (MvPowerSeries (Fin r) R'), F s ∈ maximalIdeal R)
    (hF_C : ∀ a : R', F (MvPowerSeries.C a) = f.hom a)
    (hF_X : ∀ i, F (MvPowerSeries.X i) = (x i).1) :
    Function.Surjective F := by
  let A := MvPowerSeries (Fin r) R'
  let mA : Ideal A := maximalIdeal A
  let mR : Ideal R := maximalIdeal R
  have hFlocal : IsLocalHom F := by
    refine ⟨fun s hu => ?_⟩
    by_contra hs
    have hsM : s ∈ mA := (IsLocalRing.mem_maximalIdeal _).2 hs
    exact (IsLocalRing.mem_maximalIdeal _).mp (hFmax s hsM) hu
  let G : A →ₐ[Λ] R :=
    { toRingHom := F
      commutes' a := by
        show F (algebraMap Λ (MvPowerSeries (Fin r) R') a) = algebraMap Λ R a
        rw [MvPowerSeries.algebraMap_apply, hF_C]
        exact f.hom.commutes a }
  let S : CompleteLocalAlgCat.{u, v, w} Λ k := mvPowerSeriesObject R' r
  have : IsLocalHom G.toRingHom := hFlocal
  have : IsLocalHom G := ⟨fun a h => IsLocalHom.map_nonunit (f := G.toRingHom) a h⟩
  let φ : S ⟶ R :=
    { hom := G
      isLocal := hFlocal
      residue_comm := by
        intro s
        let sA : A := s
        have htail : sA - MvPowerSeries.C (MvPowerSeries.constantCoeff sA) ∈ mA := by
          rw [mem_maximalIdeal_mvPowerSeries_iff]
          simp
        have hres : residue R (F sA) =
            residue R (F (MvPowerSeries.C (MvPowerSeries.constantCoeff sA))) := by
          apply sub_eq_zero.mp
          rw [← map_sub, residue_eq_zero_iff]
          simpa only [map_sub] using hFmax _ htail
        calc
          R.residueEquiv (residue R (F sA)) =
              R.residueEquiv (residue R (F (MvPowerSeries.C (MvPowerSeries.constantCoeff sA)))) :=
                congrArg R.residueEquiv hres
          _ = R'.residueEquiv (residue R' (MvPowerSeries.constantCoeff sA)) := by
                rw [hF_C]
                exact f.residue_comm (MvPowerSeries.constantCoeff sA)
          _ = S.residueEquiv (residue S s) := rfl }
  have hI : I ≤ mR := ideal_le_maximalIdeal_of_prodDecomposition f I hdecomp
  have hmap : mA ≤ mR.comap G := hFmax
  have hcot : Function.Surjective (Ideal.mapCotangent mA mR G hmap) := by
    intro y
    obtain ⟨z, rfl⟩ := mR.toCotangent_surjective y
    obtain ⟨⟨a, i⟩, hp, -⟩ := hdecomp z
    have hiM : i.1 ∈ mR := hI i.2
    have hfaM : f.hom a ∈ mR := by
      rw [show f.hom a = z - i.1 by rw [(hp : (z : R) = f.hom a + i.1)]; ring]
      exact mR.sub_mem z.2 hiM
    have haM : a ∈ maximalIdeal R' := by
      have := f.isLocal
      rwa [← maximalIdeal_comap f.hom.toRingHom]
    obtain ⟨b, hb⟩ := hspan i
    have hparts : ∀ j : Fin r, ∃ c : R', ∃ q : I, b j = f.hom c + q.1 :=
      fun j => by obtain ⟨q, hq, _⟩ := hdecomp (b j); exact ⟨q.1, q.2, hq⟩
    choose c q hbc using hparts
    let s : A := MvPowerSeries.C a + ∑ j : Fin r,
      MvPowerSeries.C (c j) * MvPowerSeries.X j
    have hCa : MvPowerSeries.C a ∈ mA := by
      rwa [mem_maximalIdeal_mvPowerSeries_iff, MvPowerSeries.constantCoeff_C]
    have hX : ∀ j : Fin r, MvPowerSeries.X j ∈ mA := fun j => by
      rw [mem_maximalIdeal_mvPowerSeries_iff]
      simp
    have hs : s ∈ mA :=
      mA.add_mem hCa (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hX j))
    have hFs : F s = f.hom a + ∑ j : Fin r, f.hom (c j) * (x j).1 := by
      simp [s, hF_C, hF_X]
    have hmi : mR * I ≤ mR ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mono le_rfl hI
    have hrem₁ : (i.1 - ∑ j : Fin r, b j * (x j).1) ∈ mR ^ 2 := hmi hb
    have hrem₂ : (∑ j : Fin r, b j * (x j).1) -
        (∑ j : Fin r, f.hom (c j) * (x j).1) ∈ mR ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun j _ => ?_
      have hqx : (q j).1 * (x j).1 ∈ mR ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul (hI (q j).2) (hI (x j).2)
      rw [hbc j]
      convert hqx using 1; ring
    have hrem : (z : R) - F s ∈ mR ^ 2 := by
      rw [hFs, hp]
      convert Ideal.add_mem (mR ^ 2) hrem₁ hrem₂ using 1; ring
    refine ⟨mA.toCotangent ⟨s, hs⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent]
    apply mR.toCotangent_eq.mpr
    show F s - (z : R) ∈ mR ^ 2
    convert (mR ^ 2).neg_mem hrem using 1; ring
  exact (surjective_iff_surjective_cotangentSpaceMap φ).2 hcot

/-- Suppose `R` is the additive direct sum of the image of `R'` and an ideal `I`, and
`x : Fin r → I` is a basis of `I / 𝔪_R I`.  The power-series map which sends `X i` to
`x i` is bijective if, in all sufficiently high degrees, its maps modulo powers of the
maximal ideals have local `Λ`-algebra retractions. -/
@[stacks 06SG]
public theorem mvPowerSeries_bijective_of_eventually_quotient_retract
    {R' R : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R' ⟶ R) (I : Ideal R)
    (hdecomp : ∀ z : R, ∃! p : R' × I, z = f.hom p.1 + p.2.1)
    {r : ℕ} (x : Fin r → I)
    (hspan : ∀ y : I, ∃ a : Fin r → R,
      y.1 - ∑ i, a i * (x i).1 ∈ maximalIdeal R * I)
    (hindep : ∀ a : Fin r → R,
      (∑ i, a i * (x i).1 ∈ maximalIdeal R * I) →
        ∀ i, a i ∈ maximalIdeal R)
    (F : MvPowerSeries (Fin r) R' →+* R)
    (hF_C : ∀ a : R', F (MvPowerSeries.C a) = f.hom a)
    (hF_X : ∀ i, F (MvPowerSeries.X i) = (x i).1)
    (hretract : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Ideal.map F (maximalIdeal (MvPowerSeries (Fin r) R') ^ n) ≤
          maximalIdeal R ^ n ∧
        ∃ h : (R ⧸ maximalIdeal R ^ n) →+*
            (MvPowerSeries (Fin r) R' ⧸ maximalIdeal (MvPowerSeries (Fin r) R') ^ n),
          IsLocalHom h ∧
          (∀ s : MvPowerSeries (Fin r) R',
            h (Ideal.Quotient.mk (maximalIdeal R ^ n) (F s)) =
              Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin r) R') ^ n) s) ∧
      (∀ a : Λ,
            h (Ideal.Quotient.mk (maximalIdeal R ^ n) (algebraMap Λ R a)) =
              Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin r) R') ^ n)
                (MvPowerSeries.C (algebraMap Λ R' a)))) :
    Function.Bijective F := by
  let A := MvPowerSeries (Fin r) R'
  let mA : Ideal A := maximalIdeal A
  let mR : Ideal R := maximalIdeal R
  obtain ⟨N, hN⟩ := hretract
  let n₀ := max N 1
  have hn₀pos : 0 < n₀ := lt_max_of_lt_right Nat.one_pos
  have hFmax : ∀ s ∈ mA, F s ∈ mR := fun s hs =>
    (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem n₀ <| Ideal.pow_le_self hn₀pos.ne' <| by
      simpa only [map_pow] using
        (hN n₀ (le_max_left _ _)).1 (Ideal.mem_map_of_mem F (Ideal.pow_mem_pow hs n₀))
  refine ⟨fun s t hst => sub_eq_zero.mp <| IsHausdorff.haus
    (IsHausdorff.of_isLocalRing mA A (maximalIdeal.isMaximal A).ne_top) _ fun n => ?_,
    surjective_of_mvPowerSeriesEval f I hdecomp x hspan F hFmax hF_C hF_X⟩
  obtain ⟨-, h, -, hleft, -⟩ := hN (N + n) (Nat.le_add_right N n)
  have hmk : Ideal.Quotient.mk (mR ^ (N + n)) (F (s - t)) = 0 := by
    rw [map_sub, hst, sub_self, map_zero]
  have hmem : s - t ∈ mA ^ (N + n) := by
    have := hleft (s - t)
    rw [hmk, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using
    Ideal.pow_le_pow_right (Nat.le_add_left n N) hmem

end

end Deformation
