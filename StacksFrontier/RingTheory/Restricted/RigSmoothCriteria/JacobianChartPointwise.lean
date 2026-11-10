module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.TwoTermComplex.IdealPower
public import StacksFrontier.Homology.TwoTermComplex.Representative
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Restricted.RigSmooth
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Homology
public import StacksFrontier.RingTheory.Smooth.JacobianCriterion
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria.Conditions
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria.Equivalences

/-!
# Criteria for rig-smoothness: a single Jacobian chart and the pointwise reading

On one Jacobian chart `H⁰(NL^∧_{B/A})` becomes finite free after inverting its element, and
Stacks 0GAJ read at a single prime away from the ideal of definition, in both directions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open Rig.AdicFiniteTypeAlgebra
open Rig.CompletedPolynomialPresentation
open Rig.CompletedNaiveCotangentComplex

universe u v

namespace Rig
open Stacks.Smooth.JacobianCriterion

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CompletedPolynomialPresentation.extension
  Algebra.Extension.ofSurjective CompletedNaiveCotangentComplex.cochainComplex

/-! ### `H⁻¹` and `H⁰` on a single Jacobian chart

These are the two claims the Stacks Project establishes inside the `(4) ⟹ (2)` direction of
0GAJ, after inverting one element `b = b_l` of a Jacobian cover: `H⁻¹(NL^∧_{B/A})` is
`b`-power torsion, and `H⁰(NL^∧_{B/A})` becomes finite free after inverting `b`.  They are
stated for a single chart, which is the form in which the source proves and uses them.
-/

section JacobianMinor

variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D]

section Coordinates

variable {n m : ℕ} (T : Fin m ↪ Fin n)

/-- Extend a tuple indexed by the coordinates outside `T` by zero. -/
private def inclT : ({i : Fin n // i ∉ Set.range T} → R) →ₗ[R] (Fin n → R) :=
  LinearMap.pi fun i ↦
    if h : i ∈ Set.range T then 0
    else LinearMap.proj (⟨i, h⟩ : {i : Fin n // i ∉ Set.range T})

/-- Restrict a tuple to the coordinates outside `T`. -/
private def restrT : (Fin n → R) →ₗ[R] ({i : Fin n // i ∉ Set.range T} → R) :=
  LinearMap.pi fun i ↦ LinearMap.proj i.1

private lemma inclT_apply_of_notMem (y : {i : Fin n // i ∉ Set.range T} → R) {i : Fin n}
    (h : i ∉ Set.range T) : inclT T y i = y ⟨i, h⟩ := by
  change (dite _ _ _ : (_ → R) →ₗ[R] R) y = _
  split
  · exact absurd ‹_› h
  · rfl

private lemma inclT_apply_of_mem (y : {i : Fin n // i ∉ Set.range T} → R) {i : Fin n}
    (h : i ∈ Set.range T) : inclT T y i = 0 := by
  change (dite _ _ _ : (_ → R) →ₗ[R] R) y = _
  split
  · rfl
  · exact absurd h ‹_›

private lemma restrT_inclT (y : {i : Fin n // i ∉ Set.range T} → R) :
    restrT T (inclT T y) = y := by
  funext i
  exact inclT_apply_of_notMem T y i.2

private lemma inclT_injective : Function.Injective (inclT (R := R) T) :=
  Function.LeftInverse.injective (restrT_inclT T)

private lemma inclT_restrT (x : Fin n → R) (hx : ∀ j : Fin m, x (T j) = 0) :
    inclT T (restrT T x) = x := by
  funext i
  by_cases h : i ∈ Set.range T
  · obtain ⟨j, rfl⟩ := h
    rw [inclT_apply_of_mem T _ ⟨j, rfl⟩, hx j]
  · rw [inclT_apply_of_notMem T _ h]
    rfl

end Coordinates

/-- **The localized cokernel of a map with a Jacobian minor is free on the complementary
coordinates.**  Let `d : D → ⨁_{i < n} R` be a linear map, `T` an embedding of `m` of the `n`
coordinates, `u₁, …, u_m` elements of `D` spanning `t · D`, and suppose the `m × m` minor of
`d` on the `uⱼ` along `T` divides `t`.  Then after inverting `t` the cokernel of `d` becomes
isomorphic to the free module on the coordinates **outside** `T` — so it is free of rank
`n - m`, which is `Rig.card_notMem_range`.

This is the rank-bearing form of the freeness and finiteness of that cokernel: the index set of
the basis is left visible.  The map realizing it sends the free module on the complementary
coordinates to the cokernel by extending a tuple by zeros along `T`; it is surjective because
`t` is a unit and the "Newton" correction `t · x - d(Gu(adj(M)(x|_T)))` has vanishing
`T`-coordinates, and injective because `t`-power torsion is what `M.det ∣ t` kills. -/
public theorem nonempty_linearEquiv_localizedQuotient_of_jacobianMinor
    {n m : ℕ} (d : D →ₗ[R] (Fin n → R)) (T : Fin m ↪ Fin n) (u : Fin m → D) (t : R)
    (hu : ∀ x : D, t • x ∈ Submodule.span R (Set.range u))
    (hdet : (Matrix.of fun i j : Fin m ↦ d (u j) (T i)).det ∣ t) :
    Nonempty (LocalizedModule (Submonoid.powers t) ({i : Fin n // i ∉ Set.range T} → R)
        ≃ₗ[Localization.Away t]
      LocalizedModule (Submonoid.powers t) ((Fin n → R) ⧸ LinearMap.range d)) := by
  classical
  set M : Matrix (Fin m) (Fin m) R := Matrix.of fun i j ↦ d (u j) (T i) with hMdef
  set coord : (Fin n → R) →ₗ[R] (Fin m → R) := LinearMap.pi fun i ↦ LinearMap.proj (T i)
    with hcoorddef
  set Gu : (Fin m → R) →ₗ[R] D := ∑ j, (LinearMap.proj j).smulRight (u j) with hGudef
  set adj : (Fin m → R) →ₗ[R] (Fin m → R) := M.adjugate.mulVecLin with hadjdef
  set pr : (Fin n → R) →ₗ[R] (Fin n → R) := d ∘ₗ Gu ∘ₗ adj ∘ₗ coord with hprdef
  have hcoord : ∀ (x : Fin n → R) (i : Fin m), coord x i = x (T i) := fun x i ↦ rfl
  have hGu : ∀ y : Fin m → R, Gu y = ∑ j, y j • u j := by
    intro y
    simp [hGudef, LinearMap.sum_apply]
  have hcoordGu : ∀ y : Fin m → R, coord (d (Gu y)) = M.mulVec y := by
    intro y
    funext i
    rw [hcoord, Matrix.mulVec_apply_eq_sum, hGu y, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hMdef, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hcoordpr : ∀ x : Fin n → R, coord (pr x) = M.det • coord x := by
    intro x
    have h1 : pr x = d (Gu (adj (coord x))) := rfl
    rw [h1, hcoordGu, hadjdef]
    change M.mulVec (M.adjugate.mulVec (coord x)) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hgen : ∀ j : Fin m, pr (d (u j)) = M.det • d (u j) := by
    intro j
    have hco : coord (d (u j)) = fun i ↦ M i j := by
      funext i; rw [hcoord]; rfl
    have hadjc : adj (coord (d (u j))) = M.det • (Pi.single j (1 : R)) := by
      rw [hco, hadjdef]
      funext k
      change M.adjugate.mulVec (fun i ↦ M i j) k = _
      have he : M.adjugate.mulVec (fun i ↦ M i j) k = (M.adjugate * M) k j := by
        rw [Matrix.mulVec_apply_eq_sum, Matrix.mul_apply]
      rw [he, Matrix.adjugate_mul]
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [hkj]
    have h5 : Gu (M.det • (Pi.single j (1 : R))) = M.det • u j := by
      rw [map_smul, hGu]
      congr 1
      simp [Pi.single_apply]
    have h1 : pr (d (u j)) = d (Gu (adj (coord (d (u j))))) := rfl
    rw [h1, hadjc, h5, map_smul]
  have hspan : ∀ x : D, x ∈ Submodule.span R (Set.range u) → pr (d x) = M.det • d x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hgen j
    | zero => simp
    | add x y _ _ ihx ihy => rw [map_add, map_add, ihx, ihy, smul_add]
    | smul a x _ ih =>
      have e1 : pr (d (a • x)) = a • pr (d x) := by rw [map_smul, map_smul]
      rw [e1, ih, map_smul, smul_comm]
  have hprker : ∀ x : Fin n → R, coord x = 0 → pr x = 0 := by
    intro x hx
    have h1 : pr x = d (Gu (adj (coord x))) := rfl
    rw [h1, hx, map_zero, map_zero, map_zero]
  have hprrange : ∀ x : Fin n → R, pr x ∈ LinearMap.range d := fun x ↦ ⟨_, rfl⟩
  set nu : (Fin n → R) →ₗ[R] (Fin n → R) := M.det • LinearMap.id - pr with hnudef
  have hnuval : ∀ x : Fin n → R, nu x = M.det • x - pr x := fun x ↦ rfl
  have hnucoord : ∀ (x : Fin n → R) (j : Fin m), nu x (T j) = 0 := by
    intro x j
    have h2 : coord (nu x) = 0 := by
      have e : coord (nu x) = M.det • coord x - coord (pr x) := by
        rw [hnuval, map_sub, map_smul]
      rw [e, hcoordpr x, sub_self]
    have h3 := congrArg (fun z : Fin m → R ↦ z j) h2
    simpa [hcoord] using h3
  set F := ({i : Fin n // i ∉ Set.range T} → R) with hFdef
  set Q := (Fin n → R) ⧸ LinearMap.range d with hQdef
  set rho : F →ₗ[R] Q := (LinearMap.range d).mkQ ∘ₗ inclT T with hrhodef
  set S := Submonoid.powers t with hSdef
  set R' := Localization.Away t with hR'def
  have htunit : IsUnit (algebraMap R R' t) :=
    IsLocalization.map_units R' (⟨t, Submonoid.mem_powers t⟩ : S)
  have hdetunit : IsUnit (algebraMap R R' M.det) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap R R') hdet) htunit
  set mkF := LocalizedModule.mkLinearMap S F with hmkFdef
  set mkQQ := LocalizedModule.mkLinearMap S Q with hmkQdef
  set Phi : LocalizedModule S F →ₗ[R'] LocalizedModule S Q :=
    (IsLocalizedModule.map S mkF mkQQ rho).extendScalarsOfIsLocalization S R' with hPhidef
  have hPhi_mk' : ∀ (y : F) (s : S),
      Phi (IsLocalizedModule.mk' mkF y s) = IsLocalizedModule.mk' mkQQ (rho y) s :=
    fun y s ↦ IsLocalizedModule.map_mk' S mkF mkQQ rho y s
  have hrhoval : ∀ y : F, rho y = (LinearMap.range d).mkQ (inclT T y) := fun y ↦ rfl
  -- surjectivity
  have hsurj : Function.Surjective Phi := by
    intro z
    obtain ⟨⟨q, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S mkQQ z
    simp only [Function.uncurry_apply_pair]
    obtain ⟨x, rfl⟩ := (LinearMap.range d).mkQ_surjective q
    refine ⟨(↑hdetunit.unit⁻¹ : R') • IsLocalizedModule.mk' mkF (restrT T (nu x)) s, ?_⟩
    rw [map_smul, hPhi_mk']
    have h7 : (LinearMap.range d).mkQ (pr x) = 0 := by
      simpa using (Submodule.Quotient.mk_eq_zero _).2 (hprrange x)
    have hrv : rho (restrT T (nu x)) = M.det • (LinearMap.range d).mkQ x := by
      rw [hrhoval, inclT_restrT T _ (hnucoord x), hnuval, map_sub, map_smul, h7, sub_zero]
    rw [hrv, IsLocalizedModule.mk'_smul, ← algebraMap_smul R' M.det, smul_smul,
      IsUnit.val_inv_mul, one_smul]
  -- injectivity
  have hinj : Function.Injective Phi := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S mkF w
    simp only [Function.uncurry_apply_pair] at hw ⊢
    rw [LinearMap.mem_ker, hPhi_mk', IsLocalizedModule.mk'_eq_zero'] at hw
    obtain ⟨s', hs'⟩ := hw
    obtain ⟨k, hk⟩ := s'.2
    set z : Fin n → R := inclT T y with hzdef
    have hzcoord : coord z = 0 := by
      funext i
      rw [hcoord]
      exact inclT_apply_of_mem T y ⟨i, rfl⟩
    have hmem : t ^ k • z ∈ LinearMap.range d := by
      have hk' : t ^ k = (s' : R) := hk
      have h1 : (LinearMap.range d).mkQ (t ^ k • z) = 0 := by
        rw [map_smul, hk', ← hrhoval y]
        exact hs'
      rw [Submodule.mkQ_apply] at h1
      exact (Submodule.Quotient.mk_eq_zero _).1 h1
    obtain ⟨x₀, hx₀⟩ := hmem
    have hstep : M.det • (t ^ (k + 1) • z) = 0 := by
      have e1 : d (t • x₀) = t ^ (k + 1) • z := by
        rw [map_smul, hx₀, smul_smul]
        congr 1
        ring
      have e2 := hspan (t • x₀) (hu x₀)
      rw [e1] at e2
      have e3 : pr (t ^ (k + 1) • z) = 0 := by
        rw [map_smul, hprker z hzcoord, smul_zero]
      rw [e3] at e2
      exact e2.symm
    obtain ⟨q, hq⟩ := hdet
    have hzero : t ^ (k + 2) • z = 0 := by
      have h6 : t ^ (k + 2) = q * (M.det * t ^ (k + 1)) := by
        have e : t ^ (k + 2) = t * t ^ (k + 1) := by ring
        rw [e, hq]; ring
      rw [h6, mul_smul, mul_smul, hstep, smul_zero]
    have hy : t ^ (k + 2) • y = 0 := by
      apply inclT_injective T
      rw [map_smul, map_zero]
      exact hzero
    rw [IsLocalizedModule.mk'_eq_zero']
    exact ⟨⟨t ^ (k + 2), ⟨k + 2, rfl⟩⟩, hy⟩
  exact ⟨LinearEquiv.ofBijective Phi ⟨hinj, hsurj⟩⟩

/-- The number of coordinates outside an embedding of `m` of `n` coordinates is `n - m`. -/
public theorem card_notMem_range {n m : ℕ} (T : Fin m ↪ Fin n) :
    Nat.card {i : Fin n // i ∉ Set.range T} = n - m := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (p := fun i : Fin n ↦ i ∈ Set.range T),
    Fintype.card_fin, Set.card_range_of_injective T.injective, Fintype.card_fin]

/-- **The localized cokernel has a basis indexed by the coordinates outside the minor.**  Under
the hypotheses of `Rig.nonempty_linearEquiv_localizedQuotient_of_jacobianMinor` the localization
of `coker d` at `t` is free with a basis indexed by `{i : Fin n // i ∉ Set.range T}`, a set of
cardinality `n - m` by `Rig.card_notMem_range`.  This is the "free of rank `n - m` on
`dx_{m+1}, …, dx_n`" of the proofs of Stacks 0GAJ and 0GAW. -/
public theorem nonempty_basis_localizedQuotient_of_jacobianMinor
    {n m : ℕ} (d : D →ₗ[R] (Fin n → R)) (T : Fin m ↪ Fin n) (u : Fin m → D) (t : R)
    (hu : ∀ x : D, t • x ∈ Submodule.span R (Set.range u))
    (hdet : (Matrix.of fun i j : Fin m ↦ d (u j) (T i)).det ∣ t) :
    Nonempty (Module.Basis {i : Fin n // i ∉ Set.range T} (Localization.Away t)
      (LocalizedModule (Submonoid.powers t) ((Fin n → R) ⧸ LinearMap.range d))) := by
  classical
  obtain ⟨e⟩ := nonempty_linearEquiv_localizedQuotient_of_jacobianMinor d T u t hu hdet
  exact ⟨(((Pi.basisFun R {i : Fin n // i ∉ Set.range T}).baseChange
    (Localization.Away t)).map
      (IsLocalizedModule.isBaseChange (Submonoid.powers t) (Localization.Away t)
        (LocalizedModule.mkLinearMap (Submonoid.powers t)
          ({i : Fin n // i ∉ Set.range T} → R))).equiv).map e⟩

end JacobianMinor

/-- The relation `b J ⊆ (f₁, …, fₘ) + J²` of a Jacobian chart says exactly that `b` carries
the conormal module into the submodule generated by the classes of `f₁, …, fₘ`. -/
private lemma jacobianChart_smul_mem_span
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (b : P.completedPolynomialRing)
    {m : ℕ} (f : Fin m → P.ker)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2) :
    ∀ x : P.extension.Cotangent, P.toAlgHom b • x ∈
      Submodule.span B.carrier (Set.range fun j : Fin m ↦
        Algebra.Extension.Cotangent.mk (P := P.extension) (f j)) := by
  have hkerEq : P.ker = P.extension.ker := rfl
  intro x
  obtain ⟨z, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := P.extension) x
  let b' : P.extension.Ring := b
  have hzker : b' * z.val ∈ P.extension.ker := by
    change algebraMap P.extension.Ring B.carrier (b' * z.val) = 0
    rw [map_mul, z.property, mul_zero]
  have hzP : z.val ∈ P.ker := hkerEq.symm ▸ z.property
  obtain ⟨y, hy, w, hw, hsum⟩ := Submodule.mem_sup.mp (hrelations z.val hzP)
  have hyker : y ∈ P.extension.ker := by
    have hfker : Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) ≤
        P.extension.ker := Ideal.span_le.mpr (by
          rintro a ⟨j, rfl⟩
          exact (f j).property)
    exact hfker hy
  have hyspan := cotangent_mk_mem_span_of_mem_span P.extension f y hyker hy
  have hwzero : Algebra.Extension.Cotangent.mk (P := P.extension) ⟨w, by
      have hwsq : P.extension.ker ^ 2 ≤ P.extension.ker := Ideal.pow_le_self (by norm_num)
      exact hwsq hw⟩ = 0 :=
    (Algebra.Extension.Cotangent.mk_eq_zero_iff _).2 hw
  have hsum' : (⟨b' * z.val, hzker⟩ : P.extension.ker) =
      ⟨y, hyker⟩ + ⟨w, by
        have hwsq : P.extension.ker ^ 2 ≤ P.extension.ker := Ideal.pow_le_self (by norm_num)
        exact hwsq hw⟩ := Subtype.ext hsum.symm
  have hmk := congrArg (Algebra.Extension.Cotangent.mk (P := P.extension)) hsum'
  have hscalar : Algebra.Extension.Cotangent.mk (P := P.extension) ⟨b' * z.val, hzker⟩ =
      P.toAlgHom b • Algebra.Extension.Cotangent.mk (P := P.extension) z := by
    calc
      _ = b' • Algebra.Extension.Cotangent.mk (P := P.extension) z := by
        change Algebra.Extension.Cotangent.mk (P := P.extension) (b' • z) = _
        exact map_smul (Algebra.Extension.Cotangent.mk (P := P.extension)) b' z
      _ = _ := by
        rw [extension_cotangent_ring_smul_eq_algebraMap]
        congr 1
  rw [hscalar, map_add, hwzero] at hmk
  simp only [add_zero] at hmk
  exact hmk.symm ▸ hyspan

/-- The Jacobian minor of a chart, read as a minor of the differential of the completed naive
cotangent complex: the entries of the two matrices agree by
`Rig.CompletedNaiveCotangentComplex.differential_mk`, so the divisibility hypothesis of a chart
is a divisibility of that minor's determinant. -/
private lemma det_differential_dvd_of_jacobianChart
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (b : P.completedPolynomialRing)
    {m : ℕ} (T : Fin m ↪ Fin P.variableCount) (f : Fin m → P.ker)
    (hdet : P.toAlgHom
      (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (T i) (f j : P.completedPolynomialRing)) ∣
        P.toAlgHom b) :
    (Matrix.of fun i j : Fin m ↦ (completedNaiveCotangentComplex B P).differential
        (Algebra.Extension.Cotangent.mk (P := P.extension) (f j)) (T i)).det ∣
      P.toAlgHom b := by
  classical
  have hM : (Matrix.of fun i j : Fin m ↦ (completedNaiveCotangentComplex B P).differential
        (Algebra.Extension.Cotangent.mk (P := P.extension) (f j)) (T i)) =
      Matrix.of fun i j : Fin m ↦
        P.toAlgHom ((completedNaiveCotangentComplex B P).partialDeriv (T i)
          (f j : P.completedPolynomialRing)) := by
    ext i j
    exact congrFun ((completedNaiveCotangentComplex B P).differential_mk (f j)) (T i)
  rw [hM, show (Matrix.of fun i j : Fin m ↦
        P.toAlgHom ((completedNaiveCotangentComplex B P).partialDeriv (T i)
          (f j : P.completedPolynomialRing))).det =
      P.toAlgHom (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (T i)
          (f j : P.completedPolynomialRing)) from (P.toAlgHom.map_det _).symm]
  exact hdet

/-- **Stacks 0GAJ, inside the proof of (4) ⟹ (2): the rank.**  Let `b` carry a Jacobian chart
as in `Rig.free_localized_hzero_of_jacobianChart`.  Then `H⁰(NL^∧_{B/A})[1/b]` has a basis
indexed by the variables **outside** the chart's minor, so it is free of rank
`P.variableCount - m` (`Rig.card_notMem_range`), on the classes of the `dxᵢ` with
`i ∉ T`.

This is the rank that the last step of the proof of Stacks 0GAW compares: "both are free
`B[1/b]` modules of rank `r - m` with basis `dx_{m+1}, …, dx_r`". -/
public theorem nonempty_basis_localized_hzero_of_jacobianChart
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (b : P.completedPolynomialRing)
    {m : ℕ} (T : Fin m ↪ Fin P.variableCount) (f : Fin m → P.ker)
    (hdet : P.toAlgHom
      (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (T i) (f j : P.completedPolynomialRing)) ∣
        P.toAlgHom b)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2) :
    Nonempty (Module.Basis {i : Fin P.variableCount // i ∉ Set.range T}
      (Localization.Away (P.toAlgHom b))
      (LocalizedModule (Submonoid.powers (P.toAlgHom b))
        (completedNaiveCotangentComplex B P).Hzero)) := by
  classical
  exact nonempty_basis_localizedQuotient_of_jacobianMinor
    (completedNaiveCotangentComplex B P).differential T
    (fun j ↦ Algebra.Extension.Cotangent.mk (P := P.extension) (f j)) (P.toAlgHom b)
    (jacobianChart_smul_mem_span B P b f hrelations)
    (det_differential_dvd_of_jacobianChart B P b T f hdet)

/-- **Stacks 0GAJ, inside the proof of (4) ⟹ (2).**  Let `b` carry a Jacobian chart: a subset
`T` of `m` of the variables and `m` elements `f₁, …, fₘ` of the presentation ideal `J` whose
Jacobian minor along `T` divides `b`, with `b J ⊆ (f₁, …, fₘ) + J²`.  Then `H⁰(NL^∧_{B/A})`
becomes finite free after inverting `b`. -/
@[stacks 0GAJ "the proof of (4) ⟹ (2): H⁰(NL^∧) is finite free after inverting b_l"]
public theorem free_localized_hzero_of_jacobianChart
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (b : P.completedPolynomialRing)
    {m : ℕ} (T : Fin m ↪ Fin P.variableCount) (f : Fin m → P.ker)
    (hdet : P.toAlgHom
      (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (T i) (f j : P.completedPolynomialRing)) ∣
        P.toAlgHom b)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2) :
    Module.Free (Localization.Away (P.toAlgHom b))
        (LocalizedModule (Submonoid.powers (P.toAlgHom b))
          (completedNaiveCotangentComplex B P).Hzero) ∧
      Module.Finite (Localization.Away (P.toAlgHom b))
        (LocalizedModule (Submonoid.powers (P.toAlgHom b))
          (completedNaiveCotangentComplex B P).Hzero) := by
  obtain ⟨bs⟩ := nonempty_basis_localized_hzero_of_jacobianChart B P b T f hdet hrelations
  exact ⟨Module.Free.of_basis bs, Module.Finite.of_basis bs⟩

section PrimeLocal

/-- **Vanishing and freeness descend along a flat local homomorphism.** Let `R → S` be a local
homomorphism of local rings with `S` flat over `R`, and let `M` be a finite `R`-module. If
`S ⊗_R M` vanishes then so does `M`, and if `S ⊗_R M` is a free `S`-module then `M` is a free
`R`-module.

This is the last step of the source's proof of **Stacks 0GH6**: there `R = B_𝔮` and `S = A_𝔭`
for a prime `𝔭` of `A` lying over `𝔮`, the map is flat by Stacks 0GH1, and `M` is one of the
two cohomology modules of `NL^∧_{B/C}` localized at `𝔮`. A flat local homomorphism of local
rings is faithfully flat, and a finite flat module over a local ring is free.

The general faithfully flat descent lemmas of this library live in
`StacksFrontier/RingTheory/Flat/FaithfullyFlat/`; none of them descends freeness of a module of
arbitrary rank — `Module.free_of_tensorProduct_of_faithfullyFlat` there is the rank-one case —
which is why the statement is made here, in the shape its one consumer needs. -/
@[sga "1 VIII 1.11" "special case", sga "4½ Arcata 1.4.2" "(ii), special case"]
public theorem subsingleton_and_free_of_flat_isLocalHom
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (Subsingleton (TensorProduct R S M) → Subsingleton M) ∧
      (Module.Free S (TensorProduct R S M) → Module.Free R M) := by
  have hff : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R S).mp h
  · have : Module.Flat S (TensorProduct R S M) := Module.Flat.of_free
    have : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
    exact Module.free_of_flat_of_isLocalRing

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- **Stacks 0GAJ at a single prime.** Let `B` be rig-smooth over `(A, I)` and let `𝔮` be a
prime of `B` which does not contain the ideal of definition `I B`. Then, for any completed
polynomial presentation of `B`, the localization at `𝔮` of `H⁻¹(NL^∧_{B/A})` vanishes and the
localization at `𝔮` of `H⁰(NL^∧_{B/A})` is a free `B_𝔮`-module.

The source's proof of Stacks 0GH6 uses exactly this reading of 0GAJ: it assumes a chart map is
not rig-smooth and extracts a prime away from the ideal of definition at which one of these two
conclusions fails. -/
public theorem subsingleton_hneg_and_free_hzero_localizedAtPrime_of_isRigSmooth
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (hB : IsRigSmooth B) (q : Ideal B.carrier) [q.IsPrime] (hq : ¬ B.adicIdeal ≤ q) :
    Subsingleton (LocalizedModule q.primeCompl
        (completedNaiveCotangentComplex B P).Hneg) ∧
      Module.Free (Localization.AtPrime q)
        (LocalizedModule q.primeCompl (completedNaiveCotangentComplex B P).Hzero) := by
  classical
  obtain ⟨s, b, hcover, hcharts⟩ := (isRigSmooth_iff_hasJacobianCover B P).mp hB
  -- The cover condition produces a chart element `b l` which is a unit at `𝔮`.
  obtain ⟨l, hl⟩ : ∃ l : Fin s, P.toAlgHom (b l) ∉ q := by
    by_contra hall
    push Not at hall
    refine hq fun a ha ↦ ?_
    by_contra haq
    obtain ⟨n, hn⟩ := hcover ha
    have hspan : Ideal.span (Set.range fun l : Fin s ↦ P.toAlgHom (b l)) ≤ q :=
      Ideal.span_le.mpr (by rintro x ⟨l, rfl⟩; exact hall l)
    exact q.primeCompl.pow_mem haq n (hspan hn)
  obtain ⟨m, T, f, hdet, hrelations⟩ := hcharts l
  have hfin : Module.Finite B.carrier (completedNaiveCotangentComplex B P).Hzero :=
    Module.Finite.quotient _ _
  have hfp : Module.FinitePresentation B.carrier
      (completedNaiveCotangentComplex B P).Hzero :=
    Module.finitePresentation_of_finite _ _
  refine ⟨?_, ?_⟩
  · -- `H⁻¹` is `b l`-power torsion and `b l` is invertible at `𝔮`.
    have htor := isElementPowerTorsion_hneg_of_jacobianChart B P (b l) T f hdet hrelations
    refine LocalizedModule.subsingleton_iff.mpr fun x ↦ ?_
    obtain ⟨n, -, hx⟩ := htor x
    exact ⟨P.toAlgHom (b l) ^ n, q.primeCompl.pow_mem hl n, hx⟩
  · -- `D(b l)` lies in the free locus of `H⁰`, and `𝔮` lies in `D(b l)`.
    obtain ⟨hfree, -⟩ := free_localized_hzero_of_jacobianChart B P (b l) T f hdet hrelations
    have hsub := Module.basicOpen_subset_freeLocus_iff
      (R := B.carrier) (M := (completedNaiveCotangentComplex B P).Hzero)
      (f := P.toAlgHom (b l)) |>.mpr Module.Projective.of_free
    exact hsub (show (⟨q, inferInstance⟩ : PrimeSpectrum B.carrier) ∈
      PrimeSpectrum.basicOpen (P.toAlgHom (b l)) from hl)


section DerivedComparison

variable {R : Type*} [CommRing R]
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    {N₁ : Type*} [AddCommGroup N₁] [Module R N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module R N₂]

public lemma map_ker_of_square
    {f₁ : M₁ →ₗ[R] N₁} {f₂ : M₂ →ₗ[R] N₂} (eM : M₁ ≃ₗ[R] M₂) (eN : N₁ ≃ₗ[R] N₂)
    (h : f₂ ∘ₗ (eM : M₁ →ₗ[R] M₂) = (eN : N₁ →ₗ[R] N₂) ∘ₗ f₁) :
    (LinearMap.ker f₁).map (eM : M₁ →ₗ[R] M₂) = LinearMap.ker f₂ := by
  have hcomap : (LinearMap.ker f₂).comap (eM : M₁ →ₗ[R] M₂) = LinearMap.ker f₁ := by
    rw [← LinearMap.ker_comp, h, LinearMap.ker_comp, eN.ker, Submodule.comap_bot]
  rw [← hcomap, Submodule.map_comap_eq_of_surjective eM.surjective]

public lemma map_range_of_square
    {f₁ : M₁ →ₗ[R] N₁} {f₂ : M₂ →ₗ[R] N₂} (eM : M₁ ≃ₗ[R] M₂) (eN : N₁ ≃ₗ[R] N₂)
    (h : f₂ ∘ₗ (eM : M₁ →ₗ[R] M₂) = (eN : N₁ →ₗ[R] N₂) ∘ₗ f₁) :
    (LinearMap.range f₁).map (eN : N₁ →ₗ[R] N₂) = LinearMap.range f₂ := by
  have h₂ : LinearMap.range (f₂ ∘ₗ (eM : M₁ →ₗ[R] M₂)) = LinearMap.range f₂ :=
    LinearMap.range_comp_of_range_eq_top _ eM.range
  rw [← h₂, h, LinearMap.range_comp]

/-- Transport of the kernel along a commuting square of linear equivalences. -/
public def kerEquivOfSquare
    {f₁ : M₁ →ₗ[R] N₁} {f₂ : M₂ →ₗ[R] N₂} (eM : M₁ ≃ₗ[R] M₂) (eN : N₁ ≃ₗ[R] N₂)
    (h : f₂ ∘ₗ (eM : M₁ →ₗ[R] M₂) = (eN : N₁ →ₗ[R] N₂) ∘ₗ f₁) :
    LinearMap.ker f₁ ≃ₗ[R] LinearMap.ker f₂ :=
  (eM.submoduleMap (LinearMap.ker f₁)).trans
    (LinearEquiv.ofEq _ _ (map_ker_of_square eM eN h))

/-- Transport of the cokernel along a commuting square of linear equivalences. -/
public def cokerEquivOfSquare
    {f₁ : M₁ →ₗ[R] N₁} {f₂ : M₂ →ₗ[R] N₂} (eM : M₁ ≃ₗ[R] M₂) (eN : N₁ ≃ₗ[R] N₂)
    (h : f₂ ∘ₗ (eM : M₁ →ₗ[R] M₂) = (eN : N₁ →ₗ[R] N₂) ∘ₗ f₁) :
    (N₁ ⧸ LinearMap.range f₁) ≃ₗ[R] (N₂ ⧸ LinearMap.range f₂) :=
  Submodule.Quotient.equiv _ _ eN (map_range_of_square eM eN h)

end DerivedComparison

/-- The identification of degree `-1` of the chosen complex with the lifted conormal module. -/
public def cochainDegreeNegOneEquiv
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) :
    P.extension.Cotangent ≃ₗ[B.carrier]
      (completedNaiveCotangentComplex B P).cochainComplex.X (-1) :=
  ULift.moduleEquiv.symm.trans
    (completedNaiveCotangentComplex B P).degreeNegOneIso.symm.toLinearEquiv

/-- The identification of degree `0` of the chosen complex with the lifted free module. -/
public def cochainDegreeZeroEquiv
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) :
    (Fin P.variableCount → B.carrier) ≃ₗ[B.carrier]
      (completedNaiveCotangentComplex B P).cochainComplex.X 0 :=
  ULift.moduleEquiv.symm.trans
    (completedNaiveCotangentComplex B P).degreeZeroIso.symm.toLinearEquiv

/-- Under the term identifications, the degree `-1` differential of the chosen complex is the
differential of the completed naive cotangent complex. -/
public lemma differential_square
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) :
    ((completedNaiveCotangentComplex B P).cochainComplex.d (-1) 0).hom ∘ₗ
        (cochainDegreeNegOneEquiv B P : P.extension.Cotangent →ₗ[B.carrier]
          (completedNaiveCotangentComplex B P).cochainComplex.X (-1))
      = (cochainDegreeZeroEquiv B P : (Fin P.variableCount → B.carrier) →ₗ[B.carrier]
          (completedNaiveCotangentComplex B P).cochainComplex.X 0)
        ∘ₗ (completedNaiveCotangentComplex B P).differential := by
  ext x
  change ((completedNaiveCotangentComplex B P).cochainComplex.d (-1) 0).hom
      ((completedNaiveCotangentComplex B P).degreeNegOneIso.inv (ULift.up x))
    = (completedNaiveCotangentComplex B P).degreeZeroIso.inv
      (ULift.up ((completedNaiveCotangentComplex B P).differential x))
  rw [(completedNaiveCotangentComplex B P).cochainComplex_d]
  simp

/-- **The derived/kernel comparison for `H⁻¹(NL^∧_{B/A})`.** The degree-minus-one cohomology of
the derived object represented by the chosen complex is the kernel of the differential, which is
`Rig.CompletedNaiveCotangentComplex.Hneg`.

The complex is strictly supported in degrees `≥ -1`, so its degree-minus-one homology is
computed by the short complex `0 ⟶ L.X (-1) ⟶ L.X 0`, whose right homology is the kernel of
the differential; that kernel is then transported through the term identifications of
`Rig.CompletedNaiveCotangentComplex.cochainComplex`. -/
private def derivedHnegEquivHneg
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) (-1)).obj
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex))
      ≃ₗ[B.carrier] (completedNaiveCotangentComplex B P).Hneg :=
  haveI := (completedNaiveCotangent_strictBounds B P).1
  let L := (completedNaiveCotangentComplex B P).cochainComplex
  let h : (L.sc' (-2) (-1) 0).f = 0 :=
    (L.isZero_of_isStrictlyGE (-1) (-2) (by norm_num)).eq_of_src _ _
  (((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B.carrier) (-1)).app L ≪≫
      L.homologyIsoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
      (ShortComplex.RightHomologyData.ofHasKernel _ h).homologyIso ≪≫
      ModuleCat.kernelIsoKer (L.d (-1) 0)).toLinearEquiv).trans
    (kerEquivOfSquare (cochainDegreeNegOneEquiv B P) (cochainDegreeZeroEquiv B P)
      (differential_square B P)).symm

/-- **The derived/cokernel comparison for `H⁰(NL^∧_{B/A})`.** The degree-zero cohomology of the
derived object represented by the chosen complex is the cokernel of the differential, which is
`Rig.CompletedNaiveCotangentComplex.Hzero`.

The complex is strictly supported in degrees `≤ 0`, so its degree-zero homology is computed by
the short complex `L.X (-1) ⟶ L.X 0 ⟶ 0`, whose left homology is `L.X 0` modulo the range of
the differential; that cokernel is then transported through the term identifications of
`Rig.CompletedNaiveCotangentComplex.cochainComplex`. -/
private def derivedHzeroEquivHzero
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) 0).obj
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex))
      ≃ₗ[B.carrier] (completedNaiveCotangentComplex B P).Hzero :=
  haveI := (completedNaiveCotangent_strictBounds B P).2
  let L := (completedNaiveCotangentComplex B P).cochainComplex
  let h : (L.sc' (-1) 0 1).g = 0 :=
    (L.isZero_of_isStrictlyLE 0 1 (by norm_num)).eq_of_tgt _ _
  (((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B.carrier) 0).app L ≪≫
      L.homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
      (ShortComplex.LeftHomologyData.ofHasCokernel _ h).homologyIso ≪≫
      ModuleCat.cokernelIsoRangeQuotient (L.d (-1) 0)).toLinearEquiv).trans
    (cokerEquivOfSquare (cochainDegreeNegOneEquiv B P) (cochainDegreeZeroEquiv B P)
      (differential_square B P)).symm

/-- The conormal module of a completed polynomial presentation is a finite `B`-module. -/
public lemma finite_extension_cotangent
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) :
    Module.Finite B.carrier P.extension.Cotangent := by
  have : IsNoetherianRing P.completedPolynomialRing := AdicCompletion.isNoetherianRing _
  have : IsNoetherianRing P.extension.Ring := by
    change IsNoetherianRing P.completedPolynomialRing
    infer_instance
  exact Algebra.Extension.Cotangent.finite (Ideal.fg_of_isNoetherianRing _)

/-- **Stacks 0GAJ read backwards at every prime.** Let `B` be an object of the category over
`(A, I)` and let `P` be a completed polynomial presentation of `B`. Suppose that for every prime
`𝔮` of `B` which does not contain the ideal of definition `I B` the localization of
`H⁻¹(NL^∧_{B/A})` at `𝔮` vanishes and the localization of `H⁰(NL^∧_{B/A})` at `𝔮` is a free
`B_𝔮`-module. Then `B` is rig-smooth over `(A, I)`.

This is the converse of
`Rig.subsingleton_hneg_and_free_hzero_localizedAtPrime_of_isRigSmooth`; together the two say that
rig-smoothness *is* this pointwise condition on the complement of `V(I B)`.

No Jacobian chart has to be manufactured, which is why the converse is available at all. `I B` is
finitely generated over the Noetherian ring `B`, so a finite generating family `g₁, …, g_n` of
`I B` already covers the complement of `V(I B)` by the principal opens `D(gᵢ)`, and
`Module.basicOpen_subset_freeLocus_iff` turns the pointwise freeness hypothesis on `D(gᵢ)` into
projectivity of `H⁰` over `B_{gᵢ}`. Vanishing of `H⁻¹` at every prime off `V(I B)` is exactly
`I B`-power torsion, by `isIPowerTorsion_iff_localization_eq_zero`. Stacks 0G9K carries that pair
to its cohomological condition, which is condition (2) of Stacks 0GAJ, i.e.
`Rig.isRigSmooth_iff_cotangentCohomologyCondition`.

Stacks 0G9K and condition (2) speak about `DerivedCategory.homologyFunctor`, while the hypothesis
speaks about the kernel and cokernel of the differential; the two presentations are matched by
`Rig.derivedHnegEquivHneg` and `Rig.derivedHzeroEquivHzero`. -/
public theorem isRigSmooth_of_forall_prime
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (h : ∀ (q : Ideal B.carrier) [q.IsPrime], ¬ B.adicIdeal ≤ q →
      Subsingleton (LocalizedModule q.primeCompl (completedNaiveCotangentComplex B P).Hneg) ∧
        Module.Free (Localization.AtPrime q)
          (LocalizedModule q.primeCompl (completedNaiveCotangentComplex B P).Hzero)) :
    Rig.IsRigSmooth B := by
  classical
  have : IsNoetherianRing B.carrier := Rig.isNoetherianRing B
  have : Module.Finite B.carrier P.extension.Cotangent := finite_extension_cotangent B P
  set K := completedNaiveCotangentComplex B P with hK
  let eneg := derivedHnegEquivHneg B P
  let ezero := derivedHzeroEquivHzero B P
  have hfgI : B.adicIdeal.FG := Ideal.fg_of_isNoetherianRing _
  have hfinZeroQuot : Module.Finite B.carrier K.Hzero := Module.Finite.quotient _ _
  have hfinNeg : Module.Finite B.carrier
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) (-1)).obj
        (DerivedCategory.Q.obj K.cochainComplex)) :=
    Module.Finite.equiv eneg.symm
  have hfinZero : Module.Finite B.carrier
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) 0).obj
        (DerivedCategory.Q.obj K.cochainComplex)) :=
    Module.Finite.equiv ezero.symm
  have := hfinZero
  have : Module.FinitePresentation B.carrier
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) 0).obj
        (DerivedCategory.Q.obj K.cochainComplex)) :=
    Module.finitePresentation_of_finite _ _
  -- `H⁻¹` vanishes at every prime off `V(I B)`, hence is `I B`-power torsion.
  have htorKer : IsIPowerTorsion B.carrier K.Hneg B.adicIdeal := by
    rw [isIPowerTorsion_iff_localization_eq_zero _ _ _ hfgI]
    intro p hp
    have := p.isPrime
    exact not_nontrivial_iff_subsingleton.mpr (h p.asIdeal hp).1
  have htor : IsIPowerTorsion B.carrier
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) (-1)).obj
        (DerivedCategory.Q.obj K.cochainComplex)) B.adicIdeal := by
    intro x
    obtain ⟨n, hn, hx⟩ := htorKer (eneg x)
    refine ⟨n, hn, fun a ha ↦ ?_⟩
    have hax : eneg (a • x) = 0 := by rw [map_smul]; exact hx a ha
    exact eneg.map_eq_zero_iff.mp hax
  -- A finite generating family of `I B` already covers the complement of `V(I B)`.
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfgI
  change Ideal.span (Set.range g) = B.adicIdeal at hg
  have hgmem (i : Fin n) : g i ∈ B.adicIdeal := by
    rw [← hg]; exact Ideal.subset_span ⟨i, rfl⟩
  have hproj : ∀ i : Fin n, Module.Projective (Localization.Away (g i))
      (LocalizedModule (Submonoid.powers (g i))
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) 0).obj
          (DerivedCategory.Q.obj K.cochainComplex))) := by
    intro i
    rw [← Module.basicOpen_subset_freeLocus_iff, Module.freeLocus_congr ezero]
    intro p hp
    have hgi : g i ∉ p.asIdeal := hp
    have hnotle : ¬ B.adicIdeal ≤ p.asIdeal := fun hle ↦ hgi (hle (hgmem i))
    have := p.isPrime
    exact Module.mem_freeLocus.mpr (h p.asIdeal hnotle).2
  -- Stacks 0G9K carries the pair to condition (2) of Stacks 0GAJ.
  obtain ⟨hEC, hrest⟩ :=
    TwoTermComplex.exists_power_ext_one_annihilated_iff_cohomology_conditions
      B.adicIdeal (DerivedCategory.Q.obj K.cochainComplex)
      (completedNaiveCotangent_homology_vanishes B P)
  obtain ⟨hEF, hFN, -, -⟩ := hrest inferInstance hfinNeg hfinZero
  rw [isRigSmooth_iff_cotangentCohomologyCondition B P]
  exact hEC.mp (hEF.mpr (hFN.mpr ⟨htor, n, g, by rw [hg], hproj⟩))


/-- **A rig-smooth algebra admits a Jacobian chart away from any prime off `V(I B)`.** If `B` is
rig-smooth over `(A, I)` and `𝔮` is a prime of `B` not containing the ideal of definition, then
there is an element `b` of the completed polynomial ring with `P.toAlgHom b ∉ 𝔮` whose image is
divisible by a minor of the Jacobian matrix of a finite subfamily `f` of the presentation ideal,
and such that `b` multiplies the presentation ideal into the span of `f` plus its square.

This is condition (3) of Stacks 0GAJ, `Rig.isRigSmooth_iff_cotangentFactorization`, fed to the
prime-local selection `Rig.exists_jacobian_chart_away_prime`. It is the chart-producing companion
of `Rig.subsingleton_hneg_and_free_hzero_localizedAtPrime_of_isRigSmooth`, which reads off the
two cohomological conclusions at `𝔮` instead. -/
public theorem exists_jacobian_chart_away_prime_of_isRigSmooth
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (hB : IsRigSmooth B) (q : Ideal B.carrier) [q.IsPrime] (hq : ¬ B.adicIdeal ≤ q) :
    ∃ b : P.completedPolynomialRing, P.toAlgHom b ∉ q ∧
      ∃ (m : ℕ) (T : Fin m ↪ Fin P.variableCount) (f : Fin m → P.ker),
        (P.toAlgHom (Matrix.det fun i j : Fin m ↦
            (completedNaiveCotangentComplex B P).partialDeriv (T i)
              (f j : P.completedPolynomialRing)) ∣
            P.toAlgHom b) ∧
        (∀ x : P.completedPolynomialRing, x ∈ P.ker →
          b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
            P.ker ^ 2) :=
  exists_jacobian_chart_away_prime B P
    ((isRigSmooth_iff_cotangentFactorization B P).mp hB) q hq

end PrimeLocal

end Rig

end
