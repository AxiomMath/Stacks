module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Derivation.QuotientDescent
public import StacksFrontier.RingTheory.Flat.RegularSequenceAtPrime
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria
public import StacksFrontier.RingTheory.Rig.ClosedPoint.Regular
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RestrictedPowerSeries
public import StacksFrontier.RingTheory.Rig.Lifting
public import StacksFrontier.RingTheory.Sequence.RegularLocus

/-!
# The equations of a rig-smooth presentation at a prime of the generic fibre

Let `A` be a Noetherian adic topological ring with ideal of definition `I`, let `B` be an
`I`-adically complete `A`-algebra of finite type modulo `I` which is rig-smooth, and let
`B = A⟨x₁, …, x_n⟩ / J` be a completed polynomial presentation.  Let `𝔮` be a prime of
`A⟨x₁, …, x_n⟩` containing `J` and not containing `I A⟨x₁, …, x_n⟩`.

Two ingredients of the proof of Stacks 0GH1 are proved here.  First, the Jacobian criterion of
Tag 0GAJ produces, at `𝔮`, finitely many equations `f₁, …, f_m ∈ J` which generate `J_𝔮` and
whose Jacobian minor `det (∂ f_j / ∂ x_{T i})` is a unit in `A⟨x⟩_𝔮`; the passage from the
criterion's conclusion `b · J ⊆ (f₁, …, f_m) + J²` to the equality `J_𝔮 = (f₁, …, f_m)` is
Nakayama's lemma.  Second, when the prime `𝔭 = 𝔮 ∩ A` is rig-closed, elements of `𝔮` with an
invertible Jacobian minor are a regular sequence with flat quotient: the fibre
`A{x} ⊗_A κ(𝔭)` is geometrically regular over `κ(𝔭)` by Tag 0GGJ, so the fibre ring
`A{x}_𝔮 / 𝔭 A{x}_𝔮` is a regular local ring; the derivations descend to it; Tag 0GEE makes the
elements a regular sequence there; and Tag 00MG at a prime lifts that to `A{x}_𝔮`, because
`A → A{x}` is flat.  The removal of the hypothesis on `𝔭`, and the tag itself, are in
`StacksFrontier.RingTheory.Rig.RigSmoothRegularSequenceDescent` and
`StacksFrontier.RingTheory.Rig.RigSmoothRigFlat`.

## Main results

* `Rig.exists_jacobianChart_map_eq_span_atPrime`: the generating equations with unit Jacobian
  minor at a prime of the generic fibre.
* `Rig.flat_restrictedPowerSeries`: restricted power series are flat over a Noetherian ring.
* `Rig.isRegularLocalRing_fibre_atPrime`: regularity of the local fibre ring at a rig-closed
  prime of the base.
* `Rig.isRegular_and_flat_of_isUnit_det_of_isRegularLocalRing_fibre`: the Jacobian criterion on a
  regular fibre.
* `Rig.isRegular_and_flat_of_isUnit_det_of_isRigPointLocalCondition`: elements with an invertible
  Jacobian minor at a prime over a rig-closed prime form a regular sequence with flat quotient.

## References

* [Stacks Project, Tag 0GH1](https://stacks.math.columbia.edu/tag/0GH1)
* [Stacks Project, Tag 0GAJ](https://stacks.math.columbia.edu/tag/0GAJ)
* [Stacks Project, Tag 0GGJ](https://stacks.math.columbia.edu/tag/0GGJ)
* [Stacks Project, Tag 0GEE](https://stacks.math.columbia.edu/tag/0GEE)
* [Stacks Project, Tag 00MG](https://stacks.math.columbia.edu/tag/00MG)
-/

@[expose] public noncomputable section

open Algebra TensorProduct

universe u v

namespace Rig

/-- Nakayama's lemma in the form the Jacobian criterion needs: if `f₁, …, f_m` lie in an ideal
`J ≤ 𝔮` and some `u ∉ 𝔮` satisfies `u · J ⊆ (f₁, …, f_m) + J²`, then `J` and `(f₁, …, f_m)` have
the same image in the localization of `R` at `𝔮`. -/
public lemma map_eq_span_of_mul_mem_span_add_sq {R : Type u} [CommRing R] [IsNoetherianRing R]
    {q : Ideal R} [q.IsPrime] {J : Ideal R} (hJq : J ≤ q) {m : ℕ} (f : Fin m → R)
    (hf : ∀ j, f j ∈ J) {u : R} (hu : u ∉ q)
    (hrel : ∀ x ∈ J, u * x ∈ Ideal.span (Set.range f) + J ^ 2) :
    J.map (algebraMap R (Localization.AtPrime q)) =
      Ideal.span (Set.range fun j ↦ algebraMap R (Localization.AtPrime q) (f j)) := by
  have hGN : Ideal.span (Set.range fun j ↦ algebraMap R (Localization.AtPrime q) (f j)) ≤
      J.map (algebraMap R (Localization.AtPrime q)) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_map_of_mem _ (hf j)
  refine le_antisymm ?_ hGN
  have hmapspan : (Ideal.span (Set.range f) + J ^ 2).map
        (algebraMap R (Localization.AtPrime q)) =
      Ideal.span (Set.range fun j ↦ algebraMap R (Localization.AtPrime q) (f j)) ⊔
        (J.map (algebraMap R (Localization.AtPrime q))) ^ 2 := by
    rw [Ideal.add_eq_sup, Ideal.map_sup, Ideal.map_pow, Ideal.map_span, ← Set.range_comp]
    rfl
  have hNle : J.map (algebraMap R (Localization.AtPrime q)) ≤
      Ideal.span (Set.range fun j ↦ algebraMap R (Localization.AtPrime q) (f j)) ⊔
        (J.map (algebraMap R (Localization.AtPrime q))) ^ 2 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have h1 : algebraMap R (Localization.AtPrime q) (u * x) ∈
        (Ideal.span (Set.range f) + J ^ 2).map (algebraMap R (Localization.AtPrime q)) :=
      Ideal.mem_map_of_mem _ (hrel x hx)
    rw [hmapspan, map_mul] at h1
    obtain ⟨w, hw⟩ := IsLocalization.map_units (M := q.primeCompl)
      (Localization.AtPrime q) ⟨u, hu⟩
    refine Ideal.mem_comap.mpr ?_
    have h2 : algebraMap R (Localization.AtPrime q) x
        = (↑w⁻¹ : Localization.AtPrime q) *
          (algebraMap R (Localization.AtPrime q) u *
            algebraMap R (Localization.AtPrime q) x) := by
      rw [show (algebraMap R (Localization.AtPrime q) u) = (w : Localization.AtPrime q) from
        hw.symm, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
  have hNmax : J.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun x hx ↦ (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q x).mpr (hJq hx)
  have hsq : (J.map (algebraMap R (Localization.AtPrime q))) ^ 2 ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) •
        J.map (algebraMap R (Localization.AtPrime q)) := by
    rw [Ideal.smul_eq_mul, pow_two]
    exact Ideal.mul_mono_left hNmax
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (Ideal.fg_of_isNoetherianRing _)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) (hNle.trans (sup_le_sup_left hsq _))

/-- **The Jacobian chart of a rig-smooth presentation at a prime of the generic fibre.**  Let `B`
be rig-smooth over `(A, I)` with completed polynomial presentation `P` and let `𝔮` be a prime of
the completed polynomial ring containing `P.ideal` and not containing `I`.  Then finitely many
elements of `P.ideal` generate `P.ideal` after localizing at `𝔮`, and the determinant of their
derivatives along a subfamily of the variables is a unit there. -/
public theorem exists_jacobianChart_map_eq_span_atPrime
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (hB : IsRigSmooth B)
    (q : Ideal P.completedPolynomialRing) [q.IsPrime]
    (hq : ¬ I.map (algebraMap A P.completedPolynomialRing) ≤ q)
    (hJq : P.ideal ≤ q) :
    ∃ (m : ℕ) (T : Fin m ↪ Fin P.variableCount) (f : Fin m → P.completedPolynomialRing),
      (∀ j, f j ∈ P.ideal) ∧
      IsUnit (algebraMap P.completedPolynomialRing (Localization.AtPrime q)
        (Matrix.det fun i j : Fin m ↦
          (completedNaiveCotangentComplex B P).partialDeriv (T i) (f j))) ∧
      P.ideal.map (algebraMap P.completedPolynomialRing (Localization.AtPrime q)) =
        Ideal.span (Set.range fun j ↦
          algebraMap P.completedPolynomialRing (Localization.AtPrime q) (f j)) := by
  have hNoeth : IsNoetherianRing P.completedPolynomialRing := AdicCompletion.isNoetherianRing _
  obtain ⟨s, b, hrad, hchart⟩ := (isRigSmooth_iff_hasJacobianCover B P).mp hB
  have hsurj : Function.Surjective P.toAlgHom.toRingHom := P.toAlgHom_surjective
  have hkerq : RingHom.ker P.toAlgHom.toRingHom ≤ q := P.ker_eq_ideal.le.trans hJq
  have hcomap : (q.map P.toAlgHom.toRingHom).comap P.toAlgHom.toRingHom = q := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hkerq
  have hqB : (q.map P.toAlgHom.toRingHom).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj hkerq
  have hmem : ∀ x : P.completedPolynomialRing,
      x ∈ q ↔ P.toAlgHom x ∈ q.map P.toAlgHom.toRingHom := by
    refine fun x ↦ ⟨fun hx ↦ Ideal.mem_map_of_mem _ hx, fun hx ↦ ?_⟩
    exact hcomap.le (Ideal.mem_comap.mpr hx)
  have halg : P.toAlgHom.toRingHom.comp (algebraMap A P.completedPolynomialRing)
      = algebraMap A B.carrier := by
    ext a
    exact P.toAlgHom.commutes a
  have hadic : (I.map (algebraMap A P.completedPolynomialRing)).map P.toAlgHom.toRingHom
      = B.adicIdeal := by
    rw [Ideal.map_map, halg]
  have hnotle : ¬ B.adicIdeal ≤ q.map P.toAlgHom.toRingHom := fun hle ↦ hq <|
    (Ideal.map_le_iff_le_comap.mp (hadic.trans_le hle)).trans hcomap.le
  obtain ⟨l, hl⟩ : ∃ l : Fin s, b l ∉ q := by
    by_contra hall
    refine hnotle (hrad.trans fun x hx ↦ ?_)
    obtain ⟨n, hn⟩ := hx
    refine hqB.mem_of_pow_mem n (Ideal.span_le.mpr ?_ hn)
    rintro _ ⟨l, rfl⟩
    exact (hmem _).mp (not_not.mp fun h ↦ hall ⟨l, h⟩)
  obtain ⟨m, T, f, hdvd, hrel⟩ := hchart l
  have hfJ : ∀ j, (f j : P.completedPolynomialRing) ∈ P.ideal := fun j ↦
    P.ker_eq_ideal.le (f j).2
  refine ⟨m, T, fun j ↦ (f j : P.completedPolynomialRing), hfJ, ?_, ?_⟩
  · have hd : (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (T i)
          (f j : P.completedPolynomialRing)) ∉ q := by
      intro hdq
      refine hl ((hmem _).mpr ?_)
      obtain ⟨c, hc⟩ := hdvd
      rw [hc]
      exact Ideal.mul_mem_right _ _ ((hmem _).mp hdq)
    exact IsLocalization.map_units (M := q.primeCompl) _ ⟨_, hd⟩
  · have hker2 : P.ker ^ 2 = P.ideal ^ 2 := by rw [P.ker_eq_ideal]
    exact map_eq_span_of_mul_mem_span_add_sq hJq _ hfJ hl fun x hx ↦ by
      have h := hrel x (P.ker_eq_ideal.ge hx)
      rwa [hker2] at h

/-- Geometric regularity over a field transports along an algebra equivalence. -/
public theorem isGeometricallyRegular_congr {k : Type u} {S T : Type*}
    [Field k] [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
    (h : Algebra.IsGeometricallyRegular k S) (e : S ≃ₐ[k] T) :
    Algebra.IsGeometricallyRegular k T := by
  refine ⟨fun K _ _ _ ↦ ?_⟩
  have : IsRegularRing (K ⊗[k] S) := h.isRegularRing_tensorProduct K
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[k] K) e).toRingEquiv

/-- If the fibre `κ(𝔭) ⊗_A S` is a regular ring then for every prime `𝔮` of `S` lying over `𝔭`
the local fibre ring `S_𝔮 / 𝔭 S_𝔮` is a regular local ring. -/
public theorem isRegularLocalRing_quotient_of_isRegularRing_fibre
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] (p : Ideal A) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] (hpq : q.comap (algebraMap A S) = p)
    (h : IsRegularRing (p.Fiber S)) :
    IsRegularLocalRing (Localization.AtPrime q ⧸
      p.map (algebraMap A (Localization.AtPrime q))) := by
  obtain ⟨Q, hQp, hQ⟩ := Ideal.Fiber.exists_comap_includeRight_eq q p hpq
  have := hQp
  subst hQ
  have hmap : (p.map (algebraMap A S)).map
        (algebraMap S (Localization.AtPrime (Q.comap Algebra.TensorProduct.includeRight))) =
      p.map (algebraMap A
        (Localization.AtPrime (Q.comap Algebra.TensorProduct.includeRight))) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have := h.isRegularLocalRing_localization Q
  exact IsRegularLocalRing.of_ringEquiv
    ((Ideal.Fiber.algEquivAux₂ p Q).toRingEquiv.trans (Ideal.quotEquivOfEq hmap))

/-- **Restricted power series are flat.**  Over a Noetherian ring `A`, the restricted power series
ring `A{x_σ}` in finitely many variables is flat over `A`: it is the adic completion of the
Noetherian ring `A[x_σ]`, which is flat over `A[x_σ]`, and `A[x_σ]` is flat over `A`. -/
public theorem flat_restrictedPowerSeries {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (σ : Type v) [Finite σ] :
    Module.Flat A (RestrictedPowerSeries I σ) := by
  have : Module.Flat A (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
      (MvPolynomial σ A)) := Module.Flat.trans A (MvPolynomial σ A) _
  exact Module.Flat.of_linearEquiv (RestrictedPowerSeries.adicCompletionAlgEquiv I σ).toLinearEquiv

/-- **Regularity of the local fibre ring of a restricted power series algebra at a rig-closed
prime.**  For a Noetherian adic ring `A`, a rig-closed prime `𝔭` of `A` and a prime `𝔮` of
`A{x₁, …, x_n}` lying over `𝔭`, the ring `A{x}_𝔮 / 𝔭 A{x}_𝔮` is a regular local ring. -/
public theorem isRegularLocalRing_fibre_atPrime
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A]
    (hA : TopologicalRing.IsAdic A) (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) [p.IsPrime] (hp : Ideal.IsRigPointLocalCondition p)
    (n : ℕ) (hn : 0 < n)
    (q : Ideal (RestrictedPowerSeries I (Fin n))) [q.IsPrime]
    (hpq : q.comap (algebraMap A (RestrictedPowerSeries I (Fin n))) = p) :
    IsRegularLocalRing (Localization.AtPrime q ⧸
      p.map (algebraMap A (Localization.AtPrime q))) := by
  let : Algebra p.ResidueField (RestrictedPowerSeries I (Fin n) ⊗[A] p.ResidueField) :=
    Algebra.TensorProduct.rightAlgebra
  have hgeom : Algebra.IsGeometricallyRegular p.ResidueField
      (RestrictedPowerSeries I (Fin n) ⊗[A] p.ResidueField) :=
    isGeometricallyRegular_fibre hA I hI p hp n hn
  have hfib : Algebra.IsGeometricallyRegular p.ResidueField
      (p.Fiber (RestrictedPowerSeries I (Fin n))) :=
    isGeometricallyRegular_congr hgeom
      (Algebra.TensorProduct.commRight (R := A) (S := p.ResidueField)
          (A := RestrictedPowerSeries I (Fin n))).symm
  exact isRegularLocalRing_quotient_of_isRegularRing_fibre p q hpq
    (isRegularRing_of_isGeometricallyRegular hfib)

/-- The extension of the contraction of `𝔮` lies in the maximal ideal of `R_𝔮`. -/
public lemma map_comap_le_maximalIdeal_atPrime {A R : Type*} [CommRing A] [CommRing R]
    [Algebra A R] (q : Ideal R) [q.IsPrime] :
    (q.comap (algebraMap A R)).map (algebraMap A (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A R (Localization.AtPrime q) a,
    IsLocalization.AtPrime.to_map_mem_maximal_iff _ q]
  exact ha

/-- **Elements with an invertible Jacobian minor on a regular fibre form a regular sequence.**
Let `R` be a Noetherian algebra over a Noetherian ring `A`, flat over `A`, let `𝔮` be a prime of
`R` lying over `𝔭`, and assume that the local fibre ring `R_𝔮 / 𝔭 R_𝔮` is regular.  If
`y₁, …, y_m ∈ 𝔮` and `A`-derivations `D₁, …, D_m` of `R` satisfy `det (D_i y_j) ∉ 𝔮`, then the
images of the `y_j` form a regular sequence in `R_𝔮` and the quotient by them is flat over `A`.

The derivations descend to the fibre ring, where Stacks 0GEE makes the `y_j` a regular
sequence; Stacks 00MG at a prime lifts that to `R_𝔮`. -/
public theorem isRegular_and_flat_of_isUnit_det_of_isRegularLocalRing_fibre
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing A]
    [IsNoetherianRing R] [Module.Flat A R] (q : Ideal R) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime q ⧸
      (q.comap (algebraMap A R)).map (algebraMap A (Localization.AtPrime q))))
    {m : ℕ} (D : Fin m → Derivation A R R) (y : Fin m → R) (hy : ∀ j, y j ∈ q)
    (hdet : Matrix.det (fun i j : Fin m ↦ D i (y j)) ∉ q) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q)
        (List.ofFn fun j ↦ algebraMap R (Localization.AtPrime q) (y j)) ∧
      Module.Flat A (Localization.AtPrime q ⧸ Ideal.ofList (List.ofFn fun j ↦
        algebraMap R (Localization.AtPrime q) (y j))) := by
  have hp' : (q.comap (algebraMap A R)).IsPrime := Ideal.comap_isPrime _ _
  let pS : Ideal (Localization.AtPrime q) :=
    (q.comap (algebraMap A R)).map (algebraMap A (Localization.AtPrime q))
  have : IsRegularLocalRing (Localization.AtPrime q ⧸ pS) := hreg
  have hpSle : pS ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
    map_comap_le_maximalIdeal_atPrime q
  let y' : Fin m → Localization.AtPrime q := fun j ↦ algebraMap R (Localization.AtPrime q) (y j)
  let E : Fin m → Derivation A (Localization.AtPrime q) (Localization.AtPrime q) := fun i ↦
    (D i).localization q.primeCompl (Localization.AtPrime q)
  have hstab : ∀ i, ∀ x ∈ pS, E i x ∈ pS := fun i _ hx ↦
    Derivation.map_mem_map_algebraMap (E i) _ hx
  have hy'm : ∀ j, (Ideal.Quotient.mk pS) (y' j) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q ⧸ pS) := by
    intro j
    exact Stacks.RegularSequence.FibrewiseLocus.mk_mem_maximalIdeal_quotient hpSle
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).mpr (hy j))
  have hdetS : IsUnit ((Ideal.Quotient.mk pS) (Matrix.det fun i j ↦ E i (y' j))) := by
    have hd : (Matrix.det fun i j ↦ E i (y' j)) =
        algebraMap R (Localization.AtPrime q) (Matrix.det fun i j ↦ D i (y j)) := by
      rw [RingHom.map_det (algebraMap R (Localization.AtPrime q)) (fun i j ↦ D i (y j))]
      congr 1
      ext i j
      exact Derivation.localization_algebraMap _ _ _ (y j)
    rw [hd]
    exact (IsLocalization.map_units (M := q.primeCompl) _ ⟨_, hdet⟩).map
      (Ideal.Quotient.mk pS)
  have hfib : RingTheory.Sequence.IsRegular (Localization.AtPrime q ⧸ pS)
      ((List.ofFn y').map (Ideal.Quotient.mk pS)) := by
    rw [List.map_ofFn]
    exact isRegular_ofList_quotient_of_isUnit_det_derivation pS E hstab y' hy'm hdetS
  obtain ⟨hregq, hflat⟩ := isRegular_and_flat_quotient_ofList_take_atPrime (A := A) q hfib
  have h := hflat (List.ofFn y').length
  rw [List.take_length] at h
  exact ⟨hregq, h⟩

/-- **Elements with an invertible Jacobian minor at a prime over a rig-closed prime form a regular
sequence.**  Let `A` be a Noetherian adic ring with ideal of definition `I`, let `𝔮` be a prime
of `A{x₁, …, x_n}` whose contraction `𝔭 = 𝔮 ∩ A` is rig-closed, and let `y₁, …, y_m ∈ 𝔮` be
elements such that `det (D_{T i} y_j) ∉ 𝔮` for some `A`-derivations `D₁, …, D_n` and some
injection `T` of `{1, …, m}` into `{1, …, n}`.  Then the images of `y₁, …, y_m` form a regular
sequence in `A{x}_𝔮`, and the quotient of `A{x}_𝔮` by them is flat over `A`.

The fibre `A{x} ⊗_A κ(𝔭)` is geometrically regular by Stacks 0GGJ, so `A{x}_𝔮 / 𝔭 A{x}_𝔮` is a
regular local ring, and `Rig.isRegular_and_flat_of_isUnit_det_of_isRegularLocalRing_fibre`
applies.  This is the last paragraph of the proof of Stacks 0GH1. -/
public theorem isRegular_and_flat_of_isUnit_det_of_isRigPointLocalCondition
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A]
    (hA : TopologicalRing.IsAdic A) {I : Ideal A} (hI : IsAdic I) {n : ℕ}
    (D : Fin n → Derivation A (RestrictedPowerSeries I (Fin n))
      (RestrictedPowerSeries I (Fin n)))
    (q : Ideal (RestrictedPowerSeries I (Fin n))) [q.IsPrime]
    (hp : Ideal.IsRigPointLocalCondition
      (q.comap (algebraMap A (RestrictedPowerSeries I (Fin n)))))
    {m : ℕ} (T : Fin m ↪ Fin n) (y : Fin m → RestrictedPowerSeries I (Fin n))
    (hy : ∀ j, y j ∈ q) (hdet : Matrix.det (fun i j : Fin m ↦ D (T i) (y j)) ∉ q) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q)
        (List.ofFn fun j ↦ algebraMap (RestrictedPowerSeries I (Fin n))
          (Localization.AtPrime q) (y j)) ∧
      Module.Flat A (Localization.AtPrime q ⧸ Ideal.ofList (List.ofFn fun j ↦
        algebraMap (RestrictedPowerSeries I (Fin n)) (Localization.AtPrime q) (y j))) := by
  have hRnoeth : IsNoetherianRing (RestrictedPowerSeries I (Fin n)) :=
    isNoetherianRing_restrictedPowerSeries I (Fin n)
  have hRflat : Module.Flat A (RestrictedPowerSeries I (Fin n)) :=
    flat_restrictedPowerSeries I (Fin n)
  have hp' : (q.comap (algebraMap A (RestrictedPowerSeries I (Fin n)))).IsPrime :=
    Ideal.comap_isPrime _ _
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hm : m = 0 := Nat.le_zero.mp (by simpa using Fintype.card_le_of_embedding T)
    subst hm
    have : Nontrivial (Localization.AtPrime q ⧸
        (q.comap (algebraMap A (RestrictedPowerSeries I (Fin 0)))).map
          (algebraMap A (Localization.AtPrime q))) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
          (map_comap_le_maximalIdeal_atPrime (A := A) q))
    obtain ⟨hregq, hflat⟩ := isRegular_and_flat_quotient_ofList_take_atPrime (A := A)
      (R := RestrictedPowerSeries I (Fin 0)) q (fs := [])
      (by simpa using RingTheory.Sequence.IsRegular.nil _ _)
    have h := hflat 0
    rw [List.take_zero] at h
    rw [List.ofFn_zero]
    exact ⟨by simpa using hregq, h⟩
  exact isRegular_and_flat_of_isUnit_det_of_isRegularLocalRing_fibre q
    (isRegularLocalRing_fibre_atPrime hA I hI _ hp n hn q rfl) (fun i ↦ D (T i)) y hy hdet

end Rig

end
