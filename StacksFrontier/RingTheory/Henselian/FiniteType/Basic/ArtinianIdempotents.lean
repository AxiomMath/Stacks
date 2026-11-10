module

import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.RingTheory.Artinian.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic.QuasiFiniteSplit

/-!
# Idempotents of the closed fibre of a module-finite algebra

The closed fibre of a module-finite algebra over a local ring is Artinian, an Artinian ring has a
complete orthogonal family of idempotents with local factors, and primitive idempotents of the
closed fibre lift to isolating idempotents.
-/

@[expose] public section

universe u v

/-!
## Part (10) of Stacks 04GG: module-finite implies a finite product of local rings

A module-finite algebra `A` over a henselian local ring `R` decomposes as a finite
product `∏ i : Fin n, Aᵢ` of `R`-algebras, each local and module-finite over `R`.

Informally: since `A` is module-finite over the (Noetherian, local) henselian ring `R`, it is
itself
Noetherian and `Spec A` is a finite discrete-fibre over the closed point: the closed
fibre `A ⊗_R κ = A/𝔪A` is a finite-dimensional `κ`-algebra, hence Artinian, hence a
finite product of local Artinian `κ`-algebras `∏ⱼ (A/𝔪A)ⱼ`. The corresponding orthogonal
idempotents `ē₁, …, ēₙ` of `A/𝔪A` (with `∑ ēⱼ = 1`, `ēⱼēₖ = 0` for `j ≠ k`) *lift*,
because `R` is henselian local, to orthogonal idempotents `e₁, …, eₙ ∈ A` summing to `1`
(`HenselianLocalRing` ⇒ idempotents lift along the surjection `A → A/𝔪A`, as `A` is
`𝔪`-adically separated being module-finite over the henselian local `R`).

The idempotent decomposition `A ≃ₐ[R] ∏ⱼ A·eⱼ` then exhibits `A` as a product of the
`R`-algebras `Aⱼ := A·eⱼ`. Each `Aⱼ` is a direct factor of the module-finite `A`, hence
module-finite over `R` (`Module.Finite R Aⱼ`). Each `Aⱼ` is *local*: its closed fibre
`Aⱼ/𝔪Aⱼ = (A/𝔪A)ⱼ` is local Artinian (one of the connected pieces), so `Aⱼ` has a unique
prime over `𝔪`; being module-finite over the local `R`, all of its primes lie over `𝔪`
(integrality forces lying-over of the unique maximal ideal `𝔪` ↦ closed fibre), so `Aⱼ`
has a unique maximal ideal, i.e. `IsLocalRing Aⱼ`. Taking `n` = the number of connected
components of the closed fibre and `A : Fin n → _` the family `Aⱼ` completes the
decomposition, with `n = 0` precisely when `A` is the zero ring.
-/

/-- The closed fibre of a module-finite algebra over a local ring is Artinian: `A/𝔪A = A ⊗_R κ`
is a finite-dimensional `κ`-algebra for `κ = R/𝔪`, hence Artinian.

Concretely, `A ⧸ 𝔪A` carries a `κ`-algebra structure via
`Ideal.Quotient.algebraQuotientOfLEComap`; module-finiteness of `A` over `R` passes to `A ⧸ 𝔪A`
over `κ` along the surjection `A ↠ A ⧸ 𝔪A`, and a finite-dimensional algebra over a field is
Artinian. -/
@[ega "IV 2.5.8.8" "special case"]
lemma closedFibre_isArtinian'
    (R : Type u) [CommRing R] [IsLocalRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A] :
    IsArtinianRing (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) := by
  classical
  set 𝔪 : Ideal R := IsLocalRing.maximalIdeal R with h𝔪
  set 𝔪A : Ideal A := 𝔪.map (algebraMap R A) with h𝔪A
  -- Work over the residue field `K := R ⧸ 𝔪` (a field since `𝔪` is maximal).
  have hmax : (𝔪).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  let fieldK : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  -- `𝔪 ≤ comap (algebraMap R A) 𝔪A` so that `A ⧸ 𝔪A` is a `K = R ⧸ 𝔪`-algebra.
  have hle : 𝔪 ≤ Ideal.comap (algebraMap R A) 𝔪A := by
    rw [← Ideal.map_le_iff_le_comap]
  let algK : Algebra (R ⧸ 𝔪) (A ⧸ 𝔪A) := Ideal.Quotient.algebraQuotientOfLEComap hle
  have towerK : IsScalarTower R (R ⧸ 𝔪) (A ⧸ 𝔪A) :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  -- `A ⧸ 𝔪A` is module-finite over `R` (quotient of the module-finite `A`).
  have hRfin : Module.Finite R (A ⧸ 𝔪A) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R 𝔪A).toLinearMap
      Ideal.Quotient.mk_surjective
  -- Transfer finiteness to `K`: the structure map `R → K` is surjective, so the identity on
  -- `A ⧸ 𝔪A` is a surjective `(algebraMap R K)`-semilinear map.
  have hσsurj : Function.Surjective (algebraMap R (R ⧸ 𝔪)) := Ideal.Quotient.mk_surjective
  have : RingHomSurjective (algebraMap R (R ⧸ 𝔪)) := ⟨hσsurj⟩
  have hKfin : Module.Finite (R ⧸ 𝔪) (A ⧸ 𝔪A) := by
    let L : (A ⧸ 𝔪A) →ₛₗ[algebraMap R (R ⧸ 𝔪)] (A ⧸ 𝔪A) :=
      { toFun := id
        map_add' := fun x y => rfl
        map_smul' := fun r x => (IsScalarTower.algebraMap_smul (R ⧸ 𝔪) r x).symm }
    exact Module.Finite.of_surjective L Function.surjective_id
  have : FiniteDimensional (R ⧸ 𝔪) (A ⧸ 𝔪A) := hKfin
  exact finite_dimensional_algebra_is_artinian (R ⧸ 𝔪) (A ⧸ 𝔪A)

-- needed: `artinian_coi_local`'s `simpa using ht` for surjectivity of `g` needs defeq to
-- unfold the composed `Ideal.Quotient.mk` maps behind `mkS`.
set_option backward.isDefEq.respectTransparency false in
/-- Complete orthogonal idempotents of an Artinian ring, with local corners. Any commutative
Artinian ring `T` has a complete orthogonal family of idempotents `e : Fin n → T` — so `∑ eᵢ = 1`,
`eᵢeⱼ = 0` for `i ≠ j` and each `eᵢ` is idempotent, i.e. `CompleteOrthogonalIdempotents e` —
such that each corner `T ⧸ span{1 - eᵢ} = T·eᵢ` is a local ring. These corners are the local
Artinian factors of the structure theorem `T ≅ ∏ local Artinian`.

A commutative Artinian ring has finitely many maximal ideals
(`IsArtinianRing.setOf_isMaximal_finite`) and every prime is maximal
(`IsArtinianRing.isMaximal_of_isPrime`), and its Jacobson radical `J = ⋂ 𝔪ᵢ` is nilpotent. The
reduced quotient is a product of residue fields, `T/J ≅ ∏ κ(𝔪ᵢ)` (`IsArtinianRing.equivPi`), so
its standard complete orthogonal family (`CompleteOrthogonalIdempotents.single`) lifts through
the nilpotent-kernel surjection `T ↠ T/J` by
`CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`. Each corner `T·eᵢ` is then local: its
reduction mod `J` is the field `κ(𝔪ᵢ)` and the corner of `J` is nilpotent. -/
@[ega "I 6.2.2" "special case", sga "3 VIIB 0.1.1" "partial"]
lemma artinian_coi_local (T : Type*) [CommRing T] [IsArtinianRing T] :
    ∃ (n : ℕ) (e : Fin n → T), CompleteOrthogonalIdempotents e ∧
      ∀ i, IsLocalRing (T ⧸ Ideal.span {1 - e i}) := by
  set J : Ideal T := Ideal.jacobson (⊥ : Ideal T) with hJ
  have hred : IsReduced (T ⧸ J) := by
    rw [hJ, ← Ideal.isRadical_iff_quotient_reduced, IsArtinianRing.jacobson_eq_radical]
    exact Ideal.radical_isRadical _
  have hJnil : IsNilpotent J := by rw [hJ]; exact IsArtinianRing.isNilpotent_jacobson_bot
  set mk : T →+* (T ⧸ J) := Ideal.Quotient.mk J with hmkdef
  -- Each corner of `T` is local once its reduction mod `J` is local (nilpotent-kernel lift).
  have corner_local : ∀ (ei : T),
      IsLocalRing ((T ⧸ J) ⧸ Ideal.span {(1:(T ⧸ J)) - mk ei}) →
      IsLocalRing (T ⧸ Ideal.span {(1:T) - ei}) := by
    intro ei hKloc
    have := hKloc
    set s : (T ⧸ J) := mk ei with hs
    set qm : (T ⧸ J) →+* ((T ⧸ J) ⧸ Ideal.span {(1:(T ⧸ J)) - s}) :=
      Ideal.Quotient.mk (Ideal.span {(1:(T ⧸ J)) - s}) with hqm
    set g0 : T →+* ((T ⧸ J) ⧸ Ideal.span {(1:(T ⧸ J)) - s}) := qm.comp mk with hg0
    set mkS : T →+* (T ⧸ Ideal.span {(1:T) - ei}) := Ideal.Quotient.mk _ with hmkS
    have hsub : Ideal.span {(1:T) - ei} ≤ RingHom.ker g0 := by
      rw [Ideal.span_le]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      rw [SetLike.mem_coe, RingHom.mem_ker, hg0, RingHom.comp_apply]
      have h1 : mk (1 - ei) = 1 - s := by rw [map_sub, map_one]
      rw [h1, hqm, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton _)
    set g : (T ⧸ Ideal.span {(1:T) - ei}) →+* ((T ⧸ J) ⧸ Ideal.span {(1:(T ⧸ J)) - s}) :=
      Ideal.Quotient.lift _ g0 hsub with hg
    have hg0surj : Function.Surjective g0 := by
      rw [hg0]; exact (Ideal.Quotient.mk_surjective).comp (Ideal.Quotient.mk_surjective)
    have hgsurj : Function.Surjective g := by
      rw [hg]; intro z; obtain ⟨t, ht⟩ := hg0surj z
      exact ⟨mkS t, by rw [hmkS] at *; simpa using ht⟩
    have hnil : ∀ x ∈ RingHom.ker g, IsNilpotent x := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      obtain ⟨t, rfl⟩ : ∃ t, mkS t = x := by rw [hmkS]; exact Ideal.Quotient.mk_surjective x
      have hgt : g0 t = 0 := by
        have : g (mkS t) = g0 t := by rw [hg, hmkS]; rfl
        rw [this] at hx; exact hx
      have hmkt : mk t ∈ Ideal.span {(1:(T ⧸ J)) - s} := by
        rw [hg0, RingHom.comp_apply] at hgt
        rwa [hqm, Ideal.Quotient.eq_zero_iff_mem] at hgt
      rw [Ideal.mem_span_singleton] at hmkt
      obtain ⟨c, hc⟩ := hmkt
      obtain ⟨c', rfl⟩ : ∃ c', mk c' = c := by rw [hmkdef]; exact Ideal.Quotient.mk_surjective c
      have hj : t - c' * (1 - ei) ∈ J := by
        have : mk (t - c' * (1 - ei)) = 0 := by
          rw [map_sub, hc, hs, map_mul, map_sub, map_one]; ring
        rwa [hmkdef, Ideal.Quotient.eq_zero_iff_mem] at this
      have hmkScancel : mkS (c' * (1 - ei)) = 0 := by
        rw [map_mul]
        have : mkS (1 - ei) = 0 := by
          rw [hmkS, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span (Set.mem_singleton _)
        rw [this, mul_zero]
      have hmkSeq : mkS t = mkS (t - c' * (1 - ei)) := by rw [map_sub, hmkScancel, sub_zero]
      obtain ⟨k, hk⟩ := hJnil
      refine ⟨k, ?_⟩
      rw [hmkSeq, ← map_pow]
      have hmem : (t - c' * (1 - ei)) ^ k ∈ J ^ k := Ideal.pow_mem_pow hj k
      rw [hk, Submodule.zero_eq_bot, Ideal.mem_bot] at hmem
      rw [hmem, map_zero]
    have : Nontrivial (T ⧸ Ideal.span {(1:T) - ei}) := hgsurj.nontrivial
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro a
    have reflect : ∀ (a : T ⧸ Ideal.span {(1:T) - ei}), IsUnit (g a) → IsUnit a := by
      intro a h
      obtain ⟨b, hb⟩ := hgsurj (↑h.unit⁻¹)
      have hab : g (a * b) = 1 := by
        rw [map_mul, hb]
        exact h.mul_val_inv
      have hker : (a * b - 1) ∈ RingHom.ker g := by
        rw [RingHom.mem_ker, map_sub, hab, map_one, sub_self]
      have hunit : IsUnit (a * b) := by
        simpa using (hnil _ hker).isUnit_add_one
      exact isUnit_of_mul_isUnit_left hunit
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (g a) with h | h
    · exact Or.inl (reflect a h)
    · exact Or.inr (reflect (1 - a) (by simpa using h))
  -- Reduced quotient `T/J ≅ ∏ κ(𝔪ᵢ)`; transport the standard COI and lift it back to `T`.
  have eqP := IsArtinianRing.equivPi (T ⧸ J)
  have : Fintype (MaximalSpectrum (T ⧸ J)) := Fintype.ofFinite _
  have : DecidableEq (MaximalSpectrum (T ⧸ J)) := Classical.decEq _
  set ι := MaximalSpectrum (T ⧸ J) with hι
  have hsingle := CompleteOrthogonalIdempotents.single (fun x : ι => (T ⧸ J) ⧸ x.asIdeal)
  have hQcoi : CompleteOrthogonalIdempotents (fun x : ι => eqP.symm (Pi.single x 1)) := by
    have := hsingle.map (eqP.symm.toAlgHom.toRingHom)
    exact this
  set n := Fintype.card ι with hn
  set ev : Fin n ≃ ι := (Fintype.equivFin ι).symm with hev
  have hQcoiFin : CompleteOrthogonalIdempotents
      ((fun x : ι => eqP.symm (Pi.single x 1)) ∘ ev) :=
    (CompleteOrthogonalIdempotents.equiv ev).mpr hQcoi
  have hnilker : ∀ x ∈ RingHom.ker mk, IsNilpotent x := by
    intro x hx
    rw [hmkdef, Ideal.mk_ker] at hx
    obtain ⟨k, hk⟩ := hJnil
    exact ⟨k, by have := Ideal.pow_mem_pow hx k; rw [hk] at this; simpa using this⟩
  have hrange : ∀ i : Fin n, ((fun x : ι => eqP.symm (Pi.single x 1)) ∘ ev) i ∈ mk.range := by
    intro i; rw [hmkdef]; exact Ideal.Quotient.mk_surjective _
  obtain ⟨e', he'coi, he'mk⟩ :=
    CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker mk hnilker hQcoiFin hrange
  refine ⟨n, e', he'coi, ?_⟩
  intro i
  apply corner_local
  have hsi : mk (e' i) = eqP.symm (Pi.single (ev i) 1) := by
    have := congrFun he'mk i
    simpa [Function.comp] using this
  rw [hsi]
  -- `Q ⧸ span{1 - eqP.symm (Pi.single (ev i) 1)}` is the residue field `κ(𝔪_{ev i})`, hence local.
  set s : (T ⧸ J) := eqP.symm (Pi.single (ev i) 1) with hsdef
  set f : (T ⧸ J) →+* ((T ⧸ J) ⧸ (ev i).asIdeal) :=
    (Pi.evalRingHom (fun x : ι => (T ⧸ J) ⧸ x.asIdeal) (ev i)).comp eqP.toRingEquiv.toRingHom
    with hf
  have hfval : ∀ z, f z = (eqP z) (ev i) := by intro z; rw [hf]; rfl
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨q, hq⟩ := eqP.surjective (Pi.single (ev i) y)
    exact ⟨q, by rw [hfval, hq]; simp⟩
  have hfker : RingHom.ker f = Ideal.span {(1:(T ⧸ J)) - s} := by
    apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker, hfval] at hz
      rw [Ideal.mem_span_singleton]
      refine ⟨z, ?_⟩
      have hzs : z * s = 0 := by
        have heq : eqP (z * s) = 0 := by
          rw [map_mul, hsdef, eqP.apply_symm_apply]
          ext j
          by_cases hj : j = ev i
          · subst hj; simp [hz]
          · simp [Pi.single_eq_of_ne hj]
        exact eqP.injective (by rw [heq, map_zero])
      rw [mul_comm, mul_sub, mul_one, hzs, sub_zero]
    · rw [Ideal.span_le]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      rw [SetLike.mem_coe, RingHom.mem_ker, hfval, map_sub, map_one]
      rw [hsdef, eqP.apply_symm_apply]
      simp
  rw [← hfker]
  have e3 := RingHom.quotientKerEquivOfSurjective hfsurj
  have hmax : ((ev i).asIdeal).IsMaximal := (ev i).isMaximal
  have hFa : IsField ((T ⧸ J) ⧸ (ev i).asIdeal) := by
    rw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient]; infer_instance
  let := hFa.toField
  have : IsLocalRing ((T ⧸ J) ⧸ (ev i).asIdeal) := Field.instIsLocalRing _
  have : Nontrivial ((T ⧸ J) ⧸ RingHom.ker f) := e3.toEquiv.nontrivial
  exact IsLocalRing.of_surjective' e3.symm.toRingHom e3.symm.surjective

/-- The primitive idempotent at a point of the closed fibre. For `A` module-finite over a
henselian local ring `R` and a prime `q` of `A` lying over the maximal ideal `𝔪 = maximalIdeal R`,
there is an idempotent `g ∈ A` which, modulo `𝔪A`, is the primitive idempotent supported at the
single point `q` of the finite discrete spectrum of the closed fibre `Ā = A/𝔪A`. Concretely
`g ∉ q`, so that `mk g ≡ 1` at `q`, and `g ∈ q'` for every other prime `q'` of `A` over `𝔪`, so
that `mk g ≡ 0` there.

The argument is étale descent:
* `A` is module-finite over the local `R`, hence integral, so `Algebra.QuasiFiniteAt R q` holds
  for every `q` over `𝔪` — the whole closed fibre `Ā` is a finite `κ`-module.
* Stacks 00UJ (`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq 𝔪 q`) gives an étale
  `R'` in `Type u`, a κ-rational prime `P` over `𝔪` with residue bijectivity `κ ≅ R'/P`, and an
  idempotent `E ∈ R' ⊗ A` isolating the unique prime `P'` over both `P` and `q`, so `E ∉ P'`,
  with a uniqueness clause.
* `henselian_etale_residue_point_section R R' P hbij` gives a residue-compatible section
  `σ : R' →ₐ[R] R` with `∀ r', r' - algebraMap R R' (σ r') ∈ P`.
* Pushing `E` along `δ := (TensorProduct.lid R A) ∘ (TensorProduct.map σ (AlgHom.id R A))` gives
  `g := δ E`, idempotent by `IsIdempotentElem.map`. Here `g ∉ q` is the computation of
  `isolating_idempotent_per_point`, namely the identity `π = π ∘ includeRight ∘ δ` together with
  residue compatibility.
* For `g ∈ q'` with `q' ≠ q`: reducing mod `𝔪`, `E` is the indicator of the single fibre point
  `(P, q)`, and residue compatibility forces the reduction of `δ` to be evaluation at the
  κ-point `P`, so `mk g` is the indicator of `q` and vanishes at every other fibre point. -/
lemma reduction_of_isolating_idem
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A]
    (q : Ideal A) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)] :
    ∃ g : A, IsIdempotentElem g ∧ g ∉ q ∧
      ∀ (q' : Ideal A), q'.IsPrime → q'.LiesOver (IsLocalRing.maximalIdeal
          R) → q' ≠ q → g ∈ q' := by
  -- The 00UJ étale neighbourhood plus `henselian_etale_residue_point_section`, pushing along
  -- δ = lid ∘ (σ ⊗ id_A). The `g ∉ q` half mirrors `isolating_idempotent_per_point`; the
  -- `g ∈ q'` half for q' ≠ q reads the same `π = π ∘ ι ∘ δ` identity at a prime P'' over (P, q')
  -- and combines it with the isolation clause `huniq`.
  set 𝔪 := IsLocalRing.maximalIdeal R with h𝔪
  -- Step 1: Stacks 00UJ.
  obtain ⟨R', _, _, _, P, _, _, E, hE, P', _, hPP', hcomap, hEP', hbij, hfin, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq 𝔪 q
  -- Step 2: the henselian section σ : R' →ₐ[R] R, residue-compatible with P (keystone).
  obtain ⟨σ, hσP⟩ := henselian_etale_residue_point_section R R' P hbij
  -- Step 3: push E to g := δ E along δ = (lid) ∘ (σ ⊗ id_A).
  set δ : TensorProduct R R' A →ₐ[R] A :=
    (Algebra.TensorProduct.lid R A).toAlgHom.comp (Algebra.TensorProduct.map σ (AlgHom.id R A))
      with hδ
  have hδab : ∀ (a : R') (b : A), δ (a ⊗ₜ[R] b) = (algebraMap R A) (σ a) * b := by
    intro a b
    simp [hδ, Algebra.TensorProduct.map_tmul, Algebra.smul_def]
  -- The key residue identity: for ANY prime `P''` of `R' ⊗ A` lying over `P`, the two R-algebra
  -- maps `π''` and `π'' ∘ includeRight ∘ δ` into the quotient by P'' agree; hence
  -- `E - includeRight (δ E) ∈ P''`.
  have key_sub : ∀ (P'' : Ideal (TensorProduct R R' A)) [P''.IsPrime] [P''.LiesOver P],
      E - Algebra.TensorProduct.includeRight (δ E) ∈ P'' := by
    intro P'' _ _
    have hagree : (Ideal.Quotient.mkₐ R P'' : TensorProduct R R' A →ₐ[R] _)
        = (Ideal.Quotient.mkₐ R P'').comp (Algebra.TensorProduct.includeRight.comp δ) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      change (Ideal.Quotient.mkₐ R P'') (a ⊗ₜ[R] b)
          = (Ideal.Quotient.mkₐ R P'') (Algebra.TensorProduct.includeRight (δ (a ⊗ₜ[R] b)))
      rw [hδab, map_mul]
      have hir : Algebra.TensorProduct.includeRight ((algebraMap R A) (σ a))
          = (algebraMap R (TensorProduct R R' A)) (σ a) := by
        rw [← Algebra.TensorProduct.includeRight.commutes (σ a)]
      rw [hir, Algebra.TensorProduct.includeRight_apply]
      have key : a ⊗ₜ[R] b
          - (algebraMap R (TensorProduct R R' A)) (σ a) * (1 ⊗ₜ[R] b) ∈ P'' := by
        have ha : a ⊗ₜ[R] b
            = (algebraMap R' (TensorProduct R R' A) a) * (1 ⊗ₜ[R] b) := by
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
          simp
        have hb : (algebraMap R (TensorProduct R R' A)) (σ a)
            = algebraMap R' (TensorProduct R R' A) (algebraMap R R' (σ a)) := by
          rw [← IsScalarTower.algebraMap_apply]
        rw [ha, hb, ← sub_mul]
        apply Ideal.mul_mem_right
        rw [← map_sub]
        have hmemP : a - algebraMap R R' (σ a) ∈ P := hσP a
        have hlo : P = Ideal.under R' P'' := Ideal.LiesOver.over
        rw [hlo] at hmemP
        exact hmemP
      change (Ideal.Quotient.mkₐ R P'') (a ⊗ₜ[R] b)
          = (Ideal.Quotient.mkₐ R P'') ((algebraMap R (TensorProduct R R' A)) (σ a) * (1 ⊗ₜ[R] b))
      simp only [Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq]
      exact key
    have hfe := congrArg (fun (h : TensorProduct R R' A →ₐ[R] _) => h E) hagree
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hfe
    rw [Ideal.Quotient.eq] at hfe
    exact hfe
  refine ⟨δ E, hE.map δ, ?_, ?_⟩
  · -- g ∉ q : exactly `isolating_idempotent_per_point`.
    intro hg
    apply hEP'
    rw [← hcomap, Ideal.mem_comap] at hg
    have hgP' : Algebra.TensorProduct.includeRight (δ E) ∈ P' := hg
    have hsub : E - Algebra.TensorProduct.includeRight (δ E) ∈ P' := key_sub P'
    have := Ideal.add_mem P' hsub hgP'
    simpa using this
  · -- g ∈ q' for q' ≠ q : take P'' := comap δ q', a prime over (P, q'); use huniq to get E ∈ P'',
    -- then includeRight (δ E) ∈ P'' so δ E ∈ comap includeRight P'' = q'.
    intro q' _ _ hne
    -- P'' := comap of q' along δ : R' ⊗ A → A.  It is prime, lies over P, comaps to q'.
    set P'' : Ideal (TensorProduct R R' A) := Ideal.comap δ.toRingHom q' with hP''def
    have hP''prime : P''.IsPrime := Ideal.comap_isPrime δ.toRingHom q'
    -- δ ∘ includeRight = id_A  (δ (1 ⊗ a) = a).
    have hδι : ∀ a : A, δ (Algebra.TensorProduct.includeRight a) = a := by
      intro a
      rw [Algebra.TensorProduct.includeRight_apply, hδab]
      simp
    -- comap includeRight P'' = q'.
    have hP''comap : Ideal.comap Algebra.TensorProduct.includeRight.toRingHom P'' = q' := by
      ext a
      simp only [Ideal.mem_comap, hP''def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change δ (Algebra.TensorProduct.includeRight a) ∈ q' ↔ a ∈ q'
      rw [hδι]
    -- δ ∘ algebraMap R' = algebraMap R A ∘ σ  (δ (x ⊗ 1) = algebraMap R A (σ x)).
    have hδalg : ∀ x : R', δ (algebraMap R' (TensorProduct R R' A) x) = algebraMap R A (σ x) := by
      intro x
      have hx : algebraMap R' (TensorProduct R R' A) x = x ⊗ₜ[R] (1 : A) := by
        rw [Algebra.TensorProduct.algebraMap_apply]; simp
      rw [hx, hδab, mul_one]
    -- `σ x ∈ 𝔪 ↔ x ∈ P`, from residue compatibility `hσP`.
    have hσmem : ∀ x, σ x ∈ 𝔪 ↔ x ∈ P := fun x => by
      have hover : Ideal.comap (algebraMap R R') P = 𝔪 :=
        (Ideal.LiesOver.over (p := 𝔪) (P := P)).symm
      rw [← hover, Ideal.mem_comap]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simpa using P.add_mem (hσP x) h
      · simpa using P.sub_mem h (hσP x)
    -- P''.LiesOver P : comap (algebraMap R' (R'⊗A)) P'' = P.
    have hP''over : P''.LiesOver P := by
      refine ⟨Ideal.ext fun x => ?_⟩
      change x ∈ P ↔ δ (algebraMap R' (TensorProduct R R' A) x) ∈ q'
      have hqover : Ideal.comap (algebraMap R A) q' = 𝔪 :=
        (Ideal.LiesOver.over (p := 𝔪) (P := q')).symm
      rw [hδalg, ← hσmem, ← hqover, Ideal.mem_comap]
    have := hP''over
    -- huniq: P'' ≠ P' ⟹ E ∈ P''.
    have hP''ne : P'' ≠ P' := by
      intro h
      apply hne
      rw [← hcomap, ← hP''comap, h]
    have hEP'' : E ∈ P'' := by
      by_contra hEnot
      exact hP''ne (huniq P'' hP''prime hP''over hEnot)
    have hsub : E - Algebra.TensorProduct.includeRight (δ E) ∈ P'' := key_sub P''
    have hir : Algebra.TensorProduct.includeRight (δ E) ∈ P'' := by
      have := Ideal.sub_mem P'' hEP'' hsub
      simpa using this
    rw [← hP''comap, Ideal.mem_comap]
    exact hir

end
