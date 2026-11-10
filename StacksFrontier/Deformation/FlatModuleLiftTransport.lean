module

public import StacksFrontier.Deformation.FlatModuleLiftLocalization

/-!
# Transport of the two lifting problems along isomorphisms of the ambient rings

The comparison of lifting problems proved in
`StacksFrontier.Deformation.FlatModuleLiftLocalization` is stated at the *literal* base changes
`P' ⊗_{A'} A` and `Q' ⊗_{A'} A`, and packages a flat module lift as an isomorphism in
`ModuleCat` of a `ULift`ed module. The consumers of Stacks 0DZ2 — the proofs of Stacks 0DZ3 and
Stacks 0DZ7 — instead carry *abstract* rings `P` and `Q` with the kernel identities
`ker(P' → P) = ker(A' → A) · P'` and `ker(Q' → Q) = ker(A' → A) · Q'`, and package a lift as a
plain linear equivalence `P ⊗_{P'} M' ≃ M`. This file provides the dictionary.

Everything here is transport: not a single mathematical step of Stacks 0DZ2 is used or
reproved.

## Main results

* `Deformation.nonempty_moduleCatIso_iff_nonempty_linearEquiv`: the two packagings of a flat
  module lift agree.
* `Deformation.exists_flatModuleLift_congr`: the existence of an `A'`-flat `P'`-module lift
  transports along a ring isomorphism of the ambient ring over `P'`, together with a
  semilinear isomorphism of the module being lifted.
* `Deformation.ringEquiv_baseChange_of_ker_eq`: for two surjections out of `P'` with the same
  kernel, the induced isomorphism of the targets, over `P'`.
* `Deformation.nonempty_linearEquiv_tensor_congr`: base change of a module transports along a
  compatible pair of ring isomorphisms.
* `Deformation.bijective_quotientMap_of_surjective`: the descent of the hypothesis
  `P'/J' = Q'/J'Q'` to the quotients `P/J'P = Q/J'Q`.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Deformation

/-! ### The workhorse -/

/-- The inverse of an additive isomorphism semilinear for `ε` is semilinear for `ε.symm`. -/
private theorem symm_smul_of_smul {R S X Z : Type u} [CommRing R] [CommRing S]
    [AddCommGroup X] [Module R X] [AddCommGroup Z] [Module S Z]
    (ε : R ≃+* S) (α : X ≃+ Z) (hα : ∀ (r : R) (x : X), α (r • x) = ε r • α x)
    (s : S) (z : Z) : α.symm (s • z) = ε.symm s • α.symm z := by
  refine α.injective ?_
  rw [AddEquiv.apply_symm_apply, hα, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- **A linear equivalence transports along a pair of semilinear additive isomorphisms.** If
`α : X ≃ Z` and `β : Y ≃ W` are additive isomorphisms semilinear for a ring isomorphism
`ε : R ≃ S`, then an `R`-linear isomorphism `X ≃ Y` gives an `S`-linear isomorphism `Z ≃ W`. -/
theorem nonempty_linearEquiv_congr {R S X Y Z W : Type u} [CommRing R] [CommRing S]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module S Z] [AddCommGroup W] [Module S W]
    (ε : R ≃+* S) (α : X ≃+ Z) (hα : ∀ (r : R) (x : X), α (r • x) = ε r • α x)
    (β : Y ≃+ W) (hβ : ∀ (r : R) (y : Y), β (r • y) = ε r • β y)
    (h : Nonempty (X ≃ₗ[R] Y)) : Nonempty (Z ≃ₗ[S] W) := by
  obtain ⟨e⟩ := h
  refine ⟨{ (α.symm.trans (e.toAddEquiv.trans β)) with map_smul' := fun s z => ?_ }⟩
  change β (e (α.symm (s • z))) = s • β (e (α.symm z))
  rw [symm_smul_of_smul ε α hα, e.map_smul, hβ, RingEquiv.apply_symm_apply]

/-! ### The two packagings of a flat module lift -/

/-- The carrier of `ModuleCat.extendScalars` along `algebraMap P' R` is `R ⊗_{P'} M'`, but
the `P'`-algebra structure it uses on `R` is built from the ring map rather than taken from
the ambient instance. This is the comparison of the two. -/
private def extendScalarsLinearEquiv {P' : Type u} (R : Type u) [CommRing P'] [CommRing R]
    [Algebra P' R] (M' : ModuleCat.{u} P') :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap P' R)).obj M' ≃ₗ[R] R ⊗[P'] M' :=
  letI N := (ModuleCat.restrictScalars (algebraMap P' R)).obj (ModuleCat.of R R)
  letI : IsScalarTower P' R N :=
    ⟨fun x y z => by
      change (x • y) • z = algebraMap P' R x • (y • z)
      rw [Algebra.smul_def, mul_smul]⟩
  letI e : N ≃ₗ[R] R :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl P' M')

/-- **The two packagings of a flat module lift agree.** An isomorphism in `ModuleCat R` from
the extension of scalars of `M'` to the `ULift` of `M` is the same thing as an `R`-linear
isomorphism `R ⊗_{P'} M' ≃ M`. -/
theorem nonempty_moduleCatIso_iff_nonempty_linearEquiv {P' R : Type u} [CommRing P']
    [CommRing R] [Algebra P' R] (M' : Type u) [AddCommGroup M'] [Module P' M']
    (M : Type u) [AddCommGroup M] [Module R M] :
    Nonempty ((ModuleCat.extendScalars.{u, u, u} (algebraMap P' R)).obj
        (ModuleCat.of P' M') ≅ ModuleCat.of R (ULift.{u} M)) ↔
      Nonempty ((R ⊗[P'] M') ≃ₗ[R] M) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨((extendScalarsLinearEquiv R (ModuleCat.of P' M')).symm.trans
      e.toLinearEquiv).trans ULift.moduleEquiv⟩
  · rintro ⟨e⟩
    exact ⟨(((extendScalarsLinearEquiv R (ModuleCat.of P' M')).trans e).trans
      ULift.moduleEquiv.symm).toModuleIso⟩

/-- Base change `Q₀ ⊗_{P₀} M₀ ≃ Q ⊗_P M` along compatible semilinear isomorphisms. -/
private theorem exists_addEquiv_tensor_smul {P P₀ Q Q₀ : Type u} [CommRing P] [CommRing P₀]
    [CommRing Q] [CommRing Q₀] [Algebra P Q] [Algebra P₀ Q₀]
    (εP : P₀ ≃+* P) (εQ : Q₀ ≃+* Q)
    (hcomm : ∀ x : P₀, εQ (algebraMap P₀ Q₀ x) = algebraMap P Q (εP x))
    (M₀ : Type u) [AddCommGroup M₀] [Module P₀ M₀]
    (M : Type u) [AddCommGroup M] [Module P M]
    (φ : M₀ ≃+ M) (hφ : ∀ (x : P₀) (m : M₀), φ (x • m) = εP x • φ m) :
    ∃ α : (Q₀ ⊗[P₀] M₀) ≃+ (Q ⊗[P] M),
      ∀ (y : Q₀) (z : Q₀ ⊗[P₀] M₀), α (y • z) = εQ y • α z := by
  let : RingHomInvPair (εP : P₀ →+* P) (εP.symm : P →+* P₀) := RingHomInvPair.of_ringEquiv εP
  let : RingHomInvPair (εP.symm : P →+* P₀) (εP : P₀ →+* P) :=
    RingHomInvPair.of_ringEquiv εP.symm
  let tQ : Q₀ ≃ₛₗ[(εP : P₀ →+* P)] Q :=
    { εQ with
      map_smul' := fun x y => by
        change εQ (x • y) = εP x • εQ y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcomm] }
  let tM : M₀ ≃ₛₗ[(εP : P₀ →+* P)] M := { φ with map_smul' := fun x m => hφ x m }
  set t : (Q₀ ⊗[P₀] M₀) ≃ₛₗ[(εP : P₀ →+* P)] (Q ⊗[P] M) := TensorProduct.congr tQ tM with htdef
  have ht : ∀ (y : Q₀) (m : M₀), t (y ⊗ₜ[P₀] m) = (εQ y) ⊗ₜ[P] (φ m) := fun y m => by
    rw [htdef]
    exact TensorProduct.congr_tmul tQ tM y m
  refine ⟨t.toAddEquiv, fun y z => ?_⟩
  change t (y • z) = εQ y • t z
  induction z with
  | tmul q m =>
    rw [show y • q ⊗ₜ[P₀] m = (y * q) ⊗ₜ[P₀] m from rfl, ht, ht,
      show εQ y • (εQ q) ⊗ₜ[P] (φ m) = (εQ y * εQ q) ⊗ₜ[P] (φ m) from rfl, map_mul]
  | add z w hz hw => rw [smul_add, map_add, hz, hw, map_add, smul_add]

/-! ### Transport along a ring isomorphism over the presentation -/

section Congr

variable {A' P' R S : Type u} [CommRing A'] [CommRing P'] [CommRing R] [CommRing S]
  [Algebra A' P'] [Algebra P' R] [Algebra P' S]

/-- One direction of `Deformation.exists_flatModuleLift_congr`. -/
private theorem nonempty_linearEquiv_congr_of (ε : R ≃+* S)
    (hε : ∀ x : P', ε (algebraMap P' R x) = algebraMap P' S x)
    {M : Type u} [AddCommGroup M] [Module R M] {N : Type u} [AddCommGroup N] [Module S N]
    (φ : M ≃+ N) (hφ : ∀ (r : R) (m : M), φ (r • m) = ε r • φ m)
    (M' : Type u) [AddCommGroup M'] [Module P' M']
    (e : (R ⊗[P'] M') ≃ₗ[R] M) :
    Nonempty ((S ⊗[P'] M') ≃ₗ[S] N) :=
  have ⟨α, hα⟩ := exists_addEquiv_tensor_smul (RingEquiv.refl P') ε hε M' M' (AddEquiv.refl M')
    fun _ _ => rfl
  nonempty_linearEquiv_congr ε α hα φ hφ ⟨e⟩

/-- **Existence of an `A'`-flat `P'`-module lift transports along a ring isomorphism of the
ambient ring over `P'`.** If `ε : R ≃ S` is an isomorphism of `P'`-algebras and `φ : M ≃ N` is
an additive isomorphism semilinear for it, then `M` has an `A'`-flat `P'`-module lift exactly
when `N` does. -/
theorem exists_flatModuleLift_congr (ε : R ≃+* S)
    (hε : ∀ x : P', ε (algebraMap P' R x) = algebraMap P' S x)
    {M : Type u} [AddCommGroup M] [Module R M] {N : Type u} [AddCommGroup N] [Module S N]
    (φ : M ≃+ N) (hφ : ∀ (r : R) (m : M), φ (r • m) = ε r • φ m) :
    (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
        (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
        Nonempty ((R ⊗[P'] M') ≃ₗ[R] M)) ↔
      (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module P' N') (_ : Module A' N')
        (_ : IsScalarTower A' P' N'), Module.Flat A' N' ∧
        Nonempty ((S ⊗[P'] N') ≃ₗ[S] N)) := by
  have hεsymm : ∀ x : P', ε.symm (algebraMap P' S x) = algebraMap P' R x := fun x =>
    ε.symm_apply_eq.mpr (hε x).symm
  constructor
  · rintro ⟨M', _, _, _, _, hflat, ⟨e⟩⟩
    exact ⟨M', inferInstance, inferInstance, inferInstance, inferInstance, hflat,
      nonempty_linearEquiv_congr_of ε hε φ hφ M' e⟩
  · rintro ⟨N', _, _, _, _, hflat, ⟨e⟩⟩
    exact ⟨N', inferInstance, inferInstance, inferInstance, inferInstance, hflat,
      nonempty_linearEquiv_congr_of ε.symm hεsymm φ.symm
        (symm_smul_of_smul ε φ hφ) N' e⟩

/-- **`R ⊗_{P'} M'` transports along a ring isomorphism `R ≃ S` of `P'`-algebras.** -/
theorem exists_addEquiv_tensorCongr (ε : R ≃+* S)
    (hε : ∀ x : P', ε (algebraMap P' R x) = algebraMap P' S x)
    (M' : Type u) [AddCommGroup M'] [Module P' M'] :
    ∃ α : (R ⊗[P'] M') ≃+ (S ⊗[P'] M'),
      ∀ (r : R) (z : R ⊗[P'] M'), α (r • z) = ε r • α z :=
  exists_addEquiv_tensor_smul (RingEquiv.refl P') ε hε M' M' (AddEquiv.refl M') fun _ _ => rfl

end Congr

/-! ### The isomorphism of two base changes with the same kernel -/

/-- For two surjections `P' → R` and `P' → S` with the same kernel, the induced isomorphism
`R ≃ S`, which is one of `P'`-algebras. -/
theorem ringEquiv_baseChange_of_ker_eq {P' R S : Type u} [CommRing P'] [CommRing R]
    [CommRing S] [Algebra P' R] [Algebra P' S]
    (hsurjR : Function.Surjective (algebraMap P' R))
    (hsurjS : Function.Surjective (algebraMap P' S))
    (hker : RingHom.ker (algebraMap P' R) = RingHom.ker (algebraMap P' S)) :
    ∃ ε : R ≃+* S, ∀ x : P', ε (algebraMap P' R x) = algebraMap P' S x := by
  refine ⟨((RingHom.quotientKerEquivOfSurjective hsurjR).symm.trans
    (Ideal.quotEquivOfEq hker)).trans (RingHom.quotientKerEquivOfSurjective hsurjS),
    fun x => ?_⟩
  have h1 : (RingHom.quotientKerEquivOfSurjective hsurjR) (Ideal.Quotient.mk _ x) =
    algebraMap P' R x := rfl
  have h2 : (RingHom.quotientKerEquivOfSurjective hsurjS) (Ideal.Quotient.mk _ x) =
    algebraMap P' S x := rfl
  rw [← h1, RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.symm_apply_apply,
    show (Ideal.quotEquivOfEq hker) (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x from rfl, h2]

/-! ### Transport of a base change along a compatible pair of ring isomorphisms -/

section TensorCongr

variable {P P₀ Q Q₀ : Type u} [CommRing P] [CommRing P₀] [CommRing Q] [CommRing Q₀]
  [Algebra P Q] [Algebra P₀ Q₀]

/-- **Base change of a module transports along a compatible pair of ring isomorphisms.** -/
theorem nonempty_linearEquiv_tensor_congr (εP : P₀ ≃+* P) (εQ : Q₀ ≃+* Q)
    (hcomm : ∀ x : P₀, εQ (algebraMap P₀ Q₀ x) = algebraMap P Q (εP x))
    (M : Type u) [AddCommGroup M] [Module P M] [Module P₀ M]
    (hM : ∀ (x : P₀) (m : M), x • m = εP x • m)
    (N : Type u) [AddCommGroup N] [Module Q N] [Module Q₀ N]
    (hN : ∀ (y : Q₀) (n : N), y • n = εQ y • n)
    (e : (Q ⊗[P] M) ≃ₗ[Q] N) :
    Nonempty ((Q₀ ⊗[P₀] M) ≃ₗ[Q₀] N) := by
  obtain ⟨α, hα⟩ := exists_addEquiv_tensor_smul εP εQ hcomm M M (AddEquiv.refl M) hM
  exact nonempty_linearEquiv_congr εQ.symm α.symm (symm_smul_of_smul εQ α hα)
    (AddEquiv.refl N) (fun q n => by
      change q • n = εQ.symm q • n
      rw [hN (εQ.symm q) n, RingEquiv.apply_symm_apply]) ⟨e⟩

end TensorCongr

/-! ### Descent of the comparison of the two quotients -/

/-- **The hypothesis `P'/J' = Q'/J'Q'` descends to the quotients of `P'` and `Q'` by the
image of a further ideal.** Here `P` and `Q` are those quotients: the maps `P' → P` and
`Q' → Q` are surjective and the kernel of the second is generated by the image of the kernel
of the first. -/
theorem bijective_quotientMap_of_surjective {P' P Q' Q : Type u} [CommRing P'] [CommRing P]
    [CommRing Q'] [CommRing Q] [Algebra P' P] [Algebra Q' Q] [Algebra P' Q'] [Algebra P Q]
    [Algebra P' Q] [IsScalarTower P' P Q] [IsScalarTower P' Q' Q]
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hsurjQ : Function.Surjective (algebraMap Q' Q))
    (hker : RingHom.ker (algebraMap Q' Q) =
      (RingHom.ker (algebraMap P' P)).map (algebraMap P' Q'))
    (J' : Ideal P')
    (hquot : Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q'))
      (algebraMap P' Q') Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap
      ((J'.map (algebraMap P' P)).map (algebraMap P Q)) (algebraMap P Q)
      Ideal.le_comap_map) := by
  classical
  set K : Ideal P' := RingHom.ker (algebraMap P' P) with hKdef
  set L : Ideal P' := J' ⊔ K with hLdef
  have hJL : J' ≤ L := le_sup_left
  have hcomp : ∀ x : P', algebraMap P Q (algebraMap P' P x) =
      algebraMap Q' Q (algebraMap P' Q' x) := fun x => by
    rw [← IsScalarTower.algebraMap_apply P' P Q, ← IsScalarTower.algebraMap_apply P' Q' Q]
  have hmapcomp : ∀ I : Ideal P', (I.map (algebraMap P' P)).map (algebraMap P Q) =
      (I.map (algebraMap P' Q')).map (algebraMap Q' Q) := fun I => by
    rw [Ideal.map_map, Ideal.map_map]
    exact congrArg (fun f => Ideal.map f I) (RingHom.ext hcomp)
  -- the image of `L` in `P'/J'` goes to the image of `L·Q'` in `Q'/J'Q'`
  set σ := Ideal.quotientMap (J'.map (algebraMap P' Q')) (algebraMap P' Q')
    (Ideal.le_comap_map (f := algebraMap P' Q')) with hσdef
  have hσmk : ∀ x : P', σ (Ideal.Quotient.mk J' x) =
      Ideal.Quotient.mk (J'.map (algebraMap P' Q')) (algebraMap P' Q' x) :=
    fun _ => Ideal.quotientMap_mk
  have hσmap : (L.map (Ideal.Quotient.mk J')).map σ =
      (L.map (algebraMap P' Q')).map (Ideal.Quotient.mk (J'.map (algebraMap P' Q'))) := by
    rw [Ideal.map_map, Ideal.map_map]
    exact congrArg (fun f => Ideal.map f L) (RingHom.ext hσmk)
  -- membership in `L` is detected in `P'/J'`, and in `L·Q'` in `Q'/J'Q'`
  have hLmem : ∀ x : P', x ∈ L ↔ Ideal.Quotient.mk J' x ∈ L.map (Ideal.Quotient.mk J') := by
    intro x
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective (Ideal.Quotient.mk J')
      Ideal.Quotient.mk_surjective L, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hJL]
  have hLQmem : ∀ y : Q', y ∈ L.map (algebraMap P' Q') ↔
      Ideal.Quotient.mk (J'.map (algebraMap P' Q')) y ∈
        (L.map (algebraMap P' Q')).map
          (Ideal.Quotient.mk (J'.map (algebraMap P' Q'))) := by
    intro y
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective (Ideal.Quotient.mk _)
      Ideal.Quotient.mk_surjective (L.map (algebraMap P' Q')),
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr (Ideal.map_mono hJL)]
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · -- injectivity
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hab
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    obtain ⟨w, hw0⟩ := hsurjP (x - z)
    have hd : algebraMap Q' Q (algebraMap P' Q' w) ∈
        (J'.map (algebraMap P' Q')).map (algebraMap Q' Q) := by
      rw [← hcomp, hw0, ← hmapcomp, map_sub]
      exact hab
    -- `w` lands in `L·Q'`, hence `w ∈ L`
    have hw : algebraMap P' Q' w ∈ L.map (algebraMap P' Q') := by
      have h1 : algebraMap P' Q' w ∈ Ideal.comap (algebraMap Q' Q)
          ((J'.map (algebraMap P' Q')).map (algebraMap Q' Q)) := hd
      rw [Ideal.comap_map_of_surjective (algebraMap Q' Q) hsurjQ,
        ← RingHom.ker_eq_comap_bot, hker, ← Ideal.map_sup, ← hLdef] at h1
      exact h1
    rw [hLQmem, ← hσmk, ← hσmap] at hw
    obtain ⟨c, hc, hcw⟩ := (Ideal.mem_map_iff_of_surjective σ hquot.2).mp hw
    have hwL : w ∈ L := (hLmem w).mpr (hquot.1 hcw ▸ hc)
    rw [← hw0]
    obtain ⟨j, hj, c₀, hc₀, hjc⟩ := Submodule.mem_sup.mp hwL
    rw [← hjc, map_add,
      show algebraMap P' P c₀ = 0 from RingHom.mem_ker.mp (hKdef ▸ hc₀), add_zero]
    exact Ideal.mem_map_of_mem _ hj
  · -- surjectivity
    obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨y', rfl⟩ := hsurjQ y₀
    obtain ⟨a, ha⟩ := hquot.2 (Ideal.Quotient.mk (J'.map (algebraMap P' Q')) y')
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨Ideal.Quotient.mk _ (algebraMap P' P x'), ?_⟩
    rw [hσmk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
    rw [Ideal.quotientMap_mk, hcomp, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub, hmapcomp]
    exact Ideal.mem_map_of_mem _ ha

/-! ### Transport of a base change along a compatible pair of ring isomorphisms -/

/-- **`Q ⊗_P M` transports along a compatible pair of ring isomorphisms and a semilinear
isomorphism of `M`.** -/
theorem exists_addEquiv_tensorBaseChangeCongr {P P₀ Q Q₀ : Type u} [CommRing P] [CommRing P₀]
    [CommRing Q] [CommRing Q₀] [Algebra P Q] [Algebra P₀ Q₀]
    (εP : P₀ ≃+* P) (εQ : Q₀ ≃+* Q)
    (hcomm : ∀ x : P₀, εQ (algebraMap P₀ Q₀ x) = algebraMap P Q (εP x))
    (M₀ : Type u) [AddCommGroup M₀] [Module P₀ M₀]
    (M : Type u) [AddCommGroup M] [Module P M]
    (φ : M₀ ≃+ M) (hφ : ∀ (x : P₀) (m : M₀), φ (x • m) = εP x • φ m) :
    ∃ α : (Q₀ ⊗[P₀] M₀) ≃+ (Q ⊗[P] M),
      ∀ (y : Q₀) (z : Q₀ ⊗[P₀] M₀), α (y • z) = εQ y • α z :=
  exists_addEquiv_tensor_smul εP εQ hcomm M₀ M φ hφ

/-! ### Flatness and finiteness across a ring isomorphism -/

section Structure

variable {R S M N : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [Module R N]
  [IsScalarTower R S N]

/-- For a ring isomorphism `ε : R ≃ S` whose structure map is the algebra map, and an additive
isomorphism `M ≃ N` semilinear for it, `N` is the base change of `M`. -/
private def baseChangeEquivOfRingEquiv (ε : R ≃+* S)
    (hε : ∀ r : R, algebraMap R S r = ε r)
    (φ : M ≃+ N) (hφ : ∀ (r : R) (m : M), φ (r • m) = ε r • φ m) :
    (S ⊗[R] M) ≃ₗ[S] N := by
  have hsmul : ∀ (r : R) (n : N), r • n = ε r • n := fun r n => by
    rw [← hε, algebraMap_smul]
  have hsmulT : ∀ (s : S) (z : S ⊗[R] M), (ε.symm s) • z = s • z := fun s z => by
    have hz := algebraMap_smul (A := S) (R := R) (M := S ⊗[R] M) (ε.symm s) z
    rw [hε, RingEquiv.apply_symm_apply] at hz
    exact hz.symm
  have hsymm := symm_smul_of_smul ε φ hφ
  letI g : M →ₗ[R] N :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun r m => by
        change φ (r • m) = r • φ m
        rw [hφ, ← hsmul] }
  letI h : N →ₗ[S] S ⊗[R] M :=
    { toFun := fun n => (1 : S) ⊗ₜ[R] φ.symm n
      map_add' := fun n₁ n₂ => by
        show (1 : S) ⊗ₜ[R] φ.symm (n₁ + n₂) = _
        rw [map_add, TensorProduct.tmul_add]
      map_smul' := fun s n => by
        change (1 : S) ⊗ₜ[R] φ.symm (s • n) = s • ((1 : S) ⊗ₜ[R] φ.symm n)
        rw [hsymm, TensorProduct.tmul_smul, hsmulT] }
  refine LinearEquiv.ofLinearMap (g.liftBaseChange S) h ?_ ?_
  · refine LinearMap.ext fun n => ?_
    change g.liftBaseChange S ((1 : S) ⊗ₜ[R] φ.symm n) = n
    rw [LinearMap.liftBaseChange_tmul]
    change (1 : S) • φ (φ.symm n) = n
    rw [AddEquiv.apply_symm_apply, one_smul]
  · refine LinearMap.ext fun z => ?_
    change h (g.liftBaseChange S z) = z
    induction z with
    | tmul s m =>
      rw [LinearMap.liftBaseChange_tmul]
      change (1 : S) ⊗ₜ[R] φ.symm (s • φ m) = s ⊗ₜ[R] m
      rw [hsymm, AddEquiv.symm_apply_apply, TensorProduct.tmul_smul, hsmulT]
      change (s * 1) ⊗ₜ[R] m = s ⊗ₜ[R] m
      rw [mul_one]
    | add z w hz hw => rw [map_add, map_add, hz, hw]

end Structure

/-- **Flatness transports along a ring isomorphism.** -/
theorem flat_of_ringEquiv {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (ε : R ≃+* S) (φ : M ≃+ N) (hφ : ∀ (r : R) (m : M), φ (r • m) = ε r • φ m)
    (hflat : Module.Flat R M) : Module.Flat S N := by
  let : Algebra R S := (ε : R →+* S).toAlgebra
  let : Module R N := Module.compHom N (ε : R →+* S)
  let : IsScalarTower R S N := ⟨fun r s n => by
    change (algebraMap R S r * s) • n = ε r • (s • n)
    rw [mul_smul]
    rfl⟩
  exact Module.Flat.of_linearEquiv
    (baseChangeEquivOfRingEquiv ε (fun _ => rfl) φ hφ).symm

/-- **Finiteness transports along a ring isomorphism.** -/
theorem finite_of_ringEquiv {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (ε : R ≃+* S) (φ : M ≃+ N) (hφ : ∀ (r : R) (m : M), φ (r • m) = ε r • φ m)
    (hfin : Module.Finite R M) : Module.Finite S N := by
  let : Algebra R S := (ε : R →+* S).toAlgebra
  let : Module R N := Module.compHom N (ε : R →+* S)
  let : IsScalarTower R S N := ⟨fun r s n => by
    change (algebraMap R S r * s) • n = ε r • (s • n)
    rw [mul_smul]
    rfl⟩
  exact Module.Finite.equiv (baseChangeEquivOfRingEquiv ε (fun _ => rfl) φ hφ)

end Deformation

end
