module

import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Algebra.DirectLimit.Hom
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel.FiniteTypeModel

/-!
# Cartesian directed systems of finitely presented models

The colimit of a cartesian directed system of finitely presented algebras and modules is the base
change of every stage, and part (3) of Stacks 02JO: such a system with flat colimit is flat at all
sufficiently large stages.

## Main results

* `Module.Flat.DirectedModel.isPushout_colimit`, `Module.Flat.DirectedModel.isBaseChange_colimit`
* `Module.Flat.eventually_flat_of_directed`: Stacks 02JO (3).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-! ### Base change to the colimit of a cartesian directed system -/

section Colimit

variable {K P : Type*} [CommRing K] [AddCommGroup P] [Module K P]
  {J : Type*} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
  {G : J → Type*} [∀ j, CommRing (G j)] [∀ j, Algebra K (G j)]
  (f : ∀ j k, j ≤ k → G j →ₐ[K] G k) {R : Type*} [CommRing R] [Algebra K R]
  (g : ∀ j, G j →ₐ[K] R) (hg : ∀ j k (h : j ≤ k) x, g k (f j k h x) = g j x)
  (hs : ∀ r, ∃ j x, g j x = r)

omit [Nonempty J] in
include hg hs in
/-- Every element of `R ⊗[K] P` comes from some `G j ⊗[K] P`. -/
theorem TensorProduct.exists_rTensor_eq_of_directed (z : R ⊗[K] P) :
    ∃ j x, LinearMap.rTensor P (g j).toLinearMap x = z := by
  induction z using TensorProduct.inductionOn with
  | tmul r p =>
    obtain ⟨j, x, hx⟩ := hs r
    exact ⟨j, x ⊗ₜ p, by rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, hx]⟩
  | add z w hz hw =>
    obtain ⟨j, x, rfl⟩ := hz
    obtain ⟨k, y, rfl⟩ := hw
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
    have hc (i : J) (h : i ≤ l) : (g l).toLinearMap ∘ₗ (f i l h).toLinearMap = (g i).toLinearMap :=
      LinearMap.ext fun x => hg i l h x
    refine ⟨l, LinearMap.rTensor P (f j l hjl).toLinearMap x +
      LinearMap.rTensor P (f k l hkl).toLinearMap y, ?_⟩
    rw [map_add, ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply, hc, hc]

omit [Nonempty J] in
include hg hs in
/-- **Base change to the colimit of a cartesian system.** Let `R` be the directed colimit of
`K`-algebras `G j` and `Y` the directed colimit of abelian groups `Q j`, and suppose that each
`Q j` is identified with `G j ⊗[K] P`, compatibly with the transition maps. Then a map
`R ⊗[K] P → Y` compatible with these identifications is bijective. -/
theorem TensorProduct.bijective_of_directed {Q : J → Type*} [∀ j, AddCommGroup (Q j)]
    (q : ∀ j k, j ≤ k → Q j →+ Q k) {Y : Type*} [AddCommGroup Y] (ν : ∀ j, Q j →+ Y)
    (hνs : ∀ y, ∃ j x, ν j x = y) (hνz : ∀ j x, ν j x = 0 → ∃ k, ∃ h : j ≤ k, q j k h x = 0)
    (e : ∀ j, G j ⊗[K] P →+ Q j) (he : ∀ j, Function.Bijective (e j))
    (hqe : ∀ j k (h : j ≤ k) x,
      q j k h (e j x) = e k (LinearMap.rTensor P (f j k h).toLinearMap x))
    (c : R ⊗[K] P →+ Y) (hc : ∀ j x, c (LinearMap.rTensor P (g j).toLinearMap x) = ν j (e j x)) :
    Function.Bijective c := by
  refine ⟨(injective_iff_map_eq_zero c).mpr fun z hz => ?_, fun y => ?_⟩
  · obtain ⟨j, x, rfl⟩ := TensorProduct.exists_rTensor_eq_of_directed f g hg hs z
    obtain ⟨k, h, hk⟩ := hνz j (e j x) (by rw [← hc, hz])
    rw [hqe, ← map_zero (e k)] at hk
    have hc' : (g k).toLinearMap ∘ₗ (f j k h).toLinearMap = (g j).toLinearMap :=
      LinearMap.ext fun x => hg j k h x
    rw [← hc', LinearMap.rTensor_comp_apply, (he k).1 hk, map_zero]
  · obtain ⟨j, t, rfl⟩ := hνs y
    obtain ⟨x, rfl⟩ := (he j).2 t
    exact ⟨_, hc j x⟩

/-- The comparison map from the direct limit of a directed system of algebras to an algebra `R`
is bijective as soon as `R` is the colimit elementwise: every element comes from a stage, and an
element of a stage dying in `R` dies at a later stage. -/
theorem DirectLimit.Algebra.bijective_lift_of_directed {K : Type*} [CommRing K] {J : Type*}
    [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)] {G : J → Type*} [∀ j, CommRing (G j)]
    [∀ j, Algebra K (G j)] (f : ∀ j k, j ≤ k → G j →ₐ[K] G k)
    [DirectedSystem G fun j k h => f j k h] {R : Type*} [CommRing R] [Algebra K R]
    (g : ∀ j, G j →ₐ[K] R) (hg : ∀ j k (h : j ≤ k) x, g k (f j k h x) = g j x)
    (hs : ∀ r, ∃ j x, g j x = r) (hz : ∀ j x, g j x = 0 → ∃ k, ∃ h : j ≤ k, f j k h x = 0) :
    Function.Bijective (DirectLimit.Algebra.lift G f R g hg) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun z hz' => ?_, fun r => ?_⟩
  · obtain ⟨j, x, rfl⟩ := DirectLimit.exists_eq_mk f z
    rw [← DirectLimit.Algebra.of_apply, DirectLimit.Algebra.lift_of] at hz'
    obtain ⟨k, h, hk⟩ := hz j x hz'
    rw [← DirectLimit.Algebra.of_apply, ← DirectLimit.Algebra.of_f h, hk, map_zero]
  · obtain ⟨j, x, rfl⟩ := hs r
    exact ⟨_, DirectLimit.Algebra.lift_of (G := G) (f := f) R g hg j x⟩

end Colimit

/-! ### Comparison maps of base changes -/

section Comparison

variable {A R B C S : Type*} [CommRing A] [CommRing R] [CommRing B] [CommRing C] [CommRing S]
  [Algebra A R] [Algebra A B] [Algebra A C]

/-- If `B` and `C` both base change along `A → R` to `S`, then a map `u : C → B` compatible with
the maps to `S` is an isomorphism after base change to `R`. -/
theorem Algebra.TensorProduct.lTensor_bijective_of_isPushout [Algebra A S] [Algebra R S]
    [Algebra B S] [Algebra C S] [IsScalarTower A R S] [IsScalarTower A B S] [IsScalarTower A C S]
    [Algebra.IsPushout A R B S] [Algebra.IsPushout A R C S] (u : C →ₐ[A] B)
    (hu : ∀ y, algebraMap B S (u y) = algebraMap C S y) :
    Function.Bijective (Algebra.TensorProduct.lTensor (S := R) R u) := by
  have e : ⇑(Algebra.IsPushout.equiv A R B S) ∘ ⇑(Algebra.TensorProduct.lTensor (S := R) R u) =
      ⇑(Algebra.IsPushout.equiv A R C S) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul r y => simp [Algebra.IsPushout.equiv_tmul, hu]
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  rw [← Function.Bijective.of_comp_iff' (Algebra.IsPushout.equiv A R B S).bijective, e]
  exact (Algebra.IsPushout.equiv A R C S).bijective

/-- If `B' = R ⊗_A B` and `u : C → B` becomes an isomorphism after base change to `R`, then
`B' = R ⊗_A C` as well, along the composite `C → B → B'`. -/
theorem Algebra.IsPushout.of_lTensor_bijective [Algebra R S] [Algebra B S] [Algebra A S]
    [IsScalarTower A R S] [IsScalarTower A B S] [Algebra.IsPushout A R B S] [Algebra C S]
    [IsScalarTower A C S] (u : C →ₐ[A] B) (hu : ∀ y, algebraMap C S y = algebraMap B S (u y))
    (h : Function.Bijective (Algebra.TensorProduct.lTensor (S := R) R u)) :
    Algebra.IsPushout A R C S := by
  refine (Algebra.isPushout_iff _ _ _ _).mpr (IsBaseChange.of_equiv
    ((LinearEquiv.ofBijective (Algebra.TensorProduct.lTensor (S := R) R u).toLinearMap
      (by rwa [AlgHom.coe_toLinearMap])).trans
      (Algebra.IsPushout.equiv A R B S).toLinearEquiv) fun y => ?_)
  rw [LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply]
  simp [Algebra.IsPushout.equiv_tmul, hu]

end Comparison

section ModuleComparison

variable {T B S : Type*} [CommRing T] [CommRing B] [CommRing S] [Algebra T B] [Algebra B S]
  [Algebra T S] [IsScalarTower T B S]
  {P N M : Type*} [AddCommGroup P] [Module T P] [AddCommGroup N] [Module B N] [Module T N]
  [IsScalarTower T B N] [AddCommGroup M] [Module S M] [Module B M] [IsScalarTower B S M]
  [Module T M] [IsScalarTower T S M]

/-- If `M = S ⊗_T P` and `M = S ⊗_B N`, then a map `ψ : P → N` compatible with the maps to `M`
induces an isomorphism `S ⊗_B (B ⊗_T P) ≅ S ⊗_B N`. -/
theorem LinearMap.baseChange_liftBaseChange_bijective (ψ : P →ₗ[T] N) {f : P →ₗ[T] M}
    (hf : IsBaseChange S f) {g : N →ₗ[B] M} (hg : IsBaseChange S g)
    (hψ : ∀ x, g (ψ x) = f x) :
    Function.Bijective (LinearMap.baseChange S (ψ.liftBaseChange B)) := by
  have e : ⇑hg.equiv ∘ ⇑(LinearMap.baseChange S (ψ.liftBaseChange B)) =
      ⇑((TensorProduct.AlgebraTensorModule.cancelBaseChange T B S S P).trans hf.equiv) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul s y =>
      induction y using TensorProduct.inductionOn with
      | tmul c q => simp [IsBaseChange.equiv_tmul, ← hψ, TensorProduct.smul_tmul']
      | add y z hy hz =>
        simp only [Function.comp_apply, TensorProduct.tmul_add, map_add] at hy hz ⊢
        rw [hy, hz]
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  rw [← Function.Bijective.of_comp_iff' hg.equiv.bijective, e]
  exact LinearEquiv.bijective _

end ModuleComparison

/-! ### Cartesian directed systems of finitely presented models -/

namespace Module.Flat.DirectedModel

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
  {A B : ι → Type v} [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i, Algebra (A i) (B i)]
  (a : ∀ i j, i ≤ j → A i →+* A j) (b : ∀ i j, i ≤ j → B i →+* B j)
  [DirectedSystem A fun i j h => a i j h] [DirectedSystem B fun i j h => b i j h]
  (hab : ∀ i j (h : i ≤ j),
    (b i j h).comp (algebraMap (A i) (B i)) = (algebraMap (A j) (B j)).comp (a i j h))

/-- The tail `{j // i ≤ j}` of the index. -/
abbrev Tail (i : ι) : Type _ := { j // i ≤ j }

/-- The tail `Tail i` is nonempty, since it contains `i`. -/
instance (i : ι) : Nonempty (Tail i) := ⟨⟨i, le_rfl⟩⟩

/-- The tail `Tail i` of a directed preorder is directed. -/
instance (i : ι) : IsDirected (Tail i) (· ≤ ·) :=
  ⟨fun j k => let ⟨l, hjl, hkl⟩ := exists_ge_ge j.1 k.1
    ⟨⟨l, j.2.trans hjl⟩, hjl, hkl⟩⟩

/-- The algebra structure of a later stage `A j` over `A i`. -/
abbrev algebraA {i j : ι} (h : i ≤ j) : Algebra (A i) (A j) := (a i j h).toAlgebra

/-- The algebra structure of a later stage `B j` over `B i`. -/
abbrev algebraB {i j : ι} (h : i ≤ j) : Algebra (B i) (B j) := (b i j h).toAlgebra

/-- The algebra structure of a later stage `B j` over `A i`. -/
abbrev algebraAB {i j : ι} (h : i ≤ j) : Algebra (A i) (B j) :=
  ((algebraMap (A j) (B j)).comp (a i j h)).toAlgebra

/-- Restricting a directed system to a tail, along maps that agree with the original ones. -/
private theorem directedSystem_tail {κ : Type*} [Preorder κ] {G : κ → Type*}
    {f : ∀ ⦃i j⦄, i ≤ j → G i → G j} [DirectedSystem G f] {i : κ}
    {F : ∀ ⦃j k : Tail i⦄, j ≤ k → G j.1 → G k.1} (hF : ∀ j k (h : j ≤ k) x, F h x = f h x) :
    DirectedSystem (fun j : Tail i => G j.1) F :=
  ⟨fun _ x => by rw [hF]; exact (‹DirectedSystem G f›).map_self x,
    fun _ _ _ hjk hkl x => by rw [hF, hF, hF]; exact (‹DirectedSystem G f›).map_map hjk hkl x⟩

/-- Every element is represented by a stage in the tail, given representatives above `i`. -/
private theorem exists_tail_rep {κ : Type*} [Preorder κ] {G : κ → Type*} {X : Type*}
    {φ : ∀ i, G i → X} {i : κ} {r : X} (h : ∃ j, i ≤ j ∧ ∃ x, φ j x = r) :
    ∃ (j : Tail i) (x : G j.1), φ j.1 x = r :=
  let ⟨j, hij, x, hx⟩ := h
  ⟨⟨j, hij⟩, x, hx⟩

/-- An element of a stage in the tail which dies in the limit dies at a later stage of the tail. -/
private theorem exists_tail_zero {κ : Type*} [Preorder κ] {G : κ → Type*} {X : Type*} [Zero X]
    [∀ i, Zero (G i)] {φ : ∀ i, G i → X} {f : ∀ i j, i ≤ j → G i → G j} {i : κ}
    (hz : ∀ i x, φ i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) (j : Tail i) (x : G j.1)
    (hx : φ j.1 x = 0) : ∃ (k : Tail i) (h : j ≤ k), f j.1 k.1 h x = 0 :=
  let ⟨k, hk, hk'⟩ := hz j.1 x hx
  ⟨⟨k, j.2.trans hk⟩, hk, hk'⟩

section Ring

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (ρ : ∀ i, A i →+* R) (σ : ∀ i, B i →+* S)
  (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x)
  (hσ : ∀ i j (h : i ≤ j) x, σ j (b i j h x) = σ i x)

omit [Nonempty ι] [DirectedSystem A fun i j h => a i j h] in
include hρ in
/-- Every element of `R` comes from a stage above any given one. -/
theorem exists_ge_rep (hρs : ∀ r, ∃ i x, ρ i x = r) (i : ι) (r : R) :
    ∃ j, i ≤ j ∧ ∃ x, ρ j x = r := by
  obtain ⟨j, x, rfl⟩ := hρs r
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  exact ⟨k, hik, a j k hjk x, hρ j k hjk x⟩

omit [Nonempty ι] in
include hab hρ hσ in
/-- **The colimit is the base change of every stage.** If the transition squares of the system
are cartesian, then `S = R ⊗_{A i} B i`. -/
theorem isPushout_colimit
    (hpush : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
      (CommRingCat.ofHom (algebraMap (A i) (B i))) (CommRingCat.ofHom (algebraMap (A j) (B j)))
      (CommRingCat.ofHom (b i j h)))
    (hρσ : ∀ i, (σ i).comp (algebraMap (A i) (B i)) = (algebraMap R S).comp (ρ i))
    (hρs : ∀ r, ∃ i x, ρ i x = r) (hσs : ∀ s, ∃ i x, σ i x = s)
    (hσz : ∀ i x, σ i x = 0 → ∃ j, ∃ h : i ≤ j, b i j h x = 0)
    (i : ι) [Algebra (A i) R] [Algebra (B i) S] [Algebra (A i) S] [IsScalarTower (A i) R S]
    [IsScalarTower (A i) (B i) S] (hA : algebraMap (A i) R = ρ i)
    (hB : algebraMap (B i) S = σ i) :
    Algebra.IsPushout (A i) R (B i) S := by
  classical
  have hab' (j k : ι) (h : j ≤ k) (x : A j) :
      b j k h (algebraMap (A j) (B j) x) = algebraMap (A k) (B k) (a j k h x) :=
    DFunLike.congr_fun (hab j k h) x
  have hρσ' (j : ι) (x : A j) : σ j (algebraMap (A j) (B j) x) = algebraMap R S (ρ j x) :=
    DFunLike.congr_fun (hρσ j) x
  let (j : Tail i) : Algebra (A i) (A j.1) := algebraA a j.2
  let (j : Tail i) : Algebra (B i) (B j.1) := algebraB b j.2
  let (j : Tail i) : Algebra (A i) (B j.1) := algebraAB a j.2
  have (j : Tail i) : IsScalarTower (A i) (A j.1) (B j.1) := .of_algebraMap_eq' rfl
  have (j : Tail i) : IsScalarTower (A i) (B i) (B j.1) := .of_algebraMap_eq' (hab i j.1 j.2).symm
  have (j : Tail i) : Algebra.IsPushout (A i) (A j.1) (B i) (B j.1) :=
    CommRingCat.isPushout_iff_isPushout.mp (hpush i j.1 j.2)
  let f (j k : Tail i) (h : j ≤ k) : A j.1 →ₐ[A i] A k.1 :=
    { a j.1 k.1 h with
      commutes' := fun x => by
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
        exact DirectedSystem.map_map' (fun i j h => a i j h) j.2 h x }
  let g (j : Tail i) : A j.1 →ₐ[A i] R :=
    { ρ j.1 with
      commutes' := fun x => by
        rw [RingHom.algebraMap_toAlgebra, hA]
        exact hρ i j.1 j.2 x }
  let c := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId R S)
    (IsScalarTower.toAlgHom (A i) (B i) S)
  have hbij : Function.Bijective c := by
    refine TensorProduct.bijective_of_directed f g (fun j k h x => hρ j.1 k.1 h x)
      (fun r => ?_) (fun j k h => (b j.1 k.1 h).toAddMonoidHom)
      (fun j => (σ j.1).toAddMonoidHom) (fun s => ?_) (fun j x hx => ?_)
      (fun j => (Algebra.IsPushout.equiv (A i) (A j.1) (B i) (B j.1)).toAddMonoidHom)
      (fun j => (Algebra.IsPushout.equiv (A i) (A j.1) (B i) (B j.1)).bijective)
      (fun j k h x => ?_) c.toRingHom.toAddMonoidHom (fun j x => ?_)
    · exact exists_tail_rep (exists_ge_rep a ρ hρ hρs i r)
    · exact exists_tail_rep (exists_ge_rep b σ hσ hσs i s)
    · exact exists_tail_zero hσz j x hx
    · induction x using TensorProduct.inductionOn with
      | tmul x y =>
        simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra, f, hab',
          DirectedSystem.map_map' (fun i j h => b i j h)]
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
    · induction x using TensorProduct.inductionOn with
      | tmul x y =>
        simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra, c, g, hB, hσ, hρσ']
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  exact (Algebra.isPushout_iff _ _ _ _).mpr (IsBaseChange.of_equiv (LinearEquiv.ofBijective
    c.toLinearMap hbij) fun x => (LinearEquiv.ofBijective_apply _ _).trans (by simp [c]))

end Ring

section Module

variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module (B i) (N i)]
  (n : ∀ i j (h : i ≤ j), N i →ₛₗ[b i j h] N j) [DirectedSystem N fun i j h => n i j h]
  {i : ι}

/-- A transition map of the module system, as a linear map over the source stage. -/
abbrev transLinear {i j : ι} (h : i ≤ j) :
    letI := Module.compHom (N j) (b i j h)
    N i →ₗ[B i] N j :=
  letI := Module.compHom (N j) (b i j h)
  ⟨(n i j h).toAddHom, (n i j h).map_smulₛₗ⟩

/-- A leg of a cocone of modules, semilinear over a leg `σ i : B i → S` of a cocone of rings, as
a `B i`-linear map. -/
def legLinear {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M] {σ : B i →+* S}
    (ν : N i →ₛₗ[σ] M) [Algebra (B i) S] [Module (B i) M] [IsScalarTower (B i) S M]
    (hB : algebraMap (B i) S = σ) : N i →ₗ[B i] M where
  __ := ν
  map_smul' c x := by
    rw [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_smulₛₗ, RingHom.id_apply,
      ← algebraMap_smul S c (ν x), hB]

omit [Nonempty ι] in
/-- **The colimit module is the base change of every stage.** If the transition maps of the
module system are base changes, then `M = S ⊗_{B i} N i`. -/
theorem isBaseChange_colimit
    (hbc : ∀ i j (h : i ≤ j), letI := algebraB b h
      letI := Module.compHom (N j) (b i j h)
      haveI : IsScalarTower (B i) (B j) (N j) := .of_algebraMap_smul fun _ _ => rfl
      IsBaseChange (B j) (transLinear b n h))
    {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M] (σ : ∀ i, B i →+* S)
    (ν : ∀ i, N i →ₛₗ[σ i] M) (hσ : ∀ i j (h : i ≤ j) x, σ j (b i j h x) = σ i x)
    (hν : ∀ i j (h : i ≤ j) x, ν j (n i j h x) = ν i x)
    (hσs : ∀ s, ∃ i x, σ i x = s) (hνs : ∀ m, ∃ i x, ν i x = m)
    (hνz : ∀ i x, ν i x = 0 → ∃ j, ∃ h : i ≤ j, n i j h x = 0)
    (i : ι) [Algebra (B i) S] [Module (B i) M] [IsScalarTower (B i) S M]
    (hB : algebraMap (B i) S = σ i) :
    IsBaseChange S (legLinear (ν i) hB) := by
  classical
  let (j : Tail i) : Algebra (B i) (B j.1) := algebraB b j.2
  let (j : Tail i) : Module (B i) (N j.1) := Module.compHom (N j.1) (b i j.1 j.2)
  have (j : Tail i) : IsScalarTower (B i) (B j.1) (N j.1) := .of_algebraMap_smul fun _ _ => rfl
  have hbc' (j : Tail i) : IsBaseChange (B j.1) (transLinear b n j.2) := hbc i j.1 j.2
  let f (j k : Tail i) (h : j ≤ k) : B j.1 →ₐ[B i] B k.1 :=
    { b j.1 k.1 h with
      commutes' := fun x => by
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
        exact DirectedSystem.map_map' (fun i j h => b i j h) j.2 h x }
  let g (j : Tail i) : B j.1 →ₐ[B i] S :=
    { σ j.1 with
      commutes' := fun x => by
        rw [RingHom.algebraMap_toAlgebra, hB]
        exact hσ i j.1 j.2 x }
  let c := (legLinear (ν i) hB).liftBaseChange S
  have hbij : Function.Bijective c := by
    refine TensorProduct.bijective_of_directed f g (fun j k h x => hσ j.1 k.1 h x)
      (fun s => ?_) (fun j k h => (n j.1 k.1 h).toAddMonoidHom)
      (fun j => (ν j.1).toAddMonoidHom) (fun m => ?_) (fun j x hx => ?_)
      (fun j => (hbc' j).equiv.toLinearMap.toAddMonoidHom) (fun j => (hbc' j).equiv.bijective)
      (fun j k h x => ?_) c.toAddMonoidHom (fun j x => ?_)
    · exact exists_tail_rep (exists_ge_rep b σ hσ hσs i s)
    · obtain ⟨j, x, rfl⟩ := hνs m
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      exact ⟨⟨k, hik⟩, n j k hjk x, hν j k hjk x⟩
    · exact exists_tail_zero hνz j x hx
    · induction x using TensorProduct.inductionOn with
      | tmul x y =>
        simp [IsBaseChange.equiv_tmul, f, DirectedSystem.map_map' (fun i j h => n i j h)]
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
    · induction x using TensorProduct.inductionOn with
      | tmul x y => simp [IsBaseChange.equiv_tmul, c, g, legLinear, hν]
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective c hbij) fun x =>
    (LinearEquiv.ofBijective_apply _ _).trans (by simp [c])

omit [Nonempty ι] [IsDirected ι (· ≤ ·)] [DirectedSystem A fun i j h => a i j h]
  [DirectedSystem B fun i j h => b i j h] [DirectedSystem N fun i j h => n i j h] in
include hab in
/-- **Flatness propagates up a cartesian system.** If `N i` is flat over `A i`, then `N j` is
flat over `A j` for every `j ≥ i`. -/
theorem flat_of_le
    (hpush : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
      (CommRingCat.ofHom (algebraMap (A i) (B i))) (CommRingCat.ofHom (algebraMap (A j) (B j)))
      (CommRingCat.ofHom (b i j h)))
    (hbc : ∀ i j (h : i ≤ j), letI := algebraB b h
      letI := Module.compHom (N j) (b i j h)
      haveI : IsScalarTower (B i) (B j) (N j) := .of_algebraMap_smul fun _ _ => rfl
      IsBaseChange (B j) (transLinear b n h))
    {j : ι} (h : i ≤ j)
    (hi : letI := Module.compHom (N i) (algebraMap (A i) (B i)); Module.Flat (A i) (N i)) :
    letI := Module.compHom (N j) (algebraMap (A j) (B j)); Module.Flat (A j) (N j) := by
  let := algebraA a h
  let := algebraB b h
  let := algebraAB (B := B) a h
  have : IsScalarTower (A i) (A j) (B j) := .of_algebraMap_eq' rfl
  have : IsScalarTower (A i) (B i) (B j) := .of_algebraMap_eq' (hab i j h).symm
  have : Algebra.IsPushout (A i) (A j) (B i) (B j) :=
    CommRingCat.isPushout_iff_isPushout.mp (hpush i j h)
  let : Module (A i) (N i) := Module.compHom (N i) (algebraMap (A i) (B i))
  have : IsScalarTower (A i) (B i) (N i) := .of_algebraMap_smul fun _ _ => rfl
  let : Module (A j) (N j) := Module.compHom (N j) (algebraMap (A j) (B j))
  have : IsScalarTower (A j) (B j) (N j) := .of_algebraMap_smul fun _ _ => rfl
  let : Module (B i) (N j) := Module.compHom (N j) (b i j h)
  have : IsScalarTower (B i) (B j) (N j) := .of_algebraMap_smul fun _ _ => rfl
  exact Module.Flat.of_linearEquiv (((hbc i j h).equiv.restrictScalars (A j)).symm.trans
    (Algebra.IsPushout.cancelBaseChange (A i) (A j) (B i) (B j) (N i)))


section Stage

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (ρ : ∀ i, A i →+* R) (σ : ∀ i, B i →+* S)
  (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x)
  (hσ : ∀ i j (h : i ≤ j) x, σ j (b i j h x) = σ i x)
  (hρσ : ∀ i, (σ i).comp (algebraMap (A i) (B i)) = (algebraMap R S).comp (ρ i))
  (hσs : ∀ s, ∃ i x, σ i x = s) (hσz : ∀ i x, σ i x = 0 → ∃ j, ∃ h : i ≤ j, b i j h x = 0)

/-- `χ : T → B μ` exhibits `B μ` as the base change `A μ ⊗_{A i₀} T`. The two scalar towers,
propositions determined by the algebra structures, are quantified over. -/
def IsStageModel {i₀ μ : ι} (h : i₀ ≤ μ) (T : Type*) [CommRing T] [Algebra (A i₀) T]
    (χ : T →+* B μ) : Prop :=
  letI := algebraA a h
  letI := algebraAB (B := B) a h
  letI := χ.toAlgebra
  ∀ [IsScalarTower (A i₀) (A μ) (B μ)] [IsScalarTower (A i₀) T (B μ)],
    Algebra.IsPushout (A i₀) (A μ) T (B μ)

omit [Nonempty ι] [DirectedSystem N fun i j h => n i j h] in
include hab hρ hσ hρσ hσs hσz in
/-- **The structure map of a model lifts to a stage.** If `T` is a finitely presented
`A i₀`-algebra over `S`, then `T → S` factors through some `B i₁`, compatibly with `A i₀`. -/
theorem exists_lift_stage {i₀ : ι} (T : Type*) [CommRing T] [Algebra (A i₀) T] [Algebra T S]
    [Algebra (A i₀) S] [IsScalarTower (A i₀) T S] [Algebra.FinitePresentation (A i₀) T]
    (hAS : ∀ x, algebraMap (A i₀) S x = algebraMap R S (ρ i₀ x)) :
    ∃ j, ∃ h : i₀ ≤ j, ∃ χ : T →+* B j, (σ j).comp χ = algebraMap T S ∧
      χ.comp (algebraMap (A i₀) T) = (algebraMap (A j) (B j)).comp (a i₀ j h) := by
  have hab' (j k : ι) (h : j ≤ k) (x : A j) :
      b j k h (algebraMap (A j) (B j) x) = algebraMap (A k) (B k) (a j k h x) :=
    DFunLike.congr_fun (hab j k h) x
  have hρσ' (j : ι) (x : A j) : σ j (algebraMap (A j) (B j) x) = algebraMap R S (ρ j x) :=
    DFunLike.congr_fun (hρσ j) x
  -- Step 2: the structure map `T → S` factors through some `B i₁`.
  let (j : Tail i₀) : Algebra (A i₀) (B j.1) := algebraAB (B := B) a j.2
  let fB (j k : Tail i₀) (h : j ≤ k) : B j.1 →ₐ[A i₀] B k.1 :=
    { b j.1 k.1 h with
      commutes' := fun x => by
        simp [RingHom.algebraMap_toAlgebra, hab', DirectedSystem.map_map' (fun i j h => a i j h)] }
  let gB (j : Tail i₀) : B j.1 →ₐ[A i₀] S :=
    { σ j.1 with
      commutes' := fun x => by
        rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, hAS]
        exact (hρσ' j.1 _).trans (congrArg _ (hρ i₀ j.1 j.2 x)) }
  have : DirectedSystem (fun j : Tail i₀ => B j.1) fun j k h => ⇑(fB j k h) :=
    directedSystem_tail (f := fun i j h => b i j h) fun _ _ _ _ => rfl
  obtain ⟨i₁, χ, hχ⟩ := AlgHom.exists_comp_eq_of_finitePresentation fB gB
    (fun j k h x => hσ j.1 k.1 h x)
    (fun s => exists_tail_rep (exists_ge_rep b σ hσ hσs i₀ s)) (exists_tail_zero hσz)
    (IsScalarTower.toAlgHom (A i₀) T S)
  refine ⟨i₁.1, i₁.2, χ.toRingHom, RingHom.ext fun t => DFunLike.congr_fun hχ t,
    RingHom.ext fun x => ?_⟩
  simp [RingHom.algebraMap_toAlgebra]

omit [Nonempty ι] [DirectedSystem N fun i j h => n i j h] in
include hρ in
/-- A map of `A i₁`-algebras `u : C → B i₁`, with `C` of finite type and `B i₁` of finite
presentation, which becomes an isomorphism after base change to `R` becomes one after base change
to some `A μ` (Stacks 05N8). -/
theorem exists_lTensor_bijective (hρs : ∀ r, ∃ i x, ρ i x = r)
    (hρz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0) {i₁ : ι} {C : Type*} [CommRing C]
    [Algebra (A i₁) C] [Algebra.FiniteType (A i₁) C] [Algebra.FinitePresentation (A i₁) (B i₁)]
    (u : C →ₐ[A i₁] B i₁)
    (hL : letI := (ρ i₁).toAlgebra
      Function.Bijective (Algebra.TensorProduct.lTensor (S := R) R u)) :
    ∃ μ, ∃ h : i₁ ≤ μ, letI := algebraA a h
      Function.Bijective (Algebra.TensorProduct.lTensor (S := A μ) (A μ) u) := by
  let : Algebra (A i₁) R := (ρ i₁).toAlgebra
  let (j : Tail i₁) : Algebra (A i₁) (A j.1) := algebraA a j.2
  let fA (j k : Tail i₁) (h : j ≤ k) : A j.1 →ₐ[A i₁] A k.1 :=
    { a j.1 k.1 h with
      commutes' := fun x => by
        simp [RingHom.algebraMap_toAlgebra, DirectedSystem.map_map' (fun i j h => a i j h)] }
  let gA (j : Tail i₁) : A j.1 →ₐ[A i₁] R :=
    { ρ j.1 with
      commutes' := fun x => by simp [RingHom.algebraMap_toAlgebra, hρ] }
  have : DirectedSystem (fun j : Tail i₁ => A j.1) fun j k h => ⇑(fA j k h) :=
    directedSystem_tail (f := fun i j h => a i j h) fun _ _ _ _ => rfl
  have hgA (j k : Tail i₁) (h : j ≤ k) (x : A j.1) : gA k (fA j k h x) = gA j x :=
    hρ j.1 k.1 h x
  have hR := DirectLimit.Algebra.bijective_lift_of_directed fA gA hgA
    (fun r => exists_tail_rep (exists_ge_rep a ρ hρ hρs i₁ r)) (exists_tail_zero hρz)
  obtain ⟨μ, hμ⟩ := (Algebra.TensorProduct.exists_of_directLimit fA gA hgA hR).2.2.2
    inferInstance inferInstance u hL
  exact ⟨μ.1, μ.2, hμ⟩

omit [Nonempty ι] [DirectedSystem N fun i j h => n i j h] in
include hσ hσs hσz in
/-- A map `u : B ν₁ ⊗_T P → N ν₁`, with `P` finitely presented over `T`, which becomes an
isomorphism after base change to `S` becomes one after base change to some `B ν` (Stacks 05LI). -/
theorem exists_baseChange_bijective (hfpN : ∀ i, Module.FinitePresentation (B i) (N i))
    {ν₁ : ι} {T : Type*} [CommRing T] [Algebra T (B ν₁)] (P : Type*) [AddCommGroup P]
    [Module T P] [Module.FinitePresentation T P] (uM : B ν₁ ⊗[T] P →ₗ[B ν₁] N ν₁)
    (hS : letI := (σ ν₁).toAlgebra; Function.Bijective (LinearMap.baseChange S uM)) :
    ∃ ν, ∃ h : ν₁ ≤ ν, letI := algebraB b h
      Function.Bijective (LinearMap.baseChange (B ν) uM) := by
  let (j : Tail ν₁) : Algebra (B ν₁) (B j.1) := algebraB b j.2
  let (j : Tail ν₁) : Algebra (B j.1) S := (σ j.1).toAlgebra
  let : Algebra (B ν₁) S := (σ ν₁).toAlgebra
  have (j : Tail ν₁) : IsScalarTower (B ν₁) (B j.1) S :=
    .of_algebraMap_eq fun x => (hσ ν₁ j.1 j.2 x).symm
  let fN (j k : Tail ν₁) (h : j ≤ k) : B j.1 →ₐ[B ν₁] B k.1 :=
    { b j.1 k.1 h with
      commutes' := fun x => by
        simp [RingHom.algebraMap_toAlgebra, DirectedSystem.map_map' (fun i j h => b i j h)] }
  have : DirectedSystem (fun j : Tail ν₁ => B j.1) fun j k h => ⇑(fN j k h) :=
    directedSystem_tail (f := fun i j h => b i j h) fun _ _ _ _ => rfl
  have hfN (j k : Tail ν₁) (h : j ≤ k) (x : B j.1) :
      algebraMap (B k.1) S (fN j k h x) = algebraMap (B j.1) S x := hσ j.1 k.1 h x
  have hsN (s : S) : ∃ (j : Tail ν₁) (x : B j.1), algebraMap (B j.1) S x = s :=
    exists_tail_rep (exists_ge_rep b σ hσ hσs ν₁ s)
  have hzN (j : Tail ν₁) (x : B j.1) (hx : algebraMap (B j.1) S x = 0) :
      ∃ (k : Tail ν₁) (h : j ≤ k), fN j k h x = 0 :=
    exists_tail_zero hσz j x hx
  have := hfpN ν₁
  obtain ⟨ν, hν⟩ := Stacks.FinitePresentation.ColimitDescent.statement_four (fun j k (h : j ≤ k) =>
    fN j k h)
    (fun j => IsScalarTower.toAlgHom (B ν₁) (B j.1) S)
    ⟨fun _ x => DirectedSystem.map_self' (fun i j h => b i j h) x,
      fun _ _ _ hjk hkl x => DirectedSystem.map_map' (fun i j h => b i j h) hjk hkl x⟩
    (fun j k h x => hfN j k h x)
    (Stacks.ColimitPresentation.FPModules.isModuleColimit fN hfN hsN hzN _)
    (Stacks.ColimitPresentation.FPModules.isModuleColimit fN hfN hsN hzN _)
    inferInstance inferInstance uM hS
  exact ⟨ν.1, ν.2, hν⟩

omit [Nonempty ι] [DirectedSystem N fun i j h => n i j h] in
include hab hρ hσ hρσ hσs hσz in
/-- **A lifted model is a model at a later stage.** If `χ : T → B i₁` lifts the structure map
of a finitely presented model `T` of `S` over `A i₀`, then `B μ = A μ ⊗_{A i₀} T` for some
`μ ≥ i₁` (Stacks 05N8). -/
theorem exists_isStageModel
    (hρs : ∀ r, ∃ i x, ρ i x = r) (hρz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0)
    (hpush : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
      (CommRingCat.ofHom (algebraMap (A i) (B i))) (CommRingCat.ofHom (algebraMap (A j) (B j)))
      (CommRingCat.ofHom (b i j h)))
    (hfp : ∀ i, Algebra.FinitePresentation (A i) (B i))
    {i₀ : ι} (T : Type*) [CommRing T] [Algebra (A i₀) T] [Algebra T S]
    [Algebra (A i₀) S] [IsScalarTower (A i₀) T S] [Algebra.FinitePresentation (A i₀) T]
    [Algebra (A i₀) R] [IsScalarTower (A i₀) R S] [Algebra.IsPushout (A i₀) R T S]
    (hA : algebraMap (A i₀) R = ρ i₀) {i₁ : ι} (h₁ : i₀ ≤ i₁) (χ : T →+* B i₁)
    (hχS : (σ i₁).comp χ = algebraMap T S)
    (hχA : χ.comp (algebraMap (A i₀) T) = (algebraMap (A i₁) (B i₁)).comp (a i₀ i₁ h₁)) :
    ∃ μ, ∃ h : i₁ ≤ μ, IsStageModel a (h₁.trans h) T ((b i₁ μ h).comp χ) := by
  classical
  have hab' (j k : ι) (h : j ≤ k) (x : A j) :
      b j k h (algebraMap (A j) (B j) x) = algebraMap (A k) (B k) (a j k h x) :=
    DFunLike.congr_fun (hab j k h) x
  have hρσ' (j : ι) (x : A j) : σ j (algebraMap (A j) (B j) x) = algebraMap R S (ρ j x) :=
    DFunLike.congr_fun (hρσ j) x
  have hAS (x : A i₀) : algebraMap (A i₀) S x = algebraMap R S (ρ i₀ x) := by
    rw [IsScalarTower.algebraMap_apply (A i₀) R S x, hA]
  let : Algebra (A i₀) (B i₁) := algebraAB (B := B) a h₁
  have hχA' (x : A i₀) : χ (algebraMap (A i₀) T x) = algebraMap (A i₁) (B i₁) (a i₀ i₁ h₁ x) :=
    DFunLike.congr_fun hχA x
  let χA : T →ₐ[A i₀] B i₁ :=
    { χ with
      commutes' := fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun hχA x }
  -- Step 3: the comparison map `A i₁ ⊗_{A i₀} T → B i₁`.
  let : Algebra (A i₀) (A i₁) := algebraA a h₁
  have : IsScalarTower (A i₀) (A i₁) (B i₁) := .of_algebraMap_eq' rfl
  let u : A i₁ ⊗[A i₀] T →ₐ[A i₁] B i₁ :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId (A i₁) (B i₁)) χA
  -- Step 4: `u` is an isomorphism after base change to `R`.
  let : Algebra (A i₁) R := (ρ i₁).toAlgebra
  let : Algebra (A i₁) S := ((algebraMap R S).comp (ρ i₁)).toAlgebra
  have : IsScalarTower (A i₁) R S := .of_algebraMap_eq' rfl
  let : Algebra (B i₁) S := (σ i₁).toAlgebra
  have : IsScalarTower (A i₁) (B i₁) S := .of_algebraMap_eq' (hρσ i₁).symm
  have hpB : Algebra.IsPushout (A i₁) R (B i₁) S :=
    isPushout_colimit a b hab ρ σ hρ hσ hpush hρσ hρs hσs hσz i₁ rfl rfl
  have : IsScalarTower (A i₀) (A i₁) R := .of_algebraMap_eq fun x => by
    rw [hA]
    exact (hρ i₀ i₁ h₁ x).symm
  have : IsScalarTower (A i₀) (A i₁) S := .of_algebraMap_eq fun x => by
    rw [hAS, RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.algebraMap_toAlgebra, hρ]
  let : Algebra (A i₁ ⊗[A i₀] T) S := (Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId (A i₁) S) (IsScalarTower.toAlgHom (A i₀) T S)).toRingHom.toAlgebra
  have : IsScalarTower (A i₁) (A i₁ ⊗[A i₀] T) S := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have : IsScalarTower T (A i₁ ⊗[A i₀] T) S := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower (A i₀) (A i₁ ⊗[A i₀] T) S := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (A i₀) T (A i₁ ⊗[A i₀] T),
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hpT : Algebra.IsPushout (A i₁) R (A i₁ ⊗[A i₀] T) S :=
    (Algebra.IsPushout.comp_iff (A i₀) (A i₁) T (A i₁ ⊗[A i₀] T)).mp inferInstance
  have hu (y : A i₁ ⊗[A i₀] T) :
      algebraMap (B i₁) S (u y) = algebraMap (A i₁ ⊗[A i₀] T) S y := by
    induction y using TensorProduct.inductionOn with
    | tmul x t =>
      have ht := DFunLike.congr_fun hχS t
      simp only [RingHom.comp_apply] at ht
      simp [u, χA, RingHom.algebraMap_toAlgebra, hρσ', ← ht]
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  have hL := Algebra.TensorProduct.lTensor_bijective_of_isPushout (R := R) (S := S) u hu
  -- Step 5: so `u` is an isomorphism after base change to some `A μ` (Stacks 05N8).
  have := hfp i₁
  obtain ⟨μ, hμ1, hμ⟩ := exists_lTensor_bijective a ρ hρ hρs hρz u hL
  -- Step 6: `B μ = A μ ⊗_{A i₀} T`.
  let : Algebra (A i₁) (A μ) := algebraA a hμ1
  have hi₀μ : i₀ ≤ μ := h₁.trans hμ1
  let : Algebra (B i₁) (B μ) := algebraB b hμ1
  let : Algebra (A i₁) (B μ) := algebraAB (B := B) a hμ1
  have : IsScalarTower (A i₁) (A μ) (B μ) := .of_algebraMap_eq' rfl
  have : IsScalarTower (A i₁) (B i₁) (B μ) := .of_algebraMap_eq' (hab i₁ μ hμ1).symm
  have : Algebra.IsPushout (A i₁) (A μ) (B i₁) (B μ) :=
    CommRingCat.isPushout_iff_isPushout.mp (hpush i₁ μ hμ1)
  let : Algebra (A i₁ ⊗[A i₀] T) (B μ) := ((b i₁ μ hμ1).comp u.toRingHom).toAlgebra
  have : IsScalarTower (A i₁) (A i₁ ⊗[A i₀] T) (B μ) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, u, hab']
  have hp1 := Algebra.IsPushout.of_lTensor_bijective (R := A μ) (S := B μ) u (fun _ => rfl) hμ
  let : Algebra (A i₀) (A μ) := algebraA a hi₀μ
  let : Algebra (A i₀) (B μ) := algebraAB (B := B) a hi₀μ
  let : Algebra T (B μ) := ((b i₁ μ hμ1).comp χ).toAlgebra
  have : IsScalarTower (A i₀) (A μ) (B μ) := .of_algebraMap_eq' rfl
  have : IsScalarTower (A i₀) (A i₁) (A μ) := .of_algebraMap_eq fun x =>
    (DirectedSystem.map_map' (fun i j h => a i j h) h₁ hμ1 x).symm
  have : IsScalarTower (A i₀) T (B μ) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, hχA', hab', DirectedSystem.map_map' (fun i j h => a i j h)]
  have : IsScalarTower T (A i₁ ⊗[A i₀] T) (B μ) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, u, χA]
  have : IsScalarTower (A i₀) (A i₁ ⊗[A i₀] T) (B μ) := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (A i₀) T (A i₁ ⊗[A i₀] T),
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hp2 : Algebra.IsPushout (A i₀) (A μ) T (B μ) :=
    (Algebra.IsPushout.comp_iff (A i₀) (A i₁) T (A i₁ ⊗[A i₀] T)).mpr hp1
  refine ⟨μ, hμ1, ?_⟩
  unfold IsStageModel
  intro _ _
  exact hp2

omit [Nonempty ι] in
include hab hσ hσs hσz in
/-- **A flat model at a stage makes a later stage flat.** If `B μ = A μ ⊗_{A i₀} T` and `M` is
the base change of a finitely presented `T`-module `P` flat over `A i₀`, then `N ν` is flat over
`A ν` for some `ν ≥ μ` (Stacks 05LI). -/
theorem exists_flat_of_isStageModel {M : Type*} [AddCommGroup M] [Module S M]
    (ν : ∀ i, N i →ₛₗ[σ i] M) (hν : ∀ i j (h : i ≤ j) x, ν j (n i j h x) = ν i x)
    (hνs : ∀ m, ∃ i x, ν i x = m) (hνz : ∀ i x, ν i x = 0 → ∃ j, ∃ h : i ≤ j, n i j h x = 0)
    (hbc : ∀ i j (h : i ≤ j), letI := algebraB b h
      letI := Module.compHom (N j) (b i j h)
      haveI : IsScalarTower (B i) (B j) (N j) := .of_algebraMap_smul fun _ _ => rfl
      IsBaseChange (B j) (transLinear b n h))
    (hfpN : ∀ i, Module.FinitePresentation (B i) (N i))
    (hpush : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
      (CommRingCat.ofHom (algebraMap (A i) (B i))) (CommRingCat.ofHom (algebraMap (A j) (B j)))
      (CommRingCat.ofHom (b i j h)))
    {i₀ : ι} (T : Type*) [CommRing T] [Algebra (A i₀) T] [Algebra T S]
    (P : Type*) [AddCommGroup P] [Module T P] [Module (A i₀) P] [IsScalarTower (A i₀) T P]
    [Module.FinitePresentation T P] [Module.Flat (A i₀) P] [Module T M] [IsScalarTower T S M]
    (f : P →ₗ[T] M) (hf : IsBaseChange S f) {μ : ι} (h : i₀ ≤ μ) (χ : T →+* B μ)
    (hχS : (σ μ).comp χ = algebraMap T S)
    (hχA : χ.comp (algebraMap (A i₀) T) = (algebraMap (A μ) (B μ)).comp (a i₀ μ h))
    (hmodel : IsStageModel a h T χ) :
    ∃ ν, letI := Module.compHom (N ν) (algebraMap (A ν) (B ν)); Module.Flat (A ν) (N ν) := by
  classical
  have hab' (j k : ι) (h : j ≤ k) (x : A j) :
      b j k h (algebraMap (A j) (B j) x) = algebraMap (A k) (B k) (a j k h x) :=
    DFunLike.congr_fun (hab j k h) x
  let : Algebra (A i₀) (A μ) := algebraA a h
  let : Algebra (A i₀) (B μ) := algebraAB (B := B) a h
  let : Algebra T (B μ) := χ.toAlgebra
  have : IsScalarTower (A i₀) (A μ) (B μ) := .of_algebraMap_eq' rfl
  have : IsScalarTower (A i₀) T (B μ) := .of_algebraMap_eq fun x =>
    (DFunLike.congr_fun hχA x).symm
  have hp2 : Algebra.IsPushout (A i₀) (A μ) T (B μ) := by
    unfold IsStageModel at hmodel
    exact hmodel
  have hχA' (x : A i₀) : χ (algebraMap (A i₀) T x) = algebraMap (A μ) (B μ) (a i₀ μ h x) :=
    DFunLike.congr_fun hχA x
  -- Step 1: the map `P → M` factors through some `N ν₁`.
  have hTS (t : T) : σ μ (χ t) = algebraMap T S t := DFunLike.congr_fun hχS t
  let (j : Tail μ) : Algebra T (B j.1) :=
    ((b μ j.1 j.2).comp (algebraMap T (B μ))).toAlgebra
  let (j : Tail μ) : Module T (N j.1) := Module.compHom (N j.1) (algebraMap T (B j.1))
  have (j : Tail μ) : IsScalarTower T (B j.1) (N j.1) := .of_algebraMap_smul fun _ _ => rfl
  have hTB (j k : Tail μ) (h : j ≤ k) (t : T) :
      b j.1 k.1 h (algebraMap T (B j.1) t) = algebraMap T (B k.1) t := by
    simp [RingHom.algebraMap_toAlgebra, DirectedSystem.map_map' (fun i j h => b i j h)]
  let qN (j k : Tail μ) (h : j ≤ k) : N j.1 →ₗ[T] N k.1 :=
    { toFun := n j.1 k.1 h
      map_add' := map_add _
      map_smul' := fun t x => by
        rw [← algebraMap_smul (B j.1) t x, map_smulₛₗ, hTB, RingHom.id_apply,
          algebraMap_smul] }
  let νT (j : Tail μ) : N j.1 →ₗ[T] M :=
    { toFun := ν j.1
      map_add' := map_add _
      map_smul' := fun t x => by
        rw [← algebraMap_smul (B j.1) t x, map_smulₛₗ, RingHom.id_apply, ← algebraMap_smul S t]
        congr 1
        simp [RingHom.algebraMap_toAlgebra, hσ, hTS] }
  have : DirectedSystem (fun j : Tail μ => N j.1) fun j k h => ⇑(qN j k h) :=
    directedSystem_tail (f := fun i j h => n i j h) fun _ _ _ _ => rfl
  obtain ⟨ν₁, ψ, hψ⟩ := LinearMap.exists_comp_eq_of_finitePresentation qN νT
    (fun j k h x => hν j.1 k.1 h x)
    (fun m => let ⟨j, x, hx⟩ := hνs m; let ⟨k, hμk, hjk⟩ := exists_ge_ge μ j
      ⟨⟨k, hμk⟩, n j k hjk x, (hν j k hjk x).trans hx⟩)
    (exists_tail_zero hνz) f
  -- Step 2: `B ν₁ ⊗_T P → N ν₁` is an isomorphism over `S`, hence over some `B ν` (05LI).
  let uM : B ν₁.1 ⊗[T] P →ₗ[B ν₁.1] N ν₁.1 := ψ.liftBaseChange (B ν₁.1)
  let : Algebra (B ν₁.1) S := (σ ν₁.1).toAlgebra
  let : Module (B ν₁.1) M := Module.compHom M (algebraMap (B ν₁.1) S)
  have : IsScalarTower (B ν₁.1) S M := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower T (B ν₁.1) S := .of_algebraMap_eq fun t => by
    simp [RingHom.algebraMap_toAlgebra, hσ, hTS]
  have hS := LinearMap.baseChange_liftBaseChange_bijective ψ hf
    (isBaseChange_colimit b n hbc σ ν hσ hν hσs hνs hνz ν₁.1 rfl)
    (fun x => LinearMap.congr_fun hψ x)
  obtain ⟨ν, hν1, hν'⟩ := exists_baseChange_bijective b σ hσ hσs hσz hfpN P uM hS
  -- Step 3: `N ν = B ν ⊗_T P = A ν ⊗_{A i₀} P` is flat over `A ν`.
  have hμν : μ ≤ ν := ν₁.2.trans hν1
  let : Algebra (B ν₁.1) (B ν) := algebraB b hν1
  refine ⟨ν, ?_⟩
  let : Algebra (A μ) (A ν) := algebraA a hμν
  let : Algebra (B μ) (B ν) := algebraB b hμν
  let : Algebra (A μ) (B ν) := algebraAB (B := B) a hμν
  have : IsScalarTower (A μ) (A ν) (B ν) := .of_algebraMap_eq' rfl
  have : IsScalarTower (A μ) (B μ) (B ν) := .of_algebraMap_eq' (hab μ ν hμν).symm
  have : Algebra.IsPushout (A μ) (A ν) (B μ) (B ν) :=
    CommRingCat.isPushout_iff_isPushout.mp (hpush μ ν hμν)
  let : Algebra (A i₀) (A ν) := algebraA a (h.trans hμν)
  let : Algebra (A i₀) (B ν) := algebraAB (B := B) a (h.trans hμν)
  have : IsScalarTower (A i₀) (A ν) (B ν) := .of_algebraMap_eq' rfl
  have : IsScalarTower (A i₀) (A μ) (A ν) := .of_algebraMap_eq fun x =>
    (DirectedSystem.map_map' (fun i j h => a i j h) h hμν x).symm
  let : Algebra T (B ν) := ((b μ ν hμν).comp (algebraMap T (B μ))).toAlgebra
  have : IsScalarTower T (B μ) (B ν) := .of_algebraMap_eq' rfl
  have : IsScalarTower (A i₀) T (B ν) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, hχA', hab', DirectedSystem.map_map' (fun i j h => a i j h)]
  have : IsScalarTower (A i₀) (B μ) (B ν) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, hab', DirectedSystem.map_map' (fun i j h => a i j h)]
  have hpν : Algebra.IsPushout (A i₀) (A ν) T (B ν) :=
    (Algebra.IsPushout.comp_iff (A i₀) (A μ) T (B μ)).mpr inferInstance
  let : Module (A ν) (N ν) := Module.compHom (N ν) (algebraMap (A ν) (B ν))
  have : IsScalarTower (A ν) (B ν) (N ν) := .of_algebraMap_smul fun _ _ => rfl
  let : Module (B ν₁.1) (N ν) := Module.compHom (N ν) (b ν₁.1 ν hν1)
  have : IsScalarTower (B ν₁.1) (B ν) (N ν) := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower T (B ν₁.1) (B ν) := .of_algebraMap_eq fun t => by
    simp [RingHom.algebraMap_toAlgebra, DirectedSystem.map_map' (fun i j h => b i j h)]
  let e : N ν ≃ₗ[B ν] B ν ⊗[T] P :=
    (hbc ν₁.1 ν hν1).equiv.symm ≪≫ₗ
      (LinearEquiv.ofBijective (LinearMap.baseChange (B ν) uM) hν').symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange T (B ν₁.1) (B ν) (B ν) P
  exact Module.Flat.of_linearEquiv ((e.restrictScalars (A ν)).trans
    (Algebra.IsPushout.cancelBaseChange (A i₀) (A ν) T (B ν) P))

end Stage

end Module

end Module.Flat.DirectedModel

open Module.Flat.DirectedModel in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Stacks 02JO (3).** Let `R → S` be of finite presentation and let `M` be a finitely
presented `S`-module which is flat over `R`. Let `(R → S, M) = colim_λ (R_λ → S_λ, M_λ)` be a
directed colimit such that `R_μ ⊗_{R_λ} S_λ → S_μ` and `S_μ ⊗_{S_λ} M_λ → M_μ` are isomorphisms
for `μ ≥ λ`, each `R_λ → S_λ` is of finite presentation and each `M_λ` is a finitely presented
`S_λ`-module. Then `M_λ` is flat over `R_λ` for all sufficiently large `λ`. -/
@[stacks 02JO "(3)", ega "IV 11.2.6" "affine case, (ii)", ega "IV 11.2.6.1" "(ii) necessity"]
theorem Module.Flat.eventually_flat_of_directed {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] (M : Type w) [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [Module.FinitePresentation S M] [Module.Flat R M]
    {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {A B : ι → Type v} [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i, Algebra (A i) (B i)]
    {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module (B i) (N i)]
    (a : ∀ i j, i ≤ j → A i →+* A j) (b : ∀ i j, i ≤ j → B i →+* B j)
    (n : ∀ i j (h : i ≤ j), N i →ₛₗ[b i j h] N j)
    [DirectedSystem A fun i j h => a i j h] [DirectedSystem B fun i j h => b i j h]
    [DirectedSystem N fun i j h => n i j h]
    (hab : ∀ i j (h : i ≤ j),
      (b i j h).comp (algebraMap (A i) (B i)) = (algebraMap (A j) (B j)).comp (a i j h))
    (ρ : ∀ i, A i →+* R) (σ : ∀ i, B i →+* S) (ν : ∀ i, N i →ₛₗ[σ i] M)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x)
    (hσ : ∀ i j (h : i ≤ j) x, σ j (b i j h x) = σ i x)
    (hν : ∀ i j (h : i ≤ j) x, ν j (n i j h x) = ν i x)
    (hρσ : ∀ i, (σ i).comp (algebraMap (A i) (B i)) = (algebraMap R S).comp (ρ i))
    (hρs : ∀ r, ∃ i x, ρ i x = r) (hρz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0)
    (hσs : ∀ s, ∃ i x, σ i x = s) (hσz : ∀ i x, σ i x = 0 → ∃ j, ∃ h : i ≤ j, b i j h x = 0)
    (hνs : ∀ m, ∃ i x, ν i x = m) (hνz : ∀ i x, ν i x = 0 → ∃ j, ∃ h : i ≤ j, n i j h x = 0)
    (hpush : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
      (CommRingCat.ofHom (algebraMap (A i) (B i))) (CommRingCat.ofHom (algebraMap (A j) (B j)))
      (CommRingCat.ofHom (b i j h)))
    (hbc : ∀ i j (h : i ≤ j), letI := algebraB b h
      letI := Module.compHom (N j) (b i j h)
      haveI : IsScalarTower (B i) (B j) (N j) := .of_algebraMap_smul fun _ _ => rfl
      IsBaseChange (B j) (transLinear b n h))
    (hfp : ∀ i, Algebra.FinitePresentation (A i) (B i))
    (hfpN : ∀ i, Module.FinitePresentation (B i) (N i)) :
    ∃ i, ∀ j, i ≤ j →
      letI := Module.compHom (N j) (algebraMap (A j) (B j)); Module.Flat (A j) (N j) := by
  obtain ⟨i₀, T, P, _, _, _, _, _, _, _, _, _, _, _, _, f, _, _, _, _, hf⟩ :=
    Module.Flat.exists_finitePresentation_model_of_directed (R := R) (S := S) M a ρ hρ hρs hρz
  let : Algebra (A i₀) R := (ρ i₀).toAlgebra
  obtain ⟨i₁, h₁, χ, hχS, hχA⟩ := exists_lift_stage a b hab ρ σ hρ hσ hρσ hσs hσz T
    fun x => IsScalarTower.algebraMap_apply (A i₀) R S x
  obtain ⟨μ, hμ, hmodel⟩ := exists_isStageModel a b hab ρ σ hρ hσ hρσ hσs hσz hρs hρz hpush
    hfp T rfl h₁ χ hχS hχA
  obtain ⟨ν', hν'⟩ := exists_flat_of_isStageModel a b hab n σ hσ hσs hσz ν hν hνs hνz hbc hfpN
    hpush T P f hf (h₁.trans hμ) ((b i₁ μ hμ).comp χ)
    (RingHom.ext fun t => (hσ i₁ μ hμ (χ t)).trans (DFunLike.congr_fun hχS t))
    (RingHom.ext fun x => by
      simp only [RingHom.comp_apply]
      rw [← RingHom.comp_apply χ, hχA, RingHom.comp_apply, ← RingHom.comp_apply (b i₁ μ hμ), hab,
        RingHom.comp_apply, DirectedSystem.map_map' (fun i j h => a i j h)]) hmodel
  exact ⟨ν', fun j hj => flat_of_le a b hab n hpush hbc hj hν'⟩
