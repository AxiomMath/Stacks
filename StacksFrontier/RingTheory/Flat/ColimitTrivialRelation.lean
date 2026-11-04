module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# Relations over a filtered colimit of rings become trivial at a finite stage

Let `A : Λ ⥤ CommRingCat` be a system of commutative rings over a directed preorder with
colimit `R`, and let `N : Λ ⥤ AddCommGrpCat` be a compatible system of modules — each
`N i` an `A i`-module, the transition maps semilinear over the transition maps of `A` — with
colimit `M`. If `M` is flat over `R`, then every relation `∑ aₖ • vₖ = 0` holding at a finite
stage `i` is *trivial* at some later stage `j`, in the sense of Mathlib's
`Module.IsTrivialRelation`: the vectors `vₖ` become `A j`-combinations of finitely many
elements of `N j` whose coefficient vectors are syzygies of the `aₖ`.

This is the substitute, for elementwise purposes, for the statement that a filtered colimit
commutes with the tensor product over a *varying* base ring, which Mathlib does not have:
`TensorProduct.directLimitLeft` and `TensorProduct.directLimitRight` are for a fixed base.
Together with `Module.IsTrivialRelation.sum_tmul_eq_zero` it shows that a relation coming from
stage `i` dies in `I A j ⊗_{A j} N j` for `j` large.

## Main results

* `Module.exists_hom_isTrivialRelation_of_isColimit`: a relation at a finite stage becomes
  trivial at a later stage, when the colimit module is flat over the colimit ring.
* `Module.IsTrivialRelation.mapOfSystem`, `Module.IsTrivialRelation.mapOfSystem'`: triviality is
  preserved by pushing up the system.
* `Module.IsTrivialRelation.const_smul`: triviality is preserved by scaling the vectors.
* `Module.IsTrivialRelation.sum_tmul_eq_zero`: a trivial relation whose coefficients lie in an
  ideal `I` gives a vanishing element of `I ⊗ M`.
* `TensorProduct.exists_sum_tmul_of_span_eq`: every element of `I ⊗ M` is `∑ aₖ ⊗ vₖ` for a
  generating family `a` of `I`.
* `Module.sum_tmul_eq_zero_of_mem_ker_rTensor`: the comparison map
  `Ker(I ⊗_R M → R ⊗_R M) → I' ⊗_{R'} M'` of Stacks 00MO vanishes as soon as the syzygies of
  the chosen generators of `I` trivialize after a generating family of them is pushed to `M'`.
* `Module.Flat.of_isColimit_of_forall_exists_ge_flat`: the converse direction — flatness at
  cofinally many stages of the system gives flatness of the colimit. This is what turns "flat at
  some stage above every stage" into flatness over the colimit ring.
* `Ideal.sum_tmul_eq_zero_of_vanishing_certificate`,
  `Ideal.exists_tmul_vanishing_certificate`: the finitary certificate for the vanishing of
  `∑ₖ pₖ ⊗ yₖ` in `I ⊗_R N`, and the fact that a vanishing element always has one. This is
  `Module.IsTrivialRelation` with an extra family of unknown elements of `I` allowed, which is the
  price of needing no flatness.
* `Ideal.exists_hom_tmul_eq_zero_of_isColimit`: an element of `I ⊗_R M` coming from a stage and
  vanishing already vanishes in `I_j ⊗_{A j} N j` for some later stage `j`, where
  `I_j = ρ_j^{-1}(I)`. This is the flatness-free analogue of
  `Module.exists_hom_isTrivialRelation_of_isColimit`.
* `Module.sum_tmul_eq_zero_of_mem_ker_rTensor'`: the comparison map of Stacks 00MO again, now
  from the vanishing of the pushed syzygies rather than their triviality.

## Implementation notes

The relation is transported to `M` over `R`, made trivial there by the equational criterion for
flatness (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`, Stacks 00HK), and the resulting
finitely many coefficients and vectors are then pulled back to a finite stage and the finitely
many equations they satisfy are forced to hold at a still later stage. Both steps are
elementwise facts about filtered colimits in a concrete category:
`CategoryTheory.Limits.Concrete.exists_hom_ι_eq_of_isColimit` and
`CategoryTheory.Limits.Concrete.isColimit_exists_of_rep_eq`, available because
`CategoryTheory.forget` preserves filtered colimits of rings and of abelian groups. Choosing a
single stage for finitely many of them is `Preorder.exists_forall_le_of_fintype`.

Morphisms of a preorder viewed as a category form a subsingleton, which is what lets the two
maps produced by `Concrete.isColimit_exists_of_rep_eq` be identified.
-/

universe u

open CategoryTheory Limits
open scoped TensorProduct

/-- A finite family in a nonempty directed preorder has an upper bound. -/
public theorem Preorder.exists_forall_le_of_fintype {Λ : Type u} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)] {ι : Type*} [Finite ι] (f : ι → Λ) : ∃ z, ∀ i, f i ≤ z := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨z, hz⟩ := Finset.exists_le (Finset.univ.image f)
  exact ⟨z, fun i => hz _ (Finset.mem_image_of_mem f (Finset.mem_univ i))⟩

namespace Module

/-- Transition maps of a diagram in a concrete category compose, whatever the chosen composite. -/
private theorem map_map_apply {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {Λ : Type*} [Preorder Λ]
    (F : Λ ⥤ C) {p q r : Λ} (f : p ⟶ q) (g : q ⟶ r) (f' : p ⟶ r) (x : ToType (F.obj p)) :
    F.map g (F.map f x) = F.map f' x := by
  rw [← CategoryTheory.comp_apply, ← F.map_comp, Subsingleton.elim (f ≫ g) f']

/-- A cocone leg of a diagram in a concrete category is compatible with transition maps. -/
private theorem app_map_const {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {Λ : Type*} [Preorder Λ]
    {F : Λ ⥤ C} {X : C} (τ : F ⟶ (Functor.const Λ).obj X) {p q : Λ} (f : p ⟶ q)
    (x : ToType (F.obj p)) : τ.app q (F.map f x) = τ.app p x := by
  simp

/-- **A relation over a filtered colimit of rings becomes trivial at a finite stage.** -/
public theorem exists_hom_isTrivialRelation_of_isColimit
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {A : Λ ⥤ CommRingCat.{u}} {N : Λ ⥤ AddCommGrpCat.{u}}
    (mod : ∀ i, Module (A.obj i) (N.obj i))
    (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (a : A.obj i) (m : N.obj i),
      N.map h (a • m) = A.map h a • N.map h m)
    {ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R)}
    {ν : N ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M)}
    (hR : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
    (hM : IsColimit (Cocone.mk (AddCommGrpCat.of M) ν))
    (hν : ∀ (i : Λ) (a : A.obj i) (m : N.obj i),
      (ν.app i (a • m) : M) = HSMul.hSMul (α := R) (β := M) (ρ.app i a) (ν.app i m))
    {i : Λ} {n : ℕ} (a : Fin n → A.obj i) (v : Fin n → N.obj i)
    (hav : ∑ k, a k • v k = 0) :
    ∃ (j : Λ) (h : i ⟶ j),
      Module.IsTrivialRelation (fun k => A.map h (a k)) (fun k => N.map h (v k)) := by
  classical
  -- the relation holds in `M` over `R`
  have hsum : ∑ k, HSMul.hSMul (α := R) (β := M) (ρ.app i (a k)) (ν.app i (v k)) = 0 := by
    have h0 : ∑ k, (ν.app i (a k • v k) : M) = 0 := by
      rw [← map_sum (ν.app i).hom, hav, map_zero]
    simpa only [hν] using h0
  -- flatness makes it trivial over `R`
  obtain ⟨m, c, y, hc, hy⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := M)
      (f := fun k => (ρ.app i (a k) : R)) (x := fun k => (ν.app i (v k) : M)) hsum
  have hc' : ∀ κ, (ν.app i (v κ) : M) = ∑ l, c κ l • y l := hc
  have hy' : ∀ l, ∑ κ, HMul.hMul (α := R) (β := R) (ρ.app i (a κ)) (c κ l) = 0 := hy
  -- lift the witnesses to a common stage `j₁ ≥ i`
  choose jc _hjc cc hcc using fun (p : Fin n × Fin m) =>
    Concrete.exists_hom_ι_eq_of_isColimit A hR (c p.1 p.2) i
  choose jy _hjy yy hyy using fun (l : Fin m) =>
    Concrete.exists_hom_ι_eq_of_isColimit N hM (y l) i
  obtain ⟨j₁, hj₁⟩ := Preorder.exists_forall_le_of_fintype
    (fun p : Option (Fin n × Fin m) ⊕ Fin m => p.elim (fun p => p.elim i jc) jy)
  have hi1 : i ≤ j₁ := hj₁ (.inl none)
  have hjc1 : ∀ p, jc p ≤ j₁ := fun p => hj₁ (.inl (some p))
  have hjy1 : ∀ l, jy l ≤ j₁ := fun l => hj₁ (.inr l)
  set h₁ : i ⟶ j₁ := homOfLE hi1
  set C : Fin n → Fin m → A.obj j₁ :=
    fun κ l => A.map (homOfLE (hjc1 (κ, l))) (cc (κ, l))
  set Y : Fin m → N.obj j₁ := fun l => N.map (homOfLE (hjy1 l)) (yy l)
  have hC : ∀ κ l, (ρ.app j₁ (C κ l) : R) = c κ l := fun κ l =>
    (app_map_const ρ (homOfLE (hjc1 (κ, l))) _).trans (hcc (κ, l))
  have hY : ∀ l, (ν.app j₁ (Y l) : M) = y l := fun l =>
    (app_map_const ν (homOfLE (hjy1 l)) _).trans (hyy l)
  -- the two families of relations hold after `ρ`, `ν`, hence at some later stage
  have hz : ∀ l, ∃ (q : Λ) (f : j₁ ⟶ q),
      A.map f (∑ κ, A.map h₁ (a κ) * C κ l) = 0 := by
    intro l
    have key : (ρ.app j₁ (∑ κ, A.map h₁ (a κ) * C κ l) : R) = ρ.app j₁ (0 : A.obj j₁) := by
      rw [map_sum (ρ.app j₁).hom, map_zero (ρ.app j₁).hom, ← hy' l]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [map_mul (ρ.app j₁).hom, app_map_const ρ, hC]
    obtain ⟨q, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq A hR _ _ key
    exact ⟨q, f, by rw [hfg, map_zero (A.map g).hom]⟩
  have hb : ∀ κ, ∃ (q : Λ) (f : j₁ ⟶ q),
      N.map f (N.map h₁ (v κ)) = N.map f (∑ l, C κ l • Y l) := by
    intro κ
    have key : (ν.app j₁ (N.map h₁ (v κ)) : M) = ν.app j₁ (∑ l, C κ l • Y l) := by
      rw [app_map_const ν, hc' κ, map_sum (ν.app j₁).hom]
      exact Finset.sum_congr rfl fun l _ => by rw [hν j₁, hC, hY]
    obtain ⟨q, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq N hM _ _ key
    exact ⟨q, f, by rw [hfg, Subsingleton.elim g f]⟩
  choose qa fa hqa using hz
  choose qb fb hqb using hb
  obtain ⟨j, hj⟩ := Preorder.exists_forall_le_of_fintype
    (fun p : Option (Fin m) ⊕ Fin n => p.elim (fun p => p.elim j₁ qa) qb)
  have h1j : j₁ ≤ j := hj (.inl none)
  have hqaj : ∀ l, qa l ≤ j := fun l => hj (.inl (some l))
  have hqbj : ∀ κ, qb κ ≤ j := fun κ => hj (.inr κ)
  set g₁ : j₁ ⟶ j := homOfLE h1j
  refine ⟨j, homOfLE (hi1.trans h1j), m,
    fun κ l => A.map g₁ (C κ l), fun l => N.map g₁ (Y l), ?_, ?_⟩
  · intro κ
    change N.map (homOfLE (hi1.trans h1j)) (v κ) = ∑ l, A.map g₁ (C κ l) • N.map g₁ (Y l)
    have e1 : N.map (homOfLE (hi1.trans h1j)) (v κ) = N.map g₁ (N.map h₁ (v κ)) :=
      (map_map_apply N h₁ g₁ _ (v κ)).symm
    have e2 : N.map g₁ (N.map h₁ (v κ)) = N.map g₁ (∑ l, C κ l • Y l) := by
      rw [← map_map_apply N (fb κ) (homOfLE (hqbj κ)) g₁ (N.map h₁ (v κ)), hqb κ,
        map_map_apply N (fb κ) (homOfLE (hqbj κ)) g₁]
    rw [e1, e2, map_sum (N.map g₁).hom]
    exact Finset.sum_congr rfl fun l _ => hsmul g₁ (C κ l) (Y l)
  · intro l
    change ∑ κ, HMul.hMul (α := (A.obj j : Type u)) (β := (A.obj j : Type u))
      (A.map (homOfLE (hi1.trans h1j)) (a κ)) (A.map g₁ (C κ l)) = 0
    have e1 : ∀ κ, A.map (homOfLE (hi1.trans h1j)) (a κ) = A.map g₁ (A.map h₁ (a κ)) :=
      fun κ => (map_map_apply A h₁ g₁ _ (a κ)).symm
    have e2 : A.map g₁ (∑ κ, A.map h₁ (a κ) * C κ l) = 0 := by
      rw [← map_map_apply A (fa l) (homOfLE (hqaj l)) g₁, hqa l,
        map_zero (A.map (homOfLE (hqaj l))).hom]
    rw [← e2, map_sum (A.map g₁).hom]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [e1 κ, map_mul (A.map g₁).hom]

/-- Pushing a trivial relation forward along the system keeps it trivial. -/
public theorem IsTrivialRelation.mapOfSystem
    {Λ : Type u} [Preorder Λ]
    {A : Λ ⥤ CommRingCat.{u}} {N : Λ ⥤ AddCommGrpCat.{u}}
    (mod : ∀ i, Module (A.obj i) (N.obj i))
    (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (a : A.obj i) (m : N.obj i),
      N.map h (a • m) = A.map h a • N.map h m)
    {i j : Λ} (h : i ⟶ j) {n : ℕ} {f : Fin n → A.obj i} {x : Fin n → N.obj i}
    (H : Module.IsTrivialRelation f x) :
    Module.IsTrivialRelation (fun k => A.map h (f k)) (fun k => N.map h (x k)) := by
  obtain ⟨p, c, y, hx, hf⟩ := H
  refine ⟨p, fun κ l => A.map h (c κ l), fun l => N.map h (y l), fun κ => ?_, fun l => ?_⟩
  · change N.map h (x κ) = ∑ l, A.map h (c κ l) • N.map h (y l)
    rw [hx κ, map_sum (N.map h).hom]
    exact Finset.sum_congr rfl fun l _ => hsmul h (c κ l) (y l)
  · change ∑ κ, HMul.hMul (α := (A.obj j : Type u)) (β := (A.obj j : Type u))
      (A.map h (f κ)) (A.map h (c κ l)) = 0
    rw [← map_zero (A.map h).hom, ← hf l, map_sum (A.map h).hom]
    exact Finset.sum_congr rfl fun κ _ => (map_mul (A.map h).hom _ _).symm

/-- `IsTrivialRelation.mapOfSystem` with the composite rewritten: a relation trivialized at
`j` is trivialized at any `j'` above it, and the conclusion is stated with the transition map
`i ⟶ j'` itself. -/
public theorem IsTrivialRelation.mapOfSystem' {Λ : Type u} [Preorder Λ]
    {A : Λ ⥤ CommRingCat.{u}} {N : Λ ⥤ AddCommGrpCat.{u}}
    (mod : ∀ i, Module (A.obj i) (N.obj i))
    (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (a : A.obj i) (m : N.obj i),
      N.map h (a • m) = A.map h a • N.map h m)
    {i j j' : Λ} (h : i ⟶ j) (g : j ⟶ j') (h' : i ⟶ j') {n : ℕ}
    {f : Fin n → A.obj i} {x : Fin n → N.obj i}
    (H : Module.IsTrivialRelation (fun k => A.map h (f k)) (fun k => N.map h (x k))) :
    Module.IsTrivialRelation (fun k => A.map h' (f k)) (fun k => N.map h' (x k)) := by
  have H2 := IsTrivialRelation.mapOfSystem mod hsmul g H
  simpa only [map_map_apply A h g h', map_map_apply N h g h'] using H2

/-- Scaling the right-hand family of a trivial relation keeps it trivial. -/
public theorem IsTrivialRelation.const_smul {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    {n : ℕ} {f : Fin n → R} {u : Fin n → M} (h : Module.IsTrivialRelation f u) (β : S) :
    Module.IsTrivialRelation f (fun k => β • u k) := by
  obtain ⟨p, c, y, hu, hc⟩ := h
  refine ⟨p, c, fun l => β • y l, fun k => ?_, hc⟩
  change β • u k = ∑ l, c k l • (β • y l)
  rw [hu k, Finset.smul_sum]
  exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _

/-- **A trivial relation with coefficients in an ideal `I` dies in `I ⊗ M`.** -/
public theorem IsTrivialRelation.sum_tmul_eq_zero {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ} (α : Fin n → I) {u : Fin n → M}
    (h : Module.IsTrivialRelation (fun k => (α k : R)) u) :
    ∑ k, (α k) ⊗ₜ[R] (u k) = (0 : ↥I ⊗[R] M) := by
  obtain ⟨p, c, y, hu, hc⟩ := h
  have hzero : ∀ l, ∑ k, c k l • α k = (0 : ↥I) := fun l =>
    Subtype.ext (by simpa [mul_comm] using hc l)
  calc ∑ k, (α k) ⊗ₜ[R] (u k)
      = ∑ k, ∑ l, (α k) ⊗ₜ[R] (c k l • y l) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hu k, TensorProduct.tmul_sum]
    _ = ∑ l, (∑ k, c k l • α k) ⊗ₜ[R] (y l) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [TensorProduct.sum_tmul]
        exact Finset.sum_congr rfl fun k _ => (TensorProduct.smul_tmul _ _ _).symm
    _ = 0 := by simp [hzero]

/-- Every element of `I ⊗[R] M` is a combination of a generating family of `I`. -/
public theorem _root_.TensorProduct.exists_sum_tmul_of_span_eq {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {I : Ideal R} {n : ℕ} (a : Fin n → I)
    (hspan : Ideal.span (Set.range fun k => (a k : R)) = I) (t : ↥I ⊗[R] M) :
    ∃ v : Fin n → M, t = ∑ k, (a k) ⊗ₜ[R] (v k) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x m =>
      have hx : (x : R) ∈ Submodule.span R (Set.range fun k => (a k : R)) := by
        rw [show Submodule.span R (Set.range fun k => (a k : R))
          = (I : Submodule R R) from hspan]
        exact x.2
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hx
      refine ⟨fun k => r k • m, ?_⟩
      have hxe : x = ∑ k, r k • a k := Subtype.ext (by simpa using hr.symm)
      rw [hxe, TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun k _ => TensorProduct.smul_tmul _ _ _
  | add x y hx hy =>
      obtain ⟨vx, hvx⟩ := hx
      obtain ⟨vy, hvy⟩ := hy
      exact ⟨vx + vy, by simp [hvx, hvy, TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

/-- The comparison map kills the kernel once the pushed syzygies vanish in `I' ⊗ M'`. -/
private theorem sum_tmul_eq_zero_of_vanishing_syzygies
    {R R' S S' M M' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R R'] [Algebra R S] [Algebra R' S'] [Algebra S S']
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module R' M'] [Module S M'] [Module S' M']
    [IsScalarTower R' S' M'] [IsScalarTower S S' M']
    {I : Ideal R} {I' : Ideal R'} {n : ℕ} (a : Fin n → I)
    (hspan : Ideal.span (Set.range fun k => (a k : R)) = I)
    (f : M →ₗ[S] M') (α : Fin n → I')
    (Φ : ↥I ⊗[R] M →+ ↥I' ⊗[R'] M')
    (hΦ : ∀ (k : Fin n) (m : M), Φ ((a k) ⊗ₜ[R] m) = (α k) ⊗ₜ[R'] (f m))
    {p : ℕ} (w : Fin p → Fin n → M)
    (hwspan : ∀ v : Fin n → M, (∑ k, (a k : R) • v k = 0) →
      ∃ b : Fin p → S, ∀ k, v k = ∑ q, b q • w q k)
    (hvanish : ∀ q, ∑ k, (α k) ⊗ₜ[R'] (f (w q k)) = (0 : ↥I' ⊗[R'] M'))
    (t : ↥I ⊗[R] M) (ht : t ∈ LinearMap.ker (I.subtype.rTensor M)) :
    Φ t = 0 := by
  obtain ⟨v, rfl⟩ := TensorProduct.exists_sum_tmul_of_span_eq a hspan t
  -- the relation satisfied by `v`
  have hv0 : ∑ k, (a k : R) • v k = 0 := by
    simpa using congrArg (TensorProduct.lid R M) (LinearMap.mem_ker.mp ht)
  obtain ⟨b, hb⟩ := hwspan v hv0
  have hstep : ∀ q : Fin p, ∑ k, (α k) ⊗ₜ[R'] (f (b q • w q k)) = (0 : ↥I' ⊗[R'] M') := by
    intro q
    have hsm : ∀ k, f (b q • w q k) = (algebraMap S S' (b q)) • f (w q k) := by
      intro k
      rw [map_smul, IsScalarTower.algebraMap_smul]
    have e : ∑ k, (α k) ⊗ₜ[R'] (f (b q • w q k))
        = LinearMap.lTensor ↥I'
            ((LinearMap.lsmul S' M' (algebraMap S S' (b q))).restrictScalars R')
            (∑ k, (α k) ⊗ₜ[R'] (f (w q k))) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsm k, LinearMap.lTensor_tmul]
      rfl
    rw [e, hvanish q, map_zero]
  rw [map_sum Φ]
  calc ∑ k, Φ ((a k) ⊗ₜ[R] (v k))
      = ∑ k, ∑ q, (α k) ⊗ₜ[R'] (f (b q • w q k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hΦ k, hb k, map_sum, TensorProduct.tmul_sum]
    _ = ∑ q, ∑ k, (α k) ⊗ₜ[R'] (f (b q • w q k)) := Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun q _ => hstep q

/-- **The `Tor₁` comparison map kills the kernel once the syzygies trivialize.** -/
public theorem sum_tmul_eq_zero_of_mem_ker_rTensor
    {R R' S S' M M' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R R'] [Algebra R S] [Algebra R' S'] [Algebra S S']
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module R' M'] [Module S M'] [Module S' M']
    [IsScalarTower R' S' M'] [IsScalarTower S S' M']
    {I : Ideal R} {I' : Ideal R'} {n : ℕ} (a : Fin n → I)
    (hspan : Ideal.span (Set.range fun k => (a k : R)) = I)
    (f : M →ₗ[S] M') (α : Fin n → I')
    (Φ : ↥I ⊗[R] M →+ ↥I' ⊗[R'] M')
    (hΦ : ∀ (k : Fin n) (m : M), Φ ((a k) ⊗ₜ[R] m) = (α k) ⊗ₜ[R'] (f m))
    {p : ℕ} (w : Fin p → Fin n → M)
    (hwspan : ∀ v : Fin n → M, (∑ k, (a k : R) • v k = 0) →
      ∃ b : Fin p → S, ∀ k, v k = ∑ q, b q • w q k)
    (htriv : ∀ q, IsTrivialRelation (fun k => (α k : R')) (fun k => f (w q k)))
    (t : ↥I ⊗[R] M) (ht : t ∈ LinearMap.ker (I.subtype.rTensor M)) :
    Φ t = 0 := by
  exact sum_tmul_eq_zero_of_vanishing_syzygies (S' := S') a hspan f α Φ hΦ w hwspan
    (fun q => IsTrivialRelation.sum_tmul_eq_zero α (htriv q)) t ht

/-- **Flatness ascends from cofinally many stages of the system to the colimit.** If `N j` is flat
over `A j` for arbitrarily large `j`, then the colimit `M` is flat over the colimit `R`.

This is the converse direction to `Module.exists_hom_isTrivialRelation_of_isColimit`, and it is
what turns "flat at some stage above every stage" — the shape in which both Stacks 00R6 and
Stacks 0471 produce flatness — into flatness of the colimit. Only the cofinal form suffices: a
relation in `M` over `R` is lifted to a stage, and one then passes to a stage above it at which `N`
is flat, where the relation becomes trivial by the equational criterion for flatness (Stacks 00HK);
the legs of the two cocones carry the resulting witnesses back down to `R` and `M`. -/
public theorem Flat.of_isColimit_of_forall_exists_ge_flat
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {A : Λ ⥤ CommRingCat.{u}} {N : Λ ⥤ AddCommGrpCat.{u}}
    (mod : ∀ i, Module (A.obj i) (N.obj i))
    (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (a : A.obj i) (m : N.obj i),
      N.map h (a • m) = A.map h a • N.map h m)
    {ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R)}
    {ν : N ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M)}
    (hR : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
    (hM : IsColimit (Cocone.mk (AddCommGrpCat.of M) ν))
    (hν : ∀ (i : Λ) (a : A.obj i) (m : N.obj i),
      (ν.app i (a • m) : M) = HSMul.hSMul (α := R) (β := M) (ρ.app i a) (ν.app i m))
    (hflat : ∀ i : Λ, ∃ j, i ≤ j ∧ Module.Flat ↑(A.obj j) ↑(N.obj j)) :
    Module.Flat R M := by
  classical
  refine Module.Flat.of_forall_isTrivialRelation ?_
  intro l f x hfx
  obtain ⟨i₀⟩ := ‹Nonempty Λ›
  -- lift the coefficients and the vectors to a common stage `j₁`
  choose jf _hjf af haf using fun k : Fin l =>
    Concrete.exists_hom_ι_eq_of_isColimit A hR (f k) i₀
  choose jx _hjx vx hvx using fun k : Fin l =>
    Concrete.exists_hom_ι_eq_of_isColimit N hM (x k) i₀
  obtain ⟨j₁, hj₁⟩ := Preorder.exists_forall_le_of_fintype
    (fun p : Option (Fin l) ⊕ Fin l => p.elim (fun p => p.elim i₀ jf) jx)
  have hjf1 : ∀ k, jf k ≤ j₁ := fun k => hj₁ (.inl (some k))
  have hjx1 : ∀ k, jx k ≤ j₁ := fun k => hj₁ (.inr k)
  set a : Fin l → A.obj j₁ := fun k => A.map (homOfLE (hjf1 k)) (af k)
  set v : Fin l → N.obj j₁ := fun k => N.map (homOfLE (hjx1 k)) (vx k)
  have ha : ∀ k, (ρ.app j₁ (a k) : R) = f k := fun k =>
    (app_map_const ρ (homOfLE (hjf1 k)) _).trans (haf k)
  have hv : ∀ k, (ν.app j₁ (v k) : M) = x k := fun k =>
    (app_map_const ν (homOfLE (hjx1 k)) _).trans (hvx k)
  -- the relation holds at a stage `j₂ ≥ j₁`
  have key : (ν.app j₁ (∑ k, a k • v k) : M) = ν.app j₁ (0 : N.obj j₁) := by
    rw [map_sum (ν.app j₁).hom, map_zero (ν.app j₁).hom, ← hfx]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hν j₁, ha, hv]
  obtain ⟨j₂, g₂, g', hg₂⟩ := Concrete.isColimit_exists_of_rep_eq N hM _ _ key
  -- pass to a stage `j ≥ j₂` at which `N j` is flat over `A j`
  obtain ⟨j, hj2j, hflatj⟩ := hflat j₂
  set hh : j₁ ⟶ j := homOfLE (le_trans (leOfHom g₂) hj2j)
  have hzero : ∑ k, A.map hh (a k) • N.map hh (v k) = 0 := by
    have e : N.map hh (∑ k, a k • v k) = 0 := by
      rw [← map_map_apply N g₂ (homOfLE hj2j) hh, hg₂, map_zero (N.map g').hom,
        map_zero (N.map (homOfLE hj2j)).hom]
    rw [← e, map_sum (N.map hh).hom]
    exact Finset.sum_congr rfl fun k _ => (hsmul hh (a k) (v k)).symm
  -- flatness at `j` makes it trivial there
  obtain ⟨p, c, y, hy, hc⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := ↑(A.obj j)) (M := ↑(N.obj j))
      (f := fun k => A.map hh (a k)) (x := fun k => N.map hh (v k)) hzero
  -- carry the witnesses down to `R` and `M`
  refine ⟨p, fun k n => (ρ.app j (c k n) : R), fun n => (ν.app j (y n) : M), fun k => ?_,
    fun n => ?_⟩
  · have e : (ν.app j (N.map hh (v k)) : M) = x k := (app_map_const ν hh (v k)).trans (hv k)
    have hyk : N.map hh (v k) = ∑ n, c k n • y n := hy k
    rw [← e, hyk, map_sum (ν.app j).hom]
    exact Finset.sum_congr rfl fun n _ => hν j (c k n) (y n)
  · have e : ∀ k, f k = (ρ.app j (A.map hh (a k)) : R) := fun k =>
      ((app_map_const ρ hh (a k)).trans (ha k)).symm
    have e2 : (ρ.app j (∑ k, A.map hh (a k) * c k n) : R) = 0 := by rw [hc n, map_zero]
    rw [← e2, map_sum (ρ.app j).hom]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul (ρ.app j).hom, e k]

/-- **A finitary certificate for the vanishing of `∑ αₖ ⊗ uₖ` in `J ⊗_A X`.** If the coefficient
vectors `c` express the `uₖ` in terms of finitely many `Yₗ`, the vectors `β` lie in `J`, the `Yₗ`
satisfy the relations with coefficients `d`, and each syzygy `∑ₖ cₖₗ αₖ + ∑_b d_bₗ β_b` vanishes in
`A`, then `∑ₖ αₖ ⊗ uₖ = 0`.

This is `Module.IsTrivialRelation.sum_tmul_eq_zero` with the extra family `β` allowed: for `n' = 0`
the syzygy condition says the relation `(α, u)` is trivial. The extra family is what makes the
certificate *unconditional* — see `Ideal.exists_tmul_vanishing_certificate`, where it is produced
from nothing but the vanishing itself, at the cost of the `β_b` being unknown elements of `J`. -/
public theorem _root_.Ideal.sum_tmul_eq_zero_of_vanishing_certificate
    {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X] [Module A X] (J : Ideal A)
    {n n' m : ℕ} (α : Fin n → ↥J) (u : Fin n → X) (β : Fin n' → ↥J) (Y : Fin m → X)
    (c : Fin n → Fin m → A) (d : Fin n' → Fin m → A)
    (h1 : ∀ k, u k = ∑ l, c k l • Y l)
    (h2 : ∀ b, ∑ l, d b l • Y l = 0)
    (h3 : ∀ l, ∑ k, c k l • (α k : A) + ∑ b, d b l • (β b : A) = 0) :
    ∑ k, (α k) ⊗ₜ[A] (u k) = (0 : ↥J ⊗[A] X) := by
  have key : ∀ l, ∑ k, c k l • α k = -∑ b, d b l • β b := by
    intro l
    refine Subtype.ext ?_
    have e : ((∑ k, c k l • α k : ↥J) : A) = ∑ k, c k l • (α k : A) := by
      simp only [Submodule.coe_sum, SetLike.val_smul]
    have e2 : ((-∑ b, d b l • β b : ↥J) : A) = -∑ b, d b l • (β b : A) := by
      simp only [NegMemClass.coe_neg, Submodule.coe_sum, SetLike.val_smul]
    rw [e, e2, ← sub_eq_zero, sub_neg_eq_add]
    exact h3 l
  have swap : ∀ {q : ℕ} (γ : Fin q → ↥J) (e : Fin q → Fin m → A),
      ∑ k, (γ k) ⊗ₜ[A] (∑ l, e k l • Y l) = ∑ l, (∑ k, e k l • γ k) ⊗ₜ[A] (Y l) := by
    intro q γ e
    simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul]
    rw [Finset.sum_comm]
    simp_rw [← TensorProduct.tmul_smul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
  calc ∑ k, (α k) ⊗ₜ[A] (u k)
      = ∑ k, (α k) ⊗ₜ[A] (∑ l, c k l • Y l) := by simp_rw [h1]
    _ = ∑ l, (∑ k, c k l • α k) ⊗ₜ[A] (Y l) := swap α c
    _ = ∑ l, (-∑ b, d b l • β b) ⊗ₜ[A] (Y l) := by simp_rw [key]
    _ = -∑ l, (∑ b, d b l • β b) ⊗ₜ[A] (Y l) := by simp [TensorProduct.neg_tmul]
    _ = -∑ b, (β b) ⊗ₜ[A] (∑ l, d b l • Y l) := by rw [swap β d]
    _ = 0 := by simp [h2]

/-- **The equational criterion for vanishing in `I ⊗_R N`, with the extra generators inside `I`.**
If `∑ₖ pₖ ⊗ yₖ = 0` in `I ⊗_R N` for elements `pₖ` of the ideal `I`, then there are finitely many
further elements `g_b` of `I`, finitely many `Yₗ` in `N`, and coefficients `c`, `d` in `R`
certifying the vanishing in the sense of `Ideal.sum_tmul_eq_zero_of_vanishing_certificate`.

This is the substitute for the equational criterion for flatness in a situation where no flatness
is available: Mathlib's `TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero` asks that the `pₖ`
generate the ambient module, which finitely many elements of `I` will not do unless `I` is finitely
generated, so `I` is first replaced by a finitely generated submodule containing the `pₖ` in which
the element already vanishes (`TensorProduct.eq_zero_of_fg_of_subtype_eq_zero`), and the generators
of that submodule are the extra family `g`. Being finitary, the certificate descends along a
filtered colimit; that is `Ideal.exists_hom_tmul_eq_zero_of_isColimit`. -/
public theorem _root_.Ideal.exists_tmul_vanishing_certificate
    {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] (I : Ideal R)
    {n : ℕ} (p : Fin n → R) (hp : ∀ k, p k ∈ I) (y : Fin n → N)
    (h : ∑ k, (⟨p k, hp k⟩ : ↥I) ⊗ₜ[R] y k = (0 : ↥I ⊗[R] N)) :
    ∃ (n' m : ℕ) (g : Fin n' → R) (_ : ∀ b, g b ∈ I) (Y : Fin m → N)
      (c : Fin n → Fin m → R) (d : Fin n' → Fin m → R),
      (∀ k, y k = ∑ l, c k l • Y l) ∧
      (∀ b, ∑ l, d b l • Y l = 0) ∧
      (∀ l, ∑ k, c k l • p k + ∑ b, d b l • g b = 0) := by
  classical
  set p' : Fin n → ↥I := fun k => ⟨p k, hp k⟩ with hp'def
  set P : Submodule R ↥I := Submodule.span R (Set.range p')
  have hPfg : P.FG := Submodule.fg_span (Set.finite_range p')
  have hmemP : ∀ k, p' k ∈ P := fun k => Submodule.subset_span ⟨k, rfl⟩
  have ht : LinearMap.rTensor N P.subtype (∑ k, (⟨p' k, hmemP k⟩ : ↥P) ⊗ₜ[R] y k) = 0 := by
    rw [map_sum]
    simp only [LinearMap.rTensor_tmul]
    exact h
  obtain ⟨Q, hPQ, hQfg, htQ⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hPfg ht
  obtain ⟨n', gQ, hgQ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hQfg
  have hmemQg : ∀ b, gQ b ∈ Q := fun b => by
    rw [← hgQ]
    exact Submodule.subset_span ⟨b, rfl⟩
  set mm : Fin n ⊕ Fin n' → ↥Q :=
    Sum.elim (fun k => (⟨p' k, hPQ (hmemP k)⟩ : ↥Q)) (fun b => (⟨gQ b, hmemQg b⟩ : ↥Q)) with hmmdef
  set nn : Fin n ⊕ Fin n' → N := Sum.elim y 0 with hnndef
  have hspan : Submodule.span R (Set.range mm) = ⊤ := by
    apply Submodule.map_injective_of_injective (Submodule.injective_subtype Q)
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    refine le_antisymm (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact (mm i).2
    · refine le_trans (le_of_eq hgQ.symm) (Submodule.span_le.mpr ?_)
      rintro _ ⟨b, rfl⟩
      exact Submodule.subset_span ⟨mm (Sum.inr b), ⟨Sum.inr b, rfl⟩, rfl⟩
  have hsum : ∑ i, mm i ⊗ₜ[R] nn i = (0 : ↥Q ⊗[R] N) := by
    rw [Fintype.sum_sum_type]
    have hzr : ∑ b : Fin n', mm (Sum.inr b) ⊗ₜ[R] nn (Sum.inr b) = (0 : ↥Q ⊗[R] N) := by
      simp [hnndef]
    rw [hzr, add_zero, ← htQ, map_sum]
    exact Finset.sum_congr rfl fun k _ => rfl
  obtain ⟨κ, aa, Y, h1, h2⟩ := TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero R hspan hsum
  refine ⟨n', κ, fun b => ((gQ b : ↥I) : R), fun b => (gQ b).2, Y,
    fun k l => aa (Sum.inl k) l, fun b l => aa (Sum.inr b) l, fun k => h1 (Sum.inl k),
    fun b => (h1 (Sum.inr b)).symm, fun l => ?_⟩
  have e : (I.subtype ∘ₗ Q.subtype) (∑ i, aa i l • mm i) = 0 := by rw [h2 l, map_zero]
  rw [map_sum] at e
  simp only [LinearMap.comp_apply, map_smul, smul_eq_mul] at e
  rw [Fintype.sum_sum_type] at e
  simpa [hmmdef, hp'def, smul_eq_mul] using e

/-- **A vanishing element of `I ⊗_R M` already vanishes at a finite stage of the system.**
Let `A`, `N` be a system of rings and compatible modules with colimits `R` and `M`, let `I` be an
ideal of `R`, and let `I_j = ρ_j^{-1}(I)` be its inverse image at the stage `j`. If the element
`∑ₖ pₖ ⊗ uₖ` of `I ⊗_R M` vanishes, where `pₖ` is the image of `aₖ ∈ A i` and `uₖ` the image of
`wₖ ∈ N i`, then already `∑ₖ aₖ ⊗ wₖ = 0` in `I_j ⊗_{A j} N j` for some `j ≥ i`.

This is the elementwise substitute, for the ideals `I_j`, for the statement that the tensor product
commutes with a filtered colimit over a *varying* base ring — the statement the source's proof of
Stacks 0471 invokes as "⊗ commutes with colimits" to make the generators of
`Tor₁^{A i}(N i, A i/I_i)` die at a finite stage. Unlike
`Module.exists_hom_isTrivialRelation_of_isColimit`, which proves the analogous descent from the
*flatness* of `M` over `R` through the equational criterion, this needs no flatness: the finitary
certificate of `Ideal.exists_tmul_vanishing_certificate` is produced from the vanishing alone, and
each of its finitely many witnesses and finitely many equations descends. The price is the extra
family `g` of that certificate, whose members are unknown elements of `I`; it is for their sake
that the ideal at the stage `j` has to be the whole inverse image `I_j`, not the image of `I_i`. -/
public theorem _root_.Ideal.exists_hom_tmul_eq_zero_of_isColimit
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {A : Λ ⥤ CommRingCat.{u}} {N : Λ ⥤ AddCommGrpCat.{u}}
    (mod : ∀ i, Module (A.obj i) (N.obj i))
    (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (a : A.obj i) (m : N.obj i),
      N.map h (a • m) = A.map h a • N.map h m)
    {ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R)}
    {ν : N ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M)}
    (hR : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
    (hM : IsColimit (Cocone.mk (AddCommGrpCat.of M) ν))
    (hν : ∀ (i : Λ) (a : A.obj i) (m : N.obj i),
      (ν.app i (a • m) : M) = HSMul.hSMul (α := R) (β := M) (ρ.app i a) (ν.app i m))
    (I : Ideal R) {i : Λ} {n : ℕ} (a : Fin n → A.obj i) (w : Fin n → N.obj i)
    (p : Fin n → ↥I) (hp : ∀ k, ((p k : R)) = ρ.app i (a k))
    (u : Fin n → M) (hu : ∀ k, u k = ν.app i (w k))
    (hzero : ∑ k, (p k) ⊗ₜ[R] (u k) = (0 : ↥I ⊗[R] M)) :
    ∃ (j : Λ) (h : i ⟶ j) (hmem : ∀ k, A.map h (a k) ∈ I.comap (ρ.app j).hom),
      ∑ k, (⟨A.map h (a k), hmem k⟩ : ↥(I.comap (ρ.app j).hom)) ⊗ₜ[↑(A.obj j)] (N.map h (w k))
        = (0 : ↥(I.comap (ρ.app j).hom) ⊗[↑(A.obj j)] ↑(N.obj j)) := by
  classical
  -- the finitary certificate of the vanishing, over `R`
  obtain ⟨n', m, g, hgI, Y, c, d, h1, h2, h3⟩ :=
    I.exists_tmul_vanishing_certificate (fun k => ((p k : R))) (fun k => (p k).2) u hzero
  -- lift every witness of the certificate to a common stage `j₁ ≥ i`
  choose jg _hjg gg hgg using fun b : Fin n' => Concrete.exists_hom_ι_eq_of_isColimit A hR (g b) i
  choose jY _hjY yy hyy using fun l : Fin m => Concrete.exists_hom_ι_eq_of_isColimit N hM (Y l) i
  choose jc _hjc cc hcc using fun q : Fin n × Fin m =>
    Concrete.exists_hom_ι_eq_of_isColimit A hR (c q.1 q.2) i
  choose jd _hjd dd hdd using fun q : Fin n' × Fin m =>
    Concrete.exists_hom_ι_eq_of_isColimit A hR (d q.1 q.2) i
  obtain ⟨j₁, hj₁⟩ := Preorder.exists_forall_le_of_fintype
    (Sum.elim (fun s : Option (Fin n') => s.elim i jg)
      (Sum.elim jY (Sum.elim (fun q : Fin n × Fin m => jc q) (fun q : Fin n' × Fin m => jd q))))
  have hi1 : i ≤ j₁ := hj₁ (.inl none)
  have hg1 : ∀ b, jg b ≤ j₁ := fun b => hj₁ (.inl (some b))
  have hY1 : ∀ l, jY l ≤ j₁ := fun l => hj₁ (.inr (.inl l))
  have hc1 : ∀ q, jc q ≤ j₁ := fun q => hj₁ (.inr (.inr (.inl q)))
  have hd1 : ∀ q, jd q ≤ j₁ := fun q => hj₁ (.inr (.inr (.inr q)))
  set h₁ : i ⟶ j₁ := homOfLE hi1
  set G : Fin n' → A.obj j₁ := fun b => A.map (homOfLE (hg1 b)) (gg b)
  set YY : Fin m → N.obj j₁ := fun l => N.map (homOfLE (hY1 l)) (yy l)
  set C : Fin n → Fin m → A.obj j₁ := fun k l => A.map (homOfLE (hc1 (k, l))) (cc (k, l))
  set D : Fin n' → Fin m → A.obj j₁ := fun b l => A.map (homOfLE (hd1 (b, l))) (dd (b, l))
  have hG : ∀ b, (ρ.app j₁ (G b) : R) = g b := fun b =>
    (app_map_const ρ (homOfLE (hg1 b)) _).trans (hgg b)
  have hYY : ∀ l, (ν.app j₁ (YY l) : M) = Y l := fun l =>
    (app_map_const ν (homOfLE (hY1 l)) _).trans (hyy l)
  have hC : ∀ k l, (ρ.app j₁ (C k l) : R) = c k l := fun k l =>
    (app_map_const ρ (homOfLE (hc1 (k, l))) _).trans (hcc (k, l))
  have hD : ∀ b l, (ρ.app j₁ (D b l) : R) = d b l := fun b l =>
    (app_map_const ρ (homOfLE (hd1 (b, l))) _).trans (hdd (b, l))
  -- the three families of equations of the certificate hold at later stages
  have e1 : ∀ k, ∃ (q : Λ) (f : j₁ ⟶ q),
      N.map f (N.map h₁ (w k)) = N.map f (∑ l, C k l • YY l) := by
    intro k
    have key : (ν.app j₁ (N.map h₁ (w k)) : M) = ν.app j₁ (∑ l, C k l • YY l) := by
      rw [app_map_const ν, ← hu k, h1 k, map_sum (ν.app j₁).hom]
      exact Finset.sum_congr rfl fun l _ => by rw [hν j₁, hC, hYY]
    obtain ⟨q, f, f', hff⟩ := Concrete.isColimit_exists_of_rep_eq N hM _ _ key
    exact ⟨q, f, by rw [hff, Subsingleton.elim f' f]⟩
  have e2 : ∀ b, ∃ (q : Λ) (f : j₁ ⟶ q), N.map f (∑ l, D b l • YY l) = 0 := by
    intro b
    have key : (ν.app j₁ (∑ l, D b l • YY l) : M) = ν.app j₁ (0 : N.obj j₁) := by
      rw [map_sum (ν.app j₁).hom, map_zero (ν.app j₁).hom, ← h2 b]
      exact Finset.sum_congr rfl fun l _ => by rw [hν j₁, hD, hYY]
    obtain ⟨q, f, f', hff⟩ := Concrete.isColimit_exists_of_rep_eq N hM _ _ key
    exact ⟨q, f, by rw [hff, map_zero (N.map f').hom]⟩
  have e3 : ∀ l, ∃ (q : Λ) (f : j₁ ⟶ q),
      A.map f (∑ k, C k l * A.map h₁ (a k) + ∑ b, D b l * G b) = 0 := by
    intro l
    have key : (ρ.app j₁ (∑ k, C k l * A.map h₁ (a k) + ∑ b, D b l * G b) : R)
        = ρ.app j₁ (0 : A.obj j₁) := by
      rw [map_add (ρ.app j₁).hom, map_sum (ρ.app j₁).hom, map_sum (ρ.app j₁).hom,
        map_zero (ρ.app j₁).hom]
      have hl := h3 l
      simp only [smul_eq_mul] at hl
      rw [← hl]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by
          rw [map_mul (ρ.app j₁).hom, hC, app_map_const ρ, ← hp k]
      · exact Finset.sum_congr rfl fun b _ => by rw [map_mul (ρ.app j₁).hom, hD, hG]
    obtain ⟨q, f, f', hff⟩ := Concrete.isColimit_exists_of_rep_eq A hR _ _ key
    exact ⟨q, f, by rw [hff, map_zero (A.map f').hom]⟩
  choose q1 f1 hf1 using e1
  choose q2 f2 hf2 using e2
  choose q3 f3 hf3 using e3
  obtain ⟨j, hjb⟩ := Preorder.exists_forall_le_of_fintype
    (Sum.elim (fun s : Option (Fin n) => s.elim j₁ q1) (Sum.elim q2 q3))
  have h1j : j₁ ≤ j := hjb (.inl none)
  have hq1 : ∀ k, q1 k ≤ j := fun k => hjb (.inl (some k))
  have hq2 : ∀ b, q2 b ≤ j := fun b => hjb (.inr (.inl b))
  have hq3 : ∀ l, q3 l ≤ j := fun l => hjb (.inr (.inr l))
  set g₁ : j₁ ⟶ j := homOfLE h1j
  set hh : i ⟶ j := homOfLE (le_trans hi1 h1j)
  -- the certificate, transported to the stage `j`
  have hmem : ∀ k, A.map hh (a k) ∈ I.comap (ρ.app j).hom := by
    intro k
    refine Ideal.mem_comap.mpr ?_
    have hv : (ρ.app j (A.map hh (a k)) : R) = ((p k : R)) :=
      (app_map_const ρ hh (a k)).trans (hp k).symm
    rw [show ((ρ.app j).hom (A.map hh (a k))) = (ρ.app j (A.map hh (a k)) : R) from rfl, hv]
    exact (p k).2
  have hmemG : ∀ b, A.map g₁ (G b) ∈ I.comap (ρ.app j).hom := by
    intro b
    refine Ideal.mem_comap.mpr ?_
    have hv : (ρ.app j (A.map g₁ (G b)) : R) = g b := by rw [app_map_const ρ, hG]
    rw [show ((ρ.app j).hom (A.map g₁ (G b))) = (ρ.app j (A.map g₁ (G b)) : R) from rfl, hv]
    exact hgI b
  refine ⟨j, hh, hmem, ?_⟩
  refine (I.comap (ρ.app j).hom).sum_tmul_eq_zero_of_vanishing_certificate
    (fun k => ⟨A.map hh (a k), hmem k⟩) (fun k => N.map hh (w k))
    (fun b => ⟨A.map g₁ (G b), hmemG b⟩) (fun l => N.map g₁ (YY l))
    (fun k l => A.map g₁ (C k l)) (fun b l => A.map g₁ (D b l)) ?_ ?_ ?_
  · intro k
    have key : N.map g₁ (N.map h₁ (w k)) = N.map g₁ (∑ l, C k l • YY l) := by
      rw [← map_map_apply N (f1 k) (homOfLE (hq1 k)) g₁ (N.map h₁ (w k)), hf1 k,
        map_map_apply N (f1 k) (homOfLE (hq1 k)) g₁]
    rw [← map_map_apply N h₁ g₁ hh (w k), key, map_sum (N.map g₁).hom]
    exact Finset.sum_congr rfl fun l _ => hsmul g₁ (C k l) (YY l)
  · intro b
    have key : N.map g₁ (∑ l, D b l • YY l) = 0 := by
      rw [← map_map_apply N (f2 b) (homOfLE (hq2 b)) g₁, hf2 b,
        map_zero (N.map (homOfLE (hq2 b))).hom]
    rw [← key, map_sum (N.map g₁).hom]
    exact (Finset.sum_congr rfl fun l _ => hsmul g₁ (D b l) (YY l)).symm
  · intro l
    have key : A.map g₁ (∑ k, C k l * A.map h₁ (a k) + ∑ b, D b l * G b) = 0 := by
      rw [← map_map_apply A (f3 l) (homOfLE (hq3 l)) g₁, hf3 l,
        map_zero (A.map (homOfLE (hq3 l))).hom]
    rw [map_add (A.map g₁).hom, map_sum (A.map g₁).hom, map_sum (A.map g₁).hom] at key
    simp only [smul_eq_mul]
    rw [← key]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul (A.map g₁).hom]
      congr 1
      exact (map_map_apply A h₁ g₁ hh (a k)).symm
    · exact Finset.sum_congr rfl fun b _ => by rw [map_mul (A.map g₁).hom]

/-- **`Module.sum_tmul_eq_zero_of_mem_ker_rTensor` with vanishing syzygies in place of trivial
ones.** The comparison map `Ker(I ⊗_R M → R ⊗_R M) → I' ⊗_{R'} M'` of Stacks 00MO vanishes as soon
as each of the finitely many generating syzygies of the chosen generators of `I` already dies in
`I' ⊗_{R'} M'` after being pushed to `M'`.

This is the form Stacks 0471 needs: there the syzygies die because the element of `I ⊗_R M` they
produce vanishes and `Ideal.exists_hom_tmul_eq_zero_of_isColimit` descends that vanishing, whereas
in Stacks 00R6 they become *trivial* relations because the colimit module is flat. Triviality
implies vanishing (`Module.IsTrivialRelation.sum_tmul_eq_zero`) but not conversely, so this is the
weaker hypothesis. -/
public theorem sum_tmul_eq_zero_of_mem_ker_rTensor'
    {R R' S S' M M' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R R'] [Algebra R S] [Algebra R' S'] [Algebra S S']
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module R' M'] [Module S M'] [Module S' M']
    [IsScalarTower R' S' M'] [IsScalarTower S S' M']
    {I : Ideal R} {I' : Ideal R'} {n : ℕ} (a : Fin n → I)
    (hspan : Ideal.span (Set.range fun k => (a k : R)) = I)
    (f : M →ₗ[S] M') (α : Fin n → I')
    (Φ : ↥I ⊗[R] M →+ ↥I' ⊗[R'] M')
    (hΦ : ∀ (k : Fin n) (m : M), Φ ((a k) ⊗ₜ[R] m) = (α k) ⊗ₜ[R'] (f m))
    {p : ℕ} (w : Fin p → Fin n → M)
    (hwspan : ∀ v : Fin n → M, (∑ k, (a k : R) • v k = 0) →
      ∃ b : Fin p → S, ∀ k, v k = ∑ q, b q • w q k)
    (hvanish : ∀ q, ∑ k, (α k) ⊗ₜ[R'] (f (w q k)) = (0 : ↥I' ⊗[R'] M'))
    (t : ↥I ⊗[R] M) (ht : t ∈ LinearMap.ker (I.subtype.rTensor M)) :
    Φ t = 0 :=
  sum_tmul_eq_zero_of_vanishing_syzygies (S' := S') a hspan f α Φ hΦ w hwspan hvanish t ht

/-- **Pushing a vanishing element of `I_j ⊗_{A j} N j` up the system keeps it vanishing.** This is
the analogue for `Ideal.exists_hom_tmul_eq_zero_of_isColimit` of
`Module.IsTrivialRelation.mapOfSystem'`: it is what lets the finitely many stages produced for
finitely many syzygies be replaced by a single stage dominating them all. -/
public theorem _root_.Ideal.tmul_eq_zero_of_mapOfSystem
    {R : Type u} [CommRing R] {Λ : Type u} [Preorder Λ]
    {A : Λ ⥤ CommRingCat.{u}} {N : Λ ⥤ AddCommGrpCat.{u}}
    (mod : ∀ i, Module (A.obj i) (N.obj i))
    (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (a : A.obj i) (m : N.obj i),
      N.map h (a • m) = A.map h a • N.map h m)
    {ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R)}
    (I : Ideal R) {i j j' : Λ} (h : i ⟶ j) (g : j ⟶ j') (h' : i ⟶ j') {n : ℕ}
    (a : Fin n → A.obj i) (w : Fin n → N.obj i)
    (hmem : ∀ k, A.map h (a k) ∈ I.comap (ρ.app j).hom)
    (hmem' : ∀ k, A.map h' (a k) ∈ I.comap (ρ.app j').hom)
    (hz : ∑ k, (⟨A.map h (a k), hmem k⟩ : ↥(I.comap (ρ.app j).hom)) ⊗ₜ[↑(A.obj j)]
      (N.map h (w k)) = (0 : ↥(I.comap (ρ.app j).hom) ⊗[↑(A.obj j)] ↑(N.obj j))) :
    ∑ k, (⟨A.map h' (a k), hmem' k⟩ : ↥(I.comap (ρ.app j').hom)) ⊗ₜ[↑(A.obj j')]
      (N.map h' (w k)) = (0 : ↥(I.comap (ρ.app j').hom) ⊗[↑(A.obj j')] ↑(N.obj j')) := by
  have hpush : ∀ x : ↥(I.comap (ρ.app j).hom), A.map g (x : A.obj j) ∈ I.comap (ρ.app j').hom :=
    fun x => by
      rw [Ideal.mem_comap, show ((ρ.app j').hom (A.map g (x : A.obj j)))
        = (ρ.app j' (A.map g (x : A.obj j)) : R) from rfl, app_map_const ρ]
      exact x.2
  set ι' : ↥(I.comap (ρ.app j).hom) →+ ↥(I.comap (ρ.app j').hom) :=
    { toFun := fun x => ⟨A.map g (x : A.obj j), hpush x⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) } with hι'
  have hι'apply : ∀ x : ↥(I.comap (ρ.app j).hom), ((ι' x : ↥(I.comap (ρ.app j').hom)) : A.obj j')
      = A.map g (x : A.obj j) := fun _ => rfl
  set F : ↥(I.comap (ρ.app j).hom) →+
      (↑(N.obj j) →+ (↥(I.comap (ρ.app j').hom) ⊗[↑(A.obj j')] ↑(N.obj j'))) :=
    { toFun := fun x =>
        { toFun := fun m => (ι' x) ⊗ₜ[↑(A.obj j')] (N.map g m)
          map_zero' := by simp
          map_add' := fun m₁ m₂ => by rw [map_add, TensorProduct.tmul_add] }
      map_zero' := by ext m; simp
      map_add' := fun x y => by ext m; simp [TensorProduct.add_tmul] } with hF
  have hbal : ∀ (r : A.obj j) (x : ↥(I.comap (ρ.app j).hom)) (m : ↑(N.obj j)),
      F (r • x) m = F x (r • m) := by
    intro r x m
    change (ι' (r • x)) ⊗ₜ[↑(A.obj j')] (N.map g m)
      = (ι' x) ⊗ₜ[↑(A.obj j')] (N.map g (r • m))
    rw [hsmul g r m, ← TensorProduct.smul_tmul]
    congr 1
    refine Subtype.ext ?_
    change A.map g ((r • x : ↥(I.comap (ρ.app j).hom)) : A.obj j)
      = (A.map g r) * (A.map g ((x : ↥(I.comap (ρ.app j).hom)) : A.obj j))
    rw [show ((r • x : ↥(I.comap (ρ.app j).hom)) : A.obj j) = r * (x : A.obj j) from rfl,
      map_mul (A.map g).hom]
  have hΘ := congrArg (TensorProduct.liftAddHom F hbal) hz
  rw [map_sum, map_zero] at hΘ
  rw [← hΘ]
  refine Finset.sum_congr rfl fun k _ => ?_
  change _ = (ι' ⟨A.map h (a k), hmem k⟩) ⊗ₜ[↑(A.obj j')] (N.map g (N.map h (w k)))
  rw [map_map_apply N h g h' (w k)]
  congr 1
  refine Subtype.ext ?_
  rw [hι'apply]
  exact (map_map_apply A h g h' (a k)).symm

end Module
