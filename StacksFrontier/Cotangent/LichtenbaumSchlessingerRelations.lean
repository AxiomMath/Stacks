module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import StacksFrontier.Cotangent.Biderivation
public import StacksFrontier.Cotangent.IdealTensorSquare
public import StacksFrontier.Cotangent.LichtenbaumSchlessingerFunctoriality

/-!
# Relations modulo trivial relations, and the degree `-2` term of the Lichtenbaum–Schlessinger
complex

Let `P → B` be a polynomial presentation with chosen generators `f_t` of its kernel `I`, let
`F = ⊕_t P` and `ρ : F → P`, `e_t ↦ f_t`. This file studies the quotient `F/TrivRel` of the free
module by the trivial relations `f_s e_t - f_t e_s`, which contains `Rel/TrivRel`, and the map

`μ : I ⊗_P I → F/TrivRel`, `ρ(u) ⊗ b ↦ b u`.

## Main definitions

* `Algebra.Presentation.trivialRelationsFree`: the trivial relations as a submodule of `F`.
* `Algebra.Presentation.freeQuotient`: `F/TrivRel`, and `freeQuotientRelationMap` the map
  `F/TrivRel → P` induced by `ρ`.
* `Algebra.Presentation.relationQuotientToFree`: the injection `Rel/TrivRel → F/TrivRel`.
* `Algebra.Presentation.kerTensorRelation`: the map `μ`.
* `Algebra.Presentation.TwistedFreeQuotient`: `F/TrivRel` as a bimodule over a polynomial ring
  through two algebra maps to `P`.

## Main results

* `Algebra.Presentation.relationMap_smul_sub_relationMap_smul_mem`: `ρ(y) x - ρ(x) y` is a
  trivial relation for all `x, y ∈ F`.
* `Algebra.Presentation.ker_smul_mem_trivialRelationsFree`: `I · Rel ⊆ TrivRel`.
* `Algebra.Presentation.exists_kerTensorRelation_eq`: every relation with coefficients in `I` is
  a value of `μ` on `Ker(I ⊗ I → I²)`.
* `Algebra.Presentation.mem_antisymm_of_kerTensorRelation_eq_zero`: the kernel of `μ` consists of
  antisymmetric tensors.
* `Algebra.Presentation.exists_biderivation_freeQuotient`: Stacks 09CF for `F/TrivRel`, a
  biderivation `R[S] → F/TrivRel` lifting the difference of two algebra maps `R[S] → P` over `B`.
* `Algebra.Presentation.freeQuotient_sub_sub_add_mul`: the alternating difference of four such
  biderivations is a derivation with values in `Rel/TrivRel`.

## Implementation notes

These are the two facts used in [Stacks, Tag 09CG] to identify `H^{-2}` of the
Lichtenbaum–Schlessinger complex with `Ker(I ⊗ I → I²)` modulo antisymmetric tensors, namely
`Tor₂^P(B, B)` modulo the image of `∧²_B(I/I²)`: the source computes
`Tor₂^P(B, B) = Ker(Rel ⊗ B → F ⊗ B)` and observes that the image of `∧²_B(I/I²)` is that of
`TrivRel ⊗ B`.

## References

* [Stacks Project, Tag 09CG](https://stacks.math.columbia.edu/tag/09CG)
-/

@[expose] public section

open TensorProduct Stacks.Cotangent

universe u v w

noncomputable section

namespace Algebra.Presentation

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {X T : Type w} (P : Algebra.Presentation A B X T)

/-- The trivial relations `f_s e_t - f_t e_s`, as a submodule of the free module `F`. -/
def trivialRelationsFree : Submodule P.Ring (T →₀ P.Ring) :=
  Submodule.span P.Ring (Set.range fun p : T × T ↦ trivialRelation P p.1 p.2)

/-- The free module on the generators modulo the trivial relations. -/
abbrev freeQuotient := (T →₀ P.Ring) ⧸ trivialRelationsFree P

/-- Each trivial relation `f_s e_t - f_t e_s` lies in the kernel of `ρ`. -/
theorem relationMap_trivialRelation (s t : T) : relationMap P (trivialRelation P s t) = 0 :=
  LinearMap.mem_ker.1 (trivialRelationInRelations P s t).2

/-- The trivial relations are relations: `TrivRel ⊆ Rel`. -/
theorem trivialRelationsFree_le_relations : trivialRelationsFree P ≤ relations P :=
  Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact relationMap_trivialRelation P p.1 p.2)

/-- The map `F/TrivRel → P` induced by `e_t ↦ f_t`. -/
def freeQuotientRelationMap : freeQuotient P →ₗ[P.Ring] P.Ring :=
  (trivialRelationsFree P).liftQ (relationMap P)
    (le_trans (trivialRelationsFree_le_relations P) le_rfl)

/-- `freeQuotientRelationMap` sends the class of `u` to `ρ(u)`. -/
@[simp]
theorem freeQuotientRelationMap_mk (u : T →₀ P.Ring) :
    freeQuotientRelationMap P (Submodule.Quotient.mk u) = relationMap P u := rfl

/-- `ρ` is the linear combination map `e_t ↦ f_t`. -/
theorem relationMap_eq_linearCombination :
    relationMap P = Finsupp.linearCombination P.Ring P.relation := by
  ext t
  simp [relationMap]

/-- The image of `ρ` is contained in `I`. -/
theorem relationMap_mem_ker (u : T →₀ P.Ring) : relationMap P u ∈ P.ker := by
  rw [relationMap_eq_linearCombination, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun t _ ↦ Ideal.mul_mem_left _ _ (P.relation_mem_ker t)

/-- Every element of `I` is of the form `ρ(u)` for some `u ∈ F`. -/
theorem exists_relationMap_eq (a : P.Ring) (ha : a ∈ P.ker) :
    ∃ u : T →₀ P.Ring, relationMap P u = a := by
  rw [← P.span_range_relation_eq_ker] at ha
  change a ∈ Submodule.span P.Ring (Set.range P.relation) at ha
  rw [← Finsupp.range_linearCombination] at ha
  obtain ⟨u, rfl⟩ := ha
  exact ⟨u, by rw [relationMap_eq_linearCombination]⟩

/-- The trivial relations in `F` are the image of the trivial relations in `Rel` under the
inclusion `Rel → F`. -/
theorem trivialRelationsFree_eq_map :
    trivialRelationsFree P = (trivialRelations P).map (relations P).subtype := by
  rw [trivialRelations, Submodule.map_span, trivialRelationsFree, ← Set.range_comp]
  rfl

/-- The injection `Rel/TrivRel → F/TrivRel`. -/
def relationQuotientToFree : relationQuotient P →ₗ[P.Ring] freeQuotient P :=
  Submodule.mapQ _ _ (relations P).subtype
    (by rw [trivialRelationsFree_eq_map]; exact Submodule.le_comap_map _ _)

/-- `relationQuotientToFree` sends the class of `r ∈ Rel` to the class of `r` in `F/TrivRel`. -/
@[simp]
theorem relationQuotientToFree_mk (r : relations P) :
    relationQuotientToFree P (Submodule.Quotient.mk r) = Submodule.Quotient.mk (r : T →₀ P.Ring) :=
  rfl

/-- The map `Rel/TrivRel → F/TrivRel` is injective. -/
theorem relationQuotientToFree_injective : Function.Injective (relationQuotientToFree P) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [LinearMap.mem_ker, Submodule.mkQ_apply, relationQuotientToFree_mk,
    Submodule.Quotient.mk_eq_zero, trivialRelationsFree_eq_map] at hx
  obtain ⟨r', hr', he⟩ := hx
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rwa [← Subtype.ext he]

/-- The composite `Rel/TrivRel → F/TrivRel → P` is zero. -/
theorem freeQuotientRelationMap_relationQuotientToFree (x : relationQuotient P) :
    freeQuotientRelationMap P (relationQuotientToFree P x) = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective _ x
  exact LinearMap.mem_ker.1 r.2

/-- Every element of the kernel of `freeQuotientRelationMap : F/TrivRel → P` lies in the image of
`Rel/TrivRel`. -/
theorem exists_relationQuotientToFree_eq (x : freeQuotient P)
    (hx : freeQuotientRelationMap P x = 0) : ∃ y, relationQuotientToFree P y = x := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ x
  exact ⟨Submodule.Quotient.mk ⟨u, LinearMap.mem_ker.2 hx⟩, rfl⟩

/-- **`ρ(y) x - ρ(x) y` is a trivial relation.** -/
theorem relationMap_smul_sub_relationMap_smul_mem (x y : T →₀ P.Ring) :
    relationMap P y • x - relationMap P x • y ∈ trivialRelationsFree P := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' =>
    rw [map_add, add_smul, smul_add]
    convert add_mem hx hx' using 1
    abel
  | single s a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' =>
      rw [map_add, add_smul, smul_add]
      convert add_mem hy hy' using 1
      abel
    | single t b =>
      have h : relationMap P (Finsupp.single t b) • Finsupp.single s a -
          relationMap P (Finsupp.single s a) • Finsupp.single t b =
          (a * b) • trivialRelation P t s := by
        rw [relationMap_single, relationMap_single, trivialRelation, smul_sub,
          Finsupp.smul_single, Finsupp.smul_single, Finsupp.smul_single, Finsupp.smul_single]
        congr 1 <;> congr 1 <;> simp only [smul_eq_mul] <;> ring
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(t, s), rfl⟩)

/-- For `x, y ∈ F/TrivRel`, `ρ(y) x = ρ(x) y`. -/
theorem freeQuotientRelationMap_smul_comm (x y : freeQuotient P) :
    freeQuotientRelationMap P y • x = freeQuotientRelationMap P x • y := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, freeQuotientRelationMap_mk,
    freeQuotientRelationMap_mk, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.eq]
  exact relationMap_smul_sub_relationMap_smul_mem P x y

/-- **The difference of four biderivations into `F/TrivRel`.** Let `l, l', t₀, t₁ : S → F/TrivRel`
satisfy the Leibniz rules for the pairs of actions `(α₀, α₁)`, `(β₀, β₁)`, `(α₀, β₀)`,
`(α₁, β₁)` and lift the differences of their pairs along `ρ`. Then `u = l - l' - t₀ + t₁`
satisfies the Leibniz rule for `(α₀, β₁)`; and `ρ ∘ u = 0`, so `u` takes values in
`Rel/TrivRel`, where all four actions agree. -/
theorem freeQuotient_sub_sub_add_mul {S : Type*} [Mul S] (α₀ α₁ β₀ β₁ : S → P.Ring)
    (l l' t₀ t₁ : S → freeQuotient P) (x y : S)
    (hl : l (x * y) = α₀ x • l y + α₁ y • l x) (hl' : l' (x * y) = β₀ x • l' y + β₁ y • l' x)
    (ht₀ : t₀ (x * y) = α₀ x • t₀ y + β₀ y • t₀ x)
    (ht₁ : t₁ (x * y) = α₁ x • t₁ y + β₁ y • t₁ x)
    (hρl : freeQuotientRelationMap P (l x) = α₀ x - α₁ x)
    (hρl' : freeQuotientRelationMap P (l' y) = β₀ y - β₁ y)
    (hρt₀ : freeQuotientRelationMap P (t₀ x) = α₀ x - β₀ x)
    (hρt₁ : freeQuotientRelationMap P (t₁ y) = α₁ y - β₁ y) :
    l (x * y) - l' (x * y) - t₀ (x * y) + t₁ (x * y) =
      α₀ x • (l y - l' y - t₀ y + t₁ y) + β₁ y • (l x - l' x - t₀ x + t₁ x) := by
  have c₁ := freeQuotientRelationMap_smul_comm P (l x) (t₁ y)
  have c₂ := freeQuotientRelationMap_smul_comm P (t₀ x) (l' y)
  rw [hρl, hρt₁] at c₁
  rw [hρl', hρt₀] at c₂
  rw [hl, hl', ht₀, ht₁]
  linear_combination (norm := module) c₁ - c₂

/-- **`I · Rel ⊆ TrivRel`.** -/
theorem ker_smul_mem_trivialRelationsFree {a : P.Ring} (ha : a ∈ P.ker)
    {r : T →₀ P.Ring} (hr : relationMap P r = 0) : a • r ∈ trivialRelationsFree P := by
  obtain ⟨u, rfl⟩ := exists_relationMap_eq P a ha
  have := relationMap_smul_sub_relationMap_smul_mem P r u
  rwa [hr, zero_smul, sub_zero] at this

/-- In `F/TrivRel`, multiplication by an element of `I` only depends on the image under `ρ`. -/
theorem ker_smul_mk_eq {b : P.Ring} (hb : b ∈ P.ker) {u u' : T →₀ P.Ring}
    (h : relationMap P u = relationMap P u') :
    b • (Submodule.Quotient.mk u : freeQuotient P) = b • Submodule.Quotient.mk u' := by
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    ← smul_sub]
  exact ker_smul_mem_trivialRelationsFree P hb (by rw [map_sub, h, sub_self])

/-- An element of `F` mapping to a given element of `I`. -/
def kerLift (a : P.ker) : T →₀ P.Ring := (exists_relationMap_eq P a a.2).choose

/-- The element `kerLift P a` of `F` maps to `a` under `ρ`. -/
theorem relationMap_kerLift (a : P.ker) : relationMap P (kerLift P a) = a :=
  (exists_relationMap_eq P a a.2).choose_spec

/-- The map `μ : I ⊗_P I → F/TrivRel`, `ρ(u) ⊗ b ↦ b u`. -/
def kerTensorRelation : P.ker ⊗[P.Ring] P.ker →ₗ[P.Ring] freeQuotient P :=
  _root_.TensorProduct.lift <| LinearMap.mk₂ P.Ring
    (fun a b : P.ker ↦ (b : P.Ring) • (Submodule.Quotient.mk (kerLift P a) : freeQuotient P))
    (fun a a' b ↦ by
      rw [← smul_add, ← Submodule.Quotient.mk_add]
      exact ker_smul_mk_eq P b.2 (by simp [relationMap_kerLift]))
    (fun c a b ↦ by
      rw [smul_comm c, ← Submodule.Quotient.mk_smul]
      exact ker_smul_mk_eq P b.2 (by simp [relationMap_kerLift]))
    (fun a b b' ↦ by rw [Submodule.coe_add, add_smul])
    (fun c a b ↦ by rw [Submodule.coe_smul, smul_eq_mul, mul_smul])

/-- `μ(a ⊗ b) = b u` for every `u ∈ F` with `ρ(u) = a`. -/
theorem kerTensorRelation_tmul (a b : P.ker) (u : T →₀ P.Ring) (hu : relationMap P u = a) :
    kerTensorRelation P (a ⊗ₜ b) = (b : P.Ring) • Submodule.Quotient.mk u := by
  change (b : P.Ring) • (Submodule.Quotient.mk (kerLift P a) : freeQuotient P) = _
  exact ker_smul_mk_eq P b.2 (by rw [relationMap_kerLift, hu])

/-- `μ` is symmetric: `μ(a ⊗ b) = μ(b ⊗ a)`. -/
theorem kerTensorRelation_comm (a b : P.ker) :
    kerTensorRelation P (a ⊗ₜ b) = kerTensorRelation P (b ⊗ₜ a) := by
  rw [kerTensorRelation_tmul P a b _ (relationMap_kerLift P a),
    kerTensorRelation_tmul P b a _ (relationMap_kerLift P b)]
  have := freeQuotientRelationMap_smul_comm P (Submodule.Quotient.mk (kerLift P a))
    (Submodule.Quotient.mk (kerLift P b))
  simpa [relationMap_kerLift] using this

/-- `μ` vanishes on antisymmetric tensors. -/
theorem kerTensorRelation_antisymm {ξ : P.ker ⊗[P.Ring] P.ker}
    (hξ : ξ ∈ idealTensorAntisymm P.ker) : kerTensorRelation P ξ = 0 := by
  refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy ↦ by rw [map_add, hx, hy,
    add_zero]) (fun r x _ hx ↦ by rw [map_smul, hx, smul_zero]) hξ
  rintro _ ⟨⟨a, b⟩, rfl⟩
  rw [map_sub, kerTensorRelation_comm, sub_self]

/-- The composite `I ⊗_P I → F/TrivRel → P` of `μ` and `freeQuotientRelationMap` is the
multiplication map `a ⊗ b ↦ a b`. -/
theorem freeQuotientRelationMap_kerTensorRelation (ξ : P.ker ⊗[P.Ring] P.ker) :
    freeQuotientRelationMap P (kerTensorRelation P ξ) = idealTensorMul P.ker ξ := by
  induction ξ using _root_.TensorProduct.inductionOn with
  | tmul a b =>
    rw [kerTensorRelation_tmul P a b _ (relationMap_kerLift P a), map_smul,
      freeQuotientRelationMap_mk, relationMap_kerLift, idealTensorMul_tmul, smul_eq_mul, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

open scoped Classical in
/-- The map `F ⊗_P I → F`, `u ⊗ b ↦ b u`, which is injective because `F` is free. -/
def freeTensorKer : (T →₀ P.Ring) ⊗[P.Ring] P.ker →ₗ[P.Ring] (T →₀ P.Ring) :=
  Finsupp.mapRange.linearMap P.ker.subtype ∘ₗ (finsuppScalarLeft P.Ring P.ker T).toLinearMap

open scoped Classical in
/-- `freeTensorKer` sends `u ⊗ b` to `b u`. -/
theorem freeTensorKer_tmul (u : T →₀ P.Ring) (b : P.ker) :
    freeTensorKer P (u ⊗ₜ b) = (b : P.Ring) • u := by
  ext t
  simp [freeTensorKer, finsuppScalarLeft_apply_tmul_apply, mul_comm]

open scoped Classical in
/-- The map `freeTensorKer : F ⊗_P I → F` is injective. -/
theorem freeTensorKer_injective : Function.Injective (freeTensorKer P) :=
  (Finsupp.mapRange_injective _ (map_zero _) Subtype.val_injective).comp
    (finsuppScalarLeft P.Ring P.ker T).injective

/-- The map `F → I`, `u ↦ ρ(u)`. -/
def relationMapToKer : (T →₀ P.Ring) →ₗ[P.Ring] P.ker :=
  LinearMap.codRestrict _ (relationMap P) (relationMap_mem_ker P)

/-- The map `relationMapToKer : F → I` is surjective. -/
theorem relationMapToKer_surjective : Function.Surjective (relationMapToKer P) := by
  intro a
  obtain ⟨u, hu⟩ := exists_relationMap_eq P a a.2
  exact ⟨u, Subtype.ext hu⟩

/-- `μ ∘ (ρ ⊗ id_I) : F ⊗_P I → F/TrivRel` is `freeTensorKer` followed by the projection
`F → F/TrivRel`. -/
theorem kerTensorRelation_rTensor (η : (T →₀ P.Ring) ⊗[P.Ring] P.ker) :
    kerTensorRelation P ((relationMapToKer P).rTensor P.ker η) =
      Submodule.Quotient.mk (freeTensorKer P η) := by
  induction η using _root_.TensorProduct.inductionOn with
  | tmul u b =>
    rw [LinearMap.rTensor_tmul, kerTensorRelation_tmul P _ b u rfl, freeTensorKer_tmul,
      Submodule.Quotient.mk_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Submodule.Quotient.mk_add]

/-- The generator `f_t` as an element of `I`. -/
private def relationKer (t : T) : P.ker := ⟨P.relation t, P.relation_mem_ker t⟩

/-- `ρ(e_t) = f_t`. -/
private theorem relationMap_single_one (t : T) :
    relationMap P (Finsupp.single t 1) = P.relation t := by
  simp [relationMap_single]

/-- **The kernel of `μ` consists of antisymmetric tensors.** -/
theorem mem_antisymm_of_kerTensorRelation_eq_zero {ξ : P.ker ⊗[P.Ring] P.ker}
    (hξ : kerTensorRelation P ξ = 0) : ξ ∈ idealTensorAntisymm P.ker := by
  obtain ⟨η, rfl⟩ := LinearMap.rTensor_surjective P.ker (relationMapToKer_surjective P) ξ
  rw [kerTensorRelation_rTensor, Submodule.Quotient.mk_eq_zero, trivialRelationsFree,
    Finsupp.mem_span_range_iff_exists_finsupp] at hξ
  obtain ⟨c, hc⟩ := hξ
  have hη : η = c.sum fun p a ↦ a • (Finsupp.single p.2 1 ⊗ₜ relationKer P p.1 -
      Finsupp.single p.1 1 ⊗ₜ relationKer P p.2) := by
    apply freeTensorKer_injective P
    rw [← hc, Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [map_smul, map_sub, freeTensorKer_tmul, freeTensorKer_tmul, trivialRelation]
    simp [relationKer, Finsupp.smul_single]
  rw [hη, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun p _ ↦ ?_
  rw [map_smul, map_sub, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
  have e : ∀ t, relationMapToKer P (Finsupp.single t 1) = relationKer P t := fun t ↦
    Subtype.ext (relationMap_single_one P t)
  rw [e, e]
  exact Submodule.smul_mem _ _ (tmul_sub_tmul_mem_idealTensorAntisymm P.ker _ _)

/-- **Relations with coefficients in `I` are values of `μ` on `Ker(I ⊗ I → I²)`.** -/
theorem exists_kerTensorRelation_eq (r : T →₀ P.Ring) (hr : relationMap P r = 0)
    (hrI : ∀ t, r t ∈ P.ker) :
    ∃ ξ : P.ker ⊗[P.Ring] P.ker, idealTensorMul P.ker ξ = 0 ∧
      kerTensorRelation P ξ = Submodule.Quotient.mk r := by
  refine ⟨∑ t ∈ r.support, relationKer P t ⊗ₜ ⟨r t, hrI t⟩, ?_, ?_⟩
  · rw [map_sum, ← hr, relationMap_eq_linearCombination,
      Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    simp [relationKer, smul_eq_mul, mul_comm]
  · rw [map_sum]
    conv_rhs => rw [← Finsupp.sum_single r, Finsupp.sum, ← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [kerTensorRelation_tmul P _ _ (Finsupp.single t 1) (relationMap_single_one P t),
      ← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl

/-! ### `F/TrivRel → F ⊗_P B` and the differentials of `L` -/

section Tensor

open KaehlerDifferential

/-- For a `P`-module `M`, `p ∈ P` and `m ∈ M`, `1 ⊗ p m = p̄ (1 ⊗ m)` in `B ⊗_P M`, where `p̄` is
the image of `p` in `B`. -/
theorem tmul_smul_eq_algebraMap_smul {M : Type*} [AddCommGroup M] [Module P.Ring M] (p : P.Ring)
    (m : M) : (1 : B) ⊗ₜ[P.Ring] (p • m) = algebraMap P.Ring B p • ((1 : B) ⊗ₜ[P.Ring] m) := by
  rw [tmul_smul, smul_tmul', Algebra.smul_def, mul_one, smul_tmul', smul_eq_mul, mul_one]

/-- `F/TrivRel → F ⊗_P B`, `u ↦ 1 ⊗ u`. -/
def freeQuotientToTensor : freeQuotient P →ₗ[P.Ring] B ⊗[P.Ring] (T →₀ P.Ring) :=
  (trivialRelationsFree P).liftQ (TensorProduct.mk P.Ring B (T →₀ P.Ring) 1) (by
    rw [trivialRelationsFree, Submodule.span_le]
    rintro _ ⟨⟨s, t⟩, rfl⟩
    have h : ∀ (t' : T) (c : P.Ring), c ∈ P.ker →
        (1 : B) ⊗ₜ[P.Ring] Finsupp.single t' c = 0 := fun t' c hc => by
      rw [← mul_one c, ← smul_eq_mul, ← Finsupp.smul_single, tmul_smul, smul_tmul',
        Algebra.smul_def, mul_one, show algebraMap P.Ring B c = 0 from hc, zero_tmul]
    change (1 : B) ⊗ₜ[P.Ring] trivialRelation P s t = 0
    rw [trivialRelation, tmul_sub, h _ _ (P.relation_mem_ker s), h _ _ (P.relation_mem_ker t),
      sub_zero])

/-- `freeQuotientToTensor` sends the class of `u` to `1 ⊗ u`. -/
@[simp]
theorem freeQuotientToTensor_mk (u : T →₀ P.Ring) :
    freeQuotientToTensor P (Submodule.Quotient.mk u) = (1 : B) ⊗ₜ u := rfl

/-- `freeQuotientToTensor` sends `r m` to `r̄ (1 ⊗ m)`, where `r̄` is the image of `r` in `B`. -/
theorem freeQuotientToTensor_smul (r : P.Ring) (m : freeQuotient P) :
    freeQuotientToTensor P (r • m) = algebraMap P.Ring B r • freeQuotientToTensor P m := by
  rw [map_smul, algebraMap_smul]

/-- `F/TrivRel → Ω_{P/A} ⊗ B` through the differential of `LS` is `1 ⊗ d ∘ ρ`. -/
theorem relationDifferentialB_freeQuotientToTensor (m : freeQuotient P) :
    relationDifferentialB P (freeQuotientToTensor P m) =
      (1 : B) ⊗ₜ D A P.Ring (freeQuotientRelationMap P m) := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ m
  rw [Submodule.mkQ_apply, freeQuotientToTensor_mk, relationDifferentialB_tmul,
    freeQuotientRelationMap_mk, derivation_relationMap, tmul_add, left_eq_add]
  rw [Finsupp.sum, tmul_sum]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [tmul_smul_eq_algebraMap_smul,
    show algebraMap P.Ring B (P.relation t) = 0 from P.relation_mem_ker t, zero_smul]

/-- `relationBoundaryR` is the composite `Rel/TrivRel → F/TrivRel → B ⊗_P F`. -/
theorem relationBoundaryR_eq (q : relationQuotient P) :
    relationBoundaryR P q = freeQuotientToTensor P (relationQuotientToFree P q) := by
  obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [relationBoundaryR_mk, Submodule.mkQ_apply, relationQuotientToFree_mk,
    freeQuotientToTensor_mk]

/-- `relationBoundary` sends `1 ⊗ q` to the image of `q` under
`Rel/TrivRel → F/TrivRel → B ⊗_P F`. -/
theorem relationBoundary_tmul_one (q : relationQuotient P) :
    letI := relationModule P
    relationBoundary P ((1 : B) ⊗ₜ q) = freeQuotientToTensor P (relationQuotientToFree P q) := by
  let := relationModule P
  change relationBoundaryB P (relationBaseChangeEquiv P ((1 : B) ⊗ₜ q)) = _
  rw [relationBaseChangeEquiv_tmul]
  exact relationBoundaryR_eq P q

/-- Under the identifications of the terms of degree `-2` and `-1` of the Lichtenbaum–Schlessinger
complex with `B ⊗_P (Rel/TrivRel)` and `B ⊗_P F`, the differential `d^{-2}` is
`relationBoundary`. -/
theorem lsComplex_d_negTwo_inv_apply (w : B ⊗[P.Ring] relationQuotient P) :
    letI := relationModule P
    (lichtenbaumSchlessingerComplex P).freeIso.hom
        ((lichtenbaumSchlessingerComplex P).complex.d (-2) (-1)
          ((lichtenbaumSchlessingerComplex P).relationIso.inv w)) = relationBoundary P w := by
  let := relationModule P
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul b q =>
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective _ q
    have hb : b ⊗ₜ[P.Ring] Submodule.mkQ (trivialRelations P) r =
        b • ((1 : B) ⊗ₜ[P.Ring] Submodule.mkQ (trivialRelations P) r) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [hb, map_smul, map_smul, map_smul, map_smul,
      (lichtenbaumSchlessingerComplex P).d_relation, relationBoundary_tmul]

/-- Under the identifications of the terms of degree `-1` and `0` of the Lichtenbaum–Schlessinger
complex with `B ⊗_P F` and `B ⊗_P Ω_{P/A}`, the differential `d^{-1}` is
`relationDifferentialB`. -/
theorem lsComplex_d_negOne_inv_apply (w : B ⊗[P.Ring] (T →₀ P.Ring)) :
    (lichtenbaumSchlessingerComplex P).differentialIso.hom
        ((lichtenbaumSchlessingerComplex P).complex.d (-1) 0
          ((lichtenbaumSchlessingerComplex P).freeIso.inv w)) = relationDifferentialB P w := by
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul b x => rw [(lichtenbaumSchlessingerComplex P).d_free, relationDifferentialB_tmul]

end Tensor

/-! ### `F/TrivRel` as a bimodule, and biderivations into it -/

section Twisted

variable {R : Type*} [CommRing R] [Algebra R P.Ring] {S : Type*}

/-- `F/TrivRel` regarded as a bimodule over `R[S]`, the left action through `α` and the right
action through `β`. -/
def TwistedFreeQuotient (_α _β : MvPolynomial S R →ₐ[R] P.Ring) : Type _ := freeQuotient P

variable (α β : MvPolynomial S R →ₐ[R] P.Ring)

/-- The additive group structure of `F/TrivRel`. -/
instance : AddCommGroup (TwistedFreeQuotient P α β) :=
  Submodule.Quotient.addCommGroup (trivialRelationsFree P)

/-- The `R`-module structure of `F/TrivRel`. -/
instance : Module R (TwistedFreeQuotient P α β) :=
  Submodule.Quotient.module' (trivialRelationsFree P)

/-- The left action of `R[S]`, through `α`. -/
instance : Module (MvPolynomial S R) (TwistedFreeQuotient P α β) :=
  Module.compHom (freeQuotient P) α.toRingHom

/-- The right action of `R[S]`, through `β`. -/
instance : Module (MvPolynomial S R)ᵐᵒᵖ (TwistedFreeQuotient P α β) :=
  Module.compHom (freeQuotient P) (β.toRingHom.fromOpposite fun _ _ => Commute.all _ _)

/-- The identification of the bimodule with `F/TrivRel`. -/
def TwistedFreeQuotient.equiv : TwistedFreeQuotient P α β ≃+ freeQuotient P := AddEquiv.refl _

/-- The left action of `s ∈ R[S]` is multiplication by `α(s)`. -/
theorem TwistedFreeQuotient.equiv_smul (s : MvPolynomial S R) (m : TwistedFreeQuotient P α β) :
    TwistedFreeQuotient.equiv P α β (s • m) =
      (α s • (TwistedFreeQuotient.equiv P α β m : freeQuotient P) : freeQuotient P) := rfl

/-- The right action of `s ∈ R[S]` is multiplication by `β(s)`. -/
theorem TwistedFreeQuotient.equiv_op_smul (s : MvPolynomial S R)
    (m : TwistedFreeQuotient P α β) :
    TwistedFreeQuotient.equiv P α β (MulOpposite.op s • m) =
      (β s • (TwistedFreeQuotient.equiv P α β m : freeQuotient P) : freeQuotient P) := rfl

/-- The action of `a ∈ R` is its action on `F/TrivRel`. -/
theorem TwistedFreeQuotient.equiv_smul_A (a : R) (m : TwistedFreeQuotient P α β) :
    TwistedFreeQuotient.equiv P α β (a • m) =
      (a • (TwistedFreeQuotient.equiv P α β m : freeQuotient P) : freeQuotient P) := rfl

/-- The left action of `R[S]` is compatible with the action of `R`. -/
instance : IsScalarTower R (MvPolynomial S R) (TwistedFreeQuotient P α β) :=
  ⟨fun a s m => (TwistedFreeQuotient.equiv P α β).injective (by
    rw [TwistedFreeQuotient.equiv_smul, TwistedFreeQuotient.equiv_smul_A,
      TwistedFreeQuotient.equiv_smul, map_smul, smul_assoc])⟩

/-- The right action of `R[S]` is compatible with the action of `R`. -/
instance : IsScalarTower R (MvPolynomial S R)ᵐᵒᵖ (TwistedFreeQuotient P α β) :=
  ⟨fun a s m => (TwistedFreeQuotient.equiv P α β).injective (by
    rw [TwistedFreeQuotient.equiv_smul_A, ← MulOpposite.op_unop s,
      TwistedFreeQuotient.equiv_op_smul, ← MulOpposite.op_smul, TwistedFreeQuotient.equiv_op_smul,
      map_smul, smul_assoc])⟩

/-- The left and right actions of `R[S]` commute. -/
instance : SMulCommClass (MvPolynomial S R) (MvPolynomial S R)ᵐᵒᵖ (TwistedFreeQuotient P α β) :=
  ⟨fun s t m => (TwistedFreeQuotient.equiv P α β).injective (by
    rw [← MulOpposite.op_unop t, TwistedFreeQuotient.equiv_smul,
      TwistedFreeQuotient.equiv_op_smul, TwistedFreeQuotient.equiv_op_smul,
      TwistedFreeQuotient.equiv_smul, smul_comm])⟩

/-- **Stacks 09CF applied to `F/TrivRel`.** Values `m_s` on the variables with
`ρ(m_s) = α(x_s) - β(x_s)` are compatible, hence extend to a biderivation. -/
theorem exists_biderivation_twisted (m : S → freeQuotient P)
    (hm : ∀ s, freeQuotientRelationMap P (m s) = α (MvPolynomial.X s) - β (MvPolynomial.X s)) :
    ∃ D : Biderivation R (MvPolynomial S R) (TwistedFreeQuotient P α β),
      ∀ s, D (MvPolynomial.X s) = (TwistedFreeQuotient.equiv P α β).symm (m s) := by
  refine (Biderivation.existsUnique_mvPolynomial _ fun s t => ?_).exists
  apply (TwistedFreeQuotient.equiv P α β).injective
  simp only [map_add, TwistedFreeQuotient.equiv_smul, TwistedFreeQuotient.equiv_op_smul,
    AddEquiv.apply_symm_apply]
  have h := freeQuotientRelationMap_smul_comm P (m t) (m s)
  rw [hm, hm, sub_smul, sub_smul] at h
  calc α (MvPolynomial.X s) • m t + β (MvPolynomial.X t) • m s =
      (α (MvPolynomial.X s) • m t - β (MvPolynomial.X s) • m t) +
        β (MvPolynomial.X s) • m t + β (MvPolynomial.X t) • m s := by abel
    _ = (α (MvPolynomial.X t) • m s - β (MvPolynomial.X t) • m s) +
        β (MvPolynomial.X s) • m t + β (MvPolynomial.X t) • m s := by rw [h]
    _ = _ := by abel

/-- **Biderivations into `F/TrivRel` lifting a difference.** For two `R`-algebra maps
`α, β : R[S] → P` whose difference on each variable lies in `I`, there is an `R`-linear map
`D : R[S] → F/TrivRel` with `D(xy) = α(x) D(y) + β(y) D(x)` and `ρ ∘ D = α - β`. -/
theorem exists_biderivation_freeQuotient
    (h : ∀ s, α (MvPolynomial.X s) - β (MvPolynomial.X s) ∈ P.ker) :
    ∃ D : MvPolynomial S R →ₗ[R] freeQuotient P,
      (∀ x y, D (x * y) = α x • D y + β y • D x) ∧
        ∀ x, freeQuotientRelationMap P (D x) = α x - β x := by
  obtain ⟨E, hE⟩ := exists_biderivation_twisted P α β
    (fun s => Submodule.Quotient.mk (kerLift P ⟨_, h s⟩))
    (fun s => by rw [freeQuotientRelationMap_mk, relationMap_kerLift])
  let D : MvPolynomial S R →ₗ[R] freeQuotient P :=
    { toFun := fun x => TwistedFreeQuotient.equiv P α β (E x)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun a x => by
        rw [RingHom.id_apply, ← TwistedFreeQuotient.equiv_smul_A]
        exact congrArg _ (E.toLinearMap.map_smul a x) }
  have hmul : ∀ x y, D (x * y) = α x • D y + β y • D x := fun x y => by
    change TwistedFreeQuotient.equiv P α β (E.toLinearMap (x * y)) = _
    rw [E.leibniz, map_add, TwistedFreeQuotient.equiv_smul, TwistedFreeQuotient.equiv_op_smul]
    rfl
  refine ⟨D, hmul, fun x => ?_⟩
  induction x using MvPolynomial.induction_on with
  | C a =>
    have h1 : D 1 = 0 := by
      have := hmul 1 1
      rw [mul_one, map_one α, map_one β, one_smul] at this
      exact add_eq_left.1 this.symm
    rw [← mul_one (MvPolynomial.C a), ← MvPolynomial.smul_eq_C_mul, map_smul, h1, smul_zero,
      map_zero, map_smul, map_smul, map_one, map_one, sub_self]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add, map_add]
    abel
  | mul_X p s hp =>
    have hs : D (MvPolynomial.X s) = Submodule.Quotient.mk (kerLift P ⟨_, h s⟩) := by
      change TwistedFreeQuotient.equiv P α β (E (MvPolynomial.X s)) = _
      rw [hE]
      rfl
    rw [hmul, map_add, map_smul, map_smul, hp, hs, freeQuotientRelationMap_mk,
      relationMap_kerLift, map_mul, map_mul, smul_eq_mul, smul_eq_mul]
    ring

end Twisted

end Algebra.Presentation

end
