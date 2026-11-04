module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.GroupWithZero.Units.Basic
public import StacksCore.GroupTheory.GroupAction.Defs

/-! # Quotient by square of units

Given a monoid `M` we make a new type which consists of elements of `M` but `x` is identified with
`u ^ 2 * x` for any unit `u : Mˣ`.

-/

@[expose] public section

/-- The quotient map `M → MulAction.orbitRel.Quotient G M` packaged as a monoid homomorphism
when `G` acts on the commutative monoid `M` by monoid automorphisms. -/
def MulAction.orbitRel.mkMonoidHom
    (G M : Type*) [Group G] [CommMonoid M] [MulAction G M] [IsScalarTower G M M] :
    M →* MulAction.orbitRel.Quotient G M where
  toFun := Quotient.mk''
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The quotient of a commutative monoid `M` by the action of the subgroup of squares of `Mˣ`,
i.e. `M` modulo the equivalence relation `x ∼ u ^ 2 * x` for `u : Mˣ`. -/
def QuotSq (M : Type*) [CommMonoid M] : Type _ :=
  MulAction.orbitRel.Quotient (Subgroup.square Mˣ) M
deriving CommMonoid

namespace QuotSq
variable {M : Type*}

section comm_monoid
variable [CommMonoid M]

variable (M) in
/-- The canonical monoid homomorphism `M → QuotSq M`. -/
def mk : M →* QuotSq M := MulAction.orbitRel.mkMonoidHom _ _

/-- The map `mk M : M → QuotSq M` is surjective. -/
theorem mk_surjective : Function.Surjective (mk M) := Quotient.mk_surjective

/-- If `M` is a subsingleton, so is `QuotSq M`. -/
instance [Subsingleton M] : Subsingleton (QuotSq M) := mk_surjective.subsingleton

/-- Induction principle for `QuotSq M`: a property holds on every element of the quotient as
soon as it holds on every class `mk M x`. -/
@[elab_as_elim] theorem mk_induction
    {C : QuotSq M → Prop} (h : ∀ x, C (mk M x)) (x : QuotSq M) : C x :=
  Quotient.inductionOn x fun _ ↦ h _

/-- Two elements of `M` have the same class in `QuotSq M` iff they differ by the action of
`u ^ 2` for some unit `u : Mˣ`. -/
theorem mk_eq_iff (x y : M) : mk M x = mk M y ↔ ∃ u : Mˣ, u ^ 2 • x = y :=
  (eq_comm.trans Quotient.eq).trans <| by
    simp [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, IsSquare, sq]

/-- Variant of `mk_eq_iff` with the unit action expanded to multiplication. -/
theorem mk_eq_iff' (x y : M) : mk M x = mk M y ↔ ∃ u : Mˣ, u ^ 2 * x = y := mk_eq_iff ..

/-- Variant of `mk_eq_iff` with the equality flipped. -/
theorem mk_eq_iff'' (x y : M) : mk M x = mk M y ↔ ∃ u : Mˣ, x = u ^ 2 • y := by
  simp_rw [eq_comm (a := mk M x), mk_eq_iff, eq_comm]

/-- Variant of `mk_eq_iff''` with the unit action expanded to multiplication. -/
theorem mk_eq_iff''' (x y : M) : mk M x = mk M y ↔ ∃ u : Mˣ, x = u ^ 2 * y := mk_eq_iff'' ..

/-- Like `mk_eq_iff'`, but stated for an element `u : M` together with `IsUnit u`. -/
theorem mk_eq_iff_isUnit (x y : M) : mk M x = mk M y ↔ ∃ u : M, IsUnit u ∧ u ^ 2 * x = y :=
  (mk_eq_iff' ..).trans ⟨fun ⟨u, hu⟩ ↦ ⟨u, by simpa⟩, fun ⟨u, hu1, hu2⟩ ↦ ⟨hu1.unit, hu2⟩⟩

/-- Like `mk_eq_iff'''`, but stated for an element `u : M` together with `IsUnit u`. -/
theorem mk_eq_iff_isUnit' (x y : M) : mk M x = mk M y ↔ ∃ u : M, IsUnit u ∧ x = u ^ 2 * y := by
  simp_rw [eq_comm (a := mk M x), mk_eq_iff_isUnit, eq_comm]

/-- If `mk M x = mk M y` then `y = u ^ 2 * x` for some unit `u : Mˣ`. -/
theorem exact {x y : M} (h : mk M x = mk M y) : ∃ u : Mˣ, u ^ 2 * x = y := (mk_eq_iff' ..).mp h

/-- If `mk M x = mk M y` then `x = u ^ 2 * y` for some unit `u : Mˣ`. -/
theorem exact' {x y : M} (h : mk M x = mk M y) : ∃ u : Mˣ, x = u ^ 2 * y := (mk_eq_iff''' ..).mp h

/-- The square of the class of any unit `u : Mˣ` is `1` in `QuotSq M`. -/
@[simp] theorem mk_unit_sq (u : Mˣ) : mk M u ^ 2 = 1 :=
  .symm <| (mk_eq_iff' ..).mpr ⟨u, by simp [sq]⟩

/-- A chosen lift `QuotSq M → M`, sending `1` to `1` and otherwise picking
`Quotient.out`. -/
noncomputable def out (x : QuotSq M) : M :=
  open scoped Classical in
  if x = 1 then 1 else Quotient.out x

/-- The lift of `1 : QuotSq M` is `1 : M`. -/
@[simp] theorem out_one : out (1 : QuotSq M) = 1 := ite_eq_left rfl

/-- The lift `out` is a section of `mk`: `mk M (out x) = x`. -/
@[simp] theorem mk_out (x : QuotSq M) : mk M (out x) = x := by
  unfold out
  split_ifs
  · simp [*]
  · exact Quotient.out_eq x

/-- For any `x : M`, the lift of `mk M x` differs from `x` by `u ^ 2` for some unit `u : Mˣ`. -/
theorem exists_out_mk_eq (x : M) : ∃ u : Mˣ, (mk M x).out = u ^ 2 * x := exact' <| by simp

end comm_monoid

section comm_monoid_with_zero
variable [CommMonoidWithZero M]

/-- `QuotSq M` inherits a `CommMonoidWithZero` structure from `M`, with zero given by the
class of `0 : M`. -/
instance : CommMonoidWithZero (QuotSq M) where
  zero := mk M 0
  zero_mul x := x.mk_induction fun x ↦ show mk M (0 * x) = mk M 0 by simp
  mul_zero x := x.mk_induction fun x ↦ show mk M (x * 0) = mk M 0 by simp

variable (M) in
/-- The canonical monoid-with-zero homomorphism `M → QuotSq M`, refining `mk` when `M` is a
`CommMonoidWithZero`. -/
def mk₀ : M →*₀ QuotSq M where
  __ := mk M
  map_zero' := rfl

/-- The underlying function of `mk₀ M` agrees with `mk M`. -/
@[simp] theorem coe_mk₀ : ⇑(mk₀ M) = mk M := rfl

/-- The class of `0 : M` is the zero element of `QuotSq M`. -/
theorem mk_zero : mk M 0 = 0 := rfl

/-- The class of `x : M` in `QuotSq M` is zero iff `x = 0`. -/
@[simp] theorem mk_eq_zero (x : M) : mk M x = 0 ↔ x = 0 := by
  simp [show 0 = mk M 0 from rfl, mk_eq_iff''']

/-- The lift of `0 : QuotSq M` is `0 : M`. -/
@[simp] theorem out_zero : out (0 : QuotSq M) = 0 := (mk_eq_zero _).mp <| by simp

end comm_monoid_with_zero

section comm_group_with_zero
variable {G : Type*} [CommGroupWithZero G]

/-- In a commutative group with zero `G`, the class `mk G x` in `QuotSq G` is neither `0`
nor `1` iff `x` is not a square. -/
theorem mk_ne_zero_and_one_iff_not_isSquare (x : G) :
    QuotSq.mk G x ≠ 0 ∧ QuotSq.mk G x ≠ 1 ↔ ¬IsSquare x := by
  rw [ne_eq, QuotSq.mk_eq_zero, ← (QuotSq.mk G).map_one, ne_eq, QuotSq.mk_eq_iff_isUnit']
  simp_rw [isUnit_iff_ne_zero, mul_one, IsSquare, sq]
  refine ⟨fun h ⟨r, hr⟩ ↦ ?_, fun h ↦ ⟨mt (fun hx0 ↦ ⟨0, by simp [hx0]⟩) h, by grind⟩⟩
  obtain rfl | hx0 := eq_or_ne x 0
  · grind
  exact h.2 ⟨r, by rwa [← and_self (r ≠ 0), ← mul_ne_zero_iff, ← hr], hr⟩

end comm_group_with_zero

end QuotSq
