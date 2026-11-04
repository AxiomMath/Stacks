module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.RingTheory.Ideal.Operations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Powers of a sheaf of ideals and the associated graded algebra

Let `R` be a sheaf of rings on a site and let `𝓘 ⊆ R` be a sheaf submodule of the free rank-one
module, that is, a sheaf of ideals.  Its `n`-th power `𝓘ⁿ` is the sheaf of ideals whose sections
over an object are the sections lying, locally on a covering sieve, in the `n`-th power of the
ideal of sections.  The powers decrease, the zeroth is everything, the first is `𝓘`, and they
multiply: `𝓘ⁿ · 𝓘ᵐ ⊆ 𝓘ⁿ⁺ᵐ`.

Extending the family by the zero sheaf of ideals in negative degrees makes `⨁_n 𝓘ⁿ` a sheaf of
`ℤ`-graded `R`-algebras, concentrated in nonnegative degrees, whose multiplication is the
multiplication of sections of `R`.

## Main definitions

* `SheafOfModules.zeroIdealSheaf`: the zero sheaf of ideals.
* `SheafOfModules.idealSheafPow`: the `n`-th power of a sheaf of ideals, for `n : ℕ`.
* `SheafOfModules.idealSheafZPow`: the same family extended by zero in negative degrees.
* `SheafOfModules.reesGradedAlgebra`: the sheaf of graded algebras `⨁_{n ≥ 0} 𝓘ⁿ`.

## Main results

* `SheafOfModules.mem_idealSheafPow_of_mem_pow`: a section of the `n`-th power of the ideal of
  sections is a section of the `n`-th power of the sheaf of ideals.
* `SheafOfModules.mem_idealSheafPow_zero`, `SheafOfModules.idealSheafPow_one` and
  `SheafOfModules.idealSheafPow_antitone`: the zeroth power is everything, the first power is
  `𝓘` itself, and the powers decrease.
* `SheafOfModules.mul_mem_idealSheafPow_add` and
  `SheafOfModules.mul_mem_idealSheafZPow_add`: products of local sections add degrees.
* `SheafOfModules.idealSheafZPow_of_neg`: in negative degrees the extended family is the zero
  sheaf of ideals, so the graded algebra is concentrated in nonnegative degrees.

## Implementation notes

The power is defined by its membership sieve rather than as an infimum of sheaf submodules.
Membership of `x` in `𝓘ⁿ` over `X` is covering of the sieve of all `f : W ⟶ X` whose restriction
of `x` lies in `𝓘(W)ⁿ`; that this is a sieve is the fact that a restriction map is a ring
homomorphism and therefore carries `𝓘(W)ⁿ` into `𝓘(W')ⁿ`.  Defining the power this way makes all
four properties above local statements about the ideals of sections, which the infimum
description does not: with the infimum, multiplicativity of the family is a statement about an
arbitrary sheaf submodule containing the sectionwise powers and has no sectionwise proof.

Every statement below is phrased with the sections of the structure sheaf in the ring
`ToType (R.obj.obj X)` and with the ideals of sections as `Ideal (ToType (R.obj.obj X))`,
through `SheafOfModules.idealAt`, rather than with the sections of the free rank-one module;
the two agree, but only the first carries the ring structure that the powers and their products
are stated in.  The fields of the sheaf submodules built below are therefore always filled by a
previously stated lemma rather than proved in place.

Commutativity of the sections of `R` is carried as the hypothesis `hcomm` rather than by taking
`R` to be a sheaf of commutative rings, because `SheafOfModules` is indexed by a `RingCat`-valued
sheaf.  It is used exactly twice: for the right-hand scalar law of the multiplication, and for
the degree-zero case of `mul_mem_idealAt_pow_add`, where the second factor is an arbitrary
section of `R` and the first has to be absorbed by a left ideal.  Both are instances of the
observation recorded in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits`: the two scalar laws of
a bilinear map of sheaves of modules already force the commutators of `R` to act trivially, so
the notion is faithful exactly in the commutative case.

The zero sheaf of ideals is constructed explicitly rather than taken to be the bottom element of
the lattice of sheaf submodules: that element is an infimum, and identifying its sections with
`0` is the same separatedness argument with the construction in the way.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory Opposite

universe t v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Sheaves of ideals through their ideals of sections -/

section Generalities

/-- The ideal of sections of a sheaf of ideals over an object of the site. -/
abbrev idealAt (I : (unit R).Submodule) (X : Cᵒᵖ) : Ideal (ToType (R.obj.obj X)) := I.obj X

/-- Two sheaf submodules of the structure sheaf with the same ideals of sections agree. -/
theorem idealSheaf_ext {I K : (unit R).Submodule} (h : ∀ X : Cᵒᵖ, idealAt I X = idealAt K X) :
    I = K :=
  SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext h)

/-- A sheaf submodule of the structure sheaf is contained in another as soon as this holds on
the ideals of sections. -/
theorem idealSheaf_le {I K : (unit R).Submodule} (h : ∀ X : Cᵒᵖ, idealAt I X ≤ idealAt K X) :
    I ≤ K := h

/-- Restriction of sections along a composite is the composite of the restrictions. -/
theorem structureMap_comp_apply {X Y Z : Cᵒᵖ} (g : X ⟶ Y) (h : Y ⟶ Z)
    (x : ToType (R.obj.obj X)) :
    (R.obj.map (g ≫ h)).hom x = (R.obj.map h).hom ((R.obj.map g).hom x) := by
  rw [R.obj.map_comp]
  rfl

/-- Restriction of sections carries the ideal of sections of a sheaf of ideals into the ideal of
sections over the smaller object. -/
theorem map_mem_idealAt {I : (unit R).Submodule} {X Y : Cᵒᵖ} (g : X ⟶ Y)
    {x : ToType (R.obj.obj X)} (hx : x ∈ idealAt I X) :
    (R.obj.map g).hom x ∈ idealAt I Y :=
  I.map_mem g hx

/-- **Membership in a sheaf of ideals is local.** -/
theorem mem_idealAt_of_sieve (I : (unit R).Submodule) {X : Cᵒᵖ} (s : ToType (R.obj.obj X))
    (T : Sieve X.unop) (hT : T ∈ J X.unop)
    (h : ∀ ⦃W : C⦄ (f : W ⟶ X.unop), T f → (R.obj.map f.op).hom s ∈ idealAt I (op W)) :
    s ∈ idealAt I X :=
  I.isSheaf s (J.superset_covering (fun _ f hf => h f hf) hT)

/-- **A section of the structure sheaf which vanishes locally vanishes.** -/
theorem eq_zero_of_locally_zero {X : Cᵒᵖ} (s : ToType (R.obj.obj X))
    (T : Sieve X.unop) (hT : T ∈ J X.unop)
    (h : ∀ ⦃W : C⦄ (f : W ⟶ X.unop), T f → (R.obj.map f.op).hom s = 0) : s = 0 :=
  (unit R).isSheaf.isSeparated X.unop T hT s 0 (fun _ f hf => by
    rw [show ((unit R).val.presheaf.map f.op) s = (R.obj.map f.op).hom s from rfl, h f hf,
      show ((unit R).val.presheaf.map f.op) 0 = (R.obj.map f.op).hom 0 from rfl, map_zero])

/-- A section of the zero ideal of sections is zero. -/
theorem eq_zero_of_mem_bot {X : Cᵒᵖ} {s : ToType (R.obj.obj X)}
    (hs : s ∈ (⊥ : Ideal (ToType (R.obj.obj X)))) : s = 0 :=
  Submodule.mem_bot _ |>.mp hs

/-- The zero ideal of sections is stable under restriction. -/
theorem map_mem_bot {X Y : Cᵒᵖ} (g : X ⟶ Y) {x : ToType (R.obj.obj X)}
    (hx : x ∈ (⊥ : Ideal (ToType (R.obj.obj X)))) :
    (R.obj.map g).hom x ∈ (⊥ : Ideal (ToType (R.obj.obj Y))) := by
  rw [eq_zero_of_mem_bot hx, map_zero]
  exact zero_mem _

/-- Membership in the zero ideal of sections is local. -/
theorem mem_bot_of_sieve {X : Cᵒᵖ} (s : ToType (R.obj.obj X)) (T : Sieve X.unop)
    (hT : T ∈ J X.unop)
    (h : ∀ ⦃W : C⦄ (f : W ⟶ X.unop), T f →
      (R.obj.map f.op).hom s ∈ (⊥ : Ideal (ToType (R.obj.obj (op W))))) :
    s ∈ (⊥ : Ideal (ToType (R.obj.obj X))) :=
  (Submodule.mem_bot _).2 (eq_zero_of_locally_zero s T hT fun _ f hf => eq_zero_of_mem_bot (h f hf))

/-- **The zero sheaf of ideals.**  Its ideal of sections over every object is zero. -/
def zeroIdealSheaf : (unit R).Submodule where
  obj X := (⊥ : Ideal (ToType (R.obj.obj X)))
  map {_ _} g {_} hx := map_mem_bot g hx
  isSheaf {_} s hs := mem_bot_of_sieve s _ hs (fun _ _f hf => hf)

/-- The ideal of sections of the zero sheaf of ideals over every object is zero. -/
theorem idealAt_zeroIdealSheaf (X : Cᵒᵖ) :
    idealAt (zeroIdealSheaf (R := R)) X = ⊥ :=
  rfl

end Generalities

/-! ### Powers of the ideals of sections -/

section Sections

variable {I : (unit R).Submodule}

/-- Every section lies in the zeroth power of the ideal of sections. -/
private theorem mem_idealAt_pow_zero {I : (unit R).Submodule} {X : Cᵒᵖ}
    (x : ToType (R.obj.obj X)) : x ∈ idealAt I X ^ 0 := by
  rw [Submodule.pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

/-- **Restriction of sections respects the powers of the ideal of sections**: it carries
`𝓘(X)ⁿ` into `𝓘(Y)ⁿ`. -/
theorem map_mem_idealAt_pow {X Y : Cᵒᵖ} (g : X ⟶ Y) (n : ℕ) {x : ToType (R.obj.obj X)}
    (hx : x ∈ idealAt I X ^ n) : (R.obj.map g).hom x ∈ idealAt I Y ^ n := by
  induction n generalizing x with
  | zero => exact mem_idealAt_pow_zero _
  | succ n ih =>
    rw [Submodule.pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    · rw [map_mul, Submodule.pow_succ]
      exact Submodule.mul_mem_mul (ih ha) (map_mem_idealAt g hb)
    · rw [map_add]
      exact add_mem hy hz

/-- **The product of a section of `𝓘ⁿ` and a section of `𝓘ᵐ` lies in `𝓘ⁿ⁺ᵐ`**, at the level of
the ideals of sections, provided the sections of `R` commute. -/
theorem mul_mem_idealAt_pow_add
    (hcomm : ∀ (X : Cᵒᵖ) (a b : ToType (R.obj.obj X)), a * b = b * a)
    {X : Cᵒᵖ} (n m : ℕ) {x y : ToType (R.obj.obj X)}
    (hx : x ∈ idealAt I X ^ n) (hy : y ∈ idealAt I X ^ m) :
    x * y ∈ idealAt I X ^ (n + m) := by
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · rw [Nat.add_zero, hcomm X x y, ← smul_eq_mul]
    exact Submodule.smul_mem _ y hx
  · rw [Submodule.pow_add _ (Nat.pos_iff_ne_zero.mp hm)]
    exact Submodule.mul_mem_mul hx hy

end Sections

/-! ### Powers of a sheaf of ideals -/

section Powers

variable (I : (unit R).Submodule)

/-- The sieve of objects over which a local section of the structure sheaf restricts into the
`n`-th power of the ideal of sections of a sheaf of ideals. -/
def powSieve (n : ℕ) {X : Cᵒᵖ} (x : ToType (R.obj.obj X)) : Sieve X.unop where
  arrows W f := (R.obj.map f.op).hom x ∈ idealAt I (op W) ^ n
  downward_closed := by
    intro W W' f hf g
    have h : ((g ≫ f).op : X ⟶ op W') = f.op ≫ g.op := rfl
    change (R.obj.map ((g ≫ f).op)).hom x ∈ _
    rw [h, structureMap_comp_apply]
    exact map_mem_idealAt_pow g.op n hf

/-- An arrow `f : W ⟶ X` lies in the membership sieve of `x` for the `n`-th power exactly when the
restriction of `x` along `f` lies in `𝓘(W)ⁿ`. -/
theorem mem_powSieve_iff (n : ℕ) {X : Cᵒᵖ} (x : ToType (R.obj.obj X)) {W : C} (f : W ⟶ X.unop) :
    powSieve I n x f ↔ (R.obj.map f.op).hom x ∈ idealAt I (op W) ^ n :=
  Iff.rfl

/-- Restricting a section pulls back its membership sieve. -/
theorem powSieve_map (n : ℕ) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : ToType (R.obj.obj X)) :
    powSieve I n ((R.obj.map g).hom x) = (powSieve I n x).pullback g.unop := by
  refine Sieve.ext (fun W f => ?_)
  have h : ((f ≫ g.unop).op : X ⟶ op W) = g ≫ f.op := rfl
  show (R.obj.map f.op).hom ((R.obj.map g).hom x) ∈ _ ↔
    (R.obj.map ((f ≫ g.unop).op)).hom x ∈ _
  rw [h, structureMap_comp_apply]

/-- The membership condition of the `n`-th power is stable under addition. -/
theorem powSieve_add_mem (n : ℕ) {X : Cᵒᵖ} {x y : ToType (R.obj.obj X)}
    (hx : powSieve I n x ∈ J X.unop) (hy : powSieve I n y ∈ J X.unop) :
    powSieve I n (x + y) ∈ J X.unop :=
  J.superset_covering (fun W f hf => by
    show (R.obj.map f.op).hom (x + y) ∈ _
    rw [map_add]
    exact add_mem hf.1 hf.2) (J.intersection_covering hx hy)

/-- The zero section satisfies the membership condition of the `n`-th power. -/
theorem powSieve_zero_mem (n : ℕ) (X : Cᵒᵖ) :
    powSieve I n (0 : ToType (R.obj.obj X)) ∈ J X.unop :=
  J.superset_covering (fun W f _ => by
    show (R.obj.map f.op).hom 0 ∈ _
    rw [map_zero]
    exact zero_mem _) (J.top_mem X.unop)

/-- The membership condition of the `n`-th power is stable under multiplication by a section of
the structure sheaf. -/
theorem powSieve_mul_mem (n : ℕ) {X : Cᵒᵖ} (r : ToType (R.obj.obj X))
    {x : ToType (R.obj.obj X)} (hx : powSieve I n x ∈ J X.unop) :
    powSieve I n (r * x) ∈ J X.unop :=
  J.superset_covering (fun W f hf => by
    show (R.obj.map f.op).hom (r * x) ∈ _
    rw [map_mul, ← smul_eq_mul]
    exact Submodule.smul_mem _ _ hf) hx

/-- The membership condition of the `n`-th power is stable under restriction. -/
theorem powSieve_map_mem (n : ℕ) {X Y : Cᵒᵖ} (g : X ⟶ Y) {x : ToType (R.obj.obj X)}
    (hx : powSieve I n x ∈ J X.unop) :
    powSieve I n ((R.obj.map g).hom x) ∈ J Y.unop := by
  rw [powSieve_map]
  exact J.pullback_stable g.unop hx

/-- The membership condition of the `n`-th power is local. -/
theorem powSieve_local (n : ℕ) {X : Cᵒᵖ} (s : ToType (R.obj.obj X)) (T : Sieve X.unop)
    (hT : T ∈ J X.unop)
    (h : ∀ ⦃W : C⦄ (f : W ⟶ X.unop), T f → powSieve I n ((R.obj.map f.op).hom s) ∈ J W) :
    powSieve I n s ∈ J X.unop :=
  J.transitive hT (powSieve I n s) (fun {W} {f} hf => by
    have h' := h f hf
    rwa [powSieve_map] at h')

/-- **The `n`-th power of a sheaf of ideals.**  Its sections over an object are the sections of
the structure sheaf which, locally on a covering sieve, lie in the `n`-th power of the ideal of
sections. -/
def idealSheafPow (n : ℕ) : (unit R).Submodule where
  obj X :=
    { carrier := {x | powSieve I n x ∈ J X.unop}
      add_mem' := fun {_ _} hx hy => powSieve_add_mem I n hx hy
      zero_mem' := powSieve_zero_mem I n X
      smul_mem' := fun r {_} hx => powSieve_mul_mem I n r hx }
  map {_ _} g {_} hx := powSieve_map_mem I n g hx
  isSheaf {_} s hs := powSieve_local I n s _ hs (fun _ _f hf => hf)

/-- A section lies in the `n`-th power of a sheaf of ideals exactly when its membership sieve for
the `n`-th power is covering. -/
theorem mem_idealSheafPow_iff (n : ℕ) {X : Cᵒᵖ} (x : ToType (R.obj.obj X)) :
    x ∈ idealAt (idealSheafPow I n) X ↔ powSieve I n x ∈ J X.unop :=
  Iff.rfl

/-- A section lying in the `n`-th power of the ideal of sections lies in the `n`-th power of the
sheaf of ideals. -/
theorem mem_idealSheafPow_of_mem_pow (n : ℕ) {X : Cᵒᵖ} {x : ToType (R.obj.obj X)}
    (hx : x ∈ idealAt I X ^ n) : x ∈ idealAt (idealSheafPow I n) X :=
  J.superset_covering (fun _ f _ => map_mem_idealAt_pow f.op n hx) (J.top_mem X.unop)

/-- **The zeroth power of a sheaf of ideals is the whole structure sheaf.** -/
theorem mem_idealSheafPow_zero {X : Cᵒᵖ} (x : ToType (R.obj.obj X)) :
    x ∈ idealAt (idealSheafPow I 0) X := by
  exact mem_idealSheafPow_of_mem_pow I 0 (mem_idealAt_pow_zero x)

/-- **The powers of a sheaf of ideals decrease with the exponent.** -/
theorem idealSheafPow_antitone : Antitone (idealSheafPow I) :=
  fun _ _ h => idealSheaf_le (fun _ _ hx =>
    J.superset_covering (fun _ _ hf => Ideal.pow_le_pow_right h hf) hx)

/-- **The first power of a sheaf of ideals is the sheaf of ideals itself.** -/
theorem idealSheafPow_one : idealSheafPow I 1 = I := by
  refine idealSheaf_ext (fun X => le_antisymm (fun x hx => ?_) (fun x hx => ?_))
  · refine mem_idealAt_of_sieve I x _ hx (fun W f hf => ?_)
    rwa [← Submodule.pow_one (idealAt I (op W))]
  · refine mem_idealSheafPow_of_mem_pow I 1 ?_
    rwa [Submodule.pow_one]

/-- **The product of a section of `𝓘ⁿ` and a section of `𝓘ᵐ` is a section of `𝓘ⁿ⁺ᵐ`.** -/
theorem mul_mem_idealSheafPow_add
    (hcomm : ∀ (X : Cᵒᵖ) (a b : ToType (R.obj.obj X)), a * b = b * a)
    (n m : ℕ) {X : Cᵒᵖ} {x y : ToType (R.obj.obj X)}
    (hx : x ∈ idealAt (idealSheafPow I n) X) (hy : y ∈ idealAt (idealSheafPow I m) X) :
    x * y ∈ idealAt (idealSheafPow I (n + m)) X :=
  J.superset_covering (fun W f hf => by
      show (R.obj.map f.op).hom (x * y) ∈ _
      rw [map_mul]
      exact mul_mem_idealAt_pow_add hcomm n m hf.1 hf.2)
    (J.intersection_covering hx hy)

end Powers

/-! ### The family of powers indexed by the integers -/

section ZPow

variable (I : (unit R).Submodule)

/-- The powers of a sheaf of ideals, indexed by the integers: the `n`-th power in degree
`n ≥ 0`, and the zero sheaf of ideals in negative degrees. -/
def idealSheafZPow (n : ℤ) : (unit R).Submodule :=
  if 0 ≤ n then idealSheafPow I n.toNat else zeroIdealSheaf

/-- In a nonnegative degree `n` the integer-indexed family of powers is the power of exponent
`n.toNat`. -/
theorem idealSheafZPow_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    idealSheafZPow I n = idealSheafPow I n.toNat :=
  ite_eq_left_of_eq_true _ _ (eq_true hn)

/-- **In negative degrees the integer-indexed family of powers is the zero sheaf of ideals.** -/
theorem idealSheafZPow_of_neg {n : ℤ} (hn : n < 0) : idealSheafZPow I n = zeroIdealSheaf :=
  ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr hn))

/-- At a natural number `n` the integer-indexed family of powers is the `n`-th power. -/
theorem idealSheafZPow_natCast (n : ℕ) : idealSheafZPow I (n : ℤ) = idealSheafPow I n := by
  rw [idealSheafZPow_of_nonneg I (Int.natCast_nonneg n), Int.toNat_natCast]

/-- In degree one the integer-indexed family of powers is the sheaf of ideals itself. -/
theorem idealSheafZPow_one : idealSheafZPow I 1 = I := by
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, idealSheafZPow_natCast, idealSheafPow_one]

/-- A section of a negative degree of the family is zero. -/
theorem eq_zero_of_mem_idealSheafZPow_neg {n : ℤ} (hn : n < 0) {X : Cᵒᵖ}
    {x : ToType (R.obj.obj X)} (hx : x ∈ idealAt (idealSheafZPow I n) X) : x = 0 := by
  rw [idealSheafZPow_of_neg I hn, idealAt_zeroIdealSheaf] at hx
  exact eq_zero_of_mem_bot hx

/-- The section `1` of the structure sheaf lies in the degree-zero part. -/
theorem one_mem_idealSheafZPow_zero (X : Cᵒᵖ) :
    (1 : ToType (R.obj.obj X)) ∈ idealAt (idealSheafZPow I 0) X := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, idealSheafZPow_natCast]
  exact mem_idealSheafPow_zero I 1

/-- **The product of a section of `𝓘ⁱ` and a section of `𝓘ʲ` is a section of `𝓘ⁱ⁺ʲ`**, for
integer exponents, provided the sections of `R` commute. -/
theorem mul_mem_idealSheafZPow_add
    (hcomm : ∀ (X : Cᵒᵖ) (a b : ToType (R.obj.obj X)), a * b = b * a)
    (i j : ℤ) {X : Cᵒᵖ} {x y : ToType (R.obj.obj X)}
    (hx : x ∈ idealAt (idealSheafZPow I i) X) (hy : y ∈ idealAt (idealSheafZPow I j) X) :
    x * y ∈ idealAt (idealSheafZPow I (i + j)) X := by
  rcases lt_or_ge i 0 with hi | hi
  · simp [eq_zero_of_mem_idealSheafZPow_neg I hi hx]
  rcases lt_or_ge j 0 with hj | hj
  · simp [eq_zero_of_mem_idealSheafZPow_neg I hj hy]
  rw [idealSheafZPow_of_nonneg I hi] at hx
  rw [idealSheafZPow_of_nonneg I hj] at hy
  rw [idealSheafZPow_of_nonneg I (add_nonneg hi hj), Int.toNat_add hi hj]
  exact mul_mem_idealSheafPow_add I hcomm _ _ hx hy

end ZPow

/-! ### The graded algebra of the powers of a sheaf of ideals -/

section Rees

variable (I : (unit R).Submodule)
  (hcomm : ∀ (X : Cᵒᵖ) (a b : ToType (R.obj.obj X)), a * b = b * a)

/-- The degree-`n` homogeneous piece of the graded algebra of the powers of a sheaf of
ideals. -/
noncomputable abbrev reesPiece (n : ℤ) : SheafOfModules.{t} R :=
  (idealSheafZPow I n).toSheafOfModules

/-- The underlying section of the structure sheaf of a homogeneous local section. -/
abbrev reesVal {n : ℤ} {X : Cᵒᵖ} (x : (reesPiece I n).val.obj X) : ToType (R.obj.obj X) := x.1

/-- A homogeneous local section of degree `n` from a section of `𝓘ⁿ`. -/
def reesMk {n : ℤ} {X : Cᵒᵖ} (a : ToType (R.obj.obj X))
    (ha : a ∈ idealAt (idealSheafZPow I n) X) : (reesPiece I n).val.obj X :=
  ⟨a, ha⟩

/-- The underlying section of a homogeneous local section of degree `n` lies in `𝓘ⁿ`. -/
theorem reesVal_mem {n : ℤ} {X : Cᵒᵖ} (x : (reesPiece I n).val.obj X) :
    reesVal I x ∈ idealAt (idealSheafZPow I n) X :=
  x.2

/-- A homogeneous local section is determined by its underlying section of the structure
sheaf. -/
theorem reesPiece_ext {n : ℤ} {X : Cᵒᵖ} {x y : (reesPiece I n).val.obj X}
    (h : reesVal I x = reesVal I y) : x = y :=
  Subtype.ext h

/-- The underlying section of `reesMk I a ha` is `a`. -/
@[simp]
theorem reesVal_reesMk {n : ℤ} {X : Cᵒᵖ} (a : ToType (R.obj.obj X))
    (ha : a ∈ idealAt (idealSheafZPow I n) X) : reesVal I (reesMk I (n := n) a ha) = a :=
  rfl

/-- The underlying section of a sum of homogeneous local sections is the sum of their underlying
sections. -/
@[simp]
theorem reesVal_add {n : ℤ} {X : Cᵒᵖ} (x y : (reesPiece I n).val.obj X) :
    reesVal I (x + y) = reesVal I x + reesVal I y :=
  rfl

/-- Scalar multiplication of a homogeneous local section by `r` multiplies its underlying section
by `r` on the left. -/
@[simp]
theorem reesVal_smul {n : ℤ} {X : Cᵒᵖ} (r : ToType (R.obj.obj X))
    (x : (reesPiece I n).val.obj X) : reesVal I (r • x) = r * reesVal I x :=
  rfl

/-- Restricting a homogeneous local section restricts its underlying section. -/
@[simp]
theorem reesVal_map {n : ℤ} {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : (reesPiece I n).val.obj X) :
    reesVal I ((reesPiece I n).val.map g x) = (R.obj.map g).hom (reesVal I x) :=
  rfl

/-- Multiplication of homogeneous local sections, in the second variable. -/
noncomputable def reesMulApp (i j : ℤ) (X : Cᵒᵖ) (x : (reesPiece I i).val.obj X) :
    (reesPiece I j).val.obj X →+ (reesPiece I (i + j)).val.obj X :=
  AddMonoidHom.mk'
    (fun y => reesMk I (reesVal I x * reesVal I y)
      (mul_mem_idealSheafZPow_add I hcomm i j (reesVal_mem I x) (reesVal_mem I y)))
    (fun y z => reesPiece_ext I (mul_add (reesVal I x) (reesVal I y) (reesVal I z)))

/-- The underlying section of `reesMulApp I hcomm i j X x y` is the product of the underlying
sections of `x` and `y`. -/
@[simp]
theorem reesVal_reesMulApp (i j : ℤ) (X : Cᵒᵖ) (x : (reesPiece I i).val.obj X)
    (y : (reesPiece I j).val.obj X) :
    reesVal I (reesMulApp I hcomm i j X x y) = reesVal I x * reesVal I y :=
  rfl

/-- **Multiplication on the graded algebra of the powers of a sheaf of ideals**: the
multiplication of sections of the structure sheaf, which adds the degrees. -/
noncomputable def reesMul (i j : ℤ) :
    BilinearMap (reesPiece I i) (reesPiece I j) (reesPiece I (i + j)) where
  app X := AddMonoidHom.mk' (reesMulApp I hcomm i j X)
    (fun x y => by
      ext z
      exact reesPiece_ext I (add_mul (reesVal I x) (reesVal I y) (reesVal I z)))
  map_smul_left X r x y :=
    reesPiece_ext I (mul_assoc r (reesVal I x) (reesVal I y))
  map_smul_right X r x y :=
    reesPiece_ext I (show reesVal I x * (r * reesVal I y) = r * (reesVal I x * reesVal I y) by
      rw [← mul_assoc, hcomm X (reesVal I x) r, mul_assoc])
  naturality {_X _Y} g x y :=
    reesPiece_ext I (map_mul (R.obj.map g).hom (reesVal I x) (reesVal I y))

/-- The underlying section of a product in the graded algebra of the powers is the product of the
underlying sections of the factors. -/
@[simp]
theorem reesVal_reesMul_app (i j : ℤ) (X : Cᵒᵖ) (x : (reesPiece I i).val.obj X)
    (y : (reesPiece I j).val.obj X) :
    reesVal I ((reesMul I hcomm i j).app X x y) = reesVal I x * reesVal I y :=
  rfl

/-- The degree-zero unit of the graded algebra of the powers of a sheaf of ideals: the section
`1` of the structure sheaf. -/
noncomputable def reesOne : (reesPiece I 0).sections :=
  PresheafOfModules.sectionsMk (fun X => reesMk I (n := 0) 1 (one_mem_idealSheafZPow_zero I X))
    (fun {_X _Y} g => reesPiece_ext I (map_one (R.obj.map g).hom))

/-- The underlying section of the degree-zero unit over every object is `1`. -/
@[simp]
theorem reesVal_reesOne (X : Cᵒᵖ) : reesVal I ((reesOne I).eval X) = 1 := rfl

/-- Two homogeneous local sections with the same underlying section of the structure sheaf and
propositionally equal degrees are heterogeneously equal. -/
theorem reesPiece_heq {i j : ℤ} (hij : i = j) {X : Cᵒᵖ} (x : (reesPiece I i).val.obj X)
    (y : (reesPiece I j).val.obj X) (hxy : reesVal I x = reesVal I y) : HEq x y :=
  (Subtype.heq_iff_coe_eq (fun _ => by rw [hij])).2 hxy

/-- **The sheaf of graded algebras `⨁_{n ≥ 0} 𝓘ⁿ` of a sheaf of ideals.**  Its degree-`n`
homogeneous piece is the `n`-th power of `𝓘` for `n ≥ 0` and the zero sheaf of ideals otherwise,
and its multiplication is the multiplication of sections of the structure sheaf. -/
@[stacks 0FQW "the graded algebra of the powers of a sheaf of ideals", sga "2 XII 4.2" "partial"]
noncomputable def reesGradedAlgebra : GradedAlgebra.{t, t} R where
  piece n := reesPiece I n
  mul i j := reesMul I hcomm i j
  one := reesOne I
  mul_assoc i j k _X x y z :=
    reesPiece_heq I (add_assoc i j k) _ _
      (mul_assoc (reesVal I x) (reesVal I y) (reesVal I z))
  one_mul i _X x := reesPiece_heq I (zero_add i) _ _ (one_mul (reesVal I x))
  mul_one i _X x := reesPiece_heq I (add_zero i) _ _ (mul_one (reesVal I x))

/-- The degree-`n` homogeneous piece of `reesGradedAlgebra I hcomm` is the degree-`n` member of
the integer-indexed family of powers. -/
theorem reesGradedAlgebra_piece (n : ℤ) :
    (reesGradedAlgebra I hcomm).piece n = (idealSheafZPow I n).toSheafOfModules :=
  rfl

end Rees

end SheafOfModules

end
