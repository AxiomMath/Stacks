module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import StacksFrontier.CategoryTheory.Functor.Derived.ValueReflection

/-! # A conservative functor that does not reflect right derivability

`CategoryTheory.Functor.IsRightDerivable.of_comp` reflects right derivability along a functor
that is full and faithful and whose source splits idempotents, and
`CategoryTheory.Functor.isRightDerivable_comp_and_not_isRightDerivable_of_map_eq_zero` says that
conservativity cannot replace full faithfulness there as soon as the functor kills a chain of
morphisms whose composites never vanish. This file exhibits such a functor, so that the
hypotheses of that criterion are seen to be consistent.

The construction is the smallest one. For a ring `R`, the category `SingleObjWithZero R` has two
objects, a zero object and an object `star` whose endomorphism ring is `R`, and a ring
homomorphism `φ : R →+* S` induces a functor `SingleObjWithZero.map φ` between two such
categories. That functor reflects isomorphisms exactly when `φ` reflects units, and it kills a
morphism of infinite multiplicative order as soon as that morphism lies in the kernel of `φ`. For
`R = ℤ⟦X⟧`, `S = ℤ` and `φ` the constant coefficient both happen: a power series is a unit iff
its constant coefficient is one, and `X` is a non-nilpotent element of the kernel. The system
`n ↦ star` with transition morphisms the powers of `X` is then the counterexample.

## Main definitions

* `CategoryTheory.SingleObjWithZero`: for a ring `R`, the category with a zero object and one
  further object whose endomorphism ring is `R`.
* `CategoryTheory.SingleObjWithZero.hom`: the element of `R` underlying a morphism.
* `CategoryTheory.SingleObjWithZero.map`: the functor induced by a ring homomorphism.
* `CategoryTheory.SingleObjWithZero.powSystem`: the `ℕ`-indexed system constant at `star` whose
  transition morphism `n ⟶ m` is `t ^ (m - n)`.

## Main results

* `CategoryTheory.SingleObjWithZero.isIdempotentComplete`: idempotents split in
  `SingleObjWithZero R` as soon as `R` has no zero divisors, the only idempotents of `R` being
  `0` and `1` and the idempotent `0` splitting through the zero object.
* `CategoryTheory.SingleObjWithZero.reflectsIsomorphisms_map`: `SingleObjWithZero.map φ` is
  conservative when `φ` reflects units and the target ring is nontrivial.
* `CategoryTheory.SingleObjWithZero.isRightDerivable_comp_and_not_isRightDerivable` and
  `CategoryTheory.SingleObjWithZero.exists_conservative_not_reflecting_isRightDerivable`: with
  `W = ⊤` on `ℕ`, the right derived functor of `powSystem X ⋙ map constantCoeff` is everywhere
  defined while that of `powSystem X` is defined nowhere — and the source of the functor has a
  zero object and splits idempotents, so neither of those can be what rescues the implication.

## Implementation notes

*What this does and does not settle.* The functor whose reflection Tag 09LK's proof needs is
`DifferentialGradedModule.derivedForget`, and the counterexample here is not that functor: it
shows that the implication cannot be proved from the properties of `derivedForget` that are
recorded in this repository — conservativity (`derivedForget_reflectsIsomorphisms`), zero objects
in source and target, and split idempotents in the source — because those properties hold of
`SingleObjWithZero.map PowerSeries.constantCoeff` as well. Whether the implication is *false* for
`derivedForget` is the question of whether that functor admits a system of the kind the criterion
asks for, i.e. a self-extension of infinite order that it does not see; the implementation notes
of `StacksFrontier/CategoryTheory/Functor/Derived/ValueReflection.lean` describe the expected
example over `ℤ[x]/(x²)` and the Ext computation it needs, which is not formalised here.

*Why not an additive category.* `SingleObjWithZero R` has a zero object but no biproducts, so it
is not additive, let alone triangulated. Additivity is not among the hypotheses of
`CategoryTheory.Functor.IsRightDerivable.of_comp`, so it is not what is being tested; a
counterexample inside a triangulated category would be a stronger statement, and is exactly what
the Ext computation above would provide.

*Why morphisms are read through `hom`.* The morphisms of `SingleObjWithZero R` are a structure
with one field, but `𝟙 a` and `f ≫ g` have the type `a ⟶ b`, on which dot notation for that
field does not fire; every statement below therefore goes through
`CategoryTheory.SingleObjWithZero.hom`, with `hom_ext` for equality of morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-- The objects of `CategoryTheory.SingleObjWithZero R`: a zero object, and an object whose
endomorphism ring is `R`. -/
inductive SingleObjWithZero (R : Type u) : Type
  /-- The zero object. -/
  | zero : SingleObjWithZero R
  /-- The object whose endomorphism ring is `R`. -/
  | star : SingleObjWithZero R

namespace SingleObjWithZero

variable {R : Type u} [Ring R]

/-- A morphism of `CategoryTheory.SingleObjWithZero R`: an element of `R`, required to vanish as
soon as one of the two objects is the zero object. -/
@[ext]
structure Mor (a b : SingleObjWithZero R) where
  /-- The element of `R` underlying the morphism. -/
  val : R
  /-- A morphism into or out of the zero object is zero. -/
  val_eq_zero : a = .zero ∨ b = .zero → val = 0

/-- The identity morphism of `CategoryTheory.SingleObjWithZero R`. -/
def Mor.id' (a : SingleObjWithZero R) : Mor a a where
  val := match a with
    | .zero => 0
    | .star => 1
  val_eq_zero h := by rcases h with h | h <;> subst h <;> rfl

/-- Composition of morphisms of `CategoryTheory.SingleObjWithZero R`, given by multiplication
in `R`. -/
def Mor.comp' {a b c : SingleObjWithZero R} (f : Mor a b) (g : Mor b c) : Mor a c where
  val := f.val * g.val
  val_eq_zero h := by
    rcases h with h | h
    · rw [f.val_eq_zero (Or.inl h), zero_mul]
    · rw [g.val_eq_zero (Or.inr h), mul_zero]

/-- The category with a zero object and one further object whose endomorphism ring is `R`. -/
instance category : Category.{u} (SingleObjWithZero R) where
  Hom a b := Mor a b
  id a := Mor.id' a
  comp f g := Mor.comp' f g
  id_comp {a _} f := Mor.ext <| by
    rcases a with _ | _
    · change (0 : R) * f.val = f.val
      rw [zero_mul, f.val_eq_zero (Or.inl rfl)]
    · change (1 : R) * f.val = f.val
      rw [one_mul]
  comp_id {_ b} f := Mor.ext <| by
    rcases b with _ | _
    · change f.val * (0 : R) = f.val
      rw [mul_zero, f.val_eq_zero (Or.inr rfl)]
    · change f.val * (1 : R) = f.val
      rw [mul_one]
  assoc f g h := Mor.ext <| by
    change f.val * g.val * h.val = f.val * (g.val * h.val)
    rw [mul_assoc]

/-- The element of `R` underlying a morphism of `CategoryTheory.SingleObjWithZero R`. -/
def hom {a b : SingleObjWithZero R} (f : a ⟶ b) : R :=
  Mor.val f

/-- Two morphisms with the same underlying element of `R` are equal. -/
theorem hom_ext {a b : SingleObjWithZero R} {f g : a ⟶ b} (h : hom f = hom g) : f = g :=
  Mor.ext h

/-- A morphism into or out of the zero object has underlying element `0`. -/
theorem hom_eq_zero {a b : SingleObjWithZero R} (f : a ⟶ b) (h : a = .zero ∨ b = .zero) :
    hom f = 0 :=
  Mor.val_eq_zero f h

/-- The element underlying a composite is the product of the underlying elements. -/
@[simp]
theorem hom_comp {a b c : SingleObjWithZero R} (f : a ⟶ b) (g : b ⟶ c) :
    hom (f ≫ g) = hom f * hom g :=
  rfl

/-- The identity of `star` has underlying element `1`. -/
@[simp]
theorem hom_id_star : hom (𝟙 (SingleObjWithZero.star : SingleObjWithZero R)) = 1 :=
  rfl

/-- The identity of the zero object has underlying element `0`. -/
@[simp]
theorem hom_id_zero : hom (𝟙 (SingleObjWithZero.zero : SingleObjWithZero R)) = 0 :=
  rfl

/-- The zero morphisms of `CategoryTheory.SingleObjWithZero R`: the zero element of `R`. -/
instance : HasZeroMorphisms (SingleObjWithZero R) where
  zero _ _ := ⟨⟨0, fun _ => rfl⟩⟩
  comp_zero := by
    intro a b f c
    exact hom_ext (by change hom f * (0 : R) = 0; rw [mul_zero])
  zero_comp := by
    intro a b c f
    exact hom_ext (by change (0 : R) * hom f = 0; rw [zero_mul])

/-- The zero morphism has underlying element `0`. -/
@[simp]
theorem hom_zero {a b : SingleObjWithZero R} : hom (0 : a ⟶ b) = 0 :=
  rfl

/-- The object `CategoryTheory.SingleObjWithZero.zero` is a zero object: every morphism into or
out of it vanishes, hence is the only one. -/
theorem isZero_zeroObj : IsZero (SingleObjWithZero.zero : SingleObjWithZero R) where
  unique_to _ :=
    ⟨{ default := 0, uniq := fun f => hom_ext (by rw [hom_eq_zero f (Or.inl rfl), hom_zero]) }⟩
  unique_from _ :=
    ⟨{ default := 0, uniq := fun f => hom_ext (by rw [hom_eq_zero f (Or.inr rfl), hom_zero]) }⟩

/-- `CategoryTheory.SingleObjWithZero R` has a zero object, namely `zero`. -/
instance : HasZeroObject (SingleObjWithZero R) :=
  ⟨⟨SingleObjWithZero.zero, isZero_zeroObj⟩⟩

/-- **An endomorphism of `star` is invertible exactly when the element of `R` underlying it is a
unit.** -/
theorem isIso_iff_isUnit {f : (SingleObjWithZero.star : SingleObjWithZero R) ⟶ .star} :
    IsIso f ↔ IsUnit (hom f) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨g, h₁, h₂⟩ := h.out
    exact ⟨⟨hom f, hom g, by simpa using congrArg hom h₁, by simpa using congrArg hom h₂⟩, rfl⟩
  · obtain ⟨u, hu⟩ := h
    refine ⟨⟨⟨(↑u⁻¹ : R), fun h => by simp at h⟩, hom_ext ?_, hom_ext ?_⟩⟩
    · change hom f * (↑u⁻¹ : R) = 1
      rw [← hu, Units.mul_inv]
    · change (↑u⁻¹ : R) * hom f = 1
      rw [← hu, Units.inv_mul]

/-- **A morphism into `star` whose underlying element vanishes is not invertible**, the identity
of `star` being nonzero. -/
theorem not_isIso_of_hom_eq_zero [Nontrivial R] {a : SingleObjWithZero R}
    (f : a ⟶ (SingleObjWithZero.star : SingleObjWithZero R)) (hf : hom f = 0) : ¬ IsIso f := by
  intro h
  obtain ⟨g, -, h₂⟩ := h.out
  simpa [hf] using congrArg hom h₂

/-- **A morphism out of `star` whose underlying element vanishes is not invertible**, the
identity of `star` being nonzero. -/
theorem not_isIso_of_hom_eq_zero' [Nontrivial R] {b : SingleObjWithZero R}
    (f : (SingleObjWithZero.star : SingleObjWithZero R) ⟶ b) (hf : hom f = 0) : ¬ IsIso f := by
  intro h
  obtain ⟨g, h₁, -⟩ := h.out
  simpa [hf] using congrArg hom h₁

/-- **Idempotents split in `SingleObjWithZero R`** as soon as `R` has no zero divisors: the only
idempotents of `R` are then `0` and `1`, the first splitting through the zero object and the
second through `star`. -/
instance isIdempotentComplete [NoZeroDivisors R] : IsIdempotentComplete (SingleObjWithZero R) where
  idempotents_split a p hp := by
    have hval : hom p * hom p = hom p := by simpa using congrArg hom hp
    rcases a with _ | _
    · exact ⟨SingleObjWithZero.zero, 𝟙 _, 𝟙 _, Category.id_comp _,
        hom_ext (by rw [hom_comp, hom_id_zero, mul_zero, hom_eq_zero p (Or.inl rfl)])⟩
    · have hfac : hom p * (hom p - 1) = 0 := by rw [mul_sub, mul_one, hval, sub_self]
      rcases mul_eq_zero.1 hfac with h | h
      · refine ⟨SingleObjWithZero.zero, 0, 0, hom_ext ?_, hom_ext ?_⟩
        · simp
        · simp [h]
      · exact ⟨SingleObjWithZero.star, 𝟙 _, 𝟙 _, Category.id_comp _,
          hom_ext (by rw [hom_comp, hom_id_star, mul_one, sub_eq_zero.1 h])⟩

variable {S : Type u} [Ring S]

/-- The object map of `CategoryTheory.SingleObjWithZero.map`: it matches the two objects. -/
def objMap : SingleObjWithZero R → SingleObjWithZero S
  | .zero => .zero
  | .star => .star

omit [Ring R] [Ring S] in
/-- `objMap` sends an object to `zero` exactly when the object is `zero`. -/
@[simp]
theorem objMap_eq_zero_iff {a : SingleObjWithZero R} :
    (objMap a : SingleObjWithZero S) = .zero ↔ a = .zero := by
  cases a <;> simp [objMap]

/-- The functor `SingleObjWithZero R ⥤ SingleObjWithZero S` induced by a ring homomorphism: it
matches the two objects and acts by `φ` on the endomorphisms of `star`. -/
def map (φ : R →+* S) : SingleObjWithZero R ⥤ SingleObjWithZero S where
  obj := objMap
  map f :=
    ⟨φ (hom f), fun h => by
      rcases h with h | h
      · rw [hom_eq_zero f (Or.inl (objMap_eq_zero_iff.1 h)), map_zero]
      · rw [hom_eq_zero f (Or.inr (objMap_eq_zero_iff.1 h)), map_zero]⟩
  map_id a := by
    refine hom_ext ?_
    rcases a with _ | _
    · change φ (hom (𝟙 _)) = hom (𝟙 (SingleObjWithZero.zero : SingleObjWithZero S))
      rw [hom_id_zero, hom_id_zero, map_zero]
    · change φ (hom (𝟙 _)) = hom (𝟙 (SingleObjWithZero.star : SingleObjWithZero S))
      rw [hom_id_star, hom_id_star, map_one]
  map_comp f g := hom_ext (by
    change φ (hom (f ≫ g)) = φ (hom f) * φ (hom g)
    rw [hom_comp, map_mul])

/-- The functor `map φ` acts on underlying elements by `φ`. -/
@[simp]
theorem hom_map_map (φ : R →+* S) {a b : SingleObjWithZero R} (f : a ⟶ b) :
    hom ((map φ).map f) = φ (hom f) :=
  rfl

/-- The functor `map φ` preserves zero morphisms. -/
instance (φ : R →+* S) : (map φ).PreservesZeroMorphisms where
  map_zero _ _ := hom_ext (by rw [hom_map_map, hom_zero, hom_zero, map_zero])

/-- **The functor induced by a ring homomorphism that reflects units is conservative.** An
endomorphism of `star` is invertible exactly when its underlying element is a unit, and no
morphism between the zero object and `star` is invertible as soon as the target ring is
nontrivial, so the hypothesis on `φ` is all that is needed. -/
theorem reflectsIsomorphisms_map [Nontrivial S] (φ : R →+* S)
    (hφ : ∀ x : R, IsUnit (φ x) → IsUnit x) : (map φ).ReflectsIsomorphisms where
  reflects {a b} f hiso := by
    rcases a with _ | _ <;> rcases b with _ | _
    · rw [show f = 𝟙 _ from hom_ext (by rw [hom_eq_zero f (Or.inl rfl), hom_id_zero])]
      infer_instance
    · refine absurd hiso (not_isIso_of_hom_eq_zero ((map φ).map f) ?_)
      change φ (hom f) = 0
      rw [hom_eq_zero f (Or.inl rfl), map_zero]
    · refine absurd hiso (not_isIso_of_hom_eq_zero' ((map φ).map f) ?_)
      change φ (hom f) = 0
      rw [hom_eq_zero f (Or.inr rfl), map_zero]
    · exact isIso_iff_isUnit.2 (hφ (hom f) (isIso_iff_isUnit.1 hiso))

/-- The `ℕ`-indexed system in `SingleObjWithZero R` which is constant at `star` and whose
transition morphism `n ⟶ m` is `t ^ (m - n)`. -/
def powSystem (t : R) : ℕ ⥤ SingleObjWithZero R where
  obj _ := .star
  map {n m} _ := ⟨t ^ (m - n), fun h => by simp at h⟩
  map_id n := hom_ext (by
    change t ^ (n - n) = hom (𝟙 (SingleObjWithZero.star : SingleObjWithZero R))
    rw [hom_id_star, Nat.sub_self, pow_zero])
  map_comp {n m k} f g := hom_ext <| by
    have hnm : n ≤ m := leOfHom f
    have hmk : m ≤ k := leOfHom g
    change t ^ (k - n) = t ^ (m - n) * t ^ (k - m)
    rw [← pow_add]
    congr 1
    omega

/-- The transition morphism `n ⟶ m` of `powSystem t` has underlying element `t ^ (m - n)`. -/
@[simp]
theorem hom_powSystem_map (t : R) {n m : ℕ} (f : n ⟶ m) : hom ((powSystem t).map f) = t ^ (m - n) :=
  rfl

/-- The system `n ↦ star` over `ℤ⟦X⟧` whose transition morphisms are the powers of `X`. -/
abbrev xSystem : ℕ ⥤ SingleObjWithZero (PowerSeries ℤ) :=
  powSystem PowerSeries.X

/-- The functor `SingleObjWithZero ℤ⟦X⟧ ⥤ SingleObjWithZero ℤ` induced by the constant
coefficient. It is conservative, because a power series is a unit exactly when its constant
coefficient is one, and it kills `X`. -/
abbrev constantCoeffFunctor : SingleObjWithZero (PowerSeries ℤ) ⥤ SingleObjWithZero ℤ :=
  map (PowerSeries.constantCoeff (R := ℤ))

/-- **The constant-coefficient functor is conservative**: a power series is a unit exactly when
its constant coefficient is a unit. -/
instance reflectsIsomorphisms_constantCoeffFunctor : constantCoeffFunctor.ReflectsIsomorphisms :=
  reflectsIsomorphisms_map _ fun _ hx => PowerSeries.isUnit_iff_constantCoeff.2 hx

/-- **A conservative functor that does not reflect right derivability.** For `W = ⊤` on `ℕ`, the
right derived functor of `xSystem ⋙ constantCoeffFunctor` is everywhere defined — its values
being zero objects — while that of `xSystem` is defined at no object at all: no transition
morphism `X ^ k` of the system vanishes, while every one of them is killed by the constant
coefficient. -/
theorem isRightDerivable_comp_and_not_isRightDerivable :
    (xSystem ⋙ constantCoeffFunctor).IsRightDerivable ⊤ ∧
      ¬ xSystem.IsRightDerivable (⊤ : MorphismProperty ℕ) :=
  Functor.isRightDerivable_comp_and_not_isRightDerivable_of_map_eq_zero xSystem
    constantCoeffFunctor
    (fun {n m} f h => by
      have hx : (PowerSeries.X : PowerSeries ℤ) ^ (m - n) = 0 := by
        simpa using congrArg hom h
      exact pow_ne_zero (m - n) PowerSeries.X_ne_zero hx)
    fun n => hom_ext (by simp)

/-- **Conservativity, zero objects and split idempotents do not reflect right derivability.**
There are categories `𝒟'` and `𝒟''` with zero objects, `𝒟'` idempotent complete, a functor
`U : 𝒟' ⥤ 𝒟''` preserving zero morphisms and reflecting isomorphisms, and a system `F : ℕ ⥤ 𝒟'`,
such that the right derived functor of `F ⋙ U` is everywhere defined and that of `F` is defined
nowhere, for `W = ⊤`.

So the hypotheses `[G.Full] [G.Faithful]` of `CategoryTheory.Functor.IsRightDerivable.of_comp`
cannot be weakened to conservativity. The properties of
`DifferentialGradedModule.derivedForget` that are available in this repository are exactly the
ones listed here, which is why they do not suffice to carry the essential-constancy witness of
Tag 09LK's proof backwards. -/
theorem exists_conservative_not_reflecting_isRightDerivable :
    ∃ (D' : Type) (_ : Category.{0} D') (D'' : Type) (_ : Category.{0} D'')
      (_ : HasZeroMorphisms D') (_ : HasZeroObject D') (_ : IsIdempotentComplete D')
      (_ : HasZeroMorphisms D'') (_ : HasZeroObject D'') (F : ℕ ⥤ D') (U : D' ⥤ D'')
      (_ : U.PreservesZeroMorphisms) (_ : U.ReflectsIsomorphisms),
      (F ⋙ U).IsRightDerivable ⊤ ∧ ¬ F.IsRightDerivable (⊤ : MorphismProperty ℕ) :=
  ⟨SingleObjWithZero (PowerSeries ℤ), inferInstance, SingleObjWithZero ℤ, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, xSystem,
    constantCoeffFunctor, inferInstance, inferInstance,
    isRightDerivable_comp_and_not_isRightDerivable⟩

end SingleObjWithZero

end CategoryTheory

end
