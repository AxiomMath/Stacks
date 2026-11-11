module

public import Mathlib.CategoryTheory.Countable
public import Mathlib.CategoryTheory.Equivalence

/-!
# Codes for countable categories

A countable category is equivalent to one whose objects form a subset of `ℕ` and whose morphism
sets are subsets of `ℕ`. Such a category is determined by a value of the type
`CategoryTheory.CountableCategoryCode`, which lives in `Type`. So the countable categories form a
set up to equivalence: this is the remark "there is a set `CountCat` of countable categories such
that any countable category is isomorphic to an element of `CountCat`" in the proof of
Stacks 000J.

## Main definitions

* `CategoryTheory.CountableCategoryCode`: a category structure on a subset of `ℕ` whose morphism
  sets are subsets of `ℕ`.
* `CategoryTheory.CountableCategoryCode.Obj`: the small category of a code.
* `CategoryTheory.CountableCategoryCode.ofCountable`: the code of a countable category.
* `CategoryTheory.CountableCategoryCode.equivOfCountable`: a countable category is equivalent to the
  category of its code.
-/

@[expose] public section

universe w v

namespace CategoryTheory

/-- A category whose set of objects is a subset of `ℕ` and whose morphism sets are subsets
of `ℕ`. -/
structure CountableCategoryCode : Type where
  /-- The objects. -/
  obj : Set ℕ
  /-- The morphisms between two objects. -/
  hom : obj → obj → Set ℕ
  /-- The identity morphisms. -/
  id : ∀ a, ↥(hom a a)
  /-- The composition. -/
  comp : ∀ {a b c}, ↥(hom a b) → ↥(hom b c) → ↥(hom a c)
  id_comp : ∀ {a b} (f : ↥(hom a b)), comp (id a) f = f
  comp_id : ∀ {a b} (f : ↥(hom a b)), comp f (id b) = f
  assoc : ∀ {a b c d} (f : ↥(hom a b)) (g : ↥(hom b c)) (k : ↥(hom c d)),
    comp (comp f g) k = comp f (comp g k)

namespace CountableCategoryCode

/-- The objects of the category of a code. -/
def Obj (c : CountableCategoryCode) : Type := c.obj

instance (c : CountableCategoryCode) : SmallCategory c.Obj where
  Hom a b := c.hom a b
  id a := c.id a
  comp f g := c.comp f g
  id_comp f := c.id_comp f
  comp_id f := c.comp_id f
  assoc f g k := c.assoc f g k

instance (c : CountableCategoryCode) : Countable c.Obj := inferInstanceAs (Countable c.obj)

instance (c : CountableCategoryCode) (a b : c.Obj) : Countable (a ⟶ b) :=
  inferInstanceAs (Countable (c.hom a b))

instance (c : CountableCategoryCode) : CountableCategory c.Obj where

section ofCountable

variable (J : Type v) [Category.{w} J] [CountableCategory J]

/-- An injection of the objects of a countable category into `ℕ`. -/
noncomputable def objEnc : J → ℕ := (Countable.exists_injective_nat J).choose

theorem objEnc_injective : Function.Injective (objEnc J) :=
  (Countable.exists_injective_nat J).choose_spec

/-- The objects of a countable category are in bijection with the range of `objEnc`. -/
noncomputable def objEquiv : J ≃ Set.range (objEnc J) :=
  Equiv.ofInjective _ (objEnc_injective J)

variable {J} in
/-- An injection of a morphism set of a countable category into `ℕ`. -/
noncomputable def homEnc (a b : J) : (a ⟶ b) → ℕ :=
  (Countable.exists_injective_nat (a ⟶ b)).choose

variable {J} in
theorem homEnc_injective (a b : J) : Function.Injective (homEnc a b) :=
  (Countable.exists_injective_nat (a ⟶ b)).choose_spec

/-- A morphism set of a countable category is in bijection with the range of `homEnc`. -/
noncomputable def homEquiv (x y : Set.range (objEnc J)) :
    ((objEquiv J).symm x ⟶ (objEquiv J).symm y) ≃
      Set.range (homEnc ((objEquiv J).symm x) ((objEquiv J).symm y)) :=
  Equiv.ofInjective _ (homEnc_injective _ _)

/-- The code of a countable category. -/
noncomputable def ofCountable : CountableCategoryCode where
  obj := Set.range (objEnc J)
  hom x y := Set.range (homEnc ((objEquiv J).symm x) ((objEquiv J).symm y))
  id x := homEquiv J x x (𝟙 _)
  comp f g := homEquiv J _ _ ((homEquiv J _ _).symm f ≫ (homEquiv J _ _).symm g)
  id_comp f := by simp
  comp_id f := by simp
  assoc f g k := by simp

/-- The functor from the category of the code of a countable category to the category. -/
noncomputable def toOfCountable : (ofCountable J).Obj ⥤ J where
  obj x := (objEquiv J).symm x
  map {x y} f := (homEquiv J x y).symm f
  map_id x := show (homEquiv J x x).symm (homEquiv J x x (𝟙 _)) = _ by simp
  map_comp {x y z} f g := show (homEquiv J x z).symm (homEquiv J x z _) = _ by simp

/-- The functor `toOfCountable` is fully faithful. -/
noncomputable def fullyFaithfulToOfCountable : (toOfCountable J).FullyFaithful where
  preimage {x y} f := homEquiv J x y f
  map_preimage {x y} f := (homEquiv J x y).symm_apply_apply f
  preimage_map {x y} f := (homEquiv J x y).apply_symm_apply f

instance : (toOfCountable J).Full := (fullyFaithfulToOfCountable J).full

instance : (toOfCountable J).Faithful := (fullyFaithfulToOfCountable J).faithful

instance : (toOfCountable J).EssSurj where
  mem_essImage a := ⟨(objEquiv J a : Set.range (objEnc J)),
    ⟨eqToIso ((objEquiv J).symm_apply_apply a)⟩⟩

instance : (toOfCountable J).IsEquivalence where

/-- A countable category is equivalent to the category of its code. -/
noncomputable def equivOfCountable : (ofCountable J).Obj ≌ J :=
  (toOfCountable J).asEquivalence

end ofCountable

end CountableCategoryCode

end CategoryTheory
