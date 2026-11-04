module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-
# Problem Description

We formalize Stacks project, Section 22.26 (Tags 09L4–09L8), on differential
graded categories over a commutative ring `R`, the associated category of
complexes `Comp(A)` and homotopy category `K(A)`, functors of differential
graded categories, and the induced functors on `Comp` and `K` (Tag 09L8).

A *differential graded `R`-module* is a `ℤ`-graded family of `R`-modules
`M = (M^n)` with an `R`-linear differential `d : M^n → M^{n+1}` satisfying
`d ∘ d = 0`.  A *differential graded category over `R`* has, for each pair of
objects `x, y`, such a differential graded module of morphisms, with an
`R`-bilinear, graded composition obeying the Leibniz rule, and with closed
degree-`0` identities.
-/

open CategoryTheory

universe v u

-- Main Definition(s)

/-- **Definition 1 (Tag 09L5).**  A *differential graded category over a
commutative ring `R`*.  For each pair of objects `x, y` the family
`Hom x y n` (degree-`n` morphisms) is a graded `R`-module; the differential `d`
raises the degree by one and squares to zero; composition `comp` is graded and
`R`-bilinear, obeys the Leibniz rule, is associative and unital, and the
identities are closed of degree `0`.

To avoid casting along the (non-definitional) arithmetic identities of the
grading group `ℤ`, the graded operations carry an explicit equality of degrees
(e.g. composition of a degree-`m` and a degree-`n` morphism lands in any
prescribed degree `k` together with a proof `m + n = k`). -/
@[stacks 09L5]
structure DGCategory (R : Type*) [CommRing R] where
  /-- The objects. -/
  Obj : Type u
  /-- Degree-`n` morphisms from `x` to `y`. -/
  Hom : Obj → Obj → ℤ → Type v
  /-- Each degree-`n` Hom-set is an additive abelian group. -/
  addCommGroup : ∀ x y n, AddCommGroup (Hom x y n)
  /-- Each degree-`n` Hom-set is an `R`-module. -/
  module : ∀ x y n, @Module R (Hom x y n) _ (addCommGroup x y n).toAddCommMonoid
  /-- The differential, raising degree by one. -/
  d : ∀ {x y n}, Hom x y n → Hom x y (n + 1)
  /-- The differential is additive. -/
  d_add : ∀ {x y n} (f g : Hom x y n), d (f + g) = d f + d g
  /-- The differential is `R`-linear. -/
  d_smul : ∀ {x y n} (r : R) (f : Hom x y n), d (r • f) = r • d f
  /-- `d ∘ d = 0`. -/
  d_d : ∀ {x y n} (f : Hom x y n), d (d f) = 0
  /-- Composition of a degree-`m` morphism with a degree-`n` morphism, landing
  in the prescribed degree `k = m + n`. -/
  comp : ∀ {x y z} {m n k : ℤ}, m + n = k → Hom y z m → Hom x y n → Hom x z k
  /-- Composition is additive in the first argument. -/
  comp_add_left : ∀ {x y z} {m n k : ℤ} (h : m + n = k) (g₁ g₂ : Hom y z m) (f : Hom x y n),
    comp h (g₁ + g₂) f = comp h g₁ f + comp h g₂ f
  /-- Composition is additive in the second argument. -/
  comp_add_right : ∀ {x y z} {m n k : ℤ} (h : m + n = k) (g : Hom y z m) (f₁ f₂ : Hom x y n),
    comp h g (f₁ + f₂) = comp h g f₁ + comp h g f₂
  /-- Composition is `R`-linear in the first argument. -/
  comp_smul_left : ∀ {x y z} {m n k : ℤ} (h : m + n = k) (r : R) (g : Hom y z m) (f : Hom x y n),
    comp h (r • g) f = r • comp h g f
  /-- Composition is `R`-linear in the second argument. -/
  comp_smul_right : ∀ {x y z} {m n k : ℤ} (h : m + n = k) (r : R) (g : Hom y z m) (f : Hom x y n),
    comp h g (r • f) = r • comp h g f
  /-- The Leibniz rule: for `g` of degree `m` and `f` of degree `n`,
  `d (g ∘ f) = d g ∘ f + (-1)^m • g ∘ d f`.  (Both summands on the right live in
  the degree `k + 1`, with `k = m + n`.) -/
  leibniz : ∀ {x y z} {m n k : ℤ} (h : m + n = k) (g : Hom y z m) (f : Hom x y n),
    d (comp h g f)
      = comp (by omega : (m + 1) + n = k + 1) (d g) f
        + (-1 : R)^(m.natAbs) • comp (by omega : m + (n + 1) = k + 1) g (d f)
  /-- Associativity of composition. -/
  assoc : ∀ {w x y z} {l m n p q r : ℤ}
    (h₁ : m + n = p) (h₂ : l + p = r) (h₃ : l + m = q) (h₄ : q + n = r)
    (e : Hom y z l) (g : Hom x y m) (f : Hom w x n),
    comp h₂ e (comp h₁ g f) = comp h₄ (comp h₃ e g) f
  /-- The identity morphism, of degree `0`. -/
  id : ∀ x, Hom x x 0
  /-- The identity is a left unit. -/
  id_comp : ∀ {x y} {n : ℤ} (f : Hom x y n), comp (by omega : (0 : ℤ) + n = n) (id y) f = f
  /-- The identity is a right unit. -/
  comp_id : ∀ {x y} {n : ℤ} (f : Hom x y n), comp (by omega : n + (0 : ℤ) = n) f (id x) = f
  /-- The identity is closed. -/
  d_id : ∀ x, d (id x) = 0

attribute [instance] DGCategory.addCommGroup DGCategory.module

namespace DGCategory

variable {R : Type*} [CommRing R] (A : DGCategory R)

/-! ### Elementary consequences of the axioms -/

/-- Composition with the zero morphism on the left is zero. -/
@[simp] lemma comp_zero_left {x y z : A.Obj} {m n k : ℤ} (h : m + n = k) (f : A.Hom x y n) :
    A.comp h (0 : A.Hom y z m) f = 0 := by
  simpa using (A.comp_add_left h (0 : A.Hom y z m) 0 f).symm

/-- Composition with the zero morphism on the right is zero. -/
@[simp] lemma comp_zero_right {x y z : A.Obj} {m n k : ℤ} (h : m + n = k) (g : A.Hom y z m) :
    A.comp h g (0 : A.Hom x y n) = 0 := by
  simpa using (A.comp_add_right h g (0 : A.Hom x y n) 0).symm

/-- Composition is compatible with subtraction in the first argument. -/
lemma comp_sub_left {x y z : A.Obj} {m n k : ℤ} (h : m + n = k)
    (g₁ g₂ : A.Hom y z m) (f : A.Hom x y n) :
    A.comp h (g₁ - g₂) f = A.comp h g₁ f - A.comp h g₂ f := by
  exact map_sub (AddMonoidHom.mk' (fun g => A.comp h g f) fun a b => A.comp_add_left h a b f) g₁ g₂

/-- Composition is compatible with subtraction in the second argument. -/
lemma comp_sub_right {x y z : A.Obj} {m n k : ℤ} (h : m + n = k)
    (g : A.Hom y z m) (f₁ f₂ : A.Hom x y n) :
    A.comp h g (f₁ - f₂) = A.comp h g f₁ - A.comp h g f₂ := by
  exact map_sub (AddMonoidHom.mk' (fun f => A.comp h g f) fun a b => A.comp_add_right h g a b) f₁ f₂

/-- The differential sends `0` to `0`. -/
lemma d_zero {x y : A.Obj} {n : ℤ} : A.d (0 : A.Hom x y n) = 0 := by
  simpa using (A.d_add (0 : A.Hom x y n) 0).symm

/-- **A base-ring scalar is composition with a scalar multiple of an identity.** Multiplying a
homogeneous morphism by `r : R` is composing it with `r` times the identity of its target, by
`DGCategory.comp_smul_left` and `DGCategory.id_comp`. Together with `DGFunctor.map_comp` and
`DGFunctor.map_id` this reduces the `R`-linearity of a differential graded functor to its value
on the scalar multiples of the identities. -/
lemma smul_eq_comp_smul_id {x y : A.Obj} {n : ℤ} (r : R) (f : A.Hom x y n) :
    A.comp (zero_add n) (r • A.id y) f = r • f := by
  rw [A.comp_smul_left, A.id_comp]

/-- The same with the identity of the source, by `DGCategory.comp_smul_right` and
`DGCategory.comp_id`. -/
lemma smul_eq_comp_id_smul {x y : A.Obj} {n : ℤ} (r : R) (f : A.Hom x y n) :
    A.comp (add_zero n) f (r • A.id x) = r • f := by
  rw [A.comp_smul_right, A.comp_id]

/-! ### Degree-zero composition

The morphisms of `Comp A` and of `K A` are degree-`0`, so the calculus of composites of
degree-`0` morphisms is what every computation in those categories runs on.
`DGCategory.comp0` is that composition, written in the diagrammatic order, with the degree
bookkeeping `0 + 0 = 0` discharged once and for all; the lemmas below are the axioms of
`DGCategory` read through it. -/

section Comp0

variable {A}

/-- **Composition of two degree-`0` morphisms**, in the diagrammatic order: `comp0 f g` is `f`
followed by `g`.  This is `DGCategory.comp` at `m = n = k = 0`, with the degree equality
discharged, so that composites of degree-`0` morphisms carry no visible degree bookkeeping. -/
def comp0 {x y z : A.Obj} (f : A.Hom x y 0) (g : A.Hom y z 0) : A.Hom x z 0 :=
  A.comp (by omega : (0 : ℤ) + 0 = 0) g f

local infixr:80 " ≫₀ " => comp0

/-- Degree-`0` composition is associative. -/
lemma comp0_assoc {w x y z : A.Obj} (f : A.Hom w x 0) (g : A.Hom x y 0) (h : A.Hom y z 0) :
    (f ≫₀ g) ≫₀ h = f ≫₀ (g ≫₀ h) :=
  A.assoc rfl rfl rfl rfl h g f

/-- The identity of the source is a left unit for degree-`0` composition. -/
lemma id_comp0 {x y : A.Obj} (f : A.Hom x y 0) : A.id x ≫₀ f = f :=
  A.comp_id f

/-- The identity of the target is a right unit for degree-`0` composition. -/
lemma comp0_id {x y : A.Obj} (f : A.Hom x y 0) : f ≫₀ A.id y = f :=
  A.id_comp f

/-- Degree-`0` composition with `0` on the left. -/
lemma zero_comp0 {x y z : A.Obj} (g : A.Hom y z 0) : (0 : A.Hom x y 0) ≫₀ g = 0 :=
  A.comp_zero_right _ g

/-- Degree-`0` composition with `0` on the right. -/
lemma comp0_zero {x y z : A.Obj} (f : A.Hom x y 0) : f ≫₀ (0 : A.Hom y z 0) = 0 :=
  A.comp_zero_left _ f

/-- Degree-`0` composition is additive in its first argument. -/
lemma add_comp0 {x y z : A.Obj} (f g : A.Hom x y 0) (h : A.Hom y z 0) :
    (f + g) ≫₀ h = f ≫₀ h + g ≫₀ h :=
  A.comp_add_right rfl h f g

/-- Degree-`0` composition is additive in its second argument. -/
lemma comp0_add {x y z : A.Obj} (f : A.Hom x y 0) (g h : A.Hom y z 0) :
    f ≫₀ (g + h) = f ≫₀ g + f ≫₀ h :=
  A.comp_add_left rfl g h f

/-- Cancel the last two factors of a degree-`0` composite against each other, when they
compose to an identity. -/
lemma comp0_cancel {x y z : A.Obj} (f : A.Hom x y 0) (g : A.Hom y z 0) (h : A.Hom z y 0)
    (hgh : g ≫₀ h = A.id y) : (f ≫₀ g) ≫₀ h = f := by
  rw [comp0_assoc, hgh, comp0_id]

/-- A degree-`0` composite whose last two factors compose to `0` is itself `0`. -/
lemma comp0_cancel_zero {w x y z : A.Obj} (f : A.Hom w x 0) (g : A.Hom x y 0) (h : A.Hom y z 0)
    (hgh : g ≫₀ h = 0) : (f ≫₀ g) ≫₀ h = 0 := by
  rw [comp0_assoc, hgh, comp0_zero]

end Comp0

/-- The differential reaching a prescribed degree `n` (a cast wrapper around `d`). -/
def d' {x y : A.Obj} {m n : ℤ} (e : m + 1 = n) (f : A.Hom x y m) : A.Hom x y n := e ▸ A.d f

/-- The differential reaching degree `n`, as an additive map. -/
private def d'Hom {x y : A.Obj} {m n : ℤ} (e : m + 1 = n) : A.Hom x y m →+ A.Hom x y n :=
  AddMonoidHom.mk' (A.d' e) (by subst e; exact A.d_add)

/-- A closed degree-`0` morphism, i.e. a cocycle; these are the morphisms of
`Comp A`. -/
abbrev Cocycle (x y : A.Obj) : Type _ := { f : A.Hom x y 0 // A.d f = 0 }

/-- The composite of two cocycles, again a cocycle. -/
def compCocycle {x y z : A.Obj} (g : A.Cocycle y z) (f : A.Cocycle x y) : A.Cocycle x z :=
  ⟨A.comp (show (0 : ℤ) + 0 = 0 by omega) g.1 f.1, by
    rw [A.leibniz, g.2, f.2, A.comp_zero_left, A.comp_zero_right, smul_zero, add_zero]⟩

/-- Composing a closed degree-`0` morphism `g` with the coboundary `d' h`
(`h` of degree `-1`) is a coboundary. -/
lemma comp_dboundary_right {x y z : A.Obj} (g : A.Hom y z 0) (hg : A.d g = 0) (h : A.Hom x y (-1)) :
    A.comp (show (0 : ℤ) + 0 = 0 by omega) g (A.d' (show (-1 : ℤ) + 1 = 0 by omega) h)
      = A.d' (show (-1 : ℤ) + 1 = 0 by omega)
          (A.comp (show (0 : ℤ) + (-1) = -1 by omega) g h) := by
  have hL := A.leibniz (show (0 : ℤ) + (-1) = -1 by omega) g h
  simp only [d']
  rw [hL, hg, A.comp_zero_left, show ((-1 : R) ^ (Int.natAbs 0)) = 1 by norm_num, one_smul]
  abel

/-- Composing the coboundary `d' h` (`h` of degree `-1`) with a closed
degree-`0` morphism `f` is a coboundary. -/
lemma comp_dboundary_left {x y z : A.Obj} (f : A.Hom x y 0) (hf : A.d f = 0) (h : A.Hom y z (-1)) :
    A.comp (show (0 : ℤ) + 0 = 0 by omega) (A.d' (show (-1 : ℤ) + 1 = 0 by omega) h) f
      = A.d' (show (-1 : ℤ) + 1 = 0 by omega)
          (A.comp (show (-1 : ℤ) + 0 = -1 by omega) h f) := by
  have hL := A.leibniz (show (-1 : ℤ) + 0 = -1 by omega) h f
  simp only [d']
  rw [hL, hf, A.comp_zero_right, smul_zero]
  abel

/-! ### Definition 3 (Tag 09L7): the category of complexes `Comp(A)` -/

/-- **Definition 3.1 (Tag 09L7).**  The *category of complexes* `Comp A`: the
objects are those of `A`, the morphisms `x ⟶ y` are the closed degree-`0`
morphisms (cocycles), with composition and identities inherited from `A`. -/
def Comp (A : DGCategory R) : Type _ := A.Obj

/-- The category structure on `Comp A`: morphisms are cocycles, composed by
`DGCategory.compCocycle`, with the identities of `A`. -/
@[sga "4½ Etat_0 1.2.1" "more general"]
instance instCategoryComp : Category (A.Comp) where
  Hom x y := A.Cocycle (x : A.Obj) (y : A.Obj)
  id x := ⟨A.id x, A.d_id x⟩
  comp f g := A.compCocycle g f
  id_comp f := Subtype.ext (A.comp_id f.1)
  comp_id f := Subtype.ext (A.id_comp f.1)
  assoc f g h := Subtype.ext (A.assoc rfl rfl rfl rfl h.1 g.1 f.1)

section Comp0Iso

variable {A}

local infixr:80 " ≫₀ " => comp0

/-- **The first cancellation of an isomorphism of `Comp A`, read on homogeneous morphisms.**
The two components of such an isomorphism are closed degree-`0` morphisms, and the identity
`e.hom ≫ e.inv = 𝟙` is an identity of degree-`0` composites. -/
lemma hom_inv_comp0 {z z' : A.Obj} (e : (show A.Comp from z) ≅ (show A.Comp from z')) :
    e.hom.1 ≫₀ e.inv.1 = A.id z :=
  congrArg Subtype.val e.hom_inv_id

/-- **The second cancellation of an isomorphism of `Comp A`, read on homogeneous morphisms**,
the companion of `DGCategory.hom_inv_comp0`. -/
lemma inv_hom_comp0 {z z' : A.Obj} (e : (show A.Comp from z) ≅ (show A.Comp from z')) :
    e.inv.1 ≫₀ e.hom.1 = A.id z' :=
  congrArg Subtype.val e.inv_hom_id

end Comp0Iso

/-! ### Definition 3 (Tag 09L7): the homotopy category `K(A)` -/

/-- Two cocycles are homotopic if their difference is a coboundary `d h` with
`h` of degree `-1`. -/
def Homotopic {x y : A.Obj} (f g : A.Cocycle x y) : Prop :=
  ∃ h : A.Hom x y (-1), f.1 - g.1 = A.d' (show (-1 : ℤ) + 1 = 0 by omega) h

/-- Every cocycle is homotopic to itself. -/
lemma homotopic_refl {x y : A.Obj} (f : A.Cocycle x y) : A.Homotopic f f := by
  refine ⟨0, ?_⟩
  rw [show (0 : A.Hom x y (-1)) = (0 : A.Hom x y (-1)) - 0 by simp]
  simp [d', A.d_zero]

/-- Homotopy of cocycles is symmetric. -/
lemma homotopic_symm {x y : A.Obj} {f g : A.Cocycle x y} (hfg : A.Homotopic f g) :
    A.Homotopic g f := by
  obtain ⟨h, hh⟩ := hfg
  refine ⟨-h, ?_⟩
  have := map_neg (A.d'Hom (show (-1 : ℤ) + 1 = 0 by omega)) h
  rw [d'Hom, AddMonoidHom.mk'_apply] at this
  rw [this, ← hh]
  abel

/-- Homotopy of cocycles is transitive. -/
lemma homotopic_trans {x y : A.Obj} {f g k : A.Cocycle x y}
    (hfg : A.Homotopic f g) (hgk : A.Homotopic g k) : A.Homotopic f k := by
  obtain ⟨h₁, hh₁⟩ := hfg
  obtain ⟨h₂, hh₂⟩ := hgk
  refine ⟨h₁ + h₂, ?_⟩
  have := map_add (A.d'Hom (show (-1 : ℤ) + 1 = 0 by omega)) h₁ h₂
  rw [d'Hom, AddMonoidHom.mk'_apply] at this
  rw [this, ← hh₁, ← hh₂]
  abel

/-- Homotopy as an equivalence relation on the cocycles from `x` to `y`. -/
instance homotopySetoid (x y : A.Obj) : Setoid (A.Cocycle x y) where
  r := A.Homotopic
  iseqv := ⟨A.homotopic_refl, A.homotopic_symm, A.homotopic_trans⟩

/-- Composition of cocycles respects homotopy in the second argument. -/
lemma compCocycle_homotopic_right {x y z : A.Obj} (g : A.Cocycle y z) {f₁ f₂ : A.Cocycle x y}
    (hf : A.Homotopic f₁ f₂) : A.Homotopic (A.compCocycle g f₁) (A.compCocycle g f₂) := by
  obtain ⟨h, hh⟩ := hf
  refine ⟨A.comp (show (0 : ℤ) + (-1) = -1 by omega) g.1 h, ?_⟩
  simp only [compCocycle]
  rw [← A.comp_sub_right, hh, ← A.comp_dboundary_right g.1 g.2 h]

/-- Composition of cocycles respects homotopy in the first argument. -/
lemma compCocycle_homotopic_left {x y z : A.Obj} {g₁ g₂ : A.Cocycle y z} (f : A.Cocycle x y)
    (hg : A.Homotopic g₁ g₂) : A.Homotopic (A.compCocycle g₁ f) (A.compCocycle g₂ f) := by
  obtain ⟨h, hh⟩ := hg
  refine ⟨A.comp (show (-1 : ℤ) + 0 = -1 by omega) h f.1, ?_⟩
  simp only [compCocycle]
  rw [← A.comp_sub_left, hh, ← A.comp_dboundary_left f.1 f.2 h]

/-- **Definition 3.2 (Tag 09L7).**  The *homotopy category* `K A`: the objects
are those of `A`, and `Hom x y = H^0(Hom_A(x, y))`, i.e. cocycles modulo
homotopy. -/
@[sga "4½ Etat_0 1.2.2"]
def K (A : DGCategory R) : Type _ := A.Obj

/-- Morphisms of `K A` are homotopy classes of cocycles. -/
@[sga "4 XVII 2.2.8" "absolute (non-fibered)"]
abbrev HomotopyClass (x y : A.Obj) : Type _ := Quotient (A.homotopySetoid x y)

/-- Composition of homotopy classes, well-defined by
`compCocycle_homotopic_left` and `compCocycle_homotopic_right`. -/
@[sga "4½ Etat_0 1.2.2"]
def compK {x y z : A.Obj} (g : A.HomotopyClass y z) (f : A.HomotopyClass x y) :
    A.HomotopyClass x z :=
  Quotient.map₂ (fun g f => A.compCocycle g f)
    (fun _ g₂ hg f₁ _ hf =>
      A.homotopic_trans (A.compCocycle_homotopic_left f₁ hg)
        (A.compCocycle_homotopic_right g₂ hf)) g f

/-- The category structure on `K A`: morphisms are homotopy classes of cocycles, composed by
`DGCategory.compK`, with the classes of the identities of `A`. -/
@[sga "4½ Etat_0 1.2.2" "more general"]
instance instCategoryK : Category (A.K) where
  Hom x y := A.HomotopyClass (x : A.Obj) (y : A.Obj)
  id x := Quotient.mk _ ⟨A.id x, A.d_id x⟩
  comp f g := A.compK g f
  id_comp {x y} f :=
    Quotient.inductionOn f fun f => congrArg (Quotient.mk _) (Subtype.ext (A.comp_id f.1))
  comp_id {x y} f :=
    Quotient.inductionOn f fun f => congrArg (Quotient.mk _) (Subtype.ext (A.id_comp f.1))
  assoc {w x y z} f g h := by
    refine Quotient.inductionOn₃ f g h (fun f g h => ?_)
    simp only [compK, Quotient.map₂_mk]
    exact congrArg (Quotient.mk _) (Subtype.ext (A.assoc rfl rfl rfl rfl h.1 g.1 f.1))

/-! ### Definition 2 (Tag 09L6): functors of differential graded categories -/

/-- **Definition 2 (Tag 09L6).**  A *functor of differential graded categories
over `R`*: a map on objects together with degree-preserving `R`-linear maps on
Hom-modules that commute with the differential and preserve composition and
identities. -/
@[stacks 09L6]
structure DGFunctor {R : Type*} [CommRing R] (A B : DGCategory R) where
  /-- The map on objects. -/
  obj : A.Obj → B.Obj
  /-- The degree-preserving map on Hom-modules. -/
  map : ∀ {x y : A.Obj} {n : ℤ}, A.Hom x y n → B.Hom (obj x) (obj y) n
  /-- `F` is additive on Hom-modules. -/
  map_add : ∀ {x y : A.Obj} {n : ℤ} (f g : A.Hom x y n), map (f + g) = map f + map g
  /-- `F` is `R`-linear on Hom-modules. -/
  map_smul : ∀ {x y : A.Obj} {n : ℤ} (r : R) (f : A.Hom x y n), map (r • f) = r • map f
  /-- `F` commutes with the differential. -/
  map_d : ∀ {x y : A.Obj} {n : ℤ} (f : A.Hom x y n), map (A.d f) = B.d (map f)
  /-- `F` preserves composition. -/
  map_comp : ∀ {x y z : A.Obj} {m n k : ℤ} (h : m + n = k) (g : A.Hom y z m) (f : A.Hom x y n),
    map (A.comp h g f) = B.comp h (map g) (map f)
  /-- `F` preserves identities. -/
  map_id : ∀ x : A.Obj, map (A.id x) = B.id (obj x)

/-! ### Supporting constructions for Tag 09L8 -/

/-- A DG-functor sends `0` to `0`. -/
lemma DGFunctor.map_zero {A B : DGCategory R} (F : DGFunctor A B) {x y : A.Obj} {n : ℤ} :
    F.map (0 : A.Hom x y n) = 0 := by
  simpa using (F.map_add (0 : A.Hom x y n) 0).symm

/-- The image of a cocycle under a DG-functor is a cocycle. -/
lemma DGFunctor.map_cocycle {A B : DGCategory R} (F : DGFunctor A B) {x y : A.Obj}
    (f : A.Cocycle x y) : B.d (F.map f.1) = 0 := by
  rw [← F.map_d, f.2, F.map_zero]

/-- The cocycle `F.map f` for a cocycle `f`. -/
def DGFunctor.mapCocycle {A B : DGCategory R} (F : DGFunctor A B) {x y : A.Obj}
    (f : A.Cocycle x y) : B.Cocycle (F.obj x) (F.obj y) :=
  ⟨F.map f.1, F.map_cocycle f⟩

/-- The induced functor on `Comp`, equal to `F.obj` on objects and sending a
cocycle `f` to the cocycle `F.map f`. -/
def DGFunctor.onComp {A B : DGCategory R} (F : DGFunctor A B) : A.Comp ⥤ B.Comp where
  obj x := F.obj x
  map f := F.mapCocycle f
  map_id x := Subtype.ext (F.map_id x)
  map_comp f g := Subtype.ext (F.map_comp _ g.1 f.1)

/-- The induced map on homotopy classes, descending `F.mapCocycle`. -/
def DGFunctor.mapHomotopyClass {A B : DGCategory R} (F : DGFunctor A B) {x y : A.Obj}
    (f : A.HomotopyClass x y) : B.HomotopyClass (F.obj x) (F.obj y) :=
  Quotient.map (fun f => F.mapCocycle f)
    (fun f₁ f₂ hf => by
      obtain ⟨h, hh⟩ := hf
      refine ⟨F.map h, ?_⟩
      have : (F.mapCocycle f₁).1 - (F.mapCocycle f₂).1 = F.map (f₁.1 - f₂.1) := by
        simp only [DGFunctor.mapCocycle]
        rw [show f₁.1 - f₂.1 = f₁.1 + (-1 : R) • f₂.1 by rw [neg_one_smul, sub_eq_add_neg],
          F.map_add, F.map_smul, neg_one_smul]
        abel
      rw [this, hh]
      simp only [d']
      rw [F.map_d]) f

/-- The induced functor on `K`, equal to `F.obj` on objects and sending the
homotopy class `[f]` to `[F.map f]`. -/
def DGFunctor.onK {A B : DGCategory R} (F : DGFunctor A B) : A.K ⥤ B.K where
  obj x := F.obj x
  map f := F.mapHomotopyClass f
  map_id x := congrArg (Quotient.mk _) (Subtype.ext (F.map_id x))
  map_comp f g :=
    Quotient.inductionOn₂ f g fun f g =>
      congrArg (Quotient.mk _) (Subtype.ext (F.map_comp _ g.1 f.1))

/-- The canonical functor `Comp A ⥤ K A` sending a cocycle to its homotopy
class (identity on objects). -/
@[sga "4½ Etat_0 1.2.2"]
def compToK (A : DGCategory R) : A.Comp ⥤ A.K where
  obj x := x
  map f := Quotient.mk _ f
  map_id _ := rfl
  map_comp _ _ := rfl

end DGCategory

-- Main Statement(s)

/-
**Theorem (Stacks Tag 09L8).**  A functor `F : A → B` of differential graded
categories over `R` induces functors of ordinary categories
`Comp F : Comp A ⥤ Comp B` and `K F : K A ⥤ K B`, agreeing with `F` on objects,
sending a closed degree-`0` morphism (resp. its homotopy class) to its image.

We state this as the existence of two ordinary functors together with their
characterising properties:
* on objects both functors equal `F.obj`;
* `Comp F` sends a cocycle `f` to `F.map f` (which is again a cocycle);
* `K F` sends the homotopy class `[f]` to `[F.map f]`;
* the canonical functor `Comp → K` intertwines `Comp F` and `K F`.
-/

namespace DGCategory

variable {R : Type*} [CommRing R] {A B : DGCategory R}

/-- **Tag 09L8.**  A DG-functor `F : A → B` induces ordinary functors
`Comp F : Comp A ⥤ Comp B` (here `F.onComp`) and `K F : K A ⥤ K B` (here
`F.onK`), characterised by:

1. (objects) both agree with `F` on objects;
2. (morphisms of `Comp`) `Comp F` sends a closed degree-`0` morphism `f` to the
   (again closed) morphism `F.map f`;
3. (morphisms of `K`) `K F` sends the homotopy class `[f]` to `[F.map f]`;
4. (compatibility) the canonical functors `Comp → K` intertwine `Comp F` and
   `K F`, i.e. `compToK A ⋙ K F = Comp F ⋙ compToK B`.

These are the genuine functoriality content of the lemma; `F.onComp` and
`F.onK` are honest `CategoryTheory.Functor`s, so identity- and
composition-preservation (part (4) of the informal statement) is built into
their types. -/
@[stacks 09L8]
theorem dgFunctor_induces_functors (F : DGFunctor A B) :
    (∀ x : A.Comp, F.onComp.obj x = F.obj x) ∧
      (∀ {x y : A.Comp} (f : x ⟶ y), (F.onComp.map f).1 = F.map f.1) ∧
      (∀ x : A.K, F.onK.obj x = F.obj x) ∧
      (∀ {x y : A.Obj} (f : A.Cocycle x y),
        F.onK.map (Quotient.mk _ f : A.HomotopyClass x y)
          = Quotient.mk _ (F.mapCocycle f)) ∧
      (compToK A ⋙ F.onK = F.onComp ⋙ compToK B) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

end DGCategory
