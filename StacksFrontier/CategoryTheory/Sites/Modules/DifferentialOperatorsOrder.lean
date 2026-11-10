module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Throughout, fix a site `C` (a category equipped with a Grothendieck topology `J`)
and a homomorphism of sheaves of rings `φ : O₁ ⟶ O₂` on `C`. All modules below are
sheaves of `O₂`-modules. Via `φ`, every sheaf of `O₂`-modules is also a sheaf of
`O₁`-modules, so "`O₁`-linear" applied to an `O₂`-module map makes sense.

A map `D : F → G` of sheaves of `O₂`-modules means a morphism of the underlying
sheaves of abelian groups (a collection of additive maps on local sections compatible
with restriction). For a local section `g` of `O₂`, multiplication by `g` is the map
`s ↦ g • s` on local sections.

## Main Definition (Differential operator of order `k`; Stacks Tag 09CR)

Let `k ≥ 0` be an integer, and let `F, G` be sheaves of `O₂`-modules. A differential
operator `D : F → G` of order `k` (relative to `φ : O₁ → O₂`) is defined recursively:

* (Base case, `k = 0`.) `D` is a differential operator of order `0` iff `D` is
  `O₂`-linear (a morphism of sheaves of `O₂`-modules).
* (Inductive case, `k ≥ 1`.) `D` is a differential operator of order `k` iff `D` is
  `O₁`-linear (via `φ`) and, for every local section `g` of `O₂` over every object `U`,
  the commutator `[D, g] : s ↦ D (g • s) - g • D s` is a differential operator of
  order `k - 1`.

## Main Statement (Stacks Tag 09CS, Lemma 18.34.2)

If `D : E → F` is a differential operator of order `k` and `D' : F → G` is a
differential operator of order `k'`, then `D' ∘ D : E → G` is a differential operator
of order `k + k'`.

## Formalization notes

* We model a "map of underlying sheaves of abelian groups" by the data of additive
  maps on sections, indexed by objects, that is compatible with restriction. To make
  the recursive definition (and the commutator) stay on a single site we work, for a
  fixed base object `U`, with families indexed by the slice category `Over U`. Such a
  family is `DiffOp.RawOp F G U`. The commutator with respect to a section
  `g : O₂(U)` again lives over the same base `U`, so the recursion on the order is
  well-founded without changing the site.

* A *global* operator (indexed by all objects of `C`) is restricted to each base `U`
  by precomposing with the slice projection; it is a global differential operator of
  order `k` iff every such restriction is. This is faithful to Stacks 09CR, where the
  defining condition on `[D, g]` is checked on the localized site `C/U`.
-/

open CategoryTheory Opposite

namespace DiffOp

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
variable {O₁ O₂ : Sheaf J RingCat}

/-- The ring homomorphism on sections of `O₁ → O₂` induced by `φ` at an object `X`. -/
@[ega "0 12.1.3" "more general"]
noncomputable def sectionRingHom (φ : O₁ ⟶ O₂) (X : Cᵒᵖ) :
    O₁.obj.obj X →+* O₂.obj.obj X :=
  (((sheafToPresheaf J RingCat).map φ).app X).hom

/-- A *raw operator* `F → G` over a base object `U : C`: the data of an additive map on
local sections over each object `Y` of the slice category `Over U` (i.e. each `Y → U`).
This is the underlying datum of a "map of sheaves of abelian groups" localized at `U`. -/
def RawOp (F G : SheafOfModules O₂) (U : C) : Type _ :=
  ∀ (Y : Over U), (F.val.obj (op Y.left)) →+ (G.val.obj (op Y.left))

namespace RawOp

variable {F G : SheafOfModules O₂} {U : C}

/-- A raw operator is *natural* (compatible with restriction inside the slice) if for
every morphism `h : Y ⟶ Y'` in `Over U`, applying `D` and then restricting equals
restricting and then applying `D`. -/
def IsNatural (D : RawOp F G U) : Prop :=
  ∀ (Y Y' : Over U) (h : Y ⟶ Y') (s : F.val.obj (op Y'.left)),
    D Y ((F.val.presheaf.map h.left.op) s) = (G.val.presheaf.map h.left.op) (D Y' s)

/-- `D` is `O₂`-linear over the base `U`: at each object of the slice it commutes with
multiplication by ring sections. -/
def IsO2Linear (D : RawOp F G U) : Prop :=
  ∀ (Y : Over U) (r : O₂.obj.obj (op Y.left)) (s : F.val.obj (op Y.left)),
    D Y (r • s) = r • D Y s

/-- `D` is `O₁`-linear over the base `U` (via `φ`): at each object of the slice it
commutes with multiplication by ring sections coming from `O₁`. -/
def IsO1Linear (φ : O₁ ⟶ O₂) (D : RawOp F G U) : Prop :=
  ∀ (Y : Over U) (a : O₁.obj.obj (op Y.left)) (s : F.val.obj (op Y.left)),
    D Y (sectionRingHom φ (op Y.left) a • s) = sectionRingHom φ (op Y.left) a • D Y s

/-- The commutator `[D, g]` of a raw operator `D` over base `U` with a ring section
`g : O₂(U)`. At an object `Y → U` of the slice it sends `s` to `D Y (g·s) - g·D Y s`,
where `g` is restricted to `Y` along the structural map `Y.hom : Y.left ⟶ U`. -/
@[ega "IV 16.8.8"]
noncomputable def commutator (g : O₂.obj.obj (op U)) (D : RawOp F G U) : RawOp F G U :=
  fun Y =>
    let gY : O₂.obj.obj (op Y.left) := (O₂.obj.map Y.hom.op) g
    { toFun := fun s => D Y (gY • s) - gY • D Y s
      map_zero' := by simp
      map_add' := by
        intro a b
        simp only [smul_add, map_add]
        abel }

/-- Composition of raw operators over the same base `U`, pointwise on the slice. -/
def comp {E F G : SheafOfModules O₂} {U : C}
    (D' : RawOp F G U) (D : RawOp E F U) : RawOp E G U :=
  fun Y => (D' Y).comp (D Y)

/-- Evaluating the composite `comp D' D` at `Y` applies `D Y` and then `D' Y`. -/
@[simp] lemma comp_apply {E F G : SheafOfModules O₂} {U : C}
    (D' : RawOp F G U) (D : RawOp E F U) (Y : Over U) (s) :
    comp D' D Y s = D' Y (D Y s) := rfl

/-- The restriction of a raw operator over `U` to the slice over `Y.left`. -/
def slice {F G : SheafOfModules O₂} {U : C}
    (D : RawOp F G U) (Y : Over U) : RawOp F G Y.left :=
  fun Z => D (Over.mk (Z.hom ≫ Y.hom))

/-- Evaluating `slice D Y` at `Z` is evaluating `D` at the composite `Z.left ⟶ Y.left ⟶ U`. -/
@[simp] lemma slice_apply {F G : SheafOfModules O₂} {U : C}
    (D : RawOp F G U) (Y : Over U) (Z : Over Y.left) (s) :
    slice D Y Z s = D (Over.mk (Z.hom ≫ Y.hom)) s := rfl

/-- Pointwise sum of raw operators. -/
def add {F G : SheafOfModules O₂} {U : C}
    (D₁ D₂ : RawOp F G U) : RawOp F G U :=
  fun Y => D₁ Y + D₂ Y

/-- Evaluating the sum `add D₁ D₂` at `Y` is the sum of the evaluations of `D₁` and `D₂`. -/
@[simp] lemma add_apply {F G : SheafOfModules O₂} {U : C}
    (D₁ D₂ : RawOp F G U) (Y : Over U) (s) :
    add D₁ D₂ Y s = D₁ Y s + D₂ Y s := rfl

end RawOp

/-- A differential operator of order `≤ k` over the base `U` (Stacks Tag 09CR), defined
recursively on `k`.

* Order `0`: `D` is `O₂`-linear (and natural).
* Order `k+1`: `D` is `O₁`-linear (and natural) and, for every object `Y → U` of the
  slice and every section `g` of `O₂` over `Y`, the commutator `[D, g]` (over base
  `Y.left`) is a differential operator of order `k`. -/
@[ega "IV 16.8.1" "more general", sga "3 VIIA 1.1.1" "more general", sga "3 VIIA 1.4"]
def IsDiffOpOfOrder (φ : O₁ ⟶ O₂) :
    ∀ (_ : ℕ) {F G : SheafOfModules O₂} {U : C}, RawOp F G U → Prop
  | 0, _, _, _, D => D.IsNatural ∧ D.IsO2Linear
  | (k + 1), F, G, U, D =>
      D.IsNatural ∧ D.IsO1Linear φ ∧
        ∀ (Y : Over U) (g : O₂.obj.obj (op Y.left)),
          IsDiffOpOfOrder φ k
            (F := F) (G := G) (U := Y.left)
            (RawOp.commutator (F := F) (G := G) (U := Y.left) g
              (fun (Z : Over Y.left) => D (Over.mk (Z.hom ≫ Y.hom))))

/-- A *global* operator `F → G`: an additive map on local sections over every object. -/
def GlobalOp (F G : SheafOfModules O₂) : Type _ :=
  ∀ (X : Cᵒᵖ), (F.val.obj X) →+ (G.val.obj X)

namespace GlobalOp

variable {F G : SheafOfModules O₂}

/-- The restriction of a global operator to the slice over a base object `U`. -/
def restrict (D : GlobalOp F G) (U : C) : RawOp F G U :=
  fun Y => D (op Y.left)

end GlobalOp

/-- A global operator `D : F → G` is a differential operator of order `≤ k` if its
restriction to every base object `U` is a differential operator of order `≤ k`. -/
@[ega "IV 16.8.1",
  sga "3 VIIA 1.4" "order ≤ n operators",
  sga "6 II AppII.1.2.2" "Diff^n(E,F)",
  sga "3 VIIA 1.1.1" "more general"]
def IsGlobalDiffOpOfOrder (φ : O₁ ⟶ O₂) (k : ℕ) {F G : SheafOfModules O₂}
    (D : GlobalOp F G) : Prop :=
  ∀ (U : C), IsDiffOpOfOrder φ k (D.restrict U)

/-- Composition of global operators: `(D' ∘ D) X = D' X ∘ D X` on sections. -/
def GlobalOp.comp {E F G : SheafOfModules O₂} (D' : GlobalOp F G) (D : GlobalOp E F) :
    GlobalOp E G :=
  fun X => (D' X).comp (D X)

/-- **S0 (global → raw reduction).** The restriction of a composite global operator is
the raw composite of the restrictions. Definitional:
`(D'.comp D).restrict U = fun Y => (D' (op Y.left)).comp (D (op Y.left))
   = RawOp.comp (D'.restrict U) (D.restrict U)`. -/
lemma GlobalOp.restrict_comp {E F G : SheafOfModules O₂}
    (D' : GlobalOp F G) (D : GlobalOp E F) (U : C) :
    (D'.comp D).restrict U = RawOp.comp (D'.restrict U) (D.restrict U) := rfl

namespace RawOp

variable {E F G : SheafOfModules O₂} {U : C}

/-- Unfolding of `IsDiffOpOfOrder` at a successor: the third conjunct phrased via
`slice`. (Definitional; `slice D Y Z = D (Over.mk (Z.hom ≫ Y.hom))`.) -/
lemma isDiffOpOfOrder_succ_iff (φ : O₁ ⟶ O₂) (k : ℕ) (D : RawOp F G U) :
    IsDiffOpOfOrder φ (k + 1) D ↔
      D.IsNatural ∧ D.IsO1Linear φ ∧
        ∀ (Y : Over U) (g : O₂.obj.obj (op Y.left)),
          IsDiffOpOfOrder φ k (commutator g (slice D Y)) :=
  Iff.rfl

/-! ### Supporting lemmas for the composition theorem (subgoals to be proved later) -/

/-- An `O₂`-linear raw operator is `O₁`-linear (via `φ`). -/
private theorem isO1Linear_of_isO2Linear (φ : O₁ ⟶ O₂) {D : RawOp F G U}
    (h : D.IsO2Linear) : D.IsO1Linear φ :=
  fun Y a s => h Y (sectionRingHom φ (op Y.left) a) s

/-- The commutator of an `O₂`-linear raw operator with any section vanishes. -/
private theorem commutator_apply_eq_zero {D : RawOp F G U} (h : D.IsO2Linear)
    (g : O₂.obj.obj (op U)) (Y : Over U) (s : F.val.obj (op Y.left)) :
    commutator g D Y s = 0 :=
  sub_eq_zero_of_eq (h Y _ s)

/-- A raw operator that is pointwise zero has every order. -/
private theorem isDiffOpOfOrder_of_forall_eq_zero (φ : O₁ ⟶ O₂) (j : ℕ) :
    ∀ {E' F' : SheafOfModules O₂} {U' : C} (Z0 : RawOp E' F' U'),
      (∀ Y s, Z0 Y s = 0) → IsDiffOpOfOrder φ j Z0 := by
  induction j with
  | zero =>
    intro E' F' U' Z0 hZ
    refine ⟨?_, ?_⟩
    · intro Y Y' h s
      rw [hZ Y _, hZ Y' s, map_zero]
    · intro Y r s
      rw [hZ Y _, hZ Y s, smul_zero]
  | succ n ih =>
    intro E' F' U' Z0 hZ
    refine ⟨?_, ?_, ?_⟩
    · intro Y Y' h s
      rw [hZ Y _, hZ Y' s, map_zero]
    · intro Y a s
      rw [hZ Y _, hZ Y s, smul_zero]
    · intro Y g
      apply ih
      intro Z s
      change (Z0 (Over.mk (Z.hom ≫ Y.hom))) _ - _ • (Z0 (Over.mk (Z.hom ≫ Y.hom))) s = 0
      rw [hZ, hZ, smul_zero, sub_zero]

/-- **S1 (Monotonicity).** A differential operator of order `k` is also one of order
`k+1`. Proof by induction on `k`: at `k = 0`, `O₂`-linear ⇒ `O₁`-linear (via `φ`), so
the natural+`O₂`-linear datum satisfies the order-1 clause whose commutators are
order-0 (each `[D,g]` of an `O₂`-linear `D` is the zero operator, which is natural &
`O₂`-linear). At the successor, `D` is `O₁`-linear and each `[D,g]` has order `k`, hence
order `k+1` by the IH; naturality and `O₁`-linearity carry over unchanged. -/
@[ega "IV 16.8.10" "more general"]
lemma isDiffOpOfOrder_succ_of_isDiffOpOfOrder (φ : O₁ ⟶ O₂) (k : ℕ)
    {U : C} (D : RawOp F G U) (h : IsDiffOpOfOrder φ k D) :
    IsDiffOpOfOrder φ (k + 1) D := by
  induction k generalizing F G U with
  | zero =>
    refine ⟨h.1, isO1Linear_of_isO2Linear φ h.2, fun Y g => ?_⟩
    -- The commutator of an O₂-linear operator is the zero operator, hence order 0.
    exact isDiffOpOfOrder_of_forall_eq_zero φ 0 _
      (commutator_apply_eq_zero (D := slice D Y)
        (fun Z r s => h.2 (Over.mk (Z.hom ≫ Y.hom)) r s) g)
  | succ n ih =>
    refine ⟨h.1, h.2.1, ?_⟩
    intro Y g
    exact ih (commutator g (slice D Y)) (h.2.2 Y g)

/-- **S1b.** Any order-`k` operator is `O₁`-linear (via `φ`). For `k = 0` this is
"`O₂`-linear ⇒ `O₁`-linear via `φ`": `sectionRingHom φ a • s = φ(a) • s`, and `D` is
`O₂`-linear. For `k+1` it is the first/second conjunct of the definition. -/
lemma isO1Linear_of_isDiffOpOfOrder (φ : O₁ ⟶ O₂) (k : ℕ)
    {U : C} (D : RawOp F G U) (h : IsDiffOpOfOrder φ k D) :
    D.IsO1Linear φ := by
  -- For k=0: unfold IsO2Linear, rewrite the O₁-scalar action through `sectionRingHom`
  -- = `φ.app`/`RingHom`, reduce to O₂-linearity.  For k+1: it is `h.2.1`.
  cases k with
  | zero => exact isO1Linear_of_isO2Linear φ h.2
  | succ n => exact h.2.1

/-- **S1c.** Any order-`k` operator is natural. (`h.1` in both clauses.) -/
lemma isNatural_of_isDiffOpOfOrder (φ : O₁ ⟶ O₂) (k : ℕ)
    {U : C} (D : RawOp F G U) (h : IsDiffOpOfOrder φ k D) :
    D.IsNatural := by
  cases k with
  | zero => exact h.1
  | succ n => exact h.1

/-- **S2-nat.** Composition of natural raw operators is natural. -/
lemma IsNatural.comp {U : C} {D' : RawOp F G U} {D : RawOp E F U}
    (hD' : D'.IsNatural) (hD : D.IsNatural) : (RawOp.comp D' D).IsNatural := by
  -- unfold IsNatural; comp_apply; chain hD then hD'.
  intro Y Y' h s
  simp only [comp_apply]
  rw [hD Y Y' h s, hD' Y Y' h (D Y' s)]

/-- **S2-O2.** Composition of `O₂`-linear raw operators is `O₂`-linear. -/
lemma IsO2Linear.comp {U : C} {D' : RawOp F G U} {D : RawOp E F U}
    (hD' : D'.IsO2Linear) (hD : D.IsO2Linear) : (RawOp.comp D' D).IsO2Linear := by
  -- comp_apply; rewrite hD then hD'.
  intro Y r s
  simp only [comp_apply]
  rw [hD Y r s, hD' Y r (D Y s)]

/-- **S2-O1.** Composition of `O₁`-linear raw operators is `O₁`-linear. -/
lemma IsO1Linear.comp (φ : O₁ ⟶ O₂) {U : C} {D' : RawOp F G U} {D : RawOp E F U}
    (hD' : D'.IsO1Linear φ) (hD : D.IsO1Linear φ) : (RawOp.comp D' D).IsO1Linear φ := by
  -- comp_apply; rewrite hD then hD'.
  intro Y a s
  simp only [comp_apply]
  rw [hD Y a s, hD' Y a (D Y s)]

/-- **S3 (CRUX — commutator-of-composition identity).** For raw operators `A : F → G`
and `B : E → F` over the base `U` and a section `g : O₂(U)`,
`[g, A∘B] = A∘[g,B] + [g,A]∘B` as raw operators. Pointwise this is the telescoping
`A(B(g·s)) − g·A(B s) = A(B(g·s) − g·B s) + (A(g·B s) − g·A(B s))`, which holds because
each `A Y` is additive (an `AddMonoidHom`). Pure algebra; no order hypotheses. -/
lemma commutator_comp {U : C} (g : O₂.obj.obj (op U))
    (A : RawOp F G U) (B : RawOp E F U) :
    commutator g (comp A B)
      = add (comp A (commutator g B)) (comp (commutator g A) B) := by
  -- SANITY CHECK PASSED (statement TRUE; this proof was machine-verified to close it):
  funext Y; ext s
  simp only [comp_apply, add_apply, commutator, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [map_sub]; abel

/-- **S3-slice.** `slice` commutes with `comp`: `slice (comp D' D) Y = comp (slice D' Y)
(slice D Y)`. Definitional (both sides apply `D'`/`D` at `Over.mk (Z.hom ≫ Y.hom)`). -/
lemma slice_comp {U : C} (D' : RawOp F G U) (D : RawOp E F U) (Y : Over U) :
    slice (comp D' D) Y = comp (slice D' Y) (slice D Y) := rfl

/-- **S6 (slice preserves order).** A slice of an order-`k` operator has order `k`.
Proof by induction on `k`: at `0`, restricting the naturality / `O₂`-linearity quantifier
to the slice; at `k+1`, the successor clause already quantifies over all slices, and the
commutator over a slice is itself a slice of the commutator (definitional reindexing of
`Over` along `Z.hom ≫ Y.hom`), reduced by the IH. -/
@[ega "IV 16.8.3" "partial"]
lemma isDiffOpOfOrder_slice (φ : O₁ ⟶ O₂) (k : ℕ)
    {U : C} (D : RawOp F G U) (h : IsDiffOpOfOrder φ k D) (Y : Over U) :
    IsDiffOpOfOrder φ k (slice D Y) := by
  -- induction on k; uses that `commutator g (slice (slice D Y) Z)` is definitionally a
  -- slice of `commutator g' (slice D ·)`; reindex `Over` and apply IH.
  induction k generalizing F G U with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro Z Z' hh s
      exact h.1 (Over.mk (Z.hom ≫ Y.hom)) (Over.mk (Z'.hom ≫ Y.hom))
        (Over.homMk hh.left (by simp)) s
    · intro Z r s
      exact h.2 (Over.mk (Z.hom ≫ Y.hom)) r s
  | succ n ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro Z Z' hh s
      exact h.1 (Over.mk (Z.hom ≫ Y.hom)) (Over.mk (Z'.hom ≫ Y.hom))
        (Over.homMk hh.left (by simp)) s
    · intro Z a s
      exact h.2.1 (Over.mk (Z.hom ≫ Y.hom)) a s
    · intro Z g
      have key : (fun (W : Over Z.left) => (slice D Y) (Over.mk (W.hom ≫ Z.hom)))
          = slice D (Over.mk (Z.hom ≫ Y.hom)) := by
        funext W
        simp only [slice, Over.mk_left, Over.mk_hom]
        rw [Category.assoc]
      rw [show (commutator g (fun (W : Over Z.left) => (slice D Y) (Over.mk (W.hom ≫ Z.hom))))
            = commutator g (slice D (Over.mk (Z.hom ≫ Y.hom))) from by rw [key]]
      exact h.2.2 (Over.mk (Z.hom ≫ Y.hom)) g

/-- **S5 (Additivity closure).** The pointwise sum of two order-`m` operators is an
order-`m` operator. Proof by induction on `m`: at `0`, sum of natural is natural and sum
of `O₂`-linear is `O₂`-linear; at `m+1`, sum of natural/`O₁`-linear are such, and
`[g, D₁+D₂] = [g,D₁] + [g,D₂]`, which is order-`m` by the IH (and `add`/`slice`
distribute). -/
@[ega "IV 16.8.3" "partial", sga "3 VIIA 1.4" "partial"]
lemma isDiffOpOfOrder_add (φ : O₁ ⟶ O₂) (m : ℕ)
    {U : C} (D₁ D₂ : RawOp F G U)
    (h₁ : IsDiffOpOfOrder φ m D₁) (h₂ : IsDiffOpOfOrder φ m D₂) :
    IsDiffOpOfOrder φ m (add D₁ D₂) := by
  -- induction on m; needs `commutator g (add D₁ D₂) = add (commutator g D₁) (commutator g D₂)`
  -- and that `slice (add D₁ D₂) Y = add (slice D₁ Y) (slice D₂ Y)` (definitional).
  induction m generalizing F G U with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro Y Y' h s
      simp only [add_apply]
      rw [h₁.1 Y Y' h s, h₂.1 Y Y' h s, map_add]
    · intro Y r s
      simp only [add_apply]
      rw [h₁.2 Y r s, h₂.2 Y r s, smul_add]
  | succ n ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro Y Y' h s
      simp only [add_apply]
      rw [h₁.1 Y Y' h s, h₂.1 Y Y' h s, map_add]
    · intro Y a s
      simp only [add_apply]
      rw [h₁.2.1 Y a s, h₂.2.1 Y a s, smul_add]
    · intro Y g
      have comm_add :
          (commutator g fun Z => add D₁ D₂ (Over.mk (Z.hom ≫ Y.hom)))
          = add (commutator g (slice D₁ Y)) (commutator g (slice D₂ Y)) := by
        change commutator g (add (slice D₁ Y) (slice D₂ Y))
          = add (commutator g (slice D₁ Y)) (commutator g (slice D₂ Y))
        generalize slice D₁ Y = A
        generalize slice D₂ Y = B
        funext Z; ext s
        simp only [commutator, add, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          AddMonoidHom.add_apply, smul_add]
        abel
      rw [comm_add]
      exact ih (commutator g (slice D₁ Y)) (commutator g (slice D₂ Y))
        (h₁.2.2 Y g) (h₂.2.2 Y g)

end RawOp

/-- **S4 (Main raw lemma).** Composition of an order-`k` and an order-`k'` raw operator
(over the same base, slice-uniformly) is an order-`(k+k')` raw operator.

Proof by strong induction on `n = k + k'`.

* **Base `n = 0`** (`k = k' = 0`): `D, D'` are natural & `O₂`-linear, so `comp D' D` is
  natural (`IsNatural.comp`) and `O₂`-linear (`IsO2Linear.comp`), i.e. order 0.
* **Successor `n = m+1`**: `comp D' D` is natural (`IsNatural.comp`) and `O₁`-linear
  (`IsO1Linear.comp` applied to `isO1Linear_of_isDiffOpOfOrder` of `D` and `D'`). For
  the commutator clause, fix `Y` and `g`. By `slice_comp`,
  `slice (comp D' D) Y = comp (slice D' Y) (slice D Y)`; by `commutator_comp`,
  `[g, comp (slice D' Y) (slice D Y)] = comp (slice D' Y) [g, slice D Y]
     + [g, slice D' Y] ∘ (slice D Y)`.
  Now `slice D Y` has order `k` (slice of order-k is order-k — note `IsDiffOpOfOrder`'s
  successor clause already quantifies over slices, and order-0 is preserved by slicing),
  so `[g, slice D Y]` has order `k-1`; `slice D' Y` has order `k'`. Hence
  `comp (slice D' Y) [g, slice D Y]` has order `k' + (k-1) = m` by the IH (sum is
  `m = k+k'-1`). Symmetrically the second summand has order `(k'-1)+k = m`. By S5
  (`isDiffOpOfOrder_add`) their sum has order `m`, as required. Case `k=0` (resp.
  `k'=0`): `slice D Y` is order 0, so `[g, slice D Y] = 0`, and the first summand
  vanishes / is order anything; the order bookkeeping is handled by S1 (monotonicity)
  to align both summands at order `m`. -/
@[ega "IV 16.8.10" "more general",
  ega "IV 16.8.9" "more general",
  sga "3 VIIA 1.2" "special case",
  sga "3 VIIA 1.4" "partial",
  sga "6 II AppII.1.2.4" "more general"]
lemma isDiffOpOfOrder_comp_raw (φ : O₁ ⟶ O₂) :
    ∀ (n : ℕ) (k k' : ℕ), k + k' = n →
      ∀ {E F G : SheafOfModules O₂} {U : C}
        (D : RawOp E F U) (D' : RawOp F G U),
        IsDiffOpOfOrder φ k D → IsDiffOpOfOrder φ k' D' →
        IsDiffOpOfOrder φ (k + k') (RawOp.comp D' D) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro k k' hn E F G U D D' hD hD'
    -- Naturality and O₁-linearity of the composite (needed in every nonzero case).
    have hnat : (RawOp.comp D' D).IsNatural :=
      RawOp.IsNatural.comp (RawOp.isNatural_of_isDiffOpOfOrder φ k' D' hD')
        (RawOp.isNatural_of_isDiffOpOfOrder φ k D hD)
    have hO1 : (RawOp.comp D' D).IsO1Linear φ :=
      RawOp.IsO1Linear.comp φ (RawOp.isO1Linear_of_isDiffOpOfOrder φ k' D' hD')
        (RawOp.isO1Linear_of_isDiffOpOfOrder φ k D hD)
    -- The order of the composite is one more than the order of the summands of its commutators.
    have step : ∀ m, (∀ (Y : Over U) (g : O₂.obj.obj (op Y.left)), IsDiffOpOfOrder φ m
        (RawOp.add (RawOp.comp (RawOp.slice D' Y) (RawOp.commutator g (RawOp.slice D Y)))
          (RawOp.comp (RawOp.commutator g (RawOp.slice D' Y)) (RawOp.slice D Y)))) →
        IsDiffOpOfOrder φ (m + 1) (RawOp.comp D' D) := fun m h =>
      ⟨hnat, hO1, fun Y g => by
        have := h Y g
        rw [← RawOp.commutator_comp, ← RawOp.slice_comp] at this
        exact this⟩
    rcases k with _ | a
    · rcases k' with _ | b
      · -- (0, 0): order 0.
        exact ⟨RawOp.IsNatural.comp hD'.1 hD.1, RawOp.IsO2Linear.comp hD'.2 hD.2⟩
      · -- (0, b+1): goal order 0 + (b+1) = b+1.
        rw [Nat.zero_add]
        refine step b fun Y g => ?_
        have hsD := RawOp.isDiffOpOfOrder_slice φ 0 D hD Y
        refine RawOp.isDiffOpOfOrder_add φ b _ _
          (RawOp.isDiffOpOfOrder_of_forall_eq_zero φ b _ fun Z s => ?_) ?_
        · rw [RawOp.comp_apply, RawOp.commutator_apply_eq_zero hsD.2, map_zero]
        · simpa using IH b (by omega) 0 b (by omega) (RawOp.slice D Y)
            (RawOp.commutator g (RawOp.slice D' Y)) hsD (hD'.2.2 Y g)
    · rcases k' with _ | b
      · -- (a+1, 0): goal order (a+1) + 0 = a+1.
        refine step a fun Y g => ?_
        have hsD' := RawOp.isDiffOpOfOrder_slice φ 0 D' hD' Y
        refine RawOp.isDiffOpOfOrder_add φ a _ _ ?_
          (RawOp.isDiffOpOfOrder_of_forall_eq_zero φ a _ fun Z s => ?_)
        · simpa using IH a (by omega) a 0 (by omega) (RawOp.commutator g (RawOp.slice D Y))
            (RawOp.slice D' Y) (hD.2.2 Y g) hsD'
        · rw [RawOp.comp_apply]
          exact RawOp.commutator_apply_eq_zero hsD'.2 g _ _
      · -- (a+1, b+1): goal order (a+1) + (b+1).
        refine step ((a + 1) + b) fun Y g => ?_
        have hsD := RawOp.isDiffOpOfOrder_slice φ (a + 1) D hD Y
        have hsD' := RawOp.isDiffOpOfOrder_slice φ (b + 1) D' hD' Y
        have hfirst := IH ((b + 1) + a) (by omega) a (b + 1) (by omega)
          (RawOp.commutator g (RawOp.slice D Y)) (RawOp.slice D' Y) (hD.2.2 Y g) hsD'
        rw [show a + (b + 1) = (a + 1) + b by omega] at hfirst
        exact RawOp.isDiffOpOfOrder_add φ _ _ _ hfirst
          (IH (b + (a + 1)) (by omega) (a + 1) b (by omega) (RawOp.slice D Y)
            (RawOp.commutator g (RawOp.slice D' Y)) hsD (hD'.2.2 Y g))

-- Main Statement (Stacks Tag 09CS, Lemma 18.34.2)

/-- The composition of a differential operator of order `k` with a differential operator
of order `k'` is a differential operator of order `k + k'`.

The argument: `IsGlobalDiffOpOfOrder` is `∀ U, IsDiffOpOfOrder` on `restrict`; by
`GlobalOp.restrict_comp` the restriction of the composite is the raw composite of the
restrictions; then apply the raw composition lemma `isDiffOpOfOrder_comp_raw`
(strong induction on `k + k'` via the commutator-of-composition identity). -/
@[stacks 09CS,
  ega "IV 16.8.9" "more general",
  sga "3 VIIA 1.2" "sheaf, deviations of id",
  ega "IV 16.8.10" "more general",
  sga "3 VIIA 1.4" "partial",
  sga "6 II AppII.1.2.4" "more general"]
theorem isGlobalDiffOpOfOrder_comp (φ : O₁ ⟶ O₂)
    {E F G : SheafOfModules O₂} {k k' : ℕ}
    (D : GlobalOp E F) (D' : GlobalOp F G)
    (hD : IsGlobalDiffOpOfOrder φ k D) (hD' : IsGlobalDiffOpOfOrder φ k' D') :
    IsGlobalDiffOpOfOrder φ (k + k') (D'.comp D) := by
  intro U
  rw [GlobalOp.restrict_comp]
  exact isDiffOpOfOrder_comp_raw φ (k + k') k k' rfl (D.restrict U) (D'.restrict U)
    (hD U) (hD' U)

end DiffOp

