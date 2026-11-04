module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.StrictProLimit

/-!
# The morphisms of the strict pro-category are exactly its representatives

The strict pro-category `Stacks.LocalCohomology.StrictProCategory C` of Stacks 0GA5 is presented
by generators and relations: its morphisms are paths of `StrictProHomRep`s, modulo the relations
identifying a formal composite with the composite representative, a formal identity with the
identity representative, and two eventually-agreeing representatives with each other.  The
presentation was chosen because composition of representatives adds the shifts and so is
associative only up to the `eqToHom` of `Nat.add_assoc`.

This file shows that the presentation makes no further identifications: the quotient functor is
**full** — every morphism is `proHom` of a single representative — and **faithful** —
`proHom f = proHom g` exactly when `f` and `g` are `StrictProHomRep.Equivalent`.  Consequently
two inverse sequences are isomorphic in the strict pro-category *exactly* when there is a pair
of representatives whose two composites are equivalent to the identity representatives, which is
what makes a negative statement about the strict pro-category provable.

## Main results

* `Stacks.LocalCohomology.StrictProHomRep.Equivalent` is an equivalence relation
  (`Equivalent.refl`, `Equivalent.symm`, `Equivalent.trans`), and `StrictProHomRep.comp`
  respects it on both sides, is associative up to it, and has the identity representatives as
  units up to it.
* `Stacks.LocalCohomology.proHom_eq_iff`: **faithfulness** — `proHom f = proHom g ↔
  f.Equivalent g`.
* `Stacks.LocalCohomology.exists_proHom_eq`: **fullness** — every morphism of the strict
  pro-category is `proHom` of a representative.
* `Stacks.LocalCohomology.nonempty_iso_iff_exists_rep`: two inverse sequences are isomorphic in
  the strict pro-category if and only if there are representatives in both directions whose two
  composites are equivalent to the identity representatives.

## Implementation notes

Faithfulness is deduced from `CategoryTheory.Quotient.functor_map_eq_iff`, which says that
quotienting by a *congruence* makes no unnecessary identifications.  The relation
`Stacks.LocalCohomology.pathsEquivalent` on the path category — two paths are related when their
folded composite representatives are equivalent — is such a congruence, and it contains the
three generating relations, so the identity functor of the path category descends to a functor
from the strict pro-category to the quotient by `pathsEquivalent`.  Composing with that functor
turns an equality of `proHom`s into an equivalence of representatives.

All the manipulations below rest on one fact: `ℕᵒᵖ` is a preorder, so any two parallel arrows of
an inverse sequence have the same image (`inverseSequence_map_eq`).  Every structural map is
therefore written as `X.map (opHomOfLE h)` for an inequality proved by `omega`, and composites of
such maps collapse by `map_opHomOfLE_comp`.

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
-/

@[expose] public section

open CategoryTheory Opposite

namespace Stacks.LocalCohomology

universe v u

variable {C : Type u} [Category.{v} C]

/-! ## Structural maps of an inverse sequence -/

/-- Parallel arrows of an inverse sequence have the same image: `ℕᵒᵖ` is a preorder, so its hom
types are subsingletons. -/
public theorem inverseSequence_map_eq (X : Functor ℕᵒᵖ C) {m n : ℕᵒᵖ} (g g' : m ⟶ n) :
    X.map g = X.map g' :=
  congrArg X.map (Subsingleton.elim _ _)

/-- A structural map of an inverse sequence from a level to itself is the identity. -/
private theorem map_opHomOfLE_self (X : Functor ℕᵒᵖ C) {a : ℕ} (h : a ≤ a) :
    X.map (opHomOfLE h) = 𝟙 _ :=
  (inverseSequence_map_eq X _ (𝟙 (op a))).trans (X.map_id _)

/-- A composite of structural maps of an inverse sequence is a structural map. -/
public theorem map_opHomOfLE_comp' (X : Functor ℕᵒᵖ C) {a b c : ℕ} (hab : b ≤ a) (hbc : c ≤ b)
    (hac : c ≤ a) :
    X.map (opHomOfLE hab) ≫ X.map (opHomOfLE hbc) = X.map (opHomOfLE hac) := by
  rw [← X.map_comp]
  exact inverseSequence_map_eq X _ _

/-- `map_opHomOfLE_comp'`, in the form that applies inside a longer composite. -/
public theorem map_opHomOfLE_comp (X : Functor ℕᵒᵖ C) {a b c : ℕ} (hab : b ≤ a) (hbc : c ≤ b)
    (hac : c ≤ a) {Z : C} (k : X.obj (op c) ⟶ Z) :
    X.map (opHomOfLE hab) ≫ X.map (opHomOfLE hbc) ≫ k =
      X.map (opHomOfLE hac) ≫ k := by
  rw [← Category.assoc, map_opHomOfLE_comp' X hab hbc hac]

/-- The component of the transition between two shifts of an inverse sequence. -/
public theorem shiftedInverseSequenceTransition_app (X : Functor ℕᵒᵖ C) {c d : ℕ} (h : c ≤ d)
    (n : ℕ) :
    (shiftedInverseSequenceTransition X h).app (op n) =
      X.map (opHomOfLE (Nat.add_le_add_left h n)) := rfl

/-- The transition of an inverse sequence to its own shift is the identity. -/
public theorem shiftedInverseSequenceTransition_refl (X : Functor ℕᵒᵖ C) {c : ℕ} (h : c ≤ c)
    (n : ℕ) : (shiftedInverseSequenceTransition X h).app (op n) = 𝟙 _ := by
  rw [shiftedInverseSequenceTransition_app, map_opHomOfLE_self]
  rfl

/-- The structural maps of a shifted inverse sequence are structural maps of the sequence. -/
public theorem shiftedInverseSequence_map (X : Functor ℕᵒᵖ C) (c : ℕ) {m n : ℕ} (h : n ≤ m)
    (h' : n + c ≤ m + c) :
    (shiftedInverseSequence X c).map (opHomOfLE h) = X.map (opHomOfLE h') := by
  show X.map ((inverseSequenceShift c).map (opHomOfLE h)) = _
  exact inverseSequence_map_eq X _ _

namespace StrictProHomRep

variable {X Y Z W : Functor ℕᵒᵖ C}

/-- `Equivalent`, written with the structural maps of `X`. -/
public theorem equivalent_iff (f g : StrictProHomRep X Y) :
    f.Equivalent g ↔ ∃ (d N : ℕ) (hf : f.shift ≤ d) (hg : g.shift ≤ d), ∀ n, N ≤ n →
      X.map (opHomOfLE (Nat.add_le_add_left hf n)) ≫ f.hom.app (op n) =
        X.map (opHomOfLE (Nat.add_le_add_left hg n)) ≫ g.hom.app (op n) := Iff.rfl

/-- The component of a composite representative, written with the structural maps of `X`. -/
public theorem comp_hom_app (f : StrictProHomRep X Y) (g : StrictProHomRep Y Z) (n : ℕ) :
    (f.comp g).hom.app (op n) =
      X.map (opHomOfLE (le_of_eq (Nat.add_assoc n g.shift f.shift))) ≫
        f.hom.app (op (n + g.shift)) ≫ g.hom.app (op n) := by
  dsimp only [StrictProHomRep.comp]
  rw [inverseSequence_map_eq X (eqToHom (congrArg Opposite.op
    (Nat.add_assoc n g.shift f.shift).symm))
    (opHomOfLE (le_of_eq (Nat.add_assoc n g.shift f.shift)))]

/-- The shift of a composite representative. -/
@[simp]
public theorem comp_shift (f : StrictProHomRep X Y) (g : StrictProHomRep Y Z) :
    (f.comp g).shift = g.shift + f.shift := rfl

/-- The shift of the identity representative. -/
@[simp]
public theorem id_shift (X : Functor ℕᵒᵖ C) : (StrictProHomRep.id X).shift = 0 := rfl

/-- The component of the identity representative. -/
public theorem id_hom_app (X : Functor ℕᵒᵖ C) (n : ℕ) :
    (StrictProHomRep.id X).hom.app (op n) = 𝟙 _ := rfl

/-- **The component of a composite, cut after `f`.**  A composite representative preceded by a
structural map, rewritten with the component of `f` preceded by a structural map of `X`. -/
public theorem map_comp_hom_app (f : StrictProHomRep X Y) (g : StrictProHomRep Y Z)
    (n e b : ℕ) (he : n + (g.shift + f.shift) ≤ e) (hb : f.shift ≤ b)
    (hbe : n + g.shift + b ≤ e) :
    X.map (opHomOfLE he) ≫ (f.comp g).hom.app (op n) =
      X.map (opHomOfLE hbe) ≫
        (X.map (opHomOfLE (Nat.add_le_add_left hb (n + g.shift))) ≫
          f.hom.app (op (n + g.shift))) ≫ g.hom.app (op n) := by
  rw [comp_hom_app,
    map_opHomOfLE_comp X he (le_of_eq (Nat.add_assoc n g.shift f.shift))
      (show n + g.shift + f.shift ≤ e by omega),
    Category.assoc,
    map_opHomOfLE_comp X hbe (Nat.add_le_add_left hb (n + g.shift))
      (show n + g.shift + f.shift ≤ e by omega)]

/-- Naturality of a representative, written with the structural maps of `X` and `Y`. -/
private theorem map_hom_app_comm (f : StrictProHomRep X Y) {m n : ℕ} (h : n ≤ m)
    (h' : n + f.shift ≤ m + f.shift) :
    X.map (opHomOfLE h') ≫ f.hom.app (op n) = f.hom.app (op m) ≫ Y.map (opHomOfLE h) := by
  have hnat := f.hom.naturality (opHomOfLE h)
  rwa [shiftedInverseSequence_map X f.shift h h'] at hnat

/-- **The component of a composite, cut after `g`.**  A composite representative preceded by a
structural map, rewritten with the component of `g` preceded by a structural map of `Y`; the
component of `f` moves across by naturality. -/
public theorem map_comp_hom_app' (f : StrictProHomRep X Y) (g : StrictProHomRep Y Z)
    (n e b : ℕ) (he : n + (g.shift + f.shift) ≤ e) (hb : g.shift ≤ b)
    (hbe : n + b + f.shift ≤ e) :
    X.map (opHomOfLE he) ≫ (f.comp g).hom.app (op n) =
      X.map (opHomOfLE hbe) ≫ f.hom.app (op (n + b)) ≫
        Y.map (opHomOfLE (Nat.add_le_add_left hb n)) ≫ g.hom.app (op n) := by
  have hnat := map_hom_app_comm f (Nat.add_le_add_left hb n)
    (Nat.add_le_add_right (Nat.add_le_add_left hb n) f.shift)
  rw [comp_hom_app,
    map_opHomOfLE_comp X he (le_of_eq (Nat.add_assoc n g.shift f.shift))
      (show n + g.shift + f.shift ≤ e by omega),
    ← map_opHomOfLE_comp X hbe
      (Nat.add_le_add_right (Nat.add_le_add_left hb n) f.shift)
      (show n + g.shift + f.shift ≤ e by omega),
    ← Category.assoc (X.map (opHomOfLE (Nat.add_le_add_right
      (Nat.add_le_add_left hb n) f.shift))), hnat, Category.assoc]

/-- An equivalence of representatives witnessed at a shift `d` and from a level `N`. -/
public theorem equivalent_of_agree {f g : StrictProHomRep X Y} {d N : ℕ}
    (hf : f.shift ≤ d) (hg : g.shift ≤ d)
    (H : ∀ n, N ≤ n → X.map (opHomOfLE (Nat.add_le_add_left hf n)) ≫ f.hom.app (op n) =
      X.map (opHomOfLE (Nat.add_le_add_left hg n)) ≫ g.hom.app (op n)) :
    f.Equivalent g := ⟨d, N, hf, hg, H⟩

/-- The witnessing identity of `Equivalent` at a shift `d` holds at every larger shift `d'`. -/
public theorem agree_of_le {f g : StrictProHomRep X Y} {d N : ℕ}
    {hf : f.shift ≤ d} {hg : g.shift ≤ d}
    (H : ∀ n, N ≤ n → X.map (opHomOfLE (Nat.add_le_add_left hf n)) ≫ f.hom.app (op n) =
      X.map (opHomOfLE (Nat.add_le_add_left hg n)) ≫ g.hom.app (op n))
    {d' : ℕ} (hdd : d ≤ d') (hf' : f.shift ≤ d') (hg' : g.shift ≤ d') :
    ∀ n, N ≤ n → X.map (opHomOfLE (Nat.add_le_add_left hf' n)) ≫ f.hom.app (op n) =
      X.map (opHomOfLE (Nat.add_le_add_left hg' n)) ≫ g.hom.app (op n) := by
  intro n hn
  rw [← map_opHomOfLE_comp X (Nat.add_le_add_left hdd n) (Nat.add_le_add_left hf n)
      (Nat.add_le_add_left hf' n),
    ← map_opHomOfLE_comp X (Nat.add_le_add_left hdd n) (Nat.add_le_add_left hg n)
      (Nat.add_le_add_left hg' n),
    H n hn]

/-- `StrictProHomRep.Equivalent` is reflexive. -/
public theorem Equivalent.refl (f : StrictProHomRep X Y) : f.Equivalent f :=
  ⟨f.shift, 0, le_rfl, le_rfl, fun _ _ => rfl⟩

/-- `StrictProHomRep.Equivalent` is symmetric. -/
public theorem Equivalent.symm {f g : StrictProHomRep X Y} (h : f.Equivalent g) :
    g.Equivalent f := by
  obtain ⟨d, N, hf, hg, H⟩ := h
  exact ⟨d, N, hg, hf, fun n hn => (H n hn).symm⟩

/-- `StrictProHomRep.Equivalent` is transitive. -/
public theorem Equivalent.trans {f g k : StrictProHomRep X Y} (h : f.Equivalent g)
    (h' : g.Equivalent k) : f.Equivalent k := by
  obtain ⟨d₁, N₁, hf₁, hg₁, H₁⟩ := h
  obtain ⟨d₂, N₂, hg₂, hk₂, H₂⟩ := h'
  refine ⟨max d₁ d₂, max N₁ N₂, hf₁.trans (le_max_left _ _), hk₂.trans (le_max_right _ _),
    fun n hn => ?_⟩
  exact (agree_of_le (hf := hf₁) (hg := hg₁) H₁ (le_max_left d₁ d₂)
      (hf₁.trans (le_max_left _ _)) (hg₁.trans (le_max_left _ _)) n
      (le_trans (le_max_left _ _) hn)).trans
    (agree_of_le (hf := hg₂) (hg := hk₂) H₂ (le_max_right d₁ d₂)
      (hg₂.trans (le_max_right _ _)) (hk₂.trans (le_max_right _ _)) n
      (le_trans (le_max_right _ _) hn))

/-- `StrictProHomRep.Equivalent` is an equivalence relation. -/
public theorem equivalent_equivalence (X Y : Functor ℕᵒᵖ C) :
    _root_.Equivalence (fun f g : StrictProHomRep X Y => f.Equivalent g) :=
  ⟨Equivalent.refl, Equivalent.symm, Equivalent.trans⟩

/-! ### Composition respects the equivalence -/

/-- Composition of representatives respects the equivalence in the left argument. -/
public theorem comp_equivalent_comp_left {f f' : StrictProHomRep X Y} (g : StrictProHomRep Y Z)
    (h : f.Equivalent f') : (f.comp g).Equivalent (f'.comp g) := by
  obtain ⟨d, N, hf, hf', H⟩ := h
  have H' : ∀ m, N ≤ m →
      X.map (opHomOfLE (Nat.add_le_add_left hf m)) ≫ f.hom.app (op m) =
        X.map (opHomOfLE (Nat.add_le_add_left hf' m)) ≫ f'.hom.app (op m) := H
  refine equivalent_of_agree (d := g.shift + d)
    (show (f.comp g).shift ≤ g.shift + d from Nat.add_le_add_left hf g.shift)
    (show (f'.comp g).shift ≤ g.shift + d from Nat.add_le_add_left hf' g.shift)
    (N := N) (fun n hn => ?_)
  show X.map (opHomOfLE (show n + (g.shift + f.shift) ≤ n + (g.shift + d) by omega)) ≫
      (f.comp g).hom.app (op n) =
    X.map (opHomOfLE (show n + (g.shift + f'.shift) ≤ n + (g.shift + d) by omega)) ≫
      (f'.comp g).hom.app (op n)
  rw [map_comp_hom_app f g n (n + (g.shift + d)) d (by omega) hf (by omega),
    map_comp_hom_app f' g n (n + (g.shift + d)) d (by omega) hf' (by omega),
    H' (n + g.shift) (hn.trans (Nat.le_add_right n g.shift))]

/-- Composition of representatives respects the equivalence in the right argument. -/
public theorem comp_equivalent_comp_right (f : StrictProHomRep X Y)
    {g g' : StrictProHomRep Y Z} (h : g.Equivalent g') :
    (f.comp g).Equivalent (f.comp g') := by
  obtain ⟨d, N, hg, hg', H⟩ := h
  have H' : ∀ m, N ≤ m →
      Y.map (opHomOfLE (Nat.add_le_add_left hg m)) ≫ g.hom.app (op m) =
        Y.map (opHomOfLE (Nat.add_le_add_left hg' m)) ≫ g'.hom.app (op m) := H
  refine equivalent_of_agree (d := d + f.shift)
    (show (f.comp g).shift ≤ d + f.shift from Nat.add_le_add_right hg f.shift)
    (show (f.comp g').shift ≤ d + f.shift from Nat.add_le_add_right hg' f.shift)
    (N := N) (fun n hn => ?_)
  show X.map (opHomOfLE (show n + (g.shift + f.shift) ≤ n + (d + f.shift) by omega)) ≫
      (f.comp g).hom.app (op n) =
    X.map (opHomOfLE (show n + (g'.shift + f.shift) ≤ n + (d + f.shift) by omega)) ≫
      (f.comp g').hom.app (op n)
  rw [map_comp_hom_app' f g n (n + (d + f.shift)) d (by omega) hg (by omega),
    map_comp_hom_app' f g' n (n + (d + f.shift)) d (by omega) hg' (by omega),
    H' n hn]

/-! ### The identity representatives are units, and composition is associative -/

/-- The identity representative is a left unit up to equivalence. -/
public theorem id_comp_equivalent (g : StrictProHomRep X Y) :
    ((StrictProHomRep.id X).comp g).Equivalent g := by
  have hd : ((StrictProHomRep.id X).comp g).shift ≤ g.shift := Nat.le_refl _
  have hg : g.shift ≤ g.shift := Nat.le_refl _
  refine equivalent_of_agree (d := g.shift) hd hg (N := 0) (fun n _ => ?_)
  have he : n + (g.shift + (StrictProHomRep.id X).shift) ≤ n + g.shift := Nat.le_refl _
  have hb : (StrictProHomRep.id X).shift ≤ 0 := Nat.le_refl _
  have hbe : n + g.shift + 0 ≤ n + g.shift := Nat.le_refl _
  refine (map_comp_hom_app (StrictProHomRep.id X) g n (n + g.shift) 0 he hb hbe).trans ?_
  have h2 : X.map (opHomOfLE hbe) = 𝟙 _ := map_opHomOfLE_self X _
  have h3 : X.map (opHomOfLE (Nat.add_le_add_left hb (n + g.shift))) = 𝟙 _ :=
    map_opHomOfLE_self X _
  rw [h2, h3, id_hom_app]
  simp only [Nat.add_zero, id_shift, Category.id_comp]
  exact Category.id_comp (g.hom.app (op n))

/-- The identity representative is a right unit up to equivalence. -/
public theorem comp_id_equivalent (f : StrictProHomRep X Y) :
    (f.comp (StrictProHomRep.id Y)).Equivalent f := by
  have hd : (f.comp (StrictProHomRep.id Y)).shift ≤ f.shift :=
    Nat.le_of_eq (Nat.zero_add f.shift)
  have hf : f.shift ≤ f.shift := Nat.le_refl _
  refine equivalent_of_agree (d := f.shift) hd hf (N := 0) (fun n _ => ?_)
  have he : n + ((StrictProHomRep.id Y).shift + f.shift) ≤ n + f.shift :=
    Nat.le_of_eq (congrArg (fun k => n + k) (Nat.zero_add f.shift))
  have hb : f.shift ≤ f.shift := Nat.le_refl _
  have hbe : n + (StrictProHomRep.id Y).shift + f.shift ≤ n + f.shift := Nat.le_refl _
  refine (map_comp_hom_app f (StrictProHomRep.id Y) n (n + f.shift) f.shift he hb hbe).trans ?_
  have h2 : X.map (opHomOfLE hbe) = 𝟙 _ := map_opHomOfLE_self X _
  have h3 : X.map (opHomOfLE (Nat.add_le_add_left hb (n + (StrictProHomRep.id Y).shift)))
      = 𝟙 _ := map_opHomOfLE_self X _
  have h4 : X.map (opHomOfLE (Nat.add_le_add_left hf n)) = 𝟙 _ := map_opHomOfLE_self X _
  rw [h2, h3, h4, id_hom_app]
  simp only [id_shift, Nat.add_zero, Category.id_comp]
  exact Category.comp_id (f.hom.app (op n))

/-- A triple composite, bracketed to the left, reduced to a normal form. -/
public theorem map_comp3 (f : StrictProHomRep X Y) (g : StrictProHomRep Y Z)
    (h : StrictProHomRep Z W) (n e : ℕ)
    (he : n + (h.shift + (g.shift + f.shift)) ≤ e) :
    X.map (opHomOfLE he) ≫ ((f.comp g).comp h).hom.app (op n) =
      X.map (opHomOfLE (show n + h.shift + g.shift + f.shift ≤ e by omega)) ≫
        f.hom.app (op (n + h.shift + g.shift)) ≫ g.hom.app (op (n + h.shift)) ≫
          h.hom.app (op n) := by
  have hb : (f.comp g).shift ≤ g.shift + f.shift := Nat.le_refl _
  have hbe : n + h.shift + (g.shift + f.shift) ≤ e := by omega
  have hm : n + h.shift + g.shift + f.shift ≤ n + h.shift + (g.shift + f.shift) := by omega
  have hrfl : n + h.shift + (g.shift + f.shift) ≤ n + h.shift + (g.shift + f.shift) :=
    Nat.le_refl _
  refine (map_comp_hom_app (f.comp g) h n e (g.shift + f.shift) he hb hbe).trans ?_
  show X.map (opHomOfLE hbe) ≫ (X.map (opHomOfLE hrfl) ≫
      (f.comp g).hom.app (op (n + h.shift))) ≫ h.hom.app (op n) = _
  rw [comp_hom_app f g (n + h.shift)]
  simp only [Category.assoc]
  rw [map_opHomOfLE_comp X hrfl (le_of_eq (Nat.add_assoc (n + h.shift) g.shift f.shift)) hm,
    map_opHomOfLE_comp X hbe hm (show n + h.shift + g.shift + f.shift ≤ e by omega)]

/-- A triple composite, bracketed to the right, reduced to the same normal form. -/
public theorem map_comp3' (f : StrictProHomRep X Y) (g : StrictProHomRep Y Z)
    (h : StrictProHomRep Z W) (n e : ℕ)
    (he : n + (h.shift + g.shift + f.shift) ≤ e) :
    X.map (opHomOfLE he) ≫ (f.comp (g.comp h)).hom.app (op n) =
      X.map (opHomOfLE (show n + h.shift + g.shift + f.shift ≤ e by omega)) ≫
        f.hom.app (op (n + h.shift + g.shift)) ≫ g.hom.app (op (n + h.shift)) ≫
          h.hom.app (op n) := by
  have hbe : n + (h.shift + g.shift) + f.shift ≤ e := by omega
  have hmg : n + h.shift + g.shift ≤ n + (h.shift + g.shift) := by omega
  have hmgf : n + h.shift + g.shift + f.shift ≤ n + (h.shift + g.shift) + f.shift := by omega
  have hYrfl : n + (h.shift + g.shift) ≤ n + (h.shift + g.shift) := Nat.le_refl _
  have hnat := map_hom_app_comm f hmg hmgf
  refine (map_comp_hom_app' f (g.comp h) n e (h.shift + g.shift) he le_rfl hbe).trans ?_
  show X.map (opHomOfLE hbe) ≫ f.hom.app (op (n + (h.shift + g.shift))) ≫
      Y.map (opHomOfLE hYrfl) ≫ (g.comp h).hom.app (op n) = _
  rw [comp_hom_app g h n,
    map_opHomOfLE_comp Y hYrfl (le_of_eq (Nat.add_assoc n h.shift g.shift)) hmg,
    ← Category.assoc (f.hom.app (op (n + (h.shift + g.shift)))), ← hnat]
  simp only [Category.assoc]
  rw [map_opHomOfLE_comp X hbe hmgf (show n + h.shift + g.shift + f.shift ≤ e by omega)]

/-- Composition of representatives is associative up to equivalence. -/
public theorem comp_assoc_equivalent (f : StrictProHomRep X Y) (g : StrictProHomRep Y Z)
    (h : StrictProHomRep Z W) :
    ((f.comp g).comp h).Equivalent (f.comp (g.comp h)) := by
  refine equivalent_of_agree (d := h.shift + (g.shift + f.shift))
    (show ((f.comp g).comp h).shift ≤ h.shift + (g.shift + f.shift) from Nat.le_refl _)
    (show (f.comp (g.comp h)).shift ≤ h.shift + (g.shift + f.shift) from
      Nat.le_of_eq (Nat.add_assoc h.shift g.shift f.shift))
    (N := 0) (fun n _ => ?_)
  exact (map_comp3 f g h n (n + (h.shift + (g.shift + f.shift))) (by omega)).trans
    (map_comp3' f g h n (n + (h.shift + (g.shift + f.shift))) (by omega)).symm

end StrictProHomRep

/-! ## Folding a path of representatives -/

/-- The composite representative of a path of representatives. -/
public def normalize {X Y : strictProQuiver C} (p : Quiver.Path X Y) : StrictProHomRep X Y :=
  Quiver.Path.rec (motive := fun {Y} _ => StrictProHomRep X Y) (StrictProHomRep.id X)
    (fun _ e ih => StrictProHomRep.comp ih e) p

/-- Folding the empty path gives the identity representative. -/
@[simp]
public theorem normalize_nil (X : strictProQuiver C) :
    normalize (Quiver.Path.nil (a := X)) = StrictProHomRep.id X := rfl

/-- Folding a path extended by one arrow composes the fold with that arrow. -/
@[simp]
public theorem normalize_cons {X Y Z : strictProQuiver C} (q : Quiver.Path X Y) (e : Y ⟶ Z) :
    normalize (q.cons e) = StrictProHomRep.comp (normalize q) e := rfl

/-- Folding the one-arrow path of a representative returns that representative, up to
equivalence. -/
public theorem normalize_toPath_equivalent {X Y : strictProQuiver C} (f : X ⟶ Y) :
    (normalize (Quiver.Hom.toPath f)).Equivalent f :=
  StrictProHomRep.id_comp_equivalent f

/-- Folding a concatenation of paths is the composite of the two folds, up to equivalence. -/
public theorem normalize_comp_equivalent {X Y Z : strictProQuiver C} (p : Quiver.Path X Y)
    (q : Quiver.Path Y Z) :
    (normalize (p.comp q)).Equivalent (StrictProHomRep.comp (normalize p) (normalize q)) := by
  induction q with
  | nil => exact (StrictProHomRep.comp_id_equivalent (normalize p)).symm
  | cons q e ih =>
    exact (StrictProHomRep.comp_equivalent_comp_left e ih).trans
      (StrictProHomRep.comp_assoc_equivalent (normalize p) (normalize q) e)

/-! ## The congruence generated by the equivalence of representatives -/

/-- Two paths of representatives are related when their folded composites are equivalent. -/
public def pathsEquivalent : HomRel (CategoryTheory.Paths (strictProQuiver C)) :=
  fun _ _ p q => (normalize p).Equivalent (normalize q)

/-- `pathsEquivalent` is stable under precomposition. -/
public instance : HomRel.IsStableUnderPrecomp (pathsEquivalent (C := C)) where
  comp_left := by
    intro _ _ _ p q q' hq
    exact ((normalize_comp_equivalent p q).trans
        (StrictProHomRep.comp_equivalent_comp_right (normalize p) hq)).trans
      (normalize_comp_equivalent p q').symm

/-- `pathsEquivalent` is stable under postcomposition. -/
public instance : HomRel.IsStableUnderPostcomp (pathsEquivalent (C := C)) where
  comp_right := by
    intro _ _ _ p p' q hp
    exact ((normalize_comp_equivalent p q).trans
        (StrictProHomRep.comp_equivalent_comp_left (normalize q) hp)).trans
      (normalize_comp_equivalent p' q).symm

/-- `pathsEquivalent` is a congruence on the path category. -/
public instance : Congruence (pathsEquivalent (C := C)) where
  equivalence :=
    ⟨fun p => StrictProHomRep.Equivalent.refl (normalize p),
      fun h => StrictProHomRep.Equivalent.symm h,
      fun h h' => StrictProHomRep.Equivalent.trans h h'⟩

/-- The presenting relations of the strict pro-category are contained in `pathsEquivalent`. -/
public theorem strictProRelations_le_pathsEquivalent
    {X Y : CategoryTheory.Paths (strictProQuiver C)} {p q : X ⟶ Y}
    (h : strictProRelations p q) : pathsEquivalent p q := by
  cases h with
  | id Z => exact (normalize_toPath_equivalent (StrictProHomRep.id Z)).symm
  | comp f g =>
    refine (normalize_comp_equivalent (Quiver.Hom.toPath f) (Quiver.Hom.toPath g)).trans ?_
    refine StrictProHomRep.Equivalent.trans ?_
      (normalize_toPath_equivalent (StrictProHomRep.comp f g)).symm
    exact (StrictProHomRep.comp_equivalent_comp_left _ (normalize_toPath_equivalent f)).trans
      (StrictProHomRep.comp_equivalent_comp_right f (normalize_toPath_equivalent g))
  | equivalent f g hfg =>
    exact ((normalize_toPath_equivalent f).trans hfg).trans
      (normalize_toPath_equivalent g).symm

/-- The comparison from the strict pro-category to the quotient of the path category by
`pathsEquivalent`.  It exists because the presenting relations are contained in
`pathsEquivalent`, and it is what makes the presentation faithful. -/
public def toPathsQuotient :
    StrictProCategory C ⥤ CategoryTheory.Quotient (pathsEquivalent (C := C)) :=
  CategoryTheory.Quotient.lift _ (CategoryTheory.Quotient.functor _)
    (fun _ _ _ _ h => CategoryTheory.Quotient.sound _ (strictProRelations_le_pathsEquivalent h))

/-! ## Fullness and faithfulness -/

/-- **Faithfulness of the presentation.**  Two representatives give the same morphism of the
strict pro-category exactly when they are equivalent. -/
public theorem proHom_eq_iff {X Y : Functor ℕᵒᵖ C} (f g : StrictProHomRep X Y) :
    proHom f = proHom g ↔ f.Equivalent g := by
  refine ⟨fun h => ?_, proHom_eq_of_equivalent⟩
  have hrel : pathsEquivalent (Quiver.Hom.toPath f) (Quiver.Hom.toPath g) :=
    (CategoryTheory.Quotient.functor_map_eq_iff (pathsEquivalent (C := C)) _ _).1
      (congrArg (toPathsQuotient (C := C)).map h)
  exact ((normalize_toPath_equivalent f).symm.trans hrel).trans
    (normalize_toPath_equivalent g)

/-- The quotient functor sends a path to the morphism of its folded representative. -/
public theorem functor_map_eq_proHom_normalize {X Y : strictProQuiver C}
    (p : Quiver.Path X Y) :
    (CategoryTheory.Quotient.functor (strictProRelations (C := C))).map p =
      proHom (normalize p) := by
  induction p with
  | nil => exact (proHom_id X).symm
  | cons q e ih =>
    exact (congrArg (fun k => k ≫ proHom e) ih).trans (proHom_comp (normalize q) e)

/-- **Fullness of the presentation.**  Every morphism of the strict pro-category is represented
by a single representative. -/
public theorem exists_proHom_eq {X Y : Functor ℕᵒᵖ C} (φ : proObj X ⟶ proObj Y) :
    ∃ f : StrictProHomRep X Y, φ = proHom f := by
  refine Quot.inductionOn (motive := fun ψ => ∃ f : StrictProHomRep X Y, ψ = proHom f) φ ?_
  intro p
  exact ⟨normalize p, functor_map_eq_proHom_normalize p⟩

/-- **Isomorphism in the strict pro-category is interleaving of representatives.**  Two inverse
sequences are isomorphic in the strict pro-category exactly when there are representatives in
both directions whose two composites are equivalent to the identity representatives. -/
public theorem nonempty_iso_iff_exists_rep {X Y : Functor ℕᵒᵖ C} :
    Nonempty (proObj X ≅ proObj Y) ↔
      ∃ (f : StrictProHomRep X Y) (g : StrictProHomRep Y X),
        (f.comp g).Equivalent (StrictProHomRep.id X) ∧
          (g.comp f).Equivalent (StrictProHomRep.id Y) := by
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨f, g, hfg, hgf⟩ => ⟨⟨proHom f, proHom g, ?_, ?_⟩⟩⟩
  · obtain ⟨f, hf⟩ := exists_proHom_eq e.hom
    obtain ⟨g, hg⟩ := exists_proHom_eq e.inv
    refine ⟨f, g, (proHom_eq_iff _ _).1 ?_, (proHom_eq_iff _ _).1 ?_⟩
    · rw [← proHom_comp, ← hf, ← hg, e.hom_inv_id, proHom_id]
    · rw [← proHom_comp, ← hf, ← hg, e.inv_hom_id, proHom_id]
  · rw [proHom_comp, proHom_eq_of_equivalent hfg, proHom_id]
  · rw [proHom_comp, proHom_eq_of_equivalent hgf, proHom_id]

end Stacks.LocalCohomology

end
