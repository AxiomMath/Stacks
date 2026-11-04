module


public import StacksFrontier.Topology.Sheaves.Presheaf.Terminal
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Four descriptions of an abelian group structure on a presheaf of sets

Let `X` be a topological space and `P` a presheaf of sets on `X`.  Stacks Tag 006J lists
four kinds of structure one may put on `P` to make it an abelian presheaf:

1. an abelian group structure on every `P(U)` for which all restriction maps are group
   homomorphisms;
2. maps of presheaves `+ : P × P ⟶ P`, `- : P ⟶ P` and `0 : * ⟶ P` satisfying the axioms
   of an abelian group;
3. the same three maps, subject instead to the requirement that every quadruple
   `(P(U), +, -, 0)` be an abelian group;
4. only a map of presheaves `+ : P × P ⟶ P`, such that every `(P(U), +)` is an abelian
   group.

Here `P × P` is `selfProd P` (certified to be the categorical product by
`selfProdIsLimit`) and `*` is `singletonPresheaf X` (certified terminal in Tag 006H).
The four are in bijection; the content is that the zero and the negation are determined by
the addition, and that their naturality is automatic.

Being an abelian group is expressed by Mathlib's `AddCommGroup`; since the group structure
is determined by its addition (`AddCommGroup.ext`) this loses nothing, and it makes the
bijection with (1) — where the group structures are the data — provable rather than
assumed.

## Main results

* `SectionwiseGroup`, `AddNegZeroAxioms`, `AddNegZeroGroup`, `AdditionGroup`: the four
  types of structure, in the order above.
* `addNegZeroAxiomsEquivAddNegZeroGroup`, `addNegZeroGroupEquivAdditionGroup`,
  `additionGroupEquivSectionwiseGroup`: Stacks Tag 006J, the natural bijections between
  them.

Supporting constructions:

* `selfProd`, `selfProdIsLimit`: the product presheaf `P × P`.
* `AdditionGroup.group`, `AdditionGroup.negMap`, `AdditionGroup.zeroMap`: the group
  structure, the negation and the zero recovered from the addition alone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w

namespace TopCat.Presheaf

variable {X : TopCat.{w}}

/-! ### The product presheaf `P × P` -/

/-- The product `P × P` of a presheaf of sets with itself: `U ↦ P(U) × P(U)`, with
restriction acting componentwise. -/
def selfProd (P : TopCat.Presheaf (Type u) X) : TopCat.Presheaf (Type u) X where
  obj U := P.obj U × P.obj U
  map i := ↾(Prod.map (P.map i) (P.map i))
  map_id _ := by ext s <;> simp
  map_comp _ _ := by ext s <;> simp

/-- Restriction in `P × P` is componentwise: it restricts each entry of a pair of sections. -/
@[simp] lemma selfProd_map_apply (P : TopCat.Presheaf (Type u) X) {U V : (Opens X)ᵒᵖ}
    (i : U ⟶ V) (s : (selfProd P).obj U) :
    (selfProd P).map i s = (P.map i s.1, P.map i s.2) := rfl

/-- The first projection `P × P ⟶ P`. -/
def selfProdFst (P : TopCat.Presheaf (Type u) X) : selfProd P ⟶ P where
  app _ := ↾Prod.fst
  naturality _ _ _ := rfl

/-- The second projection `P × P ⟶ P`. -/
def selfProdSnd (P : TopCat.Presheaf (Type u) X) : selfProd P ⟶ P where
  app _ := ↾Prod.snd
  naturality _ _ _ := rfl

/-- `selfProd P` really is the categorical product of `P` with itself in the category of
presheaves of sets, so that a "map of presheaves `P × P → P`" is a morphism out of it. -/
def selfProdIsLimit (P : TopCat.Presheaf (Type u) X) :
    IsLimit (BinaryFan.mk (selfProdFst P) (selfProdSnd P)) :=
  BinaryFan.isLimitMk
    (fun s => { app := fun U => ↾fun x => (s.fst.app U x, s.snd.app U x)
                naturality := fun _ _ i => by
                  ext x
                  refine Prod.ext ?_ ?_
                  · exact NatTrans.naturality_apply s.fst i x
                  · exact NatTrans.naturality_apply s.snd i x })
    (fun _ => rfl) (fun _ => rfl)
    (fun s m h₁ h₂ => by
      refine NatTrans.ext (funext fun U => ConcreteCategory.coe_ext (funext fun x => ?_))
      refine Prod.ext ?_ ?_
      · exact congrFun (congrArg (fun t : s.pt ⟶ P => ⇑(t.app U)) h₁) x
      · exact congrFun (congrArg (fun t : s.pt ⟶ P => ⇑(t.app U)) h₂) x)

variable (P : TopCat.Presheaf (Type u) X)

/-! ### The four types of structure -/

/-- Structure of type (1): an abelian group structure on `P(U)` for every open `U`, such
that all restriction maps are additive — equivalently, group homomorphisms, since a map of
abelian groups preserving addition preserves the zero and the negation. -/
@[sga "3 I 2.1.1" "special case"]
structure SectionwiseGroup where
  /-- The abelian group structure on the sections over each open. -/
  group : ∀ U : (Opens X)ᵒᵖ, AddCommGroup (P.obj U)
  /-- Restriction maps are additive. -/
  map_add : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s t : P.obj U),
    letI := group U; letI := group V; P.map i (s + t) = P.map i s + P.map i t

/-- Structure of type (2): maps of presheaves `+ : P × P ⟶ P`, `- : P ⟶ P` and
`0 : * ⟶ P` satisfying the axioms of an abelian group.  Equations between maps of
presheaves are equations between their values on sections, so the axioms are stated that
way; that this axiom list is exactly "the axioms of an abelian group" is the content of
`addNegZeroAxiomsEquivAddNegZeroGroup`. -/
structure AddNegZeroAxioms where
  /-- The addition, as a map of presheaves `P × P ⟶ P`. -/
  add : selfProd P ⟶ P
  /-- The negation, as a map of presheaves `P ⟶ P`. -/
  neg : P ⟶ P
  /-- The zero, as a map of presheaves `* ⟶ P` from the singleton presheaf. -/
  zero : singletonPresheaf.{u} X ⟶ P
  add_assoc : ∀ (U : (Opens X)ᵒᵖ) (s t v : P.obj U),
    add.app U (add.app U (s, t), v) = add.app U (s, add.app U (t, v))
  add_comm : ∀ (U : (Opens X)ᵒᵖ) (s t : P.obj U), add.app U (s, t) = add.app U (t, s)
  zero_add : ∀ (U : (Opens X)ᵒᵖ) (s : P.obj U), add.app U (zero.app U PUnit.unit, s) = s
  neg_add_cancel : ∀ (U : (Opens X)ᵒᵖ) (s : P.obj U),
    add.app U (neg.app U s, s) = zero.app U PUnit.unit

/-- Structure of type (3): maps of presheaves `+`, `-`, `0` such that for every open `U`
the quadruple `(P(U), +, -, 0)` is an abelian group. -/
structure AddNegZeroGroup where
  /-- The addition, as a map of presheaves `P × P ⟶ P`. -/
  add : selfProd P ⟶ P
  /-- The negation, as a map of presheaves `P ⟶ P`. -/
  neg : P ⟶ P
  /-- The zero, as a map of presheaves `* ⟶ P` from the singleton presheaf. -/
  zero : singletonPresheaf.{u} X ⟶ P
  /-- Each quadruple `(P(U), +, -, 0)` is an abelian group. -/
  isAddCommGroup : ∀ U : (Opens X)ᵒᵖ, ∃ G : AddCommGroup (P.obj U), letI := G;
    (∀ s t : P.obj U, s + t = add.app U (s, t)) ∧ (∀ s : P.obj U, -s = neg.app U s) ∧
      (0 : P.obj U) = zero.app U PUnit.unit

/-- Structure of type (4): a map of presheaves `+ : P × P ⟶ P` such that for every open `U`
the map `+ : P(U) × P(U) → P(U)` defines the structure of an abelian group. -/
structure AdditionGroup where
  /-- The addition, as a map of presheaves `P × P ⟶ P`. -/
  add : selfProd P ⟶ P
  /-- Each `(P(U), +)` is an abelian group. -/
  isAddCommGroup : ∀ U : (Opens X)ᵒᵖ, ∃ G : AddCommGroup (P.obj U), letI := G;
    ∀ s t : P.obj U, s + t = add.app U (s, t)

/-- Two structures of type (1) with the same group structures are equal. -/
lemma SectionwiseGroup.ext' {G H : SectionwiseGroup P} (h : G.group = H.group) : G = H := by
  cases G with | mk g hg => cases H with | mk g' hg' => subst h; rfl

/-- Two structures of type (4) with the same addition are equal. -/
lemma AdditionGroup.ext' {S T : AdditionGroup P} (h : S.add = T.add) : S = T := by
  cases S with | mk a ha => cases T with | mk a' ha' => subst h; rfl

/-! ### From the axioms to the group structures, and back -/

/-- The abelian group axioms for `+`, `-`, `0` assemble into an `AddCommGroup` on every
`P(U)`: structure (2) gives structure (3). -/
def AddNegZeroAxioms.toAddNegZeroGroup (S : AddNegZeroAxioms P) : AddNegZeroGroup P where
  add := S.add
  neg := S.neg
  zero := S.zero
  isAddCommGroup U := by
    let : Add (P.obj U) := ⟨fun s t => S.add.app U (s, t)⟩
    let : Neg (P.obj U) := ⟨fun s => S.neg.app U s⟩
    let : Zero (P.obj U) := ⟨S.zero.app U PUnit.unit⟩
    let : AddGroup (P.obj U) :=
      AddGroup.ofLeftAxioms (S.add_assoc U) (S.zero_add U) (S.neg_add_cancel U)
    exact ⟨{ add_comm := S.add_comm U }, fun _ _ => rfl, fun _ => rfl, rfl⟩

/-- Reading the abelian group axioms off the sectionwise group structures: structure (3)
gives structure (2). -/
def AddNegZeroGroup.toAddNegZeroAxioms (T : AddNegZeroGroup P) : AddNegZeroAxioms P where
  add := T.add
  neg := T.neg
  zero := T.zero
  add_assoc U s t v := by
    obtain ⟨G, h₁, -, -⟩ := T.isAddCommGroup U
    let := G
    rw [← h₁, ← h₁, ← h₁, ← h₁, add_assoc]
  add_comm U s t := by
    obtain ⟨G, h₁, -, -⟩ := T.isAddCommGroup U
    let := G
    rw [← h₁, ← h₁, add_comm]
  zero_add U s := by
    obtain ⟨G, h₁, -, h₃⟩ := T.isAddCommGroup U
    let := G
    rw [← h₁, ← h₃, zero_add]
  neg_add_cancel U s := by
    obtain ⟨G, h₁, h₂, h₃⟩ := T.isAddCommGroup U
    let := G
    rw [← h₁, ← h₂, ← h₃, neg_add_cancel]

/-- **Stacks Tag 006J**, the bijection between structures of type (2) and type (3): the
abelian group axioms for the maps of presheaves `+`, `-`, `0` say exactly that every
quadruple `(P(U), +, -, 0)` is an abelian group. -/
@[stacks 006J]
def addNegZeroAxiomsEquivAddNegZeroGroup : AddNegZeroAxioms P ≃ AddNegZeroGroup P where
  toFun := AddNegZeroAxioms.toAddNegZeroGroup P
  invFun := AddNegZeroGroup.toAddNegZeroAxioms P
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Recovering the zero and the negation from the addition -/

namespace AdditionGroup

variable {P}

/-- The abelian group structure on `P(U)` determined by the addition map. -/
@[instance_reducible]
noncomputable def group (S : AdditionGroup P) (U : (Opens X)ᵒᵖ) : AddCommGroup (P.obj U) :=
  (S.isAddCommGroup U).choose

/-- The addition of the group structure `S.group U` is the given map of presheaves, read on
sections over `U`. -/
lemma group_add (S : AdditionGroup P) (U : (Opens X)ᵒᵖ) (s t : P.obj U) :
    letI := S.group U; s + t = S.add.app U (s, t) :=
  (S.isAddCommGroup U).choose_spec s t

/-- The group structure of `S.group U` is the only abelian group structure on `P(U)` whose
addition is the given one. -/
lemma group_eq (S : AdditionGroup P) (U : (Opens X)ᵒᵖ) (G : AddCommGroup (P.obj U))
    (h : ∀ s t : P.obj U, letI := G; s + t = S.add.app U (s, t)) : G = S.group U :=
  AddCommGroup.ext (funext fun s => funext fun t => (h s t).trans (S.group_add U s t).symm)

/-- Naturality of the addition says precisely that the restriction maps are additive. -/
lemma map_add (S : AdditionGroup P) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s t : P.obj U) :
    letI := S.group U; letI := S.group V; P.map i (s + t) = P.map i s + P.map i t := by
  rw [S.group_add U s t, S.group_add V (P.map i s) (P.map i t)]
  exact (NatTrans.naturality_apply S.add i ((s, t) : (selfProd P).obj U)).symm

/-- The restriction maps, packaged as homomorphisms of abelian groups. -/
noncomputable def restrictionHom (S : AdditionGroup P) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    letI := S.group U; letI := S.group V; P.obj U →+ P.obj V :=
  letI := S.group U; letI := S.group V
  AddMonoidHom.mk' (fun s => P.map i s) (S.map_add i)

/-- The restriction maps send the zero section to the zero section: this is the naturality of
the zero, and it is a consequence of the additivity of restriction. -/
lemma map_zero (S : AdditionGroup P) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    letI := S.group U; letI := S.group V; P.map i (0 : P.obj U) = 0 := by
  let := S.group U; let := S.group V
  exact (S.restrictionHom i).map_zero

/-- The restriction maps commute with negation: this is the naturality of the negation, and it
is a consequence of the additivity of restriction. -/
lemma map_neg (S : AdditionGroup P) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s : P.obj U) :
    letI := S.group U; letI := S.group V; P.map i (-s) = -P.map i s := by
  let := S.group U; let := S.group V
  exact (S.restrictionHom i).map_neg s

/-- The negation is automatically a map of presheaves: its naturality is
`AdditionGroup.map_neg`. -/
noncomputable def negMap (S : AdditionGroup P) : P ⟶ P where
  app U := ↾fun s => letI := S.group U; -s
  naturality _ _ i := ConcreteCategory.coe_ext (funext fun s => (S.map_neg i s).symm)

/-- The zero is automatically a map of presheaves `* ⟶ P`: its naturality is
`AdditionGroup.map_zero`. -/
noncomputable def zeroMap (S : AdditionGroup P) : singletonPresheaf.{u} X ⟶ P where
  app U := ↾fun _ => letI := S.group U; (0 : P.obj U)
  naturality _ _ i := ConcreteCategory.coe_ext (funext fun _ => (S.map_zero i).symm)

/-- Structure (4) gives structure (3), adjoining the negation and zero it determines. -/
noncomputable def toAddNegZeroGroup (S : AdditionGroup P) : AddNegZeroGroup P where
  add := S.add
  neg := S.negMap
  zero := S.zeroMap
  isAddCommGroup U := ⟨S.group U, S.group_add U, fun _ => rfl, rfl⟩

/-- Structure (4) gives structure (1). -/
noncomputable def toSectionwiseGroup (S : AdditionGroup P) : SectionwiseGroup P where
  group := S.group
  map_add := S.map_add

end AdditionGroup

/-- Structure (3) gives structure (4), forgetting the negation and the zero. -/
def AddNegZeroGroup.toAdditionGroup (T : AddNegZeroGroup P) : AdditionGroup P where
  add := T.add
  isAddCommGroup U := by
    obtain ⟨G, h₁, -, -⟩ := T.isAddCommGroup U
    exact ⟨G, h₁⟩

/-- Structure (1) gives structure (4): the sectionwise additions form a map of presheaves
because the restriction maps are additive. -/
def SectionwiseGroup.toAdditionGroup (G : SectionwiseGroup P) : AdditionGroup P where
  add :=
    { app := fun U => ↾fun x => letI := G.group U; x.1 + x.2
      naturality := fun _ _ i =>
        ConcreteCategory.coe_ext (funext fun x => (G.map_add i x.1 x.2).symm) }
  isAddCommGroup U := ⟨G.group U, fun _ _ => rfl⟩

/-- **Stacks Tag 006J**, the bijection between structures of type (3) and type (4): the
negation and the zero are determined by the addition, and are automatically maps of
presheaves. -/
@[stacks 006J]
noncomputable def addNegZeroGroupEquivAdditionGroup :
    AddNegZeroGroup P ≃ AdditionGroup P where
  toFun := AddNegZeroGroup.toAdditionGroup P
  invFun := AdditionGroup.toAddNegZeroGroup
  left_inv T := by
    set S := AddNegZeroGroup.toAdditionGroup P T with hS
    have hneg : S.negMap = T.neg := by
      refine NatTrans.ext (funext fun U => ConcreteCategory.coe_ext (funext fun s => ?_))
      obtain ⟨G, h₁, h₂, -⟩ := T.isAddCommGroup U
      have hG : G = S.group U := S.group_eq U G h₁
      subst hG
      exact h₂ s
    have hzero : S.zeroMap = T.zero := by
      refine NatTrans.ext (funext fun U => ConcreteCategory.coe_ext (funext fun _ => ?_))
      obtain ⟨G, h₁, -, h₃⟩ := T.isAddCommGroup U
      have hG : G = S.group U := S.group_eq U G h₁
      subst hG
      exact h₃
    cases T with
    | mk add neg zero h =>
        simp only [AdditionGroup.toAddNegZeroGroup]
        congr 1
  right_inv _ := rfl

/-- **Stacks Tag 006J**, the bijection between structures of type (4) and type (1): an
abelian group structure on each `P(U)` with additive restrictions is the same thing as a
map of presheaves `+ : P × P ⟶ P` making each `P(U)` an abelian group. -/
@[stacks 006J]
noncomputable def additionGroupEquivSectionwiseGroup :
    AdditionGroup P ≃ SectionwiseGroup P where
  toFun := AdditionGroup.toSectionwiseGroup
  invFun := SectionwiseGroup.toAdditionGroup P
  left_inv S :=
    AdditionGroup.ext' P
      (NatTrans.ext (funext fun U =>
        ConcreteCategory.coe_ext (funext fun x => S.group_add U x.1 x.2)))
  right_inv G :=
    SectionwiseGroup.ext' P
      (funext fun U =>
        ((SectionwiseGroup.toAdditionGroup P G).group_eq U (G.group U) fun _ _ => rfl).symm)

end TopCat.Presheaf
