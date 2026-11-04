module

public import Mathlib.Topology.Sets.Opens
public import Mathlib.Order.Zorn
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Tactic.Abel

/-!
# Gluing in the cokernel of a map of flasque sheaves

Let `X` be a topological space and `C₂ ⟶ C₁ ⟶ Z` maps of presheaves of abelian groups on the
opens of `X` with composite zero, exact at `C₁` over every open, where `C₁` and `Z` are sheaves
and `C₂` and `C₁` are flasque.  Then the presheaf `U ↦ Z(U) / d(C₁(U))` is a sheaf: classes
given on the members of an open covering of `U` which agree on the overlaps come from a class over
`U`, and a class over `U` vanishing on every member vanishes.

This is the elementary input of the Zariski gluing of morphisms in a derived category under the
vanishing of `Ext⁻¹` (the source's Stacks 0D66 in the flasque form): with `I` a K-injective
complex with injective terms, the complex `U ↦ Hom^•(K|_U, I|_U)` is a complex of flasque
sheaves, its `H⁰` is `U ↦ Hom(K|_U, E|_U)` and its `H⁻¹` is `U ↦ Ext⁻¹(K|_U, E|_U)`.

Both statements are proved by Zorn's lemma on the partial sections over the opens below `U`:
a maximal partial section is defined on all of `U`, since a partial section over `W` and the
given datum on a member `V` not contained in `W` differ on `W ∩ V` by a boundary, which flasqueness
extends to `V`, so that the two glue to a partial section over `W ∪ V`.  The separation statement
(`Stacks.FlasqueCokernel.FlasqueTriple.isBoundary_of_isBoundary_res`) uses the flasqueness of `C₂`
and the exactness at `C₁`; the gluing statement
(`Stacks.FlasqueCokernel.FlasqueTriple.exists_glue_mod_boundary`) uses the flasqueness of `C₁` and
the separation statement.

The presheaves are given as raw data (`Stacks.FlasqueCokernel.OpensPresheafData`): a type of
sections over each open, the restriction maps and their two laws.  The sheaf condition is the
unique gluing condition for families indexed by a type in the universe of `X`; gluing along an
arbitrary family of opens (`Stacks.FlasqueCokernel.OpensPresheafData.IsSheaf.exists_glue`) is
deduced by reindexing along the set of opens occurring in it.

## Main definitions

* `Stacks.FlasqueCokernel.OpensPresheafData`: a presheaf of abelian groups on the opens of `X`.
* `Stacks.FlasqueCokernel.OpensPresheafData.IsSheaf`, `…IsFlasque`.
* `Stacks.FlasqueCokernel.FlasqueTriple`: the complex `C₂ ⟶ C₁ ⟶ Z` with its hypotheses.

## Main results

* `Stacks.FlasqueCokernel.FlasqueTriple.isBoundary_of_isBoundary_res`: a section of `Z` which is
  locally a boundary is a boundary.
* `Stacks.FlasqueCokernel.FlasqueTriple.exists_glue_mod_boundary`: sections of `Z` on the
  members of a covering which agree up to boundaries on the overlaps come from a section over the
  union, up to boundaries on every member.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public section

open TopologicalSpace

namespace Stacks.FlasqueCokernel

universe v w

variable {X : Type v} [TopologicalSpace X]

variable (X) in
/-- **A presheaf of abelian groups on the opens of `X`, as raw data**: the sections over each
open, the restriction maps, and the two presheaf laws. -/
structure OpensPresheafData where
  /-- The sections over an open. -/
  obj : Opens X → Type w
  /-- The abelian groups of sections. -/
  [addCommGroup : ∀ U, AddCommGroup (obj U)]
  /-- The restriction maps. -/
  res : ∀ {U V : Opens X}, V ≤ U → obj U →+ obj V
  res_self : ∀ {U : Opens X} (h : U ≤ U) (x : obj U), res h x = x
  res_res : ∀ {U V W : Opens X} (h : V ≤ U) (h' : W ≤ V) (x : obj U),
    res h' (res h x) = res (h'.trans h) x

attribute [instance] OpensPresheafData.addCommGroup

namespace OpensPresheafData

variable (F : OpensPresheafData.{v, w} X)

/-- **The sheaf condition**: for an open `U` and a family of opens `V i ≤ U` with union `U`,
sections over the `V i` agreeing on the overlaps are the restrictions of exactly one section over
`U`. -/
def IsSheaf : Prop :=
  ∀ (U : Opens X) {ι : Type v} (V : ι → Opens X) (hV : ∀ i, V i ≤ U), iSup V = U →
    ∀ s : ∀ i, F.obj (V i),
    (∀ i k, F.res (inf_le_left : V i ⊓ V k ≤ V i) (s i) = F.res inf_le_right (s k)) →
    ∃! x : F.obj U, ∀ i, F.res (hV i) x = s i

/-- **Flasqueness**: every restriction map is surjective. -/
def IsFlasque : Prop :=
  ∀ {U V : Opens X} (h : V ≤ U), Function.Surjective (F.res h)

variable {F}

/-- Compatibility on the overlaps, read on any open below two members. -/
theorem res_eq_res_of_compatible {ι : Type*} {V : ι → Opens X} {s : ∀ i, F.obj (V i)}
    (hs : ∀ i k, F.res (inf_le_left : V i ⊓ V k ≤ V i) (s i) = F.res inf_le_right (s k))
    (i k : ι) {O : Opens X} (hi : O ≤ V i) (hk : O ≤ V k) :
    F.res hi (s i) = F.res hk (s k) := by
  rw [← F.res_res inf_le_left (le_inf hi hk), hs i k, F.res_res]

/-- Gluing along a family of opens indexed by a type in the universe of `X`, with the
compatibility read on the opens below two members. -/
theorem IsSheaf.exists_glue_of_small (hF : F.IsSheaf) {U : Opens X} {ι : Type v}
    (V : ι → Opens X) (hV : ∀ i, V i ≤ U) (hsup : iSup V = U) (s : ∀ i, F.obj (V i))
    (hs : ∀ i k (O : Opens X) (hi : O ≤ V i) (hk : O ≤ V k), F.res hi (s i) = F.res hk (s k)) :
    ∃ x : F.obj U, ∀ i, F.res (hV i) x = s i :=
  (hF U V hV hsup s fun i k => hs i k _ inf_le_left inf_le_right).exists

/-- **Gluing along an arbitrary family of opens**: sections over the members of a family of
opens with union `U`, agreeing on every open below two members, are the restrictions of a
section over `U`.  The family is reindexed along the set of opens occurring in it. -/
theorem IsSheaf.exists_glue (hF : F.IsSheaf) {U : Opens X} {A : Type*} (W : A → Opens X)
    (hW : ∀ a, W a ≤ U) (hsup : iSup W = U) (x : ∀ a, F.obj (W a))
    (hx : ∀ a b (O : Opens X) (ha : O ≤ W a) (hb : O ≤ W b), F.res ha (x a) = F.res hb (x b)) :
    ∃ y : F.obj U, ∀ a, F.res (hW a) y = x a := by
  let V : Set.range W → Opens X := fun w => w.1
  let pick : ∀ w : Set.range W, A := fun w => w.2.choose
  have hpick : ∀ w : Set.range W, W (pick w) = w.1 := fun w => w.2.choose_spec
  let s : ∀ w : Set.range W, F.obj (V w) := fun w =>
    F.res (le_of_eq (hpick w).symm) (x (pick w))
  obtain ⟨y, hy⟩ := hF.exists_glue_of_small V (fun w => (le_of_eq (hpick w).symm).trans (hW _))
      ((iSup_range' (fun b => b) W).trans hsup) s fun w w' O hw hw' => by
    simp only [s]
    rw [F.res_res, F.res_res]
    exact hx _ _ O _ _
  refine ⟨y, fun a => (hy ⟨W a, a, rfl⟩).trans ?_⟩
  simp only [s]
  rw [hx (pick ⟨W a, a, rfl⟩) a (W a) _ le_rfl, F.res_self]

/-- **Separation along an arbitrary family of opens**: two sections over `U` with the same
restrictions to the members of a family of opens with union `U` are equal. -/
theorem IsSheaf.ext (hF : F.IsSheaf) {U : Opens X} {A : Type*} (W : A → Opens X)
    (hW : ∀ a, W a ≤ U) (hsup : iSup W = U) {x y : F.obj U}
    (h : ∀ a, F.res (hW a) x = F.res (hW a) y) : x = y := by
  let V : Set.range W → Opens X := fun w => w.1
  have hpick : ∀ w : Set.range W, W w.2.choose = w.1 := fun w => w.2.choose_spec
  have hV : ∀ w, V w ≤ U := fun w => (le_of_eq (hpick w).symm).trans (hW _)
  have hsupV : iSup V = U := (iSup_range' (fun b => b) W).trans hsup
  obtain ⟨_, -, hu⟩ := hF U V hV hsupV (fun w => F.res (hV w) y) fun i k => by
    rw [F.res_res, F.res_res]
  refine (hu x fun w => ?_).trans (hu y fun _ => rfl).symm
  have hw : V w ≤ W w.2.choose := le_of_eq (hpick w).symm
  rw [← F.res_res (hW _) hw, h, F.res_res]

/-- Gluing along two opens. -/
theorem IsSheaf.exists_glue₂ (hF : F.IsSheaf) {U A B : Opens X} (hA : A ≤ U) (hB : B ≤ U)
    (hAB : A ⊔ B = U) (a : F.obj A) (b : F.obj B)
    (h : F.res (inf_le_left : A ⊓ B ≤ A) a = F.res inf_le_right b) :
    ∃ y : F.obj U, F.res hA y = a ∧ F.res hB y = b := by
  let W : Bool → Opens X := fun t => bif t then A else B
  let x : ∀ t, F.obj (W t) := fun t => Bool.rec (motive := fun t => F.obj (W t)) b a t
  have hBA : ∀ (O : Opens X) (hO : O ≤ A) (hO' : O ≤ B), F.res hO a = F.res hO' b := by
    intro O hO hO'
    rw [← F.res_res (inf_le_left : A ⊓ B ≤ A) (le_inf hO hO'), h, F.res_res]
  obtain ⟨y, hy⟩ := hF.exists_glue W (fun t => by cases t <;> assumption)
      (by rw [iSup_bool_eq]; exact hAB) x fun t t' O ht ht' => by
    cases t <;> cases t'
    · rfl
    · exact (hBA O ht' ht).symm
    · exact hBA O ht ht'
    · rfl
  exact ⟨y, hy true, hy false⟩

/-- Separation along two opens. -/
theorem IsSheaf.ext₂ (hF : F.IsSheaf) {U A B : Opens X} (hA : A ≤ U) (hB : B ≤ U)
    (hAB : A ⊔ B = U) {x y : F.obj U} (h₁ : F.res hA x = F.res hA y)
    (h₂ : F.res hB x = F.res hB y) : x = y := by
  let W : Bool → Opens X := fun t => bif t then A else B
  exact hF.ext W (fun t => by cases t <;> assumption) (by rw [iSup_bool_eq]; exact hAB)
    fun t => by cases t <;> assumption

/-- Partial sections, ordered by extension, form a transitive relation. -/
private theorem res_trans_of_extends {p q s : Σ W : Opens X, F.obj W}
    (h₁ : ∃ h : p.1 ≤ q.1, F.res h q.2 = p.2) (h₂ : ∃ h : q.1 ≤ s.1, F.res h s.2 = q.2) :
    ∃ h : p.1 ≤ s.1, F.res h s.2 = p.2 := by
  obtain ⟨h₁, e₁⟩ := h₁
  obtain ⟨h₂, e₂⟩ := h₂
  exact ⟨h₁.trans h₂, by rw [← e₁, ← e₂, F.res_res]⟩

/-- A family of sections, any two of which extend one another, glues over the union. -/
private theorem IsSheaf.exists_glue_of_chain (hF : F.IsSheaf) {ι : Type*} {W : ι → Opens X}
    {x : ∀ i, F.obj (W i)}
    (hx : ∀ i j, i ≠ j → (∃ h : W i ≤ W j, F.res h (x j) = x i) ∨
      ∃ h : W j ≤ W i, F.res h (x i) = x j) :
    ∃ y : F.obj (iSup W), ∀ i, F.res (le_iSup W i) y = x i := by
  refine hF.exists_glue W (fun i => le_iSup W i) rfl x fun i j O hi hj => ?_
  rcases eq_or_ne i j with rfl | hij
  · rfl
  rcases hx i j hij with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [← e, F.res_res]

end OpensPresheafData

variable (X) in
/-- **A complex `C₂ ⟶ C₁ ⟶ Z` of presheaves of abelian groups on the opens of `X`**, exact at
`C₁` over every open, with `C₁` and `Z` sheaves and `C₂` and `C₁` flasque. -/
structure FlasqueTriple where
  /-- The first term. -/
  C₂ : OpensPresheafData.{v, w} X
  /-- The middle term. -/
  C₁ : OpensPresheafData.{v, w} X
  /-- The last term. -/
  Z : OpensPresheafData.{v, w} X
  /-- The first map. -/
  d₂ : ∀ U, C₂.obj U →+ C₁.obj U
  /-- The second map. -/
  d₁ : ∀ U, C₁.obj U →+ Z.obj U
  d₂_res : ∀ {U V : Opens X} (h : V ≤ U) (x : C₂.obj U), d₂ V (C₂.res h x) = C₁.res h (d₂ U x)
  d₁_res : ∀ {U V : Opens X} (h : V ≤ U) (x : C₁.obj U), d₁ V (C₁.res h x) = Z.res h (d₁ U x)
  d₁_d₂ : ∀ U (x : C₂.obj U), d₁ U (d₂ U x) = 0
  exact : ∀ U (y : C₁.obj U), d₁ U y = 0 → ∃ x, d₂ U x = y
  isSheaf_C₁ : C₁.IsSheaf
  isSheaf_Z : Z.IsSheaf
  isFlasque_C₂ : C₂.IsFlasque
  isFlasque_C₁ : C₁.IsFlasque

namespace FlasqueTriple

variable (T : FlasqueTriple.{v, w} X)

/-- A section of `Z` over `U` is a boundary when it is the image of a section of `C₁`. -/
def IsBoundary (U : Opens X) (z : T.Z.obj U) : Prop :=
  ∃ c, T.d₁ U c = z

variable {T}

/-- A sum of boundaries is a boundary. -/
theorem IsBoundary.add {U : Opens X} {z z' : T.Z.obj U} (h : T.IsBoundary U z)
    (h' : T.IsBoundary U z') : T.IsBoundary U (z + z') := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨c', rfl⟩ := h'
  exact ⟨c + c', map_add _ _ _⟩

/-- A difference of boundaries is a boundary. -/
theorem IsBoundary.sub {U : Opens X} {z z' : T.Z.obj U} (h : T.IsBoundary U z)
    (h' : T.IsBoundary U z') : T.IsBoundary U (z - z') := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨c', rfl⟩ := h'
  exact ⟨c - c', map_sub _ _ _⟩

/-- The restriction of a boundary is a boundary. -/
theorem IsBoundary.res {U V : Opens X} (h : V ≤ U) {z : T.Z.obj U} (hz : T.IsBoundary U z) :
    T.IsBoundary V (T.Z.res h z) := by
  obtain ⟨c, rfl⟩ := hz
  exact ⟨T.C₁.res h c, T.d₁_res h c⟩

/-- The zero section is a boundary. -/
theorem isBoundary_zero (U : Opens X) : T.IsBoundary U 0 :=
  ⟨0, map_zero _⟩

/-- **A section of `Z` which is locally a boundary is a boundary.**  If the restrictions of `z`
to the members of a family of opens with union `U` are boundaries, so is `z`.  Uses the
flasqueness of `C₂` and the exactness at `C₁`. -/
theorem isBoundary_of_isBoundary_res {U : Opens X} {A : Type*} (V : A → Opens X)
    (hV : ∀ a, V a ≤ U) (hsup : iSup V = U) (z : T.Z.obj U)
    (hz : ∀ a, T.IsBoundary (V a) (T.Z.res (hV a) z)) : T.IsBoundary U z := by
  -- partial primitives of `z` over the opens below `U`
  let P := {p : Σ W : Opens X, T.C₁.obj W // ∃ h : p.1 ≤ U, T.d₁ p.1 p.2 = T.Z.res h z}
  let r : P → P → Prop := fun p q => ∃ h : p.1.1 ≤ q.1.1, T.C₁.res h q.1.2 = p.1.2
  have htrans : ∀ {p q s : P}, r p q → r q s → r p s := OpensPresheafData.res_trans_of_extends
  have hbound : ∀ c : Set P, IsChain r c → ∃ ub, ∀ p ∈ c, r p ub := by
    intro c hc
    let W : c → Opens X := fun p => p.1.1.1
    let x : ∀ p : c, T.C₁.obj (W p) := fun p => p.1.1.2
    have hWU : iSup W ≤ U := iSup_le fun p => p.1.2.1
    obtain ⟨y, hy⟩ := T.isSheaf_C₁.exists_glue_of_chain (W := W) (x := x)
      fun p q hpq => hc p.2 q.2 fun h => hpq (Subtype.ext h)
    have hdy : T.d₁ _ y = T.Z.res hWU z := by
      refine T.isSheaf_Z.ext W (fun p => le_iSup W p) rfl fun p => ?_
      rw [← T.d₁_res, hy p, T.Z.res_res]
      exact p.1.2.2
    exact ⟨⟨⟨iSup W, y⟩, hWU, hdy⟩, fun p hp => ⟨le_iSup W ⟨p, hp⟩, hy ⟨p, hp⟩⟩⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hbound htrans
  obtain ⟨⟨W, c⟩, hWU, hc⟩ := m
  -- every member lies below the domain of a maximal partial primitive
  have hle : ∀ a, V a ≤ W := by
    intro a
    by_contra hna
    obtain ⟨ca, hca⟩ := hz a
    let O := W ⊓ V a
    have hδ : T.d₁ O (T.C₁.res inf_le_left c - T.C₁.res inf_le_right ca) = 0 := by
      rw [map_sub, T.d₁_res, T.d₁_res, hc, hca, T.Z.res_res, T.Z.res_res, sub_self]
    obtain ⟨e, he⟩ := T.exact O _ hδ
    obtain ⟨e', rfl⟩ := T.isFlasque_C₂ (inf_le_right : O ≤ V a) e
    let ca' := ca + T.d₂ (V a) e'
    have hagree : T.C₁.res (inf_le_left : W ⊓ V a ≤ W) c = T.C₁.res inf_le_right ca' := by
      rw [map_add, ← T.d₂_res, he, add_sub_cancel]
    obtain ⟨y, hyW, hyV⟩ := T.isSheaf_C₁.exists_glue₂ (le_sup_left : W ≤ W ⊔ V a)
      le_sup_right rfl c ca' hagree
    have hWVU : W ⊔ V a ≤ U := sup_le hWU (hV a)
    have hdy : T.d₁ _ y = T.Z.res hWVU z := by
      refine T.isSheaf_Z.ext₂ (le_sup_left : W ≤ W ⊔ V a) le_sup_right rfl ?_ ?_
      · rw [← T.d₁_res, hyW, hc, T.Z.res_res]
      · rw [← T.d₁_res, hyV, map_add, T.d₁_d₂, add_zero, hca, T.Z.res_res]
    obtain ⟨h, -⟩ := hm ⟨⟨W ⊔ V a, y⟩, hWVU, hdy⟩ ⟨le_sup_left, hyW⟩
    exact hna (le_sup_right.trans h)
  have hUW : U ≤ W := hsup ▸ iSup_le hle
  refine ⟨T.C₁.res hUW c, ?_⟩
  rw [T.d₁_res, hc, T.Z.res_res, T.Z.res_self]

/-- **Gluing up to boundaries.**  Let `V a` be a family of opens with union `U` and `z a`
sections of `Z` over the `V a` whose differences on the overlaps are boundaries.  Then there is a
section of `Z` over `U` whose restriction to every `V a` differs from `z a` by a boundary, and
two such sections differ by a boundary.  Uses the flasqueness of `C₁` and
`Stacks.FlasqueCokernel.FlasqueTriple.isBoundary_of_isBoundary_res`. -/
theorem exists_glue_mod_boundary {U : Opens X} {A : Type*} (V : A → Opens X)
    (hV : ∀ a, V a ≤ U) (hsup : iSup V = U) (z : ∀ a, T.Z.obj (V a))
    (hz : ∀ a b, T.IsBoundary (V a ⊓ V b)
      (T.Z.res inf_le_left (z a) - T.Z.res inf_le_right (z b))) :
    (∃ y : T.Z.obj U, ∀ a, T.IsBoundary (V a) (T.Z.res (hV a) y - z a)) ∧
      ∀ y y' : T.Z.obj U, (∀ a, T.IsBoundary (V a) (T.Z.res (hV a) y - z a)) →
        (∀ a, T.IsBoundary (V a) (T.Z.res (hV a) y' - z a)) → T.IsBoundary U (y - y') := by
  have hz' : ∀ a b (O : Opens X) (ha : O ≤ V a) (hb : O ≤ V b),
      T.IsBoundary O (T.Z.res ha (z a) - T.Z.res hb (z b)) := fun a b O ha hb => by
    simpa only [map_sub, T.Z.res_res] using (hz a b).res (le_inf ha hb)
  refine ⟨?_, fun y y' hy hy' => ?_⟩
  swap
  · refine isBoundary_of_isBoundary_res V hV hsup _ fun a => ?_
    rw [map_sub, show T.Z.res (hV a) y - T.Z.res (hV a) y' =
      (T.Z.res (hV a) y - z a) - (T.Z.res (hV a) y' - z a) by abel]
    exact (hy a).sub (hy' a)
  -- partial gluings over the opens below `U`
  let P := {p : Σ W : Opens X, T.Z.obj W // p.1 ≤ U ∧ ∀ a (O : Opens X) (hO : O ≤ p.1)
    (hO' : O ≤ V a), T.IsBoundary O (T.Z.res hO p.2 - T.Z.res hO' (z a))}
  let r : P → P → Prop := fun p q => ∃ h : p.1.1 ≤ q.1.1, T.Z.res h q.1.2 = p.1.2
  have htrans : ∀ {p q s : P}, r p q → r q s → r p s := OpensPresheafData.res_trans_of_extends
  have hbound : ∀ c : Set P, IsChain r c → ∃ ub, ∀ p ∈ c, r p ub := by
    intro c hc
    let W : c → Opens X := fun p => p.1.1.1
    let x : ∀ p : c, T.Z.obj (W p) := fun p => p.1.1.2
    have hWU : iSup W ≤ U := iSup_le fun p => p.1.2.1
    obtain ⟨y, hy⟩ := T.isSheaf_Z.exists_glue_of_chain (W := W) (x := x)
      fun p q hpq => hc p.2 q.2 fun h => hpq (Subtype.ext h)
    refine ⟨⟨⟨iSup W, y⟩, hWU, fun a O hO hO' => ?_⟩,
      fun p hp => ⟨le_iSup W ⟨p, hp⟩, hy ⟨p, hp⟩⟩⟩
    refine isBoundary_of_isBoundary_res (fun p : c => O ⊓ W p) (fun p => inf_le_left)
      (by rw [← inf_iSup_eq]; exact inf_eq_left.2 hO) _ fun p => ?_
    have hp := p.1.2.2 a (O ⊓ W p) inf_le_right (inf_le_left.trans hO')
    rwa [map_sub, T.Z.res_res, T.Z.res_res, ← T.Z.res_res (le_iSup W p) inf_le_right, hy p]
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hbound htrans
  obtain ⟨⟨W, zW⟩, hWU, hzW⟩ := m
  have hle : ∀ a, V a ≤ W := by
    intro a
    by_contra hna
    obtain ⟨c, hc⟩ := hzW a (W ⊓ V a) inf_le_left inf_le_right
    obtain ⟨c', rfl⟩ := T.isFlasque_C₁ (inf_le_right : W ⊓ V a ≤ V a) c
    let za := z a + T.d₁ (V a) c'
    have hagree : T.Z.res (inf_le_left : W ⊓ V a ≤ W) zW = T.Z.res inf_le_right za := by
      rw [map_add, ← T.d₁_res, hc, add_sub_cancel]
    obtain ⟨y, hyW, hyV⟩ := T.isSheaf_Z.exists_glue₂ (le_sup_left : W ≤ W ⊔ V a)
      le_sup_right rfl zW za hagree
    have hWVU : W ⊔ V a ≤ U := sup_le hWU (hV a)
    have hnew : ∀ b (O : Opens X) (hO : O ≤ W ⊔ V a) (hO' : O ≤ V b),
        T.IsBoundary O (T.Z.res hO y - T.Z.res hO' (z b)) := by
      intro b O hO hO'
      let C : Bool → Opens X := fun t => bif t then O ⊓ W else O ⊓ V a
      have hC : ∀ t, C t ≤ O := fun t => by cases t <;> exact inf_le_left
      have hCsup : iSup C = O := by
        rw [iSup_bool_eq]
        exact (inf_sup_left O W (V a)).symm.trans (inf_eq_left.2 hO)
      refine isBoundary_of_isBoundary_res C hC hCsup _ fun t => ?_
      cases t
      · -- on `O ⊓ V a`, where `y` is `z a + d c'`
        show T.IsBoundary (O ⊓ V a) (T.Z.res inf_le_left (T.Z.res hO y - T.Z.res hO' (z b)))
        rw [map_sub, T.Z.res_res, T.Z.res_res,
          ← T.Z.res_res (le_sup_right : V a ≤ W ⊔ V a) inf_le_right, hyV, map_add,
          ← T.d₁_res, show T.Z.res (inf_le_right : O ⊓ V a ≤ V a) (z a) +
              T.d₁ (O ⊓ V a) (T.C₁.res inf_le_right c') -
              T.Z.res (inf_le_left.trans hO') (z b) =
            (T.Z.res inf_le_right (z a) - T.Z.res (inf_le_left.trans hO') (z b)) +
              T.d₁ (O ⊓ V a) (T.C₁.res inf_le_right c') by abel]
        exact (hz' a b _ _ _).add ⟨_, rfl⟩
      · -- on `O ⊓ W`, where `y` is `zW`
        show T.IsBoundary (O ⊓ W) (T.Z.res inf_le_left (T.Z.res hO y - T.Z.res hO' (z b)))
        rw [map_sub, T.Z.res_res, T.Z.res_res,
          ← T.Z.res_res (le_sup_left : W ≤ W ⊔ V a) inf_le_right, hyW]
        exact hzW b (O ⊓ W) inf_le_right (inf_le_left.trans hO')
    obtain ⟨h, -⟩ := hm ⟨⟨W ⊔ V a, y⟩, hWVU, hnew⟩ ⟨le_sup_left, hyW⟩
    exact hna (le_sup_right.trans h)
  have hUW : U ≤ W := hsup ▸ iSup_le hle
  refine ⟨T.Z.res hUW zW, fun a => ?_⟩
  simpa only [T.Z.res_res, T.Z.res_self] using hzW a (V a) (hle a) le_rfl

end FlasqueTriple

end Stacks.FlasqueCokernel

end
