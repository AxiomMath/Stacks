module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Limits.Types.Images

/-!
# A Mittag-Leffler system over `ℕᵒᵖ` with nonempty values has a section

Mathlib's `nonempty_sections_of_finite_cofiltered_system` needs each value finite. For a system
indexed by `ℕᵒᵖ` the Mittag-Leffler condition replaces finiteness: the eventual ranges form a
surjective tower, and a surjective tower over `ℕ` has a section.

Three ways of recognizing the condition are proved as well.

* `CategoryTheory.Functor.isMittagLeffler_of_surjective_natTrans`: it passes to a pointwise
  surjective image.
* `CategoryTheory.Functor.IsMittagLeffler.comp_type`: it survives postcomposition with an
  arbitrary functor of types. The condition is a family of inclusions of ranges, each of which is
  witnessed by a splitting of one map by the other — a function, not a morphism of systems — and
  a functor carries a splitting to a splitting.
* `CategoryTheory.Functor.isMittagLeffler_of_pretransitive`: a system of sets on which a
  Mittag-Leffler system acts transitively and compatibly with the transition maps inherits the
  condition. This is the condition for a system of *pseudo-torsors* which have a point at every
  level: each value is then a translate of the acting set, and the ranges of the transition maps
  are translates of the ranges in the acting system.

The second of these is applied to towers in a category: if isomorphisms descend along the
transition maps of a tower `A`, which are epimorphisms, then the sets of isomorphisms
`A_n ≅ B_n` form a system on which the automorphisms of `A` act transitively, so
`CategoryTheory.Functor.nonempty_natIso_of_isMittagLeffler_isoTower` upgrades isomorphisms at
every level to an isomorphism of towers.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits

/-- A Mittag-Leffler functor `ℕᵒᵖ ⥤ Type u` with nonempty values has a nonempty set of
sections. -/
theorem nonempty_sections_of_isMittagLeffler {E : ℕᵒᵖ ⥤ Type u} (hML : E.IsMittagLeffler)
    (hne : ∀ i, Nonempty (E.obj i)) : Nonempty E.sections := by
  have : ∀ i, Nonempty (E.obj i) := hne
  have : ∀ i, Nonempty (E.toEventualRanges.obj i) :=
    fun i => E.toEventualRanges_nonempty hML i
  have hsurj : ∀ n : ℕ, Function.Surjective
      (E.toEventualRanges.map (homOfLE (Nat.le_succ n)).op) :=
    fun n => E.surjective_toEventualRanges hML _
  obtain ⟨s, -⟩ := Types.surjective_π_app_zero_of_surjective_map
    (limit.isLimit E.toEventualRanges) hsurj
      ((inferInstance : Nonempty (E.toEventualRanges.obj (Opposite.op 0))).some)
  exact ⟨E.toEventualRangesSectionsEquiv (Types.limitEquivSections _ s)⟩

namespace CategoryTheory.Functor

/-- The Mittag-Leffler condition is preserved by postcomposition with an arbitrary functor of
types. The condition asks that the range of one transition map be contained in the range of
every other, and such an inclusion is witnessed by a function splitting the first map through
the second; a functor carries that splitting to a splitting of the images. -/
theorem IsMittagLeffler.comp_type {J : Type*} [Category J] {F : J ⥤ Type u}
    (hF : F.IsMittagLeffler) (Φ : Type u ⥤ Type u') : (F ⋙ Φ).IsMittagLeffler := by
  classical
  intro j
  obtain ⟨i, f, hf⟩ := hF j
  refine ⟨i, f, fun {k} g => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : F.obj i ⟶ F.obj k, s ≫ F.map g = F.map f :=
    ⟨TypeCat.ofHom fun x => (hf g ⟨x, rfl⟩).choose,
      ConcreteCategory.hom_ext _ _ fun x => (hf g ⟨x, rfl⟩).choose_spec⟩
  rintro y ⟨x, rfl⟩
  refine ⟨Φ.map s x, ?_⟩
  change Φ.map (F.map g) (Φ.map s x) = Φ.map (F.map f) x
  rw [← Functor.map_comp_apply, hs]

/-- **A pointwise surjective image of a Mittag-Leffler system of sets is Mittag-Leffler.** An
element in the range of a transition map of the image lifts to the source, where the condition
places it in the range of any other transition map; its image is then in that range for the
image system, by naturality. -/
theorem isMittagLeffler_of_surjective_natTrans {J : Type*} [Category J] {F G : J ⥤ Type u}
    (q : F ⟶ G) (hq : ∀ i, Function.Surjective (q.app i)) (hF : F.IsMittagLeffler) :
    G.IsMittagLeffler := by
  intro j
  obtain ⟨i, f, hf⟩ := hF j
  refine ⟨i, f, fun {k} g y hy => ?_⟩
  obtain ⟨y, rfl⟩ := hy
  obtain ⟨x, rfl⟩ := hq i y
  obtain ⟨z, hz⟩ := hf g ⟨x, rfl⟩
  exact ⟨q.app k z, by
    rw [← NatTrans.naturality_apply q g, hz, NatTrans.naturality_apply q f]⟩

/-- A system of sets carrying a transitive action of a Mittag-Leffler system, compatible with
the transition maps, is itself Mittag-Leffler.

No freeness and no group structure is used: transitivity at every level together with a point at
every level makes each value a translate of the acting set, and that is enough to turn an
inclusion of ranges in the acting system into one in the system acted on. -/
theorem isMittagLeffler_of_pretransitive {G : ℕᵒᵖ ⥤ Type u} {S : ℕᵒᵖ ⥤ Type u'}
    (act : ∀ n, G.obj n → S.obj n → S.obj n)
    (act_map : ∀ {m n : ℕᵒᵖ} (f : m ⟶ n) (u : G.obj m) (s : S.obj m),
      S.map f (act m u s) = act n (G.map f u) (S.map f s))
    (act_trans : ∀ (n : ℕᵒᵖ) (s t : S.obj n), ∃ u, act n u s = t)
    (hne : ∀ n, Nonempty (S.obj n)) (hG : G.IsMittagLeffler) : S.IsMittagLeffler := by
  intro j
  obtain ⟨i, f, hf⟩ := hG j
  refine ⟨i, f, fun {k} g => ?_⟩
  rintro x ⟨a, rfl⟩
  -- a common refinement of the two levels `i` and `k`
  obtain ⟨b⟩ := hne (Opposite.op (max i.unop k.unop))
  set h₁ : (Opposite.op (max i.unop k.unop) : ℕᵒᵖ) ⟶ i :=
    (homOfLE (le_max_left i.unop k.unop)).op with hh₁
  set h₂ : (Opposite.op (max i.unop k.unop) : ℕᵒᵖ) ⟶ k :=
    (homOfLE (le_max_right i.unop k.unop)).op with hh₂
  obtain ⟨v, hv⟩ := act_trans i (S.map h₁ b) a
  obtain ⟨z, hz⟩ := hf g ⟨v, rfl⟩
  -- the two paths to level `j` agree, the index category being a partial order
  have hcomp : S.map g (S.map h₂ b) = S.map f (S.map h₁ b) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
      Subsingleton.elim (h₂ ≫ g) (h₁ ≫ f)]
  exact ⟨act k z (S.map h₂ b), by
    rw [act_map g z (S.map h₂ b), hz, hcomp, ← act_map f v (S.map h₁ b), hv]⟩

/-- A system of sets with a point at every level, carrying a transitive action of a
Mittag-Leffler system compatibly with the transition maps, has a section. -/
theorem nonempty_sections_of_pretransitive {G : ℕᵒᵖ ⥤ Type u} {S : ℕᵒᵖ ⥤ Type u'}
    (act : ∀ n, G.obj n → S.obj n → S.obj n)
    (act_map : ∀ {m n : ℕᵒᵖ} (f : m ⟶ n) (u : G.obj m) (s : S.obj m),
      S.map f (act m u s) = act n (G.map f u) (S.map f s))
    (act_trans : ∀ (n : ℕᵒᵖ) (s t : S.obj n), ∃ u, act n u s = t)
    (hne : ∀ n, Nonempty (S.obj n)) (hG : G.IsMittagLeffler) : Nonempty S.sections :=
  nonempty_sections_of_isMittagLeffler
    (isMittagLeffler_of_pretransitive act act_map act_trans hne hG) hne

section Tower

variable {C : Type u} [Category.{u'} C]

/-- A tower all of whose one-step transition maps are epimorphisms has all its transition maps
epimorphisms, every morphism of `ℕᵒᵖ` being a composite of one-step ones. -/
theorem epi_map_of_epi_succ {A : ℕᵒᵖ ⥤ C}
    (hsucc : ∀ n : ℕ, Epi (A.map (homOfLE (Nat.le_succ n)).op)) ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n) :
    Epi (A.map f) := by
  have key : ∀ (j k : ℕ) (hjk : j ≤ k),
      Epi (A.map ((homOfLE hjk).op : (Opposite.op k : ℕᵒᵖ) ⟶ Opposite.op j)) := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base =>
      rw [show ((homOfLE (le_refl j)).op : (Opposite.op j : ℕᵒᵖ) ⟶ Opposite.op j) = 𝟙 _ from
        Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
      infer_instance
    | succ k hjk ih =>
      rw [show ((homOfLE (hjk.trans (Nat.le_succ k))).op :
          (Opposite.op (k + 1) : ℕᵒᵖ) ⟶ Opposite.op j) =
        (homOfLE (Nat.le_succ k)).op ≫ (homOfLE hjk).op from Subsingleton.elim _ _, A.map_comp]
      have := hsucc k
      have := ih
      infer_instance
  rw [show f = (homOfLE (leOfHom f.unop)).op from Subsingleton.elim _ _]
  exact key _ _ _

/-- The tower `A` *descends isomorphisms to* the tower `B` if every isomorphism between their
values at one level pushes along the transition maps to an isomorphism between their values at a
lower level, compatibly with those transition maps.

In the situation this abstracts, `A.map f` and `B.map f` are quotient maps characterized by a
universal property and the pushed isomorphism is the induced map of quotients. -/
def DescendsIsos (A B : ℕᵒᵖ ⥤ C) : Prop :=
  ∀ ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n) (α : A.obj m ≅ B.obj m),
    ∃ β : A.obj n ≅ B.obj n, A.map f ≫ β.hom = α.hom ≫ B.map f

/-- A descended isomorphism is unique as soon as the transition maps of `A` are epimorphisms. -/
theorem DescendsIsos.unique {A B : ℕᵒᵖ ⥤ C} (hepi : ∀ ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n), Epi (A.map f))
    {m n : ℕᵒᵖ} (f : m ⟶ n) {α : A.obj m ≅ B.obj m} {β β' : A.obj n ≅ B.obj n}
    (hβ : A.map f ≫ β.hom = α.hom ≫ B.map f) (hβ' : A.map f ≫ β'.hom = α.hom ≫ B.map f) :
    β = β' :=
  have := hepi f
  Iso.ext ((cancel_epi (A.map f)).1 (hβ.trans hβ'.symm))

/-- The tower of sets of isomorphisms `n ↦ (A_n ≅ B_n)`, with the descended isomorphisms as its
transition maps. Uniqueness of a descended isomorphism is what makes this a functor. -/
noncomputable def isoTower (A B : ℕᵒᵖ ⥤ C)
    (hepi : ∀ ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n), Epi (A.map f))
    (h : DescendsIsos A B) : ℕᵒᵖ ⥤ Type u' where
  obj n := A.obj n ≅ B.obj n
  map f := TypeCat.ofHom fun α => (h f α).choose
  map_id n := ConcreteCategory.hom_ext _ _ fun α => by
    change (h (𝟙 n) α).choose = α
    exact DescendsIsos.unique hepi (𝟙 n) (h (𝟙 n) α).choose_spec (by simp)
  map_comp f g := ConcreteCategory.hom_ext _ _ fun α => by
    change (h (f ≫ g) α).choose = (h g (h f α).choose).choose
    refine DescendsIsos.unique hepi (f ≫ g) (h (f ≫ g) α).choose_spec ?_
    have hβ := (h f α).choose_spec
    have hγ := (h g (h f α).choose).choose_spec
    rw [A.map_comp, Category.assoc, hγ, ← Category.assoc, hβ, Category.assoc, ← B.map_comp]

/-- The value of the transition map of `isoTower` is the descended isomorphism. -/
theorem isoTower_map_apply (A B : ℕᵒᵖ ⥤ C)
    (hepi : ∀ ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n), Epi (A.map f)) (h : DescendsIsos A B)
    {m n : ℕᵒᵖ} (f : m ⟶ n) (α : A.obj m ≅ B.obj m) :
    (isoTower A B hepi h).map f α = (h f α).choose :=
  rfl

/-- **Two towers which are isomorphic at every level are isomorphic as towers**, provided the
transition maps of the first are epimorphisms, isomorphisms descend along them — to the second
tower and to the first itself — and the tower of automorphism sets of the first is
Mittag-Leffler.

This is the torsor step of Stacks 09BV with the torsor removed. The source makes the sheaf of
isomorphisms `Isom(A_n, B_n)` a torsor under `Isom(A_n, A_n)` and takes a section of the limit
of the images; here the hypothesis that the levels are isomorphic says that that torsor has a
point, so the set of isomorphisms at each level is a translate of the set of automorphisms of
`A_n`, and `isMittagLeffler_of_pretransitive` applies to the translated system directly. -/
theorem nonempty_natIso_of_isMittagLeffler_isoTower (A B : ℕᵒᵖ ⥤ C)
    (hepi : ∀ ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n), Epi (A.map f))
    (hAA : DescendsIsos A A) (hAB : DescendsIsos A B)
    (hne : ∀ n, Nonempty (A.obj n ≅ B.obj n))
    (hML : (isoTower A A hepi hAA).IsMittagLeffler) : Nonempty (A ≅ B) := by
  obtain ⟨s⟩ := nonempty_sections_of_pretransitive
    (G := isoTower A A hepi hAA) (S := isoTower A B hepi hAB)
    (fun n (u : A.obj n ≅ A.obj n) (α : A.obj n ≅ B.obj n) => u ≪≫ α)
    (fun {m n} f (u : A.obj m ≅ A.obj m) (α : A.obj m ≅ B.obj m) =>
      DescendsIsos.unique hepi f (hAB f (u ≪≫ α)).choose_spec (by
        have hu := (hAA f u).choose_spec
        have hα := (hAB f α).choose_spec
        change A.map f ≫ ((hAA f u).choose ≪≫ (hAB f α).choose).hom = (u ≪≫ α).hom ≫ B.map f
        rw [Iso.trans_hom, ← Category.assoc, hu, Category.assoc, hα, Iso.trans_hom,
          Category.assoc]))
    (fun n (α α' : A.obj n ≅ B.obj n) => ⟨α' ≪≫ α.symm, by
      change (α' ≪≫ α.symm) ≪≫ α = α'
      rw [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]⟩)
    hne hML
  refine ⟨NatIso.ofComponents (fun n => (s.val n : A.obj n ≅ B.obj n)) (fun {m n} f => ?_)⟩
  have hα := (hAB f (s.val m : A.obj m ≅ B.obj m)).choose_spec
  rwa [show (hAB f (s.val m : A.obj m ≅ B.obj m)).choose = (s.val n : A.obj n ≅ B.obj n) from
    s.property f] at hα

end Tower

end CategoryTheory.Functor
