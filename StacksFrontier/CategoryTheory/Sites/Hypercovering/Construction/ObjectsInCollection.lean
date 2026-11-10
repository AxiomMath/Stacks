module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Skeleton
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Split

/-!
# Hypercoverings by objects in a prescribed collection

On a site with fibre products, a collection `B` of objects which supplies coverings and for which
a covering remains covering after adjoining one morphism from the collection supplies a
hypercovering of every object, all of whose constituent objects belong to `B`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.exists_hypercovering_with_objects_in`: every object admits
  a hypercovering whose terms are formal coproducts of objects in the prescribed collection.

## Implementation notes

A family is represented by its presieve of arrows. Adjoining one member to a family is therefore
expressed as the union of that presieve with a singleton presieve. Since a hypercovering of `X` is
represented in `FormalCoproduct (Over X)`, membership in the collection is imposed on the
underlying left object of every summand in every simplicial degree.

The construction is the source's: start from a covering of `X` by objects of `B`, regarded as a
constant simplicial object, and build a sequence of simplicial objects by attaching, in degree
`n + 1`, the cells of a covering of the matching object by objects of `B`. Each step changes
nothing below degree `n + 1`, so the sequence is eventually constant in every degree and its
colimit is the required hypercovering. The attached simplicial objects stay split and
degenerate above the current degree, which is what makes the fibres of the map to the matching
object finite, so that the adjoining hypothesis can be applied to them.

## References

* [Stacks Project, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV)
-/

@[expose] public section

universe w v u z t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

-- Preserve the accepted statements' category-to-quiver instance for arrow notation, so that the
-- hom types of formal coproducts written below are syntactically the ones the cofan maps have.
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

section Refinement

/-- Refining a semi-representable object over `X` by coverings from `B`, component by
component. -/
private lemma exists_covering_refinement_in_B (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (V : ι → C) (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J U)
    {X : C} (T : FormalCoproduct.{w} (Over X)) :
    ∃ K : FormalCoproduct.{w} (Over X), ∃ (g : K ⟶ T),
      (∀ i : K.I, (K.obj i).left ∈ B) ∧ IsCoveringOver J g := by
  classical
  choose ι V f hB hJ using hcover
  let K : FormalCoproduct.{w} (Over X) := ⟨Σ j : T.I, ι (T.obj j).left,
    fun a ↦ Over.mk (f (T.obj a.1).left a.2 ≫ (T.obj a.1).hom)⟩
  let g : K ⟶ T := ⟨fun a ↦ a.1, fun a ↦ Over.homMk (f (T.obj a.1).left a.2)⟩
  refine ⟨K, g, ?_, ?_⟩
  · rintro ⟨j, i⟩
    exact hB _ i
  · intro j
    have hEq : Presieve.ofArrows
        (fun i : { i : K.I // g.f i = j } ↦ (K.obj i.1).left)
        (fun i ↦ (g.φ i.1).left ≫
          eqToHom (congrArg (fun k ↦ (T.obj k).left) i.2)) =
        Presieve.ofArrows (V (T.obj j).left) (f (T.obj j).left) := by
      apply le_antisymm
      · rintro Y a ⟨⟨j', i⟩, hj⟩
        change j' = j at hj
        subst j'
        simpa [K, g] using (Presieve.ofArrows.mk i :
          Presieve.ofArrows (V (T.obj j).left) (f (T.obj j).left) _)
      · rintro Y a ⟨i⟩
        let k : { i : K.I // g.f i = j } := ⟨⟨j, i⟩, rfl⟩
        simpa [K, g] using (Presieve.ofArrows.mk k :
          Presieve.ofArrows
            (fun i : { i : K.I // g.f i = j } ↦ (K.obj i.1).left)
            (fun i ↦ (g.φ i.1).left ≫
              eqToHom (congrArg (fun k ↦ (T.obj k).left) i.2)) _)
    rw [hEq]
    exact hJ (T.obj j).left

/-- The degree-zero family of a hypercovering by objects of `B` can be chosen directly from the
covering hypothesis. This is the initial step of the recursive construction. -/
private lemma exists_initial_B_cover (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (V : ι → C) (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J U)
    (X : C) :
    ∃ T : FormalCoproduct.{w} (Over X),
      (∀ i : T.I, (T.obj i).left ∈ B) ∧ IsCoveringOver J (terminal.from T) := by
  let T : FormalCoproduct.{w} (Over X) := ⊤_ (FormalCoproduct.{w} (Over X))
  obtain ⟨K, f, hK, hf⟩ := exists_covering_refinement_in_B J B hcover T
  refine ⟨K, hK, ?_⟩
  rwa [Subsingleton.elim f (terminal.from K)] at hf

end Refinement

section Adjoin

omit [HasPullbacks C] in
/-- Reindexing the adjoined part of a family along an equivalence does not change its presieve. -/
private lemma ofArrows_sumElim_equiv {ι α β : Type w} {U : C} (V : ι → C) (f : ∀ i, V i ⟶ U)
    (e : α ≃ β) (W : β → C) (g : ∀ b, W b ⟶ U) :
    Presieve.ofArrows (Sum.elim V W)
        (fun x ↦ match x with | .inl i => f i | .inr b => g b) =
      Presieve.ofArrows (Sum.elim V (W ∘ e))
        (fun x ↦ match x with | .inl i => f i | .inr a => g (e a)) := by
  funext T
  ext q
  constructor
  · rintro ⟨i | b⟩
    · exact Presieve.ofArrows.mk (Sum.inl i)
    · obtain ⟨a, rfl⟩ := e.surjective b
      exact Presieve.ofArrows.mk (Sum.inr a)
  · rintro ⟨i | a⟩
    · exact Presieve.ofArrows.mk (Sum.inl i)
    · exact Presieve.ofArrows.mk (Sum.inr (e a))

omit [HasPullbacks C] in
/-- Adjoining an empty family does not change the presieve. -/
private lemma ofArrows_sumElim_pempty {ι : Type w} {U : C} (V : ι → C) (f : ∀ i, V i ⟶ U)
    (W : PEmpty.{w + 1} → C) (F : ∀ x, Sum.elim V W x ⟶ U) (hF : ∀ i, F (.inl i) = f i) :
    Presieve.ofArrows (Sum.elim V W) F = Presieve.ofArrows V f := by
  funext T
  ext q
  constructor
  · rintro ⟨i | k⟩
    · rw [hF]
      exact Presieve.ofArrows.mk i
    · exact k.elim
  · rintro ⟨i⟩
    rw [← hF i]
    exact Presieve.ofArrows.mk (Sum.inl i)

omit [HasPullbacks C] in
/-- Adjoining a family indexed by `Option α` is adjoining the family indexed by `α`, then the
morphism indexed by `none`. -/
private lemma ofArrows_sumElim_option {ι α : Type w} {U : C} (V : ι → C) (W : Option α → C)
    (F : ∀ x, Sum.elim V W x ⟶ U) (F' : ∀ x, Sum.elim V (fun a ↦ W (some a)) x ⟶ U)
    (hl : ∀ i, F' (.inl i) = F (.inl i)) (hr : ∀ a, F' (.inr a) = F (.inr (some a))) :
    Presieve.ofArrows (Sum.elim V W) F =
      (fun ⦃_⦄ q ↦ Presieve.ofArrows (Sum.elim V (fun a ↦ W (some a))) F' q ∨
        Presieve.singleton (F (.inr none)) q : Presieve U) := by
  funext T
  ext q
  constructor
  · rintro ⟨i | _ | a⟩
    · rw [← hl]
      exact Or.inl (Presieve.ofArrows.mk (Sum.inl i))
    · exact Or.inr (Presieve.singleton_self _)
    · rw [← hr]
      exact Or.inl (Presieve.ofArrows.mk (Sum.inr a))
  · rintro (⟨i | a⟩ | hq)
    · rw [hl]
      exact Presieve.ofArrows.mk (Sum.inl i)
    · rw [hr]
      exact Presieve.ofArrows.mk (Sum.inr (some a))
    · rcases hq with ⟨⟩
      exact Presieve.ofArrows.mk (Sum.inr none)

/-- Adjoining finitely many morphisms from `B` to a covering family keeps it covering: induct on
the finite index type, using the one-morphism hypothesis at each step. -/
private lemma covering_of_finite_adjoin (J : Pretopology C) (B : Set C)
    (hadjoin : ∀ {ι : Type w} (V : ι → C) {U : C} (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ g : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈ J U)
    {ι κ : Type w} [Finite κ] {U : C} (V : ι → C) (f : ∀ i, V i ⟶ U)
    (W : κ → C) (g : ∀ k, W k ⟶ U)
    (hV : ∀ i, V i ∈ B) (hW : ∀ k, W k ∈ B)
    (hJ : Presieve.ofArrows V f ∈ J U) :
    Presieve.ofArrows (Sum.elim V W)
      (fun x ↦ match x with | .inl i => f i | .inr k => g k) ∈ J U := by
  classical
  let P : Type w → Prop := fun κ ↦
    ∀ (W : κ → C) (g : ∀ k, W k ⟶ U), (∀ k, W k ∈ B) →
      Presieve.ofArrows (Sum.elim V W)
        (fun x ↦ match x with | .inl i => f i | .inr k => g k) ∈ J U
  have hequiv : ∀ {α β : Type w}, α ≃ β → P α → P β := by
    intro α β e h W g hW
    exact (ofArrows_sumElim_equiv V f e W g).symm ▸ h (W ∘ e) (fun a ↦ g (e a)) (fun a ↦ hW (e a))
  have hempty : P PEmpty := by
    intro W g _
    exact (congrArg (· ∈ J U) (ofArrows_sumElim_pempty V f W _ fun _ ↦ rfl)).mpr hJ
  have hoption : ∀ {α : Type w} [Fintype α], P α → P (Option α) := by
    intro α _ h W g hW
    have hV' : ∀ i, Sum.elim V (fun a ↦ W (some a)) i ∈ B := by
      rintro (i | a)
      · exact hV i
      · exact hW (some a)
    have hadd := hadjoin (Sum.elim V (fun a ↦ W (some a)))
      (fun x ↦ match x with | .inl i => f i | .inr a => g (some a)) hV'
      (h _ _ (fun a ↦ hW (some a))) (hW none) (g none)
    exact (congrArg (· ∈ J U)
      (ofArrows_sumElim_option V W _ _ (fun _ ↦ rfl) (fun _ ↦ rfl))).mpr hadd
  exact Finite.induction_empty_option hequiv hempty hoption κ W g hW

/-- A family with a covering subfamily whose complement is finite is itself covering. -/
private lemma covering_of_finite_complement (J : Pretopology C) (B : Set C)
    (hadjoin : ∀ {ι : Type w} (V : ι → C) {U : C} (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ g : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈ J U)
    {ι : Type w} {U : C} (V : ι → C) (f : ∀ i, V i ⟶ U)
    (S : Set ι) [Finite {i : ι // i ∉ S}]
    (hV : ∀ i, V i ∈ B)
    (hJ : Presieve.ofArrows (fun i : {i : ι // i ∈ S} ↦ V i.1)
      (fun i ↦ f i.1) ∈ J U) : Presieve.ofArrows V f ∈ J U := by
  have h := covering_of_finite_adjoin J B hadjoin
    (fun i : {i : ι // i ∈ S} ↦ V i.1) (fun i ↦ f i.1)
    (fun i : {i : ι // i ∉ S} ↦ V i.1) (fun i ↦ f i.1)
    (fun i ↦ hV i.1) (fun i ↦ hV i.1) hJ
  convert h using 1
  funext T
  ext q
  constructor
  · rintro ⟨i⟩
    by_cases hi : i ∈ S
    · exact Presieve.ofArrows.mk (Sum.inl (⟨i, hi⟩ : {i : ι // i ∈ S}))
    · exact Presieve.ofArrows.mk (Sum.inr (⟨i, hi⟩ : {i : ι // i ∉ S}))
  · rintro ⟨i | i⟩ <;> exact Presieve.ofArrows.mk i.1

/-- A family which becomes covering after reindexing along a map whose image omits only finitely
many indices is covering. -/
private lemma covering_of_subfamily_with_finite_complement
    (J : Pretopology C) (B : Set C)
    (hadjoin : ∀ {ι : Type w} (V : ι → C) {U : C} (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ g : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈ J U)
    {ι κ : Type w} {U : C} (V : κ → C) (f : ∀ k, V k ⟶ U)
    (r : ι → κ)
    [Finite {k : κ // k ∉ Set.range r}]
    (hV : ∀ k, V k ∈ B)
    (hJ : Presieve.ofArrows (V ∘ r) (fun i ↦ f (r i)) ∈ J U) :
    Presieve.ofArrows V f ∈ J U := by
  let S : Set κ := Set.range r
  have hS : Presieve.ofArrows (fun k : {k : κ // k ∈ S} ↦ V k.1)
      (fun k ↦ f k.1) ∈ J U := by
    have hsurj : Function.Surjective (fun i : ι ↦ (⟨r i, ⟨i, rfl⟩⟩ : {k // k ∈ S})) := by
      rintro ⟨k, i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
    rwa [← Presieve.ofArrows_comp_eq_of_surjective
      (fun k : {k : κ // k ∈ S} ↦ f k.1) hsurj]
  exact covering_of_finite_complement J B hadjoin V f S hV hS

/-- Attaching, to a covering of a semi-representable object, a further family whose fibres over
each index are finite keeps the resulting family covering. This is the form in which the adjoining
hypothesis is used on an attachment of cells, with `S` the (subsingleton) index type of the
attached cells. -/
private lemma covering_of_option_cofan_with_finite_old_fibres
    {X : C} (J : Pretopology C) (B : Set C)
    (hadjoin : ∀ {ι : Type w} (V : ι → C) {U : C} (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ g : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈ J U)
    {S : Type w} [Subsingleton S] (s : S) {Z : FormalCoproduct.{w} (Over X)}
    (F : Option S → FormalCoproduct.{w} (Over X)) (m : ∀ o, F o ⟶ Z)
    (hB : ∀ o i, ((F o).obj i).left ∈ B)
    (hq : IsCoveringOver J (m (some s)))
    (hfinite : ∀ j, Finite {i : (F none).I // (m none).f i = j}) :
    IsCoveringOver J ((FormalCoproduct.cofanHomEquiv (Option S) F Z).symm m) := by
  let L := (FormalCoproduct.cofan (Option S) F).pt
  let p : L ⟶ Z := (FormalCoproduct.cofanHomEquiv (Option S) F Z).symm m
  intro j
  let r : {i : (F (some s)).I // (m (some s)).f i = j} → {i : L.I // p.f i = j} :=
    fun i ↦ ⟨⟨some s, i.1⟩, i.2⟩
  have hcompl : Finite {k : {i : L.I // p.f i = j} // k ∉ Set.range r} := by
    let g : {k : {i : L.I // p.f i = j} // k ∉ Set.range r} →
        {i : (F none).I // (m none).f i = j} := fun k ↦ by
      rcases k with ⟨⟨⟨o, i⟩, hi⟩, hk⟩
      cases o with
      | none => exact ⟨i, hi⟩
      | some a =>
        obtain rfl : a = s := Subsingleton.elim _ _
        exact False.elim (hk ⟨⟨i, hi⟩, rfl⟩)
    apply Finite.of_injective g
    intro k l h
    rcases k with ⟨⟨⟨o, i⟩, hi⟩, hk⟩
    rcases l with ⟨⟨⟨o', i'⟩, hi'⟩, hk'⟩
    cases o with
    | none =>
      cases o' with
      | none =>
        obtain rfl : i = i' := congrArg Subtype.val h
        rfl
      | some a =>
        obtain rfl : a = s := Subsingleton.elim _ _
        exact (hk' ⟨⟨i', hi'⟩, rfl⟩).elim
    | some a =>
      obtain rfl : a = s := Subsingleton.elim _ _
      exact (hk ⟨⟨i, hi⟩, rfl⟩).elim
  exact covering_of_subfamily_with_finite_complement J B hadjoin
    (fun i : {i : L.I // p.f i = j} ↦ (L.obj i.1).left)
    (fun i ↦ (p.φ i.1).left ≫
      eqToHom (congrArg (fun k ↦ (Z.obj k).left) i.2))
    r (fun i ↦ hB i.1.1 i.1.2) (hq j)

end Adjoin

section Attachment

omit [HasPullbacks C]

/-- The family of summands of one degree of an attachment: the old term together with one copy of
`N` for each simplex of `U` outside the subcomplex `A`. -/
private abbrev attachmentFamily (K : SimplicialObject (FormalCoproduct.{w} C))
    {U : SSet.{w}} (A : U.Subcomplex) (N : FormalCoproduct.{w} C)
    (j : SimplexCategoryᵒᵖ) : Option {a : U.obj j // a ∉ A.obj j} → FormalCoproduct.{w} C :=
  fun o ↦ match o with | none => K.obj j | some _ => N

/-- One degree of an attachment. -/
private abbrev attachmentLevel (K : SimplicialObject (FormalCoproduct.{w} C))
    {U : SSet.{w}} (A : U.Subcomplex) (N : FormalCoproduct.{w} C)
    (j : SimplexCategoryᵒᵖ) :=
  (FormalCoproduct.cofan _ (attachmentFamily K A N j)).pt

/-- The inclusion of the old term into one degree of an attachment. -/
private abbrev attachmentInclusion (K : SimplicialObject (FormalCoproduct.{w} C))
    {U : SSet.{w}} (A : U.Subcomplex) (N : FormalCoproduct.{w} C)
    (j : SimplexCategoryᵒᵖ) : K.obj j ⟶ attachmentLevel K A N j :=
  (FormalCoproduct.cofan _ (attachmentFamily K A N j)).inj none

variable (K : SimplicialObject (FormalCoproduct.{w} C))
    {U : SSet.{w}} (A : U.Subcomplex) (N : FormalCoproduct.{w} C)
    (d : ∀ j, {a : U.obj j // a ∈ A.obj j} → (N ⟶ K.obj j))

/-- The cell of an attachment attached to a simplex of `U`: the new summand when the simplex lies
outside the subcomplex, and the prescribed map followed by the inclusion when it lies inside. -/
private noncomputable def attachmentCell (j : SimplexCategoryᵒᵖ) (a : U.obj j) :
    N ⟶ attachmentLevel K A N j := by
  classical
  exact if h : a ∈ A.obj j then d j ⟨a, h⟩ ≫ attachmentInclusion K A N j
    else (FormalCoproduct.cofan _ (attachmentFamily K A N j)).inj (some ⟨a, h⟩)

/-- The simplicial operator of an attachment. -/
private noncomputable def attachmentMap {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    attachmentLevel K A N i ⟶ attachmentLevel K A N j :=
  (FormalCoproduct.cofanHomEquiv _ _ _).symm
    (fun a ↦ match a with
      | none => K.map f ≫ attachmentInclusion K A N j
      | some a => attachmentCell K A N d j (U.map f a.1))

private lemma attachmentInclusion_map {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    attachmentInclusion K A N i ≫ attachmentMap K A N d f =
      K.map f ≫ attachmentInclusion K A N j :=
  congrFun ((FormalCoproduct.cofanHomEquiv _ _ _).apply_symm_apply _) none

variable (hd : ∀ {i j} (f : i ⟶ j) (a : {a : U.obj i // a ∈ A.obj i}),
  d i a ≫ K.map f = d j ⟨U.map f a.1, A.map f a.2⟩)

include hd in
private lemma attachmentCell_map {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) (a : U.obj i) :
    attachmentCell K A N d i a ≫ attachmentMap K A N d f =
      attachmentCell K A N d j (U.map f a) := by
  classical
  by_cases ha : a ∈ A.obj i
  · have haf : U.map f a ∈ A.obj j := A.map f ha
    simp only [attachmentCell, dite_eq_left ha, dite_eq_left haf, Category.assoc,
      attachmentInclusion_map]
    rw [← Category.assoc, hd]
  · simp only [attachmentCell, dite_eq_right ha]
    exact congrFun ((FormalCoproduct.cofanHomEquiv _ (attachmentFamily K A N i)
      (attachmentLevel K A N j)).apply_symm_apply _) (some ⟨a, ha⟩)

private lemma attachment_hom_ext (j : SimplexCategoryᵒᵖ) {T : FormalCoproduct.{w} C}
    {f g : attachmentLevel K A N j ⟶ T}
    (hK : attachmentInclusion K A N j ≫ f = attachmentInclusion K A N j ≫ g)
    (hN : ∀ a : U.obj j, attachmentCell K A N d j a ≫ f =
      attachmentCell K A N d j a ≫ g) : f = g := by
  classical
  apply (FormalCoproduct.cofanHomEquiv _ _ _).injective
  funext a
  cases a with
  | none => exact hK
  | some a =>
    change (FormalCoproduct.cofan _ (attachmentFamily K A N j)).inj (some a) ≫ f =
      (FormalCoproduct.cofan _ (attachmentFamily K A N j)).inj (some a) ≫ g
    simpa only [attachmentCell, dite_eq_right a.2] using hN a.1

/- Unrelated to the cell attachment of the polynomial simplicial resolutions
(`CommAlgCat.attachCells`), which adjoins polynomial generators in a single degree to a simplicial
commutative algebra and is indexed by a `CommAlgCat.CellBoundary`. This one glues a copy of a fixed
object of `FormalCoproduct C` onto `K`, and shares nothing with it but the short name. -/
/-- The simplicial object obtained from `K` by attaching a copy of `N` along each simplex of `U`
outside the subcomplex `A`. -/
private noncomputable def attachCells : SimplicialObject (FormalCoproduct.{w} C) where
  obj j := attachmentLevel K A N j
  map f := attachmentMap K A N d f
  map_id j := by
    apply attachment_hom_ext K A N d j
    · simp only [attachmentInclusion_map, K.map_id, Category.id_comp, Category.comp_id]
    · intro a
      simp only [attachmentCell_map K A N d hd, U.map_id, types_id_apply, Category.comp_id]
  map_comp f g := by
    apply attachment_hom_ext K A N d _
    · rw [attachmentInclusion_map, ← Category.assoc, attachmentInclusion_map,
        Category.assoc, attachmentInclusion_map, K.map_comp, Category.assoc]
    · intro a
      rw [attachmentCell_map K A N d hd, ← Category.assoc, attachmentCell_map K A N d hd,
        attachmentCell_map K A N d hd]
      simp only [U.map_comp, types_comp_apply]

/-- The inclusion of `K` into an attachment. -/
private noncomputable def attachmentι : K ⟶ attachCells K A N d hd where
  app j := attachmentInclusion K A N j
  naturality _ _ f := (attachmentInclusion_map K A N d f).symm

private lemma attachCells_objects (B : Set C)
    (hK : ∀ j i, (K.obj j).obj i ∈ B) (hN : ∀ i, N.obj i ∈ B) :
    ∀ j i, ((attachCells K A N d hd).obj j).obj i ∈ B := by
  rintro j ⟨a, i⟩
  cases a with
  | none => exact hK j i
  | some a => exact hN i

private lemma isIso_attachmentInclusion (j : SimplexCategoryᵒᵖ)
    (h : ∀ a : U.obj j, a ∈ A.obj j) : IsIso (attachmentInclusion K A N j) := by
  let r : attachmentLevel K A N j ⟶ K.obj j :=
    (FormalCoproduct.cofanHomEquiv _ _ _).symm (fun a ↦ match a with
      | none => 𝟙 _
      | some a => False.elim (a.2 (h a.1)))
  have hr : attachmentInclusion K A N j ≫ r = 𝟙 _ :=
    congrFun ((FormalCoproduct.cofanHomEquiv _ _ _).apply_symm_apply _) none
  refine ⟨⟨r, hr, ?_⟩⟩
  apply (FormalCoproduct.cofanHomEquiv _ _ _).injective
  funext a
  cases a with
  | none =>
    change attachmentInclusion K A N j ≫ r ≫ attachmentInclusion K A N j = _
    rw [← Category.assoc, hr, Category.id_comp]
    simp [FormalCoproduct.cofanHomEquiv]
  | some a => exact (a.2 (h a.1)).elim

private lemma subcomplex_map_notMem_of_epi {i j : SimplexCategoryᵒᵖ}
    (f : i ⟶ j) [Epi f.unop] {a : U.obj i} (ha : a ∉ A.obj i) :
    U.map f a ∉ A.obj j := by
  have := isSplitEpi_of_epi f.unop
  let s := section_ f.unop
  have hs : s ≫ f.unop = 𝟙 _ := IsSplitEpi.id _
  have hfs : f ≫ s.op = 𝟙 i := by simpa using congrArg Quiver.Hom.op hs
  intro h
  have h' : U.map s.op (U.map f a) ∈ A.obj i := A.map s.op h
  apply ha
  simpa only [← ConcreteCategory.comp_apply, ← U.map_comp, hfs, U.map_id,
    types_id_apply] using h'

private lemma attachmentMap_components_of_epi
    (hK : ∀ {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) [Epi f.unop]
      (a : (K.obj i).I), IsIso ((K.map f).φ a))
    {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) [Epi f.unop]
    (a : (attachmentLevel K A N i).I) : IsIso ((attachmentMap K A N d f).φ a) := by
  classical
  rcases a with ⟨a, b⟩
  cases a with
  | none =>
    change IsIso ((K.map f).φ b ≫ 𝟙 _)
    simpa only [Category.comp_id] using hK f b
  | some a =>
    have ha : U.map f a.1 ∉ A.obj j := subcomplex_map_notMem_of_epi A f a.2
    change IsIso ((attachmentCell K A N d j (U.map f a.1)).φ b)
    rw [attachmentCell, dite_eq_right ha]
    change IsIso (𝟙 (N.obj b))
    infer_instance

private lemma attachCells_split (hK : Nonempty K.Splitting) :
    Nonempty (attachCells K A N d hd).Splitting := by
  apply (split_iff_components_of_epi _).2
  intro i j f hf a
  exact attachmentMap_components_of_epi K A N d
    (fun g _ b ↦ (split_iff_components_of_epi K).1 hK g.unop b) f.op a

variable {L : SimplicialObject (FormalCoproduct.{w} C)} (t : K ⟶ L)
    (e : ∀ j, U.obj j → (N ⟶ L.obj j))
    (he : ∀ {i j} (f : i ⟶ j) (a : U.obj i),
      e i a ≫ L.map f = e j (U.map f a))
    (hde : ∀ j (a : {a : U.obj j // a ∈ A.obj j}), d j a ≫ t.app j = e j a.1)

/-- One degree of the map out of an attachment determined by a map out of `K` and a compatible
family of maps out of the attached copies of `N`. -/
private noncomputable def attachmentDescApp (j : SimplexCategoryᵒᵖ) :
    attachmentLevel K A N j ⟶ L.obj j :=
  (FormalCoproduct.cofanHomEquiv _ _ _).symm
    (fun a ↦ match a with | none => t.app j | some a => e j a.1)

private lemma attachmentInclusion_desc (j : SimplexCategoryᵒᵖ) :
    attachmentInclusion K A N j ≫ attachmentDescApp K A N t e j = t.app j :=
  congrFun ((FormalCoproduct.cofanHomEquiv _ _ _).apply_symm_apply _) none

include hde in
private lemma attachmentCell_desc (j : SimplexCategoryᵒᵖ) (a : U.obj j) :
    attachmentCell K A N d j a ≫ attachmentDescApp K A N t e j = e j a := by
  classical
  by_cases ha : a ∈ A.obj j
  · rw [attachmentCell, dite_eq_left ha, Category.assoc, attachmentInclusion_desc]
    exact hde j ⟨a, ha⟩
  · rw [attachmentCell, dite_eq_right ha]
    exact congrFun ((FormalCoproduct.cofanHomEquiv _ (attachmentFamily K A N j)
      (L.obj j)).apply_symm_apply _) (some ⟨a, ha⟩)

/-- The map out of an attachment determined by a map out of `K` and a compatible family of maps
out of the attached copies of `N`. -/
private noncomputable def attachmentDesc : attachCells K A N d hd ⟶ L where
  app j := attachmentDescApp K A N t e j
  naturality i j f := by
    change attachmentMap K A N d f ≫ attachmentDescApp K A N t e j =
      attachmentDescApp K A N t e i ≫ L.map f
    apply attachment_hom_ext K A N d i
    · rw [← Category.assoc, attachmentInclusion_map, Category.assoc,
        attachmentInclusion_desc, ← Category.assoc, attachmentInclusion_desc]
      exact t.naturality f
    · intro a
      rw [← Category.assoc, attachmentCell_map K A N d hd,
        attachmentCell_desc K A N d t e hde,
        ← Category.assoc, attachmentCell_desc K A N d t e hde]
      exact (he f a).symm

end Attachment

section BoundaryAttachment

omit [HasPullbacks C]

/-- A map of simplicial sets which is an isomorphism on `n`-truncations admits a lift of any
map out of the `(n + 1)`-skeleton of a simplicial set. -/
theorem exists_lift_skeleton {K L : SSet.{z}} (u : K ⟶ L) (n : ℕ)
    [IsIso ((SSet.truncation n).map u)] (S : SSet.{z})
    (g : (S.skeleton (n + 1)).toSSet ⟶ L) :
    ∃ b : (S.skeleton (n + 1)).toSSet ⟶ K, b ≫ u = g := by
  obtain ⟨e, he⟩ := SSet.exists_iso_skeleton_hom_ι_eq_skAdj_counit S n
  let adj := SSet.skAdj.{z} n
  let g' := adj.homEquiv ((SSet.truncation n).obj S) L (e.hom ≫ g)
  let b' := (adj.homEquiv ((SSet.truncation n).obj S) K).symm
    (g' ≫ inv ((SSet.truncation n).map u))
  refine ⟨e.inv ≫ b', ?_⟩
  have h : b' ≫ u = e.hom ≫ g := by
    apply (adj.homEquiv ((SSet.truncation n).obj S) L).injective
    rw [adj.homEquiv_naturality_right]
    simp [b', g']
  rw [Category.assoc, h]
  simp

/-- A map to the matching object of the `n`-truncation of `K` in degree `n + 1` extends, over the
`(n + 1)`-skeleton of the standard simplex, to a map into `K` itself. -/
theorem exists_matching_boundary
    {D : Type t} [Category.{z} D] (K : SimplicialObject D) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ D,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (T : D) (q : T ⟶ ((SimplicialObject.cosk n).obj K).obj (op ⦋n + 1⦌)) :
    ∃ b : ((Δ[n + 1] : SSet.{z}).skeleton (n + 1)).toSSet ⟶
      K ⋙ coyoneda.obj (op T),
      b ≫ Functor.whiskerRight ((SimplicialObject.coskAdj n).unit.app K)
        (coyoneda.obj (op T)) =
        ((Δ[n + 1] : SSet.{z}).skeleton (n + 1)).ι ≫ SSet.yonedaEquiv.symm q := by
  let u := Functor.whiskerRight ((SimplicialObject.coskAdj n).unit.app K)
    (coyoneda.obj (op T))
  have : IsIso ((SSet.truncation n).map u) := by
    change IsIso (Functor.whiskerRight
      ((SimplicialObject.truncation n).map ((SimplicialObject.coskAdj n).unit.app K))
      (coyoneda.obj (op T)))
    infer_instance
  exact exists_lift_skeleton u n Δ[n + 1]
    (((Δ[n + 1] : SSet.{z}).skeleton (n + 1)).ι ≫ SSet.yonedaEquiv.symm q)

private lemma boundary_le_skeleton (n : ℕ) :
    SSet.boundary.{z} (n + 1) ≤ (Δ[n + 1] : SSet.{z}).skeleton (n + 1) := by
  rw [SSet.boundary_eq_iSup]
  refine iSup_le fun i ↦ ?_
  rw [← SSet.stdSimplex.ofSimplex_yonedaEquiv_δ (n := n) i]
  exact SSet.ofSimplex_le_skeleton _ _ (Nat.lt_succ_self n)

/-- Transport of a simplex of the standard simplex between universes. -/
private def stdSimplexUniverseMap (n : ℕ) (j : SimplexCategoryᵒᵖ)
    (a : (Δ[n] : SSet.{w}).obj j) : (Δ[n] : SSet.{z}).obj j :=
  SSet.stdSimplex.objEquiv.symm (SSet.stdSimplex.objEquiv a)

private lemma stdSimplexUniverseMap_map (n : ℕ) {i j : SimplexCategoryᵒᵖ}
    (f : i ⟶ j) (a : (Δ[n] : SSet.{w}).obj i) :
    stdSimplexUniverseMap n j ((Δ[n] : SSet.{w}).map f a) =
      (Δ[n] : SSet.{z}).map f (stdSimplexUniverseMap n i a) := by
  simp [stdSimplexUniverseMap, SSet.stdSimplex.map_apply]

private lemma stdSimplexUniverseMap_boundary (n : ℕ) (j : SimplexCategoryᵒᵖ)
    (a : (Δ[n] : SSet.{w}).obj j) (ha : a ∈ (SSet.boundary n).obj j) :
    stdSimplexUniverseMap n j a ∈ (SSet.boundary.{z} n).obj j :=
  ha

/-- A simplex of the standard simplex outside the boundary is an epimorphism. -/
private lemma epi_objEquiv_of_notMem_boundary {n m : ℕ}
    (a : (Δ[n] : SSet.{w}).obj (op ⦋m⦌)) (ha : a ∉ (SSet.boundary n).obj (op ⦋m⦌)) :
    Epi (SSet.stdSimplex.objEquiv a) :=
  SimplexCategory.epi_iff_surjective.mpr (by
    change Function.Surjective (SSet.stdSimplex.asOrderHom a)
    simpa [SSet.boundary] using ha)

private lemma stdSimplex_top_not_boundary_eq_id (n : ℕ)
    (a : (Δ[n] : SSet.{w}).obj (op ⦋n⦌))
    (ha : a ∉ (SSet.boundary n).obj (op ⦋n⦌)) :
    a = SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌) := by
  let f : ⦋n⦌ ⟶ ⦋n⦌ := SSet.stdSimplex.objEquiv a
  have : Epi f := epi_objEquiv_of_notMem_boundary a ha
  have : IsIso f := (SimplexCategory.isIso_iff_of_epi f).2 rfl
  have hf : f = 𝟙 _ := SimplexCategory.eq_id_of_isIso f
  apply SSet.stdSimplex.objEquiv.injective
  simpa [f] using hf

private instance boundary_top_complement_subsingleton (n : ℕ) :
    Subsingleton {a : (Δ[n] : SSet.{w}).obj (op ⦋n⦌) //
      a ∉ (SSet.boundary n).obj (op ⦋n⦌)} :=
  ⟨fun a b ↦ Subtype.ext ((stdSimplex_top_not_boundary_eq_id n a.1 a.2).trans
    (stdSimplex_top_not_boundary_eq_id n b.1 b.2).symm)⟩

private lemma isIso_boundaryAttachment_app_of_lt
    (K : SimplicialObject (FormalCoproduct.{w} C)) (n : ℕ) (N : FormalCoproduct.{w} C)
    (d : ∀ j, {a : (Δ[n] : SSet.{w}).obj j // a ∈ (SSet.boundary n).obj j} →
      (N ⟶ K.obj j))
    (hd : ∀ {i j} (f : i ⟶ j)
      (a : {a : (Δ[n] : SSet.{w}).obj i // a ∈ (SSet.boundary n).obj i}),
      d i a ≫ K.map f = d j ⟨(Δ[n] : SSet.{w}).map f a.1, (SSet.boundary n).map f a.2⟩)
    {m : ℕ} (hm : m < n) :
    IsIso ((attachmentι K (SSet.boundary n) N d hd).app (op ⦋m⦌)) := by
  apply isIso_attachmentInclusion
  intro a
  rw [SSet.boundary_obj_eq_univ m n hm]
  trivial

end BoundaryAttachment

section Stabilization

/-- If a morphism of simplicial objects becomes an isomorphism after truncation at level `n`,
then its component at every object of length at most `n` is an isomorphism. -/
theorem isIso_app_of_truncation {D : Type u} [Category.{v} D]
    {K L : SimplicialObject D} (f : K ⟶ L) (n : ℕ)
    [IsIso ((SimplicialObject.truncation n).map f)]
    (a : SimplexCategoryᵒᵖ) (ha : a.unop.len ≤ n) : IsIso (f.app a) :=
  NatIso.isIso_app_of_isIso ((SimplicialObject.truncation n).map f)
    (op ⟨a.unop, ha⟩)

/-- A morphism of simplicial objects whose components in degrees at most `n` are isomorphisms
becomes an isomorphism after truncation at level `n`. -/
private theorem isIso_truncation_map_of_isIso_app {D : Type u} [Category.{v} D]
    {K L : SimplicialObject D} (f : K ⟶ L) (n : ℕ)
    (h : ∀ m ≤ n, IsIso (f.app (op ⦋m⦌))) :
    IsIso ((SimplicialObject.truncation n).map f) := by
  have (a : (SimplexCategory.Truncated n)ᵒᵖ) :
      IsIso (((SimplicialObject.truncation n).map f).app a) :=
    h a.unop.1.len a.unop.property
  apply NatIso.isIso_of_isIso_app

/-- A functor `F : ℕ ⥤ D` is eventually constant from `n` if every transition map
`F.obj m ⟶ F.obj (m + 1)` with `n ≤ m` is an isomorphism. -/
theorem eventually_constant_from
    {D : Type u} [Category.{v} D] (F : ℕ ⥤ D) (n : ℕ)
    (hF : ∀ m, n ≤ m → IsIso (F.map (homOfLE (Nat.le_succ m)))) :
    F.IsEventuallyConstantFrom n := by
  have h : ∀ m (hm : n ≤ m), IsIso (F.map (homOfLE hm)) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simpa using (inferInstance : IsIso (𝟙 (F.obj n)))
    | succ m hm ih =>
      have := hF m hm
      rw [← homOfLE_comp hm (Nat.le_succ m), F.map_comp]
      infer_instance
  exact fun m f ↦ h m (leOfHom f)

/-- A sequence of simplicial objects in which each step is an isomorphism below the current
degree has a colimit, computed degreewise, with the expected identifications. -/
theorem exists_stabilized_simplicial_object
    {D : Type u} [Category.{v} D] (F : ℕ ⥤ SimplicialObject D)
    (hF : ∀ n, IsIso ((SimplicialObject.truncation n).map
      (F.map (homOfLE (Nat.le_succ n))))) :
    ∃ (K : SimplicialObject D) (ι : ∀ n, F.obj n ⟶ K),
      ∃ hobj : ∀ a, K.obj a = (F.obj a.unop.len).obj a,
      (∀ n a, a.unop.len ≤ n → IsIso ((ι n).app a)) ∧
      ∀ a, (ι a.unop.len).app a = eqToHom (hobj a).symm := by
  have h (a : SimplexCategoryᵒᵖ) :
      (F.flip.obj a).IsEventuallyConstantFrom a.unop.len := by
    apply eventually_constant_from
    intro n hn
    have := hF n
    exact isIso_app_of_truncation (F.map (homOfLE (Nat.le_succ n))) n a hn
  let c : ∀ a, ColimitCocone (F.flip.obj a) :=
    fun a ↦ ⟨(h a).cocone, (h a).isColimitCocone⟩
  let t := combineCocones F c
  exact ⟨t.pt, fun n ↦ t.ι.app n, fun a ↦ rfl,
    fun n a ha ↦ (h a).isIso_ι_of_isColimit' (h a).isColimitCocone n (homOfLE ha),
    fun a ↦ (h a).coconeιApp_eq_id⟩

end Stabilization

section Degeneracy

private lemma index_injective_of_isIso
    {D : Type u} [Category.{v} D]
    {A Z : FormalCoproduct.{w} D} (f : A ⟶ Z) [IsIso f] :
    Function.Injective f.f := by
  intro i i' h
  calc
    i = (inv f).f (f.f i) := (inv_f_f f i).symm
    _ = (inv f).f (f.f i') := congrArg _ h
    _ = i' := inv_f_f f i'

private lemma map_f_map_f_of_comp_eq_id {D : Type u} [Category.{v} D]
    (K : SimplicialObject (FormalCoproduct.{w} D)) {a b : SimplexCategory}
    {f : a ⟶ b} {s : b ⟶ a} (hs : s ≫ f = 𝟙 b) (y : (K.obj (op b)).I) :
    (K.map s.op).f ((K.map f.op).f y) = y := by
  change ((K.map f.op ≫ K.map s.op).f y) = y
  rw [← K.map_comp]
  simp [← op_comp, hs]

/-- Two summands in degree `n + 1` with the same image in the matching object have the same
image under every face map to a degree at most `n`. -/
private lemma map_f_eq_of_coskUnit_f_eq
    {X : C} (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (n : ℕ) {m : ℕ} (hm : m ≤ n)
    (s : ⦋m⦌ ⟶ ⦋n + 1⦌) {i i' : (K.obj (op ⦋n + 1⦌)).I}
    (h : (((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌)).f i =
      (((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌)).f i') :
    (K.map s.op).f i = (K.map s.op).f i' := by
  let c := (SimplicialObject.coskAdj n).unit.app K
  have : IsIso (c.app (op ⦋m⦌)) := isIso_app_of_truncation c n _ hm
  have hnat := c.naturality s.op
  have hleft := congrArg (fun h : K.obj (op ⦋n + 1⦌) ⟶
    ((SimplicialObject.cosk n).obj K).obj (op ⦋m⦌) ↦ h.f i) hnat
  have hright := congrArg (fun h : K.obj (op ⦋n + 1⦌) ⟶
    ((SimplicialObject.cosk n).obj K).obj (op ⦋m⦌) ↦ h.f i') hnat
  have htarget :
      (c.app (op ⦋n + 1⦌) ≫ ((SimplicialObject.cosk n).obj K).map s.op).f i =
      (c.app (op ⦋n + 1⦌) ≫ ((SimplicialObject.cosk n).obj K).map s.op).f i' :=
    congrArg (fun x ↦ (((SimplicialObject.cosk n).obj K).map s.op).f x) h
  exact index_injective_of_isIso (c.app (op ⦋m⦌))
    (hleft.trans (htarget.trans hright.symm))

/-- If every summand in degree `n + 1` is pulled back from a lower degree along a surjective
simplicial operator, the map to the matching object has finite fibres. -/
private lemma finite_matching_fibre_of_degenerate
    {X : C} (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (n : ℕ)
    (hdeg : ∀ i : (K.obj (op ⦋n + 1⦌)).I,
      ∃ (m : Fin (n + 1)) (f : ⦋n + 1⦌ ⟶ ⦋m.1⦌),
        Epi f ∧ ∃ y : (K.obj (op ⦋m.1⦌)).I,
          i = (K.map f.op).f y) :
    ∀ j, Finite {i : (K.obj (op ⦋n + 1⦌)).I //
      (((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌)).f i = j} := by
  classical
  let c := (SimplicialObject.coskAdj n).unit.app K
  intro j
  let choosePair (i : (K.obj (op ⦋n + 1⦌)).I) :
      Σ m : Fin (n + 1), {f : ⦋n + 1⦌ ⟶ ⦋m.1⦌ // Epi f} :=
    ⟨Classical.choose (hdeg i),
      ⟨Classical.choose (Classical.choose_spec (hdeg i)),
        (Classical.choose_spec (Classical.choose_spec (hdeg i))).1⟩⟩
  have hinj : Function.Injective
      (fun i : {i : (K.obj (op ⦋n + 1⦌)).I // (c.app _).f i = j} ↦
        choosePair i.1) := by
    intro i i' hh
    rcases i with ⟨i, hi⟩
    rcases i' with ⟨i', hi'⟩
    have hrepr (k : (K.obj (op ⦋n + 1⦌)).I) :
        ∃ y : (K.obj (op ⦋(choosePair k).1.1⦌)).I,
          k = (K.map (choosePair k).2.1.op).f y :=
      (Classical.choose_spec (Classical.choose_spec (hdeg k))).2
    change choosePair i = choosePair i' at hh
    generalize hp : choosePair i = p at hh
    generalize hp' : choosePair i' = p' at hh
    change p = p' at hh
    cases hh
    let f := p.2.1
    have : Epi f := p.2.2
    have : IsSplitEpi f := isSplitEpi_of_epi f
    obtain ⟨y, hy⟩ : ∃ y : (K.obj (op ⦋p.1.1⦌)).I, i = (K.map p.2.1.op).f y := hp ▸ hrepr i
    obtain ⟨y', hy'⟩ : ∃ y : (K.obj (op ⦋p.1.1⦌)).I, i' = (K.map p.2.1.op).f y :=
      hp' ▸ hrepr i'
    let s := section_ f
    have hs : s ≫ f = 𝟙 _ := IsSplitEpi.id f
    apply Subtype.ext
    calc
      i = (K.map f.op).f y := hy
      _ = (K.map f.op).f ((K.map s.op).f i) := by
        rw [hy, map_f_map_f_of_comp_eq_id K hs]
      _ = (K.map f.op).f ((K.map s.op).f i') :=
        congrArg _ (map_f_eq_of_coskUnit_f_eq K n (Nat.lt_succ_iff.mp p.1.2) s (hi.trans hi'.symm))
      _ = (K.map f.op).f y' := by
        rw [hy', map_f_map_f_of_comp_eq_id K hs]
      _ = i' := hy'.symm
  exact Finite.of_injective _ hinj

/-- Every summand above degree `n` is pulled back from a degree at most `n` along a surjective
simplicial operator. -/
private def DegenerateAbove
    {X : C} (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (n : ℕ) : Prop :=
  ∀ (m : ℕ), n < m → ∀ i : (K.obj (op ⦋m⦌)).I,
    ∃ (k : Fin (n + 1)) (f : ⦋m⦌ ⟶ ⦋k.1⦌), Epi f ∧
      ∃ y : (K.obj (op ⦋k.1⦌)).I, i = (K.map f.op).f y

private lemma finite_matching_fibre_of_degenerateAbove
    {X : C} (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (n : ℕ)
    (hK : DegenerateAbove K n) :
    ∀ j, Finite {i : (K.obj (op ⦋n + 1⦌)).I //
      (((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌)).f i = j} :=
  finite_matching_fibre_of_degenerate K n (hK (n + 1) (by omega))

omit [HasPullbacks C] in
private lemma degenerateAbove_attachment
    {X : C} (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (n : ℕ)
    (N : FormalCoproduct.{w} (Over X))
    (d : ∀ j, {a : (Δ[n + 1] : SSet.{w}).obj j //
      a ∈ (SSet.boundary (n + 1)).obj j} → (N ⟶ K.obj j))
    (hd : ∀ {i j} (f : i ⟶ j)
      (a : {a : (Δ[n + 1] : SSet.{w}).obj i //
        a ∈ (SSet.boundary (n + 1)).obj i}),
      d i a ≫ K.map f = d j ⟨(Δ[n + 1] : SSet.{w}).map f a.1,
        (SSet.boundary (n + 1)).map f a.2⟩)
    (hK : DegenerateAbove K n) :
    DegenerateAbove (attachCells K (SSet.boundary (n + 1)) N d hd) (n + 1) := by
  classical
  intro m hm i
  rcases i with ⟨o, b⟩
  cases o with
  | none =>
    obtain ⟨k, f, hf, y, hy⟩ := hK m (by omega) b
    refine ⟨⟨k.1, by omega⟩, f, hf, ⟨none, y⟩, ?_⟩
    change (⟨none, b⟩ : (attachmentLevel K (SSet.boundary (n + 1)) N
      (op ⦋m⦌)).I) =
      (attachmentInclusion K (SSet.boundary (n + 1)) N _).f
        ((K.map f.op).f y)
    simpa only [attachmentInclusion, FormalCoproduct.cofan_inj] using
      congrArg (fun x ↦ (⟨none, x⟩ :
        (attachmentLevel K (SSet.boundary (n + 1)) N
          (op ⦋m⦌)).I)) hy
  | some a =>
    let f : ⦋m⦌ ⟶ ⦋n + 1⦌ := SSet.stdSimplex.objEquiv a.1
    have hf : Epi f := epi_objEquiv_of_notMem_boundary a.1 a.2
    let a₀ : (Δ[n + 1] : SSet.{w}).obj (op ⦋n + 1⦌) :=
      SSet.stdSimplex.objEquiv.symm (𝟙 _)
    have ha₀ : a₀ ∉ (SSet.boundary (n + 1)).obj (op ⦋n + 1⦌) :=
      SSet.stdSimplex.notMem_boundary (n + 1)
    refine ⟨⟨n + 1, by omega⟩, f, hf, ⟨some ⟨a₀, ha₀⟩, b⟩, ?_⟩
    have hmap : (Δ[n + 1] : SSet.{w}).map f.op a₀ = a.1 := by
      change SSet.stdSimplex.objEquiv.symm (f ≫ 𝟙 _) = a.1
      simp [f]
    change (⟨some a, b⟩ : (attachmentLevel K (SSet.boundary (n + 1)) N
      (op ⦋m⦌)).I) =
      (attachmentCell K (SSet.boundary (n + 1)) N d _
        ((Δ[n + 1] : SSet.{w}).map f.op a₀)).f b
    rw [hmap, attachmentCell, dite_eq_right a.2]
    rfl

end Degeneracy

section Step

/-- If a map `i : A ⟶ A'` whose image under `F` is an isomorphism factors the unit of `F ⊣ G` at
`A` through `d`, then `d` composed with `G.map (F.map i)` is the unit at `A'`. -/
theorem comp_map_eq_unit {D E : Type*} [Category D] [Category E]
    {F : D ⥤ E} {G : E ⥤ D} (adj : F ⊣ G) {A A' : D}
    (i : A ⟶ A') [IsIso (F.map i)] (d : A' ⟶ G.obj (F.obj A))
    (h : i ≫ d = adj.unit.app A) :
    d ≫ G.map (F.map i) = adj.unit.app A' := by
  apply (adj.homEquiv _ _).symm.injective
  have he : F.map i ≫ (adj.homEquiv _ _).symm d = 𝟙 _ := by
    rw [← adj.homEquiv_naturality_left_symm, h]
    simp
  rw [adj.homEquiv_naturality_right_symm]
  apply (cancel_epi (F.map i)).mp
  simp [← Category.assoc, he]

/-- A map to the matching object in degree `n + 1` gives compatible cells on the boundary of the
standard simplex in `K`, and compatible maps on the whole standard simplex in the matching
object, sending the top simplex to the given map. -/
private lemma exists_boundary_cells
    {X : C} (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (n : ℕ)
    (N : FormalCoproduct.{w} (Over X))
    (q : N ⟶ ((SimplicialObject.cosk n).obj K).obj (op ⦋n + 1⦌)) :
    ∃ (d : ∀ j, {a : (Δ[n + 1] : SSet.{w}).obj j //
        a ∈ (SSet.boundary (n + 1)).obj j} → (N ⟶ K.obj j)),
      (∀ {i j} (f : i ⟶ j)
        (a : {a : (Δ[n + 1] : SSet.{w}).obj i // a ∈ (SSet.boundary (n + 1)).obj i}),
        d i a ≫ K.map f =
          d j ⟨(Δ[n + 1] : SSet.{w}).map f a.1, (SSet.boundary (n + 1)).map f a.2⟩) ∧
      ∃ (e : ∀ j, (Δ[n + 1] : SSet.{w}).obj j →
        (N ⟶ ((SimplicialObject.cosk n).obj K).obj j)),
      (∀ {i j} (f : i ⟶ j) (a : (Δ[n + 1] : SSet.{w}).obj i),
        e i a ≫ ((SimplicialObject.cosk n).obj K).map f =
          e j ((Δ[n + 1] : SSet.{w}).map f a)) ∧
      (∀ j a, d j a ≫ ((SimplicialObject.coskAdj n).unit.app K).app j = e j a.1) ∧
      e (op ⦋n + 1⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌)) = q := by
  obtain ⟨b, hb⟩ := exists_matching_boundary K n N q
  let d : ∀ j, {a : (Δ[n + 1] : SSet.{max v w}).obj j //
      a ∈ (SSet.boundary (n + 1)).obj j} → (N ⟶ K.obj j) :=
    fun j a ↦ b.app j ⟨a.1, (boundary_le_skeleton n) j a.2⟩
  have hd : ∀ {i j} (f : i ⟶ j)
      (a : {a : (Δ[n + 1] : SSet.{max v w}).obj i //
        a ∈ (SSet.boundary (n + 1)).obj i}),
      d i a ≫ K.map f =
        d j ⟨(Δ[n + 1] : SSet.{max v w}).map f a.1,
          (SSet.boundary (n + 1)).map f a.2⟩ := fun {i _} f a ↦
    (NatTrans.naturality_apply b f ⟨a.1, (boundary_le_skeleton n) i a.2⟩).symm
  let τ : (Δ[n + 1] : SSet.{max v w}) ⟶
      ((SimplicialObject.cosk n).obj K) ⋙ coyoneda.obj (op N) :=
    SSet.yonedaEquiv.symm q
  refine ⟨fun j a ↦ d j ⟨stdSimplexUniverseMap (n + 1) j a.1,
      stdSimplexUniverseMap_boundary (n + 1) j a.1 a.2⟩, ?_,
    fun j a ↦ τ.app j (stdSimplexUniverseMap (n + 1) j a), ?_, ?_, ?_⟩
  · intro i j f a
    simpa only [stdSimplexUniverseMap_map] using
      hd f ⟨stdSimplexUniverseMap (n + 1) i a.1,
        stdSimplexUniverseMap_boundary (n + 1) i a.1 a.2⟩
  · intro i j f a
    simp [stdSimplexUniverseMap_map, Functor.comp_map, coyoneda]
  · exact fun j a ↦
      congrArg (fun f ↦ f ⟨stdSimplexUniverseMap (n + 1) j a.1,
        (boundary_le_skeleton n) j
          (stdSimplexUniverseMap_boundary (n + 1) j a.1 a.2)⟩)
        (NatTrans.congr_app hb j)
  · change q ≫ ((SimplicialObject.cosk n).obj K).map (𝟙 _) = q
    simp

/-- In degree `n + 1`, the map from a boundary attachment of a covering `N` of the matching object
to the matching object is covering. -/
private lemma isCoveringOver_attachmentDesc_top
    {X : C} (J : Pretopology C) (B : Set C)
    (hadjoin : ∀ {ι : Type w} (V : ι → C) {U : C} (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ g : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈ J U)
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (n : ℕ)
    (N : FormalCoproduct.{w} (Over X))
    (q : N ⟶ ((SimplicialObject.cosk n).obj K).obj (op ⦋n + 1⦌))
    (d : ∀ j, {a : (Δ[n + 1] : SSet.{w}).obj j //
        a ∈ (SSet.boundary (n + 1)).obj j} → (N ⟶ K.obj j))
    (hd : ∀ {i j} (f : i ⟶ j)
      (a : {a : (Δ[n + 1] : SSet.{w}).obj i // a ∈ (SSet.boundary (n + 1)).obj i}),
      d i a ≫ K.map f =
        d j ⟨(Δ[n + 1] : SSet.{w}).map f a.1, (SSet.boundary (n + 1)).map f a.2⟩)
    (e : ∀ j, (Δ[n + 1] : SSet.{w}).obj j →
      (N ⟶ ((SimplicialObject.cosk n).obj K).obj j))
    (he : ∀ {i j} (f : i ⟶ j) (a : (Δ[n + 1] : SSet.{w}).obj i),
      e i a ≫ ((SimplicialObject.cosk n).obj K).map f =
        e j ((Δ[n + 1] : SSet.{w}).map f a))
    (hde : ∀ j a, d j a ≫ ((SimplicialObject.coskAdj n).unit.app K).app j = e j a.1)
    (heq : e (op ⦋n + 1⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌)) = q)
    (hB : ∀ i, ((K.obj (op ⦋n + 1⦌)).obj i).left ∈ B) (hN : ∀ i, (N.obj i).left ∈ B)
    (hq : IsCoveringOver J q)
    (hfinite : ∀ j, Finite {i : (K.obj (op ⦋n + 1⦌)).I //
      (((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌)).f i = j}) :
    IsCoveringOver J ((attachmentDesc K (SSet.boundary (n + 1)) N d hd
      ((SimplicialObject.coskAdj n).unit.app K) e he hde).app (op ⦋n + 1⦌)) := by
  classical
  let c := (SimplicialObject.coskAdj n).unit.app K
  let S := {a : (Δ[n + 1] : SSet.{w}).obj (op ⦋n + 1⦌) //
    a ∉ (SSet.boundary (n + 1)).obj (op ⦋n + 1⦌)}
  have : Subsingleton S := boundary_top_complement_subsingleton (n + 1)
  let a₀ : S := ⟨SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌),
    SSet.stdSimplex.notMem_boundary (n + 1)⟩
  have hp : (attachmentDesc K (SSet.boundary (n + 1)) N d hd c e he hde).app (op ⦋n + 1⦌) =
      (FormalCoproduct.cofanHomEquiv (Option S)
        (attachmentFamily K (SSet.boundary (n + 1)) N (op ⦋n + 1⦌))
        _).symm (fun o ↦ match o with | none => c.app _ | some _ => q) := by
    simp only [attachmentDesc, attachmentDescApp]
    congr 1
    funext o
    cases o with
    | none => rfl
    | some b =>
      obtain rfl : b = a₀ := Subsingleton.elim _ _
      exact heq
  rw [hp]
  exact covering_of_option_cofan_with_finite_old_fibres (S := S) J B hadjoin a₀
    (Z := ((SimplicialObject.cosk n).obj K).obj (op ⦋n + 1⦌))
    (attachmentFamily K (SSet.boundary (n + 1)) N (op ⦋n + 1⦌))
    (fun o ↦ match o with | none => c.app _ | some _ => q)
    (fun o ↦ match o with | none => hB | some _ => hN) hq hfinite

/-- A morphism of simplicial objects which is an isomorphism up to degree `n` induces an
isomorphism of `n`-coskeleta. -/
private lemma isIso_cosk_map_of_isIso_app {X : C}
    {K L : SimplicialObject (FormalCoproduct.{w} (Over X))} (n : ℕ) (f : K ⟶ L)
    (h : ∀ m ≤ n, IsIso (f.app (op ⦋m⦌))) : IsIso ((SimplicialObject.cosk n).map f) := by
  have := isIso_truncation_map_of_isIso_app f n h
  change IsIso ((SimplicialObject.Truncated.cosk n).map ((SimplicialObject.truncation n).map f))
  infer_instance

/-- If `ι : K ⟶ L` is an isomorphism up to degree `n` and factors the unit of `K` through
`p : L ⟶ cosk n K`, and `p` is covering in degree `n + 1`, then so is the unit of `L`. -/
private lemma isCoveringOver_coskUnit_of_factor {X : C} (J : Pretopology C)
    {K L : SimplicialObject (FormalCoproduct.{w} (Over X))} (n : ℕ) (ι : K ⟶ L)
    (p : L ⟶ (SimplicialObject.cosk n).obj K)
    (hfd : ι ≫ p = (SimplicialObject.coskAdj n).unit.app K)
    (hι : ∀ m ≤ n, IsIso (ι.app (op ⦋m⦌)))
    (hp : IsCoveringOver J (p.app (op ⦋n + 1⦌))) :
    IsCoveringOver J (((SimplicialObject.coskAdj n).unit.app L).app (op ⦋n + 1⦌)) := by
  have := isIso_truncation_map_of_isIso_app ι n hι
  have := isIso_cosk_map_of_isIso_app n ι hι
  have hc := hp.comp_isIso J (((SimplicialObject.cosk n).map ι).app (op ⦋n + 1⦌))
  have heq := NatTrans.congr_app
    (comp_map_eq_unit (SimplicialObject.coskAdj n) ι p hfd) (op ⦋n + 1⦌)
  exact heq ▸ hc

/-- One step of the construction: attach to `K`, along the boundary of the standard simplex in
degree `n + 1`, a covering `N` of its matching object. The result is split, degenerate above
degree `n + 1`, unchanged below degree `n + 1`, and its own map to the matching object of its
`n`-truncation is covering. -/
private theorem exists_split_matching_attachment
    {X : C} (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (n : ℕ)
    (N : FormalCoproduct.{w} (Over X))
    (q : N ⟶ ((SimplicialObject.cosk n).obj K).obj (op ⦋n + 1⦌))
    (hK : Nonempty K.Splitting) (B : Set C)
    (hB : ∀ m i, ((K.obj (op ⦋m⦌)).obj i).left ∈ B)
    (hN : ∀ i, (N.obj i).left ∈ B)
    (J : Pretopology C)
    (hadjoin : ∀ {ι : Type w} (V : ι → C) {U : C} (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ g : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈ J U)
    (hq : IsCoveringOver J q)
    (hdeg : DegenerateAbove K n)
    (hfinite : ∀ j, Finite {i : (K.obj (op ⦋n + 1⦌)).I //
      (((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌)).f i = j}) :
    ∃ L : SimplicialObject (FormalCoproduct.{w} (Over X)),
      ∃ ι : K ⟶ L,
      ∃ p : L ⟶ (SimplicialObject.cosk n).obj K,
      ∃ e : N ⟶ L.obj (op ⦋n + 1⦌),
        ι ≫ p = (SimplicialObject.coskAdj n).unit.app K ∧
        e ≫ p.app (op ⦋n + 1⦌) = q ∧
        Function.Injective e.f ∧ (∀ i, IsIso (e.φ i)) ∧
        Nonempty L.Splitting ∧
        (∀ m < n + 1, IsIso (ι.app (op ⦋m⦌))) ∧
        (∀ m i, ((L.obj (op ⦋m⦌)).obj i).left ∈ B) ∧
        DegenerateAbove L (n + 1) ∧
        IsCoveringOver J
          (((SimplicialObject.coskAdj n).unit.app L).app (op ⦋n + 1⦌)) := by
  classical
  let c := (SimplicialObject.coskAdj n).unit.app K
  obtain ⟨d', hd', t, ht, hdt, htq⟩ := exists_boundary_cells K n N q
  let ι := attachmentι K (SSet.boundary (n + 1)) N d' hd'
  let p := attachmentDesc K (SSet.boundary (n + 1)) N d' hd' c t ht hdt
  let a : (Δ[n + 1] : SSet.{w}).obj (op ⦋n + 1⦌) :=
    SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌)
  have ha : a ∉ (SSet.boundary (n + 1)).obj (op ⦋n + 1⦌) :=
    SSet.stdSimplex.notMem_boundary (n + 1)
  let e : N ⟶ (attachCells K (SSet.boundary (n + 1)) N d' hd').obj (op ⦋n + 1⦌) :=
    attachmentCell K (SSet.boundary (n + 1)) N d' _ a
  have hfd : ι ≫ p = c :=
    NatTrans.ext <| funext fun j ↦ attachmentInclusion_desc K (SSet.boundary (n + 1)) N c t j
  refine ⟨attachCells K (SSet.boundary (n + 1)) N d' hd',
    ι, p, e, hfd, ?_, ?_, ?_,
    attachCells_split K (SSet.boundary (n + 1)) N d' hd' hK, ?_, ?_,
    degenerateAbove_attachment K n N d' hd' hdeg, ?_⟩
  · change attachmentCell K (SSet.boundary (n + 1)) N d' _ a ≫
      attachmentDescApp K (SSet.boundary (n + 1)) N c t _ = q
    exact (attachmentCell_desc K (SSet.boundary (n + 1)) N d' c t hdt _ a).trans htq
  · intro i j hij
    dsimp [e, attachmentCell] at hij
    simp only [dite_eq_right ha, FormalCoproduct.cofan_inj] at hij
    cases hij
    rfl
  · intro i
    dsimp [e, attachmentCell]
    rw [dite_eq_right ha]
    change IsIso (𝟙 (N.obj i))
    infer_instance
  · exact fun m hm ↦ isIso_boundaryAttachment_app_of_lt K (n + 1) N d' hd' hm
  · exact fun m i ↦ attachCells_objects K (SSet.boundary (n + 1)) N d' hd'
      {Y : Over X | Y.left ∈ B} (fun j i ↦ hB j.unop.len i) hN _ i
  · exact isCoveringOver_coskUnit_of_factor J n ι p hfd
      (fun m hm ↦ isIso_boundaryAttachment_app_of_lt K (n + 1) N d' hd' (Nat.lt_succ_of_le hm))
      (isCoveringOver_attachmentDesc_top J B hadjoin K n N q d' hd' t ht hdt htq
        (hB (n + 1)) hN hq hfinite)

private lemma covering_over_of_eqToHom {X : C}
    {A A' Z : FormalCoproduct.{w} (Over X)} (J : Pretopology C)
    (f : A ⟶ A') (h : A = A') (hf : f = eqToHom h)
    (q : A' ⟶ Z) (hq : IsCoveringOver J (f ≫ q)) :
    IsCoveringOver J q := by
  subst A'
  subst f
  simpa using hq

omit [HasPullbacks C] in
/-- A constant simplicial object is degenerate above degree `0`. -/
private lemma degenerateAbove_const {X : C} (T : FormalCoproduct.{w} (Over X)) :
    DegenerateAbove ((SimplicialObject.const _).obj T) 0 := by
  intro m hm i
  let f : ⦋m⦌ ⟶ ⦋0⦌ := SimplexCategory.isTerminalZero.from _
  have hf : Epi f := SimplexCategory.epi_iff_surjective.mpr fun j ↦ ⟨0, by
    change (0 : Fin 1) = j
    omega⟩
  exact ⟨⟨0, by omega⟩, f, hf, i, rfl⟩

/-- The inductive step of the construction: a split simplicial object with terms in `B`,
degenerate above degree `n`, maps to one degenerate above degree `n + 1` by a map which is an
isomorphism up to degree `n`, and whose map to the matching object in degree `n + 1` is
covering. -/
private lemma exists_next_attachment {X : C} (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (V : ι → C) (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J U)
    (hadjoin : ∀ {ι : Type w} (V : ι → C) {U : C} (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ g : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈ J U)
    (n : ℕ) (Q : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hQB : ∀ a i, ((Q.obj a).obj i).left ∈ B) (hQs : Nonempty Q.Splitting)
    (hQd : DegenerateAbove Q n) :
    ∃ L : SimplicialObject (FormalCoproduct.{w} (Over X)),
      ((∀ a i, ((L.obj a).obj i).left ∈ B) ∧ Nonempty L.Splitting ∧
        DegenerateAbove L (n + 1)) ∧
      ∃ f : Q ⟶ L, IsIso ((SimplicialObject.truncation n).map f) ∧
        IsCoveringOver J
          (((SimplicialObject.coskAdj n).unit.app L).app (op ⦋n + 1⦌)) := by
  obtain ⟨N, q, hN, hq⟩ := exists_covering_refinement_in_B J B hcover
    (((SimplicialObject.cosk n).obj Q).obj (op ⦋n + 1⦌))
  obtain ⟨L, f, p, e, hfp, heq, hinj, heiso, hsplit, hlo, hB, hdeg, hcov⟩ :=
    exists_split_matching_attachment Q n N q hQs B
      (fun m i ↦ hQB (op ⦋m⦌) i) hN J hadjoin hq hQd
      (finite_matching_fibre_of_degenerateAbove Q n hQd)
  exact ⟨L, ⟨fun a i ↦ hB a.unop.len i, hsplit, hdeg⟩, f,
    isIso_truncation_map_of_isIso_app f n fun m hm ↦ hlo m (Nat.lt_succ_of_le hm), hcov⟩

/-- If `ι : K ⟶ L` is an isomorphism up to degree `n` and the map from `K` to its matching object
is covering in degree `n + 1`, then so is its composite with the map from `L` to its matching
object. -/
private lemma isCoveringOver_comp_coskUnit {X : C} (J : Pretopology C)
    {K L : SimplicialObject (FormalCoproduct.{w} (Over X))} (n : ℕ) (ι : K ⟶ L)
    (hι : ∀ m ≤ n, IsIso (ι.app (op ⦋m⦌)))
    (hK : IsCoveringOver J (((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌))) :
    IsCoveringOver J (ι.app (op ⦋n + 1⦌) ≫
      ((SimplicialObject.coskAdj n).unit.app L).app (op ⦋n + 1⦌)) := by
  have := isIso_cosk_map_of_isIso_app n ι hι
  have hc := hK.comp_isIso J (((SimplicialObject.cosk n).map ι).app (op ⦋n + 1⦌))
  have hn := NatTrans.congr_app
    ((SimplicialObject.coskAdj n).unit.naturality ι) (op ⦋n + 1⦌)
  dsimp at hn
  exact hn.symm ▸ hc

end Step

/-- **Stacks Project, Tag 0DAV.** If the objects in `B` cover every object of a site and adjoining
one more morphism whose source lies in `B` preserves such a covering, then every object has a
hypercovering all of whose constituent objects lie in `B`. -/
@[stacks 0DAV]
theorem exists_hypercovering_with_objects_in
    (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (V : ι → C) (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J U)
    (hadjoin : ∀ {ι : Type w} (V : ι → C) {U : C} (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ g : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈ J U)
    (X : C) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering J K ∧
        ∀ (n : ℕ) (i : (K.obj (op (SimplexCategory.mk n))).I),
          ((K.obj (op (SimplexCategory.mk n))).obj i).left ∈ B := by
  classical
  have : HasFiniteLimits (Over X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  obtain ⟨T, hT, hTcover⟩ := exists_initial_B_cover J B hcover X
  let K₀ : SimplicialObject (FormalCoproduct.{w} (Over X)) :=
    (SimplicialObject.const _).obj T
  let Good : ℕ → SimplicialObject (FormalCoproduct.{w} (Over X)) → Prop :=
    fun n K ↦
      (∀ a i, ((K.obj a).obj i).left ∈ B) ∧
      Nonempty K.Splitting ∧ DegenerateAbove K n
  have hK₀ : Good 0 K₀ := by
    refine ⟨fun _ i ↦ hT i, (split_iff_components_of_epi K₀).2 fun _ _ i ↦ ?_,
      degenerateAbove_const T⟩
    change IsIso (𝟙 (T.obj i))
    infer_instance
  have hs : ∀ n (Q : {K // Good n K}),
      ∃ R : {L // Good (n + 1) L}, ∃ f : Q.1 ⟶ R.1,
        IsIso ((SimplicialObject.truncation n).map f) ∧
        IsCoveringOver J
          (((SimplicialObject.coskAdj n).unit.app R.1).app (op ⦋n + 1⦌)) := by
    intro n Q
    obtain ⟨L, hL, f, hf, hc⟩ :=
      exists_next_attachment J B hcover hadjoin n Q.1 Q.2.1 Q.2.2.1 Q.2.2.2
    exact ⟨⟨L, hL⟩, f, hf, hc⟩
  choose next incl htr hcov using hs
  let seq : (n : ℕ) → {K // Good n K} :=
    Nat.rec ⟨K₀, hK₀⟩ (fun n Q ↦ next n Q)
  let F : ℕ ⥤ SimplicialObject (FormalCoproduct.{w} (Over X)) :=
    Functor.ofSequence (fun n ↦ incl n (seq n))
  have hF : ∀ n, IsIso ((SimplicialObject.truncation n).map
      (F.map (homOfLE (Nat.le_succ n)))) := by
    intro n
    rw [show F.map (homOfLE (Nat.le_succ n)) = incl n (seq n) from
      Functor.ofSequence_map_homOfLE_succ _ n]
    exact htr n (seq n)
  obtain ⟨K, ι, hobj, hι, hιeq⟩ := exists_stabilized_simplicial_object F hF
  have hKB : ∀ a i, ((K.obj a).obj i).left ∈ B := by
    intro a
    rw [hobj a]
    exact (seq a.unop.len).2.1 a
  refine ⟨K, ⟨?_, ?_⟩, fun n i ↦ hKB (op ⦋n⦌) i⟩
  · have hc : IsCoveringOver J
        ((ι 0).app (op ⦋0⦌) ≫ terminal.from (K.obj (op ⦋0⦌))) := by
      rw [terminal.comp_from]
      change IsCoveringOver J (terminal.from T)
      exact hTcover
    exact covering_over_of_eqToHom J ((ι 0).app (op ⦋0⦌))
      (hobj (op ⦋0⦌)).symm (hιeq (op ⦋0⦌)) (terminal.from _) hc
  · exact fun n ↦ covering_over_of_eqToHom J ((ι (n + 1)).app (op ⦋n + 1⦌))
      (hobj (op ⦋n + 1⦌)).symm (hιeq (op ⦋n + 1⦌)) _
      (isCoveringOver_comp_coskUnit J n (ι (n + 1))
        (fun m hm ↦ hι (n + 1) _ (Nat.le_succ_of_le hm)) (hcov n (seq n)))

end Stacks.CategoryTheory.Hypercovering

end
