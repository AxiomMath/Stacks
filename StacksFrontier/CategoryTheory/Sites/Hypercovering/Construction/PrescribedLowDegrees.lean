module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects
import all StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.ObjectsInCollection
import all StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects

/-!
# Hypercoverings with prescribed terms in degrees zero and one

The construction of [Stacks, Tag 0DAV] starts from a covering `T` of `X` by objects of a
collection `B`, regarded as a constant simplicial object, and then attaches, degree by degree,
the cells of coverings of the matching objects by objects of `B`. The first two choices — the
covering `T` in degree zero and the covering `N` of the degree-one matching object `T × T` — can be
prescribed. The proof of [Stacks, Tag 0DCB] uses exactly this: it takes `K_0 = {U}_{U ∈ B}` and a
degree-one term containing, for every pair of arrows `a : U ⟶ V`, `b : U ⟶ W` of `B`, a summand
`U` whose two faces are `a` and `b`, as in the proof of [Stacks, Tag 0DAX].

## Main results

* `Stacks.CategoryTheory.Hypercovering.exists_hypercovering_with_objects_in_of_lowDegrees`: the
  construction of Tag 0DAV with prescribed degree-zero covering and degree-one cells.
* `Stacks.CategoryTheory.Hypercovering.exists_hypercoveringOfTerminal_fullSubcategory`: for a
  fully faithful `i : B ⥤ D` whose objects cover every object of `D`, a hypercovering of the final
  presheaf on `D` which is the image of a simplicial object `L` of `SR(B)`, such that every object
  `U` of `B` maps to `L_0`, and every arrow `a : U ⟶ V` of `B` comes from a map `U ⟶ L_1` whose
  two faces are `a` followed by the map of `V` and the map of `U`.

## Implementation notes

The degree-one cells are attached along the boundary of the standard `1`-simplex to the constant
simplicial object on `T`, by the attachment step of Tag 0DAV; the face maps of the attached cells
are then read off the projections of the matching object `zeroMatchingπ`. All later steps of the
construction are those of Tag 0DAV and do not change degrees zero and one. For a site `D`
without a final object the construction is carried out, as in the proof of Tag 0DAX, in the
presheaf category over the final presheaf, and the result is lifted back along the Yoneda
embedding.

## References

* [Stacks Project, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV)
* [Stacks Project, Tag 0DAX](https://stacks.math.columbia.edu/tag/0DAX)
* [Stacks Project, Tag 0DCB](https://stacks.math.columbia.edu/tag/0DCB)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

section Generic

attribute [-instance] CategoryTheory.ReflQuiver.toQuiver

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

omit [HasPullbacks C] in
/-- A constant simplicial formal coproduct is split. -/
private theorem nonempty_splitting_const {X : C} (T : FormalCoproduct.{w} (Over X)) :
    Nonempty ((SimplicialObject.const _).obj T).Splitting := by
  apply (split_iff_components_of_epi ((SimplicialObject.const _).obj T)).2
  intro m n f hf i
  show IsIso (𝟙 (T.obj i))
  infer_instance

private lemma exists_attachment_step (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (V : ι → C) (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J U)
    (hadjoin : ∀ {ι : Type w} (V : ι → C) {U : C} (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ g : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈ J U)
    {X : C} (n : ℕ) (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hB : ∀ a i, ((K.obj a).obj i).left ∈ B) (hK : Nonempty K.Splitting)
    (hdeg : DegenerateAbove K n) :
    ∃ L : SimplicialObject (FormalCoproduct.{w} (Over X)),
      ((∀ a i, ((L.obj a).obj i).left ∈ B) ∧ Nonempty L.Splitting ∧ DegenerateAbove L (n + 1)) ∧
      ∃ f : K ⟶ L, IsIso ((SimplicialObject.truncation n).map f) ∧
        IsCoveringOver J (((SimplicialObject.coskAdj n).unit.app L).app (op ⦋n + 1⦌)) := by
  obtain ⟨N, q, hN, hq⟩ := exists_covering_refinement_in_B J B hcover
    (((SimplicialObject.cosk n).obj K).obj (op ⦋n + 1⦌))
  obtain ⟨L, f, p, e, hfp, heq, hinj, heiso, hsplit, hlo, hBL, hdeg', hcov⟩ :=
    exists_split_matching_attachment K n N q hK B (fun m i ↦ hB (op ⦋m⦌) i) hN J hadjoin hq hdeg
      (finite_matching_fibre_of_degenerateAbove K n hdeg)
  exact ⟨L, ⟨fun a i ↦ hBL a.unop.len i, hsplit, hdeg'⟩, f,
    isIso_truncation_map_of_isIso_app f n fun m hm ↦ hlo m (Nat.lt_succ_of_le hm), hcov⟩

private lemma exists_hypercovering_of_sequence (J : Pretopology C) (B : Set C) {X : C}
    (F : ℕ ⥤ SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hF : ∀ n, IsIso ((SimplicialObject.truncation n).map (F.map (homOfLE (Nat.le_succ n)))))
    (hcovF : ∀ n, IsCoveringOver J
      (((SimplicialObject.coskAdj n).unit.app (F.obj (n + 1))).app (op ⦋n + 1⦌)))
    (hB : ∀ n a i, (((F.obj n).obj a).obj i).left ∈ B)
    (h₀ : IsCoveringOver J (terminal.from ((F.obj 0).obj (op ⦋0⦌)))) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)), IsHypercovering J K ∧
      (∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I), ((K.obj (op ⦋n⦌)).obj i).left ∈ B) ∧
      ∀ n, Nonempty (F.obj n ⟶ K) := by
  have : HasFiniteLimits (Over X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  obtain ⟨K, ι, hobj, hι, hιeq⟩ := exists_stabilized_simplicial_object F hF
  have hKB : ∀ a i, ((K.obj a).obj i).left ∈ B := by
    intro a
    rw [hobj a]
    exact hB a.unop.len a
  refine ⟨K, ⟨?_, ?_⟩, fun n i ↦ hKB (op ⦋n⦌) i, fun n ↦ ⟨ι n⟩⟩
  · refine covering_over_of_eqToHom J ((ι 0).app (op ⦋0⦌))
      (hobj (op ⦋0⦌)).symm (hιeq (op ⦋0⦌)) (terminal.from _) ?_
    rwa [terminal.comp_from]
  · intro n
    have := isIso_truncation_map_of_isIso_app (ι (n + 1)) n fun m hm ↦
      hι (n + 1) _ (Nat.le_succ_of_le hm)
    have : IsIso ((SimplicialObject.cosk n).map (ι (n + 1))) := by
      show IsIso ((SimplicialObject.Truncated.cosk n).map
        ((SimplicialObject.truncation n).map (ι (n + 1))))
      infer_instance
    have hc := (hcovF n).comp_isIso J
      (((SimplicialObject.cosk n).map (ι (n + 1))).app (op ⦋n + 1⦌))
    have hn := NatTrans.congr_app
      ((SimplicialObject.coskAdj n).unit.naturality (ι (n + 1))) (op ⦋n + 1⦌)
    dsimp at hn
    have hcomp : IsCoveringOver J
        ((ι (n + 1)).app (op ⦋n + 1⦌) ≫
          ((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌)) := hn.symm ▸ hc
    exact covering_over_of_eqToHom J ((ι (n + 1)).app (op ⦋n + 1⦌))
      (hobj (op ⦋n + 1⦌)).symm (hιeq (op ⦋n + 1⦌)) _ hcomp

private lemma exists_hypercovering_of_attachment (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (V : ι → C) (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J U)
    (hadjoin : ∀ {ι : Type w} (V : ι → C) {U : C} (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ g : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈ J U)
    {X : C} (T : FormalCoproduct.{w} (Over X)) (hT : ∀ i, (T.obj i).left ∈ B)
    (hTcover : IsCoveringOver J (terminal.from T))
    (L : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hBL : ∀ m i, ((L.obj (op ⦋m⦌)).obj i).left ∈ B) (hsplit : Nonempty L.Splitting)
    (hdeg : DegenerateAbove L 1) (ι : (SimplicialObject.const _).obj T ⟶ L)
    (hlo : ∀ m < 0 + 1, IsIso (ι.app (op ⦋m⦌)))
    (hcovL : IsCoveringOver J (((SimplicialObject.coskAdj 0).unit.app L).app (op ⦋0 + 1⦌))) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)), IsHypercovering J K ∧
      (∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I), ((K.obj (op ⦋n⦌)).obj i).left ∈ B) ∧
      Nonempty (L ⟶ K) := by
  let Good : ℕ → SimplicialObject (FormalCoproduct.{w} (Over X)) → Prop :=
    fun n K ↦ (∀ a i, ((K.obj a).obj i).left ∈ B) ∧ Nonempty K.Splitting ∧ DegenerateAbove K n
  have hs : ∀ n (Q : {K // Good n K}), ∃ R : {L // Good (n + 1) L}, ∃ f : Q.1 ⟶ R.1,
      IsIso ((SimplicialObject.truncation n).map f) ∧
        IsCoveringOver J (((SimplicialObject.coskAdj n).unit.app R.1).app (op ⦋n + 1⦌)) := by
    intro n Q
    obtain ⟨R, hR, f, hf⟩ :=
      exists_attachment_step J B hcover hadjoin n Q.1 Q.2.1 Q.2.2.1 Q.2.2.2
    exact ⟨⟨R, hR⟩, f, hf⟩
  choose next incl htr hcov using hs
  let seq : (n : ℕ) → {K // Good (n + 1) K} :=
    Nat.rec ⟨L, ⟨fun a i ↦ hBL a.unop.len i, hsplit, hdeg⟩⟩ (fun n Q ↦ next (n + 1) Q)
  let Xs : ℕ → SimplicialObject (FormalCoproduct.{w} (Over X)) := fun n ↦
    match n with
    | 0 => (SimplicialObject.const _).obj T
    | m + 1 => (seq m).1
  let maps : ∀ n, Xs n ⟶ Xs (n + 1) := fun n ↦
    match n with
    | 0 => ι
    | m + 1 => incl (m + 1) (seq m)
  let F : ℕ ⥤ SimplicialObject (FormalCoproduct.{w} (Over X)) := Functor.ofSequence maps
  have hF : ∀ n, IsIso ((SimplicialObject.truncation n).map
      (F.map (homOfLE (Nat.le_succ n)))) := by
    intro n
    rw [show F.map (homOfLE (Nat.le_succ n)) = maps n from
      Functor.ofSequence_map_homOfLE_succ _ n]
    cases n with
    | zero =>
      show IsIso ((SimplicialObject.truncation 0).map ι)
      exact isIso_truncation_map_of_isIso_app ι 0 fun m hm ↦ hlo m (Nat.lt_succ_of_le hm)
    | succ m => exact htr (m + 1) (seq m)
  have hcovF : ∀ n, IsCoveringOver J
      (((SimplicialObject.coskAdj n).unit.app (F.obj (n + 1))).app (op ⦋n + 1⦌)) := fun
    | 0 => hcovL
    | m + 1 => hcov (m + 1) (seq m)
  have hXs : ∀ n a i, (((F.obj n).obj a).obj i).left ∈ B := fun
    | 0 => fun _ i ↦ hT i
    | m + 1 => (seq m).2.1
  obtain ⟨K, hK, hKB, hι'⟩ := exists_hypercovering_of_sequence J B F hF hcovF hXs hTcover
  exact ⟨K, hK, hKB, hι' 1⟩

private lemma comp_map_δ_of_attachment {X : C} (T N : FormalCoproduct.{w} (Over X))
    (f₀ f₁ : N ⟶ T)
    (q : N ⟶ ((SimplicialObject.cosk 0).obj ((SimplicialObject.const _).obj T)).obj (op ⦋1⦌))
    (hqf : ∀ k : Fin 2, q ≫ (matchingCone ((SimplicialObject.const _).obj T) 0 _).π.app
      (StructuredArrow.mk (Y := op (⟨⦋0⦌, le_rfl⟩ : SimplexCategory.Truncated 0))
        (SimplexCategory.δ k).op) = if k = 0 then f₀ else f₁)
    (L : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (ι : (SimplicialObject.const _).obj T ⟶ L)
    (p : L ⟶ (SimplicialObject.cosk 0).obj ((SimplicialObject.const _).obj T))
    (e : N ⟶ L.obj (op ⦋1⦌))
    (hfp : ι ≫ p = (SimplicialObject.coskAdj 0).unit.app ((SimplicialObject.const _).obj T))
    (heq : e ≫ p.app (op ⦋1⦌) = q) [IsIso (ι.app (op ⦋0⦌))] (k : Fin 2) :
    e ≫ L.map (SimplexCategory.δ k).op = (if k = 0 then f₀ else f₁) ≫ ι.app (op ⦋0⦌) := by
  let a : StructuredArrow (op ⦋1⦌) (SimplexCategory.Truncated.inclusion 0).op :=
    StructuredArrow.mk
      (Y := op (⟨⦋0⦌, le_rfl⟩ : SimplexCategory.Truncated 0)) (SimplexCategory.δ k).op
  let ε := ((SimplicialObject.coskAdj 0).counit.app
    ((SimplicialObject.truncation 0).obj ((SimplicialObject.const _).obj T))).app a.right
  have h₀ : ι.app (op ⦋0⦌) ≫ p.app (op ⦋0⦌) =
      ((SimplicialObject.coskAdj 0).unit.app ((SimplicialObject.const _).obj T)).app
        (op ⦋0⦌) := by
    rw [← NatTrans.comp_app, hfp]
  have h₁ : ι.app (op ⦋0⦌) ≫ p.app (op ⦋0⦌) ≫ ε = 𝟙 _ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ε) h₀).trans (NatTrans.congr_app
      ((SimplicialObject.coskAdj 0).left_triangle_components
        ((SimplicialObject.const _).obj T)) a.right))
  have h₂ : e ≫ L.map (SimplexCategory.δ k).op ≫ p.app (op ⦋0⦌) ≫ ε =
      if k = 0 then f₀ else f₁ :=
    (congrArg (e ≫ ·) (Category.assoc _ _ _).symm).trans
      ((congrArg (fun t ↦ e ≫ t ≫ ε) (p.naturality (SimplexCategory.δ k).op)).trans
        ((congrArg (e ≫ ·) (Category.assoc _ _ _)).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) heq).trans (hqf k)))))
  rw [← IsIso.comp_inv_eq, IsIso.inv_eq_of_hom_inv_id h₁]
  exact (Category.assoc _ _ _).trans h₂

/-- **The construction of Stacks 0DAV with prescribed terms in degrees zero and one.** Given a
covering `T` of `X` by objects of `B` and a covering `q : N ⟶ (cosk₀ T)_1` of the degree-one
matching object of the constant simplicial object on `T`, with two faces `f₀ f₁ : N ⟶ T`, there is
a hypercovering of `X` by objects of `B` receiving maps `T ⟶ K_0` and `N ⟶ K_1` under which the two
faces of `K` are `f₀` and `f₁`. -/
theorem exists_hypercovering_with_objects_in_of_lowDegrees
    (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (V : ι → C) (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J U)
    (hadjoin : ∀ {ι : Type w} (V : ι → C) {U : C} (f : ∀ i, V i ⟶ U),
      (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ g : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈ J U)
    {X : C} (T : FormalCoproduct.{w} (Over X)) (hT : ∀ i, (T.obj i).left ∈ B)
    (hTcover : IsCoveringOver J (terminal.from T))
    (N : FormalCoproduct.{w} (Over X)) (hN : ∀ i, (N.obj i).left ∈ B) (f₀ f₁ : N ⟶ T)
    (q : N ⟶ ((SimplicialObject.cosk 0).obj ((SimplicialObject.const _).obj T)).obj (op ⦋1⦌))
    (hqf : ∀ k : Fin 2, q ≫ (matchingCone ((SimplicialObject.const _).obj T) 0 _).π.app
      (StructuredArrow.mk (Y := op (⟨⦋0⦌, le_rfl⟩ : SimplexCategory.Truncated 0))
        (SimplexCategory.δ k).op) = if k = 0 then f₀ else f₁)
    (hq : IsCoveringOver J q) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering J K ∧
        (∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I), ((K.obj (op ⦋n⦌)).obj i).left ∈ B) ∧
        ∃ (c : T ⟶ K.obj (op ⦋0⦌)) (e : N ⟶ K.obj (op ⦋1⦌)),
          e ≫ K.map (SimplexCategory.δ 0).op = f₀ ≫ c ∧
            e ≫ K.map (SimplexCategory.δ 1).op = f₁ ≫ c := by
  have : HasFiniteLimits (Over X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  obtain ⟨L, ι, p, e, hfp, heq, -, -, hsplit, hlo, hBL, hdeg, hcovL⟩ :=
    exists_split_matching_attachment ((SimplicialObject.const _).obj T) 0 N q
      (nonempty_splitting_const T) B (fun _ i ↦ hT i) hN J hadjoin hq
      (degenerateAbove_const T)
      (finite_matching_fibre_of_degenerateAbove _ 0 (degenerateAbove_const T))
  have hι₀ : IsIso (ι.app (op ⦋0⦌)) := hlo 0 (by omega)
  obtain ⟨K, hK, hKB, ⟨φ⟩⟩ := exists_hypercovering_of_attachment J B hcover hadjoin T hT
    hTcover L hBL hsplit hdeg ι hlo hcovL
  have h (k : Fin 2) : (e ≫ φ.app (op ⦋1⦌)) ≫ K.map (SimplexCategory.δ k).op =
      (if k = 0 then f₀ else f₁) ≫ ι.app (op ⦋0⦌) ≫ φ.app (op ⦋0⦌) := by
    rw [Category.assoc, ← φ.naturality, ← Category.assoc,
      comp_map_δ_of_attachment T N f₀ f₁ q hqf L ι p e hfp heq k, Category.assoc]
  exact ⟨K, hK, hKB, _, _, (h 0).trans (by rw [if_pos rfl]),
    (h 1).trans (by rw [if_neg (by decide)])⟩

end Generic

section FullSubcategory

/-- A functor lifted along a fully faithful functor, given lifts of its values. -/
@[simps]
private def liftAlongFullyFaithful {I A E : Type*} [Category I] [Category A] [Category E]
    {G : A ⥤ E} (hG : G.FullyFaithful) (F : I ⥤ E) (o : I → A)
    (e : ∀ x, G.obj (o x) ≅ F.obj x) : I ⥤ A where
  obj := o
  map f := hG.preimage ((e _).hom ≫ F.map f ≫ (e _).inv)
  map_id x := hG.map_injective (by simp)
  map_comp f g := hG.map_injective (by simp)

/-- The lifted functor followed by the fully faithful functor is the given one. -/
private def liftAlongFullyFaithfulIso {I A E : Type*} [Category I] [Category A] [Category E]
    {G : A ⥤ E} (hG : G.FullyFaithful) (F : I ⥤ E) (o : I → A)
    (e : ∀ x, G.obj (o x) ≅ F.obj x) : liftAlongFullyFaithful hG F o e ⋙ G ≅ F :=
  NatIso.ofComponents e (fun f ↦
    (congrArg (· ≫ (e _).hom) (hG.map_preimage ((e _).hom ≫ F.map f ≫ (e _).inv))).trans
      (by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl))

/-- A sieve containing the arrows of a covering family by objects `i(U)` is covering. -/
private lemma mem_toGrothendieck_of_forall_cover {D B : Type u} [SmallCategory D]
    [SmallCategory B] [HasPullbacks D] (J : Pretopology D) (i : B ⥤ D)
    (hcover : ∀ V : D, ∃ (ι : Type u) (U : ι → B) (g : ∀ k, i.obj (U k) ⟶ V),
      Presieve.ofArrows (fun k ↦ i.obj (U k)) g ∈ J V) (V : D) :
    ∃ (ι : Type u) (U : ι → B) (g : ∀ k, i.obj (U k) ⟶ V),
      ∀ S : Sieve V, (∀ k, S.arrows (g k)) → S ∈ J.toGrothendieck V := by
  obtain ⟨ι, U, g, hg⟩ := hcover V
  refine ⟨ι, U, g, fun S hS ↦ J.toGrothendieck.superset_covering ?_
    ((Pretopology.mem_toGrothendieck _ _ _).2 ⟨_, hg, Sieve.le_generate _⟩)⟩
  rw [Sieve.generate_le_iff]
  rintro W f ⟨k⟩
  exact hS k

variable {D : Type u} [SmallCategory D] [HasEqualizers D] [HasPullbacks D]
  {B : Type u} [SmallCategory B]

private abbrev allObjects (B : Type u) [SmallCategory B] : FormalCoproduct.{u} B := ⟨B, id⟩

private abbrev Span (B : Type u) [SmallCategory B] : Type u := Σ (U V W : B), (U ⟶ V) × (U ⟶ W)

private abbrev allSpans (B : Type u) [SmallCategory B] : FormalCoproduct.{u} B :=
  ⟨Span B, fun ω ↦ ω.1⟩

private abbrev spanFst (B : Type u) [SmallCategory B] : allSpans B ⟶ allObjects B :=
  ⟨fun ω ↦ ω.2.1, fun ω ↦ ω.2.2.2.1⟩

private abbrev spanSnd (B : Type u) [SmallCategory B] : allSpans B ⟶ allObjects B :=
  ⟨fun ω ↦ ω.2.2.1, fun ω ↦ ω.2.2.2.2⟩

omit [HasEqualizers D] in
private lemma isCoveringOver_zeroMatchingLift_spans (J : Pretopology D)
    (i : B ⥤ D) (hi : i.FullyFaithful)
    (hcover : ∀ V : D, ∃ (ι : Type u) (U : ι → B) (g : ∀ k, i.obj (U k) ⟶ V),
      Presieve.ofArrows (fun k ↦ i.obj (U k)) g ∈ J V) :
    IsCoveringOver (localPretopology.{u, u, u} J)
      (zeroMatchingLift ((SimplicialObject.const _).obj
          ((mapFormalCoproduct.{u} i ⋙ yonedaFormal.{u, u, u}).obj (allObjects B)))
        ((mapFormalCoproduct.{u} i ⋙ yonedaFormal.{u, u, u}).map (spanFst B))
        ((mapFormalCoproduct.{u} i ⋙ yonedaFormal.{u, u, u}).map (spanSnd B))) := by
  let Yo : FormalCoproduct.{u} D ⥤ FormalCoproduct.{u} (Over (⊤_ (Dᵒᵖ ⥤ Type u))) :=
    yonedaFormal.{u, u, u}
  let hY : Yo.FullyFaithful := yonedaFormalFullyFaithful.{u, u, u}
  let G' := mapFormalCoproduct.{u} i ⋙ Yo
  let TB := allObjects B
  let NB := allSpans B
  let g₀ := spanFst B
  let g₁ := spanSnd B
  let K₀ : SimplicialObject (FormalCoproduct.{u} (Over (⊤_ (Dᵒᵖ ⥤ Type u)))) :=
    (SimplicialObject.const _).obj (G'.obj TB)
  show IsCoveringOver _ (zeroMatchingLift K₀ (G'.map g₀) (G'.map g₁))
  refine isCoveringOver_of_homLocallySurjective J _ fun V s ↦ ?_
  let σ : ∀ k : Fin 2, (FormalCoproduct.incl D).obj V ⟶ (mapFormalCoproduct i).obj TB :=
    fun k ↦ hY.preimage (s ≫ zeroMatchingπ K₀ k)
  obtain ⟨ι, U, g, hg⟩ := mem_toGrothendieck_of_forall_cover J i hcover V
  refine hg _ fun k ↦ ?_
  let ω : Span B := ⟨U k, (σ 0).f PUnit.unit, (σ 1).f PUnit.unit,
    hi.preimage (g k ≫ (σ 0).φ PUnit.unit), hi.preimage (g k ≫ (σ 1).φ PUnit.unit)⟩
  refine ⟨Yo.map (FormalCoproduct.Hom.fromIncl (C := D) (Y := (mapFormalCoproduct i).obj NB)
    ω (𝟙 _)), ?_⟩
  refine zeroMatching_hom_ext K₀ _ _ fun m ↦ ?_
  have hπ : zeroMatchingLift K₀ (G'.map g₀) (G'.map g₁) ≫ zeroMatchingπ K₀ m =
      if m = 0 then G'.map g₀ else G'.map g₁ := zeroMatchingLift_π K₀ _ _ m
  have hs : s ≫ zeroMatchingπ K₀ m = Yo.map (σ m) := (hY.map_preimage _).symm
  rw [Category.assoc, hπ, Category.assoc, hs]
  show _ = Yo.map ((FormalCoproduct.incl D).map (g k)) ≫ _
  rw [← Yo.map_comp]
  rcases (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) m with rfl | rfl <;>
    [rw [if_pos rfl]; rw [if_neg (by decide)]] <;>
  · change Yo.map _ ≫ Yo.map ((mapFormalCoproduct i).map _) = _
    rw [← Yo.map_comp]
    congr 1
    refine FormalCoproduct.hom_ext rfl ?_
    rintro ⟨⟩
    change (𝟙 _ ≫ i.map (hi.preimage (g k ≫ _))) ≫ 𝟙 _ = g k ≫ _
    simp only [hi.map_preimage, Category.id_comp, Category.comp_id]
    rfl

private lemma exists_lift_of_hypercovering (J : Pretopology D) (i : B ⥤ D)
    (hi : i.FullyFaithful)
    (KA : SimplicialObject (FormalCoproduct.{u} (Over (⊤_ (Dᵒᵖ ⥤ Type u)))))
    (hKA : IsHypercovering (localPretopology.{u, u, u} J) KA)
    (hKB : ∀ (n : ℕ) (j : (KA.obj (op ⦋n⦌)).I),
      ∃ U ∈ Set.range i.obj, ((KA.obj (op ⦋n⦌)).obj j).left = uliftYoneda.{u} (C := D).obj U)
    (c : (mapFormalCoproduct.{u} i ⋙ yonedaFormal.{u, u, u}).obj (allObjects B) ⟶
      KA.obj (op ⦋0⦌))
    (e : (mapFormalCoproduct.{u} i ⋙ yonedaFormal.{u, u, u}).obj (allSpans B) ⟶
      KA.obj (op ⦋1⦌))
    (he₀ : e ≫ KA.map (SimplexCategory.δ 0).op =
      (mapFormalCoproduct.{u} i ⋙ yonedaFormal.{u, u, u}).map (spanFst B) ≫ c)
    (he₁ : e ≫ KA.map (SimplexCategory.δ 1).op =
      (mapFormalCoproduct.{u} i ⋙ yonedaFormal.{u, u, u}).map (spanSnd B) ≫ c) :
    ∃ (L : SimplicialObject (FormalCoproduct.{u} B)) (H : HypercoveringOfTerminal.{u} J),
      H.toSimplicialObject = L ⋙ mapFormalCoproduct i ∧
      ∃ c : ∀ U : B, (FormalCoproduct.incl B).obj U ⟶ L.obj (op ⦋0⦌),
        ∀ {U V : B} (a : U ⟶ V), ∃ e : (FormalCoproduct.incl B).obj U ⟶ L.obj (op ⦋1⦌),
          e ≫ L.map (SimplexCategory.δ 0).op = (FormalCoproduct.incl B).map a ≫ c V ∧
            e ≫ L.map (SimplexCategory.δ 1).op = c U := by
  let Yo : FormalCoproduct.{u} D ⥤ FormalCoproduct.{u} (Over (⊤_ (Dᵒᵖ ⥤ Type u))) :=
    yonedaFormal.{u, u, u}
  let G' := mapFormalCoproduct.{u} i ⋙ Yo
  let hG' : G'.FullyFaithful :=
    (mapFormalCoproductFullyFaithful i hi).comp yonedaFormalFullyFaithful.{u, u, u}
  let TB := allObjects B
  let NB := allSpans B
  let g₀ := spanFst B
  let g₁ := spanSnd B
  replace he₀ : e ≫ KA.map (SimplexCategory.δ 0).op = G'.map g₀ ≫ c := he₀
  replace he₁ : e ≫ KA.map (SimplexCategory.δ 1).op = G'.map g₁ ≫ c := he₁
  have hpre : ∀ (n : SimplexCategoryᵒᵖ) (j : (KA.obj n).I),
      ∃ U : B, uliftYoneda.{u} (C := D).obj (i.obj U) = ((KA.obj n).obj j).left := fun n j ↦ by
    obtain ⟨_, ⟨U, rfl⟩, h⟩ := hKB n.unop.len j
    exact ⟨U, h.symm⟩
  let o : SimplexCategoryᵒᵖ → FormalCoproduct.{u} B := fun n ↦
    ⟨(KA.obj n).I, fun j ↦ Classical.choose (hpre n j)⟩
  let eo : ∀ n, G'.obj (o n) ≅ KA.obj n := fun n ↦
    FormalCoproduct.isoOfComponents (Equiv.refl _) fun j ↦
      Over.isoMk (eqToIso (Classical.choose_spec (hpre n j))) (terminalIsTerminal.hom_ext _ _)
  let L := liftAlongFullyFaithful hG' KA o eo
  let Φ : L ⋙ G' ≅ KA := liftAlongFullyFaithfulIso hG' KA o eo
  obtain ⟨H, hH⟩ := hypercoveringOfTerminal_lift J (L ⋙ mapFormalCoproduct i) KA Φ hKA
  let ιT : ∀ U : B, (FormalCoproduct.incl B).obj U ⟶ TB :=
    fun U ↦ FormalCoproduct.Hom.fromIncl (Y := TB) U (𝟙 U)
  have hn (k : Fin 2) : Φ.inv.app (op ⦋1⦌) ≫ G'.map (L.map (SimplexCategory.δ k).op) =
      KA.map (SimplexCategory.δ k).op ≫ Φ.inv.app (op ⦋0⦌) :=
    (Φ.inv.naturality _).symm
  refine ⟨L, H, hH, fun U ↦ hG'.preimage (G'.map (ιT U) ≫ c ≫ Φ.inv.app (op ⦋0⦌)),
    fun {U V} a ↦ ?_⟩
  let ω : Span B := ⟨U, V, U, a, 𝟙 U⟩
  let ιN : (FormalCoproduct.incl B).obj U ⟶ NB := FormalCoproduct.Hom.fromIncl (Y := NB) ω (𝟙 U)
  have k₀ : ιN ≫ g₀ = (FormalCoproduct.incl B).map a ≫ ιT V :=
    FormalCoproduct.hom_ext rfl fun _ ↦ by
      show (𝟙 U ≫ a) ≫ 𝟙 V = a ≫ 𝟙 V
      simp
  have k₁ : ιN ≫ g₁ = ιT U :=
    FormalCoproduct.hom_ext rfl fun _ ↦ by
      show (𝟙 U ≫ 𝟙 U) ≫ 𝟙 U = 𝟙 U
      simp
  refine ⟨hG'.preimage (G'.map ιN ≫ e ≫ Φ.inv.app (op ⦋1⦌)), ?_, ?_⟩
  · apply hG'.map_injective
    simp only [Functor.map_comp, hG'.map_preimage, Category.assoc]
    rw [hn 0, reassoc_of% he₀, ← G'.map_comp_assoc, k₀, G'.map_comp_assoc]
  · apply hG'.map_injective
    simp only [Functor.map_comp, hG'.map_preimage, Category.assoc]
    rw [hn 1, reassoc_of% he₁, ← G'.map_comp_assoc, k₁]

/-- **A hypercovering of the final presheaf through a full subcategory, with prescribed terms in
degrees zero and one** (the construction in the proof of Stacks 0DAX, as used in the proof of
Stacks 0DCB). Let `i : B ⥤ D` be fully faithful and suppose every object of the site `D` has a
covering by objects `i(U)`. Then there is a simplicial object `L` of `SR(B)` whose image `i(L)`
underlies a hypercovering of the final presheaf on `D`, together with maps `c_U : U ⟶ L_0` for
every object `U` of `B`, such that for every arrow `a : U ⟶ V` of `B` some map `e : U ⟶ L_1` has
faces `d_0 ∘ e = c_V ∘ a` and `d_1 ∘ e = c_U`. -/
theorem exists_hypercoveringOfTerminal_fullSubcategory (J : Pretopology D)
    (i : B ⥤ D) (hi : i.FullyFaithful)
    (hcover : ∀ V : D, ∃ (ι : Type u) (U : ι → B) (g : ∀ k, i.obj (U k) ⟶ V),
      Presieve.ofArrows (fun k ↦ i.obj (U k)) g ∈ J V) :
    ∃ (L : SimplicialObject (FormalCoproduct.{u} B)) (H : HypercoveringOfTerminal.{u} J),
      H.toSimplicialObject = L ⋙ mapFormalCoproduct i ∧
      ∃ c : ∀ U : B, (FormalCoproduct.incl B).obj U ⟶ L.obj (op ⦋0⦌),
        ∀ {U V : B} (a : U ⟶ V), ∃ e : (FormalCoproduct.incl B).obj U ⟶ L.obj (op ⦋1⦌),
          e ≫ L.map (SimplexCategory.δ 0).op = (FormalCoproduct.incl B).map a ≫ c V ∧
            e ≫ L.map (SimplexCategory.δ 1).op = c U := by
  let BD : Set D := Set.range i.obj
  have hcoverD : ∀ U : D, ∃ (ι : Type u) (V : ι → D) (f : ∀ k, V k ⟶ U),
      (∀ k, V k ∈ BD) ∧ Presieve.ofArrows V f ∈ J U := fun U ↦
    (hcover U).imp fun _ ⟨V, g, hg⟩ ↦ ⟨_, g, fun k ↦ ⟨V k, rfl⟩, hg⟩
  let B' : Set (Dᵒᵖ ⥤ Type u) :=
    {P | ∃ U ∈ BD, P = uliftYoneda.{u} (C := D).obj U}
  have hcover' : ∀ F : Dᵒᵖ ⥤ Type u,
      ∃ (ι : Type u) (V : ι → Dᵒᵖ ⥤ Type u)
        (f : ∀ k, V k ⟶ F), (∀ k, V k ∈ B') ∧
          Presieve.ofArrows V f ∈ (localPretopology.{u, u, u} J) F :=
    exists_presheaf_cover_by_representables.{u, u, u} J BD hcoverD
  have hadjoin' : ∀ {ι : Type u} (V : ι → Dᵒᵖ ⥤ Type u)
      {F : Dᵒᵖ ⥤ Type u} (f : ∀ k, V k ⟶ F),
      (∀ k, V k ∈ B') → Presieve.ofArrows V f ∈ (localPretopology.{u, u, u} J) F →
      ∀ {F' : Dᵒᵖ ⥤ Type u}, F' ∈ B' → ∀ g : F' ⟶ F,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈
          (localPretopology.{u, u, u} J) F :=
    fun {_} _ {_} _ _ hf {_} _ g ↦ localPretopology_adjoin J hf g
  let Yo : FormalCoproduct.{u} D ⥤ FormalCoproduct.{u} (Over (⊤_ (Dᵒᵖ ⥤ Type u))) :=
    yonedaFormal.{u, u, u}
  let G' := mapFormalCoproduct.{u} i ⋙ Yo
  let TB := allObjects B
  let NB := allSpans B
  let K₀ : SimplicialObject (FormalCoproduct.{u} (Over (⊤_ (Dᵒᵖ ⥤ Type u)))) :=
    (SimplicialObject.const _).obj (G'.obj TB)
  have hT : ∀ j, ((G'.obj TB).obj j).left ∈ B' := fun j ↦ ⟨i.obj j, ⟨j, rfl⟩, rfl⟩
  have hN : ∀ j, ((G'.obj NB).obj j).left ∈ B' := fun j ↦ ⟨i.obj j.1, ⟨j.1, rfl⟩, rfl⟩
  have hTcover : IsCoveringOver (localPretopology.{u, u, u} J) (terminal.from (G'.obj TB)) := by
    refine isCoveringOver_of_homLocallySurjective J _ fun V s ↦ ?_
    obtain ⟨ι, U, g, hg⟩ := mem_toGrothendieck_of_forall_cover J i hcover V
    refine hg _ fun k ↦ ?_
    exact ⟨Yo.map (FormalCoproduct.Hom.fromIncl (C := D) (Y := (mapFormalCoproduct i).obj TB)
      (U k) (𝟙 _)), terminal.hom_ext _ _⟩
  obtain ⟨KA, hKA, hKB, c, e, he₀, he₁⟩ :=
    exists_hypercovering_with_objects_in_of_lowDegrees (localPretopology.{u, u, u} J) B'
      hcover' hadjoin' (G'.obj TB) hT hTcover (G'.obj NB) hN (G'.map (spanFst B))
      (G'.map (spanSnd B)) (zeroMatchingLift K₀ (G'.map (spanFst B)) (G'.map (spanSnd B)))
      (zeroMatchingLift_π K₀ _ _) (isCoveringOver_zeroMatchingLift_spans J i hi hcover)
  exact exists_lift_of_hypercovering J i hi KA hKA hKB c e he₀ he₁

end FullSubcategory

end Stacks.CategoryTheory.Hypercovering

end
