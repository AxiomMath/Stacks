module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Abel

/-!
# Comparing a sheaf pullback with a map into a pushforward

Let `G : C ⥤ D` be a continuous functor of sites, so that the direct image `G^*` of sheaves
has a left adjoint `G_!`, the sheaf pullback. This file collects the formal ingredients for
constructing a map `G_! ⟶ P` into some other functor and for recognising when such a map is
injective.

Constructing the map is adjunction bookkeeping: a natural transformation `𝟭 ⟶ P ⋙ G^*` has a
transpose `G_! ⟶ P`, and transposing back recovers it. Recognising injectivity is a finite
computation: the sections of `G_!F` are locally sums of finitely many sections coming from
the left Kan extension, and such a sum vanishes as soon as the summands are separated by a
family of retractions which are orthogonal in the sense that the composite of the `i`-th
inclusion with the `j`-th retraction lands back in the `j`-th summand.

## Main definitions

* `CategoryTheory.Adjunction.transposeNatTrans` — the transpose `E ⟶ P` of a natural
  transformation `𝟭 ⟶ P ⋙ R` along an adjunction `E ⊣ R`.

## Main results

* `CategoryTheory.Adjunction.unit_comp_map_transposeNatTrans` — transposing back along the
  unit recovers the original natural transformation.
* `CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous_unit_app_hom`
  — the unit of the sheaf pullback adjunction of a continuous functor is the unit of the
  left Kan extension followed by sheafification.
* `CategoryTheory.Limits.exists_list_sum_of_isColimit` — every element of a colimit of
  abelian groups is a finite sum of elements coming from the objects of the diagram.
* `AddMonoidHom.sum_eq_zero_of_projections` — a sum of elements of a family of abelian
  groups, mapped into a common target, vanishes as soon as its image under a map admitting
  orthogonal retractions vanishes.

## References

* [Stacks Project, Tag 0F4L](https://stacks.math.columbia.edu/tag/0F4L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

/-- Every element of a colimit of abelian groups is a finite sum of images of elements of the
objects of the diagram: those sums form a subgroup through which the colimit cone factors, so
the quotient by it receives the zero map. -/
public theorem exists_list_sum_of_isColimit {J : Type*} [Category J]
    (F : J ⥤ AddCommGrpCat.{u₁}) (c : Cocone F) (hc : IsColimit c) (x : c.pt) :
    ∃ l : List (Σ j, F.obj j), (l.map fun s => c.ι.app s.1 s.2).sum = x := by
  classical
  let S : AddSubgroup c.pt :=
    { carrier := {x | ∃ l : List (Σ j, F.obj j), (l.map fun s => c.ι.app s.1 s.2).sum = x}
      zero_mem' := ⟨[], rfl⟩
      add_mem' := by
        rintro x y ⟨l, rfl⟩ ⟨l', rfl⟩
        exact ⟨l ++ l', by simp only [List.map_append, List.sum_append]⟩
      neg_mem' := by
        rintro x ⟨l, rfl⟩
        refine ⟨l.map (fun s => ⟨s.1, -s.2⟩), ?_⟩
        simp only [List.map_map, Function.comp_def, map_neg]
        induction l with
        | nil => simp
        | cons a l ih =>
          simpa only [List.map_cons, List.sum_cons, neg_add] using
            congrArg (-(c.ι.app a.1 a.2) + ·) ih }
  let q : c.pt ⟶ AddCommGrpCat.of (c.pt ⧸ S) := AddCommGrpCat.ofHom (QuotientAddGroup.mk' S)
  have hq : q = 0 := by
    refine hc.hom_ext fun j => ?_
    ext y
    show (QuotientAddGroup.mk' S) (c.ι.app j y) = 0
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨[⟨j, y⟩], by simp⟩
  exact (QuotientAddGroup.eq_zero_iff _).1
    (congrArg (fun f : c.pt ⟶ AddCommGrpCat.of (c.pt ⧸ S) => f x) hq)

end CategoryTheory.Limits

namespace AddMonoidHom

/-- Let `f i : A i →+ M` be a family of maps into an abelian group, let `g : M →+ N`, and let
`r i : N →+ A i` be retractions in the sense that `r i ∘ g ∘ f i` is the identity and that
`f i ∘ r i ∘ g ∘ f j` always lands in the image of `f j`. Then a formal sum of the `f i` is
already zero as soon as `g` kills it: subtracting off the `i`-th component shortens the list
without changing its image, and induction on the length finishes. -/
public theorem sum_eq_zero_of_projections {I : Type*} (A : I → Type*)
    [∀ i, AddCommGroup (A i)] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : ∀ i, A i →+ M) (g : M →+ N) (r : ∀ i, N →+ A i)
    (hf : ∀ i s, r i (g (f i s)) = s)
    (hc : ∀ i j s, ∃ t, f i (r i (g (f j s))) = f j t)
    (l : List (Σ i, A i))
    (h : g ((l.map fun a => f a.1 a.2).sum) = 0) :
    (l.map fun a => f a.1 a.2).sum = 0 := by
  classical
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    cases l with
    | nil => simp
    | cons a l =>
      obtain ⟨i, s⟩ := a
      have hr := congrArg (fun t => f i (r i t)) h
      simp only [List.map_cons, List.sum_cons, map_add, hf, map_zero] at hr
      choose t ht using hc i
      let l' : List (Σ j, A j) := l.map fun b => ⟨b.1, b.2 - t b.1 b.2⟩
      have heq : (l'.map fun b => f b.1 b.2).sum =
          (l.map fun b => f b.1 b.2).sum - f i (r i (g ((l.map fun b => f b.1 b.2).sum))) := by
        dsimp [l']
        clear h hn hr ih n
        induction l with
        | nil => simp
        | cons b l hrec =>
          simp only [List.map_cons, List.sum_cons, map_add, map_sub, hrec, ← ht]
          abel
      have hx : f i s + (l.map fun b => f b.1 b.2).sum =
          (l'.map fun b => f b.1 b.2).sum := by
        rw [heq, eq_neg_of_add_eq_zero_left hr]
        abel
      have hz : g ((l'.map fun b => f b.1 b.2).sum) = 0 := by
        rw [← hx]
        exact h
      simp only [List.map_cons, List.sum_cons]
      rw [hx]
      exact ih l'.length (by rw [← hn]; simp [l']) l' hz rfl

end AddMonoidHom

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The transpose `E ⟶ P` of a natural transformation `η : 𝟭 C ⟶ P ⋙ R` along an adjunction
`E ⊣ R`: apply `E` to `η` and then the counit at `P`. -/
public def Adjunction.transposeNatTrans {E : C ⥤ D} {R : D ⥤ C} (adj : E ⊣ R) (P : C ⥤ D)
    (η : 𝟭 C ⟶ P ⋙ R) : E ⟶ P where
  app F := E.map (η.app F) ≫ adj.counit.app (P.obj F)
  naturality F G f := by
    have h := η.naturality f
    dsimp at h ⊢
    rw [← E.map_comp_assoc, h, E.map_comp_assoc, adj.counit_naturality, Category.assoc]

/-- Transposing `E ⟶ P` back along the unit of the adjunction recovers the natural
transformation `𝟭 C ⟶ P ⋙ R` it came from. -/
public theorem Adjunction.unit_comp_map_transposeNatTrans {E : C ⥤ D} {R : D ⥤ C}
    (adj : E ⊣ R) (P : C ⥤ D) (η : 𝟭 C ⟶ P ⋙ R) (F : C) :
    adj.unit.app F ≫ R.map ((adj.transposeNatTrans P η).app F) = η.app F := by
  simp [transposeNatTrans]

namespace Functor.sheafPullbackConstruction

/-- For a continuous functor of sites `G`, the unit of the sheaf pullback adjunction is the
unit of the left Kan extension along `G.op` followed by sheafification of that extension. -/
public theorem sheafAdjunctionContinuous_unit_app_hom {A : Type*} [Category A]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsContinuous J K] [∀ F : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension F]
    [HasWeakSheafify K A] (F : Sheaf J A) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app F).hom =
      G.op.lanUnit.app F.obj ≫ Functor.whiskerLeft G.op
        (toSheafify K (G.op.lan.obj F.obj)) := by
  have hunit : (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app F =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).homEquiv F
        _ (𝟙 _) := by
    rw [Adjunction.homEquiv_unit]
    simp
  have hjunk : ∀ {P Q R : Cᵒᵖ ⥤ A} (a : P ⟶ Q) (b : Q ⟶ R) (j₁ j₂ j₃ : R ⟶ R),
      j₁ = 𝟙 R → j₂ = 𝟙 R → j₃ = 𝟙 R → (a ≫ b) ≫ j₁ ≫ j₂ ≫ j₃ = a ≫ b := by
    rintro P Q R a b j₁ j₂ j₃ rfl rfl rfl
    simp
  have key := Adjunction.restrictFullyFaithful_homEquiv_apply
    (R := G.sheafPushforwardContinuous A J K)
    ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A))
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id (Sheaf K A))
    (Iso.refl _) (Iso.refl _)
    (𝟙 ((Functor.sheafPullbackConstruction.sheafPullback G A J K).obj F))
  show (sheafToPresheaf J A).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app F) = _
  rw [hunit, Functor.sheafPullbackConstruction.sheafAdjunctionContinuous, key,
    Functor.FullyFaithful.map_preimage, Adjunction.comp_unit_app,
    Functor.lanAdjunction_unit]
  exact hjunk _ _ _ _ _ rfl rfl rfl

end Functor.sheafPullbackConstruction

end CategoryTheory

end
