module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Reading a pro-object off its stages

A pro-object of `C` indexed by a filtered `J` is presented by the colimit of representables
`colim_j yoneda (A j)` in the presheaf category `Cᵒᵖ ⥤ Type v`, whose value at `X` is
`colim_j (X ⟶ A j)`. This file extracts the elementary content of that presentation: a morphism
of pro-objects is represented, at each stage of its source, by an honest morphism out of some
stage of its target, and two such representatives present the same morphism exactly when they
agree after passing to a common later stage.

The two facts are then assembled, for diagrams indexed by `ℕᵒᵖ`, into the *ladder* of an
isomorphism of pro-objects: mutually inverse families of maps `A_{p n} ⟶ B_n` and `B_{q n} ⟶ A_n`,
each compatible with the transition maps and each composing with the other to a transition map,
all of it only after passing far enough along the index.

## Main results

* `Stacks.ProObject.exists_stage_rep` — a morphism of the presenting presheaves is represented at
  each stage by a morphism out of some stage.
* `Stacks.ProObject.exists_common_stage_eq` — two such representatives, compatible through the
  morphism, agree after a common later stage.
* `Stacks.ProObject.HasProLadder` and `Stacks.ProObject.hasProLadder` — **the ladder of an
  isomorphism of pro-objects presented by `ℕᵒᵖ`-indexed diagrams.**

## Implementation notes

The index category `J` is left in arbitrary universes: the colimits in question are taken in a
presheaf category whose values lie in the hom universe of `C`, and the applications index by
`ℕᵒᵖᵒᵖ`, which is strictly smaller. Filteredness is used, through
`CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff`, for the stage comparison.

Elements of the colimit are reached by transporting along `preservesColimitIso` for the
evaluation functor, which is where the pointwise computation of colimits of presheaves enters.

The ladder is stated for `A B : ℕᵒᵖ ⥤ C` while the colimits are indexed by `ℕᵒᵖᵒᵖ`, the index of
the opposite diagrams `A.op`, `B.op` whose representables are being taken; an object of `ℕᵒᵖᵒᵖ` is
`op (op n)` and a morphism `op (op n) ⟶ op (op m)` is `n ≤ m`, so the two index conventions agree
on the nose.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w r

namespace Stacks.ProObject

section Stages

variable {C : Type u} [Category.{v, u} C] {J : Type w} [Category.{r} J] [IsFiltered J]
variable [HasColimitsOfShape J (Type v)]

omit [IsFiltered J] in
/-- A morphism `η` between the presheaves presenting two pro-objects is represented, at the stage
`i` of its source, by an honest morphism `G i ⟶ F j` out of some stage `j` of its target. -/
public theorem exists_stage_rep (F G : J ⥤ C)
    (η : colimit (G ⋙ yoneda) ⟶ colimit (F ⋙ yoneda)) (i : J) :
    ∃ j : J, ∃ g : G.obj i ⟶ F.obj j,
      ((colimit.ι (F ⋙ yoneda) j).app (op (G.obj i))) g =
        (η.app (op (G.obj i)))
          (((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i))) := by
  let E : (Cᵒᵖ ⥤ Type v) ⥤ Type v := (evaluation Cᵒᵖ (Type v)).obj (op (G.obj i))
  let x : E.obj (colimit (F ⋙ yoneda)) := η.app (op (G.obj i))
    (((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i)))
  let e := preservesColimitIso E (F ⋙ yoneda)
  obtain ⟨j, g, hg⟩ := Concrete.colimit_exists_rep ((F ⋙ yoneda) ⋙ E) (e.hom x)
  refine ⟨j, g, ?_⟩
  have h : e.inv ((colimit.ι ((F ⋙ yoneda) ⋙ E) j) g) = x := by
    rw [hg]
    simp [x]
  have hh := ConcreteCategory.congr_hom (ι_preservesColimitIso_inv E (F ⋙ yoneda) j) g
  have hx := hh.symm.trans h
  simpa [E, x] using hx

/-- Two representatives of a morphism of pro-objects, taken at stages `i` and `i'` of the source
linked by `a : i ⟶ i'`, agree after passage to a common later stage of the target. -/
public theorem exists_common_stage_eq (F G : J ⥤ C)
    (η : colimit (G ⋙ yoneda) ⟶ colimit (F ⋙ yoneda))
    {i i' j j' : J} (a : i ⟶ i') (g : G.obj i ⟶ F.obj j) (g' : G.obj i' ⟶ F.obj j')
    (hg : ((colimit.ι (F ⋙ yoneda) j).app (op (G.obj i))) g =
      η.app (op (G.obj i))
        (((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i))))
    (hg' : ((colimit.ι (F ⋙ yoneda) j').app (op (G.obj i'))) g' =
      η.app (op (G.obj i'))
        (((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i'))) (𝟙 (G.obj i')))) :
    ∃ (k : J) (b : j ⟶ k) (c : j' ⟶ k),
      g ≫ F.map b = G.map a ≫ g' ≫ F.map c := by
  let E : (Cᵒᵖ ⥤ Type v) ⥤ Type v := (evaluation Cᵒᵖ (Type v)).obj (op (G.obj i))
  let L := (F ⋙ yoneda) ⋙ E
  have hcocone :
      ((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i)) =
        ((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i))) (G.map a) := by
    simpa using (congrArg (fun t => (t.app (op (G.obj i))) (𝟙 (G.obj i)))
      (colimit.w (G ⋙ yoneda) a)).symm
  have hn := NatTrans.naturality_apply η (Quiver.Hom.op (G.map a))
    (((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i'))) (𝟙 (G.obj i')))
  have hmapι :
      ((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i)) =
        ((colimit (G ⋙ yoneda)).map (Quiver.Hom.op (G.map a)))
          (((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i'))) (𝟙 (G.obj i'))) := by
    calc
      _ = ((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i))) (G.map a) := hcocone
      _ = ((colimit (G ⋙ yoneda)).map (Quiver.Hom.op (G.map a)))
          (((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i'))) (𝟙 (G.obj i'))) := by
        have hnat := NatTrans.naturality_apply (colimit.ι (G ⋙ yoneda) i')
          (Quiver.Hom.op (G.map a)) (𝟙 (G.obj i'))
        simpa using hnat
  have hpresheaf :
      ((colimit.ι (F ⋙ yoneda) j).app (op (G.obj i))) g =
        ((colimit.ι (F ⋙ yoneda) j').app (op (G.obj i))) (G.map a ≫ g') := by
    calc
      ((colimit.ι (F ⋙ yoneda) j).app (op (G.obj i))) g =
          η.app (op (G.obj i))
            (((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i))) := hg
      _ = ((colimit (F ⋙ yoneda)).map (Quiver.Hom.op (G.map a)))
            (η.app (op (G.obj i'))
              (((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i'))) (𝟙 (G.obj i')))) := by
        rw [hmapι]
        exact hn
      _ = ((colimit (F ⋙ yoneda)).map (Quiver.Hom.op (G.map a)))
            (((colimit.ι (F ⋙ yoneda) j').app (op (G.obj i'))) g') := by rw [← hg']
      _ = ((colimit.ι (F ⋙ yoneda) j').app (op (G.obj i))) (G.map a ≫ g') := by
        have hnat := NatTrans.naturality_apply (colimit.ι (F ⋙ yoneda) j')
          (Quiver.Hom.op (G.map a)) g'
        simpa using hnat.symm
  let e := preservesColimitIso E (F ⋙ yoneda)
  have hcolim : (colimit.ι L j) g = (colimit.ι L j') (G.map a ≫ g') := by
    have h := congrArg e.hom hpresheaf
    simpa [L, E, e, ← ι_preservesColimitIso_hom] using h
  obtain ⟨k, b, c, hk⟩ := (Types.FilteredColimit.colimit_eq_iff L).mp hcolim
  refine ⟨k, b, c, ?_⟩
  simpa [L, E] using hk

end Stages

section Ladder

variable {C : Type u} [Category.{v, u} C] [HasColimitsOfShape ℕᵒᵖᵒᵖ (Type v)]

/-- The category `ℕᵒᵖᵒᵖ` is filtered. -/
instance : IsFiltered (ℕᵒᵖᵒᵖ) :=
  IsFiltered.of_equivalence (opOpEquivalence ℕ).symm

/-- The transition map `A_m ⟶ A_n` of an `ℕᵒᵖ`-indexed inverse diagram, for `n ≤ m`. -/
public abbrev invTransition (A : ℕᵒᵖ ⥤ C) {n m : ℕ} (h : n ≤ m) :
    A.obj (op m) ⟶ A.obj (op n) :=
  A.map (homOfLE h).op

omit [HasColimitsOfShape ℕᵒᵖᵒᵖ (Type v)] in
private theorem opopHom_eq {n : ℕ} {k : ℕᵒᵖᵒᵖ} (b : op (op n) ⟶ k) :
    b = (homOfLE (leOfHom b.unop.unop)).op.op :=
  Subsingleton.elim _ _

/-- `f` represents `Ψ`: for each `n` the morphism `A_{p n} ⟶ B_n` presents, at the stage `n` of
`B`, the value of `Ψ` on the canonical element. -/
private def Represents (A B : ℕᵒᵖ ⥤ C)
    (Ψ : colimit (B.op ⋙ yoneda) ⟶ colimit (A.op ⋙ yoneda))
    (p : ℕ → ℕ) (f : ∀ n, A.obj (op (p n)) ⟶ B.obj (op n)) : Prop :=
  ∀ n : ℕ,
    ((colimit.ι (A.op ⋙ yoneda) (op (op (p n)))).app (op (B.op.obj (op (op n))))) ((f n).op) =
      (Ψ.app (op (B.op.obj (op (op n)))))
        (((colimit.ι (B.op ⋙ yoneda) (op (op n))).app (op (B.op.obj (op (op n))))) (𝟙 _))

private theorem exists_represents (A B : ℕᵒᵖ ⥤ C)
    (Ψ : colimit (B.op ⋙ yoneda) ⟶ colimit (A.op ⋙ yoneda)) :
    ∃ (p : ℕ → ℕ) (f : ∀ n, A.obj (op (p n)) ⟶ B.obj (op n)), Represents A B Ψ p f := by
  have key : ∀ n : ℕ, ∃ (m : ℕ) (ff : A.obj (op m) ⟶ B.obj (op n)),
      ((colimit.ι (A.op ⋙ yoneda) (op (op m))).app (op (B.op.obj (op (op n))))) (ff.op) =
        (Ψ.app (op (B.op.obj (op (op n)))))
          (((colimit.ι (B.op ⋙ yoneda) (op (op n))).app
            (op (B.op.obj (op (op n))))) (𝟙 _)) := by
    intro n
    obtain ⟨j, gg, hgg⟩ := exists_stage_rep A.op B.op Ψ (op (op n))
    exact ⟨j.unop.unop, gg.unop, hgg⟩
  choose p f hf using key
  exact ⟨p, f, hf⟩

/-- A representing family is compatible with the transition maps, after passing far enough along
the index. -/
private theorem represents_compat {A B : ℕᵒᵖ ⥤ C}
    {Ψ : colimit (B.op ⋙ yoneda) ⟶ colimit (A.op ⋙ yoneda)}
    {p : ℕ → ℕ} {f : ∀ n, A.obj (op (p n)) ⟶ B.obj (op n)} (hf : Represents A B Ψ p f)
    (n m : ℕ) (hnm : n ≤ m) :
    ∃ (k : ℕ) (h₁ : p n ≤ k) (h₂ : p m ≤ k),
      invTransition A h₁ ≫ f n = invTransition A h₂ ≫ f m ≫ invTransition B hnm := by
  obtain ⟨k, b, c, hk⟩ := exists_common_stage_eq A.op B.op Ψ
    ((homOfLE hnm).op.op) ((f n).op) ((f m).op) (hf n) (hf m)
  rw [opopHom_eq b, opopHom_eq c] at hk
  exact ⟨k.unop.unop, leOfHom b.unop.unop, leOfHom c.unop.unop, by
    simpa using congrArg Quiver.Hom.unop hk⟩

/-- The two representing families of an isomorphism of pro-objects compose, after passing far
enough along the index, to a transition map. -/
private theorem represents_comp {A B : ℕᵒᵖ ⥤ C}
    {Φ : colimit (A.op ⋙ yoneda) ⟶ colimit (B.op ⋙ yoneda)}
    {Ψ : colimit (B.op ⋙ yoneda) ⟶ colimit (A.op ⋙ yoneda)}
    (hid : Φ ≫ Ψ = 𝟙 _)
    {p : ℕ → ℕ} {f : ∀ n, A.obj (op (p n)) ⟶ B.obj (op n)} (hf : Represents A B Ψ p f)
    {q : ℕ → ℕ} {g : ∀ n, B.obj (op (q n)) ⟶ A.obj (op n)} (hg : Represents B A Φ q g)
    (n : ℕ) :
    ∃ (k : ℕ) (h₁ : p (q n) ≤ k) (h₂ : n ≤ k),
      invTransition A h₁ ≫ f (q n) ≫ g n = invTransition A h₂ := by
  have hmapz : ((colimit (B.op ⋙ yoneda)).map (Quiver.Hom.op ((g n).op)))
      (((colimit.ι (B.op ⋙ yoneda) (op (op (q n)))).app
        (op (B.op.obj (op (op (q n)))))) (𝟙 (B.op.obj (op (op (q n)))))) =
      ((colimit.ι (B.op ⋙ yoneda) (op (op (q n)))).app
        (op (A.op.obj (op (op n))))) ((g n).op) := by
    have hnat := NatTrans.naturality_apply (colimit.ι (B.op ⋙ yoneda) (op (op (q n))))
      (Quiver.Hom.op ((g n).op)) (𝟙 (B.op.obj (op (op (q n)))))
    simpa using hnat.symm
  have hA : (Ψ.app (op (A.op.obj (op (op n)))))
        (((colimit (B.op ⋙ yoneda)).map (Quiver.Hom.op ((g n).op)))
          (((colimit.ι (B.op ⋙ yoneda) (op (op (q n)))).app
            (op (B.op.obj (op (op (q n)))))) (𝟙 (B.op.obj (op (op (q n))))))) =
      ((colimit (A.op ⋙ yoneda)).map (Quiver.Hom.op ((g n).op)))
        ((Ψ.app (op (B.op.obj (op (op (q n))))))
          (((colimit.ι (B.op ⋙ yoneda) (op (op (q n)))).app
            (op (B.op.obj (op (op (q n)))))) (𝟙 (B.op.obj (op (op (q n))))))) :=
    NatTrans.naturality_apply Ψ (Quiver.Hom.op ((g n).op)) _
  have hright : ((colimit (A.op ⋙ yoneda)).map (Quiver.Hom.op ((g n).op)))
      (((colimit.ι (A.op ⋙ yoneda) (op (op (p (q n))))).app
        (op (B.op.obj (op (op (q n)))))) ((f (q n)).op)) =
      ((colimit.ι (A.op ⋙ yoneda) (op (op (p (q n))))).app (op (A.op.obj (op (op n)))))
        ((g n).op ≫ (f (q n)).op) := by
    have hnat := NatTrans.naturality_apply
      (colimit.ι (A.op ⋙ yoneda) (op (op (p (q n))))) (Quiver.Hom.op ((g n).op))
      ((f (q n)).op)
    simpa using hnat.symm
  have hleft : (Ψ.app (op (A.op.obj (op (op n)))))
      ((Φ.app (op (A.op.obj (op (op n)))))
        (((colimit.ι (A.op ⋙ yoneda) (op (op n))).app
          (op (A.op.obj (op (op n))))) (𝟙 (A.op.obj (op (op n)))))) =
      ((colimit.ι (A.op ⋙ yoneda) (op (op n))).app
        (op (A.op.obj (op (op n))))) (𝟙 (A.op.obj (op (op n)))) := by
    have hv := congrArg (fun t : colimit (A.op ⋙ yoneda) ⟶ colimit (A.op ⋙ yoneda) =>
      t.app (op (A.op.obj (op (op n))))
        (((colimit.ι (A.op ⋙ yoneda) (op (op n))).app
          (op (A.op.obj (op (op n))))) (𝟙 (A.op.obj (op (op n)))))) hid
    simpa using hv
  have key : ((colimit.ι (A.op ⋙ yoneda) (op (op (p (q n))))).app
        (op (A.op.obj (op (op n))))) ((g n).op ≫ (f (q n)).op) =
      ((colimit.ι (A.op ⋙ yoneda) (op (op n))).app
        (op (A.op.obj (op (op n))))) (𝟙 (A.op.obj (op (op n)))) := by
    rw [← hright, hf (q n), ← hA, hmapz, hg n]
    exact hleft
  obtain ⟨k, b, c, hk⟩ := exists_common_stage_eq A.op A.op (𝟙 _) (𝟙 (op (op n)))
    ((g n).op ≫ (f (q n)).op) (𝟙 (A.op.obj (op (op n)))) (by simpa using key) (by simp)
  rw [opopHom_eq b, opopHom_eq c] at hk
  exact ⟨k.unop.unop, leOfHom b.unop.unop, leOfHom c.unop.unop, by
    simpa using congrArg Quiver.Hom.unop hk⟩

/-- **The ladder of a pro-isomorphism, as a predicate.** Two `ℕᵒᵖ`-indexed inverse diagrams are
linked by a ladder when there are families of maps `A_{p n} ⟶ B_n` and `B_{q n} ⟶ A_n`, each
compatible with the transition maps and each composing with the other to a transition map, in
every case after passing far enough along the index. This is the elementary content of an
isomorphism of the pro-objects they present. -/
public def HasProLadder (A B : ℕᵒᵖ ⥤ C) : Prop :=
  ∃ (p : ℕ → ℕ) (f : ∀ n, A.obj (op (p n)) ⟶ B.obj (op n))
    (q : ℕ → ℕ) (g : ∀ n, B.obj (op (q n)) ⟶ A.obj (op n)),
    (∀ n m : ℕ, ∀ hnm : n ≤ m, ∃ (k : ℕ) (h₁ : p n ≤ k) (h₂ : p m ≤ k),
      invTransition A h₁ ≫ f n = invTransition A h₂ ≫ f m ≫ invTransition B hnm) ∧
    (∀ n m : ℕ, ∀ hnm : n ≤ m, ∃ (k : ℕ) (h₁ : q n ≤ k) (h₂ : q m ≤ k),
      invTransition B h₁ ≫ g n = invTransition B h₂ ≫ g m ≫ invTransition A hnm) ∧
    (∀ n : ℕ, ∃ (k : ℕ) (h₁ : p (q n) ≤ k) (h₂ : n ≤ k),
      invTransition A h₁ ≫ f (q n) ≫ g n = invTransition A h₂) ∧
    (∀ n : ℕ, ∃ (k : ℕ) (h₁ : q (p n) ≤ k) (h₂ : n ≤ k),
      invTransition B h₁ ≫ g (p n) ≫ f n = invTransition B h₂)

/-- **The ladder of an isomorphism of pro-objects.** Two `ℕᵒᵖ`-indexed inverse diagrams presenting
isomorphic pro-objects are linked by a ladder. -/
public theorem hasProLadder (A B : ℕᵒᵖ ⥤ C)
    (h : colimit (A.op ⋙ yoneda) ≅ colimit (B.op ⋙ yoneda)) :
    HasProLadder A B := by
  obtain ⟨p, f, hf⟩ := exists_represents A B h.inv
  obtain ⟨q, g, hg⟩ := exists_represents B A h.hom
  exact ⟨p, f, q, g, fun n m hnm => represents_compat hf n m hnm,
    fun n m hnm => represents_compat hg n m hnm,
    fun n => represents_comp h.hom_inv_id hf hg n,
    fun n => represents_comp h.inv_hom_id hg hf n⟩

/-- The colimit of representables on the stages of an `ℕᵒᵖ`-indexed diagram depends on the diagram
only up to isomorphism, so a ladder may be read off an isomorphism of either diagram. -/
public def colimitYonedaIsoOfNatIso {A A' : ℕᵒᵖ ⥤ C} (e : A ≅ A') :
    colimit (A.op ⋙ yoneda) ≅ colimit (A'.op ⋙ yoneda) :=
  HasColimit.isoOfNatIso (Functor.isoWhiskerRight (NatIso.op e.symm) yoneda)

end Ladder

end Stacks.ProObject

end
