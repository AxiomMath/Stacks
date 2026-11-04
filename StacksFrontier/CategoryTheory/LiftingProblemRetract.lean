module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.NatIso

/-!
# A lifting problem with a retraction: the base case and the composition step

Fix a functor `F : D ⥤ H` — read it as restriction along an inclusion of opens — and call a
*solution* of the lifting problem posed by `α : P ⟶ F.obj E` a pair of an object `R` over `D`, a
morphism `β : R ⟶ E` and a retraction exhibiting `P` as a direct summand of `F.obj R`
compatibly with `α` and `F.map β`. Two statements about such solutions are proved here, both pure
category theory: the problem is solved when `F` is isomorphic to the identity, and a solution
transported along one `F` composes with a solution along another.

This is the skeleton of the induction in the proof of [Stacks, Tag 09IM], which grows a
quasi-compact open `U` to the whole scheme one affine open at a time while carrying a lift of a
map `P ⟶ E|_U`. The first statement is the base of that induction, where the open is `U` itself
and the lift is `P` with its own map; the second is the step, where a lift already obtained over
`W` is composed with the enlargement from `W` to `W ⊔ V`. Elaborating either step against the
restriction functors of a scheme costs an elaboration budget that the generic statements do not;
proving them here and applying them once in term mode is what keeps the geometric proof inside
the default heartbeat budget.

## Main results

* `Stacks.LiftingProblem.exists_retract_lift_of_isoId`: for `F ≅ 𝟭 C`, every `a : P ⟶ F.obj A`
  is `i ≫ F.map β` for some `β : P ⟶ A` and some split monomorphism `i : P ⟶ F.obj P`. The
  lifting problem over the open one starts with is solved by the given object.
* `Stacks.LiftingProblem.exists_retract_lift_comp`: a solution over `R₁` along `F`, together with
  a solution over `R₂` along `G` with the two maps compatible, gives a solution over `R₂` along a
  functor `L ≅ G ⋙ F`.

## Implementation notes

Nothing here assumes additivity, an abelian category or a derived category: the two statements
are about a functor, a natural isomorphism and the naturality square of that isomorphism at the
morphism being lifted. The retraction is carried as a pair `(i, p)` with `i ≫ p = 𝟙 P` rather
than as `CategoryTheory.Retract`, which is the form the conclusion of [Stacks, Tag 09IM] takes
and the form its induction has to reproduce at each step.

Two further transports are needed by the geometric proof and are deliberately *not* stated here:
carrying a solution across the identification of an open with its copy inside a larger open, and
carrying one back from the top open to the scheme. Both mention a specific presentation of
restriction in their hypotheses — which of the five spellings the two sides are written in — so
they belong where that choice is made, not in a file about an abstract functor.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.LiftingProblem

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- **The lifting problem is solved where the functor is the identity.** If `θ : F ≅ 𝟭 C` then any
`a : P ⟶ F.obj A` factors as `i ≫ F.map β` with `i : P ⟶ F.obj P` a split monomorphism: take
`β` to be `a` read through `θ` and `i` to be the component of `θ.inv`.

This is the base case of the induction in [Stacks, Tag 09IM]: over the given open `U` the lift is
`P` itself, with `P` a direct summand of its own restriction. -/
theorem exists_retract_lift_of_isoId {C : Type u₁} [Category.{v₁} C] (F : C ⥤ C) (θ : F ≅ 𝟭 C)
    (P A : C) (a : P ⟶ F.obj A) :
    ∃ (β : P ⟶ A) (i : P ⟶ F.obj P) (q : F.obj P ⟶ P),
      i ≫ q = 𝟙 P ∧ i ≫ F.map β = a := by
  refine ⟨a ≫ θ.hom.app A, θ.inv.app P, θ.hom.app P, by simp, ?_⟩
  have hnat := θ.inv.naturality (a ≫ θ.hom.app A)
  simp only [Functor.id_map] at hnat
  rw [← hnat]
  simp

/-- **Two solutions compose.** Let `L ≅ G ⋙ F`. Given `P` a direct summand of `F.obj R₁`
compatibly with `b : R₁ ⟶ G.obj E` and with `α : P ⟶ L.obj E`, and `R₁` a direct summand of
`G.obj R₂` compatibly with `c : R₂ ⟶ E` — that is, `j ≫ G.map c = b` — the object `R₂` solves the
lifting problem for `α` along `L`.

This is the step of the induction in [Stacks, Tag 09IM]: a lift already obtained over an open `W`
is composed with the enlargement of `W` by one affine open, and the compatibility with the map to
the ambient object is what the naturality of the comparison `L ≅ G ⋙ F` transports. -/
theorem exists_retract_lift_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {H : Type u₃} [Category.{v₃} H] (F : D ⥤ H) (G : C ⥤ D) (L : C ⥤ H) (e : L ≅ G ⋙ F)
    {P : H} {R₁ : D} {R₂ E : C}
    (i : P ⟶ F.obj R₁) (p : F.obj R₁ ⟶ P) (hip : i ≫ p = 𝟙 P)
    (j : R₁ ⟶ G.obj R₂) (q : G.obj R₂ ⟶ R₁) (hjq : j ≫ q = 𝟙 R₁)
    (b : R₁ ⟶ G.obj E) (c : R₂ ⟶ E) (hbc : j ≫ G.map c = b)
    (α : P ⟶ L.obj E) (hα : i ≫ F.map b = α ≫ (e.app E).hom) :
    ∃ (i' : P ⟶ L.obj R₂) (p' : L.obj R₂ ⟶ P), i' ≫ p' = 𝟙 P ∧ i' ≫ L.map c = α := by
  refine ⟨i ≫ F.map j ≫ (e.app R₂).inv, (e.app R₂).hom ≫ F.map q ≫ p, ?_, ?_⟩
  · calc
      (i ≫ F.map j ≫ (e.app R₂).inv) ≫ ((e.app R₂).hom ≫ F.map q ≫ p) =
          (i ≫ F.map j) ≫ F.map q ≫ p := by
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = i ≫ F.map (j ≫ q) ≫ p := by simp only [Category.assoc, F.map_comp]
      _ = i ≫ p := by rw [hjq, F.map_id, Category.id_comp]
      _ = 𝟙 P := hip
  · have hn := e.hom.naturality c
    change L.map c ≫ (e.app E).hom = (e.app R₂).hom ≫ F.map (G.map c) at hn
    apply (cancel_mono (e.app E).hom).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hn, ← Functor.map_comp, hbc, hα]

end Stacks.LiftingProblem

end
