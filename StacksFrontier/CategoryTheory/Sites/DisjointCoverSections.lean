module

public import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of a sheaf over a pairwise disjoint covering family

A covering family `π i : V i ⟶ B` whose members are pairwise disjoint — any object mapping to
two distinct members over `B` is covered by the empty sieve — imposes no condition on a family
of sections: the restrictions to an overlap automatically agree, because the overlap carries only
one section. Consequently the sections of a sheaf over `B` are exactly the families of sections
over the members, that is, a product.

## Main results

* `CategoryTheory.Presieve.IsSheaf.existsUnique_section_of_disjoint_arrows`: for a sheaf of
  types, every family of sections over the members of a disjoint covering family glues to a
  unique section over `B`.
* `CategoryTheory.Presheaf.IsSheaf.isLimitFanSectionsOfDisjointArrows`: for a sheaf with values
  in an arbitrary category, the sections over `B` together with the restriction maps form a
  product of the sections over the members.

## Implementation notes

Disjointness is phrased without pullbacks, matching `CategoryTheory.Presieve.Arrows.Compatible`:
whenever `gi ≫ π i = gj ≫ π j` with `i ≠ j`, the common source is covered by the empty sieve.
A sheaf has at most one section there, since the empty
family of elements has a unique amalgamation, so compatibility is automatic. For the diagonal
case `i = j` the members are asked to be monomorphisms, which turns the same equation into
`gi = gj`.

The statement for a sheaf valued in an arbitrary category is obtained from the one for sheaves of
types, applied to the sheaf of morphisms out of each object of the coefficient category; this is
the definition of `CategoryTheory.Presheaf.IsSheaf`, so no concreteness is needed and the
resulting universal property is the one of a product fan.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v₂ u₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {B : C} {I : Type*} {V : I → C}

private lemma subsingleton_obj_of_bot_mem {P : Cᵒᵖ ⥤ Type w} (hP : Presieve.IsSheaf J P) {Z : C}
    (hZ : (⊥ : Sieve Z) ∈ J Z) : Subsingleton (P.obj (op Z)) := by
  obtain ⟨_t, -, hu⟩ := hP ⊥ hZ (fun _ _ hf ↦ hf.elim) (fun _ _ _ _ _ _ _ h₁ ↦ h₁.elim)
  exact ⟨fun p q ↦ (hu p fun _ _ hf ↦ hf.elim).trans (hu q fun _ _ hf ↦ hf.elim).symm⟩

/-- **Sections glue over a pairwise disjoint covering family, with no compatibility condition.**
Given a covering family `π i : V i ⟶ B` of monomorphisms such that any object mapping to two
distinct members over `B` is covered by the empty sieve, every family of sections of a sheaf of
types over the members restricts from a unique section over `B`. -/
@[sga "4 II 4.6.2" "more general"]
theorem Presieve.IsSheaf.existsUnique_section_of_disjoint_arrows
    {P : Cᵒᵖ ⥤ Type w} (hP : Presieve.IsSheaf J P) (π : ∀ i, V i ⟶ B)
    (hcov : Sieve.ofArrows V π ∈ J B) (hmono : ∀ i, Mono (π i))
    (hdisj : ∀ i j, i ≠ j → ∀ {Z : C} (gi : Z ⟶ V i) (gj : Z ⟶ V j),
      gi ≫ π i = gj ≫ π j → (⊥ : Sieve Z) ∈ J Z)
    (x : ∀ i, P.obj (op (V i))) :
    ∃! t : P.obj (op B), ∀ i, P.map (π i).op t = x i := by
  refine (Presieve.isSheafFor_arrows_iff _ _).1 (hP.isSheafFor _ hcov) x ?_
  intro i j Z gi gj h
  rcases eq_or_ne i j with rfl | hij
  · have := hmono i
    rw [(cancel_mono (π i)).1 h]
  · have := subsingleton_obj_of_bot_mem hP (hdisj i j hij gi gj h)
    exact Subsingleton.elim _ _

/-- **The sections of a sheaf over a pairwise disjoint covering family form a product.** The
restriction maps to the members of such a family exhibit the sections over `B` as a product of
the sections over the members, for a sheaf valued in an arbitrary category. -/
@[ega "0 3.1.2" "Pairwise disjoint covers"]
noncomputable def Presheaf.IsSheaf.isLimitFanSectionsOfDisjointArrows
    {A : Type u₂} [Category.{v₂} A] {F : Cᵒᵖ ⥤ A} (hF : Presheaf.IsSheaf J F)
    (π : ∀ i, V i ⟶ B) (hcov : Sieve.ofArrows V π ∈ J B) (hmono : ∀ i, Mono (π i))
    (hdisj : ∀ i j, i ≠ j → ∀ {Z : C} (gi : Z ⟶ V i) (gj : Z ⟶ V j),
      gi ≫ π i = gj ≫ π j → (⊥ : Sieve Z) ∈ J Z) :
    IsLimit (Fan.mk (F.obj (op B)) fun i ↦ F.map (π i).op) := by
  refine Fan.IsLimit.mk _
    (fun s ↦ ((hF s.pt).existsUnique_section_of_disjoint_arrows π hcov hmono hdisj
      (fun i ↦ s.proj i)).choose) (fun s i ↦ ?_) (fun s m hm ↦ ?_)
  · exact ((hF s.pt).existsUnique_section_of_disjoint_arrows π hcov hmono hdisj
      (fun i ↦ s.proj i)).choose_spec.1 i
  · exact ((hF s.pt).existsUnique_section_of_disjoint_arrows π hcov hmono hdisj
      (fun i ↦ s.proj i)).choose_spec.2 m hm

end CategoryTheory

end
