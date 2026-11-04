module

public import Mathlib.CategoryTheory.Grothendieck
public import StacksFrontier.CategoryTheory.Sites.AbelianPullbackExact.LanCriterion

/-!
# The fibre inclusion into a Grothendieck construction has exact abelian pullback

Let `F : C ⥤ Cat` and let `b : C`. The comma category of the fibre inclusion
`CategoryTheory.Grothendieck.ι F b` over an object `V` of the Grothendieck construction is the
disjoint union, over the morphisms `α : V.base ⟶ b`, of the category of objects of `F.obj b`
under `(F.map α).obj V.fiber`: a structured arrow consists of an object `R` of the fibre together
with a morphism `V ⟶ (b, R)`, and such a morphism is a pair `(α, φ)` with
`φ : (F.map α).obj V.fiber ⟶ R`, while a morphism of structured arrows is the identity on the
base and therefore cannot change `α`.

Each summand has an initial object, namely `((F.map α).obj V.fiber, 𝟙)`. So the comma category
is pseudofiltered, and the criterion
`Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_of_span_and_coequalizer` applies
with no hypothesis on `F` at all: the pullback of abelian sheaves along a continuous fibre
inclusion is left exact.

## Main results

* `Stacks.Sites.AbelianPullback.weaklyInitial_structuredArrow_fibreInclusion`: below every object
  of the comma category of a fibre inclusion there is a weakly initial one with at most one
  morphism to any object.
* `Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_fibreInclusion` and
  `.preservesMonomorphisms_sheafPullback_fibreInclusion`: the pullback of abelian sheaves along a
  continuous fibre inclusion is left exact.

## Implementation notes

The fibre of the Grothendieck construction is a bundled category, so the base of
`(Grothendieck.ι F b).obj R` is `b` only up to unfolding the fibre inclusion, and the ambient
category instance of a hom-set reached through that projection is spelled through the projection
rather than through `b`. Simp lemmas about `F.obj b` then fail to apply to terms the elaborator
has produced through the projection. The remedy used here is to destructure a structured arrow
into its object and its two components and to normalize their types with `dsimp only` along
`rfl`-lemmas for the projections — `fibreInclusion_obj_base` and the three that follow — after
which every term lives in `F.obj b` with one spelling and the `eqToHom` bookkeeping of
`CategoryTheory.Grothendieck.ext` collapses by `eqToHom_trans_assoc`. The local
`implicit_reducible` attribute on the fibre inclusion is what makes those lemmas hold by `rfl`.

The weak-initiality statement is used rather than initiality of each connected component because
the connected components of the comma category are not individually named: an object determines
its `α`, and that is all the criterion needs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe uA u v u₂ v₂

namespace Stacks.Sites.AbelianPullback

attribute [local implicit_reducible] CategoryTheory.Grothendieck.ι

section Comma

variable {C : Type u} [Category.{v} C] {F : C ⥤ Cat.{v₂, u₂}} {b : C} {V : Grothendieck F}

private theorem fibreInclusion_obj_base (R : F.obj b) :
    ((Grothendieck.ι F b).obj R).base = b := rfl

private theorem fibreInclusion_obj_fiber (R : F.obj b) :
    ((Grothendieck.ι F b).obj R).fiber = R := rfl

private theorem fromPUnit_obj_eq (X : Discrete PUnit.{1}) :
    (Functor.fromPUnit V).obj X = V := rfl

private theorem fromPUnit_map_base {X Y : Discrete PUnit.{1}} (f : X ⟶ Y) :
    ((Functor.fromPUnit V).map f).base = 𝟙 V.base := rfl

private theorem fibreInclusion_map_base {X Y : F.obj b} (f : X ⟶ Y) :
    ((Grothendieck.ι F b).map f).base = 𝟙 b := rfl

private theorem fibreInclusion_map_fiber {X Y : F.obj b} (f : X ⟶ Y) :
    ((Grothendieck.ι F b).map f).fiber
      = eqToHom (show (F.map (𝟙 b)).toFunctor.obj X = X by simp) ≫ f := rfl

private theorem fiber_eq_of_eq {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g)
    (hb : f.base = g.base) : eqToHom (by rw [hb]) ≫ f.fiber = g.fiber := by
  subst h; simp

/-- Below every object of the comma category of a fibre inclusion there is an object which maps
to every object mapping to it and admits at most one morphism to any object: namely the initial
object `((F.map α).obj V.fiber, 𝟙)` of the summand indexed by the base component `α` of the
structured arrow. -/
theorem weaklyInitial_structuredArrow_fibreInclusion
    (x : StructuredArrow V (Grothendieck.ι F b)) :
    ∃ W : StructuredArrow V (Grothendieck.ι F b),
      (∀ {y : StructuredArrow V (Grothendieck.ι F b)}, (y ⟶ x) → Nonempty (W ⟶ y)) ∧
        ∀ {y : StructuredArrow V (Grothendieck.ι F b)} (q q' : W ⟶ y), q = q' := by
  obtain ⟨⟨⟩, R, hx⟩ := x
  obtain ⟨β, ψ⟩ := hx
  dsimp only [fibreInclusion_obj_base, fibreInclusion_obj_fiber, fromPUnit_obj_eq] at β ψ
  refine ⟨StructuredArrow.mk (Y := (F.map β).toFunctor.obj V.fiber)
    (Grothendieck.Hom.mk β (𝟙 _)), ?_, ?_⟩
  · intro y g
    obtain ⟨⟨⟩, S, hy⟩ := y
    obtain ⟨γ, χ⟩ := hy
    dsimp only [fibreInclusion_obj_base, fibreInclusion_obj_fiber, fromPUnit_obj_eq] at γ χ
    obtain ⟨⟨⟩, r, hr⟩ := g
    have hb : γ = β := by
      have h := congrArg Grothendieck.Hom.base hr
      dsimp only [Grothendieck.comp_base, fibreInclusion_map_base, fromPUnit_map_base,
        fibreInclusion_obj_base, fibreInclusion_obj_fiber, fromPUnit_obj_eq] at h
      simpa using h.symm
    subst hb
    refine ⟨StructuredArrow.homMk χ (Grothendieck.ext _ _ ?_ ?_)⟩
    · dsimp only [fibreInclusion_map_base]
      exact Category.comp_id _
    · dsimp only [Grothendieck.comp_fiber, fibreInclusion_map_base, fibreInclusion_map_fiber]
      simp only [StructuredArrow.mk_hom_eq_self, CategoryTheory.Functor.map_id, Category.id_comp,
        eqToHom_trans_assoc, eqToHom_refl]
  · intro y q q'
    apply (StructuredArrow.hom_eq_iff q q').mpr
    have h2 := fiber_eq_of_eq ((StructuredArrow.w q).trans (StructuredArrow.w q').symm) rfl
    dsimp only [Grothendieck.comp_fiber, fibreInclusion_map_base,
      fibreInclusion_map_fiber] at h2
    simp only [StructuredArrow.mk_hom_eq_self, CategoryTheory.Functor.map_id, Category.id_comp,
      eqToHom_trans_assoc] at h2
    exact (cancel_epi _).mp h2

end Comma

section Sheaves

variable {C : Type u} [SmallCategory C] (F : C ⥤ Cat.{u, u}) (b : C)
  (J : GrothendieckTopology (F.obj b)) (K : GrothendieckTopology (Grothendieck F))
  [(Grothendieck.ι F b).IsContinuous J K]
  (A : Type uA) [Category.{u} A] [Abelian A] [HasColimitsOfSize.{u, u} A] [AB5OfSize.{u, u} A]
  [HasSheafify K A]

/-- The pullback of sheaves with values in an abelian category with exact filtered colimits along
a continuous fibre inclusion into a Grothendieck construction preserves finite limits, with no
hypothesis on `F`. -/
theorem preservesFiniteLimits_sheafPullback_fibreInclusion :
    PreservesFiniteLimits ((Grothendieck.ι F b).sheafPullback A J K) :=
  preservesFiniteLimits_sheafPullback_of_span_and_coequalizer _ A J K
    ⟨fun _ => (span_and_coequalizer_op_of_weaklyInitial
        weaklyInitial_structuredArrow_fibreInclusion).1,
      fun _ => (span_and_coequalizer_op_of_weaklyInitial
        weaklyInitial_structuredArrow_fibreInclusion).2⟩

/-- The pullback of abelian sheaves along a continuous fibre inclusion into a Grothendieck
construction preserves monomorphisms. -/
theorem preservesMonomorphisms_sheafPullback_fibreInclusion :
    ((Grothendieck.ι F b).sheafPullback A J K).PreservesMonomorphisms := by
  have := preservesFiniteLimits_sheafPullback_fibreInclusion F b J K A
  infer_instance

end Sheaves

end Stacks.Sites.AbelianPullback

end
