module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.ElementwiseEffaceable
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.MapExact

/-!
# Morphisms of δ-functors composed with an exact functor; transport of effaceability

A morphism of cohomological δ-functors `F ⟶ G` ([Stacks, Tag 010Q]) composed with an exact functor
`Φ` is a morphism of the composite δ-functors `CategoryTheory.DeltaFunctor.mapExact`.

Elementwise effaceability (`CategoryTheory.DeltaFunctor.ElementwiseEffaceable`) depends only on the
component functors, so it transports along any family of natural isomorphisms of components, with
no compatibility with the connecting morphisms required.

## Main definitions

* `CategoryTheory.DeltaFunctor.mapExactHom` — the composite of a morphism with `Φ`.

## Main results

* `CategoryTheory.DeltaFunctor.ElementwiseEffaceable.of_iso` — transport of elementwise
  effaceability along isomorphisms of the component functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w

namespace CategoryTheory.DeltaFunctor

section MapExact

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] (Φ : B ⥤ C) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- A morphism of δ-functors, composed with an exact functor. -/
def mapExactHom {F G : DeltaFunctor A B} (η : F ⟶ G) : F.mapExact Φ ⟶ G.mapExact Φ where
  app n := Functor.whiskerRight (η.app n) Φ
  comm hS n := (Φ.map_comp _ _).symm.trans ((congrArg Φ.map (η.comm hS n)).trans (Φ.map_comp _ _))

/-- The degree-`n` component of `mapExactHom Φ η` is the whiskering of the degree-`n` component of
`η` by `Φ`. -/
@[simp]
lemma mapExactHom_app {F G : DeltaFunctor A B} (η : F ⟶ G) (n : ℕ) :
    (mapExactHom Φ η).app n = Functor.whiskerRight (η.app n) Φ :=
  rfl

end MapExact

namespace ElementwiseEffaceable

variable {A : Type*} [Category* A] [Abelian A] {R : Type*} [Ring R]

/-- **Elementwise effaceability transports along isomorphisms of the component functors**: a class
of `Fⁿ⁺¹(X)` is killed by a monomorphism as soon as its image in `Gⁿ⁺¹(X)` is, by naturality. -/
theorem of_iso {F G : DeltaFunctor A (ModuleCat.{w} R)} [G.ElementwiseEffaceable]
    (e : ∀ n, F.functor n ≅ G.functor n) : F.ElementwiseEffaceable where
  exists_mono {X n} x := by
    obtain ⟨I, ι, hι, h⟩ := ElementwiseEffaceable.exists_mono (F := G) ((e (n + 1)).hom.app X x)
    refine ⟨I, ι, hι, ?_⟩
    have h' := ConcreteCategory.congr_hom ((e (n + 1)).hom.naturality ι) x
    simp only [ConcreteCategory.comp_apply] at h'
    rw [h] at h'
    have h'' := congrArg ((e (n + 1)).inv.app I) h'
    rwa [← ConcreteCategory.comp_apply, Iso.hom_inv_id_app, ConcreteCategory.id_apply,
      map_zero] at h''

end ElementwiseEffaceable

end CategoryTheory.DeltaFunctor

end
