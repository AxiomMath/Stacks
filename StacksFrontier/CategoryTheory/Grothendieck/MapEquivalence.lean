module

public import Mathlib.CategoryTheory.Grothendieck

/-!
# Grothendieck constructions of degreewise equivalences

A natural transformation `α : F ⟶ G` of functors into `Cat` induces the functor
`Grothendieck.map α` between the Grothendieck constructions. If every component of `α` is
faithful, full or essentially surjective, so is `Grothendieck.map α`; in particular a natural
transformation whose components are equivalences induces an equivalence.

## Main results

* `CategoryTheory.Grothendieck.faithful_map_of_forall_faithful_mapEquivalence`,
  `CategoryTheory.Grothendieck.full_map_of_forall_full_mapEquivalence`,
  `CategoryTheory.Grothendieck.essSurj_map_mapEquivalence`.
* `CategoryTheory.Grothendieck.isEquivalence_map_mapEquivalence`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Grothendieck

variable {I : Type*} [Category* I] {F G : I ⥤ Cat.{v, u}} (α : F ⟶ G)

/-- `Grothendieck.map α` is faithful when every component of `α` is. -/
theorem faithful_map_of_forall_faithful_mapEquivalence [∀ c, (α.app c).toFunctor.Faithful] :
    (map α).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨b, f'⟩ := f
    obtain ⟨b', g'⟩ := g
    have hb : b = b' := congrArg Hom.base h
    subst hb
    have h' := Grothendieck.congr h
    simp only [map_map_fiber] at h'
    have := (α.app Y.base).toFunctor.map_injective
      ((cancel_epi _).1 (h'.trans (eqToHom_trans_assoc _ _ _)))
    subst this
    rfl

/-- `Grothendieck.map α` is full when every component of `α` is. -/
theorem full_map_of_forall_full_mapEquivalence [∀ c, (α.app c).toFunctor.Full] : (map α).Full where
  map_surjective {X Y} g := by
    obtain ⟨b, g'⟩ := g
    refine ⟨⟨b, (α.app Y.base).toFunctor.preimage
      (eqToHom congr(($(α.naturality b)).toFunctor.obj X.fiber) ≫ g')⟩, ?_⟩
    refine Grothendieck.ext _ _ rfl ?_
    simp only [map_map_fiber, Functor.map_preimage]
    exact (eqToHom_trans_assoc _ _ _).trans ((eqToHom_trans_assoc _ _ _).trans
      ((congrArg (· ≫ g') (eqToHom_refl _ _)).trans (Category.id_comp g')))

/-- `Grothendieck.map α` is essentially surjective when every component of `α` is. -/
theorem essSurj_map_mapEquivalence [∀ c, (α.app c).toFunctor.EssSurj] : (map α).EssSurj where
  mem_essImage Y :=
    ⟨⟨Y.base, (α.app Y.base).toFunctor.objPreimage Y.fiber⟩,
      ⟨(ι G Y.base).mapIso ((α.app Y.base).toFunctor.objObjPreimageIso Y.fiber)⟩⟩

/-- `Grothendieck.map α` is an equivalence when every component of `α` is. -/
theorem isEquivalence_map_mapEquivalence [∀ c, (α.app c).toFunctor.IsEquivalence] :
    (map α).IsEquivalence :=
  have := faithful_map_of_forall_faithful_mapEquivalence α
  have := full_map_of_forall_full_mapEquivalence α
  have := essSurj_map_mapEquivalence α
  { }

/-- `Grothendieck.map α` preserves morphisms with invertible fibre component. -/
theorem isIso_map_map_fiber_mapEquivalence {X Y : Grothendieck F} (f : X ⟶ Y) [IsIso f.fiber] :
    IsIso ((map α).map f).fiber := by
  simp only [map_map_fiber]
  refine IsIso.comp_isIso' ?_ (Functor.map_isIso _ f.fiber)
  exact (eqToIso congr(($(α.naturality f.base)).toFunctor.obj X.fiber).symm).isIso_hom

end CategoryTheory.Grothendieck
