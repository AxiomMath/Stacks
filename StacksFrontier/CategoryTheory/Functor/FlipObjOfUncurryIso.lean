module

public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Partial evaluation of an isomorphism of uncurried bifunctors

An isomorphism `uncurry T ⋙ G ≅ (F × F) ⋙ uncurry T'` between a bifunctor `T` followed by `G`
and a bifunctor `T'` preceded by `F` in both variables gives, for every `P`, an isomorphism
`T(-, P) ⋙ G ≅ F ⋙ T'(-, F P)` of functors of the first variable.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

/-- An isomorphism `uncurry T ⋙ G ≅ (F × F) ⋙ uncurry T'`, evaluated with a fixed second
argument `P`: `T(-, P) ⋙ G ≅ F ⋙ T'(-, F P)`. -/
def flipObjIsoOfUncurryIso {C E C' E' : Type*} [Category C] [Category E] [Category C']
    [Category E'] {T : C ⥤ C ⥤ E} {T' : C' ⥤ C' ⥤ E'} {F : C ⥤ C'} {G : E ⥤ E'}
    (τ : Functor.uncurry.obj T ⋙ G ≅ F.prod F ⋙ Functor.uncurry.obj T') (P : C) :
    T.flip.obj P ⋙ G ≅ F ⋙ T'.flip.obj (F.obj P) :=
  NatIso.ofComponents (fun K => τ.app (K, P)) (fun f => by
    simpa using τ.hom.naturality (Prod.mkHom f (𝟙 P)))

/-- The component of `flipObjIsoOfUncurryIso τ P` at `K` is the component of `τ` at `(K, P)`. -/
@[simp]
theorem flipObjIsoOfUncurryIso_app {C E C' E' : Type*} [Category C] [Category E] [Category C']
    [Category E'] {T : C ⥤ C ⥤ E} {T' : C' ⥤ C' ⥤ E'} {F : C ⥤ C'} {G : E ⥤ E'}
    (τ : Functor.uncurry.obj T ⋙ G ≅ F.prod F ⋙ Functor.uncurry.obj T') (P K : C) :
    (flipObjIsoOfUncurryIso τ P).app K = τ.app (K, P) :=
  rfl

end CategoryTheory.Functor

end
