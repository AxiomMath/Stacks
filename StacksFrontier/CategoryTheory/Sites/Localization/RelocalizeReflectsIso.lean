module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# Relocalization reflects isomorphisms

Let `f : V ⟶ U` be a morphism of a category `C`. The presheaf level relocalization functor
`Λ = CategoryTheory.OverShriek.relocalizePresheafFunctor f` is *not* full — a morphism of
presheaves on `C/U` need not respect the structure morphisms to `V` — but it is faithful and
*conservative*: a morphism of presheaves on `C/V` whose image under `Λ` is an isomorphism is
itself an isomorphism.

## Main results

* `CategoryTheory.OverShriek.map_relocalizePresheafFunctor_app_mk`: the formula for `Λ σ` on
  sections.
* `CategoryTheory.OverShriek.isIso_of_isIso_map_relocalizePresheafFunctor`: `Λ` reflects
  isomorphisms.

## References

* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
* [Stacks Project, Tag 04IL](https://stacks.math.columbia.edu/tag/04IL)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-- A section of `(relocalizePresheafFunctor f).obj G` over `W` is a factorization `ψ` of the
structure morphism of `W` through `f` together with a section of `G` over `(W.left, ψ)`, and the
image of `σ` applies `σ` to the second component. -/
theorem map_relocalizePresheafFunctor_app_mk {G H : (Over V)ᵒᵖ ⥤ Type v} (σ : G ⟶ H)
    (W : (Over U)ᵒᵖ) (ψ : W.unop.left ⟶ V) (h : ψ ≫ f = W.unop.hom)
    (s : G.obj (op (Over.mk ψ))) :
    ((relocalizePresheafFunctor f).map σ).app W ⟨⟨ψ, s⟩, h⟩
      = ⟨⟨ψ, σ.app (op (Over.mk ψ)) s⟩, h⟩ :=
  rfl

/-- **Relocalization reflects isomorphisms.** If `Λ σ` is an isomorphism of presheaves on `C/U`
then `σ` is an isomorphism of presheaves on `C/V`. -/
theorem isIso_of_isIso_map_relocalizePresheafFunctor {G H : (Over V)ᵒᵖ ⥤ Type v} (σ : G ⟶ H)
    [IsIso ((relocalizePresheafFunctor f).map σ)] : IsIso σ := by
  have (T : (Over V)ᵒᵖ) : IsIso (σ.app T) := by
    have hbij := (isIso_iff_bijective
      (((relocalizePresheafFunctor f).map σ).app
        (op (Over.mk (T.unop.hom ≫ f))))).mp inferInstance
    rw [isIso_iff_bijective]
    refine ⟨fun a b hab ↦ ?_, fun z ↦ ?_⟩
    · have key : (⟨⟨T.unop.hom, a⟩, rfl⟩ :
            ((relocalizePresheafFunctor f).obj G).obj (op (Over.mk (T.unop.hom ≫ f))))
          = ⟨⟨T.unop.hom, b⟩, rfl⟩ :=
        hbij.1 (congrArg (fun y : H.obj T ↦
          (⟨⟨T.unop.hom, y⟩, rfl⟩ :
            ((relocalizePresheafFunctor f).obj H).obj
              (op (Over.mk (T.unop.hom ≫ f))))) hab)
      exact eq_of_heq (Sigma.ext_iff.mp (congrArg Subtype.val key)).2
    · obtain ⟨p, hp⟩ := hbij.2 (⟨⟨T.unop.hom, z⟩, rfl⟩ :
        ((relocalizePresheafFunctor f).obj H).obj (op (Over.mk (T.unop.hom ≫ f))))
      obtain ⟨⟨ψ, s⟩, hψ⟩ := p
      have hp' : (⟨⟨ψ, σ.app (op (Over.mk ψ)) s⟩, hψ⟩ :
            ((relocalizePresheafFunctor f).obj H).obj (op (Over.mk (T.unop.hom ≫ f))))
          = ⟨⟨T.unop.hom, z⟩, rfl⟩ := hp
      have hp'' : (⟨ψ, σ.app (op (Over.mk ψ)) s⟩ :
            Σ χ : T.unop.left ⟶ V, H.obj (op (Over.mk χ)))
          = ⟨T.unop.hom, z⟩ := congrArg Subtype.val hp'
      obtain ⟨hfst, hsnd⟩ := Sigma.ext_iff.mp hp''
      subst hfst
      exact ⟨s, eq_of_heq hsnd⟩
  exact NatIso.isIso_of_isIso_app _

end CategoryTheory.OverShriek

end
