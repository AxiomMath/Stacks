module

public import Mathlib.CategoryTheory.Equivalence

/-!
# A roof extending a map off a subobject, transported along two equivalences

Fix a functor `res : C ⥤ D` — read it as restriction to an open — and call a *roof extending
`a : res P ⟶ res E`* a triple of an object `R`, a morphism `β : R ⟶ P` whose restriction is
invertible and a morphism `γ : R ⟶ E` whose restriction is `res β ≫ a`. That is the conclusion of
[Stacks, Tag 08EH]: a map defined only over the open extends over the whole space once the source
is replaced by something with the same restriction.

This file transports the existence of such roofs, for objects in prescribed classes, along a pair
of equivalences `Φ : C ≌ C'` and `Ψ : D ≌ D'` commuting with the two restriction functors. It is
pure category theory: no additivity, no triangulated structure, no geometry.

## Why this exists

[Stacks, Tag 08EH] is formalized only at `X = Spec A`, and the obstruction to moving it is that
the middle object of that roof is a derived tensor product over the affine site of `A`, so
transporting the statement means carrying that tensor product across an isomorphism. Once the
middle object is *existentially quantified* — which is what
`Stacks.Perfect.SupportedLiftAffineSpec.exists_roof_of_isCompact` does — the statement names no
tensor product at all, and nothing stands in the way of transporting it. The consumer is the
two-open step of [Stacks, Tag 09IM], which needs the roof at an affine *open* of a general
scheme.

## Main results

* `Stacks.LiftingProblem.exists_roof_of_equivalence`.

## Implementation notes

The comparison is `κ : Φ.functor ⋙ res' ≅ res ⋙ Ψ.functor`, and the only two facts used about
`Ψ` are that its functor is full — to pull the transported map back across it — and that it
preserves isomorphisms. The classes of objects are carried by five implications rather than by
equivalences: three to move the hypotheses on the given objects backwards along `Φ.inverse`, and
two to move the conclusion on the produced object forwards along `Φ.functor`. Stating them
separately is what lets a consumer use the honest predicates on both sides — "perfect on `X`" and
"perfect on `Spec A`" — instead of one transported along the equivalence.

The whole content is the isomorphism `res' X' ≅ Ψ (res (Φ⁻¹ X'))`, the counit of `Φ` followed by
`κ`, along which the given map is read over `C`. Both halves of the conclusion are then the
naturality square of `κ` — at `β` for the invertibility, at `γ` for the extension equation — with
the extension equation of the roof over `C` in between; the counit of `Φ` cancels against its
inverse at the end.

## References

* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.LiftingProblem

variable {C : Type u₁} {C' : Type u₂} {D : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} C'] [Category.{v₃} D] [Category.{v₄} D']

/-- **Roofs transport along a pair of equivalences commuting with the restriction functors.**
Let `res : C ⥤ D` and `res' : C' ⥤ D'`, let `Φ : C ≌ C'` and `Ψ : D ≌ D'` and let
`κ : Φ.functor ⋙ res' ≅ res ⋙ Ψ.functor`. Suppose that over `C` every `a : res P ⟶ res E`, for
`P` in the classes `Pp` and `Sp` and `E` in `Qp`, extends to a roof `P ←β— R —γ→ E` with `R`
again in `Pp` and `Sp` and `res β` invertible. Then the same holds over `C'` for the classes
`Pp'`, `Sp'`, `Qp'`, provided the five implications relating them hold.

The produced object is `Φ (R)` for the `R` obtained over `C`, and the two morphisms are the
images of `β` and `γ` followed by the counit of `Φ`. -/
theorem exists_roof_of_equivalence {res : C ⥤ D} {res' : C' ⥤ D'} (Φ : C ≌ C') (Ψ : D ≌ D')
    (κ : Φ.functor ⋙ res' ≅ res ⋙ Ψ.functor) {Pp Sp Qp : C → Prop} {Pp' Sp' Qp' : C' → Prop}
    (hPback : ∀ P' : C', Pp' P' → Pp (Φ.inverse.obj P'))
    (hSback : ∀ P' : C', Sp' P' → Sp (Φ.inverse.obj P'))
    (hQback : ∀ E' : C', Qp' E' → Qp (Φ.inverse.obj E'))
    (hPfwd : ∀ R : C, Pp R → Pp' (Φ.functor.obj R))
    (hSfwd : ∀ R : C, Sp R → Sp' (Φ.functor.obj R))
    (hroof : ∀ P E : C, Pp P → Sp P → Qp E → ∀ a : res.obj P ⟶ res.obj E,
      ∃ (R : C) (β : R ⟶ P) (γ : R ⟶ E), Pp R ∧ Sp R ∧ IsIso (res.map β) ∧
        res.map γ = res.map β ≫ a)
    (P' E' : C') (hP' : Pp' P') (hS' : Sp' P') (hQ' : Qp' E')
    (α : res'.obj P' ⟶ res'.obj E') :
    ∃ (R' : C') (β : R' ⟶ P') (γ : R' ⟶ E'), Pp' R' ∧ Sp' R' ∧ IsIso (res'.map β) ∧
      res'.map γ = res'.map β ≫ α := by
  -- the naturality square of `κ`, in the shape both halves of the conclusion need
  have hnat : ∀ {R₀ P₀ : C} (φ : R₀ ⟶ P₀), res'.map (Φ.functor.map φ) =
      κ.hom.app R₀ ≫ Ψ.functor.map (res.map φ) ≫ κ.inv.app P₀ := by
    intro R₀ P₀ φ
    have h := κ.hom.naturality φ
    simp only [Functor.comp_map] at h
    rw [← Category.assoc, ← h]
    simp
  -- the given map, read over `C` through the counit of `Φ`, `κ`, and the fullness of `Ψ.functor`
  obtain ⟨R, β, γ, hR, hRS, hβ, hγ⟩ := hroof (Φ.inverse.obj P') (Φ.inverse.obj E')
    (hPback P' hP') (hSback P' hS') (hQback E' hQ')
    (Ψ.functor.preimage (κ.inv.app (Φ.inverse.obj P') ≫
      res'.map (Φ.counitIso.hom.app P') ≫ α ≫ res'.map (Φ.counitIso.inv.app E') ≫
        κ.hom.app (Φ.inverse.obj E')))
  refine ⟨Φ.functor.obj R, Φ.functor.map β ≫ Φ.counitIso.hom.app P',
    Φ.functor.map γ ≫ Φ.counitIso.hom.app E', hPfwd R hR, hSfwd R hRS, ?_, ?_⟩
  · let := hβ
    rw [Functor.map_comp, hnat β]
    infer_instance
  · rw [Functor.map_comp, Functor.map_comp, hnat β, hnat γ, hγ, Functor.map_comp,
      Ψ.functor.map_preimage]
    simp [← CategoryTheory.Functor.map_comp res']

end Stacks.LiftingProblem

end
