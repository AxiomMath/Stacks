module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Yoneda

/-!
# A left adjoint with values in a full subcategory

Let `Λ ⊣ Ψ` with `Λ : D ⥤ C`, and let `P` be a property of objects of `C` satisfied by every
`Λ.obj Y`. Then the corestriction `P.lift Λ` of `Λ` is left adjoint to the restriction
`P.ι ⋙ Ψ` of `Ψ`. If moreover the inclusion `P.ι` has a right adjoint `DQ` (so `P` is
coreflective), then `Ψ` inverts the counit `P.ι (DQ L) ⟶ L` of the coreflection: maps from
`Λ.obj Y` to `L` all factor uniquely through it.

In the application, `Ψ = RΓ(X, E ⊗^L -)` on `D(𝒪_X)`, `P` is the property of having
quasi-coherent cohomology sheaves, and `DQ` is the coherator:
`RΓ(X, E ⊗^L DQ_X(L)) = RΓ(X, E ⊗^L L)`.

## Main definitions

* `CategoryTheory.Adjunction.liftLeftAdjoint`: `P.lift Λ ⊣ P.ι ⋙ Ψ`.

## Main results

* `CategoryTheory.Adjunction.isIso_map_counit_app_of_forall`: `Ψ` inverts the counit of a
  coreflection onto a full subcategory containing the image of its left adjoint.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {P : ObjectProperty C}
  {Λ : D ⥤ C} {Ψ : C ⥤ D}

/-- **The corestriction of a left adjoint to a full subcategory containing its image** is left
adjoint to the restriction of the right adjoint: `P.lift Λ hΛ ⊣ P.ι ⋙ Ψ`. -/
noncomputable def liftLeftAdjoint (adj : Λ ⊣ Ψ) (hΛ : ∀ Y, P (Λ.obj Y)) :
    P.lift Λ hΛ ⊣ P.ι ⋙ Ψ :=
  adj.restrictFullyFaithful (iC := 𝟭 D) (iD := P.ι) (Functor.FullyFaithful.id D)
    (ObjectProperty.fullyFaithfulι P) (Functor.leftUnitor Λ ≪≫ (P.liftCompιIso Λ hΛ).symm)
    (Functor.rightUnitor _).symm

/-- **A right adjoint inverts the counit of a coreflection onto a full subcategory containing the
image of its left adjoint.** If `Λ ⊣ Ψ`, every `Λ.obj Y` satisfies `P`, and `P.ι ⊣ DQ`, then
`Ψ.map (adjQ.counit.app L) : Ψ (P.ι (DQ L)) ⟶ Ψ L` is an isomorphism for every `L`. -/
theorem isIso_map_counit_app_of_forall {DQ : C ⥤ P.FullSubcategory} (adjQ : P.ι ⊣ DQ)
    (adj : Λ ⊣ Ψ) (hΛ : ∀ Y, P (Λ.obj Y)) (L : C) :
    IsIso (Ψ.map (adjQ.counit.app L)) := by
  refine isIso_of_yoneda_map_bijective _ fun T => ?_
  have key : (fun x : T ⟶ Ψ.obj (P.ι.obj (DQ.obj L)) => x ≫ Ψ.map (adjQ.counit.app L)) =
      (adj.homEquiv T L) ∘
        (fun y : Λ.obj T ⟶ P.ι.obj (DQ.obj L) => y ≫ adjQ.counit.app L) ∘
          (adj.homEquiv T _).symm := by
    funext x
    simp [Adjunction.homEquiv_naturality_right]
  refine (congrArg Function.Bijective key).mpr ?_
  refine (adj.homEquiv T L).bijective.comp (Function.Bijective.comp ?_
    (adj.homEquiv T _).symm.bijective)
  let Z : P.FullSubcategory := ⟨Λ.obj T, hΛ T⟩
  have e : (fun y : Λ.obj T ⟶ P.ι.obj (DQ.obj L) => y ≫ adjQ.counit.app L) =
      (adjQ.homEquiv Z L).symm ∘ (ObjectProperty.fullyFaithfulι P).homEquiv.symm := by
    funext y
    simp only [Function.comp_apply, Adjunction.homEquiv_counit, Z]
    exact congrArg (· ≫ adjQ.counit.app L)
      ((ObjectProperty.fullyFaithfulι P).map_preimage (X := Z) y).symm
  exact (congrArg Function.Bijective e).mpr <| (adjQ.homEquiv Z L).symm.bijective.comp
    (ObjectProperty.fullyFaithfulι P).homEquiv.symm.bijective

end CategoryTheory.Adjunction
