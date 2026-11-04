module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The free abelian sheaf on a representable, with coefficients in a larger universe

For an object `U` of a site `(C, J)` with `Category.{v} C`, the free abelian sheaf `ℤ_U^♯` on the
representable presheaf of `U` corepresents sections over `U`. When the sheaves take values in
`AddCommGrpCat.{max w v}` rather than in the universe `v` of the morphisms of `C`, the
representable presheaf is first lifted to `Type (max w v)` by `CategoryTheory.uliftYoneda`. This
is the situation of abelian sheaves on the small étale site of a scheme `X : Scheme.{u}`: the
morphisms of `X.Etale` live in `Type u` and the sheaves in `AddCommGrpCat.{u + 1}`, so
`Stacks.Sites.FreeRepresentable.freeRep` (which needs a small site) and
`Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheafHomAddEquiv` (which needs coefficients in
the universe of the morphisms) do not apply.

## Main definitions

* `Stacks.Sites.FreeRepresentable.freeRepULift` — the free abelian sheaf `ℤ_U^♯` with
  coefficients in `AddCommGrpCat.{max w v}`.
* `Stacks.Sites.FreeRepresentable.freeRepULiftEquiv` — `(ℤ_U^♯ ⟶ M) ≃ M(U)`.
* `Stacks.Sites.FreeRepresentable.freeRepULiftGen` — the generator, the section corresponding to
  the identity.
* `Stacks.Sites.FreeRepresentable.freeRepULiftAddEquiv` — the same bijection, additively.

## Main results

* `Stacks.Sites.FreeRepresentable.freeRepULiftEquiv_comp` and `freeRepULiftEquiv_apply` — the
  bijection is natural in the target and is evaluation at the generator.
* `Stacks.Sites.FreeRepresentable.freeRepULiftEquiv_symm_app_gen` — the morphism attached to a
  section sends the generator to that section.

## References

* [Stacks Project, Tag 03A4](https://stacks.math.columbia.edu/tag/03A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u₁

namespace Stacks.Sites.FreeRepresentable

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max w v}]

/-- The free abelian sheaf `ℤ_U^♯` on the representable presheaf of an object `U`, with
coefficients in `AddCommGrpCat.{max w v}`: the representable presheaf is lifted to
`Type (max w v)` by `CategoryTheory.uliftYoneda`. -/
abbrev freeRepULift (U : C) : Sheaf J AddCommGrpCat.{max w v} :=
  (presheafToSheaf J AddCommGrpCat.{max w v}).obj
    (uliftYoneda.{w}.obj U ⋙ AddCommGrpCat.free.{max w v})

/-- The adjunction between presheaves of sets in `Type (max w v)` and abelian sheaves through
which morphisms out of `freeRepULift J U` are computed. -/
def freeRepULiftAdj :
    ((Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free.{max w v} ⋙
        presheafToSheaf J AddCommGrpCat.{max w v}) ⊣
      (sheafToPresheaf J AddCommGrpCat.{max w v} ⋙
        (Functor.whiskeringRight Cᵒᵖ _ _).obj (forget AddCommGrpCat.{max w v})) :=
  (AddCommGrpCat.adj.{max w v}.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J _)

/-- **Morphisms out of `ℤ_U^♯` are the sections over `U`.** -/
def freeRepULiftEquiv (U : C) (M : Sheaf J AddCommGrpCat.{max w v}) :
    (freeRepULift.{w} J U ⟶ M) ≃ M.obj.obj (op U) :=
  ((freeRepULiftAdj.{w} J).homEquiv _ M).trans uliftYonedaEquiv

/-- The bijection `freeRepULiftEquiv` is natural in the target sheaf. -/
theorem freeRepULiftEquiv_comp (U : C) {M N : Sheaf J AddCommGrpCat.{max w v}}
    (φ : freeRepULift.{w} J U ⟶ M) (ψ : M ⟶ N) :
    freeRepULiftEquiv J U N (φ ≫ ψ) = ψ.hom.app (op U) (freeRepULiftEquiv J U M φ) := by
  simp only [freeRepULiftEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rw [uliftYonedaEquiv_comp]
  rfl

/-- The generator of `ℤ_U^♯`: the section over `U` corresponding to the identity. -/
def freeRepULiftGen (U : C) : (freeRepULift.{w} J U).obj.obj (op U) :=
  freeRepULiftEquiv J U (freeRepULift.{w} J U) (𝟙 _)

/-- **The bijection `freeRepULiftEquiv` is evaluation at the generator.** -/
theorem freeRepULiftEquiv_apply (U : C) {M : Sheaf J AddCommGrpCat.{max w v}}
    (φ : freeRepULift.{w} J U ⟶ M) :
    freeRepULiftEquiv J U M φ = φ.hom.app (op U) (freeRepULiftGen J U) := by
  rw [freeRepULiftGen, ← freeRepULiftEquiv_comp, Category.id_comp]

/-- The morphism `ℤ_U^♯ ⟶ M` attached to a section `s` of `M` over `U` sends the generator to
`s`. -/
theorem freeRepULiftEquiv_symm_app_gen (U : C) {M : Sheaf J AddCommGrpCat.{max w v}}
    (s : M.obj.obj (op U)) :
    ((freeRepULiftEquiv J U M).symm s).hom.app (op U) (freeRepULiftGen J U) = s := by
  rw [← freeRepULiftEquiv_apply, Equiv.apply_symm_apply]

/-- Two morphisms out of `ℤ_U^♯` agreeing on the generator are equal. -/
theorem freeRepULift_hom_ext (U : C) {M : Sheaf J AddCommGrpCat.{max w v}}
    {φ φ' : freeRepULift.{w} J U ⟶ M}
    (h : φ.hom.app (op U) (freeRepULiftGen J U) = φ'.hom.app (op U) (freeRepULiftGen J U)) :
    φ = φ' :=
  (freeRepULiftEquiv J U M).injective (by rw [freeRepULiftEquiv_apply, freeRepULiftEquiv_apply, h])

/-- **Morphisms out of `ℤ_U^♯` are the sections over `U`, additively**: the bijection
`freeRepULiftEquiv` is evaluation at the generator, which is additive in the morphism. -/
def freeRepULiftAddEquiv (U : C) (M : Sheaf J AddCommGrpCat.{max w v}) :
    (freeRepULift.{w} J U ⟶ M) ≃+ M.obj.obj (op U) where
  __ := freeRepULiftEquiv J U M
  map_add' φ ψ := by
    simp only [Equiv.toFun_as_coe, freeRepULiftEquiv_apply]
    rfl

/-- The additive equivalence `freeRepULiftAddEquiv` is evaluation at the generator. -/
theorem freeRepULiftAddEquiv_apply (U : C) {M : Sheaf J AddCommGrpCat.{max w v}}
    (φ : freeRepULift.{w} J U ⟶ M) :
    freeRepULiftAddEquiv J U M φ = φ.hom.app (op U) (freeRepULiftGen J U) :=
  freeRepULiftEquiv_apply J U φ

end Stacks.Sites.FreeRepresentable

end
