module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# The free abelian sheaf on a representable, and its inverse image

For an object `U` of a small site `(C, J)`, the free abelian sheaf `ℤ_U^♯` on the representable
presheaf of `U` corepresents sections over `U`: morphisms `ℤ_U^♯ ⟶ M` are the sections of `M`
over `U`. For a continuous functor `G : A ⥤ B` between small sites there is a canonical morphism
`ℤ_{G U}^♯ ⟶ G⁻¹ ℤ_U^♯`, the section over `G U` of `G⁻¹ ℤ_U^♯` that the unit of `G⁻¹ ⊣ G_*`
assigns to the generator of `ℤ_U^♯`.

These are the coefficient objects through which the cohomology `Ext^p(ℤ_U^♯, -)` over an object is
carried along an inverse system of sites: the transition of such a group along `G` is `Ext` along
the exact functor `G⁻¹` precomposed with this canonical morphism, and `freeRepEquiv_pullback`
computes such composites on the generator, in terms of the adjoint transpose under `G⁻¹ ⊣ G_*`.

## Main definitions

* `Stacks.Sites.FreeRepresentable.freeRep` — the free abelian sheaf `ℤ_U^♯`.
* `Stacks.Sites.FreeRepresentable.freeRepEquiv` — `(ℤ_U^♯ ⟶ M) ≃ M(U)`.
* `Stacks.Sites.FreeRepresentable.freeRepGen` — the generator, the section corresponding to the
  identity.
* `Stacks.Sites.FreeRepresentable.freeRepPullback` — the canonical `ℤ_{G U}^♯ ⟶ G⁻¹ ℤ_U^♯`.

## Main results

* `Stacks.Sites.FreeRepresentable.freeRepEquiv_comp` and `freeRepEquiv_apply` — the bijection is
  evaluation at the generator.
* `Stacks.Sites.FreeRepresentable.freeRepEquiv_pullback` — a composite
  `ℤ_{G U}^♯ ⟶ G⁻¹ ℤ_U^♯ ⟶ G⁻¹ M ⟶ N` corresponds to the section obtained by applying the adjoint
  transpose `M ⟶ G_* N` to the section of `M` that `ℤ_U^♯ ⟶ M` corresponds to.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w

namespace Stacks.Sites.FreeRepresentable

section FreeRep

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- The free abelian sheaf `ℤ_U^♯` on the representable presheaf of an object `U`. -/
abbrev freeRep (U : C) : Sheaf J AddCommGrpCat.{w} :=
  (presheafToSheaf J AddCommGrpCat.{w}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- The adjunction between presheaves of sets and abelian sheaves through which morphisms out of
a free abelian sheaf are computed. -/
def freeRepAdj :
    ((Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free ⋙
        presheafToSheaf J AddCommGrpCat.{w}) ⊣
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙
        (Functor.whiskeringRight Cᵒᵖ _ _).obj (forget AddCommGrpCat.{w})) :=
  (AddCommGrpCat.adj.{w}.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J _)

/-- **Morphisms out of `ℤ_U^♯` are the sections over `U`.** -/
def freeRepEquiv (U : C) (M : Sheaf J AddCommGrpCat.{w}) :
    (freeRep J U ⟶ M) ≃ M.obj.obj (op U) :=
  ((freeRepAdj J).homEquiv _ M).trans yonedaEquiv

/-- The bijection `freeRepEquiv` is natural in the target sheaf. -/
theorem freeRepEquiv_comp (U : C) {M N : Sheaf J AddCommGrpCat.{w}} (φ : freeRep J U ⟶ M)
    (ψ : M ⟶ N) :
    freeRepEquiv J U N (φ ≫ ψ) = ψ.hom.app (op U) (freeRepEquiv J U M φ) := by
  simp only [freeRepEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rw [yonedaEquiv_comp]
  rfl

/-- The generator of `ℤ_U^♯`: the section over `U` corresponding to the identity. -/
def freeRepGen (U : C) : (freeRep J U).obj.obj (op U) :=
  freeRepEquiv J U (freeRep J U) (𝟙 _)

/-- **The bijection `freeRepEquiv` is evaluation at the generator.** -/
theorem freeRepEquiv_apply (U : C) {M : Sheaf J AddCommGrpCat.{w}} (φ : freeRep J U ⟶ M) :
    freeRepEquiv J U M φ = φ.hom.app (op U) (freeRepGen J U) := by
  rw [freeRepGen, ← freeRepEquiv_comp, Category.id_comp]

/-- Two morphisms out of `ℤ_U^♯` agreeing on the generator are equal. -/
theorem freeRep_hom_ext (U : C) {M : Sheaf J AddCommGrpCat.{w}} {φ φ' : freeRep J U ⟶ M}
    (h : φ.hom.app (op U) (freeRepGen J U) = φ'.hom.app (op U) (freeRepGen J U)) : φ = φ' :=
  (freeRepEquiv J U M).injective (by rw [freeRepEquiv_apply, freeRepEquiv_apply, h])

/-- Transporting a morphism out of `ℤ_{U'}^♯` along an equality `U = U'` transports its section. -/
theorem freeRepEquiv_eqToHom_comp {U U' : C} (h : U = U') {M : Sheaf J AddCommGrpCat.{w}}
    (φ : freeRep J U' ⟶ M) :
    freeRepEquiv J U M (eqToHom (congrArg (freeRep J) h) ≫ φ) =
      M.obj.map (eqToHom (congrArg op h.symm)) (freeRepEquiv J U' M φ) := by
  subst h
  simp

end FreeRep

section Pullback

variable {A B : Type w} [SmallCategory A] [SmallCategory B]
  {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
  [HasSheafify JA AddCommGrpCat.{w}] [HasSheafify JB AddCommGrpCat.{w}]
  (G : A ⥤ B) [G.IsContinuous JA JB]
  {L : Sheaf JA AddCommGrpCat.{w} ⥤ Sheaf JB AddCommGrpCat.{w}}
  (adj : L ⊣ G.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB)

/-- **The canonical morphism `ℤ_{G U}^♯ ⟶ G⁻¹ ℤ_U^♯`**: the section over `G U` of `G⁻¹ ℤ_U^♯`
which the unit of `G⁻¹ ⊣ G_*` assigns to the generator of `ℤ_U^♯`. The inverse image is any
left adjoint `L` of the direct image `G_*`, given with its adjunction, so that each consumer can
use its own representative. -/
def freeRepPullback (U : A) : freeRep JB (G.obj U) ⟶ L.obj (freeRep JA U) :=
  (freeRepEquiv JB (G.obj U) _).symm
    ((adj.unit.app (freeRep JA U)).hom.app (op U) (freeRepGen JA U))

/-- `freeRepPullback` is, under `freeRepEquiv`, the image of the generator under the unit. -/
theorem freeRepEquiv_freeRepPullback (U : A) :
    freeRepEquiv JB (G.obj U) _ (freeRepPullback G adj U) =
      (adj.unit.app (freeRep JA U)).hom.app (op U) (freeRepGen JA U) :=
  Equiv.apply_symm_apply _ _

/-- **A composite through `freeRepPullback`, on the generator.** For `φ : ℤ_U^♯ ⟶ M` and
`ψ : G⁻¹ M ⟶ N`, the composite `ℤ_{G U}^♯ ⟶ G⁻¹ ℤ_U^♯ ⟶ G⁻¹ M ⟶ N` is the section of `N` over
`G U` obtained by applying the adjoint transpose `M ⟶ G_* N` of `ψ` to the section of `M` over
`U` that `φ` is. -/
theorem freeRepEquiv_pullback (U : A) {M : Sheaf JA AddCommGrpCat.{w}}
    {N : Sheaf JB AddCommGrpCat.{w}} (φ : freeRep JA U ⟶ M)
    (ψ : L.obj M ⟶ N) :
    freeRepEquiv JB (G.obj U) N (freeRepPullback G adj U ≫ L.map φ ≫ ψ) =
      ((adj.homEquiv M N ψ).hom.app (op U)) (freeRepEquiv JA U M φ) := by
  rw [freeRepEquiv_comp, freeRepEquiv_freeRepPullback, freeRepEquiv_apply JA U φ,
    Adjunction.homEquiv_unit]
  have hnat := congrArg (fun f => f.hom.app (op U) (freeRepGen JA U)) (adj.unit.naturality φ)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at hnat ⊢
  rw [hnat]
  rfl

end Pullback

end Stacks.Sites.FreeRepresentable

end
