module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.Deformation.Cofibered
public import StacksCore.Tactic.StacksAttribute

/-!
# The (2, 1)-category of categories cofibered in groupoids

Remarks (7) and (8) of Stacks 06GK. A morphism of categories cofibered in groupoids over `C` is
a functor commuting with the projections to `C`, and categories cofibered in groupoids form a
`(2, 1)`-category `Cof(C)` whose 2-morphisms `t : φ ⟶ ψ` are the morphisms of functors with
`p'(t_x) = 𝟙 (p x)` for every object `x`.

## Main definitions

* `Deformation.IsCofiberedBased`: the predicate cutting out the 2-category `Cof(C)`, i.e. the full
  sub-2-category `InducedBicategory (BasedCategory C) (Subtype.val (p := IsCofiberedBased))` of
  Mathlib's 2-category `BasedCategory C` of categories over `C`.
* `Deformation.CatCofiberedInGroupoids.homEquiv`: its 1-morphisms `𝒳 ⟶ 𝒴`, the set
  `Mor_C(𝒳, 𝒴)`, are the functors `G` with `p' ∘ G = p` (Mathlib's `BasedFunctor`).
* `Deformation.CatCofiberedInGroupoids.twoHomEquiv`: its 2-morphisms are the morphisms of functors
  whose components lie over identities (Mathlib's `BasedNatTrans`).

## Main results

* `Deformation.CatCofiberedInGroupoids.homFunctor_comp_p`: a 1-morphism commutes with the
  projections.
* `Deformation.CatCofiberedInGroupoids.isIso_twoHom`: every 2-morphism is invertible, so `Cof(C)`
  is a `(2, 1)`-category.
* `CategoryTheory.CatFiberedInGroupoids.map_app` (registered here): the image under `p'` of a
  component of a 2-morphism is an identity.

## References

* [Stacks Project, Tag 06GK](https://stacks.math.columbia.edu/tag/06GK)
* [Stacks Project, Tag 06GL](https://stacks.math.columbia.edu/tag/06GL)
* [Stacks Project, Tag 06GM](https://stacks.math.columbia.edu/tag/06GM)
-/

@[expose] public section

namespace Deformation

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

/-- **Stacks 06GK (8).** The 2-category `Cof(C)` of categories cofibered in groupoids over `C` is
`Bicategory.InducedBicategory (BasedCategory C) (Subtype.val (p := IsCofiberedBased))`: the full
sub-2-category of the 2-category `BasedCategory C` of categories over `C` spanned by the
categories satisfying this predicate, i.e. whose structure functor is cofibered in groupoids.
Its 1-morphisms are the functors commuting with the projections
(`CatCofiberedInGroupoids.homEquiv`), its 2-morphisms the morphisms of functors lying over
identities (`CatCofiberedInGroupoids.twoHomEquiv`), and every 2-morphism is
invertible (`CatCofiberedInGroupoids.isIso_twoHom`). -/
@[stacks 06GK "(8) the (2, 1)-category Cof(C): the full sub-2-category of categories over C \
cut out by this predicate"]
abbrev IsCofiberedBased {C : Type u₁} [Category.{v₁} C] (𝒳 : BasedCategory.{v₂, u₂} C) : Prop :=
  IsCofiberedInGroupoids 𝒳.p

namespace CatCofiberedInGroupoids

variable {C : Type u₁} [Category.{v₁} C]

/-- A category over `C` whose structure functor is cofibered in groupoids, as an object of
`Cof(C)`. -/
abbrev mk (𝒳 : BasedCategory.{v₂, u₂} C) (h : IsCofiberedInGroupoids 𝒳.p) :
    Bicategory.InducedBicategory (BasedCategory.{v₂, u₂} C)
      (Subtype.val (p := IsCofiberedBased (C := C))) :=
  ⟨𝒳, h⟩

variable {𝒳 𝒴 : Bicategory.InducedBicategory (BasedCategory.{v₂, u₂} C)
  (Subtype.val (p := IsCofiberedBased (C := C)))}

/-- **Stacks 06GK (7).** A morphism `𝒳 ⟶ 𝒴` of categories cofibered in groupoids over `C`, i.e. an
element of `Mor_C(𝒳, 𝒴)`, is precisely a functor between the underlying categories commuting with
the projections to `C` (a `BasedFunctor`, see `homFunctor_comp_p`). -/
@[stacks 06GK "(7) a morphism of categories cofibered in groupoids is a functor commuting with \
the projections; Mor_C(F, F')"]
def homEquiv (𝒳 𝒴 : Bicategory.InducedBicategory (BasedCategory.{v₂, u₂} C)
      (Subtype.val (p := IsCofiberedBased (C := C)))) :
    (𝒳 ⟶ 𝒴) ≃ (𝒳.val ⥤ᵇ 𝒴.val) :=
  CatFiberedInGroupoids.homEquivBasedFunctor 𝒳 𝒴

/-- **Stacks 06GK (7).** The functor underlying a 1-morphism of `Cof(C)` commutes with the
projections: `p' ∘ G = p`. -/
@[stacks 06GK "(7) 1-morphisms commute with the projections"]
lemma homFunctor_comp_p (G : 𝒳 ⟶ 𝒴) : G.hom.toFunctor ⋙ 𝒴.val.p = 𝒳.val.p :=
  G.hom.w

/-- **Stacks 06GK (8).** A 2-morphism `t : G ⟶ H` of `Cof(C)` is precisely a morphism of the
underlying functors whose components satisfy `p'(t_x) = 𝟙 (p x)`, i.e. lie over identities
(a `BasedNatTrans`). -/
@[stacks 06GK "(8) 2-morphisms are morphisms of functors t with p'(t_x) = id_{p(x)}"]
def twoHomEquiv (G H : 𝒳 ⟶ 𝒴) : (G ⟶ H) ≃ BasedNatTrans G.hom H.hom :=
  CatFiberedInGroupoids.homEquivBasedNatTrans G H

/-- **Stacks 06GK (8).** Every 2-morphism of `Cof(C)` is invertible: its components lie over
identities of `C`, hence are isomorphisms in the target, which is cofibered in groupoids. Thus
`Cof(C)` is a `(2, 1)`-category. -/
@[stacks 06GK "(8) Cof(C) is a (2, 1)-category: every 2-morphism is invertible"]
theorem isIso_twoHom {G H : 𝒳 ⟶ 𝒴} (t : G ⟶ H) : IsIso t := by
  have happ : ∀ x : 𝒳.val.obj, IsIso (t.hom.toNatTrans.app x) := fun x ↦
    isIso_of_isHomLift_id 𝒴.2 _ (t.hom.isHomLift' x)
  have : IsIso t.hom.toNatTrans := NatIso.isIso_of_isIso_app _
  have : IsIso t.hom := BasedNatIso.isIso_of_toNatTrans_isIso t.hom
  have ht : t = (Bicategory.InducedBicategory.isoMk (asIso t.hom)).hom := rfl
  rw [ht]
  infer_instance

end CatCofiberedInGroupoids

add_to_stacks 06GK "(8) p'(t_x) = id_{p(x)} for a 2-morphism t (stated for any full sub-2-category \
of categories over C, in particular Cof(C))" CategoryTheory.CatFiberedInGroupoids.map_app

end Deformation
