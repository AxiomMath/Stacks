module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftAdjunction

/-!
# Isomorphisms of sheaves of modules from isomorphisms of the underlying abelian sheaves

An isomorphism of the abelian sheaves underlying two sheaves of `Λ`-modules which commutes with
multiplication by every scalar is an isomorphism of sheaves of `Λ`-modules.

## Main definitions

* `Stacks.ModuleCatLift.sheafIsoOfScalarComm`: the isomorphism of sheaves of `Λ`-modules
  determined by an isomorphism of underlying abelian sheaves commuting with every scalar.

## Main results

* `Stacks.ModuleCatLift.sheafCompose_map_sheafIsoOfScalarComm_hom`: the underlying morphism of
  abelian sheaves of `sheafIsoOfScalarComm` is the given one.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w r u₁ v₁

namespace Stacks.ModuleCatLift

variable (Λ : Type r) [Ring Λ] {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- **An isomorphism of underlying abelian sheaves commuting with scalars is an isomorphism of
sheaves of `Λ`-modules.** -/
def sheafIsoOfScalarComm {F G : Sheaf J (ModuleCat.{w} Λ)}
    (e : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G)
    (he : ∀ a : Λ,
      (sheafScalarEnd Λ J F a).asHom ≫ e.hom = e.hom ≫ (sheafScalarEnd Λ J G a).asHom) :
    F ≅ G where
  hom := sheafHomOfScalarComm Λ J e.hom he
  inv := sheafHomOfScalarComm Λ J e.inv (fun a => by
    rw [← cancel_mono e.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, he, Iso.inv_hom_id_assoc])
  hom_inv_id := (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective (by
    rw [Functor.map_comp, sheafCompose_map_sheafHomOfScalarComm,
      sheafCompose_map_sheafHomOfScalarComm, e.hom_inv_id, CategoryTheory.Functor.map_id])
  inv_hom_id := (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective (by
    rw [Functor.map_comp, sheafCompose_map_sheafHomOfScalarComm,
      sheafCompose_map_sheafHomOfScalarComm, e.inv_hom_id, CategoryTheory.Functor.map_id])

/-- The isomorphism `sheafIsoOfScalarComm Λ J e he` has underlying morphism of abelian sheaves
`e.hom`. -/
@[simp]
lemma sheafCompose_map_sheafIsoOfScalarComm_hom {F G : Sheaf J (ModuleCat.{w} Λ)}
    (e : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G)
    (he : ∀ a : Λ,
      (sheafScalarEnd Λ J F a).asHom ≫ e.hom = e.hom ≫ (sheafScalarEnd Λ J G a).asHom) :
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
      (sheafIsoOfScalarComm Λ J e he).hom = e.hom :=
  sheafCompose_map_sheafHomOfScalarComm Λ J e.hom he

end Stacks.ModuleCatLift

end
