module

public import StacksFrontier.Cotangent.AtiyahClassSmallSiteEndpoints

/-!
# The first vertex of the Atiyah triangle, read as an objectwise tensor product

The first vertex of the Atiyah triangle of [Stacks, Tag 09DD] is `Lπ_!` of

`(AlgebraicGeometry.SheafOfModules.sheafTensorRight 𝒪 (derivationsFunctor A̲ 𝒪 φ).coreprX).obj M̲`,

a *sheaf* of modules built by tensoring objectwise and then sheafifying, with its tensor factor
named as the corepresenting object of the functor of relative derivations. This file rewrites
that vertex as the plain objectwise tensor product

`(Stacks.tensorRight Ω_{𝒪/A}).obj M̲`

whose sections are `M ⊗_P Ω[P⁄A]` with no sheafification and no corepresentability in sight,
which is the shape `CommAlgCat.smallAtiyahFirstVertexRestrictionIso` consumes.

Two things have to be undone, neither of them mathematical content on a chaotic site.

* **The sheafification.** Every presheaf on the chaotic site is a sheaf, so the unit of the
  sheafification adjunction for presheaves of modules is an isomorphism:
  `Stacks.ChaoticSite.sheafificationValIso`. The proof is the standard idiom — the unit's
  underlying map of abelian presheaves is `CategoryTheory.toSheafify`, which is an isomorphism
  by `CategoryTheory.isIso_toSheafify _ (Presheaf.isSheaf_bot _)`, and
  `PresheafOfModules.toPresheaf` reflects isomorphisms.
* **The corepresenting object.** `CommAlgCat.smallAtiyahDerivationsCoreprXIso` identifies it
  with `CommAlgCat.smallAtiyahRelativeDifferentials`, and that identification is carried into
  the tensor product by
  `AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObjIsoRight`, functoriality of the
  objectwise tensor product in its second variable.

## Main results

* `Stacks.ChaoticSite.sheafificationValIso`: on a chaotic site the sheafification of a presheaf
  of modules is the presheaf itself.
* `AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObjIsoRight`: the objectwise tensor
  product transports an isomorphism in its second variable.
* `CommAlgCat.smallAtiyahFirstVertexTensorIso`: **the first vertex of the Atiyah triangle on the
  small model of `C_{B/A}`, after `Stacks.Atiyah.chaoticModel`, is the objectwise tensor product
  `(Stacks.tensorRight Ω_{𝒪/A}).obj M̲`.**

## Implementation notes

`Stacks.tensorObj` of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorExactness.lean` and
`AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj` of
`StacksFrontier/CategoryTheory/Sites/Modules/Flat.lean` are the same construction on the nose
(`Stacks.tensorObj_eq`), the former being the one the Atiyah machinery states its tensor factor
with and the latter the one `AlgebraicGeometry.SheafOfModules.sheafTensorRight` is built from.
`AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObjIsoRight` is therefore stated for
the latter spelling and proved with its two-variable functoriality lemmas `tensorHom_comp` and
`tensorHom_id`; `Stacks.tensorObj_eq` is what lets it be used at the former.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (moduleSheaves)

universe u

namespace Stacks.ChaoticSite

variable {C : Type u} [SmallCategory C] (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{u})
  (P : PresheafOfModules.{u} R.obj)

/-- The unit of the sheafification adjunction for presheaves of modules is an isomorphism on a
chaotic site: its underlying map of abelian presheaves is `CategoryTheory.toSheafify`, which is
an isomorphism because every presheaf satisfies the sheaf condition for the topology `⊥`. -/
instance isIso_sheafificationAdjunction_unit_app :
    IsIso ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).unit.app P) := by
  have : IsIso ((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).unit.app P)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact CategoryTheory.isIso_toSheafify _ (Presheaf.isSheaf_bot _)
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf R.obj)

/-- **On a chaotic site the sheafification of a presheaf of modules is the presheaf itself.**
This is what lets a computation of an objectwise tensor product of presheaves of modules be read
off a sheafified tensor product such as
`AlgebraicGeometry.SheafOfModules.sheafTensorRight`. -/
def sheafificationValIso :
    ((PresheafOfModules.sheafification.{u} (𝟙 R.obj)).obj P).val ≅ P :=
  (asIso ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).unit.app P)).symm

end Stacks.ChaoticSite

namespace Stacks

variable {C : Type u} [SmallCategory C] {O : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The two objectwise tensor products of presheaves of modules in the tree — `Stacks.tensorObj`
and `AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj` — are the same construction on
the nose. -/
lemma tensorObj_eq (G F : PresheafOfModules.{u} (ringPresheaf O)) :
    tensorObj G F = AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj G F :=
  rfl

end Stacks

namespace AlgebraicGeometry.SheafOfModules.PresheafOfModules

variable {C : Type u} [SmallCategory C] {O : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- **The objectwise tensor product transports an isomorphism in its second variable.** By
`Stacks.tensorObj_eq` this is equally an isomorphism of `Stacks.tensorObj`s. -/
def tensorObjIsoRight (G : _root_.PresheafOfModules.{u} (Stacks.ringPresheaf O))
    {F F' : _root_.PresheafOfModules.{u} (Stacks.ringPresheaf O)} (e : F ≅ F') :
    tensorObj G F ≅ tensorObj G F' where
  hom := tensorHom (𝟙 G) e.hom
  inv := tensorHom (𝟙 G) e.inv
  hom_inv_id := by rw [tensorHom_comp, Category.comp_id, e.hom_inv_id, tensorHom_id]
  inv_hom_id := by rw [tensorHom_comp, Category.comp_id, e.inv_hom_id, tensorHom_id]

end AlgebraicGeometry.SheafOfModules.PresheafOfModules

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (M : ModuleCat.{u} (B : Type u))
  (κ : Cardinal.{u})

/-- **The first vertex of the Atiyah triangle on the small model of `C_{B/A}` is the objectwise
tensor product `M̲ ⊗_𝒪 Ω_{𝒪/A}`.** The vertex as the principal-parts sequence builds it is
`AlgebraicGeometry.SheafOfModules.sheafTensorRight 𝒪 (derivationsFunctor A̲ 𝒪 φ).coreprX` applied
to `M̲`, i.e. tensor objectwise with the corepresenting object of the functor of relative
derivations and sheafify. On the chaotic site the sheafification is undone by
`Stacks.ChaoticSite.sheafificationValIso` and the corepresenting object is named by
`CommAlgCat.smallAtiyahDerivationsCoreprXIso`; what is left is
`(Stacks.tensorRight Ω_{𝒪/A}).obj M̲`, which is the source of
`CommAlgCat.smallAtiyahFirstVertexRestrictionIso`. -/
def smallAtiyahFirstVertexTensorIso :
    Stacks.Atiyah.chaoticModel.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (smallAtiyahStructureSheaf A B κ)).flip.obj
          (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{u} (smallAtiyahBaseSheaf A B κ)
            (smallAtiyahStructureSheaf A B κ)
            (smallAtiyahBaseHom A B κ)).coreprX).obj (smallAtiyahModuleSheaf A B κ M)) ≅
      (Stacks.tensorRight (O := (smallAtiyahStructureSheaf A B κ).obj)
            (smallAtiyahRelativeDifferentialsPresheaf A B κ)).obj
        ((PresheafOfModules.restrictScalars (smallPolynomialAugmentation A B κ)).obj
          (smallAtiyahModuleOverConstant A B M κ)) :=
  Stacks.ChaoticSite.sheafificationValIso _ _ ≪≫
    AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObjIsoRight _
      (Stacks.Atiyah.chaoticModel.mapIso (smallAtiyahDerivationsCoreprXIso A B κ))

end CommAlgCat

end
