module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorProduct
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products of module sheaves on the associated sites of a fibred category

A category fibred in groupoids over the big fppf category of schemes over `S` carries five
associated topologies, all on the same category and all with the same structure sheaf. That
structure sheaf is the structure sheaf of a ringed site, so sheaves of modules on each of the five
sites have a tensor product, and the tensor product formed on any one of them is the tensor
product in the category of sheaves of modules for the inherited fppf topology: a bilinear map into
any fppf sheaf of modules factors through it uniquely.

## Main definitions

* `AlgebraicGeometry.FibredSite.monoidalCategory` is the monoidal structure on sheaves of
  modules on an associated site of the fibred category.
* `Stacks.Modules.toTensorSheaf` is the pure-tensor bilinear map from a pair of sheaves of
  modules on a ringed site into the sheafification of their objectwise tensor product.
* `AlgebraicGeometry.FibredSite.tensorSheaf` is that sheafification on an associated site, and
  `AlgebraicGeometry.FibredSite.toTensorSheaf` its pure-tensor bilinear map.

## Main results

* `AlgebraicGeometry.FibredSite.ringStructureSheafCore_eq_structureSheaf`: the coefficient
  sheaf of rings of an associated site is the structure sheaf of a ringed site, on the nose.
* `Stacks.Modules.existsUnique_hom_toTensorSheaf`: the sheafification of the objectwise tensor
  product of two sheaves of modules on a ringed site is their tensor product in the category of
  sheaves of modules for *every* topology finer than the one it is formed on.
* `AlgebraicGeometry.FibredSite.existsUnique_hom_tensorSheaf`: consequently the tensor product
  formed on any associated site of the fibred category is the tensor product in the category of
  sheaves of modules for the inherited fppf topology.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w

namespace Stacks.Modules

open AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The pure-tensor bilinear map from a pair of sheaves of modules on a ringed site into the
sheafification of their objectwise tensor product: the sheafification unit, read as a bilinear
map on sections. -/
public noncomputable def toTensorSheaf
    (F G : SheafOfModules.{u} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    BilinearMap 𝒪 F.val G.val (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat)
          h𝒪⟩).obj F).obj G).val :=
  BilinearMap.ofTensorHom
    (SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
      (PresheafOfModules.tensorObj (O := 𝒪) F.val G.val))

/-- The morphism out of the objectwise tensor product associated with the pure-tensor bilinear
map is the sheafification unit itself. -/
public theorem tensorHom_toTensorSheaf
    (F G : SheafOfModules.{u} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (toTensorSheaf 𝒪 h𝒪 F G).tensorHom =
      SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
        (PresheafOfModules.tensorObj (O := 𝒪) F.val G.val) :=
  BilinearMap.homEquiv.left_inv _

/-- The sheafification unit of the objectwise tensor product is locally injective on
sections. -/
public theorem isLocallyInjective_toTensorSheaf
    (F G : SheafOfModules.{u} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    Presheaf.IsLocallyInjective J (sectionsMap (toTensorSheaf 𝒪 h𝒪 F G).tensorHom) := by
  rw [tensorHom_toTensorSheaf]
  exact inferInstanceAs (Presheaf.IsLocallyInjective J (Functor.whiskerRight
    (CategoryTheory.toSheafify J _) (forget AddCommGrpCat.{u})))

/-- The sheafification unit of the objectwise tensor product is locally surjective on
sections. -/
public theorem isLocallySurjective_toTensorSheaf
    (F G : SheafOfModules.{u} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    Presheaf.IsLocallySurjective J (sectionsMap (toTensorSheaf 𝒪 h𝒪 F G).tensorHom) := by
  rw [tensorHom_toTensorSheaf]
  exact inferInstanceAs (Presheaf.IsLocallySurjective J (Functor.whiskerRight
    (CategoryTheory.toSheafify J _) (forget AddCommGrpCat.{u})))

/-- The sheafification of the objectwise tensor product of two sheaves of modules on a ringed
site is their tensor product in the category of sheaves of modules for *every* topology finer
than the one it is formed on: a bilinear map into a presheaf of modules whose sections form a
sheaf for the finer topology factors through the pure-tensor map uniquely. -/
public theorem existsUnique_hom_toTensorSheaf {K : GrothendieckTopology C} (hJK : J ≤ K)
    (F G : SheafOfModules.{u} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    {H : PresheafOfModules.{u} (structureRingPresheaf 𝒪)}
    (hH : Presheaf.IsSheaf K (SheafOfModules.moduleTypes H))
    (b : BilinearMap 𝒪 F.val G.val H) :
    ∃! f : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat)
          h𝒪⟩).obj F).obj G).val ⟶ H,
      ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
        f.app U ((toTensorSheaf 𝒪 h𝒪 F G).app U x y) = b.app U x y :=
  existsUnique_hom_of_le hJK (toTensorSheaf 𝒪 h𝒪 F G)
    (isLocallyInjective_toTensorSheaf 𝒪 h𝒪 F G)
    (isLocallySurjective_toTensorSheaf 𝒪 h𝒪 F G) hH b

end Stacks.Modules

namespace AlgebraicGeometry.FibredSite

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- The ring presheaf underlying the structure sheaf of an associated site of the fibred
category is a sheaf for that topology: it is the coefficient sheaf of rings. -/
public theorem structureRingPresheaf_isSheaf (τ : SiteKind) :
    Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p τ)
      (structureRingPresheaf (structureSheaf B S hS p hp τ).obj) :=
  (ringStructureSheafCore B S hS p hp τ).property

/-- The coefficient sheaf of rings of an associated site of the fibred category is the
structure sheaf of the corresponding ringed site, on the nose. -/
public theorem ringStructureSheafCore_eq_structureSheaf (τ : SiteKind) :
    ringStructureSheafCore B S hS p hp τ =
      Stacks.SheafOfModules.TensorSheafification.structureSheaf (structureSheaf B S hS p hp τ).obj
        (structureRingPresheaf_isSheaf B S hS p hp τ) :=
  rfl

variable [EssentiallySmall.{u} 𝒳]

attribute [local instance] hasWeakSheafify_associatedTopology
  wEqualsLocallyBijective_associatedTopology

/-- The monoidal structure on sheaves of modules on an associated site of the fibred category:
the tensor product is the sheafification of the objectwise tensor product and the unit is the
structure sheaf. -/
@[instance_reducible]
public noncomputable def monoidalCategory (τ : SiteKind) :
    MonoidalCategory (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) :=
  letI := hasWeakSheafify_associatedTopology B S hS p τ
  letI := wEqualsLocallyBijective_associatedTopology B S hS p τ
  Stacks.SheafOfModules.monoidalCategory
    (J := BigFppfOver.associatedTopology B S hS p τ)
    (structureSheaf B S hS p hp τ).obj (structureRingPresheaf_isSheaf B S hS p hp τ)

/-- The pure-tensor bilinear map of two sheaves of modules on an associated site of the fibred
category into their tensor product. -/
public noncomputable def toTensorSheaf (τ : SiteKind)
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) :
    Stacks.Modules.BilinearMap (structureSheaf B S hS p hp τ).obj F.val G.val
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        (structureSheaf B S hS p hp τ)).obj F).obj G).val :=
  letI := hasWeakSheafify_associatedTopology B S hS p τ
  letI := wEqualsLocallyBijective_associatedTopology B S hS p τ
  Stacks.Modules.toTensorSheaf (structureSheaf B S hS p hp τ).obj
    (structureRingPresheaf_isSheaf B S hS p hp τ) F G

/-- The tensor product of two sheaves of modules formed on any one of the five associated sites
of the fibred category is already the tensor product in the category of sheaves of modules for
the inherited fppf topology: every bilinear map into a presheaf of modules whose sections form
an fppf sheaf factors through the pure-tensor map uniquely. -/
public theorem existsUnique_hom_tensorSheaf
 (τ : SiteKind)
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ))
    {H : PresheafOfModules.{u}
      (structureRingPresheaf (structureSheaf B S hS p hp τ).obj)}
    (hH : Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p .fppf)
      (SheafOfModules.moduleTypes H))
    (b : Stacks.Modules.BilinearMap (structureSheaf B S hS p hp τ).obj F.val G.val H) :
    ∃! f : (((Stacks.SheafOfModules.Tensor.sheafTensor
        (structureSheaf B S hS p hp τ)).obj F).obj G).val ⟶ H,
      ∀ (U : 𝒳ᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
        f.app U ((toTensorSheaf B S hS p hp τ F G).app U x y) = b.app U x y :=
  let := hasWeakSheafify_associatedTopology B S hS p τ
  let := wEqualsLocallyBijective_associatedTopology B S hS p τ
  Stacks.Modules.existsUnique_hom_toTensorSheaf (structureSheaf B S hS p hp τ).obj
    (structureRingPresheaf_isSheaf B S hS p hp τ)
    (BigFppfOver.associatedTopology_le_fppf B S hS p τ) F G hH b

end AlgebraicGeometry.FibredSite

end
