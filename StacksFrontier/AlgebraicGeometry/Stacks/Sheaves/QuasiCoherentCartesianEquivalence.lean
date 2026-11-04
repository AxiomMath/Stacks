module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianChangeOfRings
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines

/-!
# Quasi-coherent modules on a category fibred in groupoids are cartesian modules on its affines

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `𝒳_{affine}` be its affine
subcategory (Stacks 0H0A), with the structure presheaf `x ↦ Γ(p(x), 𝒪)`. A presheaf of modules
on `𝒳_{affine}` is *cartesian* when every base-change map `𝓕(x') ⊗_{𝒪(x')} 𝒪(x) ⟶ 𝓕(x)` is an
isomorphism. This file proves that restriction along the affine inclusion is an equivalence

`QCoh(𝒪_𝒳) ≌ {cartesian presheaves of modules on 𝒳_{affine}}`.

This is Stacks 0H0E, conditions (1) and (8), read as an equivalence of categories: by 0H0C the
restriction of fppf sheaves of modules to `𝒳_{affine}` is an equivalence, by 0H0E (8) ⇒ (1) the
restriction of a quasi-coherent module is cartesian, and by 0H0E (1) ⇒ (8) every cartesian
presheaf is, as an fppf sheaf, the restriction of a quasi-coherent module.

## Main definitions

* `AlgebraicGeometry.Stack.AffineCategory.quasicoherentToCartesian`: the restriction functor
  `QCoh(𝒪_𝒳) ⥤ {cartesian presheaves of modules on 𝒳_{affine}}`.
* `AlgebraicGeometry.Stack.AffineCategory.quasicoherentEquivCartesian`: that functor as an
  equivalence of categories.

## References

* [Stacks Project, Tag 0H0C](https://stacks.math.columbia.edu/tag/0H0C)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack.AffineCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The structure presheaf `x ↦ Γ(p(x), 𝒪)` of the affine subcategory. -/
abbrev structureRings : (AffineCategory B S hS p)ᵒᵖ ⥤ CommRingCat.{u} :=
  (toScheme B S hS p).op ⋙ Scheme.Γ

/-- The restriction to `𝒳_{affine}` of a quasi-coherent module on `𝒳`, as a presheaf of
modules. -/
def restrictToAffine (G : FibredSite.quasicoherentModules.{u, v, w, u} B S hS p hp) :
    PresheafOfModules.{u} (Stacks.ringPresheaf (structureRings B S hS p)) :=
  letI := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  ((Stacks.DenseSubsiteModules.moduleRestriction
    (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf)
    (inclusion B S hS p) (FibredSite.ringStructureSheafCore B S hS p hp .fppf)).obj G.obj).val

/-- **The restriction to `𝒳_{affine}` of a quasi-coherent module is cartesian**: Stacks 0H0E,
(8) ⇒ (1). -/
theorem cartesianModules_restrictToAffine
    (G : FibredSite.quasicoherentModules.{u, v, w, u} B S hS p hp) :
    Stacks.PresheafOfModules.cartesianModules.{v, w, u, u} (structureRings B S hS p)
      (restrictToAffine B S hS p hp G) := by
  have := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  let N := (Stacks.DenseSubsiteModules.moduleRestriction
    (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf)
    (inclusion B S hS p) (FibredSite.ringStructureSheafCore B S hS p hp .fppf)).obj G.obj
  let F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (siteKindRingedSite B S hS p hp .fppf).chaotic.O) :=
    ⟨N.val, Presheaf.isSheaf_bot _⟩
  have key := (tfae_isQuasicoherent B S hS p hp F).out 8 1
  exact fun _ _ f => key.1 ⟨N.isSheaf, G.obj, G.property, ⟨Iso.refl _⟩⟩ f.unop

/-- **Restriction to the affine subcategory**, from the quasi-coherent modules on `𝒳` to the
cartesian presheaves of modules on `𝒳_{affine}`. -/
def quasicoherentToCartesian :
    FibredSite.quasicoherentModules.{u, v, w, u} B S hS p hp ⥤
      (Stacks.PresheafOfModules.cartesianModules.{v, w, u, u}
        (structureRings B S hS p)).FullSubcategory :=
  letI := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ Stacks.DenseSubsiteModules.moduleRestriction
      (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf)
      (inclusion B S hS p) (FibredSite.ringStructureSheafCore B S hS p hp .fppf) ⋙
      SheafOfModules.forget _)
    (cartesianModules_restrictToAffine B S hS p hp)

/-- Restriction to the affine subcategory is fully faithful on quasi-coherent modules. -/
def fullyFaithfulQuasicoherentToCartesian :
    (quasicoherentToCartesian B S hS p hp).FullyFaithful := by
  letI := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  have := isEquivalence_moduleRestriction B S hS p hp
    (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf)
    (FibredSite.ringStructureSheafCore B S hS p hp .fppf)
  refine Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι
    (Stacks.PresheafOfModules.cartesianModules.{v, w, u, u} (structureRings B S hS p))) ?_
  exact ((ObjectProperty.fullyFaithfulι (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf))).comp
    (Functor.FullyFaithful.ofFullyFaithful (Stacks.DenseSubsiteModules.moduleRestriction
      (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf)
      (inclusion B S hS p) (FibredSite.ringStructureSheafCore B S hS p hp .fppf)))).comp
    (SheafOfModules.fullyFaithfulForget _)

/-- Restriction to the affine subcategory is full on quasi-coherent modules. -/
instance : (quasicoherentToCartesian B S hS p hp).Full :=
  (fullyFaithfulQuasicoherentToCartesian B S hS p hp).full

/-- Restriction to the affine subcategory is faithful on quasi-coherent modules. -/
instance : (quasicoherentToCartesian B S hS p hp).Faithful :=
  (fullyFaithfulQuasicoherentToCartesian B S hS p hp).faithful

/-- **Every cartesian presheaf of modules on `𝒳_{affine}` is the restriction of a quasi-coherent
module on `𝒳`**: Stacks 0H0E, (1) ⇒ (8). -/
instance : (quasicoherentToCartesian B S hS p hp).EssSurj where
  mem_essImage P := by
    have := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
    let F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (siteKindRingedSite B S hS p hp .fppf).chaotic.O) :=
      ⟨P.obj, Presheaf.isSheaf_bot _⟩
    have key := (tfae_isQuasicoherent B S hS p hp F).out 8 1
    obtain ⟨_, G, hG, ⟨e⟩⟩ := key.2 fun _ _ f => P.property f.op
    exact ⟨⟨G, hG⟩, ⟨ObjectProperty.isoMk _ ((SheafOfModules.forget _).mapIso e)⟩⟩

/-- Restriction to the affine subcategory is an equivalence of categories. -/
instance : (quasicoherentToCartesian B S hS p hp).IsEquivalence where

/-- **Quasi-coherent modules on a category fibred in groupoids are the cartesian presheaves of
modules on its affine subcategory** (Stacks 0H0C and 0H0E): restriction along the affine
inclusion is an equivalence of categories. -/
def quasicoherentEquivCartesian :
    FibredSite.quasicoherentModules.{u, v, w, u} B S hS p hp ≌
      (Stacks.PresheafOfModules.cartesianModules.{v, w, u, u}
        (structureRings B S hS p)).FullSubcategory :=
  (quasicoherentToCartesian B S hS p hp).asEquivalence

end AlgebraicGeometry.Stack.AffineCategory

end
