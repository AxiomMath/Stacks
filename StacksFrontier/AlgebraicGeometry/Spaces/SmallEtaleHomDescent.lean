module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite

/-!
# Gluing morphisms of `𝒪_X`-modules from a covering family of étale charts

Let `X` be an algebraic space over a scheme `S` in a big fppf site `B`.  A family of étale charts
covering the final object of the small étale site of `X` is enough to glue morphisms of
`𝒪_X`-modules: a compatible family of morphisms over the charts extends to a unique morphism, and
a compatible family of isomorphisms to an isomorphism.  This is Stacks 03EM, instantiated at the
small étale site.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleStructurePresheaf`: the structure sheaf of the small étale
  site, as a `CommRingCat`-valued presheaf.

## Main results

* `AlgebraicGeometry.Space.existsUnique_hom_of_isCompatible_smallEtale`: a compatible family of
  morphisms of the underlying presheaves of modules over a covering family of charts extends to a
  unique morphism.
* `AlgebraicGeometry.Space.existsUnique_sheafHom_of_isCompatible_smallEtale`: the same for
  morphisms of `𝒪_X`-modules.
* `AlgebraicGeometry.Space.internalHom_isSheaf_forget_smallEtale`: the internal hom into an
  `𝒪_X`-module, read on underlying sets, is a sheaf.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The structure sheaf of the small étale site of `F`, as a `CommRingCat`-valued presheaf. -/
noncomputable abbrev smallEtaleStructurePresheaf : (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u} :=
  (structureSheaf B S hS F hF).obj

/-- The presheaves of modules over `Oforget` of `smallEtaleStructurePresheaf` are, definitionally,
the presheaves of modules over the ring sheaf of the small étale ringed site of `F`. -/
theorem modules_val_eq_presheafOfModules_smallEtale :
    PresheafOfModules.{u} (Oforget (smallEtaleStructurePresheaf B S hS F hF)) =
      PresheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj := rfl

variable {F hF}

/-- For `N` an `𝒪_F`-module, the internal hom out of any `𝒪_F`-module into `N`, read on underlying
sets, is a sheaf. -/
theorem internalHom_isSheaf_forget_smallEtale (M N : Modules.{u, u} B S hS F hF) :
    Presheaf.IsSheaf (SmallEtale.topology B S hS F)
      ((internalHom (smallEtaleStructurePresheaf B S hS F hF) M.val N.val).presheaf ⋙
        CategoryTheory.forget _) :=
  internalHom_isSheaf_forget _ M.val N.val N.isSheaf

/-- Let `Y` be a family of étale
charts of `F` covering the final object of the small étale site.  A family of morphisms of the
underlying presheaves of modules over the `Y i`, agreeing after relocalization to any common
refinement, extends to a unique morphism `M.val ⟶ N.val`. -/
theorem existsUnique_hom_of_isCompatible_smallEtale (M N : Modules.{u, u} B S hS F hF)
    {ι : Type w} {Y : ι → SmallEtale B S hS F}
    (hY : (SmallEtale.topology B S hS F).CoversTop Y)
    {α : Presheaf.FamilyOfElementsOnObjects
      ((internalHom (smallEtaleStructurePresheaf B S hS F hF) M.val N.val).presheaf ⋙
        CategoryTheory.forget _) Y}
    (hα : α.IsCompatible) :
    ∃! φ : M.val ⟶ N.val,
      ∀ i, (restrFun (smallEtaleStructurePresheaf B S hS F hF) (Y i)).map φ = α i :=
  existsUnique_hom_of_isCompatible _ M.val N.val hY
    (internalHom_isSheaf_forget_smallEtale B S hS M N) hα

/-- A compatible family of morphisms over a family of étale charts covering the final object of
the small étale site extends to a unique morphism of `𝒪_F`-modules. -/
theorem existsUnique_sheafHom_of_isCompatible_smallEtale (M N : Modules.{u, u} B S hS F hF)
    {ι : Type w} {Y : ι → SmallEtale B S hS F}
    (hY : (SmallEtale.topology B S hS F).CoversTop Y)
    {α : Presheaf.FamilyOfElementsOnObjects
      ((internalHom (smallEtaleStructurePresheaf B S hS F hF) M.val N.val).presheaf ⋙
        CategoryTheory.forget _) Y}
    (hα : α.IsCompatible) :
    ∃! φ : M ⟶ N,
      ∀ i, (restrFun (smallEtaleStructurePresheaf B S hS F hF) (Y i)).map φ.val = α i := by
  obtain ⟨ψ, hψ, huniq⟩ :=
    existsUnique_hom_of_isCompatible_smallEtale B S hS M N hY hα
  exact ⟨⟨ψ⟩, hψ, fun φ hφ ↦ SheafOfModules.hom_ext (huniq φ.val hφ)⟩

end AlgebraicGeometry.Space

end
