module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage

/-!
# Composing derived direct images on small étale sites

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and let `Λ` be a ring.  Direct image
of sheaves of `Λ`-modules for the small étale topologies composes, `(f ≫ g)_* = g_* ∘ f_*`,
because base change of étale schemes does.  This file records that composition isomorphism and
pushes it through the comparison transformation of
`CategoryTheory.Functor.rightDerivedFunctorPlusComp` to obtain the derived statement
`R(f ≫ g)_* ≅ Rf_* ∘ Rg_*` on bounded below derived categories.

The derived statement is the ingredient a geometric endomorphism needs in order to act on
cohomology: if `π : Y ⟶ Y` satisfies `π ≫ g = g` then the composition isomorphism reads
`Rπ_* ⋙ Rg_* ≅ Rg_*`, so a map `K ⟶ Rπ_* K` produces an endomorphism of `Rg_* K`.

## Main definitions

* `Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso` — transport of the right derived
  functor along an isomorphism `F ⋙ G ≅ H` of underived functors.
* `Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso` — the comparison
  `RH ≅ RF ⋙ RG` attached to such an isomorphism, when `F` preserves injective objects.
* `Stacks.EtaleCohomology.etaleModuleDirectImageComp` — the underived composition isomorphism
  `f_* ⋙ g_* ≅ (f ≫ g)_*` for sheaves of modules on small étale sites.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageComp` — its derived form
  `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*`.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageEndomorphismComp` — the special case
  `Rπ_* ⋙ Rg_* ≅ Rg_*` of an endomorphism `π` of the source over the target.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageEndomorphism` — the endomorphism of
  `Rg_*` attached to such a `π` and a transformation `𝟭 ⟶ Rπ_*`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDirectImageComp_hom_app_hom_app` — the underived
  composition isomorphism is restriction of sections along base change.

## Implementation notes

The composite morphism is a separate argument `fg` together with a proof `fg = f ≫ g`, as in
`Stacks.EtaleCohomology.smallEtalePushforwardComp'`.  This is what makes the endomorphism case
usable: for `π ≫ g = g` one takes `fg := g`, and no transport along an equality of morphisms of
schemes is needed anywhere.

Preservation of injective objects by `f_*` is a condition in the general section, where `F` is
an arbitrary additive functor, and nothing at all in the étale section: for sheaves of modules
on small étale sites it is a theorem for every morphism of schemes,
`Stacks.EtaleCohomology.etaleModuleDirectImage_preservesInjectiveObjects`, because inverse image
along `f` is exact.

## References

* [Stacks Project, Tag 03Q0](https://stacks.math.columbia.edu/tag/03Q0)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w w' w'' v v' v'' t u r

namespace Stacks.EtaleCohomology

/-! ### Transport of the comparison along an isomorphism of underived functors -/

section General

variable {C : Type u} {D : Type v} {E : Type t}
  [Category.{w} C] [Category.{w'} D] [Category.{w''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{v'} C] [HasDerivedCategory.{v''} D] [HasDerivedCategory.{v''} E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]

/-- The isomorphism `(F ⋙ G).mapHomotopyCategoryPlus ≅ H.mapHomotopyCategoryPlus` induced by an
isomorphism `F ⋙ G ≅ H`. -/
def mapHomotopyCategoryPlusIsoOfCompIso (e : F ⋙ G ≅ H) :
    (F ⋙ G).mapHomotopyCategoryPlus ≅ H.mapHomotopyCategoryPlus :=
  (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).symm ≪≫
    Functor.mapHomotopyCategoryPlusCompIso e

/-- Right derived functors on bounded below derived categories transport along an isomorphism
`F ⋙ G ≅ H` of underived functors: `R(G ∘ F) ≅ RH`. -/
def rightDerivedFunctorPlusIsoOfCompIso (e : F ⋙ G ≅ H) :
    (F ⋙ G).rightDerivedFunctorPlus ≅ H.rightDerivedFunctorPlus :=
  Functor.rightDerivedNatIso _ _ (F ⋙ G).rightDerivedFunctorPlusUnit
    H.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C)
    (Functor.isoWhiskerRight (mapHomotopyCategoryPlusIsoOfCompIso F G H e)
      DerivedCategory.Plus.Qh)

variable [F.PreservesInjectiveObjects]

/-- **The comparison isomorphism `RH ≅ RF ⋙ RG` attached to an isomorphism `F ⋙ G ≅ H`.**  It
is the composition comparison of [Stacks, Tag 05T2], which is invertible because `F` preserves
injective objects, transported along the induced isomorphism of right derived functors. -/
def rightDerivedFunctorPlusCompIsoOfIso (e : F ⋙ G ≅ H) :
    H.rightDerivedFunctorPlus ≅ F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusIsoOfCompIso F G H e).symm ≪≫
    Functor.rightDerivedFunctorPlusCompIso F G

end General

/-! ### Composition of direct images of sheaves of modules -/

section EtaleModules

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ]

/-- Direct image of sheaves of `Λ`-modules along a composite of morphisms of schemes is the
composite of the direct images, for the small étale topologies. -/
def etaleModuleDirectImageComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleDirectImage.{u, r} Λ g ≅
      etaleModuleDirectImage.{u, r} Λ fg :=
  smallEtalePushforwardComp' f g fg hfg (ModuleCat.{max (u + 1) r} Λ)

/-- The composition isomorphism for direct images of sheaves of modules is restriction of
sections along the base change comparison. -/
lemma etaleModuleDirectImageComp_hom_app_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (F : EtaleModules.{u, r} Λ X) (U : (Z.Etale)ᵒᵖ) :
    ((etaleModuleDirectImageComp.{u, r} Λ f g fg hfg).hom.app F).hom.app U =
      F.obj.map (op ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U.unop)) :=
  Category.id_comp _

/-- **`R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` for sheaves of modules on small étale sites.**  This is the
composition comparison of [Stacks, Tag 05T2] for the underived composition isomorphism
`Stacks.EtaleCohomology.etaleModuleDirectImageComp`; it is invertible because `f_*` preserves
injective objects, which is
`Stacks.EtaleCohomology.etaleModuleDirectImage_preservesInjectiveObjects`. -/
def etaleModuleDerivedDirectImageComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    etaleModuleDerivedDirectImage.{u, r} Λ fg ≅
      etaleModuleDerivedDirectImage.{u, r} Λ f ⋙ etaleModuleDerivedDirectImage.{u, r} Λ g :=
  rightDerivedFunctorPlusCompIsoOfIso (etaleModuleDirectImage.{u, r} Λ f)
    (etaleModuleDirectImage.{u, r} Λ g) (etaleModuleDirectImage.{u, r} Λ fg)
    (etaleModuleDirectImageComp.{u, r} Λ f g fg hfg)

/-- **`Rπ_* ⋙ Rg_* ≅ Rg_*` for an endomorphism `π` of the source over the target.** -/
def etaleModuleDerivedDirectImageEndomorphismComp {Y Z : Scheme.{u}} (π : Y ⟶ Y) (g : Y ⟶ Z)
    (hπ : π ≫ g = g) :
    etaleModuleDerivedDirectImage.{u, r} Λ g ≅
      etaleModuleDerivedDirectImage.{u, r} Λ π ⋙ etaleModuleDerivedDirectImage.{u, r} Λ g :=
  etaleModuleDerivedDirectImageComp.{u, r} Λ π g g hπ.symm

/-- **The endomorphism of `Rg_*` attached to an endomorphism `π` of the source over the target
and a transformation `𝟭 ⟶ Rπ_*`.**  It is `Rg_*` applied to the transformation, followed by the
inverse of the composition comparison `Rπ_* ⋙ Rg_* ≅ Rg_*`.

For `π` a Frobenius and the transformation the adjoint `K ⟶ Rπ_* K` of the canonical map
`π^{-1} K ⟶ K`, this is the pullback action of `π` on derived direct images. -/
def etaleModuleDerivedDirectImageEndomorphism {Y Z : Scheme.{u}} (π : Y ⟶ Y) (g : Y ⟶ Z)
    (hπ : π ≫ g = g)
    (γ : 𝟭 (DerivedCategory.Plus (EtaleModules.{u, r} Λ Y)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ π) :
    etaleModuleDerivedDirectImage.{u, r} Λ g ⟶ etaleModuleDerivedDirectImage.{u, r} Λ g :=
  (Functor.leftUnitor (etaleModuleDerivedDirectImage.{u, r} Λ g)).inv ≫
    Functor.whiskerRight γ (etaleModuleDerivedDirectImage.{u, r} Λ g) ≫
      (etaleModuleDerivedDirectImageEndomorphismComp.{u, r} Λ π g hπ).inv

/-- The component at `M` of `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageEndomorphism` is
`Rg_*` applied to the component of `γ` at `M`, followed by the inverse of the composition
comparison at `M`. -/
lemma etaleModuleDerivedDirectImageEndomorphism_app {Y Z : Scheme.{u}} (π : Y ⟶ Y) (g : Y ⟶ Z)
    (hπ : π ≫ g = g)
    (γ : 𝟭 (DerivedCategory.Plus (EtaleModules.{u, r} Λ Y)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ π)
    (M : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y)) :
    (etaleModuleDerivedDirectImageEndomorphism.{u, r} Λ π g hπ γ).app M =
      (etaleModuleDerivedDirectImage.{u, r} Λ g).map (γ.app M) ≫
        (etaleModuleDerivedDirectImageEndomorphismComp.{u, r} Λ π g hπ).inv.app M :=
  Category.id_comp _

end EtaleModules

end Stacks.EtaleCohomology

end
