module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
import StacksCore.Tactic.StacksAttribute

/-!
# A morphism of ringed topoi from its structure map in inverse-image form

A `Stacks.Sheaves.RingedToposModules.RingedToposHom` carries the structure map of a morphism of
ringed topoi in both of its forms — the direct-image form `f♯ : O_D ⟶ f_*O_C` of Stacks 01D3 (2)
and the inverse-image form `f⁻¹O_D ⟶ O_C` — together with the requirement that the two correspond
under the adjunction `f⁻¹ ⊣ f_*`. Either form therefore determines the morphism, and this file
builds one from the inverse-image form, which is the form in which a structure map is often the
one that is available.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.RingedToposHom.ofFSharpInverseImage`: a morphism of ringed
  topoi built from its structure map in inverse-image form.

## Implementation notes

The direct-image form is produced as the unit `O_D ⟶ f_*f⁻¹O_D` followed by the direct image of
the given map, and the adjunction condition then holds by
`Stacks.Sheaves.RingedToposModules.fSharp_underlying`. This is the half of Stacks 00YV for sheaves
of rings that the adjunction `f⁻¹ ⊣ f_*` of sheaves of sets supplies on its own, without a
ring-level adjunction.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u₁ u₂ v₁ v₂ w

namespace Stacks.Sheaves.RingedToposModules.RingedToposHom

open AlgebraicGeometry

variable {X : RingedTopos.{v₁, u₁, w}} {Y : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]

/-- A morphism of ringed topoi built from its structure map in inverse-image form. The
direct-image form is the unit `O_Y ⟶ f_*f⁻¹O_Y` followed by the direct image of `a`, which is
the adjunct of `a` by `Stacks.Sheaves.RingedToposModules.fSharp_underlying`; this is the half
of Stacks 00YV for sheaves of rings that the adjunction `f⁻¹ ⊣ f_*` of sheaves of sets
supplies without a ring-level adjunction. -/
def ofFSharpInverseImage (f : MorphismOfTopoi X.Topos Y.Topos)
    (a : inverseImageRingSheaf f (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf X.O) :
    RingedToposHom X Y where
  toToposHom := f
  fSharp :=
    ringUnit f (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≫
      (show pushforwardRingSheaf f
            (inverseImageRingSheaf f (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
          pushforwardRingSheaf f (Stacks.SheafOfModules.Tensor.ringSheaf X.O) from
        pullbackRingSheafMap Y.J f.pushforward a)
  fSharpInverseImage := a
  fSharp_adjunct := Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The morphism of topoi underlying `ofFSharpInverseImage f a` is `f`. -/
@[simp] theorem ofFSharpInverseImage_toToposHom (f : MorphismOfTopoi X.Topos Y.Topos)
    (a : inverseImageRingSheaf f (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf X.O) :
    (ofFSharpInverseImage f a).toToposHom = f := rfl

/-- The inverse-image form of the structure map of `ofFSharpInverseImage f a` is `a`. -/
@[simp] theorem ofFSharpInverseImage_fSharpInverseImage (f : MorphismOfTopoi X.Topos Y.Topos)
    (a : inverseImageRingSheaf f (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf X.O) :
    (ofFSharpInverseImage f a).fSharpInverseImage = a := rfl

end Stacks.Sheaves.RingedToposModules.RingedToposHom

end
