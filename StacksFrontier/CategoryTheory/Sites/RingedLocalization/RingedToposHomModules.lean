module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# A morphism of ringed topoi, read as the datum the modules development takes

Two structures in this development are called a *morphism of ringed topoi*. The canonical one,
`AlgebraicGeometry.RingedToposHom`, is the two-field structure that Stacks 01D3 part (2)
defines: a morphism of the underlying topoi together with the direct-image form
`f♯ : O_D ⟶ f_*O_C` of the structure map, at the level of sheaves of *commutative* rings. The
one that pullback and pushforward of sheaves of modules are built over,
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, has four fields: it works at the level of
sheaves of rings, stores *both* forms of the structure map, and asserts that they are adjunct.

This file supplies the passage from the first to the second, so that a statement quantifying
over morphisms of ringed topoi in the sense of Stacks 01D3 can still speak about the pullback
of sheaves of modules.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.ringFsharpInverseImage`: the inverse-image form of the
  structure map, at the level of sheaves of rings.
* `AlgebraicGeometry.RingedToposHom.ringFsharp`: its direct-image form at the same level.
* `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`: the four-field morphism of
  ringed topoi attached to a two-field one.

## Main results

* `AlgebraicGeometry.RingedToposHom.ringSheafMap_ringFsharp`: the two forms of the structure
  map are adjunct on underlying sheaves of sets.

## Implementation notes

The direct-image form is taken to be the adjunct of the inverse-image form under
`Stacks.Sheaves.ToposPushforward.ringImageAdjunction`, and *not* the image of `f.fSharp` under
`forget₂ CommRingCat RingCat`. The two agree, but establishing that is exactly the forgetful
compatibility of `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction` with
`ringImageAdjunction` — the statement
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`, proved in
`StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget`. Defining the
direct-image form by the adjunction instead makes the adjunctness field hold on sections by
definition, which is how `AlgebraicGeometry.RingedSite.overFsharpAdjoint` is set up for the
localization morphism, and it needs no transparency option. Nothing downstream is affected:
`pullbackModules`, and hence the pullback of sheaves of modules, depends only on the underlying
morphism of topoi and on the inverse-image form of the structure map.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y)

/-- The inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map, at the level of sheaves of
rings: the image of `AlgebraicGeometry.RingedToposHom.fSharpInverseImage` under
`forget₂ CommRingCat RingCat`. -/
noncomputable def ringFsharpInverseImage :
    inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf X.O :=
  (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map f.fSharpInverseImage

/-- The direct-image form `O_D ⟶ f_*O_C` of the structure map, at the level of sheaves of
rings: the adjunct of `ringFsharpInverseImage` under `f⁻¹ ⊣ f_*` for sheaves of rings. -/
noncomputable def ringFsharp :
    Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      pushforwardRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (ringImageAdjunction f.toToposHom).homEquiv _ _ f.ringFsharpInverseImage

/-- The two ring-level forms of the structure map are adjunct on underlying sheaves of sets:
the image of `ringFsharp` is the adjunct, under `f⁻¹ ⊣ f_*` for sheaves of sets, of the image
of `ringFsharpInverseImage`. -/
theorem ringSheafMap_ringFsharp :
    (sheafCompose Y.J (forget RingCat.{w'})).map f.ringFsharp =
      f.toToposHom.adj.homEquiv _ _
        ((sheafCompose X.J (forget RingCat.{w})).map f.ringFsharpInverseImage) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- A morphism of ringed topoi in the sense of Stacks 01D3, read as the four-field datum that
pullback and pushforward of sheaves of modules are constructed over. -/
noncomputable def toRingedToposModulesHom :
    Stacks.Sheaves.RingedToposModules.RingedToposHom X Y where
  toToposHom := f.toToposHom
  fSharp := f.ringFsharp
  fSharpInverseImage := f.ringFsharpInverseImage
  fSharp_adjunct := f.ringSheafMap_ringFsharp

/-- The underlying morphism of topoi of `toRingedToposModulesHom f` is that of `f`. -/
@[simp]
theorem toRingedToposModulesHom_toToposHom :
    f.toRingedToposModulesHom.toToposHom = f.toToposHom :=
  rfl

/-- The inverse-image form of the structure map of `toRingedToposModulesHom f` is
`ringFsharpInverseImage f`. -/
@[simp]
theorem toRingedToposModulesHom_fSharpInverseImage :
    f.toRingedToposModulesHom.fSharpInverseImage = f.ringFsharpInverseImage :=
  rfl

end AlgebraicGeometry.RingedToposHom

end
