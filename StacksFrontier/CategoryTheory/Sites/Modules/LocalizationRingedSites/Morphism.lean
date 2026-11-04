module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalizationInverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# The localization morphism of a ringed site, as a morphism of ringed topoi

Let `(C, O)` be a ringed site and `U` an object of `C`. Stacks 04IX localizes `(C, O)` at `U`
to the ringed site `(C/U, O|_U)` and exhibits the localization as a morphism of ringed topoi
`(Sh(C/U), O|_U) ⟶ (Sh(C), O)`: the morphism of topoi is `π`, whose inverse image is
restriction along `Over.forget U`, and the structure map is the canonical identification of
`π⁻¹O` with `O|_U`.

This file constructs that morphism of ringed topoi. The localized ringed site is
`AlgebraicGeometry.RingedSite.over`, and the structure map in its inverse-image and direct-image
forms is `AlgebraicGeometry.RingedSite.overInverseImageFsharp` and `.overFsharpAdjoint`; a ringed
site is read as a ringed topos and these are assembled into a `RingedToposHom`.

## Main definitions

* `AlgebraicGeometry.RingedSite.ringedTopos`: a ringed site read as a ringed topos.
* `AlgebraicGeometry.RingedSite.localizationMorphism`: the localization morphism of ringed
  topoi attached to a ringed site and an object of its underlying category.

## Main results

* `AlgebraicGeometry.RingedSite.ringSheaf_ringedTopos`: the sheaf of rings
  underlying the structure sheaf of `ringedTopos X` is the one underlying that of `X`.
* `AlgebraicGeometry.RingedSite.localizationMorphism_toToposHom`,
  `.localizationMorphism_fSharp`, `.localizationMorphism_fSharpInverseImage`: the three data
  of the localization morphism.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v w}) (U : X.C)

/-- A ringed site read as a ringed topos: the same site and the same structure sheaf. -/
abbrev ringedTopos : RingedTopos.{v, u, max u v w} where
  C := X.C
  J := X.J
  O := X.O

/-- The sheaf of rings underlying the structure sheaf of `ringedTopos X` is the sheaf of rings
underlying the structure sheaf of `X`. -/
@[simp]
theorem ringSheaf_ringedTopos :
    Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos X).O =
      Stacks.SheafOfModules.Tensor.ringSheaf X.O :=
  rfl

/-- The two forms of the localization structure map are adjunct on underlying sheaves of
sets: the direct-image form is the adjunct of the inverse-image form under `π⁻¹ ⊣ π_*`. -/
theorem ringSheafMap_overFsharpAdjoint :
    (sheafCompose X.J (forget RingCat.{max u v w})).map (X.overFsharpAdjoint U) =
      (X.overMorphismOfTopoi U).adj.homEquiv _ _
        ((sheafCompose (X.J.over U) (forget RingCat.{max u v w})).map
          (X.overInverseImageFsharp U)) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The localization morphism of ringed topoi attached to a ringed site and an object `U` of its
underlying category: the morphism of topoi is the localization morphism, and the structure map is
the identification of the inverse image of the structure sheaf with its restriction to the slice
site over `U`. -/
noncomputable def localizationMorphism :
    RingedToposHom (ringedTopos (X.over U)) (ringedTopos X) where
  toToposHom := X.overMorphismOfTopoi U
  fSharp := X.overFsharpAdjoint U
  fSharpInverseImage := X.overInverseImageFsharp U
  fSharp_adjunct := X.ringSheafMap_overFsharpAdjoint U

/-- The morphism of topoi underlying `localizationMorphism X U` is `X.overMorphismOfTopoi U`. -/
@[simp]
theorem localizationMorphism_toToposHom :
    (X.localizationMorphism U).toToposHom = X.overMorphismOfTopoi U :=
  rfl

/-- The direct-image structure map of `localizationMorphism X U` is `X.overFsharpAdjoint U`. -/
@[simp]
theorem localizationMorphism_fSharp :
    (X.localizationMorphism U).fSharp = X.overFsharpAdjoint U :=
  rfl

/-- The inverse-image structure map of `localizationMorphism X U` is
`X.overInverseImageFsharp U`. -/
@[simp]
theorem localizationMorphism_fSharpInverseImage :
    (X.localizationMorphism U).fSharpInverseImage = X.overInverseImageFsharp U :=
  rfl

end AlgebraicGeometry.RingedSite
