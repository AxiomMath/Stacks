module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism

/-!
# The comparison of direct images of a genuine composite of morphisms of ringed topoi

For two-field morphisms of ringed topoi `φ : X ⟶ Y` and `ψ : Y ⟶ Z`
(`AlgebraicGeometry.RingedToposHom`), read as four-field morphisms through
`AlgebraicGeometry.RingedToposHom.toModulesHom`, this file gives the comparison

`τ : φ_* ⋙ ψ_* ≅ (ψ ∘ φ)_*`

of the geometric direct images, which is the identity, and the equation saying that `τ` carries
the composite structure map `Stacks.Sheaves.RingedToposModules.fSharpSetComp` of `φ` and `ψ` to
the structure map of `ψ ∘ φ`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.toModulesHomPushforwardIso`: the comparison `τ` of the
  direct images of `φ`, `ψ` and `ψ ∘ φ`, the identity isomorphism.

## Main results

* `AlgebraicGeometry.RingedToposHom.fSharpSet_toModulesHom`: the direct-image form of the
  structure map of the four-field reading of a two-field morphism of ringed topoi is its
  structure map `AlgebraicGeometry.RingedToposHom.forgetFSharp` on underlying sheaves of sets.
* `AlgebraicGeometry.RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso`: the comparison
  `τ` carries the composite structure map of `φ` and `ψ` to the structure map of `ψ ∘ φ`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules (fSharpSet fSharpSetComp fSharpSetComp_eq)

namespace AlgebraicGeometry.RingedToposHom

universe w w' w'' v u v' u' v'' u''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]

/-- For two-field morphisms of ringed topoi `φ : X ⟶ Y` and `ψ : Y ⟶ Z`, the identity
isomorphism between the composite of the direct images of `φ` and `ψ` and the direct image of
`ψ ∘ φ`. -/
def toModulesHomPushforwardIso (φ : RingedToposHom X Y) (ψ : RingedToposHom Y Z) :
    φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅
      (ψ.comp φ).toToposHom.pushforward :=
  Iso.refl _

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})] in
/-- The comparison `toModulesHomPushforwardIso φ ψ` is the identity at every sheaf. -/
theorem toModulesHomPushforwardIso_hom_app (φ : RingedToposHom X Y) (ψ : RingedToposHom Y Z)
    (M : Sheaf X.J (Type w)) :
    (toModulesHomPushforwardIso φ ψ).hom.app M =
      𝟙 ((φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward).obj M) :=
  rfl

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The direct-image form of the structure map of the four-field reading
`AlgebraicGeometry.RingedToposHom.toModulesHom` of a morphism of ringed topoi, in the spelling
`Stacks.Sheaves.RingedToposModules.fSharpSet`, is the structure map
`AlgebraicGeometry.RingedToposHom.forgetFSharp` of the two-field morphism on underlying sheaves of
sets. -/
theorem fSharpSet_toModulesHom (φ : RingedToposHom X Y) :
    fSharpSet φ.toModulesHom = φ.forgetFSharp :=
  rfl

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})] in
/-- The composite structure map of `φ` and `ψ`, followed by the comparison
`AlgebraicGeometry.RingedToposHom.toModulesHomPushforwardIso` of the direct images, is the
structure map of `ψ ∘ φ`. -/
theorem fSharpSetComp_toModulesHomPushforwardIso (φ : RingedToposHom X Y)
    (ψ : RingedToposHom Y Z) :
    fSharpSetComp φ.toModulesHom ψ.toModulesHom ≫
        (toModulesHomPushforwardIso φ ψ).hom.app
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      fSharpSet (ψ.comp φ).toModulesHom :=
  (Category.comp_id (fSharpSetComp φ.toModulesHom ψ.toModulesHom)).trans
    ((fSharpSetComp_eq φ.toModulesHom ψ.toModulesHom).trans (forgetFSharp_comp ψ φ).symm)

end AlgebraicGeometry.RingedToposHom

end
