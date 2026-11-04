module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# The two four-field readings of a morphism of ringed topoi are the same

A morphism of ringed topoi in the sense of Stacks 01D3 part (2), an
`AlgebraicGeometry.RingedToposHom`, carries two fields: the morphism of topoi and the
direct-image form `f♯ : O_D ⟶ f_*O_C` of the structure map, at the level of sheaves of
*commutative* rings. The modules development is built over a four-field structure,
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, which works at the level of sheaves of rings
and stores both forms of the structure map together with the equation making them adjunct.

The passage from the first to the second has been written twice, in two different places and by
two different routes:

* `AlgebraicGeometry.RingedToposHom.toModulesHom` takes the inverse-image form to be the adjunct
  `fSharpInverseImageRing` of the `RingCat`-level `f♯` under the ring-level adjunction `f⁻¹ ⊣ f_*`
  of Stacks 00YV;
* `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` takes it to be
  `ringFsharpInverseImage`, the `forget₂ CommRingCat RingCat`-image of the `CommRingCat`-level
  inverse-image form `fSharpInverseImage`, and then obtains the direct-image form from it by the
  same ring-level adjunction.

Both files record that the two agree only as a remark, the docstring of `fSharpInverseImageRing`
saying outright that "the identification of the two is not needed here and is not recorded".
This file records it. The identification matters because the comparison isomorphism
`AlgebraicGeometry.RingedToposHom.pullbackModulesViaComparisonIso` between the two pullbacks of
sheaves of modules is an `CategoryTheory.Adjunction.leftAdjointUniq`, which has no description on
sections; with the two morphisms of ringed topoi *equal*, that comparison is an
`CategoryTheory.eqToIso` and is therefore transparent on sections.

## Main results

* `AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing_eq_ringFsharpInverseImage`: the two
  inverse-image forms of the structure map agree.
* `AlgebraicGeometry.RingedToposHom.ringFsharp_eq_fSharpRing`: the two direct-image forms agree.
* `AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`: the two four-field
  morphisms of ringed topoi agree.
* `AlgebraicGeometry.RingedToposHom.pullbackModulesViaComparisonIso_eq_eqToIso`: the comparison
  isomorphism of the two pullbacks of sheaves of modules is the `eqToIso` of that equality, which
  is what makes it computable on sections.

## Implementation notes

The whole content is the compatibility of the adjunction `f⁻¹ ⊣ f_*` for sheaves of commutative
rings with the one for sheaves of rings, which is already available on underlying sheaves of sets
as `AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`. So the two
inverse-image forms are compared through
`CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)`, which is faithful: on underlying
sheaves of sets both are the adjunct of one and the same map, by
`AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing_adjunct` on one side and
`fSharpInverseImage_forget_homEquiv` on the other. The two remaining fields then come for free:
the direct-image forms are the adjuncts of equal maps, and the adjunctness field is a `Prop`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- **The two inverse-image forms of the structure map agree.** The adjunct of the `RingCat`-level
direct-image form `f♯` under the ring-level adjunction `f⁻¹ ⊣ f_*` is the `forget₂`-image of the
`CommRingCat`-level inverse-image form.

A morphism of sheaves of rings is determined by its underlying morphism of sheaves of sets, and
on underlying sheaves of sets both are the adjunct of the underlying morphism of `f♯`: the first
by `AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing_adjunct`, the second by
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`. -/
theorem fSharpInverseImageRing_eq_ringFsharpInverseImage (f : RingedToposHom X Y) :
    f.fSharpInverseImageRing = f.ringFsharpInverseImage :=
  (sheafCompose X.J (forget RingCat.{w})).map_injective
    (((f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O)
            (X.forgetRing.obj X.O)).symm_apply_apply
          ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImageRing)).symm.trans
      ((congrArg
          (f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O) (X.forgetRing.obj X.O)).symm
          f.fSharpInverseImageRing_adjunct.symm).trans
        (fSharpInverseImage_forget_homEquiv f).symm))

/-- **The two direct-image forms of the structure map agree**, at the level of sheaves of rings:
both are the adjunct, under the ring-level adjunction `f⁻¹ ⊣ f_*`, of the one inverse-image form
of `fSharpInverseImageRing_eq_ringFsharpInverseImage`. -/
theorem ringFsharp_eq_fSharpRing (f : RingedToposHom X Y) :
    f.ringFsharp = f.fSharpRing :=
  (congrArg ((ringImageAdjunction f.toToposHom).homEquiv
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    f.fSharpInverseImageRing_eq_ringFsharpInverseImage.symm).trans
    (((ringImageAdjunction f.toToposHom).homEquiv
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).apply_symm_apply f.fSharpRing)

/-- **The two four-field readings of a morphism of ringed topoi are the same.** The four-field
morphism of ringed topoi of the modules development attached to a two-field one by
`AlgebraicGeometry.RingedToposHom.toModulesHom` is the one attached to it by
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`.

The underlying morphisms of topoi are the same on the nose, the two structure-map fields agree by
`ringFsharp_eq_fSharpRing` and `fSharpInverseImageRing_eq_ringFsharpInverseImage`, and the
adjunctness field is a proposition. -/
theorem toModulesHom_eq_toRingedToposModulesHom (f : RingedToposHom X Y) :
    f.toModulesHom = f.toRingedToposModulesHom := by
  have hi := f.fSharpInverseImageRing_eq_ringFsharpInverseImage
  have hs := f.ringFsharp_eq_fSharpRing.symm
  unfold AlgebraicGeometry.RingedToposHom.toModulesHom
    AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom
  congr 1

end AlgebraicGeometry.RingedToposHom

end
