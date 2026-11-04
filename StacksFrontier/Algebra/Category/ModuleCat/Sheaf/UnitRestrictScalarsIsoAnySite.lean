module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageAdjunction

/-!
# A sheaf of rings, over an isomorphic sheaf of rings, is the unit module

Let `e : R ≅ R'` be an isomorphism of sheaves of rings on a site `C : Type u` with
`[Category.{v} C]`, the rings taking values in `Type w`, the three universes independent. Read
`R'` as a sheaf of `R`-modules by restriction of scalars along `e`. Then it is isomorphic to `R`
viewed as a module over itself: the isomorphism is `e` itself, read as a map of modules.

## Main definitions

* `Stacks.SheafOfModules.ChangeOfRings.unitRestrictScalarsIsoOfIsoAnySite`: the isomorphism
  `unit R ≅ (restrictScalars e.hom).obj (unit R')`.

## Implementation notes

The construction is `Stacks.Sheaves.RingedToposModules.isoOfSheafIso` applied to `e` forgotten
to sheaves of sets, whose two hypotheses are that the comparison commutes with the addition maps
and with the scalar-multiplication maps. For the unit module those maps are the addition and
multiplication maps of the sheaf of rings, so the two hypotheses are that a morphism of sheaves
of rings is additive and multiplicative, which is
`CategoryTheory.Sheaf.ringAddHom_comp_ringSheafMap` and
`CategoryTheory.Sheaf.ringMulHom_comp_ringSheafMap`.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules.ChangeOfRings

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R R' : Sheaf J RingCat.{w}} (e : R ≅ R')

/-- **An isomorphic sheaf of rings, read by restriction of scalars, is the unit module.** The
comparison is `e` itself on underlying sheaves of sets; it is additive and multiplicative because
`e` is a morphism of sheaves of rings. -/
def unitRestrictScalarsIsoOfIsoAnySite :
    _root_.SheafOfModules.unit R ≅
      (_root_.SheafOfModules.restrictScalars e.hom).obj (_root_.SheafOfModules.unit R') :=
  isoOfSheafIso ((sheafCompose J (forget RingCat.{w})).mapIso e)
    (Sheaf.ringAddHom_comp_ringSheafMap e.hom)
    (by
      rw [moduleSMulHom_restrictScalars e.hom (_root_.SheafOfModules.unit R')]
      exact (Sheaf.ringMulHom_comp_ringSheafMap e.hom).trans
        (((congrArg (fun m ↦ m ≫ Sheaf.moduleSMulHom R' (_root_.SheafOfModules.unit R'))
            (Stacks.CategoryTheory.prodMap_id_comp_prodMap_id
              ((sheafCompose J (forget RingCat.{w})).map e.hom)
              ((sheafCompose J (forget RingCat.{w})).mapIso e).hom)).symm).trans
          (Category.assoc _ _ _)))

end Stacks.SheafOfModules.ChangeOfRings

end
