module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentPullbackRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposTwoMorphismUnderlying
import StacksCore.Tactic.StacksAttribute

/-!
# The underlying sheaf of sets of the comparison of Stacks 0D72

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
`CategoryTheory.SimplicialSiteSituation.componentPullbackModulesRestrictionIso` identifies the
pullback of sheaves of modules along the component morphism of ringed topoi `g_n` with the
literal restriction of modules to the degree-`n` component. This file computes its underlying
morphism of sheaves of sets: it is the comparison of Stacks 09WG, read through the identification
`AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso` of the underlying sheaf of a
pullback of modules with an inverse image.

That value is what makes the unit of the adjunction of Stacks 03D7, transported along the
comparison of Stacks 0D72, computable on underlying sheaves of sets; the comparison itself is
assembled from five factors and nothing about it was pinned down before.

## Main results

* `AlgebraicGeometry.RingedToposHom.pullbackUnitUnderlyingIso_hom_comp_extendScalarsFSharpIso`:
  the one factor of the comparison that is not the identity on underlying sheaves of sets —
  extension of scalars read as restriction of scalars along the inverse of an invertible
  structure map — is inverse to the unit of the change-of-rings adjunction of Stacks 03CZ there.
* `AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso_inv_comp_isoWhiskerLeft`: hence
  any comparison of the pullback of modules with a functor, presented as that factor followed by
  a comparison of restrictions of scalars, has that second comparison as its underlying morphism.
* `CategoryTheory.SimplicialSiteSituation.componentPullbackModulesRestrictionIso_underlying`:
  **the value.** On underlying sheaves of sets the comparison of Stacks 0D72 is the comparison of
  Stacks 09WG.

## Implementation notes

The comparison of Stacks 0D72 is `Iso.trans` of five factors, four of which are the identity on
underlying sheaves of sets: two transports of a comparison of inverse images along restriction of
scalars (`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso` and
`Stacks.Sheaves.ToposPullback.restrictionModuleIso`, whose underlying maps are the given
comparison and the identity by `Eq.refl`), an associator, and the three-fold cancellation of
restrictions of scalars. The fifth is
`Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso`,
which is a comparison of two left adjoints of the same functor and is therefore pinned down by
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`: on underlying sheaves of sets the unit
of the second adjunction is the identity, so the factor inverts the unit of the first. Those two
observations are the whole content, and they are separated into the two statements above because
only the first needs the adjunction and only the second needs the shape of the comparison.

*Why the second statement is stated at an abstract second factor.* Elaborating the value of the
comparison at the concrete component morphism of ringed topoi asks the elaborator to identify the
underlying sheaf of a restriction of scalars of an inverse image of modules with an inverse image
of sheaves of sets, and although that identification holds by `Eq.refl` it exhausts the recursion
depth at concrete morphisms. Taking the second factor as a variable leaves nothing to unfold, and
the concrete instance is then obtained by unification.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]

omit [Y.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The unit of the change-of-rings adjunction of Stacks 03CZ followed by the identification of
extension of scalars with restriction of scalars along the inverse, read on underlying sheaves of
sets, is the identity.

The identification is a comparison of two left adjoints of restriction of scalars along the
structure map, so `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` replaces the composite
by the unit of the second adjunction, which is the cancellation of two restrictions of scalars
and so the identity on underlying sheaves of sets. -/
private theorem moduleSheafFunctor_map_fSharpAdjunction_unit_comp_extendScalarsFSharpIso
    (N : SheafOfModules.{u}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((fSharpAdjunction f).unit.app N ≫
          (SheafOfModules.restrictScalars
              (commRingSheafMap X.J (fSharpCommRing f.toModulesHom)
                (inverseImageRingSheaf f.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)).map
            (f.toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso.hom.app N)) = 𝟙 _ := by
  refine Eq.trans (congrArg (fun k => (Sheaf.moduleSheafFunctor
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map k)
    (Adjunction.unit_leftAdjointUniq_hom_app _ _ N)) ?_
  rfl

/-- **The non-identity factor of a comparison of the pullback of modules inverts the unit of
Stacks 03CZ.** For a morphism of ringed topoi with invertible structure map, the comparison of
`AlgebraicGeometry.RingedToposHom.pullbackUnitUnderlyingIso` followed by the underlying morphism
of `extendScalarsFSharpIsoRestrictScalarsOfIsIso` is the identity. -/
theorem pullbackUnitUnderlyingIso_hom_comp_extendScalarsFSharpIso
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    (pullbackUnitUnderlyingIso f).hom.app M ≫
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
          (f.toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso.hom.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M)) = 𝟙 _ := by
  refine Eq.trans (congrArg
    (fun q => (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
      ((fSharpAdjunction f).unit.app
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M)) ≫ q)
    (moduleSheafFunctor_map_restrictScalars_map
      (commRingSheafMap X.J (fSharpCommRing f.toModulesHom)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
      (f.toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso.hom.app
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M))).symm) ?_
  refine Eq.trans ?_
    (f.moduleSheafFunctor_map_fSharpAdjunction_unit_comp_extendScalarsFSharpIso _)
  exact ((Sheaf.moduleSheafFunctor
    (inverseImageRingSheaf f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map_comp _ _).symm

/-- The inverse of the comparison identifying the underlying sheaf of a pullback of modules with
an inverse image is the whiskered unit of Stacks 03CZ: the other factor of that comparison is
`Stacks.Sheaves.RingedToposModules.inverseImageModuleSheafIso`, which is the
identity in each component. -/
theorem pullbackUnderlyingIsoOfIsIso_inv_app
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    (pullbackUnderlyingIsoOfIsIso f).inv.app M = (pullbackUnitUnderlyingIso f).hom.app M :=
  Category.id_comp _

/-- **The underlying morphism of a comparison of the pullback of modules.** Let the comparison be
presented as the identification of extension of scalars with restriction of scalars along the
inverse of the structure map, whiskered onto the inverse image of modules, followed by a
comparison `Ψ` of that composite with some functor. Then, read through
`AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso`, its underlying morphism of
sheaves of sets is the underlying morphism of `Ψ`.

The first factor cancels the unit of Stacks 03CZ by
`pullbackUnitUnderlyingIso_hom_comp_extendScalarsFSharpIso`, and restriction of scalars does not
change the underlying sheaf of a morphism, so only `Ψ` survives. -/
theorem pullbackUnderlyingIsoOfIsIso_inv_comp_isoWhiskerLeft
    {R : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))}
    (Ψ : inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
        SheafOfModules.restrictScalars
          (asIso f.toModulesHom.fSharpInverseImage).inv ≅ R)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    (pullbackUnderlyingIsoOfIsIso f).inv.app M ≫
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
          ((Functor.isoWhiskerLeft (inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              f.toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso ≪≫ Ψ).hom.app M) =
      (inverseImageModuleSheafIso f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).inv.app M ≫
        (Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map (Ψ.hom.app M) := by
  refine Eq.trans (congrArg
    (fun q => q ≫ (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
      ((Functor.isoWhiskerLeft (inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        f.toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso ≪≫ Ψ).hom.app M))
    (f.pullbackUnderlyingIsoOfIsIso_inv_app M)) ?_
  refine Eq.trans (congrArg (fun q => (pullbackUnitUnderlyingIso f).hom.app M ≫ q)
    ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map_comp
      (f.toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso.hom.app
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M))
      (Ψ.hom.app M))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun q => q ≫ (Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
    (Ψ.hom.app M)) (f.pullbackUnitUnderlyingIso_hom_comp_extendScalarsFSharpIso M)

end AlgebraicGeometry.RingedToposHom

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  (n : SimplexCategory)

/-- **Stacks 0D72 on underlying sheaves of sets is Stacks 09WG.** Read through the identification
of the underlying sheaf of a pullback of modules with an inverse image, the comparison of
Stacks 0D72 between the pullback of sheaves of modules along the component morphism of ringed
topoi and the literal restriction to the component is the comparison of Stacks 09WG between the
inverse image of sheaves of sets and restriction along the component inclusion. -/
@[stacks 0D72 "the comparison of the two presentations of restriction, on underlying sheaves of
sets"]
theorem componentPullbackModulesRestrictionIso_underlying
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    (AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso
          (componentRingedToposHom S O n)).inv.app M ≫
        (Sheaf.moduleSheafFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)).map
          ((componentPullbackModulesRestrictionIso S O n).hom.app M) =
      (componentRingedTopos_setRestrictionIso S n).hom.app
        (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M) := by
  refine Eq.trans
    ((componentRingedToposHom S O
      n).pullbackUnderlyingIsoOfIsIso_inv_comp_isoWhiskerLeft _ M) ?_
  rfl

end CategoryTheory.SimplicialSiteSituation

end
