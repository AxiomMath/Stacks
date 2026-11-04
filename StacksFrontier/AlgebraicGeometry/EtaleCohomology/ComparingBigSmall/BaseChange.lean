module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Support.CartesianBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite

/-!
# Base change for derived direct images on big étale sites

For a Cartesian base-change square of schemes in a big étale site, restriction of the derived
direct image of a complex of abelian sheaves to the new base agrees naturally with the derived
direct image of its restriction to the new source.

The comparison is obtained from the corresponding statement for a localized site: the big étale
category over an object `U` is the localization of the site at `U`, so its topology is
`B.topology.over U` and the general base-change isomorphism for localized sites applies.

## Main definitions

* `AlgebraicGeometry.derivedBaseChangeOfLocalizedSite` is the base-change isomorphism for four
  topologies presented as localizations of one site at the corners of a Cartesian square.
* `AlgebraicGeometry.bigEtaleOver_topology_eq_of_obj` identifies the topology of the big étale
  category over an object of the site with the localization of the site's topology there.

## Main results

* `AlgebraicGeometry.bigEtaleDerivedPushforwardBaseChangeIso` is the natural base-change
  isomorphism on the big étale site.

## Implementation notes

The equality asserted in the source is represented by a natural isomorphism of derived
functors. The four derived functors are arbitrary choices with their right-derived universal
properties rather than a fixed construction, which also records the canonicality of the
comparison: any two choices give the same isomorphism up to the derived-functor comparison maps.

## References

* [Stacks Project, Tag 075A](https://stacks.math.columbia.edu/tag/075A)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Stacks.Cohomology.Localization

universe u v wT wS wT' wS'

namespace AlgebraicGeometry

/-- The topology of the big étale category over an object of the site, in the destructured form
in which the base-change square presents its corners: for `U` an object of the site, the
topology over `U.obj` is the localization of the site's topology at `U`. -/
public theorem bigEtaleOver_topology_eq_of_obj (B : BigEtaleSite.{u}) (U : B.Scheme) :
    BigEtaleOver.topology B U.obj U.property = B.topology.over U := by
  cases U
  exact bigEtaleOver_topology_eq B _ _

/-- Base change for derived direct images between four localizations of one site at the corners
of a Cartesian square, given identifications of the four topologies with those localizations. -/
public noncomputable def derivedBaseChangeOfLocalizedSite
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {X' X Y' Y : C} (a : X' ⟶ X) (b : X' ⟶ Y') (c : X ⟶ Y) (d : Y' ⟶ Y)
    (h : IsPullback a b c d)
    (JX' : GrothendieckTopology (Over X')) (JX : GrothendieckTopology (Over X))
    (JY' : GrothendieckTopology (Over Y')) (JY : GrothendieckTopology (Over Y))
    (hX' : JX' = J.over X') (hX : JX = J.over X)
    (hY' : JY' = J.over Y') (hY : JY = J.over Y)
    [HasSheafify JX' Ab.{max u v}] [HasSheafify JX Ab.{max u v}]
    [HasSheafify JY' Ab.{max u v}] [HasSheafify JY Ab.{max u v}]
    [(Over.map c).IsCocontinuous JX JY]
    [(Over.map b).IsCocontinuous JX' JY']
    [(Over.map a).IsContinuous JX' JX]
    [(Over.map d).IsContinuous JY' JY]
    [((Over.map c).sheafPushforwardCocontinuous Ab.{max u v} JX JY).Additive]
    [((Over.map b).sheafPushforwardCocontinuous Ab.{max u v} JX' JY').Additive]
    [((Over.map a).sheafPushforwardContinuous Ab.{max u v} JX' JX).Additive]
    [((Over.map d).sheafPushforwardContinuous Ab.{max u v} JY' JY).Additive]
    [HasDerivedCategory.{wT'} (Sheaf JX' Ab.{max u v})]
    [HasDerivedCategory.{wT} (Sheaf JX Ab.{max u v})]
    [HasDerivedCategory.{wS'} (Sheaf JY' Ab.{max u v})]
    [HasDerivedCategory.{wS} (Sheaf JY Ab.{max u v})]
    (Rc : DerivedCategory (Sheaf JX Ab.{max u v}) ⥤
      DerivedCategory (Sheaf JY Ab.{max u v}))
    (Rb : DerivedCategory (Sheaf JX' Ab.{max u v}) ⥤
      DerivedCategory (Sheaf JY' Ab.{max u v}))
    (Ra : DerivedCategory (Sheaf JX Ab.{max u v}) ⥤
      DerivedCategory (Sheaf JX' Ab.{max u v}))
    (Rd : DerivedCategory (Sheaf JY Ab.{max u v}) ⥤
      DerivedCategory (Sheaf JY' Ab.{max u v}))
    (αc : homotopyToDerived
      ((Over.map c).sheafPushforwardCocontinuous Ab.{max u v} JX JY) ⟶
        DerivedCategory.Qh ⋙ Rc)
    (αb : homotopyToDerived
      ((Over.map b).sheafPushforwardCocontinuous Ab.{max u v} JX' JY') ⟶
        DerivedCategory.Qh ⋙ Rb)
    (αa : homotopyToDerived
      ((Over.map a).sheafPushforwardContinuous Ab.{max u v} JX' JX) ⟶
        DerivedCategory.Qh ⋙ Ra)
    (αd : homotopyToDerived
      ((Over.map d).sheafPushforwardContinuous Ab.{max u v} JY' JY) ⟶
        DerivedCategory.Qh ⋙ Rd)
    [Rc.IsRightDerivedFunctor αc
      (HomotopyCategory.quasiIso (Sheaf JX Ab.{max u v}) (ComplexShape.up ℤ))]
    [Rb.IsRightDerivedFunctor αb
      (HomotopyCategory.quasiIso (Sheaf JX' Ab.{max u v}) (ComplexShape.up ℤ))]
    [Ra.IsRightDerivedFunctor αa
      (HomotopyCategory.quasiIso (Sheaf JX Ab.{max u v}) (ComplexShape.up ℤ))]
    [Rd.IsRightDerivedFunctor αd
      (HomotopyCategory.quasiIso (Sheaf JY Ab.{max u v}) (ComplexShape.up ℤ))] :
    Rc ⋙ Rd ≅ Ra ⋙ Rb := by
  cases hX'
  cases hX
  cases hY'
  cases hY
  exact derivedOverPushforwardBaseChangeIso J a b c d h
    Rc Rb Ra Rd αc αb αa αd

/-- Base change for the derived direct image of abelian sheaves on big étale sites. -/
@[stacks 075A "big_site_base_change_abelian"]
public noncomputable def bigEtaleDerivedPushforwardBaseChangeIso
    (D : CartesianBaseChangeSituation.{u})
    [HasSheafify (BigEtaleOver.topology D.B D.T.obj D.T.property) Ab.{u + 1}]
    [HasSheafify (BigEtaleOver.topology D.B D.S.obj D.S.property) Ab.{u + 1}]
    [HasSheafify (BigEtaleOver.topology D.B D.T'.obj D.T'.property) Ab.{u + 1}]
    [HasSheafify (BigEtaleOver.topology D.B D.S'.obj D.S'.property) Ab.{u + 1}]
    [HasDerivedCategory.{wT} (Sheaf (BigEtaleOver.topology D.B D.T.obj D.T.property) Ab.{u + 1})]
    [HasDerivedCategory.{wS} (Sheaf (BigEtaleOver.topology D.B D.S.obj D.S.property) Ab.{u + 1})]
    [HasDerivedCategory.{wT'} (Sheaf (BigEtaleOver.topology D.B D.T'.obj D.T'.property) Ab.{u + 1})]
    [HasDerivedCategory.{wS'} (Sheaf (BigEtaleOver.topology D.B D.S'.obj D.S'.property) Ab.{u + 1})]
    [(Over.map D.g.hom).IsContinuous
      (BigEtaleOver.topology D.B D.S'.obj D.S'.property)
      (BigEtaleOver.topology D.B D.S.obj D.S.property)]
    [(Over.map D.g').IsContinuous
      (BigEtaleOver.topology D.B D.T'.obj D.T'.property)
      (BigEtaleOver.topology D.B D.T.obj D.T.property)]
    [((Over.map D.f).sheafPushforwardCocontinuous Ab.{u + 1}
      (BigEtaleOver.topology D.B D.T.obj D.T.property)
      (BigEtaleOver.topology D.B D.S.obj D.S.property)).Additive]
    [((Over.map D.f').sheafPushforwardCocontinuous Ab.{u + 1}
      (BigEtaleOver.topology D.B D.T'.obj D.T'.property)
      (BigEtaleOver.topology D.B D.S'.obj D.S'.property)).Additive]
    [((Over.map D.g.hom).sheafPushforwardContinuous Ab.{u + 1}
      (BigEtaleOver.topology D.B D.S'.obj D.S'.property)
      (BigEtaleOver.topology D.B D.S.obj D.S.property)).Additive]
    [((Over.map D.g').sheafPushforwardContinuous Ab.{u + 1}
      (BigEtaleOver.topology D.B D.T'.obj D.T'.property)
      (BigEtaleOver.topology D.B D.T.obj D.T.property)).Additive]
    (Rf : DerivedCategory (Sheaf (BigEtaleOver.topology D.B D.T.obj D.T.property) Ab.{u + 1}) ⥤
      DerivedCategory (Sheaf (BigEtaleOver.topology D.B D.S.obj D.S.property) Ab.{u + 1}))
    (Rf' : DerivedCategory (Sheaf (BigEtaleOver.topology D.B D.T'.obj D.T'.property) Ab.{u + 1}) ⥤
      DerivedCategory (Sheaf (BigEtaleOver.topology D.B D.S'.obj D.S'.property) Ab.{u + 1}))
    (Rg : DerivedCategory (Sheaf (BigEtaleOver.topology D.B D.S.obj D.S.property) Ab.{u + 1}) ⥤
      DerivedCategory (Sheaf (BigEtaleOver.topology D.B D.S'.obj D.S'.property) Ab.{u + 1}))
    (Rg' : DerivedCategory (Sheaf (BigEtaleOver.topology D.B D.T.obj D.T.property) Ab.{u + 1}) ⥤
      DerivedCategory (Sheaf (BigEtaleOver.topology D.B D.T'.obj D.T'.property) Ab.{u + 1}))
    (αf : homotopyToDerived
      ((Over.map D.f).sheafPushforwardCocontinuous Ab.{u + 1}
        (BigEtaleOver.topology D.B D.T.obj D.T.property)
        (BigEtaleOver.topology D.B D.S.obj D.S.property)) ⟶ DerivedCategory.Qh ⋙ Rf)
    (αf' : homotopyToDerived
      ((Over.map D.f').sheafPushforwardCocontinuous Ab.{u + 1}
        (BigEtaleOver.topology D.B D.T'.obj D.T'.property)
        (BigEtaleOver.topology D.B D.S'.obj D.S'.property)) ⟶ DerivedCategory.Qh ⋙ Rf')
    (αg : homotopyToDerived
      ((Over.map D.g.hom).sheafPushforwardContinuous Ab.{u + 1}
        (BigEtaleOver.topology D.B D.S'.obj D.S'.property)
        (BigEtaleOver.topology D.B D.S.obj D.S.property)) ⟶ DerivedCategory.Qh ⋙ Rg)
    (αg' : homotopyToDerived
      ((Over.map D.g').sheafPushforwardContinuous Ab.{u + 1}
        (BigEtaleOver.topology D.B D.T'.obj D.T'.property)
        (BigEtaleOver.topology D.B D.T.obj D.T.property)) ⟶ DerivedCategory.Qh ⋙ Rg')
    [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Rg'.IsRightDerivedFunctor αg' (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))] :
    Rf ⋙ Rg ≅ Rg' ⋙ Rf' := by
  let h : IsPullback D.g' D.f' D.f D.g.hom := by
    apply IsPullback.of_map_of_faithful D.B.inclusion
    exact IsPullback.of_hasPullback (D.B.inclusion.map D.f) (D.B.inclusion.map D.g.hom)
  exact derivedBaseChangeOfLocalizedSite D.B.topology D.g' D.f' D.f D.g.hom h
    (BigEtaleOver.topology D.B D.T'.obj D.T'.property)
    (BigEtaleOver.topology D.B D.T.obj D.T.property)
    (BigEtaleOver.topology D.B D.S'.obj D.S'.property)
    (BigEtaleOver.topology D.B D.S.obj D.S.property)
    (bigEtaleOver_topology_eq_of_obj D.B D.T') (bigEtaleOver_topology_eq_of_obj D.B D.T)
    (bigEtaleOver_topology_eq_of_obj D.B D.S') (bigEtaleOver_topology_eq_of_obj D.B D.S)
    Rf Rf' Rg' Rg αf αf' αg' αg

end AlgebraicGeometry
