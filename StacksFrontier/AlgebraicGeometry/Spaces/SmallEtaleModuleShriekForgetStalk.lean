module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleExtensionByZeroForget

/-!
# Extension by zero of modules and of abelian sheaves have the same stalks

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`.  Tag 0798 says that
the abelian sheaf underlying the extension by zero of a sheaf of `𝒪_X`-modules is the extension
by zero of the underlying abelian sheaf; the comparison is
`Stacks.SheafOfModules.lowerShriekForgetComparison` and it is invertible here by
`AlgebraicGeometry.Space.isIso_etaleLowerShriekForgetComparison`.  This file names that
isomorphism in the spellings this development uses, records that it carries the counit of the
module extension-by-zero adjunction to the counit of the abelian one, and draws the three
consequences used to compute the stalks of a Mayer–Vietoris sequence of modules: a stalk of a
counit, a stalk of an extension by zero, and a stalk of an extension by zero of a map are
invertible, respectively zero, exactly when their abelian counterparts are.

## Main definitions

* `AlgebraicGeometry.Space.etaleModuleShriekForgetIso`: **Tag 0798** for an étale morphism of
  algebraic spaces, as an isomorphism of functors.

## Main results

* `AlgebraicGeometry.Space.etaleModuleShriekForgetIso_hom_app_comp_counit`: it carries the
  forgotten counit of the module adjunction to the counit of the abelian one.
* `AlgebraicGeometry.Space.isIso_sheafFiber_toSheaf_etaleModuleCounit`,
  `AlgebraicGeometry.Space.isZero_sheafFiber_toSheaf_etaleModuleShriek` and
  `AlgebraicGeometry.Space.isIso_sheafFiber_toSheaf_etaleModuleShriek_map`: the three transports
  of a stalk statement from the abelian side to the module side.

## Implementation notes

No transport along a uniqueness-of-left-adjoints isomorphism is needed, and none is used: the
four identifications that could have required one hold *by definition* in this development, as
one checks by `rfl`.  Writing `u` for postcomposition with `f` on small étale charts and `O_Y`
for the structure sheaf of rings of `Y`:

* the restriction of `O_Y` along `u` is the structure sheaf of rings of `X`, so the structure
  morphism of rings of Tag 0797 is the identity that
  `AlgebraicGeometry.Space.etaleModulePullback` uses;
* `AlgebraicGeometry.Space.etaleModulePullback` is `SheafOfModules.pushforward` of it;
* hence `AlgebraicGeometry.Space.etaleModuleLowerShriek` is `SheafOfModules.pullback` of it and
  `AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction` is
  `SheafOfModules.pullbackPushforwardAdjunction`, both functors being *the* chosen left adjoint
  of one and the same functor and `CategoryTheory.Functor.IsRightAdjoint` being a proposition;
* `AlgebraicGeometry.Space.abelianEtaleExtensionByZero` and
  `AlgebraicGeometry.Space.abelianEtaleExtensionByZeroAdjunction` are
  `CategoryTheory.Functor.sheafPullback` and
  `CategoryTheory.Functor.sheafAdjunctionContinuous` along `u`.

## References

* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-- The comparison of Tag 0798 for an étale morphism of algebraic spaces, as an isomorphism, in
the spellings that `Stacks.SheafOfModules.lowerShriekForgetComparison` itself carries. -/
def etaleModuleShriekForgetIsoRaw :=
  asIso (Stacks.SheafOfModules.lowerShriekForgetComparison.{u, u}
    (smallEtalePostcomp B S hS f hf)
    (Stacks.SheafOfModules.structureMap (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1) (smallEtalePostcomp B S hS f hf)
      (etaleRingSheaf B S hS Y)))

/-- **Tag 0798 for an étale morphism of algebraic spaces.**  The abelian sheaf underlying the
extension by zero of a sheaf of `𝒪_X`-modules is the extension by zero of the abelian sheaf
underlying it.

This is `AlgebraicGeometry.Space.etaleModuleShriekForgetIsoRaw` repackaged: the two isomorphisms
have the same components, and only the spelling of the functors differs.  The repackaging is
what makes the structure sheaf of rings of `X` appear as
`AlgebraicGeometry.Space.etaleRingSheaf` rather than as the restriction along postcomposition of
that of `Y`, and the module categories appear as `AlgebraicGeometry.Space.Modules`; without it
every rewrite below is rejected for being type-incorrect at the transparency rewriting uses. -/
@[stacks 0798 "extension by zero of modules and of abelian sheaves, for an étale morphism"]
def etaleModuleShriekForgetIso :
    SheafOfModules.toSheaf (etaleRingSheaf B S hS X) ⋙
        abelianEtaleExtensionByZero B S hS f hf ≅
      etaleModuleLowerShriek B S hS f hf ⋙
        SheafOfModules.toSheaf (etaleRingSheaf B S hS Y) where
  hom := (etaleModuleShriekForgetIsoRaw B S hS f hf).hom
  inv := (etaleModuleShriekForgetIsoRaw B S hS f hf).inv
  hom_inv_id := (etaleModuleShriekForgetIsoRaw B S hS f hf).hom_inv_id
  inv_hom_id := (etaleModuleShriekForgetIsoRaw B S hS f hf).inv_hom_id

/-- The isomorphism of Tag 0798 is the comparison transformation. -/
theorem etaleModuleShriekForgetIso_hom :
    (etaleModuleShriekForgetIso B S hS f hf).hom =
      Stacks.SheafOfModules.lowerShriekForgetComparison.{u, u}
        (smallEtalePostcomp B S hS f hf)
        (Stacks.SheafOfModules.structureMap (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1) (smallEtalePostcomp B S hS f hf)
          (etaleRingSheaf B S hS Y)) :=
  rfl

/-- **The comparison of Tag 0798 carries the forgotten counit of the module extension-by-zero
adjunction to the counit of the abelian one.** -/
@[stacks 0798 "the comparison on counits, for an étale morphism"]
theorem etaleModuleShriekForgetIso_hom_app_comp_counit
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    (etaleModuleShriekForgetIso B S hS f hf).hom.app
          ((etaleModulePullback.{u, u} B S hS f hf).obj N) ≫
        (SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
          ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app N) =
      (abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj N) := by
  rw [etaleModuleShriekForgetIso_hom]
  exact Stacks.SheafOfModules.lowerShriekForgetComparison_app_comp_counit.{u, u}
    (smallEtalePostcomp B S hS f hf)
    (Stacks.SheafOfModules.structureMap (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1) (smallEtalePostcomp B S hS f hf)
      (etaleRingSheaf B S hS Y)) N

variable (x : GeometricPoint B S hS Y.1)

/-- The stalk of a component of the isomorphism of Tag 0798 is invertible. -/
private theorem isIso_sheafFiber_map_etaleModuleShriekForgetIso_hom_app
    (x : GeometricPoint B S hS Y.1) (M : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((etaleModuleShriekForgetIso B S hS f hf).hom.app M)) :=
  Iso.isIso_hom (((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber
    (A := AddCommGrpCat.{u})).mapIso ((etaleModuleShriekForgetIso B S hS f hf).app M))

/-- **The stalk of the counit of the module extension-by-zero adjunction is invertible exactly
when the stalk of the abelian one is.** -/
theorem isIso_sheafFiber_toSheaf_etaleModuleCounit (N : Modules.{u, u} B S hS Y.1 Y.2)
    (h : IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj N)))) :
    IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
        ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app N))) := by
  have hcmpiso : IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((etaleModuleShriekForgetIso B S hS f hf).hom.app
        ((etaleModulePullback.{u, u} B S hS f hf).obj N))) :=
    isIso_sheafFiber_map_etaleModuleShriekForgetIso_hom_app B S hS f hf x _
  have hc := congrArg
    ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber (A := AddCommGrpCat.{u})).map
    (etaleModuleShriekForgetIso_hom_app_comp_counit B S hS f hf N)
  rw [Functor.map_comp] at hc
  have hcomp : IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
        ((etaleModuleShriekForgetIso B S hS f hf).hom.app
          ((etaleModulePullback.{u, u} B S hS f hf).obj N)) ≫
      (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
          ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app N))) := by
    rw [hc]
    exact h
  exact IsIso.of_isIso_comp_left
    ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((etaleModuleShriekForgetIso B S hS f hf).hom.app
        ((etaleModulePullback.{u, u} B S hS f hf).obj N)))
    ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
        ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app N)))

/-- **The stalk of the extension by zero of modules vanishes exactly when the stalk of the
abelian extension by zero does.** -/
theorem isZero_sheafFiber_toSheaf_etaleModuleShriek (M : Modules.{u, u} B S hS X.1 X.2)
    (h : IsZero ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.obj
      ((abelianEtaleExtensionByZero B S hS f hf).obj
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj M)))) :
    IsZero ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.obj
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj
        ((etaleModuleLowerShriek B S hS f hf).obj M))) :=
  IsZero.of_iso h
    (((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber (A := AddCommGrpCat.{u})).mapIso
      ((etaleModuleShriekForgetIso B S hS f hf).app M)).symm

/-- **The stalk of the extension by zero of a map of modules is invertible exactly when the
stalk of the abelian extension by zero of the underlying map is.** -/
theorem isIso_sheafFiber_toSheaf_etaleModuleShriek_map
    {M M' : Modules.{u, u} B S hS X.1 X.2} (α : M ⟶ M')
    (h : IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((abelianEtaleExtensionByZero B S hS f hf).map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map α)))) :
    IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
        ((etaleModuleLowerShriek B S hS f hf).map α))) := by
  have := h
  have hM : IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((etaleModuleShriekForgetIso B S hS f hf).hom.app M)) :=
    isIso_sheafFiber_map_etaleModuleShriekForgetIso_hom_app B S hS f hf x _
  have hM' : IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((etaleModuleShriekForgetIso B S hS f hf).hom.app M')) :=
    isIso_sheafFiber_map_etaleModuleShriekForgetIso_hom_app B S hS f hf x _
  have hnat0 : (abelianEtaleExtensionByZero B S hS f hf).map
          ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map α) ≫
        (etaleModuleShriekForgetIso B S hS f hf).hom.app M' =
      (etaleModuleShriekForgetIso B S hS f hf).hom.app M ≫
        (SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
          ((etaleModuleLowerShriek B S hS f hf).map α) :=
    (etaleModuleShriekForgetIso B S hS f hf).hom.naturality α
  have hnat : (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
          ((abelianEtaleExtensionByZero B S hS f hf).map
            ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map α)) ≫
        (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
          ((etaleModuleShriekForgetIso B S hS f hf).hom.app M') =
      (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
          ((etaleModuleShriekForgetIso B S hS f hf).hom.app M) ≫
        (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
          ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
            ((etaleModuleLowerShriek B S hS f hf).map α)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hnat0]
  exact IsIso.of_isIso_fac_left hnat.symm

end AlgebraicGeometry.Space

end
