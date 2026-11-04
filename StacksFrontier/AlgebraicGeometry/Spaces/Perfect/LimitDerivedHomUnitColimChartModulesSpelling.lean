module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimChartModuleBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimPushCocyclePullback

/-!
# The cocycle for the chart comparison of direct images, in the category of modules

`AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle` is the
composition law for `AlgebraicGeometry.Space.spacesEtaleModelChartModulesPushforwardIso` read
through the functor of underlying sheaves of sets, with each of its five factors the image of a
morphism of `𝒪`-modules.  **This file carries it back to the category of modules**, which is the
hypothesis `hchart` of
`AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso_cocycle_of_chart` and of
`AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom_comp_of_chart`, and so makes both of
those unconditional.

## Main results

* `AlgebraicGeometry.Space.comp_eq_of_moduleSheafFunctor_map_comp_eq`: **a two-factor composite
  of morphisms of `𝒪`-modules equals a three-factor one as soon as the composites of the images
  of the factors under the sheaf-of-sets functor agree.**
* `AlgebraicGeometry.Space.spacesEtaleModelChartModulesPushforwardIso_cocycle`: **the composition
  law for the chart comparison of the direct images of `𝒪`-modules**, the hypothesis `hchart`.
* `AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso_cocycle` and
  `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom_cocycle`: the composition laws for
  the comparisons of Stacks 03G1, with no hypothesis left.

## Implementation notes

**Why the passage back to the module spelling is taken at plain variables.**  A morphism of
`𝒪_Z`-modules is written here in two ways that agree only definitionally: the category
`AlgebraicGeometry.Space.Modules B S hS Z.1 Z.2`, which is where the functors
`AlgebraicGeometry.Space.spacesEtaleModelChartModules` and
`AlgebraicGeometry.Space.modulePushforward` land, indexes its site by the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, while
`CategoryTheory.SheafOfModules (AlgebraicGeometry.Space.structureRingSheaf B S hS Z)`, which is
the domain of `CategoryTheory.Sheaf.moduleSheafFunctor`, indexes it by
`AlgebraicGeometry.Space.SmallEtale` and `AlgebraicGeometry.Space.SmallEtale.topology`.  At the
level of objects the two are interchangeable for nothing; at the level of a *composite* they are
not, because `CategoryTheory.CategoryStruct.comp` reduces on both sides and the recursion runs
into the transports of `AlgebraicGeometry.Space.modulePushforwardCompIso`.

So no composite of the cocycle's concrete morphisms is ever formed under the sheaf-of-sets
functor.  The two applications of `CategoryTheory.Functor.map_comp` that fold the five images
into two, and the appeal to faithfulness
(`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor`) that brings the result back to
the category of modules, are all taken in `comp_eq_of_moduleSheafFunctor_map_comp_eq` with the
five morphisms variables; that is then matched against the cocycle, whose own composites are in
the module spelling throughout.  The same fold performed on the cocycle's morphisms
themselves costs more than 200,000 heartbeats, in either spelling and whether the folded equation
is reached from
`AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_comp` or built
up from the five-factor form one `CategoryTheory.Functor.map_comp` at a time, and so does
`AlgebraicGeometry.Space.comp_eq_of_moduleSheafFunctor_sections` supplied the cocycle on a
section.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **Two composites of morphisms of `𝒪`-modules, one of two factors and one of three, agree as
soon as the composites of the images of their factors under the sheaf-of-sets functor agree.**

The two foldings `CategoryTheory.Functor.map_comp` and the faithfulness of
`CategoryTheory.Sheaf.moduleSheafFunctor` are both taken here, at the five morphisms variables.
That is the whole content of the statement: performed on the morphisms of the cocycle below
instead, in either spelling of the category of modules, each of them costs the whole heartbeat
budget — see this file's implementation notes. -/
theorem comp_eq_of_moduleSheafFunctor_map_comp_eq (W : AlgebraicSpaces B S hS)
    {M N P Q R : Modules.{u, u} B S hS W.1 W.2} (a : M ⟶ N) (b : N ⟶ P) (c : M ⟶ Q) (d : Q ⟶ R)
    (e : R ⟶ P)
    (h : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map a ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map b =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map c ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map d ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map e) :
    a ≫ b = c ≫ d ≫ e :=
  Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
    (R := structureRingSheaf B S hS W) (α := a ≫ b) (β := c ≫ d ≫ e)
    ((Functor.map_comp _ _ _).trans (h.trans
      ((congrArg (fun t ↦ (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map c ≫ t)
        (Functor.map_comp _ _ _).symm).trans (Functor.map_comp _ _ _).symm)))

/-- **The composition law for the chart comparison of the direct images of `𝒪`-modules, on a
single module.**  This is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle` read back in
the category of `𝒪_Z`-modules. -/
theorem spacesEtaleModelChartModulesPushforwardIso_cocycle_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (spacesEtaleModelChartModules B S hS Z).map
          ((spacesEtaleModelPushforwardComp B S hS f g).hom.app M) ≫
        (spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g)).hom.app M =
      (spacesEtaleModelChartModulesPushforwardIso B S hS g).hom.app
          ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M) ≫
        (modulePushforward B S hS g).map
            ((spacesEtaleModelChartModulesPushforwardIso B S hS f).hom.app M) ≫
          (modulePushforwardCompIso B S hS f g).hom.app
            ((spacesEtaleModelChartModules B S hS X).obj M) :=
  comp_eq_of_moduleSheafFunctor_map_comp_eq B S hS Z _ _ _ _ _
    (moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle B S hS f g M)

/-- **The chart comparison of the direct images of `𝒪`-modules is compatible with composition.**

Both sides are natural transformations of functors out of the modules on the spaces-étale model
of `X`, so the claim is the one above for every module; the whiskerings and the composition of
isomorphisms are expanded by `CategoryTheory.Iso.ext`, `CategoryTheory.NatTrans.ext` and
`funext`. -/
theorem spacesEtaleModelChartModulesPushforwardIso_cocycle (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.isoWhiskerRight (spacesEtaleModelPushforwardComp B S hS f g)
          (spacesEtaleModelChartModules B S hS Z) ≪≫
        spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g) =
      Functor.isoWhiskerLeft (spacesEtaleModelHom B S hS f).pushforwardTopos
          (spacesEtaleModelChartModulesPushforwardIso B S hS g) ≪≫
        Functor.isoWhiskerRight (spacesEtaleModelChartModulesPushforwardIso B S hS f)
          (modulePushforward B S hS g) ≪≫
        Functor.isoWhiskerLeft (spacesEtaleModelChartModules B S hS X)
          (modulePushforwardCompIso B S hS f g) :=
  Iso.ext (NatTrans.ext
    (funext fun M ↦ spacesEtaleModelChartModulesPushforwardIso_cocycle_app B S hS f g M))

/-- **The comparison of the direct images of `𝒪`-modules of Stacks 03G1 is compatible with
composition.**  `AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso_cocycle_of_chart`
with its hypothesis discharged. -/
theorem spacesEtaleModelModulesPushforwardIso_cocycle (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.isoWhiskerRight (spacesEtaleModelPushforwardComp B S hS f g)
          (spacesEtaleModelModulesEquiv B S hS Z).functor ≪≫
        spacesEtaleModelModulesPushforwardIso B S hS (f ≫ g) =
      Functor.isoWhiskerLeft (spacesEtaleModelHom B S hS f).pushforwardTopos
          (spacesEtaleModelModulesPushforwardIso B S hS g) ≪≫
        Functor.isoWhiskerRight (spacesEtaleModelModulesPushforwardIso B S hS f)
          (modulePushforward B S hS g) ≪≫
        Functor.isoWhiskerLeft (spacesEtaleModelModulesEquiv B S hS X).functor
          (modulePushforwardCompIso B S hS f g) :=
  spacesEtaleModelModulesPushforwardIso_cocycle_of_chart B S hS f g
    (spacesEtaleModelChartModulesPushforwardIso_cocycle B S hS f g)

/-- **The comparison of the inverse images of `𝒪`-modules of Stacks 03G1 is compatible with
composition.**  `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom_comp_of_chart` with
its hypothesis discharged. -/
theorem spacesEtaleModelModulesPullbackHom_cocycle (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerLeft (spacesEtaleModelModulesEquiv B S hS Z).functor
          (Adjunction.leftAdjointCompIso (smallEtaleModulePullbackModulesAdjunction B S hS g)
            (smallEtaleModulePullbackModulesAdjunction B S hS f)
            (smallEtaleModulePullbackModulesAdjunction B S hS (f ≫ g))
            (modulePushforwardCompIso B S hS f g)).hom ≫
        spacesEtaleModelModulesPullbackHom B S hS (f ≫ g) =
      Functor.whiskerRight (spacesEtaleModelModulesPullbackHom B S hS g)
          (smallEtaleModulePullbackModules B S hS f) ≫
        Functor.whiskerLeft (spacesEtaleModelHom B S hS g).pullbackTopos
          (spacesEtaleModelModulesPullbackHom B S hS f) ≫
        Functor.whiskerRight (spacesEtaleModelPullbackComp B S hS f g).hom
          (spacesEtaleModelModulesEquiv B S hS X).functor :=
  spacesEtaleModelModulesPullbackHom_comp_of_chart B S hS f g
    (spacesEtaleModelChartModulesPushforwardIso_cocycle B S hS f g)

end AlgebraicGeometry.Space

end
