module

public import StacksFrontier.AlgebraicGeometry.Spaces.RegularAlterationImpliedProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitIsoComp

/-!
# Pulling back global sections of modules on algebraic spaces

A global section of an `𝒪_Y`-module `M` on the small étale site of an algebraic space `Y` is a
morphism `s : 𝒪_Y ⟶ M`. Along a morphism `f : X ⟶ Y` its pullback is the global section
`𝒪_X ≅ f^*𝒪_Y ⟶ f^*M` of `f^*M` (`AlgebraicGeometry.Space.modulePullbackGlobalSection`), through
the identification `f^*𝒪_Y ≅ 𝒪_X` of [Stacks Project, Tag 03LU]. Pulling back sections is
compatible with composition of morphisms of modules, with the comparison `g^*f^* ≅ (g ≫ f)^*`
(Stacks 03D6), and with equalities of morphisms.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackGlobalSection`: the pullback `f^*s` of a global section.

## Main results

* `AlgebraicGeometry.Space.modulePullbackGlobalSection_comp`: `f^*(s ≫ t) = f^*s ≫ f^*t`.
* `AlgebraicGeometry.Space.modulePullbackGlobalSection_modulePullbackGlobalSection`: `g^*f^*s` is
  `(g ≫ f)^*s` through `g^*f^* ≅ (g ≫ f)^*`.
* `AlgebraicGeometry.Space.modulePullbackGlobalSection_eqToHom`: transport along `f = f'`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The pullback of a global section** `s : 𝒪_Y ⟶ M` along `f : X ⟶ Y`: the global section
`𝒪_X ≅ f^*𝒪_Y ⟶ f^*M` of `f^*M`. -/
def modulePullbackGlobalSection (f : X ⟶ Y) {M : Modules.{u, u} B S hS Y.1 Y.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ M) :
    SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ (modulePullback B S hS f).obj M :=
  (modulePullbackUnitIso B S hS f).inv ≫ (modulePullback B S hS f).map s

/-- Pulling back sections is compatible with composition with morphisms of modules. -/
theorem modulePullbackGlobalSection_comp (f : X ⟶ Y) {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ M) (t : M ⟶ N) :
    modulePullbackGlobalSection B S hS f (s ≫ t) =
      modulePullbackGlobalSection B S hS f s ≫ (modulePullback B S hS f).map t :=
  (congrArg (_ ≫ ·) ((modulePullback B S hS f).map_comp s t)).trans (Category.assoc _ _ _).symm

/-- **Pulling back sections twice** is pulling back along the composite, through the comparison
`g^*f^* ≅ (g ≫ f)^*` of Stacks 03D6. -/
theorem modulePullbackGlobalSection_modulePullbackGlobalSection (g : Z ⟶ X) (f : X ⟶ Y)
    {M : Modules.{u, u} B S hS Y.1 Y.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ M) :
    modulePullbackGlobalSection B S hS g (modulePullbackGlobalSection B S hS f s) ≫
        (modulePullbackCompIso B S hS g f).hom.app M =
      modulePullbackGlobalSection B S hS (g ≫ f) s := by
  have hc := modulePullbackCompIso_hom_app_comp_modulePullbackUnitIso_hom B S hS g f
  have hn := (modulePullbackCompIso B S hS g f).hom.naturality s
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  have key : (modulePullbackUnitIso B S hS g).inv ≫
      (modulePullback B S hS g).map (modulePullbackUnitIso B S hS f).inv ≫
        (modulePullbackCompIso B S hS g f).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS Y)) =
      (modulePullbackUnitIso B S hS (g ≫ f)).inv := by
    refine (Iso.comp_hom_eq_id _).1 ?_
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) hc))).trans ?_)
    refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
      (((modulePullback B S hS g).map_comp _ _).symm.trans ((congrArg
        (modulePullback B S hS g).map (Iso.inv_hom_id _)).trans
        ((modulePullback B S hS g).map_id _)))))).trans ?_
    exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Iso.inv_hom_id _)
  have e1 : modulePullbackGlobalSection B S hS g (modulePullbackGlobalSection B S hS f s) =
      (modulePullbackUnitIso B S hS g).inv ≫
        (modulePullback B S hS g).map (modulePullbackUnitIso B S hS f).inv ≫
          (modulePullback B S hS g).map ((modulePullback B S hS f).map s) :=
    congrArg (_ ≫ ·) ((modulePullback B S hS g).map_comp _ _)
  refine (congrArg (· ≫ _) e1).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) hn))).trans ?_)
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) key)

/-- Pulling back sections along equal morphisms, read through the identification of the
pullback functors. -/
theorem modulePullbackGlobalSection_eqToHom {f f' : X ⟶ Y} (h : f = f')
    {M : Modules.{u, u} B S hS Y.1 Y.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ M) :
    modulePullbackGlobalSection B S hS f s ≫
        (eqToHom (congrArg (fun f => modulePullback B S hS f) h)).app M =
      modulePullbackGlobalSection B S hS f' s := by
  subst h
  exact Category.comp_id _

end AlgebraicGeometry.Space

end
