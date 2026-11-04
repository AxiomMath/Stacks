module

public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Skyscraper

/-!
# The canonical map from a module to the skyscraper of one of its stalks

For an `O_X`-module `M` on a scheme `X` and a point `x`, there is a canonical morphism of
presheaves of modules `M ⟶ skyscraperPOM x M_x` into the skyscraper at `x` with value the
stalk of `M` at `x`: over an open set containing `x` it is the germ map at `x`, and over an
open set missing `x` it is the zero map into a zero module.  This is the unit of the
stalk/skyscraper adjunction for presheaves of modules, and it is the map whose stalk at `x`
is an isomorphism — the input a skyscraper decomposition needs at each of its points.

## Main definitions

* `toSkyscraperApp` is the component over a single open set.
* `toSkyscraperPsh` assembles those components into a morphism of the underlying presheaves
  of abelian groups.
* `moduleToSkyscraperPOM` upgrades that to a morphism of presheaves of modules.  This is the
  repository's canonical constant for that morphism, and it is the unit of the stalk/skyscraper
  adjunction of `Stacks.SheafOfModules.moduleStalkSkyscraperHomEquiv`.

## Main results

* `toSkyscraperApp_leg_apply` is the characterizing property: over an open set containing
  `x`, the component sends a section to its germ, read through the canonical identification
  `OXModule.skyscraperPOM_presheaf_obj_eq` of the skyscraper's value with the stalk.
* `subsingleton_skyscraperPOM_presheaf_obj`: the skyscraper's value is a subsingleton over an
  open set missing `x`.

## Implementation notes

The construction goes through `PresheafOfModules.homMk`, so the work splits into naturality
of the underlying presheaf morphism and `O_X(U)`-linearity of each component.  Naturality
holds because the transition maps of the skyscraper are the canonical identifications
(`OXModule.skyscraperPOM_presheaf_map_eq`) and the germ maps are compatible with restriction;
linearity is `PresheafOfModules.germ_smul` together with
`OXModule.skyscraperPOM_leg_smul`, which says the identification intertwines the
`O_X(U)`-action on the skyscraper with the `O_{X,x}`-action on the stalk.

Both halves are proved after applying the identification to a single element rather than as
equalities of morphisms: the module structure on the skyscraper's value is defined by a case
split on `x ∈ U`, and `rw` and `simp` cannot see through the resulting `Decidable.rec` even on
patterns that are present character for character.  Working on elements replaces those
rewrites by `Eq.trans` chains, which are checked at default transparency.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum

/-- Transporting along an equality of objects and back is the identity. -/
public theorem eqToHom_eqToHom_symm_apply {A B : AddCommGrpCat.{u}} (h : A = B) (y : B) :
    (eqToHom h) ((eqToHom h.symm) y) = y := by
  subst h
  simp

variable {X : Scheme.{u}} (M : X.Modules) (x : X)

/-- The underlying abelian group of the value of a skyscraper presheaf of modules is a
subsingleton over an open missing the point the skyscraper is concentrated at. -/
public theorem subsingleton_skyscraperPOM_presheaf_obj
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X.carrier)ᵒᵖ) (hx : x ∉ U.unop) :
    Subsingleton ((OXModule.skyscraperPOM x N).presheaf.obj U) :=
  AddCommGrpCat.isZero_iff_subsingleton.mp
    (Functor.map_isZero (forget₂ (ModuleCat _) AddCommGrpCat)
      (NormalizationQuotient.skyscraperPOM_obj_isZero_of_not_mem x N U.unop hx))

/-- The component over an open `U` of the canonical map from `M` to the skyscraper at `x` with
value the stalk `M_x`: the germ map when `x ∈ U`, and zero otherwise. -/
public def toSkyscraperApp (U : (Opens X.carrier)ᵒᵖ) :
    M.val.presheaf.obj U ⟶
      (OXModule.skyscraperPOM x (OXModule.stalk M x)).presheaf.obj U := by
  classical
  exact
    if hx : x ∈ U.unop then
      TopCat.Presheaf.germ M.val.presheaf U.unop x hx ≫
        eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x (OXModule.stalk M x) U hx).symm
    else 0

/-- Over an open containing `x`, `toSkyscraperApp` sends a section to its germ, read through
the canonical identification of the skyscraper's value with the stalk. -/
public theorem toSkyscraperApp_leg_apply (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop)
    (m : M.val.presheaf.obj U) :
    (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x (OXModule.stalk M x) U hx))
        (toSkyscraperApp M x U m) =
      TopCat.Presheaf.germ M.val.presheaf U.unop x hx m := by
  classical
  have h : toSkyscraperApp M x U =
      TopCat.Presheaf.germ M.val.presheaf U.unop x hx ≫
        eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x (OXModule.stalk M x) U hx).symm :=
    dite_eq_left hx
  have h1 : toSkyscraperApp M x U m =
      (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x (OXModule.stalk M x) U hx).symm)
        (TopCat.Presheaf.germ M.val.presheaf U.unop x hx m) :=
    (ConcreteCategory.congr_hom h m).trans (CategoryTheory.comp_apply _ _ m)
  exact (congrArg (fun z : (OXModule.skyscraperPOM x (OXModule.stalk M x)).presheaf.obj U =>
      (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x (OXModule.stalk M x) U hx)) z)
    h1).trans (eqToHom_eqToHom_symm_apply _ _)

/-- The underlying morphism of presheaves of abelian groups of the canonical map from `M` to
the skyscraper at `x` with value the stalk `M_x`. -/
public def toSkyscraperPsh :
    M.val.presheaf ⟶ (OXModule.skyscraperPOM x (OXModule.stalk M x)).presheaf where
  app U := toSkyscraperApp M x U
  naturality U V i := by
    classical
    by_cases hv : x ∈ V.unop
    · have hu : x ∈ U.unop := (leOfHom i.unop) hv
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y => ?_)
      apply (ConcreteCategory.bijective_of_isIso
        (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x
          (OXModule.stalk M x) V hv))).injective
      have hlhs : (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x
            (OXModule.stalk M x) V hv))
            ((M.val.presheaf.map i ≫ toSkyscraperApp M x V) y) =
          TopCat.Presheaf.germ M.val.presheaf U.unop x hu y := by
        rw [CategoryTheory.comp_apply]
        exact (toSkyscraperApp_leg_apply M x V hv _).trans
          (ConcreteCategory.congr_hom (TopCat.Presheaf.germ_res M.val.presheaf i.unop x hv) y)
      have hrhs : (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x
            (OXModule.stalk M x) V hv))
            ((toSkyscraperApp M x U ≫
              (OXModule.skyscraperPOM x (OXModule.stalk M x)).presheaf.map i) y) =
          TopCat.Presheaf.germ M.val.presheaf U.unop x hu y := by
        rw [CategoryTheory.comp_apply]
        refine Eq.trans (congrArg (fun z : (OXModule.skyscraperPOM x
            (OXModule.stalk M x)).presheaf.obj V =>
            (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x
              (OXModule.stalk M x) V hv)) z)
          ((ConcreteCategory.congr_hom
            (OXModule.skyscraperPOM_presheaf_map_eq x (OXModule.stalk M x) i hv)
            (toSkyscraperApp M x U y)).trans
            (CategoryTheory.comp_apply _ _ (toSkyscraperApp M x U y)))) ?_
        exact (eqToHom_eqToHom_symm_apply _ _).trans
          (toSkyscraperApp_leg_apply M x U hu y)
      exact hlhs.trans hrhs.symm
    · exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ => @Subsingleton.elim _
        (subsingleton_skyscraperPOM_presheaf_obj x (OXModule.stalk M x) V hv) _ _)

/-- The canonical map from a module to the skyscraper presheaf of modules whose value is the
stalk of the module at `x`. -/
public def moduleToSkyscraperPOM :
    M.val ⟶ OXModule.skyscraperPOM x (OXModule.stalk M x) := by
  classical
  refine PresheafOfModules.homMk (toSkyscraperPsh M x) ?_
  intro U r m
  let _ : Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
    (OXModule.stalk M x).isModule
  by_cases hx : x ∈ U.unop
  · apply (ConcreteCategory.bijective_of_isIso
      (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x (OXModule.stalk M x) U hx))).injective
    have hleg := OXModule.skyscraperPOM_leg_smul x (OXModule.stalk M x) U hx
      (r : (X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)
      ((toSkyscraperPsh M x).app U m)
    exact ((toSkyscraperApp_leg_apply M x U hx (r • m)).trans
      ((PresheafOfModules.germ_smul (R := X.presheaf) M.val x U.unop hx r m).trans
        (congrArg (fun z : ↑(TopCat.Presheaf.stalk M.val.presheaf x) =>
            (ConcreteCategory.hom (X.presheaf.germ U.unop x hx)) r • z)
          (toSkyscraperApp_leg_apply M x U hx m).symm))).trans hleg.symm
  · exact @Subsingleton.elim _
      (subsingleton_skyscraperPOM_presheaf_obj x (OXModule.stalk M x) U hx) _ _

end Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum

end
