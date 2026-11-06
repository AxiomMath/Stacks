module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLiftFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedPushforwardModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModuleComparison
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfDirectImages
public import StacksFrontier.CategoryTheory.Sites.UliftFunctorSheafification

/-!
# Direct images of `𝒪`-modules and the transport to the spaces-étale site

Let `f : Y ⟶ X` be a morphism of algebraic spaces. The direct image of `𝒪_Y`-modules on the
small étale sites, `AlgebraicGeometry.Space.modulePushforward`, and the direct image along the
morphism `f_{small}` of spaces-étale ringed topoi agree through the transport
`ι = AlgebraicGeometry.Space.toSpacesEtaleModules` of Stacks 03G1:
`ι_X ∘ f_* ≅ f_{small,*} ∘ ι_Y`.

On an étale chart `V` of `X` both sides have sections over `Y ×_X V`: the left side those of the
03G1 extension of `𝓕` at the universe of the schemes, lifted one universe, and the right side
those of `ι_Y𝓕`. The two are identified by `AlgebraicGeometry.Space.toSpacesEtaleModulesSheafIso`,
which restricted to the scheme charts of `Y` is the counit of Stacks 03G1. Since sections over
`Y ×_X V` are determined by their restrictions to the charts of `Y`, the scalar actions are
compared there, where both are the action of `𝓕`: on the left through the structure map `f♯`,
whose chart projections are pullback of functions along the induced morphisms of charts
(`AlgebraicGeometry.Space.chartProjection_structureMapApp`), and on the right through the
structure map of `f_{small}`, which is pullback of functions along the cartesian projection.

## Main definitions

* `AlgebraicGeometry.Space.toSpacesEtaleModulesSheafIso`: the sheaf of sets underlying `ι𝓕` is
  the universe lift of the 03G1 extension of the sheaf of sets underlying `𝓕`.
* `AlgebraicGeometry.BigEtaleSpaceSite.toSpacesEtaleModulesPushforwardChartIso`: the comparison
  of direct images on the scheme charts of `X`.
* `AlgebraicGeometry.BigEtaleSpaceSite.toSpacesEtaleModulesPushforwardIso`: the natural
  isomorphism `f_* ⋙ ι_X ≅ ι_Y ⋙ f_{small,*}`.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleRingedSiteHomPushforwardCompIso`: the
  composition comparison `h_{small,*} ⋙ f_{small,*} ≅ (h ≫ f)_{small,*}` of spaces-étale direct
  images, through the composition isomorphism of base change of Stacks 03G2, part (2).

## Main results

* `AlgebraicGeometry.Space.toSpacesEtaleModulesSheafIso_hom_smul` and `_hom_add`: the
  identification of underlying sheaves is compatible with the transported operations.
* `AlgebraicGeometry.BigEtaleSpaceSite.comparisonRingIso_inv_fSharpRing`: the structure map of
  `f_{small}` on scheme charts is pullback of regular functions.
* `AlgebraicGeometry.BigEtaleSpaceSite.toSpacesEtaleModulesPushforwardIso_comp_hom_app`: the
  comparison is compatible with composition: transported through `ι`, the composition comparison
  `AlgebraicGeometry.Space.modulePushforwardCompIso` of Stacks 03LU matches
  `smallEtaleRingedSiteHomPushforwardCompIso`.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf

universe u

namespace AlgebraicGeometry.Space

/-- Pasting two commutative squares, in the shape used for naturality of the comparison. -/
theorem comp_comp_eq_comp_comp_of_comm_sq {C : Type*} [Category C] {P Q R T T' V : C}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ V} {d : P ⟶ T} {g : T ⟶ R} {e : T ⟶ T'} {k : T' ⟶ V}
    (h1 : a ≫ b = d ≫ g) (h2 : g ≫ c = e ≫ k) : a ≫ b ≫ c = (d ≫ e) ≫ k := by
  rw [← Category.assoc, h1, Category.assoc, h2, Category.assoc]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section

variable (Y : AlgebraicSpaces B S hS)

/-- The sheaf of sets underlying the transport `ι𝓕` of an `𝒪_Y`-module to the spaces-étale
site is the universe lift of the extension of the underlying sheaf of `𝓕` along the comparison
of Stacks 03G1. -/
noncomputable def toSpacesEtaleModulesSheafIso (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (sheafCompose (SpacesEtale.topology B S hS Y) uliftFunctor.{u + 1, u}).obj
        ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)) ≅
      moduleSheaf.{u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O)
        ((toSpacesEtaleModules B S hS Y).obj M) :=
  ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).preimageIso
    ((sheafCompose (SmallEtale.topology B S hS Y.1) uliftFunctor.{u + 1, u}).mapIso
        ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.app
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)) ≪≫
      ((moduleSheafFunctor.{u + 1, u, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u}
              (smallEtaleRingedSite B S hS Y.1 Y.2)).O)).mapIso
        ((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M))).symm)

/-- Restricted to the scheme charts and read through the counit of the module form of
Stacks 03G1, the identification of underlying sheaves is the universe lift of the counit of
Stacks 03G1 for sheaves of sets. -/
theorem toSpacesEtaleModulesSheafIso_hom_counit (M : Modules.{u, u} B S hS Y.1 Y.2) :
    ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).map
        (toSpacesEtaleModulesSheafIso B S hS Y M).hom ≫
      (moduleSheafFunctor.{u + 1, u, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u}
              (smallEtaleRingedSite B S hS Y.1 Y.2)).O)).map
        ((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)).hom =
      (sheafCompose (SmallEtale.topology B S hS Y.1) uliftFunctor.{u + 1, u}).map
        ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.app
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).hom := by
  refine (congrArg (· ≫ _) (Functor.map_preimage _ _)).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans
    (Category.comp_id _))

/-- Restricted to the scheme charts, the identification of underlying sheaves is the universe
lift of the counit of Stacks 03G1 followed by the inverse counit of its module form. -/
theorem toSpacesEtaleModulesSheafIso_map_hom (M : Modules.{u, u} B S hS Y.1 Y.2) :
    ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).map
        (toSpacesEtaleModulesSheafIso B S hS Y M).hom =
      (sheafCompose (SmallEtale.topology B S hS Y.1) uliftFunctor.{u + 1, u}).map
          ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app
            (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)) ≫
        (moduleSheafFunctor.{u + 1, u, u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u}
                (smallEtaleRingedSite B S hS Y.1 Y.2)).O)).map
          ((comparisonModuleEquivalence B S hS Y).counitIso.inv.app
            ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
              (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)) :=
  Functor.map_preimage _ _

/-- The identification of underlying sheaves commutes with restriction of sections. -/
private theorem toSpacesEtaleModulesSheafIso_hom_map_apply (M : Modules.{u, u} B S hS Y.1 Y.2)
    {W W' : SpacesEtale B S hS Y} (c : W' ⟶ W)
    (y : ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.obj (op W)) :
    (toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W')
        (ULift.up (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.map c.op y)) =
      ((toSpacesEtaleModules B S hS Y).obj M).val.map c.op
        ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W) (ULift.up y)) :=
  ConcreteCategory.congr_hom ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.naturality c.op) _

/-- **The chart description of `ι`.** A section of the universe lift of the 03G1 extension of
`𝓕`, transported to `ι𝓕`, restricted to a scheme chart `U` and read in `𝓕(U)` through the
counit, is the 03G1 counit of the restricted section. -/
theorem toSpacesEtaleModulesSheafIso_hom_apply_restrict (M : Modules.{u, u} B S hS Y.1 Y.2)
    (U : SmallEtale B S hS Y.1) {W : SpacesEtale B S hS Y}
    (c : (comparisonFunctor B S hS Y).obj U ⟶ W)
    (y : ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.obj (op W)) :
    ((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)).hom.val.app (op U)
        (((toSpacesEtaleModules B S hS Y).obj M).val.map c.op
          ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W) (ULift.up y))) =
      ULift.up (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.app
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).hom.hom.app (op U)
        (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.map c.op y)) := by
  have h := congrArg (fun g ↦ g.hom.app (op U) (ULift.up
    (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.map c.op y)))
    (toSpacesEtaleModulesSheafIso_hom_counit B S hS Y M)
  have hn := toSpacesEtaleModulesSheafIso_hom_map_apply B S hS Y M c y
  exact (congrArg (((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)).hom.val.app (op U)) hn.symm).trans h

/-- Sections of `ι𝓕` are determined by their restrictions to the scheme charts, read in `𝓕`
through the counit. -/
theorem toSpacesEtaleModules_ext (M : Modules.{u, u} B S hS Y.1 Y.2) {W : SpacesEtale B S hS Y}
    {z₁ z₂ : ((toSpacesEtaleModules B S hS Y).obj M).val.obj (op W)}
    (h : ∀ (U : SmallEtale B S hS Y.1) (c : (comparisonFunctor B S hS Y).obj U ⟶ W),
      ((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)).hom.val.app (op U)
          (((toSpacesEtaleModules B S hS Y).obj M).val.map c.op z₁) =
        ((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)).hom.val.app (op U)
          (((toSpacesEtaleModules B S hS Y).obj M).val.map c.op z₂)) :
    z₁ = z₂ := by
  have := Functor.IsDenseSubsite.isCoverDense (SmallEtale.topology B S hS Y.1)
    (SpacesEtale.topology B S hS Y) (comparisonFunctor B S hS Y)
  refine Functor.IsCoverDense.ext (comparisonFunctor B S hS Y)
    (moduleSheaf.{u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O)
      ((toSpacesEtaleModules B S hS Y).obj M)) W (fun U c ↦ ?_)
  have hinv := fun x ↦ congrArg (fun g ↦ g.val.app (op U) x)
    ((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)).hom_inv_id
  exact ((hinv _).symm.trans (congrArg (((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)).inv.val.app (op U)) (h U c))).trans
    (hinv _)

/-- The identification of underlying sheaves is natural in the module, on sections. -/
theorem toSpacesEtaleModulesSheafIso_hom_naturality_apply {M M' : Modules.{u, u} B S hS Y.1 Y.2}
    (φ : M ⟶ M') (W : SpacesEtale B S hS Y)
    (y : ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.obj (op W)) :
    (toSpacesEtaleModulesSheafIso B S hS Y M').hom.hom.app (op W)
        (ULift.up (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map
          ((moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS Y)).map φ)).hom.app
            (op W) y)) =
      ((toSpacesEtaleModules B S hS Y).map φ).val.app (op W)
        ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W) (ULift.up y)) := by
  refine toSpacesEtaleModules_ext B S hS Y M' (fun U c ↦ ?_)
  refine (toSpacesEtaleModulesSheafIso_hom_apply_restrict B S hS Y M' U c _).trans ?_
  have hn1 := ConcreteCategory.congr_hom
    (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map
      ((moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS Y)).map φ)).hom.naturality
        c.op) y
  have hn2 := congrArg (fun g ↦ g.hom.app (op U)
      (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.map c.op y))
    ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.naturality
      ((moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS Y)).map φ))
  have hn3 := PresheafOfModules.naturality_apply ((toSpacesEtaleModules B S hS Y).map φ).val c.op
    ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W) (ULift.up y))
  have hn4 := congrArg (fun g ↦ g.val.app (op U)
      (((toSpacesEtaleModules B S hS Y).obj M).val.map c.op
        ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W) (ULift.up y))))
    ((comparisonModuleEquivalence B S hS Y).counitIso.hom.naturality
      ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite B S hS Y.1 Y.2)).map φ))
  refine ((congrArg (fun t ↦ ULift.up
      (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.app
        (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M')).hom.hom.app (op U) t))
      hn1.symm).trans (congrArg ULift.up hn2)).trans ?_
  refine Eq.trans ?_ ((hn4.symm.trans (congrArg
      (((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M')).hom.val.app (op U)) hn3)))
  exact congrArg (((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
      (smallEtaleRingedSite B S hS Y.1 Y.2)).map φ).val.app (op U))
    (toSpacesEtaleModulesSheafIso_hom_apply_restrict B S hS Y M U c y).symm

/-- A morphism out of a module restricted along the module form of Stacks 03G1 is semilinear
for the scalars of the spaces-étale structure sheaf, read through
`AlgebraicGeometry.Space.comparisonRingIso`. -/
theorem comparisonModuleEquivalence_functor_map_smul
    {A : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O)}
    {N : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u}
        (smallEtaleRingedSite B S hS Y.1 Y.2)).O)}
    (φ : (comparisonModuleEquivalence B S hS Y).functor.obj A ⟶ N) (U : SmallEtale B S hS Y.1)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O).obj.obj
      (op ((comparisonFunctor B S hS Y).obj U)))
    (z : A.val.obj (op ((comparisonFunctor B S hS Y).obj U))) :
    φ.val.app (op U) (r • z) =
      (comparisonRingIso B S hS Y).inv.hom.app (op U) r • φ.val.app (op U) z := by
  have hr : (comparisonRingIso B S hS Y).hom.hom.app (op U)
      ((comparisonRingIso B S hS Y).inv.hom.app (op U) r) = r :=
    congrArg (fun g ↦ g.hom.app (op U) r) (comparisonRingIso B S hS Y).inv_hom_id
  exact (congrArg (fun (r' : (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedSite B S hS Y).O).obj.obj
      (op ((comparisonFunctor B S hS Y).obj U))) ↦ φ.val.app (op U) (r' • z)) hr.symm).trans
    ((φ.val.app (op U)).hom.map_smul _ z)

/-- The projection of a section of the 03G1 extension of a sheaf of sets over `W` to a scheme
chart `U ⟶ W`: restriction followed by the counit of Stacks 03G1, as a natural transformation
of sections functors. -/
noncomputable def comparisonChartProjection {W : SpacesEtale B S hS Y} (U : SmallEtale B S hS Y.1)
    (c : (comparisonFunctor B S hS Y).obj U ⟶ W) :
    (smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse ⋙
        sectionsFunctor (SpacesEtale.topology B S hS Y) (op W) ⟶
      sectionsFunctor (SmallEtale.topology B S hS Y.1) (op U) :=
  Functor.whiskerLeft (smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse
      (sectionsRestrict c.op) ≫
    Functor.whiskerRight (smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom
      (sectionsFunctor (SmallEtale.topology B S hS Y.1) (op U))

/-- **The scalar action is compatible with `ι`.** A scalar of the 03G1 extension of `𝒪_Y`
acting on the 03G1 extension of `𝓕` is carried to a scalar of the spaces-étale structure sheaf
acting on `ι𝓕`, as soon as the two scalars have the same chart projections. -/
theorem toSpacesEtaleModulesSheafIso_hom_smul (M : Modules.{u, u} B S hS Y.1 Y.2)
    (W : SpacesEtale B S hS Y)
    (a : ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse ⋙
        sectionsFunctor (SpacesEtale.topology B S hS Y) (op W)).obj
          (ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y)))
    (x : ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse ⋙
        sectionsFunctor (SpacesEtale.topology B S hS Y) (op W)).obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M))
    (ρ : (sectionsFunctor (SpacesEtale.topology B S hS Y) (op W)).obj
      (ringSheaf.{u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O)))
    (hρ : ∀ (U : SmallEtale B S hS Y.1) (c : (comparisonFunctor B S hS Y).obj U ⟶ W),
      ULift.down ((comparisonRingIso B S hS Y).inv.hom.app (op U)
          ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O).obj.map
            c.op ρ)) =
        (comparisonChartProjection B S hS Y U c).app
          (ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y)) a) :
    @id ((sectionsFunctor (SpacesEtale.topology B S hS Y) (op W)).obj
          (moduleSheaf.{u + 1, u + 1, u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O)
            ((toSpacesEtaleModules B S hS Y).obj M)))
      ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W)
        (ULift.up (moduleSMulObj (structureRingSheaf B S hS Y) M
          ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse ⋙
            sectionsFunctor (SpacesEtale.topology B S hS Y) (op W)) a x))) =
      ρ • @id ((sectionsFunctor (SpacesEtale.topology B S hS Y) (op W)).obj
          (moduleSheaf.{u + 1, u + 1, u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O)
            ((toSpacesEtaleModules B S hS Y).obj M)))
        ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W) (ULift.up x)) := by
  refine toSpacesEtaleModules_ext B S hS Y M (fun U c ↦ ?_)
  refine (toSpacesEtaleModulesSheafIso_hom_apply_restrict B S hS Y M U c _).trans ?_
  have h1 := (moduleSMulObj_naturality (structureRingSheaf B S hS Y) M
    (comparisonChartProjection B S hS Y U c) a x).trans
      (sectionsFunctor_map_moduleSMulHom (structureRingSheaf B S hS Y) M (op U) _ _)
  have h2 := ((toSpacesEtaleModules B S hS Y).obj M).val.map_smul c.op ρ
    ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W) (ULift.up x))
  refine Eq.trans ?_ (congrArg (((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)).hom.val.app (op U)) h2).symm
  refine Eq.trans ?_ (comparisonModuleEquivalence_functor_map_smul B S hS Y _ U _ _).symm
  rw [toSpacesEtaleModulesSheafIso_hom_apply_restrict B S hS Y M U c x,
    ULift.ext (y := ULift.up ((comparisonChartProjection B S hS Y U c).app _ a)) (hρ U c)]
  exact congrArg ULift.up h1

/-- **The additive structure is compatible with `ι`.** -/
theorem toSpacesEtaleModulesSheafIso_hom_add (M : Modules.{u, u} B S hS Y.1 Y.2)
    (W : SpacesEtale B S hS Y)
    (x y : ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse ⋙
        sectionsFunctor (SpacesEtale.topology B S hS Y) (op W)).obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)) :
    @id ((sectionsFunctor (SpacesEtale.topology B S hS Y) (op W)).obj
          (moduleSheaf.{u + 1, u + 1, u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O)
            ((toSpacesEtaleModules B S hS Y).obj M)))
      ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W)
        (ULift.up (moduleAddObj (structureRingSheaf B S hS Y) M
          ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse ⋙
            sectionsFunctor (SpacesEtale.topology B S hS Y) (op W)) x y))) =
      @id ((sectionsFunctor (SpacesEtale.topology B S hS Y) (op W)).obj
          (moduleSheaf.{u + 1, u + 1, u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O)
            ((toSpacesEtaleModules B S hS Y).obj M)))
        ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W) (ULift.up x)) +
      @id ((sectionsFunctor (SpacesEtale.topology B S hS Y) (op W)).obj
          (moduleSheaf.{u + 1, u + 1, u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS Y).O)
            ((toSpacesEtaleModules B S hS Y).obj M)))
        ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W) (ULift.up y)) := by
  refine toSpacesEtaleModules_ext B S hS Y M (fun U c ↦ ?_)
  refine (toSpacesEtaleModulesSheafIso_hom_apply_restrict B S hS Y M U c _).trans ?_
  have h1 := (moduleAddObj_naturality (structureRingSheaf B S hS Y) M
    (comparisonChartProjection B S hS Y U c) x y).trans
      (sectionsFunctor_map_moduleAddHom (structureRingSheaf B S hS Y) M (op U) _ _)
  have h2 := (((toSpacesEtaleModules B S hS Y).obj M).val.map c.op).hom.map_add
    ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W) (ULift.up x))
    ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app (op W) (ULift.up y))
  refine Eq.trans ?_ (congrArg (((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)).hom.val.app (op U)) h2).symm
  refine Eq.trans ?_ ((((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)).hom.val.app (op U)).hom.map_add _ _).symm
  rw [toSpacesEtaleModulesSheafIso_hom_apply_restrict B S hS Y M U c x,
    toSpacesEtaleModulesSheafIso_hom_apply_restrict B S hS Y M U c y]
  exact congrArg ULift.up h1

/-- The quasi-inverse of Stacks 03G1 and the right Kan extension have the same counit, through
`AlgebraicGeometry.Space.smallEtaleComparisonRanIso`. -/
theorem smallEtaleComparisonRanIso_inv_counit
    (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    (smallEtaleComparisonRestriction B S hS Y).map
        ((smallEtaleComparisonRanIso B S hS Y).inv.app F) ≫
      (smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app F =
    ((comparisonFunctor B S hS Y).sheafAdjunctionCocontinuous (Type u)
      (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).counit.app F :=
  Adjunction.rightAdjointUniq_hom_app_counit _ _ F

end

variable {X Y : AlgebraicSpaces B S hS}

/-- The chart projections of the structure map `f♯` are pullback of regular functions along the
induced morphisms of charts. -/
theorem comparisonChartProjection_structureSharp (f : Y ⟶ X) (V : SmallEtale B S hS X.1)
    (U : SmallEtale B S hS Y.1)
    (c : (comparisonFunctor B S hS Y).obj U ⟶ chartBaseChange B S hS f V)
    (b : (structureRingSheaf B S hS X).obj.obj (op V)) :
    (comparisonChartProjection B S hS Y U c).app
        (ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y))
        ((structureSharp B S hS f).hom.app (op V) b) =
      chartPullback B S hS f V (StructuredArrow.mk c.op) b := by
  have h := congrArg (fun g ↦ g.hom.app (op U) (((comparisonFunctor B S hS Y).op.ran.obj
        (structureSetSheaf B S hS Y).obj).map c.op (structureMapApp B S hS f V b)))
    (smallEtaleComparisonRanIso_inv_counit B S hS Y (structureSetSheaf B S hS Y))
  refine Eq.trans ?_ (h.trans
    (chartProjection_structureMapApp B S hS f V (StructuredArrow.mk c.op) b))
  have hn := ConcreteCategory.congr_hom
    (((smallEtaleComparisonRanIso B S hS Y).inv.app (structureSetSheaf B S hS Y)).hom.naturality
      c.op) (structureMapApp B S hS f V b)
  exact congrArg (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app
    (structureSetSheaf B S hS Y)).hom.app (op U)) hn.symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigEtaleSpaceSite

open Space

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y : T.Spaces}

/-- Functoriality of a presheaf on opposites, for a composite of two morphisms. -/
private theorem map_op_comp_eq {C D : Type*} [Category C] [Category D] (G : Cᵒᵖ ⥤ D)
    {P Q R : C} {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ R} (h : a ≫ b = c) :
    G.map b.op ≫ G.map a.op = G.map c.op := by
  rw [← G.map_comp, ← op_comp, h]

/-- **The structure map of `f_{small}` on scheme charts.** Read through
`AlgebraicGeometry.Space.comparisonRingIso` on both sides, the structure map of the morphism of
spaces-étale ringed topoi, restricted from `Y ×_X V` to an étale chart `U` of `Y`, is pullback
of regular functions along the induced morphism of charts `U ⟶ V`. -/
theorem comparisonRingIso_inv_fSharpRing (f : Y ⟶ X)
    (V : Space.SmallEtale T.fppfSite S T.fppf_mem X.1)
    (U : Space.SmallEtale T.fppfSite S T.fppf_mem Y.1)
    (c : (comparisonFunctor T.fppfSite S T.fppf_mem Y).obj U ⟶
      chartBaseChange T.fppfSite S T.fppf_mem f V)
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u}
        (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).O).obj.obj (op V)) :
    ULift.down ((comparisonRingIso T.fppfSite S T.fppf_mem Y).inv.hom.app (op U)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedSite T.fppfSite S T.fppf_mem Y).O).obj.map c.op
        ((smallEtaleRingedSiteHom T f).fSharpRing.hom.app
          (op ((comparisonFunctor T.fppfSite S T.fppf_mem X).obj V))
          ((comparisonRingIso T.fppfSite S T.fppf_mem X).hom.hom.app (op V) b)))) =
      chartPullback T.fppfSite S T.fppf_mem f V (StructuredArrow.mk c.op) (ULift.down b) := by
  have hsp : (schemeSpaceFunctor T.fppfSite S T.fppf_mem).map
        (chartBaseChangeMap T.fppfSite S T.fppf_mem f V (StructuredArrow.mk c.op)) =
      (SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y).map c ≫
        (spacesBaseChange T.fppfSite S T.fppf_mem f).projection.app
          ((comparisonFunctor T.fppfSite S T.fppf_mem X).obj V) :=
    ObjectProperty.hom_ext _
      (yoneda_map_chartBaseChangeMap T.fppfSite S T.fppf_mem f V (StructuredArrow.mk c.op))
  have key : (globalFunctionsSchemeSpaceIso T.fppfSite S T.fppf_mem
        ((Space.SmallEtale.toOver T.fppfSite S T.fppf_mem X.1).obj V)).inv ≫
      (globalFunctionsPresheaf T.fppfSite S T.fppf_mem).map
        ((spacesBaseChange T.fppfSite S T.fppf_mem f).projection.app
          ((comparisonFunctor T.fppfSite S T.fppf_mem X).obj V)).op ≫
      (globalFunctionsPresheaf T.fppfSite S T.fppf_mem).map
        ((SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y).map c).op ≫
      (globalFunctionsSchemeSpaceIso T.fppfSite S T.fppf_mem
        ((Space.SmallEtale.toOver T.fppfSite S T.fppf_mem Y.1).obj U)).hom =
      CommRingCat.ofHom ((Scheme.Γ.map ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).map
        (chartBaseChangeMap T.fppfSite S T.fppf_mem f V
          (StructuredArrow.mk c.op))).op).hom.ulift) := by
    have e1 : (globalFunctionsPresheaf T.fppfSite S T.fppf_mem).map
          ((spacesBaseChange T.fppfSite S T.fppf_mem f).projection.app
            ((comparisonFunctor T.fppfSite S T.fppf_mem X).obj V)).op ≫
        (globalFunctionsPresheaf T.fppfSite S T.fppf_mem).map
          ((SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y).map c).op =
        (globalFunctionsPresheaf T.fppfSite S T.fppf_mem).map
          ((schemeSpaceFunctor T.fppfSite S T.fppf_mem).map
            (chartBaseChangeMap T.fppfSite S T.fppf_mem f V (StructuredArrow.mk c.op))).op :=
      map_op_comp_eq _ hsp.symm
    exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e1).trans
      (globalFunctionsSchemeSpaceIso_naturality T.fppfSite S T.fppf_mem
        (chartBaseChangeMap T.fppfSite S T.fppf_mem f V (StructuredArrow.mk c.op)))))).trans
      (Iso.inv_hom_id_assoc _ _)
  exact congrArg (fun φ ↦ ULift.down (φ.hom b)) key

/-- On underlying sheaves of sets, the comparison of direct images: the direct image along
`f_{small}` of the identification `AlgebraicGeometry.Space.toSpacesEtaleModulesSheafIso`. -/
noncomputable def toSpacesEtaleModulesPushforwardSheafIso (f : Y ⟶ X)
    (M : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Y.1 Y.2) :
    moduleSheaf.{u + 1, u, u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u}
          (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).O)
      ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).obj
          ((Space.modulePushforward T.fppfSite S T.fppf_mem f).obj M)) ≅
      moduleSheaf.{u + 1, u, u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u}
            (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).O)
      ((comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.obj
        ((smallEtaleRingedSiteHom T f).pushforwardTopos.obj
          ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Y).obj M)))  where
  hom := ((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem Y) ⋙
      (comparisonFunctor T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous (Type (u + 1))
        (Space.SmallEtale.topology T.fppfSite S T.fppf_mem X.1)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem X)).map
    (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y M).hom
  inv := ((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem Y) ⋙
      (comparisonFunctor T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous (Type (u + 1))
        (Space.SmallEtale.topology T.fppfSite S T.fppf_mem X.1)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem X)).map
    (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y M).inv
  hom_inv_id := (((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem Y) ⋙
      (comparisonFunctor T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous (Type (u + 1))
        (Space.SmallEtale.topology T.fppfSite S T.fppf_mem X.1)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem X)).mapIso
    (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y M)).hom_inv_id
  inv_hom_id := (((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem Y) ⋙
      (comparisonFunctor T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous (Type (u + 1))
        (Space.SmallEtale.topology T.fppfSite S T.fppf_mem X.1)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem X)).mapIso
    (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y M)).inv_hom_id

/-- **The comparison of direct images on scheme charts.** For an `𝒪_Y`-module `𝓕`, the universe
lift of `f_*𝓕` is the restriction to the scheme charts of `f_{small,*}(ι𝓕)`. -/
noncomputable def toSpacesEtaleModulesPushforwardChartIso (f : Y ⟶ X)
    (M : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Y.1 Y.2) :
    (Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).obj
          ((Space.modulePushforward T.fppfSite S T.fppf_mem f).obj M) ≅
      (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.obj
        ((smallEtaleRingedSiteHom T f).pushforwardTopos.obj
          ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Y).obj M)) :=
  Stacks.Sheaves.RingedToposModules.isoOfSheafIso
    (M := (Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).obj
          ((Space.modulePushforward T.fppfSite S T.fppf_mem f).obj M))
    (N := (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.obj
        ((smallEtaleRingedSiteHom T f).pushforwardTopos.obj
          ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Y).obj M)))
    (toSpacesEtaleModulesPushforwardSheafIso T f M)
    ((Stacks.Sheaves.RingedToposModules.moduleAddHom_comp_iff
      (toSpacesEtaleModulesPushforwardSheafIso T f M).hom).2 fun V x y ↦
      toSpacesEtaleModulesSheafIso_hom_add T.fppfSite S T.fppf_mem Y M
      (chartBaseChange T.fppfSite S T.fppf_mem f V.unop) (ULift.down x) (ULift.down y))
    ((Stacks.Sheaves.RingedToposModules.moduleSMulHom_comp_iff
      (toSpacesEtaleModulesPushforwardSheafIso T f M).hom).2 fun V r x ↦
      toSpacesEtaleModulesSheafIso_hom_smul T.fppfSite S T.fppf_mem Y M
      (chartBaseChange T.fppfSite S T.fppf_mem f V.unop) _ (ULift.down x) _ (fun U c ↦
        (comparisonRingIso_inv_fSharpRing T f V.unop U c r).trans
          (comparisonChartProjection_structureSharp T.fppfSite S T.fppf_mem f V.unop U c
            (ULift.down r)).symm))

/-- The comparison of direct images on scheme charts is natural in the module. -/
theorem toSpacesEtaleModulesPushforwardChartIso_hom_naturality (f : Y ⟶ X)
    {M M' : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Y.1 Y.2} (φ : M ⟶ M') :
    (Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).map
        ((Space.modulePushforward T.fppfSite S T.fppf_mem f).map φ) ≫
      (toSpacesEtaleModulesPushforwardChartIso T f M').hom =
    (toSpacesEtaleModulesPushforwardChartIso T f M).hom ≫
      (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.map
        ((smallEtaleRingedSiteHom T f).pushforwardTopos.map
          ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Y).map φ)) := by
  refine Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u}
        (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).O)) ?_
  refine Sheaf.hom_ext_sections fun V x ↦ ?_
  exact toSpacesEtaleModulesSheafIso_hom_naturality_apply T.fppfSite S T.fppf_mem Y φ
    (chartBaseChange T.fppfSite S T.fppf_mem f V.unop) (ULift.down x)

/-- **Direct images commute with `ι`.** For a morphism `f : Y ⟶ X` of algebraic spaces, the
transport `ι` of `𝒪`-modules from the small étale site to the spaces-étale site carries the
direct image `f_*` of `AlgebraicGeometry.Space.modulePushforward` to the direct image along the
morphism `f_{small}` of spaces-étale ringed topoi: `ι_X ∘ f_* ≅ f_{small,*} ∘ ι_Y`.

Its component at `𝓕` is the comparison on scheme charts
`AlgebraicGeometry.BigEtaleSpaceSite.toSpacesEtaleModulesPushforwardChartIso`, transported
through the module form of Stacks 03G1. -/
noncomputable def toSpacesEtaleModulesPushforwardIso (f : Y ⟶ X) :
    Space.modulePushforward T.fppfSite S T.fppf_mem f ⋙
        Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X ≅
      Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem Y ⋙
        (smallEtaleRingedSiteHom T f).pushforwardTopos :=
  NatIso.ofComponents
    (fun M ↦ (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).inverse.mapIso
        (toSpacesEtaleModulesPushforwardChartIso T f M) ≪≫
      ((comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).unitIso.app
        ((smallEtaleRingedSiteHom T f).pushforwardTopos.obj
          ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Y).obj M))).symm)
    (fun {M M'} φ ↦ by
      have h := congrArg (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).inverse.map
        (toSpacesEtaleModulesPushforwardChartIso_hom_naturality T f φ)
      rw [Functor.map_comp, Functor.map_comp] at h
      exact Space.comp_comp_eq_comp_comp_of_comm_sq h
        ((comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).unitIso.inv.naturality
          ((smallEtaleRingedSiteHom T f).pushforwardTopos.map
            ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Y).map φ))))

end AlgebraicGeometry.BigEtaleSpaceSite

/-! ### Compatibility with composition -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Y : AlgebraicSpaces B S hS)

/-- On a scheme chart, the identification of underlying sheaves is the universe lift of the
counit of Stacks 03G1, read through the counit of its module form. -/
theorem toSpacesEtaleModulesSheafIso_hom_apply_chart (M : Modules.{u, u} B S hS Y.1 Y.2)
    (U : SmallEtale B S hS Y.1)
    (y : ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.obj
        (op ((comparisonFunctor B S hS Y).obj U))) :
    ((comparisonModuleEquivalence B S hS Y).counitIso.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2)).obj M)).hom.val.app (op U)
        ((toSpacesEtaleModulesSheafIso B S hS Y M).hom.hom.app
          (op ((comparisonFunctor B S hS Y).obj U)) (ULift.up y)) =
      ULift.up (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.app
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).hom.hom.app (op U) y) :=
  congrArg (fun g ↦ g.hom.app (op U) (ULift.up y))
    (toSpacesEtaleModulesSheafIso_hom_counit B S hS Y M)

/-- Restricted to a scheme chart, the inverse unit of Stacks 03G1 is its counit. -/
theorem smallEtaleComparisonRestriction_unitIso_inv_restrict
    (F : Sheaf (SpacesEtale.topology B S hS Y) (Type u)) (U : SmallEtale B S hS Y.1)
    {W : SpacesEtale B S hS Y} (d : (comparisonFunctor B S hS Y).obj U ⟶ W)
    (y : ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
      ((smallEtaleComparisonRestriction B S hS Y).obj F)).obj.obj (op W)) :
    F.obj.map d.op (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.unitIso.inv.app
        F).hom.app (op W) y) =
      ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app
        ((smallEtaleComparisonRestriction B S hS Y).obj F)).hom.app (op U)
        (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          ((smallEtaleComparisonRestriction B S hS Y).obj F)).obj.map d.op y) :=
  (ConcreteCategory.congr_hom
    (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.unitIso.inv.app F).hom.naturality
      d.op) y).symm.trans
    (congrArg (fun g ↦ g.hom.app (op U)
        (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
          ((smallEtaleComparisonRestriction B S hS Y).obj F)).obj.map d.op y))
      ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counit_app_functor F)).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

/-- The composite of the two whiskered comparisons forming
`MorphismOfTopoi.transport_comp_pushforward` followed by a composition isomorphism, evaluated
on a section. -/
theorem transport_comp_pushforward_trans_hom_app_apply {E F G E' F' D : Type*} [Category E]
    [Category F] [Category G] [Category E'] [Category F'] [Category D]
    {K : GrothendieckTopology D} (eE : E ≌ E') (eF : F ≌ F') (eG : G ≌ Sheaf K (Type*))
    (φ : E ⥤ F) (ψ : F ⥤ G) (θ : E ⥤ G) (c : φ ⋙ ψ ≅ θ) (x : E') (V : Dᵒᵖ)
    (z : ((eE.inverse ⋙ φ ⋙ eF.functor) ⋙ eF.inverse ⋙ ψ ⋙ eG.functor).obj x |>.obj.obj V) :
    (((Functor.isoWhiskerLeft (eE.inverse ⋙ φ)
        (Functor.isoWhiskerRight eF.unitIso.symm (ψ ⋙ eG.functor)) ≪≫
      Functor.isoWhiskerLeft eE.inverse (Functor.isoWhiskerRight c eG.functor)).hom.app x).hom.app
        V z) =
      (eG.functor.map (c.hom.app (eE.inverse.obj x))).hom.app V
        ((eG.functor.map (ψ.map (eF.unitIso.inv.app (φ.obj (eE.inverse.obj x))))).hom.app V z) :=
  rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigEtaleSpaceSite

open Space

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y Z : T.Spaces}

/-- Restricted to the scheme charts, the comparison of direct images is the counit of the module
form of Stacks 03G1 followed by the chart comparison. -/
theorem comparisonModuleEquivalence_functor_map_toSpacesEtaleModulesPushforwardIso_hom_app
    (f : Y ⟶ X) (N : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Y.1 Y.2) :
    (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.map
        ((toSpacesEtaleModulesPushforwardIso T f).hom.app N) =
      (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).counitIso.hom.app
          ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
            (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).obj
              ((Space.modulePushforward T.fppfSite S T.fppf_mem f).obj N)) ≫
        (toSpacesEtaleModulesPushforwardChartIso T f N).hom := by
  have h1 := (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).counit_app_functor
    ((smallEtaleRingedSiteHom T f).pushforwardTopos.obj
      ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Y).obj N))
  have h2 := (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).counitIso.hom.naturality
    (toSpacesEtaleModulesPushforwardChartIso T f N).hom
  refine ((comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.map_comp _ _).trans ?_
  exact (congrArg (_ ≫ ·) h1.symm).trans h2

/-- The functor of sites underlying `f_{small} ∘ h_{small}` is continuous. -/
instance isContinuous_comp_smallEtaleRingedSiteHom_u (h : Z ⟶ Y) (f : Y ⟶ X) :
    ((smallEtaleRingedSiteHom T f).comp (smallEtaleRingedSiteHom T h)).u.IsContinuous
      (SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (SpacesEtale.topology T.fppfSite S T.fppf_mem Z) :=
  ((smallEtaleRingedSiteHom T f).comp (smallEtaleRingedSiteHom T h)).isContinuous

/-- The structure map of `(h ≫ f)_{small}`, transported along the composition isomorphism of
base change of Stacks 03G2, part (2), is the structure map of `f_{small} ∘ h_{small}`. -/
theorem fSharpRing_comp_spacesBaseChange_comp (h : Z ⟶ Y) (f : Y ⟶ X) :
    (smallEtaleRingedSiteHom T (h ≫ f)).fSharpRing ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (F := ((smallEtaleRingedSiteHom T f).comp (smallEtaleRingedSiteHom T h)).u)
          (spacesBaseChange_comp T.fppfSite S T.fppf_mem h f).hom _ _ _).app
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z).O) =
      ((smallEtaleRingedSiteHom T f).comp (smallEtaleRingedSiteHom T h)).fSharpRing := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V ↦ ?_))
  have key : (globalFunctionsPresheaf T.fppfSite S T.fppf_mem).map
        ((spacesBaseChange T.fppfSite S T.fppf_mem (h ≫ f)).projection.app V.unop).op ≫
      (globalFunctionsPresheaf T.fppfSite S T.fppf_mem).map
        ((SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Z).map
          ((spacesBaseChange_comp T.fppfSite S T.fppf_mem h f).hom.app V.unop)).op =
      (globalFunctionsPresheaf T.fppfSite S T.fppf_mem).map
          ((spacesBaseChange T.fppfSite S T.fppf_mem f).projection.app V.unop).op ≫
        (globalFunctionsPresheaf T.fppfSite S T.fppf_mem).map
          ((spacesBaseChange T.fppfSite S T.fppf_mem h).projection.app
            ((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.obj V.unop)).op := by
    refine (map_op_comp_eq _ rfl).trans (Eq.trans ?_ (map_op_comp_eq _ rfl).symm)
    exact (globalFunctionsPresheaf T.fppfSite S T.fppf_mem).congr_map
      (congrArg Quiver.Hom.op (spacesBaseChange_comp_projection T.fppfSite S T.fppf_mem h f V.unop))
  exact congrArg (forget₂ CommRingCat RingCat).map key

/-- **The composition comparison of spaces-étale direct images.** The direct images of
`𝒪`-modules along `h_{small}` and `f_{small}` compose to the direct image along
`(h ≫ f)_{small}`, through the composition isomorphism of base change of Stacks 03G2. -/
noncomputable def smallEtaleRingedSiteHomPushforwardCompIso (h : Z ⟶ Y) (f : Y ⟶ X) :
    (smallEtaleRingedSiteHom T h).pushforwardTopos ⋙
        (smallEtaleRingedSiteHom T f).pushforwardTopos ≅
      (smallEtaleRingedSiteHom T (h ≫ f)).pushforwardTopos :=
  haveI := (smallEtaleRingedSiteHom T (h ≫ f)).isContinuous
  (RingedToposSiteHom.pushforwardToposCompIso (smallEtaleRingedSiteHom T h)
      (smallEtaleRingedSiteHom T f)).symm ≪≫
    (SheafOfModules.pushforwardCongr₂ (smallEtaleRingedSiteHom T (h ≫ f)).fSharpRing
      (F := ((smallEtaleRingedSiteHom T f).comp (smallEtaleRingedSiteHom T h)).u)
      (spacesBaseChange_comp T.fppfSite S T.fppf_mem h f)
      (fSharpRing_comp_spacesBaseChange_comp T h f)).symm

/-- On a scheme chart of `Y`, the comparison of direct images for `h : Z ⟶ Y` is the counit
of Stacks 03G1, read through the identifications of underlying sheaves. -/
theorem toSpacesEtaleModulesPushforwardIso_hom_app_val_app_chart (h : Z ⟶ Y)
    (M : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Z.1 Z.2) (U : Space.SmallEtale T.fppfSite S
        T.fppf_mem Y.1)
    (t : ((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem Y).asEquivalence.inverse.obj
        (moduleSheaf.{u, u, u + 1} (structureRingSheaf T.fppfSite S T.fppf_mem Y)
        ((Space.modulePushforward T.fppfSite S T.fppf_mem h).obj
        M))).obj.obj (op ((comparisonFunctor T.fppfSite S T.fppf_mem Y).obj U))) :
    ((toSpacesEtaleModulesPushforwardIso T h).hom.app M).val.app (op ((comparisonFunctor T.fppfSite
        S T.fppf_mem Y).obj U))
        ((toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y ((Space.modulePushforward
            T.fppfSite S T.fppf_mem h).obj M)).hom.hom.app (op ((comparisonFunctor T.fppfSite S
                T.fppf_mem Y).obj U)) (ULift.up t)) =
      (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Z M).hom.hom.app (op ((spacesBaseChange
          T.fppfSite S T.fppf_mem h).functor.obj ((comparisonFunctor T.fppfSite S T.fppf_mem
          Y).obj U)))
        (ULift.up (((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem
            Y).asEquivalence.counitIso.hom.app
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf T.fppfSite S T.fppf_mem Y)
            ((Space.modulePushforward T.fppfSite S T.fppf_mem h).obj M))).hom.app (op U) t)) :=
  (congrArg (fun g ↦ g.val.app (op U) ((toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y
      ((Space.modulePushforward T.fppfSite S T.fppf_mem h).obj
      M)).hom.hom.app (op ((comparisonFunctor T.fppfSite S T.fppf_mem Y).obj U)) (ULift.up t)))
    (comparisonModuleEquivalence_functor_map_toSpacesEtaleModulesPushforwardIso_hom_app T h
        M)).trans
    (congrArg ((toSpacesEtaleModulesPushforwardChartIso T h M).hom.val.app (op U))
      (toSpacesEtaleModulesSheafIso_hom_apply_chart T.fppfSite S T.fppf_mem Y
          ((Space.modulePushforward T.fppfSite S T.fppf_mem h).obj M)
        U t))

/-- **The comparison of direct images on sections over any `W`.** Over an object `W` of the
spaces-étale site of `Y`, the comparison for `h : Z ⟶ Y` is the inverse unit of Stacks 03G1,
read through the identifications of underlying sheaves on both sides. -/
theorem toSpacesEtaleModulesPushforwardIso_hom_app_val_app (h : Z ⟶ Y)
    (M : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Z.1 Z.2)
    (W : SpacesEtale T.fppfSite S T.fppf_mem Y)
    (y : ((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem Y).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf T.fppfSite S T.fppf_mem Y)
            ((Space.modulePushforward T.fppfSite S T.fppf_mem h).obj M))).obj.obj (op W)) :
    ((toSpacesEtaleModulesPushforwardIso T h).hom.app M).val.app (op W)
        ((toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y
          ((Space.modulePushforward T.fppfSite S T.fppf_mem h).obj M)).hom.hom.app (op W)
          (ULift.up y)) =
      (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Z M).hom.hom.app
        (op ((spacesBaseChange T.fppfSite S T.fppf_mem h).functor.obj W))
        (ULift.up (((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem
            Y).asEquivalence.unitIso.inv.app
          (((spacesBaseChange T.fppfSite S T.fppf_mem h).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
            (SpacesEtale.topology T.fppfSite S T.fppf_mem Z)).obj
            ((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem Z).asEquivalence.inverse.obj
              (moduleSheaf.{u, u, u + 1} (structureRingSheaf T.fppfSite S T.fppf_mem Z)
                  M)))).hom.app
          (op W) y)) := by
  have := Functor.IsDenseSubsite.isCoverDense (Space.SmallEtale.topology T.fppfSite S T.fppf_mem
      Y.1)
    (SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (comparisonFunctor T.fppfSite S T.fppf_mem Y)
  refine Functor.IsCoverDense.ext (comparisonFunctor T.fppfSite S T.fppf_mem Y)
    (moduleSheaf.{u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite T.fppfSite S T.fppf_mem Y).O)
      ((smallEtaleRingedSiteHom T h).pushforwardTopos.obj
        ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Z).obj M))) W (fun U d ↦ ?_)
  -- left side
  have hL1 := PresheafOfModules.naturality_apply ((toSpacesEtaleModulesPushforwardIso T h).hom.app
      M).val
    d.op ((toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y
          ((Space.modulePushforward T.fppfSite S T.fppf_mem h).obj M)).hom.hom.app (op W)
          (ULift.up y))
  have hL2 := toSpacesEtaleModulesSheafIso_hom_map_apply T.fppfSite S T.fppf_mem Y
      ((Space.modulePushforward T.fppfSite S T.fppf_mem h).obj M) d y
  have hR1 := toSpacesEtaleModulesSheafIso_hom_map_apply T.fppfSite S T.fppf_mem Z M
    ((spacesBaseChange T.fppfSite S T.fppf_mem h).functor.map d)
    (((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem Y).asEquivalence.unitIso.inv.app
      (((spacesBaseChange T.fppfSite S T.fppf_mem h).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem Z)).obj
        ((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem Z).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf T.fppfSite S T.fppf_mem Z)
            M)))).hom.app (op W) y)
  refine (hL1.symm.trans ((congrArg (((toSpacesEtaleModulesPushforwardIso T h).hom.app M).val.app
      (op ((comparisonFunctor T.fppfSite S T.fppf_mem Y).obj U))) hL2.symm).trans
    ((toSpacesEtaleModulesPushforwardIso_hom_app_val_app_chart T h M U _).trans ?_))).trans hR1
  exact congrArg (fun t ↦ (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Z M).hom.hom.app (op
      ((spacesBaseChange T.fppfSite S T.fppf_mem h).functor.obj ((comparisonFunctor T.fppfSite S
      T.fppf_mem Y).obj U))) (ULift.up t))
    (smallEtaleComparisonRestriction_unitIso_inv_restrict T.fppfSite S T.fppf_mem Y
        (((spacesBaseChange T.fppfSite S T.fppf_mem h).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (SpacesEtale.topology T.fppfSite S
        T.fppf_mem Z)).obj ((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem
            Z).asEquivalence.inverse.obj (moduleSheaf.{u, u, u + 1} (structureRingSheaf T.fppfSite S
            T.fppf_mem Z) M))) U d y).symm

/-- `toSpacesEtaleModulesPushforwardIso_hom_app_val_app` for a section of the universe lift. -/
theorem toSpacesEtaleModulesPushforwardIso_hom_app_val_app' (h : Z ⟶ Y)
    (M : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Z.1 Z.2) (W : SpacesEtale T.fppfSite S
        T.fppf_mem Y)
    (y : ((sheafCompose (SpacesEtale.topology T.fppfSite S T.fppf_mem Y) uliftFunctor.{u + 1,
        u}).obj
      ((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem Y).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf T.fppfSite S T.fppf_mem Y)
        ((Space.modulePushforward T.fppfSite S T.fppf_mem h).obj M)))).obj.obj (op W)) :
    ((toSpacesEtaleModulesPushforwardIso T h).hom.app M).val.app (op W)
        ((toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y ((Space.modulePushforward
            T.fppfSite S T.fppf_mem h).obj M)).hom.hom.app
          (op W) y) =
      (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Z M).hom.hom.app
        (op ((spacesBaseChange T.fppfSite S T.fppf_mem h).functor.obj W))
        (ULift.up (((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem
            Y).asEquivalence.unitIso.inv.app (((spacesBaseChange T.fppfSite S T.fppf_mem
            h).functor.sheafPushforwardContinuous (Type u) (SpacesEtale.topology T.fppfSite S
                T.fppf_mem Y) (SpacesEtale.topology T.fppfSite S T.fppf_mem Z)).obj
                ((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem
                Z).asEquivalence.inverse.obj (moduleSheaf.{u, u, u + 1} (structureRingSheaf
                T.fppfSite S T.fppf_mem Z) M)))).hom.app (op W) (ULift.down y))) :=
  toSpacesEtaleModulesPushforwardIso_hom_app_val_app T h M W (ULift.down y)

/-- On sections over an étale chart `V` of `X`, the composition comparison of Stacks 03LU is
the inverse unit of Stacks 03G1 at `Y` followed by restriction along the composition
isomorphism of base change of Stacks 03G2, part (2). -/
theorem modulePushforwardCompIso_hom_app_val_app_eq (h : Z ⟶ Y) (f : Y ⟶ X)
    (M : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Z.1 Z.2)
    (V : (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2).Cᵒᵖ)
    (z : ((Space.modulePushforward T.fppfSite S T.fppf_mem f).obj
      ((Space.modulePushforward T.fppfSite S T.fppf_mem h).obj M)).val.obj V) :
    ((Space.modulePushforwardCompIso T.fppfSite S T.fppf_mem h f).hom.app M).val.app V z =
      ((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem Z).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf T.fppfSite S T.fppf_mem Z) M)).obj.map
        ((spacesBaseChange_comp T.fppfSite S T.fppf_mem h f).inv.app ((comparisonFunctor T.fppfSite
            S T.fppf_mem X).obj V.unop)).op
        (((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem Y).asEquivalence.unitIso.inv.app
            (((spacesBaseChange T.fppfSite S T.fppf_mem h).functor.sheafPushforwardContinuous (Type
            u) (SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (SpacesEtale.topology T.fppfSite S
                T.fppf_mem Z)).obj ((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem
                Z).asEquivalence.inverse.obj (moduleSheaf.{u, u, u + 1} (structureRingSheaf
                T.fppfSite S T.fppf_mem Z) M)))).hom.app
          (op ((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.obj ((comparisonFunctor
              T.fppfSite S T.fppf_mem X).obj V.unop))) z) := by
  refine (modulePushforwardCompIso_hom_app_val_app _ _ _ h f M _ z).trans ?_
  rw [smallToposMorphismTypeU_comp, MorphismOfTopoi.transport_comp_pushforward]
  exact transport_comp_pushforward_trans_hom_app_apply (smallEtaleToposEquivTypeU T.fppfSite S
      T.fppf_mem Z)
    (smallEtaleToposEquivTypeU T.fppfSite S T.fppf_mem Y) (smallEtaleToposEquivTypeU T.fppfSite S
        T.fppf_mem X)
    (spacesToposMorphismTypeU T.fppfSite S T.fppf_mem h).pushforward (spacesToposMorphismTypeU
        T.fppfSite S T.fppf_mem f).pushforward
    (spacesToposMorphismTypeU T.fppfSite S T.fppf_mem (h ≫ f)).pushforward
    (spacesBaseChange_pushforward_compTypeU T.fppfSite S T.fppf_mem h f)
    ((Sheaf.moduleSheafFunctor (structureRingSheaf T.fppfSite S T.fppf_mem Z)).obj M) V z

/-- On sections over an étale chart `V` of `X`, the chart comparison is the identification of
underlying sheaves at `Y ×_X V`. -/
theorem toSpacesEtaleModulesPushforwardChartIso_hom_val_app (f : Y ⟶ X)
    (N : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Y.1 Y.2) (V :
        (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u} (smallEtaleRingedSite
        T.fppfSite S T.fppf_mem X.1 X.2)).Cᵒᵖ)
    (x : ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).obj
          ((Space.modulePushforward T.fppfSite S T.fppf_mem f).obj N)).val.obj V) :
    ((toSpacesEtaleModulesPushforwardChartIso T f N).hom.val.app V).hom x =
      (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y N).hom.hom.app
        (op ((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.obj ((comparisonFunctor T.fppfSite
            S T.fppf_mem X).obj V.unop))) x :=
  rfl

/-- On sections over a chart, the restriction of the composition comparison of spaces-étale
direct images is restriction along the composition isomorphism of base change. -/
theorem comparisonModuleEquivalence_functor_map_smallEtaleRingedSiteHomPushforwardCompIso_val_app
    (h : Z ⟶ Y) (f : Y ⟶ X)
    (A : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite T.fppfSite S T.fppf_mem Z).O))
    (V : (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u} (smallEtaleRingedSite
        T.fppfSite S T.fppf_mem X.1 X.2)).Cᵒᵖ)
    (t : ((comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.obj
        ((smallEtaleRingedSiteHom T f).pushforwardTopos.obj
      ((smallEtaleRingedSiteHom T h).pushforwardTopos.obj A))).val.obj V) :
    (((comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.map
        ((smallEtaleRingedSiteHomPushforwardCompIso T h f).hom.app A)).val.app
        V).hom t =
      A.val.map ((spacesBaseChange_comp T.fppfSite S T.fppf_mem h f).inv.app
        ((comparisonFunctor T.fppfSite S T.fppf_mem X).obj V.unop)).op t :=
  rfl

/-- On sections over a chart, the restriction of the direct image of a morphism along
`f_{small}` is that morphism over `Y ×_X V`. -/
theorem comparisonModuleEquivalence_functor_map_pushforwardTopos_map_val_app (f : Y ⟶ X)
    {A A' : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite T.fppfSite S T.fppf_mem Y).O)}
    (φ : A ⟶ A')
    (V : (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u} (smallEtaleRingedSite
        T.fppfSite S T.fppf_mem X.1 X.2)).Cᵒᵖ)
    (t : ((comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.obj
        ((smallEtaleRingedSiteHom T f).pushforwardTopos.obj A)).val.obj V) :
    (((comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.map ((smallEtaleRingedSiteHom
        T f).pushforwardTopos.map φ)).val.app V).hom t =
      φ.val.app (op ((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.obj
        ((comparisonFunctor T.fppfSite S T.fppf_mem X).obj V.unop))) t :=
  rfl

/-- On sections, the universe lift of a morphism of modules is the lift of the morphism. -/
theorem liftModuleFunctor_map_val_app {N N' : Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1
    X.2} (φ : N ⟶ N')
    (V : (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u} (smallEtaleRingedSite
        T.fppfSite S T.fppf_mem X.1 X.2)).Cᵒᵖ)
    (x : ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).obj N).val.obj V) :
    (((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).map φ).val.app V).hom x =
      ULift.up (φ.val.app V (ULift.down x)) :=
  rfl

/-- The compatibility of the comparison of direct images with composition, on a section over
an étale chart `V` of `X`, before the universe lift. -/
theorem toSpacesEtaleModulesPushforwardIso_comp_apply₀ (h : Z ⟶ Y) (f : Y ⟶ X)
    (M : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Z.1 Z.2)
    (V : (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2).Cᵒᵖ)
    (x : ((Space.modulePushforward T.fppfSite S T.fppf_mem h ⋙
      Space.modulePushforward T.fppfSite S T.fppf_mem f).obj M).val.obj V) :
    (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Z M).hom.hom.app
        (op ((spacesBaseChange T.fppfSite S T.fppf_mem (h ≫ f)).functor.obj ((comparisonFunctor
            T.fppfSite S T.fppf_mem X).obj V.unop)))
        (ULift.up (((Space.modulePushforwardCompIso T.fppfSite S T.fppf_mem h f).hom.app M).val.app
            V x)) =
      ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Z).obj M).val.map
        ((spacesBaseChange_comp T.fppfSite S T.fppf_mem h f).inv.app ((comparisonFunctor T.fppfSite
            S T.fppf_mem X).obj V.unop)).op
        (((toSpacesEtaleModulesPushforwardIso T h).hom.app M).val.app
          (op ((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.obj ((comparisonFunctor
              T.fppfSite S T.fppf_mem X).obj V.unop)))
          ((toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y ((Space.modulePushforward
              T.fppfSite S T.fppf_mem h).obj M)).hom.hom.app
            (op ((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.obj ((comparisonFunctor
                T.fppfSite S T.fppf_mem X).obj V.unop)))
            (ULift.up x))) := by
  have s1 := modulePushforwardCompIso_hom_app_val_app_eq T h f M V x
  have s2 := toSpacesEtaleModulesPushforwardIso_hom_app_val_app T h M
    ((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.obj ((comparisonFunctor T.fppfSite S
        T.fppf_mem X).obj V.unop)) x
  have s3 := toSpacesEtaleModulesSheafIso_hom_map_apply T.fppfSite S T.fppf_mem Z M
    ((spacesBaseChange_comp T.fppfSite S T.fppf_mem h f).inv.app ((comparisonFunctor T.fppfSite S
      T.fppf_mem X).obj V.unop))
    (((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem Y).asEquivalence.unitIso.inv.app
      (((spacesBaseChange T.fppfSite S T.fppf_mem h).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (SpacesEtale.topology T.fppfSite S T.fppf_mem Z)).obj
        ((smallEtaleComparisonRestriction T.fppfSite S T.fppf_mem Z).asEquivalence.inverse.obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf T.fppfSite S T.fppf_mem Z)
            M)))).hom.app
      (op ((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.obj ((comparisonFunctor
        T.fppfSite S T.fppf_mem X).obj V.unop))) x)
  exact (congrArg (fun t ↦ (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Z M).hom.hom.app
      (op ((spacesBaseChange T.fppfSite S T.fppf_mem (h ≫ f)).functor.obj ((comparisonFunctor
          T.fppfSite S T.fppf_mem X).obj V.unop)))
      (ULift.up t)) s1).trans
    (s3.trans (congrArg (((toSpacesEtaleModules T.fppfSite S T.fppf_mem Z).obj M).val.map
      ((spacesBaseChange_comp T.fppfSite S T.fppf_mem h f).inv.app ((comparisonFunctor T.fppfSite S
          T.fppf_mem X).obj V.unop)).op)
      s2.symm))

/-- The compatibility of the comparison of direct images with composition, on a section over
an étale chart `V` of `X`. -/
theorem toSpacesEtaleModulesPushforwardIso_comp_apply (h : Z ⟶ Y) (f : Y ⟶ X)
    (M : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Z.1 Z.2) (V :
        (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u} (smallEtaleRingedSite
        T.fppfSite S T.fppf_mem X.1 X.2)).Cᵒᵖ)
    (x : ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).obj
        ((Space.modulePushforward T.fppfSite S T.fppf_mem h ⋙
          Space.modulePushforward T.fppfSite S T.fppf_mem f).obj M)).val.obj V) :
    (toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Z M).hom.hom.app
        (op ((spacesBaseChange T.fppfSite S T.fppf_mem (h ≫ f)).functor.obj ((comparisonFunctor
            T.fppfSite S T.fppf_mem X).obj V.unop)))
        (ULift.up (((Space.modulePushforwardCompIso T.fppfSite S T.fppf_mem h f).hom.app M).val.app
            V x.down)) =
      ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Z).obj M).val.map
        ((spacesBaseChange_comp T.fppfSite S T.fppf_mem h f).inv.app ((comparisonFunctor T.fppfSite
            S T.fppf_mem X).obj V.unop)).op
        ((((comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.map
          ((smallEtaleRingedSiteHom T f).pushforwardTopos.map
            ((toSpacesEtaleModulesPushforwardIso T h).hom.app M))).val.app V).hom
          ((toSpacesEtaleModulesSheafIso T.fppfSite S T.fppf_mem Y ((Space.modulePushforward
              T.fppfSite S T.fppf_mem h).obj M)).hom.hom.app
            (op ((spacesBaseChange T.fppfSite S T.fppf_mem f).functor.obj ((comparisonFunctor
                T.fppfSite S T.fppf_mem X).obj V.unop)))
            x)) := by
  refine Eq.trans ?_ (congrArg (((toSpacesEtaleModules T.fppfSite S T.fppf_mem Z).obj M).val.map
      ((spacesBaseChange_comp T.fppfSite S T.fppf_mem h f).inv.app ((comparisonFunctor T.fppfSite S
          T.fppf_mem X).obj V.unop)).op)
    (comparisonModuleEquivalence_functor_map_pushforwardTopos_map_val_app T f
      ((toSpacesEtaleModulesPushforwardIso T h).hom.app M) V _)).symm
  exact toSpacesEtaleModulesPushforwardIso_comp_apply₀ T h f M V (ULift.down x)

/-- **The chart comparison is compatible with composition**, before transport through the
module form of Stacks 03G1. -/
theorem toSpacesEtaleModulesPushforwardChartIso_comp (h : Z ⟶ Y) (f : Y ⟶ X)
    (M : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Z.1 Z.2) :
    (Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).map
        ((Space.modulePushforwardCompIso T.fppfSite S T.fppf_mem h f).hom.app M) ≫
      (toSpacesEtaleModulesPushforwardChartIso T (h ≫ f) M).hom =
    (toSpacesEtaleModulesPushforwardChartIso T f ((Space.modulePushforward T.fppfSite S T.fppf_mem
        h).obj M)).hom ≫
      (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.map ((smallEtaleRingedSiteHom
          T f).pushforwardTopos.map
        ((toSpacesEtaleModulesPushforwardIso T h).hom.app M)) ≫
      (comparisonModuleEquivalence T.fppfSite S T.fppf_mem
          X).functor.map ((smallEtaleRingedSiteHomPushforwardCompIso T h f).hom.app
        ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Z).obj M)) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rw [toSpacesEtaleModulesPushforwardChartIso_hom_val_app,
    toSpacesEtaleModulesPushforwardChartIso_hom_val_app,
    comparisonModuleEquivalence_functor_map_smallEtaleRingedSiteHomPushforwardCompIso_val_app]
  simp only [liftModuleFunctor_map_val_app]
  exact toSpacesEtaleModulesPushforwardIso_comp_apply T h f M V x

/-- `ι` on morphisms: the universe lift followed by the quasi-inverse of the module form of
Stacks 03G1. -/
theorem toSpacesEtaleModules_map {N N' : Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2} (g :
    N ⟶ N') :
    (toSpacesEtaleModules T.fppfSite S T.fppf_mem X).map g =
      (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).inverse.map
        ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
          (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).map g) :=
  rfl

/-- **The comparison of direct images is compatible with composition.** For `h : Z ⟶ Y` and
`f : Y ⟶ X`, transporting the composition comparison of Stacks 03LU through `ι` and composing
with the comparison for `h ≫ f` agrees with the comparisons for `f` and `h` followed by the
composition comparison of spaces-étale direct images. -/
theorem toSpacesEtaleModulesPushforwardIso_comp_hom_app (h : Z ⟶ Y) (f : Y ⟶ X)
    (M : Space.Modules.{u, u} T.fppfSite S T.fppf_mem Z.1 Z.2) :
    (toSpacesEtaleModules T.fppfSite S T.fppf_mem X).map ((Space.modulePushforwardCompIso T.fppfSite
        S T.fppf_mem h f).hom.app M) ≫
        (toSpacesEtaleModulesPushforwardIso T (h ≫ f)).hom.app M =
      (toSpacesEtaleModulesPushforwardIso T f).hom.app ((Space.modulePushforward T.fppfSite S
          T.fppf_mem h).obj M) ≫
        (smallEtaleRingedSiteHom T f).pushforwardTopos.map
          ((toSpacesEtaleModulesPushforwardIso T h).hom.app M) ≫
        (smallEtaleRingedSiteHomPushforwardCompIso T h f).hom.app
          ((toSpacesEtaleModules T.fppfSite S T.fppf_mem Z).obj M) := by
  refine (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).functor.map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp,
    comparisonModuleEquivalence_functor_map_toSpacesEtaleModulesPushforwardIso_hom_app,
    comparisonModuleEquivalence_functor_map_toSpacesEtaleModulesPushforwardIso_hom_app]
  have n := (comparisonModuleEquivalence T.fppfSite S T.fppf_mem X).counitIso.hom.naturality
    ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
      (smallEtaleRingedSite T.fppfSite S T.fppf_mem X.1 X.2)).map ((Space.modulePushforwardCompIso
          T.fppfSite S T.fppf_mem h f).hom.app M))
  rw [Functor.comp_map, Functor.id_map] at n
  rw [toSpacesEtaleModules_map]
  exact Space.comp_comp_eq_comp_comp_of_comm_sq n
    (toSpacesEtaleModulesPushforwardChartIso_comp T h f M)

end AlgebraicGeometry.BigEtaleSpaceSite
