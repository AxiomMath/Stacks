module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence

/-!
# The two monoidal structures on `f^*` have the same unit

Let `f : X ⟶ Y` be a morphism of ringed spaces. The pullback of sheaves of modules carries two
`CategoryTheory.Functor.Monoidal` structures in this repository, and the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence` and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackCompMonoidal` record the comparison of the
two as an **open dedup**:

* `Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`, whose tensorator is the inverse of
  the comparison `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` of Tag 01CD and whose unit morphism is the inverse of
  the structure-sheaf comparison `Stacks.PullbackTensorCoherence.pullbackUnitComparison`;
* `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`, obtained by transporting
  `Stacks.PullbackMonoidalSheaf.pullbackMonoidal` — the lift of the objectwise presheaf-level
  pullback along sheafification, by
  `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` — across the identity functors
  relating the localized and the strict spellings of the tensor product of Tag 01CA.

This file closes the **unit** half of that dedup: the two unit morphisms agree. Nothing here
compares the two tensorators, which remains open.

The point is that both unit morphisms are adjoint transposes of the *same* presheaf-level datum,
so no tensorator and no section of a sheafification has to be computed. Writing `L` for
sheafification, `P` for the presheaf-level pullback and `θ : L ⋙ f^* ≅ P ⋙ L` for Mathlib's
`SheafOfModules.sheafificationCompPullback`, the formula
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_ε` makes the oplax unit of
`pullbackStrictMonoidal` the composite

    f^*(𝒪_Y) --f^*(ε_L)⁻¹--> f^*(L 𝟙) --θ--> L (P 𝟙) --L(η_P)--> L 𝟙 --ε_L--> 𝒪_X,

and each of the four factors is characterised by an adjunction: `θ` by
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`, the two copies of `ε_L` by the triangle
identity of the sheafification adjunction, and `η_P` by
`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal_η`, which identifies its transpose with
`PresheafOfModules.pushforwardEpsilon`. The structure-sheaf comparison
`SheafOfModules.pullbackObjUnitToUnit` is by definition the transpose of
`SheafOfModules.unitToPushforwardObjUnit`, and the two presheaf-level data agree because both are
`φ` on local sections.

## Main definitions

* `Stacks.PullbackStrictUnit.sheafAdj`: the sheafification adjunction for the structure sheaf of a
  ringed space, ascribed at the spelling of the category of presheaves of modules that the
  monoidal structure is stated for.
* `Stacks.PullbackStrictUnit.adj1` and `adj2`: the two adjunctions whose left adjoints Mathlib's
  `SheafOfModules.sheafificationCompPullback` compares.
* `Stacks.PullbackStrictUnit.epsLoc`, `etaLoc`, `epsStrict` and `etaStrict`: the unit and counit
  morphisms of the two monoidal structures, each ascribed at the `SheafOfModules.unit` spelling of
  the monoidal unit.

## Main results

* `Stacks.PullbackStrictUnit.eta_pullbackFunctor`: **the oplax unit of
  `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal` is the structure-sheaf comparison
  `Stacks.PullbackTensorCoherence.pullbackUnitComparison` of Tag 01CD.**
* `Stacks.PullbackStrictUnit.epsilon_pullbackFunctor`: **its lax unit is the inverse of that
  comparison**, i.e. the unit morphism of
  `Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`.
* `Stacks.PullbackStrictUnit.pullbackOne_eq`: **the global unit of `f^*A` is the inverse of the
  structure-sheaf comparison followed by the pullback of the unit of `A`.** This is what a
  consumer of `Stacks.PullbackGradedAlgebra.pullbackOne` needs: a formula for it in terms of the
  comparison of Tag 01CD, hence one that transports along an iterated pullback by
  `Stacks.PullbackCompMonoidal.comparison_unit`.

## Implementation notes

Two spellings of the category of presheaves of modules on a ringed space occur: the index
`(Stacks.RingedSpace.structureRingSheaf Z).obj`, which the sheafification adjunction is stated
for, and `Z.presheaf ⋙ forget₂ CommRingCat RingCat`, at which the monoidal structure of
Mathlib's presheaves of modules is found by instance search. They are equal by `rfl` and not
syntactically equal, so a goal mixing them is not type-correct at `implicit` transparency and
`rw` refuses it. The cure prescribed in this directory is applied: `sheafAdj` and `forgetRestrict`
are `def`s with an **ascribed** type at the second spelling, every statement below is written with
them, and the crossing happens inside a proof given by `:=`. For the same reason every proof here
is a term built from `Eq.trans` and `congrArg` rather than a `rw` or `simp` call.

The unit object of the two monoidal structures is `SheafOfModules.unit` in both cases — the
tensor unit of `CategoryTheory.Localization.Monoidal.LocalizedMonoidal` is the target of the
chosen isomorphism `Stacks.PullbackMonoidalSheaf.sheafifyUnitIso`, and the inducing data
`Stacks.SheafOfModules.Strict.inducingFunctorData` has `Iso.refl` as its unit comparison — but
`𝟙_` does not reduce to it at `implicit` transparency either, which is why `epsLoc`, `etaLoc`,
`epsStrict` and `etaStrict` are ascribed at `SheafOfModules.unit`.

The counit of `Stacks.SheafOfModules.SliceRestriction.fromLocalizedMonoidalMonoidal` is produced
by `CategoryTheory.Functor.Monoidal.ofLaxMonoidal`, so it is an `inv`, whose definition the module
system does not expose; the transport of the counit from the localized to the strict structure
therefore goes through the lax unit, where no `inv` appears, and concludes with
`CategoryTheory.Functor.Monoidal.ε_η`.

## Not done here

* **The two tensorators are not compared.** The remaining half of the dedup is the identification
  of the tensorator of `pullbackStrictMonoidal` with the inverse of
  `Stacks.PullbackTensorCoherence.pullbackTensorComparison`, which
  `Stacks.PullbackMonoidalSheaf.pullbackMonoidal_mu` pins only at a pair of sheafified presheaves
  and in terms of the tensorator of sheafification.
* Nothing is said about the braiding, nor about the monoidal structure of a composite of two
  pullbacks beyond what `Stacks.PullbackCompMonoidal` proves.
* No `@[stacks]` attribute: Tags 01CA and 01CD are carried by the two monoidal structures being
  compared, and the comparison of two formalisations of one tag is not itself a numbered result.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.RingedSpace Stacks.PullbackMonoidalSheaf RingedSpaceModuleAdjunction
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe u

namespace Stacks.PullbackStrictUnit

attribute [local instance] PresheafOfModules.pushforwardLaxMonoidal
attribute [local instance] PresheafOfModules.pullbackOplaxMonoidal

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The adjunctions -/

/-- The right adjoint of sheafification of modules on a ringed space, ascribed so that its target
is the category of presheaves of modules at the spelling `Z.presheaf ⋙ forget₂ _ _` of the
structure ring presheaf, which is the one the monoidal structure is found at. -/
def forgetRestrict (Z : RingedSpace.{u, u}) :
    SheafOfModules.{u} (structureRingSheaf Z) ⥤
      PresheafOfModules.{u} (Z.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  SheafOfModules.forget (structureRingSheaf Z) ⋙
    PresheafOfModules.restrictScalars (𝟙 (structureRingSheaf Z).obj)

/-- The sheafification adjunction for modules on a ringed space, ascribed at `forgetRestrict`. -/
def sheafAdj (Z : RingedSpace.{u, u}) : sheafifyFunctor Z ⊣ forgetRestrict Z :=
  PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf Z).obj)

/-- The structure morphism of a morphism of ringed spaces, at the type the presheaf-level
pullback expects. -/
abbrev structureHom (f : X ⟶ Y) := Stacks.PullbackMonoidal.structurePresheafHom f

/-- The presheaf-level pullback along a morphism of ringed spaces. -/
abbrev presPullback (f : X ⟶ Y) := PresheafOfModules.pullback.{u} (structureHom f)

/-- The unit object of the objectwise monoidal structure on presheaves of modules on a ringed
space: the structure ring presheaf, as a module over itself. -/
abbrev presUnit (Z : RingedSpace.{u, u}) :
    PresheafOfModules.{u} (Z.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := 𝟙_ _

/-- Sheafification on `Y` followed by the sheaf-level pullback, as a left adjoint. This is the
first of the two adjunctions that `SheafOfModules.sheafificationCompPullback` compares. -/
def adj1 (f : X ⟶ Y) :
    sheafifyFunctor Y ⋙ pullbackFunctor f ⊣ pushforwardFunctor f ⋙ forgetRestrict Y :=
  (sheafAdj Y).comp (SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f))

/-- The presheaf-level pullback followed by sheafification on `X`, as a left adjoint. This is the
second of the two adjunctions that `SheafOfModules.sheafificationCompPullback` compares. -/
def adj2 (f : X ⟶ Y) :
    presPullback f ⋙ sheafifyFunctor X ⊣
      forgetRestrict X ⋙ PresheafOfModules.pushforward.{u} (structureHom f) :=
  (PresheafOfModules.pullbackPushforwardAdjunction (structureHom f)).comp (sheafAdj X)

/-! ### The presheaf level -/

/-- **The transpose of the oplax unit of the presheaf-level pullback is the unit map of the
presheaf-level pushforward.** This is `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal_η`, which
*defines* the oplax unit as that transpose. -/
theorem homEquiv_eta :
    (PresheafOfModules.pullbackPushforwardAdjunction (structureHom f)).unit.app (presUnit Y) ≫
        (PresheafOfModules.pushforward.{u} (structureHom f)).map (η (presPullback f)) =
      PresheafOfModules.pushforwardEpsilon (structureHom f) :=
  (Adjunction.homEquiv_apply _ _ _ _).symm.trans
    (Equiv.apply_symm_apply _ (ε (PresheafOfModules.pushforward.{u} (structureHom f))))

/-- **The unit map of the presheaf-level pushforward is the presheaf underlying the
structure-sheaf datum `SheafOfModules.unitToPushforwardObjUnit`.** Both are the structure
morphism `φ` of `f` on local sections. -/
theorem pushforwardEpsilon_eq :
    PresheafOfModules.pushforwardEpsilon (structureHom f) =
      (forgetRestrict Y).map (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  refine Eq.trans (PresheafOfModules.pushforwardEpsilon_app_apply (structureHom f) U a) ?_
  exact (SheafOfModules.unitToPushforwardObjUnit_val_app_apply (structureSheafHom f) a).symm

/-- If `a ≫ F.map g = b`, then `a ≫ F.map (g ≫ h) = b ≫ F.map h`. -/
private theorem comp_map_comp_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W : D} {X Y Z : C} {a : W ⟶ F.obj X} {g : X ⟶ Y} (h : Y ⟶ Z) {b : W ⟶ F.obj Y}
    (H : a ≫ F.map g = b) : a ≫ F.map (g ≫ h) = b ≫ F.map h :=
  (congrArg (fun z => a ≫ z) (F.map_comp g h)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ F.map h) H))

/-- The sheafification unit at `P 𝟙`, followed by the oplax unit of the presheaf-level pullback
read through sheafification and the comparison of the sheafified unit with
`SheafOfModules.unit`, is the oplax unit of the presheaf-level pullback. This is the naturality of
the sheafification unit together with the triangle identity on `X`. -/
theorem unit_comp_map_eta :
    (sheafAdj X).unit.app ((presPullback f).obj (presUnit Y)) ≫
      (forgetRestrict X).map
        ((sheafifyFunctor X).map (η (presPullback f)) ≫ (sheafifyUnitIso X).hom) =
      η (presPullback f) :=
  have h2 : (sheafAdj X).unit.app ((presPullback f).obj (presUnit Y)) ≫
        (forgetRestrict X).map ((sheafifyFunctor X).map (η (presPullback f))) =
      η (presPullback f) ≫ (sheafAdj X).unit.app (presUnit X) :=
    ((sheafAdj X).unit.naturality (η (presPullback f))).symm
  have h3 : (sheafAdj X).unit.app (presUnit X) ≫
        (forgetRestrict X).map ((sheafifyUnitIso X).hom) =
      CategoryStruct.id (presUnit X) :=
    (sheafAdj X).right_triangle_components (SheafOfModules.unit (structureRingSheaf X))
  (comp_map_comp_of_eq (forgetRestrict X) (sheafifyUnitIso X).hom h2).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => η (presPullback f) ≫ z) h3).trans (Category.comp_id _)))

/-- The transpose along `adj2` of the unit datum of the presheaf-level pullback composed with
sheafification: it is the unit map of the presheaf-level pushforward. -/
theorem adj2_unit_comp :
    (adj2 f).unit.app (presUnit Y) ≫
        (forgetRestrict X ⋙ PresheafOfModules.pushforward.{u} (structureHom f)).map
          ((sheafifyFunctor X).map (η (presPullback f)) ≫ (sheafifyUnitIso X).hom) =
      PresheafOfModules.pushforwardEpsilon (structureHom f) :=
  have hu : (adj2 f).unit.app (presUnit Y) =
      (PresheafOfModules.pullbackPushforwardAdjunction (structureHom f)).unit.app (presUnit Y) ≫
        (PresheafOfModules.pushforward.{u} (structureHom f)).map
          ((sheafAdj X).unit.app ((presPullback f).obj (presUnit Y))) :=
    Adjunction.comp_unit_app _ _ _
  have hcomp : (PresheafOfModules.pushforward.{u} (structureHom f)).map
          ((sheafAdj X).unit.app ((presPullback f).obj (presUnit Y))) ≫
        (PresheafOfModules.pushforward.{u} (structureHom f)).map ((forgetRestrict X).map
          ((sheafifyFunctor X).map (η (presPullback f)) ≫ (sheafifyUnitIso X).hom)) =
      (PresheafOfModules.pushforward.{u} (structureHom f)).map (η (presPullback f)) :=
    (Functor.map_comp _ _ _).symm.trans (congrArg
      (fun z => (PresheafOfModules.pushforward.{u} (structureHom f)).map z) (unit_comp_map_eta f))
  ((congrArg (fun z => z ≫ (forgetRestrict X ⋙
          PresheafOfModules.pushforward.{u} (structureHom f)).map
        ((sheafifyFunctor X).map (η (presPullback f)) ≫ (sheafifyUnitIso X).hom)) hu).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => (PresheafOfModules.pullbackPushforwardAdjunction
          (structureHom f)).unit.app (presUnit Y) ≫ z) hcomp).trans (homEquiv_eta f))))

/-- The transpose along `adj1` of the structure-sheaf comparison, read at the sheafified unit: it
is the presheaf underlying `SheafOfModules.unitToPushforwardObjUnit`. -/
theorem adj1_unit_comp :
    (adj1 f).unit.app (presUnit Y) ≫
        (pushforwardFunctor f ⋙ forgetRestrict Y).map
          ((pullbackFunctor f).map ((sheafifyUnitIso Y).hom) ≫
            Stacks.PullbackAlgebra.unitComparison f) =
      (forgetRestrict Y).map (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) :=
  have hu : (adj1 f).unit.app (presUnit Y) =
      (sheafAdj Y).unit.app (presUnit Y) ≫ (forgetRestrict Y).map
        ((SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f)).unit.app
          ((sheafifyFunctor Y).obj (presUnit Y))) :=
    Adjunction.comp_unit_app _ _ _
  have hnat : (SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f)).unit.app
          ((sheafifyFunctor Y).obj (presUnit Y)) ≫
        (pushforwardFunctor f).map ((pullbackFunctor f).map ((sheafifyUnitIso Y).hom)) =
      (sheafifyUnitIso Y).hom ≫
        (SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f)).unit.app
          (SheafOfModules.unit (structureRingSheaf Y)) :=
    ((SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f)).unit.naturality
      ((sheafifyUnitIso Y).hom)).symm
  have htrans : (SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f)).unit.app
          (SheafOfModules.unit (structureRingSheaf Y)) ≫
        (pushforwardFunctor f).map (Stacks.PullbackAlgebra.unitComparison f) =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) :=
    (Adjunction.homEquiv_apply _ _ _ _).symm.trans
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
        (structureSheafHom f))
  have htri : (sheafAdj Y).unit.app (presUnit Y) ≫
        (forgetRestrict Y).map ((sheafifyUnitIso Y).hom) = CategoryStruct.id (presUnit Y) :=
    (sheafAdj Y).right_triangle_components (SheafOfModules.unit (structureRingSheaf Y))
  have hinner : (SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f)).unit.app
          ((sheafifyFunctor Y).obj (presUnit Y)) ≫
        (pushforwardFunctor f).map ((pullbackFunctor f).map ((sheafifyUnitIso Y).hom) ≫
          Stacks.PullbackAlgebra.unitComparison f) =
      (sheafifyUnitIso Y).hom ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) :=
    (comp_map_comp_of_eq (pushforwardFunctor f) _ hnat).trans
      ((Category.assoc _ _ _).trans (congrArg (fun z => (sheafifyUnitIso Y).hom ≫ z) htrans))
  have htail : (sheafAdj Y).unit.app (presUnit Y) ≫
        (forgetRestrict Y).map ((sheafifyUnitIso Y).hom ≫
          SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) =
      (forgetRestrict Y).map
        (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) :=
    (comp_map_comp_of_eq (forgetRestrict Y) _ htri).trans (Category.id_comp _)
  have hmid : (forgetRestrict Y).map
          ((SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f)).unit.app
            ((sheafifyFunctor Y).obj (presUnit Y))) ≫
        (pushforwardFunctor f ⋙ forgetRestrict Y).map
          ((pullbackFunctor f).map ((sheafifyUnitIso Y).hom) ≫
            Stacks.PullbackAlgebra.unitComparison f) =
      (forgetRestrict Y).map ((sheafifyUnitIso Y).hom ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) :=
    (Functor.map_comp (forgetRestrict Y)
        ((SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f)).unit.app
          ((sheafifyFunctor Y).obj (presUnit Y)))
        ((pushforwardFunctor f).map ((pullbackFunctor f).map ((sheafifyUnitIso Y).hom) ≫
          Stacks.PullbackAlgebra.unitComparison f))).symm.trans
      (congrArg (fun z => (forgetRestrict Y).map z) hinner)
  (congrArg (fun z => z ≫ (pushforwardFunctor f ⋙ forgetRestrict Y).map
        ((pullbackFunctor f).map ((sheafifyUnitIso Y).hom) ≫
          Stacks.PullbackAlgebra.unitComparison f)) hu).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => (sheafAdj Y).unit.app (presUnit Y) ≫ z) hmid).trans htail))

/-! ### The localized monoidal structure -/

section Localized

attribute [local instance] Stacks.PullbackMonoidalSheaf.monoidalCategory
attribute [local instance] Stacks.PullbackMonoidalSheaf.sheafifyFunctorMonoidal
attribute [local instance] Stacks.PullbackMonoidalSheaf.sheafifiedPresheafPullbackMonoidal
attribute [local instance] Stacks.PullbackMonoidalSheaf.pullbackMonoidal
attribute [local instance] Stacks.PullbackMonoidal.presheafPullbackMonoidal

/-- The oplax unit of `Stacks.PullbackMonoidalSheaf.pullbackMonoidal`, ascribed at the
`SheafOfModules.unit` spelling of the monoidal unit. -/
def etaLoc (f : X ⟶ Y) :
    (pullbackFunctor f).obj (SheafOfModules.unit (structureRingSheaf Y)) ⟶
      SheafOfModules.unit (structureRingSheaf X) :=
  η (pullbackFunctor f)

/-- The lax unit of `Stacks.PullbackMonoidalSheaf.pullbackMonoidal`, ascribed at the
`SheafOfModules.unit` spelling of the monoidal unit. -/
def epsLoc (f : X ⟶ Y) :
    SheafOfModules.unit (structureRingSheaf X) ⟶
      (pullbackFunctor f).obj (SheafOfModules.unit (structureRingSheaf Y)) :=
  ε (pullbackFunctor f)

/-- The lax and oplax units of the localized structure are inverse, in one order. -/
theorem epsLoc_etaLoc : epsLoc f ≫ etaLoc f =
    CategoryStruct.id (SheafOfModules.unit (structureRingSheaf X)) :=
  Functor.Monoidal.ε_η (pullbackFunctor f)

/-- The lax and oplax units of the localized structure are inverse, in the other order. -/
theorem etaLoc_epsLoc : etaLoc f ≫ epsLoc f =
    CategoryStruct.id ((pullbackFunctor f).obj (SheafOfModules.unit (structureRingSheaf Y))) :=
  Functor.Monoidal.η_ε (pullbackFunctor f)

/-- **The oplax unit of the localized monoidal structure on `f^*` is the structure-sheaf
comparison.** Both are transposes of `SheafOfModules.unitToPushforwardObjUnit`: the four factors
of `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_ε` transpose to the unit map of
the presheaf-level pushforward, and so does the structure-sheaf comparison. -/
theorem etaLoc_eq : etaLoc f = Stacks.PullbackAlgebra.unitComparison f :=
  have hfactor : etaLoc f =
      (pullbackFunctor f).map ((sheafifyUnitIso Y).inv) ≫
        ((liftingIso f).hom.app (presUnit Y) ≫
          ((sheafifyFunctor X).map (η (presPullback f)) ≫ (sheafifyUnitIso X).hom)) := rfl
  have huniq : (adj1 f).unit.app (presUnit Y) ≫
        (pushforwardFunctor f ⋙ forgetRestrict Y).map ((liftingIso f).hom.app (presUnit Y)) =
      (adj2 f).unit.app (presUnit Y) :=
    Adjunction.unit_leftAdjointUniq_hom_app (adj1 f) (adj2 f) (presUnit Y)
  have hB : (adj2 f).unit.app (presUnit Y) ≫
        (pushforwardFunctor f ⋙ forgetRestrict Y).map
          ((sheafifyFunctor X).map (η (presPullback f)) ≫ (sheafifyUnitIso X).hom) =
      PresheafOfModules.pushforwardEpsilon (structureHom f) := adj2_unit_comp f
  have hLHS : (adj1 f).unit.app (presUnit Y) ≫
        (pushforwardFunctor f ⋙ forgetRestrict Y).map
          ((liftingIso f).hom.app (presUnit Y) ≫
            ((sheafifyFunctor X).map (η (presPullback f)) ≫ (sheafifyUnitIso X).hom)) =
      PresheafOfModules.pushforwardEpsilon (structureHom f) :=
    (comp_map_comp_of_eq (pushforwardFunctor f ⋙ forgetRestrict Y) _ huniq).trans hB
  have hcontract : (liftingIso f).hom.app (presUnit Y) ≫
        ((sheafifyFunctor X).map (η (presPullback f)) ≫ (sheafifyUnitIso X).hom) =
      (pullbackFunctor f).map ((sheafifyUnitIso Y).hom) ≫
        Stacks.PullbackAlgebra.unitComparison f :=
    ((adj1 f).homEquiv (presUnit Y)
        (SheafOfModules.unit (structureRingSheaf X))).injective
      ((Adjunction.homEquiv_apply _ _ _ _).trans
        ((hLHS.trans ((pushforwardEpsilon_eq f).trans (adj1_unit_comp f).symm)).trans
          (Adjunction.homEquiv_apply _ _ _ _).symm))
  hfactor.trans
    ((congrArg (fun z => (pullbackFunctor f).map ((sheafifyUnitIso Y).inv) ≫ z) hcontract).trans
      (Iso.inv_hom_id_assoc ((pullbackFunctor f).mapIso (sheafifyUnitIso Y)) _))

end Localized

/-! ### The strict monoidal structure -/

section Strict

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal

/-- The lax unit of `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`, ascribed at the
`SheafOfModules.unit` spelling of the monoidal unit. -/
def epsStrict (f : X ⟶ Y) :
    SheafOfModules.unit (structureRingSheaf X) ⟶
      (pullbackFunctor f).obj (SheafOfModules.unit (structureRingSheaf Y)) :=
  ε (pullbackFunctor f)

/-- The oplax unit of `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`, ascribed at the
`SheafOfModules.unit` spelling of the monoidal unit. -/
def etaStrict (f : X ⟶ Y) :
    (pullbackFunctor f).obj (SheafOfModules.unit (structureRingSheaf Y)) ⟶
      SheafOfModules.unit (structureRingSheaf X) :=
  η (pullbackFunctor f)

/-- **The lax units of the two monoidal structures agree.** The strict structure is the localized
one transported across two identity functors, whose own unit comparisons are
`CategoryTheory.Iso.refl`, so the only difference is a `f^*(𝟙)` to be removed. -/
theorem epsStrict_eq : epsStrict f = epsLoc f :=
  (show epsStrict f = epsLoc f ≫ (pullbackFunctor f).map
      (CategoryStruct.id (SheafOfModules.unit (structureRingSheaf Y))) from rfl).trans
    ((congrArg (fun z => epsLoc f ≫ z)
        (CategoryTheory.Functor.map_id (pullbackFunctor f)
          (SheafOfModules.unit (structureRingSheaf Y)))).trans (Category.comp_id _))

/-- **The oplax units of the two monoidal structures agree.** Read off `epsStrict_eq` through the
two inverse relations, which avoids the `inv` in the counit of
`Stacks.SheafOfModules.SliceRestriction.fromLocalizedMonoidalMonoidal`. -/
theorem etaStrict_eq : etaStrict f = etaLoc f :=
  have hεη : epsStrict f ≫ etaStrict f =
      CategoryStruct.id (SheafOfModules.unit (structureRingSheaf X)) :=
    Functor.Monoidal.ε_η (pullbackFunctor f)
  (Category.id_comp (etaStrict f)).symm.trans
    ((congrArg (fun z => z ≫ etaStrict f) (etaLoc_epsLoc f).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => etaLoc f ≫ z)
            ((congrArg (fun z => z ≫ etaStrict f) (epsStrict_eq f).symm).trans hεη)).trans
          (Category.comp_id _))))

/-- **The oplax unit of the strict monoidal structure on `f^*` is the structure-sheaf comparison
of Tag 01CD.** This is the unit half of the dedup between
`Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal` and
`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`. -/
theorem eta_pullbackFunctor :
    η (pullbackFunctor f) = Stacks.PullbackTensorCoherence.pullbackUnitComparison f :=
  (etaStrict_eq f).trans (etaLoc_eq f)

/-- **The lax unit of the strict monoidal structure on `f^*` is the inverse of the
structure-sheaf comparison of Tag 01CD**, i.e. it is the unit morphism of
`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`. -/
theorem epsilon_pullbackFunctor :
    ε (pullbackFunctor f) =
      inv (Stacks.PullbackTensorCoherence.pullbackUnitComparison f) :=
  IsIso.eq_inv_of_hom_inv_id
    ((congrArg (fun z => z ≫ ε (pullbackFunctor f)) (eta_pullbackFunctor f).symm).trans
      (Functor.Monoidal.η_ε (pullbackFunctor f)))

/-- **The global unit of `f^*A` is the inverse of the structure-sheaf comparison of Tag 01CD
followed by the pullback of the global unit of `A`.** This is the formula a consumer of
`Stacks.PullbackGradedAlgebra.pullbackOne` needs in order to transport it along an iterated
pullback, since `Stacks.PullbackCompMonoidal.comparison_unit` is stated for the comparison of
Tag 01CD. -/
theorem pullbackOne_eq
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)) :
    Stacks.PullbackGradedAlgebra.pullbackOne f A =
      inv (Stacks.PullbackTensorCoherence.pullbackUnitComparison f) ≫
        (pullbackFunctor f).map (SheafOfModules.GradedAlgebra.oneHom A) :=
  congrArg (fun z => z ≫ (pullbackFunctor f).map
    (SheafOfModules.GradedAlgebra.oneHom A)) (epsilon_pullbackFunctor f)

/-- **`pullbackOne_eq` with the structure-sheaf comparison moved to the other side**: the
comparison followed by the global unit of `f^*A` is the pullback of the global unit of `A`. This
is the `inv`-free form, and the one a computation with an iterated pullback uses. -/
theorem pullbackUnitComparison_comp_pullbackOne
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)) :
    Stacks.PullbackTensorCoherence.pullbackUnitComparison f ≫
        Stacks.PullbackGradedAlgebra.pullbackOne f A =
      (pullbackFunctor f).map (SheafOfModules.GradedAlgebra.oneHom A) :=
  (congrArg (fun z => Stacks.PullbackTensorCoherence.pullbackUnitComparison f ≫ z)
      (pullbackOne_eq f A)).trans
    (IsIso.hom_inv_id_assoc (Stacks.PullbackTensorCoherence.pullbackUnitComparison f) _)

end Strict

end Stacks.PullbackStrictUnit

end
