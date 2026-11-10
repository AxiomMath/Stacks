module

public import Mathlib.CategoryTheory.Functor.Flat
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleFiniteLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicityAtMorphismUniverse
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image of an injective module along `ε_a` is acyclic for `ε_*`

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site `B`, let
`ε_a : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` be the morphism of small étale ringed sites of
[Stacks, Tag 070R] (2), and let `ε : (Y_étale, 𝒪_Y) ⟶ (Y_Zar, 𝒪_Y)` be the comparison with the
small Zariski site, whose direct image is `AlgebraicGeometry.SmallEtale.restrictModule`. This file
proves that for an injective `𝒪_{X_étale}`-module `I`

`R ᵖ ε_*((ε_a)_* I) = 0` for `p > 0`.

This is [Stacks, Tag 072Z] followed by part (4) of [Stacks, Tag 0731] in this special case, at
the universes of the small étale sites.

## Main results

* `AlgebraicGeometry.SmallEtale.injective_smallEtalePushforwardAb`: the abelian direct image
  along base change preserves injectives, at the coefficient universe `u`.
* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_pushforward_of_injective`: the
  derived module-valued sections over every object of `Y_étale` of `(ε_a)_* I` vanish in positive
  degrees.
* `AlgebraicGeometry.SmallEtale.acyclic_restrictModule_pushforward_of_injective`: `(ε_a)_* I` is
  acyclic for `ε_*`.

## Implementation notes

Everything happens on the underlying abelian sheaves, where inverse image is exact.

1. The direct image `f_*` of abelian sheaves along base change `Y_étale ⥤ X_étale` preserves
   injective objects (`injective_smallEtalePushforwardAb`). Its left adjoint is a left Kan
   extension along a representably flat functor, hence exact; Mathlib proves that only for
   *small* categories, and the small étale sites have their objects in `Type (u + 1)`, so the
   argument is carried out on their `Type u` models
   (`AlgebraicGeometry.SmallEtale.smallModelEquiv`) and read back, exactly as
   `StacksFrontier/AlgebraicGeometry/EtaleCohomology/PushforwardAcyclic/Injectivity.lean` does at
   the coefficient universe `u + 1` with `CategoryTheory.ULiftHom`.
2. The underlying abelian sheaf `I_ab` of an injective module has vanishing cohomology over every
   object, at the morphism universe of the site, so its higher direct images vanish
   ([Stacks, Tag 072W] for abelian sheaves):
   `isZero_higherDirectImage_toSheaf_succAtMorphismUniverse`.
3. So `I_ab` is `f_*`-acyclic and `f_*` preserves injectives, and the collapse
   `Stacks.RightDerivedComp.objIso` identifies `H ᵖ(W, f_* I_ab)` with `H ᵖ(u W, I_ab) = 0`, for
   every object `W` of `Y_étale`.
4. [Stacks, Tag 03FD] (`AlgebraicGeometry.SmallEtale.rightDerivedSectionsIsoSheafCohomology`)
   turns that into the vanishing of the derived module-valued sections of `(ε_a)_* I`, whose
   underlying abelian sheaf is `f_* I_ab` on the nose, and the presieve criterion
   `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`
   assembles those into the vanishing of `R ᵖ ε_*`.

No `@[stacks]` attribute is placed: Stacks 072Z and 0731 are registered where they are proved in
general.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 0731](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v₁ u₁ v₂ u₂

/-! ### Higher direct images of an injective module, at the morphism universe -/

namespace Stacks.Cohomology.InjectiveModuleSheafAcyclicity

open Stacks.Cohomology.SheafifiedHigherDirectImage

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology D) (K : GrothendieckTopology C) (u : D ⥤ C) [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{max v₁ t}]
  [HasSheafify K AddCommGrpCat.{max v₁ t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max v₁ t}]
  [HasExt.{max v₁ t} (Sheaf K AddCommGrpCat.{max v₁ t})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{max v₁ t})]
  (R : Sheaf K RingCat.{max v₁ t}) (I : SheafOfModules.{max v₁ t} R) [Injective I]

/-- For an injective module `I`, the higher direct images `R^(q+1) f_* I_ab` of its underlying
abelian sheaf vanish, with coefficients at the morphism universe of the site. This is
`isZero_higherDirectImage_toSheaf_succ` with the coefficient universe free of the objects of the
site. -/
theorem isZero_higherDirectImage_toSheaf_succAtMorphismUniverse (q : ℕ) :
    IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{max v₁ t} J K).rightDerived
      (q + 1)).obj ((SheafOfModules.toSheaf R).obj I)) :=
  IsZero.of_iso
    (Functor.map_isZero (presheafToSheaf J AddCommGrpCat.{max v₁ t})
      (Functor.isZero_of_isZero_obj _ fun V ↦
        IsZero.of_iso
          (isZero_rightDerived_sections_toSheaf_succAtMorphismUniverse.{t} K R I
            (u.obj V.unop) q)
          ((pushforwardCohomologyPresheafEvaluationIso AddCommGrpCat.{max v₁ t} u (q + 1)
            V.unop).app ((SheafOfModules.toSheaf R).obj I)).symm))
    ((rightDerivedPushforwardIso AddCommGrpCat.{max v₁ t} u (q + 1)).app
      ((SheafOfModules.toSheaf R).obj I))

end Stacks.Cohomology.InjectiveModuleSheafAcyclicity

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

universe u

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-! ### The abelian direct image preserves injectives -/

/-- The direct image of abelian sheaves along base change on the small étale sites, at the
coefficient universe `u` of the structure sheaves. -/
abbrev smallEtalePushforwardAb :
    Sheaf (topology B X.obj X.property) AddCommGrpCat.{u} ⥤
      Sheaf (topology B Y.obj Y.property) AddCommGrpCat.{u} :=
  (smallEtaleBaseChange B a).sheafPushforwardContinuous AddCommGrpCat.{u}
    (topology B Y.obj Y.property) (topology B X.obj X.property)

/-- Base change, read on the `Type u` models of the two small étale sites. -/
abbrev smallModelBaseChange :
    SmallModel.{u} (SmallEtale B Y.obj Y.property) ⥤
      SmallModel.{u} (SmallEtale B X.obj X.property) :=
  (smallModelEquiv B Y.obj Y.property).inverse ⋙ smallEtaleBaseChange B a ⋙
    (smallModelEquiv B X.obj X.property).functor

/-- Base change of small étale sites is representably flat. -/
instance representablyFlat_smallEtaleBaseChange :
    RepresentablyFlat (smallEtaleBaseChange B a) :=
  flat_of_preservesFiniteLimits _

/-- Base change on the `Type u` models of the small étale sites is representably flat. -/
instance representablyFlat_smallModelBaseChange :
    RepresentablyFlat (smallModelBaseChange B a) :=
  inferInstanceAs (RepresentablyFlat ((smallModelEquiv B Y.obj Y.property).inverse ⋙
    smallEtaleBaseChange B a ⋙ (smallModelEquiv B X.obj X.property).functor))

/-- The underlying presheaf of the direct image along base change of an injective abelian sheaf
is injective, at the coefficient universe `u`. -/
@[sga "4½ Arcata 2.3.3"]
theorem injective_smallEtalePushforwardAb_obj
    (I : Sheaf (topology B X.obj X.property) AddCommGrpCat.{u}) [Injective I] :
    Injective ((smallEtalePushforwardAb B a).obj I).obj := by
  let eₓ := smallModelEquiv B X.obj X.property
  let eᵧ := smallModelEquiv B Y.obj Y.property
  let F' := smallModelBaseChange B a
  let preₓ := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj eₓ.inverse.op
  let preᵧ := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj eᵧ.inverse.op
  have : Injective I.obj :=
    (sheafificationAdjunction (topology B X.obj X.property) AddCommGrpCat.{u}).map_injective I
      inferInstance
  have : Injective (preₓ.obj I.obj) :=
    (preₓ.asEquivalence.map_injective_iff I.obj).2 inferInstance
  have hlan : Injective (F'.op ⋙ preₓ.obj I.obj) :=
    (F'.op.lanAdjunction AddCommGrpCat.{u}).map_injective (preₓ.obj I.obj) inferInstance
  have e : F'.op ⋙ preₓ.obj I.obj ≅ preᵧ.obj ((smallEtalePushforwardAb B a).obj I).obj :=
    Functor.isoWhiskerLeft (eᵧ.inverse.op ⋙ (smallEtaleBaseChange B a).op)
      (Functor.isoWhiskerRight eₓ.op.unitIso.symm I.obj)
  exact (preᵧ.asEquivalence.map_injective_iff _).1 (Injective.of_iso e hlan)

/-- The direct image of abelian sheaves along base change on the small étale sites preserves
injectives, at the coefficient universe `u`. -/
theorem injective_smallEtalePushforwardAb
    (I : Sheaf (topology B X.obj X.property) AddCommGrpCat.{u}) [Injective I] :
    Injective ((smallEtalePushforwardAb B a).obj I) :=
  (sheafificationAdjunction (topology B Y.obj Y.property)
      AddCommGrpCat.{u}).injective_of_map_injective _
    (injective_smallEtalePushforwardAb_obj B a I)

/-- The abelian direct image along base change preserves injective objects. -/
instance preservesInjectiveObjects_smallEtalePushforwardAb :
    (smallEtalePushforwardAb B a).PreservesInjectiveObjects where
  injective_obj _ := injective_smallEtalePushforwardAb B a _

/-! ### The direct image of an injective module has no higher cohomology over any object -/

variable (I : SheafOfModules.{u} (structureSheaf B X.obj X.property)) [Injective I]

/-- The underlying abelian sheaf of an injective module on `X_étale` is acyclic for the abelian
direct image along base change. -/
theorem isZero_rightDerived_smallEtalePushforwardAb_toSheaf (n : ℕ) (hn : 0 < n) :
    IsZero (((smallEtalePushforwardAb B a).rightDerived n).obj
      ((SheafOfModules.toSheaf (structureSheaf B X.obj X.property)).obj I)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one.2 hn
  open Stacks.Cohomology.InjectiveModuleSheafAcyclicity in
  exact isZero_higherDirectImage_toSheaf_succAtMorphismUniverse.{u}
    (topology B Y.obj Y.property) (topology B X.obj X.property) (smallEtaleBaseChange B a)
    (structureSheaf B X.obj X.property) I q

/-- The abelian cohomology over an object `W` of `Y_étale` of the direct image of the underlying
abelian sheaf of an injective module vanishes in positive degrees. -/
theorem isZero_rightDerived_sections_smallEtalePushforwardAb_toSheaf
    (W : SmallEtale B Y.obj Y.property) (n : ℕ) (hn : 0 < n) :
    IsZero ((((sheafSections (topology B Y.obj Y.property) AddCommGrpCat.{u}).obj
      (op W)).rightDerived n).obj ((smallEtalePushforwardAb B a).obj
        ((SheafOfModules.toSheaf (structureSheaf B X.obj X.property)).obj I))) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one.2 hn
  refine IsZero.of_iso ?_ (Stacks.RightDerivedComp.objIso (smallEtalePushforwardAb B a)
      (injectiveResolution ((SheafOfModules.toSheaf (structureSheaf B X.obj X.property)).obj I))
      (isZero_rightDerived_smallEtalePushforwardAb_toSheaf B a I)
      ((sheafSections (topology B Y.obj Y.property) AddCommGrpCat.{u}).obj (op W))
      (q + 1)).symm
  open Stacks.Cohomology.InjectiveModuleSheafAcyclicity in
  exact isZero_rightDerived_sections_toSheaf_succAtMorphismUniverse.{u}
    (topology B X.obj X.property) (structureSheaf B X.obj X.property) I
    ((smallEtaleBaseChange B a).obj W) q

/-- The derived module-valued sections over an object of `Y_étale` of the direct image along
`ε_a` of an injective module vanish in positive degrees. -/
theorem isZero_rightDerived_evaluation_pushforward_of_injective
    (W : SmallEtale B Y.obj Y.property) (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafOfModules.evaluation (structureSheaf B Y.obj Y.property) (op W)).rightDerived
      n).obj ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj I)) := by
  have h : IsZero ((forget₂ (ModuleCat.{u} ((structureSheaf B Y.obj Y.property).obj.obj (op W)))
      AddCommGrpCat.{u}).obj
        (((SheafOfModules.evaluation (structureSheaf B Y.obj Y.property) (op W)).rightDerived
          n).obj ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj I))) :=
    IsZero.of_iso (isZero_rightDerived_sections_smallEtalePushforwardAb_toSheaf B a I W n hn)
      (((Functor.rightDerivedCompIso
          (SheafOfModules.evaluation (structureSheaf B Y.obj Y.property) (op W))
          (forget₂ (ModuleCat.{u} ((structureSheaf B Y.obj Y.property).obj.obj (op W)))
            AddCommGrpCat.{u}) n).app _).symm ≪≫
        (rightDerivedSectionsToSheafIso B Y.obj Y.property W n).app _)
  exact ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.subsingleton_of_isZero h)

/-- The direct image along `ε_a` of an injective module is acyclic for `ε_*`: its higher direct
images along the comparison `ε : Y_étale ⟶ Y_Zar` vanish in positive degrees. -/
theorem acyclic_restrictModule_pushforward_of_injective :
    Stacks.RightDerivedComp.acyclic (restrictModule B Y.obj Y.property)
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj I) := fun p hp ↦
  Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (opensToSmallEtale B Y.obj Y.property) _ _ (structureMap B Y.obj Y.property) p _ fun V ↦
      ⟨affineOpensPresieve Y.obj V, generate_affineOpensPresieve_mem Y.obj V, fun W _ _ ↦
        isZero_rightDerived_evaluation_pushforward_of_injective B a I
          ((opensToSmallEtale B Y.obj Y.property).obj W) p hp⟩

end AlgebraicGeometry.SmallEtale

end
