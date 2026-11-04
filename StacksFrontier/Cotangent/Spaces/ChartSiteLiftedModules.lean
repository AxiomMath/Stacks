module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Module.ULift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Cotangent.Spaces.CotangentComplex

/-!
# Sheaves of `𝒪_X`-modules on `X_étale` presented in the universe of the site

Let `X` be an algebraic space over a ring `Λ`. Its small étale site `X_étale` has objects in
`Type (u + 1)`, while the structure sheaf `𝒪_X` has sections in the universe `u` of the schemes.
The site of polynomial charts of `X` (Tag 08VA) and the cotangent complex of Tag 08VD form their
sheaves in the universe `u + 1`, where `𝒪_X` is presented by the canonical `ULift` of its
section rings, `AlgebraicGeometry.Space.smallEtaleStructureSheafULift`. This file lifts the
(pre)sheaves of `𝒪_X`-modules of the universe `u` into that universe: the sections are `ULift`ed
together with the section rings.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.liftStructurePresheafModules`: the functor from
  presheaves of `𝒪_X`-modules to presheaves of modules over the lifted structure sheaf,
  sectionwise `ULift`.
* `AlgebraicGeometry.Space.PolynomialChart.liftStructureModules`: the same functor on sheaves.
* `AlgebraicGeometry.Space.PolynomialChart.sheafificationLiftIso` and
  `AlgebraicGeometry.Space.PolynomialChart.sheafificationLiftComplexIso`: lifting commutes with
  sheafification, of presheaves and of complexes of presheaves.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.preservesFiniteLimits_liftStructureModules` and
  `AlgebraicGeometry.Space.PolynomialChart.preservesFiniteColimits_liftStructureModules`: the
  lift is exact.
* `AlgebraicGeometry.Space.PolynomialChart.quasiIso_liftStructureModules_map`: the lift carries
  quasi-isomorphisms of complexes to quasi-isomorphisms.

## References

* [Stacks Project, Tag 08VA](https://stacks.math.columbia.edu/tag/08VA)
* [Stacks Project, Tag 08VD](https://stacks.math.columbia.edu/tag/08VD)
* [Stacks Project, Tag 08VM](https://stacks.math.columbia.edu/tag/08VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

/- The instances `CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat` and
`CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat` are stated for sections in
`max u v w`; offered a goal about `AddCommGrpCat.{u + 1}` on `X_étale` (objects in `Type (u + 1)`,
morphisms in `Type u`) instance search gets stuck on `u + 1 =?= max (u + 1) ?w` instead of moving
on to `AlgebraicGeometry.Space.hasSheafify_smallEtaleRingedTopos`, so they are switched off
here. -/
attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

/-- The sectionwise `ULift` of a presheaf of `𝒪_X`-modules on `X_étale`, over the lifted
structure sheaf. -/
def liftStructurePresheafModulesObj
    (M : PresheafOfModules.{u}
      (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O).obj) :
    PresheafOfModules.{u + 1}
      (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)).obj where
  obj V := ModuleCat.of (ULift.{u + 1}
      ((ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O).obj.obj V))
    (ULift.{u + 1} (M.obj V))
  map {V W} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars
      (R := ULift.{u + 1}
        ((ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O).obj.obj V))
      (S := ULift.{u + 1}
        ((ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O).obj.obj W))
      ((ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
        ⟨X, hX⟩)).obj.map f).hom).obj
      (ModuleCat.of (ULift.{u + 1}
        ((ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O).obj.obj W))
        (ULift.{u + 1} (M.obj W))))
    { toFun x := ULift.up (M.map f x.down)
      map_add' x y := congrArg ULift.up (map_add (M.map f).hom x.down y.down)
      map_smul' a x := congrArg ULift.up (M.map_smul f a.down x.down) }
  map_id V := by
    ext x
    apply ULift.ext
    change M.map (𝟙 V) x.down = x.down
    rw [M.map_id]
    rfl
  map_comp f g := by ext x; exact congrArg ULift.up (M.map_comp_apply f g x.down)

/-- **The lift of presheaves of `𝒪_X`-modules on `X_étale` to the universe of the site**:
sectionwise `ULift` of the sections, over the sectionwise `ULift` of `𝒪_X`. -/
def liftStructurePresheafModules :
    PresheafOfModules.{u}
        (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O).obj ⥤
      PresheafOfModules.{u + 1}
        (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
          ⟨X, hX⟩)).obj where
  obj M := liftStructurePresheafModulesObj Λ B hS X hX M
  map {M N} φ :=
    { app V := ModuleCat.ofHom
        { toFun x := ULift.up (φ.app V x.down)
          map_add' x y := congrArg ULift.up (map_add (φ.app V).hom x.down y.down)
          map_smul' a x := congrArg ULift.up ((φ.app V).hom.map_smul a.down x.down) }
      naturality {V W} f := by
        ext x
        exact congrArg ULift.up (PresheafOfModules.naturality_apply φ f x.down) }
  map_id M := by ext V x; rfl
  map_comp φ ψ := by ext V x; rfl

/-- On underlying presheaves of abelian groups the lift is postcomposition with
`AddCommGrpCat.uliftFunctor`. -/
theorem liftStructurePresheafModules_comp_toPresheaf :
    liftStructurePresheafModules Λ B hS X hX ⋙ PresheafOfModules.toPresheaf _ =
      PresheafOfModules.toPresheaf _ ⋙ (Functor.whiskeringRight _ _ _).obj
        AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  rfl

/-- The lift of presheaves of `𝒪_X`-modules is additive. -/
instance additive_liftStructurePresheafModules :
    (liftStructurePresheafModules Λ B hS X hX).Additive where
  map_add {_ _ _ _} := by ext V x; rfl

/-- The sectionwise `ULift` of a sheaf of `𝒪_X`-modules on `X_étale`, over the lifted structure
sheaf. -/
def liftStructureModulesObj
    (M : SheafOfModules.{u}
      (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O)) :
    SheafOfModules.{u + 1}
      (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)) where
  val := (liftStructurePresheafModules Λ B hS X hX).obj M.val
  isSheaf := Presheaf.isSheaf_comp_of_isSheaf _ M.val.presheaf
    AddCommGrpCat.uliftFunctor M.isSheaf

/-- **The lift of sheaves of `𝒪_X`-modules on `X_étale` to the universe of the site**:
sectionwise `ULift` of the sections, over the sectionwise `ULift` of `𝒪_X`. -/
def liftStructureModules :
    SheafOfModules.{u}
        (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O) ⥤
      SheafOfModules.{u + 1}
        (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)) where
  obj M := liftStructureModulesObj Λ B hS X hX M
  map {M N} φ := { val := (liftStructurePresheafModules Λ B hS X hX).map φ.val }
  map_id M := by ext V x; rfl
  map_comp φ ψ := by ext V x; rfl

/-- Lifting sheaves of `𝒪_X`-modules and then forgetting the module structure is forgetting it
and then lifting sheaves of abelian groups. -/
theorem liftStructureModules_comp_toSheaf :
    liftStructureModules Λ B hS X hX ⋙ SheafOfModules.toSheaf _ =
      SheafOfModules.toSheaf _ ⋙ sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  rfl

/-- The lift of sheaves of `𝒪_X`-modules is additive. -/
instance additive_liftStructureModules : (liftStructureModules Λ B hS X hX).Additive where
  map_add {_ _ _ _} := by ext V x; rfl

/-- The lift of sheaves of `𝒪_X`-modules preserves finite limits: they are computed on the
underlying presheaves of abelian groups, where the lift is postcomposition with
`AddCommGrpCat.uliftFunctor`. -/
theorem preservesFiniteLimits_liftStructureModules :
    PreservesFiniteLimits (liftStructureModules Λ B hS X hX) := by
  let G := SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf
    (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)).obj
  have : PreservesFiniteLimits (liftStructureModules Λ B hS X hX ⋙ G) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf
          (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O).obj) ⋙
        (Functor.whiskeringRight _ AddCommGrpCat.{u} AddCommGrpCat.{u + 1}).obj
          AddCommGrpCat.uliftFunctor.{u + 1, u})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (liftStructureModules Λ B hS X hX) G

/-- The lift of sheaves of `𝒪_X`-modules preserves finite colimits: read through the forgetful
functor to sheaves of abelian groups, which reflects them, it is the universe lift of abelian
sheaves, which commutes with sheafification. -/
theorem preservesFiniteColimits_liftStructureModules :
    PreservesFiniteColimits (liftStructureModules Λ B hS X hX) := by
  let F := liftStructureModules Λ B hS X hX
  let G := SheafOfModules.toSheaf
    (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩))
  have : PreservesFiniteColimits (F ⋙ G) := by
    rw [liftStructureModules_comp_toSheaf]
    have := Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{u}
      (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O)
    let L := sheafCompose (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
      AddCommGrpCat.uliftFunctor.{u + 1, u}
    have : PreservesColimitsOfSize.{u, u} L :=
      Stacks.Sheaves.UniverseLift.sheafCompose_uliftFunctor_preservesColimits.{u + 1, u, u,
        u + 1}
    have : PreservesColimitsOfSize.{0, 0} L := preservesSmallestColimits_of_preservesColimits _
    infer_instance
  have := Stacks.SheafOfModules.toSheaf_reflectsFiniteColimits.{u + 1}
    (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩))
  exact preservesFiniteColimits_of_reflects_of_preserves F G

/-- The lift of sheaves of `𝒪_X`-modules carries quasi-isomorphisms of complexes to
quasi-isomorphisms, being exact. -/
theorem quasiIso_liftStructureModules_map
    {K L : CochainComplex (SheafOfModules.{u}
      (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O)) ℤ}
    (φ : K ⟶ L) [_root_.QuasiIso φ] :
    _root_.QuasiIso
      (((liftStructureModules Λ B hS X hX).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have := preservesFiniteLimits_liftStructureModules Λ B hS X hX
  have := preservesFiniteColimits_liftStructureModules Λ B hS X hX
  infer_instance

/-- **Lifting commutes with sheafification.** The sheafification of the lift of a presheaf of
`𝒪_X`-modules on `X_étale` is the lift of its sheafification: the lift of the sheafification unit
is locally bijective, raising the universe of sections changing no image or equalizer sieve. -/
def sheafificationLiftIso
    (P : PresheafOfModules.{u}
      (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O).obj) :
    (PresheafOfModules.sheafification.{u + 1}
      (𝟙 (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
        ⟨X, hX⟩)).obj)).obj ((liftStructurePresheafModules Λ B hS X hX).obj P) ≅
      (liftStructureModules Λ B hS X hX).obj
        ((PresheafOfModules.sheafification.{u}
          (𝟙 (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS
            ⟨X, hX⟩).O).obj)).obj P) :=
  let η := PresheafOfModules.sheafificationHomEquiv.{u}
    (𝟙 (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O).obj)
    (𝟙 ((PresheafOfModules.sheafification.{u}
      (𝟙 (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS
        ⟨X, hX⟩).O).obj)).obj P))
  let ηu : (liftStructurePresheafModules Λ B hS X hX).obj P ⟶
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
          ⟨X, hX⟩)).obj)).obj
        ((liftStructureModules Λ B hS X hX).obj
          ((PresheafOfModules.sheafification.{u}
            (𝟙 (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS
              ⟨X, hX⟩).O).obj)).obj P)) :=
    PresheafOfModules.homMk
      (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map η)
        AddCommGrpCat.uliftFunctor.{u + 1, u})
      (fun V r m => congrArg ULift.up ((η.app V).hom.map_smul r.down m.down))
  have hη : (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X).W
      ((PresheafOfModules.toPresheaf _).map η) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
    exact MorphismProperty.comp_mem _ _ _
      ((SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X).W_toSheafify _)
      (ObjectProperty.isLocal_of_isIso _ (𝟙 _))
  have := hη.isLocallyInjective
  have := hη.isLocallySurjective
  @asIso _ _ _ _ _ (Stacks.SheafOfModules.SliceSheafification.isIso_sheafificationHomEquiv_symm
    (𝟙 _) ηu
    (show Presheaf.IsLocallyInjective _ (Functor.whiskerRight
      ((PresheafOfModules.toPresheaf _).map η) AddCommGrpCat.uliftFunctor.{u + 1, u}) from
      inferInstance)
    (show Presheaf.IsLocallySurjective _ (Functor.whiskerRight
      ((PresheafOfModules.toPresheaf _).map η) AddCommGrpCat.uliftFunctor.{u + 1, u}) from
      inferInstance))

/-- `sheafificationLiftIso` is natural in the presheaf of modules. -/
theorem sheafificationLiftIso_hom_naturality
    {P P' : PresheafOfModules.{u}
      (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O).obj}
    (g : P ⟶ P') :
    (PresheafOfModules.sheafification.{u + 1}
        (𝟙 (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
          ⟨X, hX⟩)).obj)).map ((liftStructurePresheafModules Λ B hS X hX).map g) ≫
        (sheafificationLiftIso Λ B hS X hX P').hom =
      (sheafificationLiftIso Λ B hS X hX P).hom ≫ (liftStructureModules Λ B hS X hX).map
        ((PresheafOfModules.sheafification.{u}
          (𝟙 (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS
            ⟨X, hX⟩).O).obj)).map g) := by
  apply ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
      ⟨X, hX⟩)).obj)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
  change _ ≫ PresheafOfModules.sheafificationHomEquiv _
      ((PresheafOfModules.sheafificationHomEquiv _).symm _) =
    PresheafOfModules.sheafificationHomEquiv _
      ((PresheafOfModules.sheafificationHomEquiv _).symm _) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext V x
  have h := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS
      ⟨X, hX⟩).O).obj)).unit.naturality g
  exact congrArg ULift.up (ConcreteCategory.congr_hom (congrArg (fun φ => φ.app V) h) x.down)

/-- The lift of presheaves of `𝒪_X`-modules preserves zero morphisms. -/
instance preservesZeroMorphisms_liftStructurePresheafModules :
    (liftStructurePresheafModules Λ B hS X hX).PreservesZeroMorphisms :=
  ⟨fun _ _ => by ext V x; rfl⟩

/-- Sheafification of presheaves of `𝒪_X`-modules on `X_étale` preserves zero morphisms. -/
instance preservesZeroMorphisms_sheafification_structureSheaf :
    (PresheafOfModules.sheafification.{u}
      (𝟙 (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS
        ⟨X, hX⟩).O).obj)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- Sheafification of presheaves of modules over the lifted structure sheaf preserves zero
morphisms. -/
instance preservesZeroMorphisms_sheafification_structureSheafULift :
    (PresheafOfModules.sheafification.{u + 1}
      (𝟙 (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
        ⟨X, hX⟩)).obj)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- Lifting commutes with the degreewise sheafification of complexes of presheaves of
`𝒪_X`-modules on `X_étale`. -/
def sheafificationLiftComplexIso
    (K : CochainComplex (PresheafOfModules.{u}
      (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O).obj) ℤ) :
    ((PresheafOfModules.sheafification.{u + 1}
        (𝟙 (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
          ⟨X, hX⟩)).obj)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((liftStructurePresheafModules Λ B hS X hX).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      ((liftStructureModules Λ B hS X hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((PresheafOfModules.sheafification.{u}
          (𝟙 (ringSheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS
            ⟨X, hX⟩).O).obj)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun j => sheafificationLiftIso Λ B hS X hX (K.X j))
    (fun i j _ => (sheafificationLiftIso_hom_naturality Λ B hS X hX (K.d i j)).symm)

end AlgebraicGeometry.Space.PolynomialChart
