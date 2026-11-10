module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartRingedTopoi

/-!
# Sheaves of `𝒪_X`-modules presented in the coefficient universe of the chart topos

The site of polynomial charts of a scheme `X` over a ring `Λ` (Tag 08VA) has its sheaves in a
coefficient universe containing `u + 1`, and there `𝒪_X` is presented by the canonical `ULift` of
its section rings, `AlgebraicGeometry.PolynomialChart.liftedStructureSheaf`. This file lifts the
sheaves of `𝒪_X`-modules of the scheme's own universe into that universe: the sections are
`ULift`ed together with the section rings.

## Main definitions

* `AlgebraicGeometry.PolynomialChart.liftStructureModules`: the functor from sheaves of
  `𝒪_X`-modules to sheaves of modules over the lifted structure sheaf, sectionwise `ULift`.

## References

* [Stacks Project, Tag 08VA](https://stacks.math.columbia.edu/tag/08VA)
* [Stacks Project, Tag 08T9](https://stacks.math.columbia.edu/tag/08T9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u w

namespace AlgebraicGeometry.PolynomialChart

variable (X : Scheme.{u})

/-- The sectionwise `ULift` of a presheaf of `𝒪_X`-modules, over the lifted structure sheaf. -/
def liftStructurePresheafModulesObj
    (M : PresheafOfModules.{u} (ringSheaf X.sheaf).obj) :
    PresheafOfModules.{max w (u + 1)} (ringSheaf (liftedStructureSheaf.{u, w} X)).obj where
  obj V := ModuleCat.of (ULift.{max w (u + 1)} ((ringSheaf X.sheaf).obj.obj V))
    (ULift.{max w (u + 1)} (M.obj V))
  map {V W} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars
      (R := ULift.{max w (u + 1)} ((ringSheaf X.sheaf).obj.obj V))
      (S := ULift.{max w (u + 1)} ((ringSheaf X.sheaf).obj.obj W))
      ((ringSheaf (liftedStructureSheaf.{u, w} X)).obj.map f).hom).obj
      (ModuleCat.of (ULift.{max w (u + 1)} ((ringSheaf X.sheaf).obj.obj W))
        (ULift.{max w (u + 1)} (M.obj W))))
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

/-- The lift of presheaves of `𝒪_X`-modules to the coefficient universe of the chart topos:
sectionwise `ULift` of the sections, over the sectionwise `ULift` of `𝒪_X`. -/
def liftStructurePresheafModules :
    PresheafOfModules.{u} (ringSheaf X.sheaf).obj ⥤
      PresheafOfModules.{max w (u + 1)} (ringSheaf (liftedStructureSheaf.{u, w} X)).obj where
  obj M := liftStructurePresheafModulesObj.{u, w} X M
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
    liftStructurePresheafModules.{u, w} X ⋙ PresheafOfModules.toPresheaf _ =
      PresheafOfModules.toPresheaf _ ⋙ (Functor.whiskeringRight _ _ _).obj
        AddCommGrpCat.uliftFunctor.{max w (u + 1), u} :=
  rfl

/-- The lift of presheaves of `𝒪_X`-modules is additive. -/
instance additive_liftStructurePresheafModules :
    (liftStructurePresheafModules.{u, w} X).Additive where
  map_add {_ _ _ _} := by ext V x; rfl

/-- The sectionwise `ULift` of a sheaf of `𝒪_X`-modules, over the lifted structure sheaf. -/
def liftStructureModulesObj
    (M : SheafOfModules.{u} (ringSheaf X.sheaf)) :
    SheafOfModules.{max w (u + 1)}
      (ringSheaf (liftedStructureSheaf.{u, w} X)) where
  val := (liftStructurePresheafModules.{u, w} X).obj M.val
  isSheaf := Presheaf.isSheaf_comp_of_isSheaf _ M.val.presheaf
    AddCommGrpCat.uliftFunctor M.isSheaf

/-- The lift of sheaves of `𝒪_X`-modules to the coefficient universe of the chart topos:
sectionwise `ULift` of the sections, over the sectionwise `ULift` of `𝒪_X`. -/
def liftStructureModules :
    SheafOfModules.{u} (ringSheaf X.sheaf) ⥤
      SheafOfModules.{max w (u + 1)}
        (ringSheaf (liftedStructureSheaf.{u, w} X)) where
  obj M := liftStructureModulesObj.{u, w} X M
  map {M N} φ := { val := (liftStructurePresheafModules.{u, w} X).map φ.val }
  map_id M := by ext V x; rfl
  map_comp φ ψ := by ext V x; rfl

/-- Lifting sheaves of `𝒪_X`-modules and then forgetting the module structure is forgetting it
and then lifting sheaves of abelian groups. -/
theorem liftStructureModules_comp_toSheaf :
    liftStructureModules.{u, w} X ⋙ SheafOfModules.toSheaf _ =
      SheafOfModules.toSheaf _ ⋙ sheafCompose _ AddCommGrpCat.uliftFunctor.{max w (u + 1), u} :=
  rfl

/-- The lift of sheaves of `𝒪_X`-modules is additive. -/
instance additive_liftStructureModules : (liftStructureModules.{u, w} X).Additive where
  map_add {_ _ _ _} := by ext V x; rfl

/-- The lift of sheaves of `𝒪_X`-modules preserves finite limits. -/
theorem preservesFiniteLimits_liftStructureModules :
    PreservesFiniteLimits (liftStructureModules.{u, w} X) := by
  let G := SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf
    (ringSheaf (liftedStructureSheaf.{u, w} X)).obj
  have : PreservesFiniteLimits (liftStructureModules.{u, w} X ⋙ G) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf (ringSheaf X.sheaf).obj) ⋙
        (Functor.whiskeringRight _ AddCommGrpCat.{u} AddCommGrpCat.{max w (u + 1)}).obj
          AddCommGrpCat.uliftFunctor.{max w (u + 1), u})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (liftStructureModules.{u, w} X) G

/-- The lift of sheaves of `𝒪_X`-modules preserves finite colimits. -/
theorem preservesFiniteColimits_liftStructureModules :
    PreservesFiniteColimits (liftStructureModules.{u, w} X) := by
  have : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max w (u + 1)} :=
    CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat.{u, u, max w (u + 1)} _
  have : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max w (u + 1)} :=
    CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat.{u, u, max w (u + 1)} _
  let F := liftStructureModules.{u, w} X
  let G := SheafOfModules.toSheaf (ringSheaf (liftedStructureSheaf.{u, w} X))
  have : PreservesFiniteColimits (F ⋙ G) := by
    rw [liftStructureModules_comp_toSheaf]
    have := Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{u} (ringSheaf X.sheaf)
    let L := sheafCompose (Opens.grothendieckTopology X)
      AddCommGrpCat.uliftFunctor.{max w (u + 1), u}
    have : PreservesColimitsOfSize.{u, u} L :=
      Stacks.Sheaves.UniverseLift.sheafCompose_uliftFunctor_preservesColimits.{u, u, u,
        max w (u + 1)}
    have : PreservesColimitsOfSize.{0, 0} L := preservesSmallestColimits_of_preservesColimits _
    infer_instance
  have := Stacks.SheafOfModules.toSheaf_reflectsFiniteColimits.{max w (u + 1)}
    (ringSheaf (liftedStructureSheaf.{u, w} X))
  exact preservesFiniteColimits_of_reflects_of_preserves F G

/-- The lift of sheaves of `𝒪_X`-modules carries quasi-isomorphisms of complexes to
quasi-isomorphisms. -/
theorem quasiIso_liftStructureModules_map
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max w (u + 1)}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max w (u + 1)}]
    {K L : CochainComplex (SheafOfModules.{u} (ringSheaf X.sheaf)) ℤ} (φ : K ⟶ L)
    [_root_.QuasiIso φ] :
    _root_.QuasiIso
      (((liftStructureModules.{u, w} X).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have := preservesFiniteLimits_liftStructureModules.{u, w} X
  have := preservesFiniteColimits_liftStructureModules.{u, w} X
  infer_instance

/-- The sheafification of the lift of a presheaf of `𝒪_X`-modules is the lift of its
sheafification. -/
def sheafificationLiftIso
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max w (u + 1)}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max w (u + 1)}]
    (P : PresheafOfModules.{u} (ringSheaf X.sheaf).obj) :
    (PresheafOfModules.sheafification.{max w (u + 1)}
      (𝟙 (ringSheaf (liftedStructureSheaf.{u, w} X)).obj)).obj
        ((liftStructurePresheafModules.{u, w} X).obj P) ≅
      (liftStructureModules.{u, w} X).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (ringSheaf X.sheaf).obj)).obj P) :=
  let η := PresheafOfModules.sheafificationHomEquiv.{u} (𝟙 (ringSheaf X.sheaf).obj)
    (𝟙 ((PresheafOfModules.sheafification.{u} (𝟙 (ringSheaf X.sheaf).obj)).obj P))
  let ηu : (liftStructurePresheafModules.{u, w} X).obj P ⟶
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 (ringSheaf (liftedStructureSheaf.{u, w} X)).obj)).obj
        ((liftStructureModules.{u, w} X).obj
          ((PresheafOfModules.sheafification.{u} (𝟙 (ringSheaf X.sheaf).obj)).obj P)) :=
    PresheafOfModules.homMk
      (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map η)
        AddCommGrpCat.uliftFunctor.{max w (u + 1), u})
      (fun V r m => congrArg ULift.up ((η.app V).hom.map_smul r.down m.down))
  have hη : (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map η) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
    exact MorphismProperty.comp_mem _ _ _ ((Opens.grothendieckTopology X).W_toSheafify _)
      (ObjectProperty.isLocal_of_isIso _ (𝟙 _))
  have := hη.isLocallyInjective
  have := hη.isLocallySurjective
  @asIso _ _ _ _ _ (Stacks.SheafOfModules.SliceSheafification.isIso_sheafificationHomEquiv_symm
    (𝟙 _) ηu
    (show Presheaf.IsLocallyInjective _ (Functor.whiskerRight
      ((PresheafOfModules.toPresheaf _).map η) AddCommGrpCat.uliftFunctor.{max w (u + 1), u}) from
      inferInstance)
    (show Presheaf.IsLocallySurjective _ (Functor.whiskerRight
      ((PresheafOfModules.toPresheaf _).map η) AddCommGrpCat.uliftFunctor.{max w (u + 1), u}) from
      inferInstance))

/-- `sheafificationLiftIso` is natural in the presheaf of modules. -/
theorem sheafificationLiftIso_hom_naturality
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max w (u + 1)}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max w (u + 1)}]
    {P P' : PresheafOfModules.{u} (ringSheaf X.sheaf).obj} (g : P ⟶ P') :
    (PresheafOfModules.sheafification.{max w (u + 1)}
        (𝟙 (ringSheaf (liftedStructureSheaf.{u, w} X)).obj)).map
          ((liftStructurePresheafModules.{u, w} X).map g) ≫
        (sheafificationLiftIso.{u, w} X P').hom =
      (sheafificationLiftIso.{u, w} X P).hom ≫ (liftStructureModules.{u, w} X).map
        ((PresheafOfModules.sheafification.{u} (𝟙 (ringSheaf X.sheaf).obj)).map g) := by
  apply ((PresheafOfModules.sheafificationAdjunction.{max w (u + 1)}
    (𝟙 (ringSheaf (liftedStructureSheaf.{u, w} X)).obj)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
  change _ ≫ PresheafOfModules.sheafificationHomEquiv _
      ((PresheafOfModules.sheafificationHomEquiv _).symm _) =
    PresheafOfModules.sheafificationHomEquiv _
      ((PresheafOfModules.sheafificationHomEquiv _).symm _) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext V x
  exact congrArg ULift.up (ConcreteCategory.congr_hom (congrArg (fun φ => φ.app V)
    ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ringSheaf X.sheaf).obj)).unit.naturality
      g)) x.down)

/-- The lift of presheaves of `𝒪_X`-modules preserves zero morphisms. -/
instance preservesZeroMorphisms_liftStructurePresheafModules :
    (liftStructurePresheafModules.{u, w} X).PreservesZeroMorphisms :=
  ⟨fun _ _ => by ext V x; rfl⟩

/-- Sheafification of presheaves of `𝒪_X`-modules preserves zero morphisms. -/
instance preservesZeroMorphisms_sheafification_structureSheaf :
    (PresheafOfModules.sheafification.{u} (𝟙 (ringSheaf X.sheaf).obj)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- Sheafification of presheaves of modules over the lifted structure sheaf preserves zero
morphisms. -/
theorem preservesZeroMorphisms_sheafification_liftedStructureSheaf
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max w (u + 1)}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max w (u + 1)}] :
    (PresheafOfModules.sheafification.{max w (u + 1)}
      (𝟙 (ringSheaf (liftedStructureSheaf.{u, w} X)).obj)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

attribute [local instance] preservesZeroMorphisms_sheafification_liftedStructureSheaf

/-- Lifting commutes with the degreewise sheafification of complexes of presheaves of
`𝒪_X`-modules. -/
def sheafificationLiftComplexIso
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max w (u + 1)}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max w (u + 1)}]
    (K : CochainComplex (PresheafOfModules.{u} (ringSheaf X.sheaf).obj) ℤ) :
    ((PresheafOfModules.sheafification.{max w (u + 1)}
        (𝟙 (ringSheaf (liftedStructureSheaf.{u, w} X)).obj)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((liftStructurePresheafModules.{u, w} X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      ((liftStructureModules.{u, w} X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((PresheafOfModules.sheafification.{u} (𝟙 (ringSheaf X.sheaf).obj)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun j => sheafificationLiftIso.{u, w} X (K.X j))
    (fun i j _ => (sheafificationLiftIso_hom_naturality.{u, w} X (K.d i j)).symm)

end AlgebraicGeometry.PolynomialChart
