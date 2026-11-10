module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessGlobalSectionsForget
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLinear
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDualGlobalFunctoriality
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Pushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroGlobal
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear

/-!
# Hom groups as degree-zero cohomology over `Γ(Spec k, 𝒪)`

Let `k` be a field and let `X` be a scheme over `Spec k`. The degree-zero Künneth statement of
`StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroGlobal` is about
`AlgebraicGeometry.degreeZeroSectionsField`, the degree-zero cohomology of the derived sections
`RΓ(X, -)` with values in `D(Γ(Spec k, 𝒪))` at which the global Künneth morphism of
[Stacks, Tag 0G7V] is stated, read over `k`. The identification of [Stacks, Tag 08DK] that turns
a Hom group into a degree-zero cohomology group is available `k`-linearly as
`Stacks.AlgebraicGeometry.ProperSupportCoherent.extAddEquiv` with
`Stacks.AlgebraicGeometry.ProperSupportCoherent.extAddEquiv_map_smul`, but for the other
spelling of `RΓ(X, -)`, `AlgebraicGeometry.derivedGlobalSectionsOver`, whose values are in
`D(k)`. This file identifies the two spellings and composes.

## Main definitions

* `AlgebraicGeometry.derivedGlobalSectionsOverIso`: `RΓ(X, -) : D(𝒪_X) ⥤ D(k)` is the derived
  sections over the base followed by restriction of scalars along `k ≅ Γ(Spec k, 𝒪)`.
* `AlgebraicGeometry.homologyZeroGlobalSectionsOverIso`: the same in degree zero, as an
  isomorphism of `k`-modules with `AlgebraicGeometry.degreeZeroSectionsField`.
* `AlgebraicGeometry.homLinearEquivDegreeZeroSections`: **[Stacks, Tag 08DK] in the spelling of
  the degree-zero Künneth statement**, the `k`-linear identification
  `Hom_{D(𝒪_X)}(N, N') ≃ H⁰RΓ(X, R𝓗om(N, N'))`.
* `AlgebraicGeometry.degreeZeroClassAddEquiv`: a morphism `𝒪_X ⟶ E` as a class in `H⁰RΓ(X, E)`.
* `AlgebraicGeometry.homTranspose`: the transpose `𝒪_X ⟶ R𝓗om(N, N')` of a morphism `N ⟶ N'`.

## Main results

* `AlgebraicGeometry.homLinearEquivDegreeZeroSections_eq_class`: the identification sends `φ` to
  the class of its transpose.
* `AlgebraicGeometry.homLinearEquivDegreeZeroSections_comp`: the identification is natural in the
  target, through the map `R𝓗om(N, χ)` induces on `H⁰RΓ(X, -)`.
* `AlgebraicGeometry.homTranspose_eq`, `AlgebraicGeometry.homTranspose_spec`: the transpose is
  Stacks 08JA applied to the inverse of [Stacks, Tag 08DK], as in
  `AlgebraicGeometry.RingedSite.derivedIdentitySection`.

## Implementation notes

The `k`-linearity of [Stacks, Tag 08DK] is proved here and not imported from
`StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLinear`, whose import cone
does not build at this base; the argument is the one of that file and of
`Stacks.AlgebraicGeometry.ProperSupportCoherent.extAddEquiv_map_smul`.

The evaluation law `(homTranspose φ ▷ N) ≫ ev = λ_N ≫ φ` is the unit law
`Stacks.SheafOfModules.derivedSheafHomCounit_unit_law_monoidal'` at `homTranspose φ` together
with `homTranspose_spec`; it is not restated here because the monoidal structure of
[Stacks, Tag 0FPT] lives on the `Stacks.SheafOfModules.StructureSheafModules` spelling of
`D(𝒪_X)`, and identifying the Hom groups of that spelling with those of the scheme's spelling
inside one equation exceeds the elaborator's recursion budget.

## References

* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.GlobalKunneth (baseRing sectionsOverBase)
open Stacks.Cohomology.DerivedSectionsLeray
  (preimageSections homotopyPreimageSections derivedPreimageSections derivedPreimageSectionsUnit)

variable (k : Type u) [Field k] (X : Over (Spec (.of k)))

/-- Restriction of scalars along `k ≅ Γ(Spec k, 𝒪)`, from `Γ(Spec k, 𝒪)`-modules to
`k`-vector spaces. -/
abbrev gammaRestrict :
    ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace) ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars.{u} (gammaSectionsInv k)

/-- The derived sections over the base followed by restriction of scalars along
`k ≅ Γ(Spec k, 𝒪)`, as a functor out of `D(𝒪_X)` in the scheme's spelling of `𝒪_X`-modules. -/
abbrev sectionsOverBaseField : DerivedCategory X.left.Modules ⥤ DerivedCategory (ModuleCat.{u} k) :=
  sectionsOverBase X.hom.toLRSHom.toShHom ⋙ (gammaRestrict k).mapDerivedCategory

/-- Restriction of scalars along `k ≅ Γ(Spec k, 𝒪)` is additive. -/
instance gammaRestrict_additive : (gammaRestrict k).Additive := inferInstance

/-- The functor of sections over the whole space `X` of an `𝒪_X`-module, valued in
`Γ(Spec k, 𝒪)`-modules, is additive. -/
instance preimageSectionsTop_additive :
    (preimageSections X.hom.toLRSHom.toShHom ⊤).Additive where
  map_add := rfl

/-- The comparison from termwise `k`-linear global sections to the derived sections over the
base with scalars restricted along `k ≅ Γ(Spec k, 𝒪)`, read on homotopy categories. -/
def globalSectionsOverRestrictUnitIso :
    homotopyGlobalSectionsOver X.hom ≅
      ((homotopyPreimageSections X.hom.toLRSHom.toShHom ⊤ ⋙ (gammaRestrict k).mapDerivedCategory :
        HomotopyCategory X.left.Modules (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{u} k))) :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (F := preimageSections X.hom.toLRSHom.toShHom ⊤)
        (G := gammaRestrict k) (H := preimageSections X.hom.toLRSHom.toShHom ⊤ ⋙ gammaRestrict k)
        (Iso.refl _) (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator
      ((preimageSections X.hom.toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      ((gammaRestrict k).mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft
      ((preimageSections X.hom.toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      (gammaRestrict k).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator
      ((preimageSections X.hom.toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh (gammaRestrict k).mapDerivedCategory).symm

/-- The comparison `Γ(X, -) ⟶ RΓ(X, -)`, with `RΓ(X, -)` the derived sections over the base read
over `k`. -/
def globalSectionsOverRestrictUnit :
    homotopyGlobalSectionsOver X.hom ⟶ DerivedCategory.Qh ⋙ sectionsOverBaseField k X :=
  (globalSectionsOverRestrictUnitIso k X).hom ≫
    Functor.whiskerRight (derivedPreimageSectionsUnit X.hom.toLRSHom.toShHom ⊤)
      (gammaRestrict k).mapDerivedCategory ≫
    (Functor.associator DerivedCategory.Qh (sectionsOverBase X.hom.toLRSHom.toShHom)
      (gammaRestrict k).mapDerivedCategory).hom

/-- **The derived sections over the base, read over `k`, are a right derived functor of
`k`-linear global sections.** Restriction of scalars is exact, and at a K-injective complex the
unit of the derived sections over the base is invertible. -/
theorem isRightDerivedFunctor_sectionsOverBase_gammaRestrict :
    (sectionsOverBaseField k X).IsRightDerivedFunctor (globalSectionsOverRestrictUnit k X)
      (HomotopyCategory.quasiIso X.left.Modules (ComplexShape.up ℤ)) := by
  refine
   Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective
      X.left.toRingedSpace) DerivedCategory.Qh _ _ fun I hI => ?_
  have := hI
  have h : IsIso ((derivedPreimageSectionsUnit X.hom.toLRSHom.toShHom ⊤).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace))
        (ComplexShape.up ℤ)).obj I)) :=
    Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective
      (preimageSections X.hom.toLRSHom.toShHom ⊤) I
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_)
  · exact ((globalSectionsOverRestrictUnitIso k X).app _).isIso_hom
  · exact Functor.map_isIso (gammaRestrict k).mapDerivedCategory _
  · infer_instance

/-- **`RΓ(X, -) : D(𝒪_X) ⥤ D(k)` is the derived sections over the base followed by restriction
of scalars along `k ≅ Γ(Spec k, 𝒪)`.** Both are right derived functors of `k`-linear global
sections, so the canonical comparison between them is invertible. -/
def derivedGlobalSectionsOverIso :
    derivedGlobalSectionsOver X.hom ≅ sectionsOverBaseField k X :=
  haveI := isRightDerivedFunctor_sectionsOverBase_gammaRestrict k X
  @asIso _ _ _ _
    ((derivedGlobalSectionsOver X.hom).rightDerivedDesc (derivedGlobalSectionsOverUnit X.hom)
      (HomotopyCategory.quasiIso X.left.Modules (ComplexShape.up ℤ)) _
      (globalSectionsOverRestrictUnit k X))
    ((Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
      (derivedGlobalSectionsOverUnit X.hom) _ _ (globalSectionsOverRestrictUnit k X)).1
      (isRightDerivedFunctor_sectionsOverBase_gammaRestrict k X))

/-- **The degree-zero cohomology of `RΓ(X, -)` over `k` is `degreeZeroSectionsField`**, naturally:
the degree-zero cohomology of the derived sections over the base, with scalars restricted along
`k ≅ Γ(Spec k, 𝒪)`. -/
def homologyZeroGlobalSectionsOverNatIso :
    derivedGlobalSectionsOver X.hom ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0 ≅
      sectionsOverBase X.hom.toLRSHom.toShHom ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0 ⋙ gammaRestrict k :=
  Functor.isoWhiskerRight (derivedGlobalSectionsOverIso k X)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sectionsOverBase X.hom.toLRSHom.toShHom)
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso (gammaRestrict k) 0)

/-- `homologyZeroGlobalSectionsOverNatIso` at one object. -/
abbrev homologyZeroGlobalSectionsOverIso (E : DerivedCategory X.left.Modules) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
        ((derivedGlobalSectionsOver X.hom).obj E) ≅
      degreeZeroSectionsField k X.hom E :=
  (homologyZeroGlobalSectionsOverNatIso k X).app E

/-! ### [Stacks, Tag 08DK] in the spelling of the degree-zero Künneth statement -/

open Stacks.AlgebraicGeometry.ProperSupportCoherent (homologyZeroForgetIso homologyZeroForgetNatIso)

/-- The comparison of `k`-linear with abelian-group-valued degree-zero hypercohomology,
`homologyZeroForgetIso`, is natural. -/
private theorem homologyZeroForgetIso_hom_naturality {E E' : DerivedCategory X.left.Modules}
    (g : E ⟶ E')
    (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
      ((derivedGlobalSectionsOver X.hom).obj E)) :
    (homologyZeroForgetIso X.hom E').hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          ((derivedGlobalSectionsOver X.hom).map g)) y) =
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
          (Stacks.SheafOfModules.ringedSite X.left.sheaf)).map g))
        ((homologyZeroForgetIso X.hom E).hom y) :=
  ((CategoryTheory.comp_apply
      ((derivedGlobalSectionsOver X.hom ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0 ⋙
        forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).map g)
      ((homologyZeroForgetNatIso X.hom).hom.app _) y).symm.trans
    (ConcreteCategory.congr_hom ((homologyZeroForgetNatIso X.hom).hom.naturality g) y)).trans
      (CategoryTheory.comp_apply ((homologyZeroForgetNatIso X.hom).hom.app _)
        ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
          (Stacks.SheafOfModules.ringedSite X.left.sheaf) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map g) y)

/-- `R𝓗om_{𝒪_X}(N, N')` on a scheme over `Spec k`, in the scheme's spelling of `D(𝒪_X)`. -/
abbrev derivedSheafHomObj (N N' : DerivedCategory X.left.Modules) :
    DerivedCategory X.left.Modules :=
  ((Stacks.SheafOfModules.derivedSheafHom X.left.sheaf).obj (op N)).obj N'

/-- `R𝓗om_{𝒪_X}(N, -)` as an endofunctor of `D(𝒪_X)` in the scheme's spelling of `𝒪_X`-modules,
so that the `k`-linear structure of `AlgebraicGeometry.modulesLinear` applies to its morphisms. -/
def sheafHomOutOf (N : DerivedCategory X.left.Modules) :
    DerivedCategory X.left.Modules ⥤ DerivedCategory X.left.Modules :=
  (Stacks.SheafOfModules.derivedSheafHom X.left.sheaf).obj (op N)

/-- [Stacks, Tag 08DK] on the scheme `X`,
`Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv`, with its Hom group written in the
scheme's spelling of `D(𝒪_X)`, where instance search finds its additive structure. -/
abbrev derivedSheafHomGlobalSectionsEquivScheme (N N' : DerivedCategory X.left.Modules) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
          (Stacks.SheafOfModules.ringedSite X.left.sheaf)).obj (derivedSheafHomObj k X N N')) :
        Type u) ≃+ (N ⟶ N') :=
  RingedSite.derivedSheafHomGlobalSectionsEquiv (Stacks.SheafOfModules.ringedSite X.left.sheaf) N N'

/-- **[Stacks, Tag 08DK], additively, in the spelling of the degree-zero Künneth statement.**
`H⁰RΓ(X, R𝓗om(N, N'))`, read over `k` as `AlgebraicGeometry.degreeZeroSectionsField`, is
`Hom_{D(𝒪_X)}(N, N')`. It is the identification
`Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv` of Tag 08DK, read through the
comparison of `k`-linear with abelian-group-valued degree-zero hypercohomology and through
`AlgebraicGeometry.homologyZeroGlobalSectionsOverIso`. -/
def degreeZeroSectionsHomAddEquiv (N N' : DerivedCategory X.left.Modules) :
    (degreeZeroSectionsField k X.hom (derivedSheafHomObj k X N N') : Type u) ≃+ (N ⟶ N') where
  toFun x := derivedSheafHomGlobalSectionsEquivScheme k X N N'
    ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N')).hom
      ((homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N')).inv.hom x))
  invFun φ := (homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N')).hom.hom
    ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N')).inv
      ((derivedSheafHomGlobalSectionsEquivScheme k X N N').symm φ))
  left_inv x := by
    simp only [AddEquiv.symm_apply_apply, Iso.hom_inv_id_apply]
    exact Iso.inv_hom_id_apply (homologyZeroGlobalSectionsOverIso k X _) x
  right_inv φ := by
    simp only [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply]
    exact AddEquiv.apply_symm_apply _ φ
  map_add' x y := by
    simp only [map_add]

/-- The identification of [Stacks, Tag 08DK] in this spelling, unfolded. -/
theorem degreeZeroSectionsHomAddEquiv_apply (N N' : DerivedCategory X.left.Modules)
    (x : degreeZeroSectionsField k X.hom (derivedSheafHomObj k X N N')) :
    degreeZeroSectionsHomAddEquiv k X N N' x =
      derivedSheafHomGlobalSectionsEquivScheme k X N N'
        ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N')).hom
          ((homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N')).inv.hom x)) :=
  rfl

/-- [Stacks, Tag 08DK] on a class over `k` is natural in the target: `R𝓗om(N, χ)` acts on
`Hom(N, N')` by postcomposition with `χ`. -/
private theorem derivedSheafHomGlobalSectionsEquivScheme_map (N : DerivedCategory X.left.Modules)
    {N' N'' : DerivedCategory X.left.Modules} (χ : N' ⟶ N'')
    (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
      ((derivedGlobalSectionsOver X.hom).obj (derivedSheafHomObj k X N N'))) :
    derivedSheafHomGlobalSectionsEquivScheme k X N N''
        ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N'')).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
            ((derivedGlobalSectionsOver X.hom).map ((sheafHomOutOf k X N).map χ))) y)) =
      derivedSheafHomGlobalSectionsEquivScheme k X N N'
        ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N')).hom y) ≫ χ :=
  (congrArg (derivedSheafHomGlobalSectionsEquivScheme k X N N'')
    (homologyZeroForgetIso_hom_naturality k X _ y)).trans
      (Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv_naturality_target
        X.left.sheaf N χ ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N')).hom y))

/-- **The identification of [Stacks, Tag 08DK] carries the action of `k` on
`H⁰RΓ(X, R𝓗om(N, N'))` to the action of `k` on `Hom_{D(𝒪_X)}(N, N')`**, the latter for the
canonical `k`-linear structure `AlgebraicGeometry.modulesLinear` of `𝒪_X`-modules.

The identification is natural in `N'`; `R𝓗om(N, -)` and `RΓ(X, -)` both carry multiplication by
a scalar to multiplication by that scalar; and the action of a scalar on `Hom(N, N')` is
postcomposition with multiplication by it on `N'`. -/
theorem degreeZeroSectionsHomAddEquiv_smul (N N' : DerivedCategory X.left.Modules) (a : k)
    (x : degreeZeroSectionsField k X.hom (derivedSheafHomObj k X N N')) :
    letI : Linear k X.left.Modules := modulesLinear k X
    degreeZeroSectionsHomAddEquiv k X N N' (a • x) =
      a • degreeZeroSectionsHomAddEquiv k X N N' x := by
  let : Linear k X.left.Modules := modulesLinear k X
  set y := (homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N')).inv.hom x
  have hy : (homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N')).inv.hom (a • x) =
      a • y :=
    map_smul _ a x
  have hsmul : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
      ((derivedGlobalSectionsOver X.hom).map ((sheafHomOutOf k X N).map (a • 𝟙 N'))) y =
        a • y := by
    rw [show (sheafHomOutOf k X N).map (a • 𝟙 N') = a • 𝟙 ((sheafHomOutOf k X N).obj N') from
        derivedSheafHomFunctor_map_smul_id X N N' a, derivedGlobalSectionsOver_map_smul_id,
      Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
    rfl
  rw [degreeZeroSectionsHomAddEquiv_apply, degreeZeroSectionsHomAddEquiv_apply, hy, ← hsmul]
  exact (derivedSheafHomGlobalSectionsEquivScheme_map k X N (a • 𝟙 N') y).trans
    ((fun g : N ⟶ N' => show g ≫ (a • 𝟙 N') = a • g by
      rw [Linear.comp_smul, Category.comp_id]) _)

/-- **[Stacks, Tag 08DK] in the spelling of the degree-zero Künneth statement, `k`-linearly.**
For a scheme `X` over a field `k` and `N, N' ∈ D(𝒪_X)`,

`Hom_{D(𝒪_X)}(N, N') ≃ H⁰RΓ(X, R𝓗om(N, N'))`

as `k`-vector spaces, where the right-hand side is `AlgebraicGeometry.degreeZeroSectionsField`,
the degree-zero cohomology of the derived sections over `Γ(Spec k, 𝒪)` at which the degree-zero
Künneth statement `AlgebraicGeometry.isTensorPairing_degreeZeroKunnethPairing` is stated, and the
left-hand side carries the `k`-linear structure of `AlgebraicGeometry.modulesLinear`. The value
of the inverse at a morphism is `AlgebraicGeometry.homLinearEquivDegreeZeroSections_apply`. -/
def homLinearEquivDegreeZeroSections (N N' : DerivedCategory X.left.Modules) :
    letI : Linear k X.left.Modules := modulesLinear k X
    (N ⟶ N') ≃ₗ[k] degreeZeroSectionsField k X.hom (derivedSheafHomObj k X N N') :=
  letI : Linear k X.left.Modules := modulesLinear k X
  LinearEquiv.symm
    { degreeZeroSectionsHomAddEquiv k X N N' with
      map_smul' := degreeZeroSectionsHomAddEquiv_smul k X N N' }

/-- **The inverse of [Stacks, Tag 08DK] in this spelling, at the image of a class.** -/
theorem homLinearEquivDegreeZeroSections_apply_equiv (N N' : DerivedCategory X.left.Modules)
    (w : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
          (Stacks.SheafOfModules.ringedSite X.left.sheaf)).obj (derivedSheafHomObj k X N N')) :
        Type u)) :
    letI : Linear k X.left.Modules := modulesLinear k X
    homLinearEquivDegreeZeroSections k X N N'
        (derivedSheafHomGlobalSectionsEquivScheme k X N N' w) =
      (homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N')).hom.hom
        ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N')).inv w) := by
  change (homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N')).hom.hom
      ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N')).inv
        ((derivedSheafHomGlobalSectionsEquivScheme k X N N').symm
          (derivedSheafHomGlobalSectionsEquivScheme k X N N' w))) = _
  rw [AddEquiv.symm_apply_apply]

/-- **[Stacks, Tag 08DK] in this spelling is natural in the target.** For `φ : N ⟶ N'` and
`χ : N' ⟶ N''`, the class of `φ ≫ χ` is the image of the class of `φ` under the map induced by
`R𝓗om(N, χ)` on `H⁰RΓ(X, -)`. -/
theorem homLinearEquivDegreeZeroSections_comp (N N' N'' : DerivedCategory X.left.Modules)
    (φ : N ⟶ N') (χ : N' ⟶ N'') :
    letI : Linear k X.left.Modules := modulesLinear k X
    homLinearEquivDegreeZeroSections k X N N'' (φ ≫ χ) =
      ((gammaRestrict k).map
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).map
          ((sectionsOverBase X.hom.toLRSHom.toShHom).map ((sheafHomOutOf k X N).map χ)))).hom
        (homLinearEquivDegreeZeroSections k X N N' φ) := by
  let : Linear k X.left.Modules := modulesLinear k X
  set x := homLinearEquivDegreeZeroSections k X N N' φ
  have hφ : degreeZeroSectionsHomAddEquiv k X N N' x = φ :=
    (homLinearEquivDegreeZeroSections k X N N').symm_apply_apply φ
  apply (homLinearEquivDegreeZeroSections k X N N'').symm.injective
  rw [LinearEquiv.symm_apply_apply]
  set g := (sheafHomOutOf k X N).map χ
  change φ ≫ χ = derivedSheafHomGlobalSectionsEquivScheme k X N N''
    ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N'')).hom
      ((homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N'')).inv.hom
        (((gammaRestrict k).map
          ((DerivedCategory.homologyFunctor
              (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).map
            ((sectionsOverBase X.hom.toLRSHom.toShHom).map g))).hom x)))
  have hnat : (homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N'')).inv.hom
      (((gammaRestrict k).map
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).map
          ((sectionsOverBase X.hom.toLRSHom.toShHom).map g))).hom x) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver X.hom).map g)).hom
        ((homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N')).inv.hom x) :=
    ConcreteCategory.congr_hom ((homologyZeroGlobalSectionsOverNatIso k X).inv.naturality g) x
  rw [hnat, degreeZeroSectionsHomAddEquiv_apply] at *
  exact ((congrArg (· ≫ χ) hφ).symm).trans
    (derivedSheafHomGlobalSectionsEquivScheme_map k X N χ _).symm

/-! ### Classes of morphisms out of the structure sheaf, and the transpose of a morphism -/

/-- `𝒪_X` in degree zero, `AlgebraicGeometry.RingedSite.derivedStructureSheaf`, as an object of
`D(𝒪_X)` in the scheme's spelling. -/
abbrev structureSheafObj : DerivedCategory X.left.Modules :=
  RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.left.sheaf)

/-- `Hom_{D(𝒪_X)}(𝒪_X, E) = H⁰(X, E)`,
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv`, with the structure sheaf
and the Hom group written in the scheme's spelling of `D(𝒪_X)`. -/
abbrev structureSheafGlobalSectionsEquivScheme (E : DerivedCategory X.left.Modules) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
          (Stacks.SheafOfModules.ringedSite X.left.sheaf)).obj E) : Type u) ≃+
      (structureSheafObj k X ⟶ E) :=
  RingedSite.derivedStructureSheafGlobalSectionsEquiv
    (Stacks.SheafOfModules.ringedSite X.left.sheaf) E

/-- **The class of a morphism out of the structure sheaf.** A morphism `s : 𝒪_X ⟶ E` in
`D(𝒪_X)` is a degree-zero cohomology class of `RΓ(X, E)`: this is
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv` (Stacks 08JA at source
the structure sheaf), read in `AlgebraicGeometry.degreeZeroSectionsField`. -/
def degreeZeroClassAddEquiv (E : DerivedCategory X.left.Modules) :
    (structureSheafObj k X ⟶ E) ≃+
      (degreeZeroSectionsField k X.hom E : Type u) where
  toFun s := (homologyZeroGlobalSectionsOverIso k X E).hom.hom
    ((homologyZeroForgetIso X.hom E).inv ((structureSheafGlobalSectionsEquivScheme k X E).symm s))
  invFun x := structureSheafGlobalSectionsEquivScheme k X E
    ((homologyZeroForgetIso X.hom E).hom ((homologyZeroGlobalSectionsOverIso k X E).inv.hom x))
  left_inv s := by
    simp only [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply]
    exact AddEquiv.apply_symm_apply _ s
  right_inv x := by
    simp only [AddEquiv.symm_apply_apply, Iso.hom_inv_id_apply]
    exact Iso.inv_hom_id_apply (homologyZeroGlobalSectionsOverIso k X E) x
  map_add' s t := by
    simp only [map_add]

/-- The class of a morphism `s : 𝒪_X ⟶ E` in `degreeZeroSectionsField`, unfolded. -/
theorem degreeZeroClassAddEquiv_apply (E : DerivedCategory X.left.Modules)
    (s : structureSheafObj k X ⟶ E) :
    degreeZeroClassAddEquiv k X E s = (homologyZeroGlobalSectionsOverIso k X E).hom.hom
      ((homologyZeroForgetIso X.hom E).inv
        ((structureSheafGlobalSectionsEquivScheme k X E).symm s)) :=
  rfl

/-- The class of the image of a morphism under [Stacks, Tag 08DK], read back as a morphism out of
the structure sheaf. -/
theorem degreeZeroClassAddEquiv_symm_homLinearEquivDegreeZeroSections
    (N N' : DerivedCategory X.left.Modules) (φ : N ⟶ N') :
    letI : Linear k X.left.Modules := modulesLinear k X
    (degreeZeroClassAddEquiv k X (derivedSheafHomObj k X N N')).symm
        (homLinearEquivDegreeZeroSections k X N N' φ) =
      structureSheafGlobalSectionsEquivScheme k X (derivedSheafHomObj k X N N')
        ((derivedSheafHomGlobalSectionsEquivScheme k X N N').symm φ) := by
  let : Linear k X.left.Modules := modulesLinear k X
  change structureSheafGlobalSectionsEquivScheme k X (derivedSheafHomObj k X N N')
      ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N')).hom
        ((homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N')).inv.hom
          ((homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N')).hom.hom
            ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N')).inv
              ((derivedSheafHomGlobalSectionsEquivScheme k X N N').symm φ))))) = _
  simp only [Iso.hom_inv_id_apply, Iso.inv_hom_id_apply]

/-- **The transpose of a morphism**, `𝒪_X ⟶ R𝓗om(N, N')`: the morphism out of the structure
sheaf which Stacks 08JA (at source the structure sheaf) matches with the class that
[Stacks, Tag 08DK] attaches to `φ`. This is how
`AlgebraicGeometry.RingedSite.derivedIdentitySection` is built from the identity, and by the unit
law of [Stacks, Tag 08J8], `Stacks.SheafOfModules.derivedSheafHomCounit_unit_law_monoidal'`, it is
a transpose of `φ` for the evaluation `ev` of [Stacks, Tag 08DI]: `(t ▷ N) ≫ ev = λ_N ≫ φ`. -/
def homTranspose (N N' : DerivedCategory X.left.Modules) (φ : N ⟶ N') :
    structureSheafObj k X ⟶ derivedSheafHomObj k X N N' :=
  structureSheafGlobalSectionsEquivScheme k X (derivedSheafHomObj k X N N')
    ((derivedSheafHomGlobalSectionsEquivScheme k X N N').symm φ)

/-- `homTranspose` is the site-level identification of Stacks 08JA applied to the inverse of
[Stacks, Tag 08DK]. -/
theorem homTranspose_eq (N N' : DerivedCategory X.left.Modules) (φ : N ⟶ N') :
    homTranspose k X N N' φ =
      RingedSite.derivedStructureSheafGlobalSectionsEquiv
        (Stacks.SheafOfModules.ringedSite X.left.sheaf) (derivedSheafHomObj k X N N')
        ((derivedSheafHomGlobalSectionsEquivScheme k X N N').symm φ) :=
  rfl

/-- **[Stacks, Tag 08DK] in the spelling of the degree-zero Künneth statement sends a morphism to
the class of its transpose.** -/
theorem homLinearEquivDegreeZeroSections_eq_class (N N' : DerivedCategory X.left.Modules)
    (φ : N ⟶ N') :
    letI : Linear k X.left.Modules := modulesLinear k X
    homLinearEquivDegreeZeroSections k X N N' φ =
      degreeZeroClassAddEquiv k X (derivedSheafHomObj k X N N') (homTranspose k X N N' φ) := by
  let : Linear k X.left.Modules := modulesLinear k X
  rw [homTranspose, ← degreeZeroClassAddEquiv_symm_homLinearEquivDegreeZeroSections,
    AddEquiv.apply_symm_apply]

/-- `homTranspose φ` read back through Stacks 08JA and [Stacks, Tag 08DK] is `φ`. -/
theorem homTranspose_spec (N N' : DerivedCategory X.left.Modules) (φ : N ⟶ N') :
    derivedSheafHomGlobalSectionsEquivScheme k X N N'
        ((structureSheafGlobalSectionsEquivScheme k X (derivedSheafHomObj k X N N')).symm
          (homTranspose k X N N' φ)) = φ := by
  rw [homTranspose, AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]

end AlgebraicGeometry

end
